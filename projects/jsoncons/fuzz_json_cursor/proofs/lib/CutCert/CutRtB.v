(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutRtA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CRB.
Definition mem := (word -> option byte).

Definition base_off (v : nat) (e : expr) : option Z :=
  match lin_of e with
  | (c, [(k, EVar w)]) => if (Z.eqb k 1 && Nat.eqb w v)%bool then Some c else None
  | _ => None
  end.
Lemma base_off_sound : forall E v e c, base_off v e = Some c -> 0 <= CL5A.uv E (EVar v) + c < 2 ^ 64 -> CL5A.uv E e = CL5A.uv E (EVar v) + c.
Proof.
  intros E v e c H Hr. unfold base_off in H. destruct (lin_of e) as [c0 ts] eqn:El. destruct ts as [|[k a] ts]; [discriminate|]. destruct a as [|w| | | | | |]; try discriminate.
  destruct ts; [|discriminate]. destruct (Z.eqb k 1 && Nat.eqb w v)%bool eqn:Hb; [|discriminate]. injection H as <-.
  apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. subst k w.
  unfold CL5A.uv. apply CL5.u_lin; [|exact Hr]. rewrite El. unfold lden. cbn [fst snd tden]. unfold uE, CL5A.uv in *. lia.
Qed.

Inductive bkind : Type := BBytes (o m : Z) | BWhole | BSh (o m : Z) | BShAll.
Definition lit_of (e : expr) : option Z := match e with ELit z => if (Z.leb 0 z && Z.leb z (2 ^ 32))%bool then Some z else None | _ => None end.
Lemma lit_of_sound : forall e z, lit_of e = Some z -> 0 <= z <= 2 ^ 32 /\ forall E, elenZ E e = z.
Proof.
  intros e z H. destruct e as [z0| | | | | | |]; try discriminate. cbn [lit_of] in H. destruct (Z.leb 0 z0 && Z.leb z0 (2 ^ 32))%bool eqn:Hb; [|discriminate]. injection H as <-.
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2. split; [lia|]. intros E. unfold elenZ. cbn [edenot]. apply u64_of_Z. lia.
Qed.
Definition cok (c : Z) : bool := (Z.leb 0 c && Z.leb c (2 ^ 32))%bool.
Definition plain_of (a0v : nat) (ne b : expr) (off : Z) (n : expr) : option bkind :=
  match base_off a0v b with
  | Some c =>
      if negb (cok c) then None
      else if (Z.eqb (c + off) 0 && expr_eqb n ne)%bool then Some BWhole
      else match lit_of ne, lit_of n with
           | Some N, Some m => if (Z.leb 0 (c + off) && Z.ltb 0 m && Z.leb (c + off + m) N)%bool then Some (BBytes (c + off) m) else None
           | _, _ => None
           end
  | None => None
  end.
Definition shad_of (a0v : nat) (ne b : expr) (off : Z) (n : expr) : option bkind :=
  match base_off a0v b with
  | Some c =>
      if negb (cok c && Z.eqb (c mod 8) 0) then None
      else match lit_of ne, lit_of n with
           | Some N, Some m => if (Z.leb 0 (c / 8 + (off - SB)) && Z.ltb 0 m && Z.leb (c / 8 + (off - SB) + m) (N / 8))%bool then Some (BSh (c / 8 + (off - SB)) m) else None
           | _, _ => if (Z.eqb c 0 && Z.eqb off SB && expr_eqb n (CHA.SRL3 ne))%bool then Some BShAll else None
           end
  | None => None
  end.
Definition bobj_of (a0v : nat) (ne : expr) (a : saddr) (n : expr) : option bkind :=
  match a with
  | SA (EAlu Instr.ALU_SRL b (ELit 3)) off => shad_of a0v ne b off n
  | SA b off => plain_of a0v ne b off n
  end.
Definition ivl (u n : Z) (kd : bkind) : Z * Z :=
  match kd with BBytes o m => (u + o, m) | BWhole => (u, n) | BSh o m => (S u + o, m) | BShAll => (S u, n / 8) end.
Definition is_sh (kd : bkind) : bool := match kd with BSh _ _ | BShAll => true | _ => false end.
Definition is_img (ILO IHI : Z) (a : saddr) (n : expr) : bool :=
  match a, n with SA (ELit 0) lo, ELit m => (Z.leb ILO lo && Z.ltb 0 m && Z.leb (lo + m) IHI)%bool | _, _ => false end.

Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Variable ILO IHI : Z.
Hypothesis LY_hull : hl_img_lo L <= ILO /\ IHI <= hl_img_hi L.
Variable NF : nat.
Variable E0 : env.
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable Wo : list L5.range.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LBrest FFrest sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.

Definition small_ok (cells : list kentry) (ne : expr) : bool :=
  match lit_of ne with Some z => Z.leb z 4096 | None => (APC.fact_ok cells (KRange ne 0 4096) || CX.fact2_ok cells (KRange ne 0 4096))%bool end.
Definition ablock_fact_ok (cells : list kentry) (nx : nat) (BLi : CA.blocks) (FLi : list (expr * Z * Z)) (a0v : nat) (ne : expr) (X : kentry) : bool :=
  match X with
  | KRange (EVar v) lo hi => (Nat.eqb v a0v && (Z.leb lo 4096 || (Z.leb lo BIGSHADOW_HI && small_ok cells ne)) && Z.leb (2 ^ 47 - 8388608 - 1) hi)%bool
  | KAlign (EVar v) m => (Nat.eqb v a0v && Z.ltb 0 m && Z.eqb (16 mod m) 0)%bool
  | KUnk a n => CRA.isS (bobj_of a0v ne a n)
  | KWr a n => match bobj_of a0v ne a n with Some kd => negb (is_sh kd) | None => false end
  | KZero a n => match bobj_of a0v ne a n with Some kd => is_sh kd | None => false end
  | KWord (SA (EAlu Instr.ALU_SRL b (ELit 3)) off) 1 (ELit v) =>
      match base_off a0v b, lit_of ne with
      | Some c, Some N => (cok c && Z.eqb (c mod 8) 0 && Z.eqb (c / 8 + (off - SB)) (N / 8) && negb (Z.eqb (N mod 8) 0) && Z.eqb v (N mod 8))%bool
      | _, _ => false
      end
  | KDisj a1 n1 a2 n2 =>
      match bobj_of a0v ne a1 n1, bobj_of a0v ne a2 n2 with
      | Some kd, None => ((match kd with BShAll => CH2.nonempty cells n1 | _ => true end) && CRA.partner_ok d cells nx BLi FLi a2 n2)%bool
      | None, Some kd => ((match kd with BShAll => CH2.nonempty cells n2 | _ => true end) &&
                          (CRA.partner_ok d cells nx BLi FLi a1 n1 || ((CRA.is_bigsh a1 n1 || is_img ILO IHI a1 n1) && negb (is_sh kd))))%bool
      | _, _ => false
      end
  | _ => false
  end.

Section Sound.
Variables (E' E2 : env) (nx : nat) (cells : list kentry) (BLi : CA.blocks) (FLi : list (expr * Z * Z)) (a0v : nat) (ne : expr).
Variables (M' M2 : mem) (A A2 : list (Z * Z)) (model' model2 : Model) (LB LB2 : list (Z * Z)) (FF FF2 LK LK2 : list fframe) (cr cr2 : credit) (u n : Z).
Hypothesis HagE' : env_agree NF E0 E'.
Hypothesis Hag2 : env_agree nx E' E2.
Hypothesis HK : know_ok (hl_segs L) E' (CCA.vis A model' M') cells.
Hypothesis HH : ri_inv HI LB FF LK cr A M' (vml_of model').
Hypothesis HLB : LB = CH2.den E' BLi ++ LBrest.
Hypothesis HFF : FF = CHA.denF sp0 E' FLi ++ FFrest.
Hypothesis Hvu : CL5A.uv E2 (EVar a0v) = u.
Hypothesis Hnv : APC.expr_vars_lt nx ne = true.
Hypothesis Hn : elenZ E' ne = n.

Hypothesis P1 : ablock_range L ar u n.
Hypothesis P2 : blocks_apart u n LB.
Hypothesis P3 : fframes_apart u n FF.
Hypothesis P4 : L5.defined M2 u n.
Hypothesis P5 : shadow_blk M2 u n.
Hypothesis HH2 : ri_inv HI LB2 FF2 LK2 cr2 A2 M2 (vml_of model2).
Hypothesis Hin2 : In (u, n) LB2.

Lemma n2 : elenZ E2 ne = n.
Proof. unfold elenZ in *. rewrite <- (SR.edenot_agree_AP nx E' E2 ne Hag2 Hnv). exact Hn. Qed.
Lemma rfx : CHA.rng_facts L ar LB FF.
Proof. exact (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)). Qed.
Lemma rfx2 : CHA.rng_facts L ar LB2 FF2.
Proof. exact (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2)). Qed.
Lemma ufacts : 4096 <= u /\ u mod 8 = 0 /\ 0 < n /\ u + n <= ahl_ceil ar /\ ahl_ceil ar <= 2 ^ 47 - 8388608 /\ 0x7fff7f800000 <= ahl_ceil ar /\ n < 2 ^ 64.
Proof.
  destruct P1 as (Q1 & _ & Q3 & Q4 & Q5 & _). destruct (CHA.rf_ceil _ _ _ _ rfx) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ rfx) as (SP1 & _).
  repeat split; try lia. exact (CHA.mod8_of_16 u Q3).
Qed.
Lemma S_u : forall c, 0 <= c -> c mod 8 = 0 -> (u + c) / 8 = u / 8 + c / 8.
Proof.
  intros c Hc Hc8. destruct ufacts as (_ & U8 & _). apply Z.mod_divide in U8; [|lia]. destruct U8 as [p Hp]. apply Z.mod_divide in Hc8; [|lia]. destruct Hc8 as [q Hq].
  rewrite Hp, Hq. replace (p * 8 + q * 8) with ((p + q) * 8) by lia. rewrite !Z.div_mul by lia. reflexivity.
Qed.

Definition SEM (a : saddr) (n' : expr) (kd : bkind) : Prop :=
  estart E2 a = fst (ivl u n kd) /\ elenZ E2 n' = snd (ivl u n kd) /\ 0 <= snd (ivl u n kd) /\ 0 <= fst (ivl u n kd) /\ fst (ivl u n kd) + snd (ivl u n kd) <= 2 ^ 64
  /\ (match kd with BShAll => True | _ => 0 < snd (ivl u n kd) end)
  /\ (forall x, fst (ivl u n kd) <= x < fst (ivl u n kd) + snd (ivl u n kd) -> if is_sh kd then in_shadow_of u n x /\ 0 <= x - S u < n / 8 else u <= x < u + n).

Lemma sh_top : forall j, 0 <= j < n / 8 -> in_shadow_of u n (S u + j).
Proof.
  intros j Hj. destruct ufacts as (U0 & U8 & N0 & UC & CL & CL0 & N64). unfold in_shadow_of, S. split; [lia|].
  apply Z.mod_divide in U8; [|lia]. destruct U8 as [p Hp]. rewrite Hp. rewrite Z.div_mul by lia.
  replace (p * 8 + n - 1) with ((n - 1) + p * 8) by lia. rewrite Z.div_add by lia.
  assert (n / 8 - 1 <= (n - 1) / 8) by (apply Z.div_le_lower_bound; [lia|]; pose proof (Z.mul_div_le n 8 ltac:(lia)); lia). lia.
Qed.

Lemma plain_sem : forall b off n' kd, plain_of a0v ne b off n' = Some kd -> SEM (SA b off) n' kd.
Proof.
  intros b off n' kd H. destruct ufacts as (U0 & U8 & N0 & UC & CL & CL0 & N64). pose proof n2 as N2.
  unfold plain_of in H. destruct (base_off a0v b) as [c|] eqn:Hb; [|discriminate].
  destruct (cok c) eqn:Hc; cbn [negb] in H; [|discriminate]. unfold cok in Hc. apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1, C2.
  assert (UB : CL5A.uv E2 b = u + c) by (rewrite (base_off_sound E2 a0v b c Hb); rewrite Hvu; lia).
  assert (ES : estart E2 (SA b off) = u + c + off) by (unfold estart; cbn [a_base a_off]; fold (CL5A.uv E2 b); rewrite UB; reflexivity).
  destruct (Z.eqb (c + off) 0 && expr_eqb n' ne)%bool eqn:C3.
  - injection H as <-. apply andb_prop in C3 as [X1 X2]. apply Z.eqb_eq in X1. apply expr_eqb_eq in X2. subst n'. unfold SEM. cbn [ivl fst snd is_sh]. rewrite ES, N2.
    split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros x Hx. lia.
  - destruct (lit_of ne) as [N|] eqn:LN; [|discriminate]. destruct (lit_of n') as [m|] eqn:LM; [|discriminate].
    destruct (Z.leb 0 (c + off) && Z.ltb 0 m && Z.leb (c + off + m) N)%bool eqn:C4; [|discriminate]. injection H as <-.
    apply andb_prop in C4 as [C4 X3]. apply andb_prop in C4 as [X1 X2]. apply Z.leb_le in X1, X3. apply Z.ltb_lt in X2.
    destruct (lit_of_sound ne N LN) as (_ & LN'). destruct (lit_of_sound n' m LM) as (_ & LM'). rewrite (LN' E2) in N2. subst N.
    unfold SEM. cbn [ivl fst snd is_sh]. rewrite ES, (LM' E2).
    split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros x Hx. lia.
Qed.

Lemma shad_sem : forall b off n' kd, shad_of a0v ne b off n' = Some kd -> SEM (SA (EAlu Instr.ALU_SRL b (ELit 3)) off) n' kd.
Proof.
  intros b off n' kd H. destruct ufacts as (U0 & U8 & N0 & UC & CL & CL0 & N64). pose proof n2 as N2.
  unfold shad_of in H. destruct (base_off a0v b) as [c|] eqn:Hb; [|discriminate].
  destruct (cok c && Z.eqb (c mod 8) 0)%bool eqn:Hc; cbn [negb] in H; [|discriminate]. apply andb_prop in Hc as [Hc C8]. unfold cok in Hc. apply andb_prop in Hc as [C1 C2].
  apply Z.leb_le in C1, C2. apply Z.eqb_eq in C8.
  assert (UB : CL5A.uv E2 b = u + c) by (rewrite (base_off_sound E2 a0v b c Hb); rewrite Hvu; lia).
  assert (ES : estart E2 (SA (EAlu Instr.ALU_SRL b (ELit 3)) off) = S u + (c / 8 + (off - SB))).
  { rewrite CL5A.estart_srl3', UB, (S_u c C1 C8). unfold S. lia. }
  pose proof (Z.div_pos u 8 ltac:(lia) ltac:(lia)) as D0. assert (D1 : u / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  assert (D2 : 0 <= n / 8 <= n) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (LITC : forall N m, lit_of ne = Some N -> lit_of n' = Some m ->
            (if (Z.leb 0 (c / 8 + (off - SB)) && Z.ltb 0 m && Z.leb (c / 8 + (off - SB) + m) (N / 8))%bool then Some (BSh (c / 8 + (off - SB)) m) else None) = Some kd ->
            SEM (SA (EAlu Instr.ALU_SRL b (ELit 3)) off) n' kd).
  { intros N m LN LM H0. destruct (Z.leb 0 (c / 8 + (off - SB)) && Z.ltb 0 m && Z.leb (c / 8 + (off - SB) + m) (N / 8))%bool eqn:C4; [|discriminate]. injection H0 as <-.
    apply andb_prop in C4 as [C4 X3]. apply andb_prop in C4 as [X1 X2]. apply Z.leb_le in X1, X3. apply Z.ltb_lt in X2.
    destruct (lit_of_sound ne N LN) as (_ & LN'). destruct (lit_of_sound n' m LM) as (_ & LM'). rewrite (LN' E2) in N2. subst N.
    unfold SEM. cbn [ivl fst snd is_sh]. rewrite ES, (LM' E2).
    split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [unfold S, SB in *; lia|]. split; [unfold S, SB in *; lia|]. split; [lia|].
    intros x Hx. split; [|lia]. replace x with (S u + (x - S u)) by lia. apply sh_top. lia. }
  assert (ALLC : (if (Z.eqb c 0 && Z.eqb off SB && expr_eqb n' (CHA.SRL3 ne))%bool then Some BShAll else None) = Some kd -> SEM (SA (EAlu Instr.ALU_SRL b (ELit 3)) off) n' kd).
  { intros H0. destruct (Z.eqb c 0 && Z.eqb off SB && expr_eqb n' (CHA.SRL3 ne))%bool eqn:C4; [|discriminate]. injection H0 as <-.
    apply andb_prop in C4 as [C4 X3]. apply andb_prop in C4 as [X1 X2]. apply Z.eqb_eq in X1, X2. apply expr_eqb_eq in X3. subst c off n'.
    unfold SEM. cbn [ivl fst snd is_sh]. rewrite ES. unfold CHA.SRL3. rewrite CL5A.elen_srl3'. fold (elenZ E2 ne). change (CL5A.uv E2 ne) with (elenZ E2 ne). rewrite N2.
    rewrite Z.div_0_l by lia.
    split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [unfold S, SB in *; lia|]. split; [unfold S, SB in *; lia|]. split; [exact I|].
    intros x Hx. split; [|lia]. replace x with (S u + (x - S u)) by lia. apply sh_top. lia. }
  destruct (lit_of ne) as [N|] eqn:LN; [destruct (lit_of n') as [m|] eqn:LM|]; [exact (LITC N m eq_refl eq_refl H) | exact (ALLC H) | exact (ALLC H)].
Qed.

Lemma obj_sem : forall a n' kd, bobj_of a0v ne a n' = Some kd -> SEM a n' kd.
Proof.
  intros [b off] n' kd H. unfold bobj_of in H.
  destruct b as [z|v|op e1 e2| | | | |]; try exact (plain_sem _ off n' kd H).
  destruct op; try exact (plain_sem _ off n' kd H).
  destruct e2 as [z| | | | | | |]; try exact (plain_sem _ off n' kd H).
  destruct z as [|p|]; try exact (plain_sem _ off n' kd H). destruct p as [p|p|]; try exact (plain_sem _ off n' kd H). destruct p as [p|p|]; try exact (plain_sem _ off n' kd H).
  exact (shad_sem e1 off n' kd H).
Qed.

Lemma obj_defvis : forall kd a n' x, bobj_of a0v ne a n' = Some kd -> fst (ivl u n kd) <= x < fst (ivl u n kd) + snd (ivl u n kd) ->
  M2 (Z_to_bv 64 x) <> None /\ ahid A2 model2 (Z_to_bv 64 x) = false /\ (is_sh kd = true -> byte_at M2 x 0).
Proof.
  intros kd a n' x H Hx. destruct (obj_sem a n' kd H) as (_ & _ & _ & _ & _ & _ & IN). specialize (IN x Hx).
  destruct ufacts as (U0 & U8 & N0 & UC & CL & CL0 & N64). destruct P1 as (_ & _ & _ & _ & _ & (_ & AM & _)).
  destruct (is_sh kd) eqn:SH.
  - destruct IN as [IN1 IN2]. pose proof (proj1 P5 (x - S u) IN2) as Bz. replace (S u + (x - S u)) with x in Bz by lia.
    split; [unfold byte_at in Bz; rewrite Bz; discriminate|]. split; [|intros _; exact Bz].
    pose proof (CHA.shadow_range u n x ltac:(lia) N0 ltac:(lia) IN1) as SRx.
    apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model2 0 0 x HH2); [lia | | ].
    + do 6 right. exists (u, n). split; [exact Hin2 | exact IN1].
    + exact (CL5A.not_stk_shadow_sh L ar LB2 FF2 u n x rfx2 ltac:(lia) N0 UC IN1).
  - split; [replace x with (u + (x - u)) by lia; apply P4; lia|]. split; [|discriminate].
    apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model2 0 0 x HH2); [lia | left; exists (u, n); split; [exact Hin2 | cbn [fst snd]; lia] | ].
    apply (CL5A.not_stk_shadow_app L ar LB2 FF2 x rfx2). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
Qed.

Lemma obj_not_cl : forall kd a n' x, bobj_of a0v ne a n' = Some kd -> fst (ivl u n kd) <= x < fst (ivl u n kd) + snd (ivl u n kd) -> ~ aclient L ar LB FF 0 0 x.
Proof.
  intros kd a n' x H Hx. destruct (obj_sem a n' kd H) as (_ & _ & _ & _ & _ & _ & IN). specialize (IN x Hx).
  destruct ufacts as (U0 & U8 & N0 & UC & CL & CL0 & N64). pose proof P1 as (_ & Q2 & _ & _ & _ & Q6).
  apply (CHA.obj_not_client L ar LY_img LB FF 0 0 u n x rfx Q6 N0 U8 UC Q2 P2 P3). destruct (is_sh kd); [right; exact (proj1 IN) | left; exact IN].
Qed.

Lemma ablock_fact_sound : forall X, ablock_fact_ok cells nx BLi FLi a0v ne X = true -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X.
Proof.
  intros X H. destruct ufacts as (U0 & U8 & N0 & UC & CL & CL0 & N64). pose proof P1 as (_ & Q2 & Q3 & _ & _ & (_ & AM & _)).
  unfold ablock_fact_ok in H.
  assert (DEFV : forall kd a n', bobj_of a0v ne a n' = Some kd -> L5.defined (CCA.vis A2 model2 M2) (estart E2 a) (elenZ E2 n') /\ flat E2 a (elenZ E2 n')).
  { intros kd a n' Ho. destruct (obj_sem a n' kd Ho) as (O1 & O2 & O3 & O4 & O5 & O6 & _). rewrite O1, O2. split.
    - intros i Hi. destruct (obj_defvis kd a n' (fst (ivl u n kd) + i) Ho ltac:(lia)) as (G1 & G2 & _). unfold CCA.vis. rewrite (CL5A.vis_eq _ M2 _ G2). exact G1.
    - unfold flat. rewrite O1. assert (fst (ivl u n kd) < 2 ^ 64) by (destruct kd; cbn [ivl fst snd] in *; unfold S, SB in *;
        pose proof (Z.div_pos u 8 ltac:(lia) ltac:(lia)); assert (u / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia). lia. }
  destruct X as [[b o] w v|a n'|a n' kk|lo hi|e m|e lo hi|a n'|a1 n1 a2 n2|a n' c0|a n']; try discriminate.
  -
    destruct b as [|vb|op e1 e2| | | | |]; try discriminate. destruct op; try discriminate. destruct e2 as [z| | | | | | |]; try discriminate.
    destruct z as [|p|]; try discriminate. destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate.
    destruct w as [|[|w]]; try discriminate. destruct v as [vz| | | | | | |]; try discriminate.
    destruct (base_off a0v e1) as [c|] eqn:Hb; [|discriminate]. destruct (lit_of ne) as [N|] eqn:LN; [|discriminate].
    apply andb_prop in H as [H X5]. apply andb_prop in H as [H X4]. apply andb_prop in H as [H X3]. apply andb_prop in H as [X1 X2].
    unfold cok in X1. apply andb_prop in X1 as [X1 X1']. apply Z.leb_le in X1, X1'. apply Z.eqb_eq in X2, X3, X5. apply negb_true_iff in X4. apply Z.eqb_neq in X4.
    destruct (lit_of_sound ne N LN) as (NR & LN'). pose proof n2 as N2. rewrite (LN' E2) in N2. subst N vz.
    pose proof (Z.mul_div_le n 8 ltac:(lia)) as ND. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as NM.
    assert (HS : in_shadow_of u n (S u + n / 8)).
    { unfold in_shadow_of, S. split; [pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)); lia|]. apply Z.mod_divide in U8; [|lia]. destruct U8 as [q Hq]. rewrite Hq. rewrite Z.div_mul by lia.
      replace (q * 8 + n - 1) with ((n - 1) + q * 8) by lia. rewrite Z.div_add by lia.
      assert (n / 8 <= (n - 1) / 8) by (apply Z.div_le_lower_bound; [lia|]; pose proof (Z_div_mod_eq_full n 8); lia). lia. }
    pose proof (CHA.shadow_range u n _ ltac:(lia) N0 ltac:(lia) HS) as SRx.
    assert (VIS : ahid A2 model2 (Z_to_bv 64 (S u + n / 8)) = false).
    { apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model2 0 0 _ HH2); [lia | do 6 right; exists (u, n); split; [exact Hin2 | exact HS] | ].
      exact (CL5A.not_stk_shadow_sh L ar LB2 FF2 u n _ rfx2 ltac:(lia) N0 UC HS). }
    assert (UB : CL5A.uv E2 e1 = u + c) by (rewrite (base_off_sound E2 a0v e1 c Hb); rewrite Hvu; lia).
    eapply CL5A.kword8_intro with (A := S u + n / 8) (z := n mod 8).
    + rewrite CL5A.estart_srl3', UB, (S_u c X1 X2). unfold S. lia.
    + lia.
    + lia.
    + reflexivity.
    + lia.
    + apply CL5A.byte_at_u8. apply CL5A.byte_vis; [exact VIS|]. exact (proj2 P5 X4).
  -
    destruct (bobj_of a0v ne a n') as [kd|] eqn:Ho; [|discriminate]. destruct (DEFV kd a n' Ho) as (_ & FL). destruct (obj_sem a n' kd Ho) as (O1 & O2 & _).
    cbn [kentry_ok]. split; [exact FL|]. rewrite O1, O2. intros i Hi.
    destruct (obj_defvis kd a n' (fst (ivl u n kd) + i) Ho ltac:(lia)) as (_ & G2 & G3). unfold CCA.vis. rewrite (CL5A.vis_eq _ M2 _ G2). exact (G3 H).
  -
    destruct e as [|v| | | | | |]; try discriminate. apply andb_prop in H as [H X3]. apply andb_prop in H as [X1 X2]. apply Nat.eqb_eq in X1. apply Z.ltb_lt in X2. apply Z.eqb_eq in X3. subst v.
    cbn [kentry_ok]. split; [exact X2|]. unfold CL5A.uv in Hvu. rewrite Hvu.
    apply Z.mod_divide in X3; [|lia]. destruct X3 as [q Hq]. apply Z.mod_divide in Q3; [|lia]. destruct Q3 as [p Hp]. rewrite Hp, Hq. replace (p * (q * m)) with ((p * q) * m) by lia. apply Z_mod_mult.
  -
    destruct e as [|v| | | | | |]; try discriminate. cbn [kentry_ok edenot]. apply andb_prop in H as [H X3]. apply andb_prop in H as [X1 X2]. apply Nat.eqb_eq in X1. apply Z.leb_le in X3. subst v.
    unfold CL5A.uv in Hvu. cbn [edenot] in Hvu. rewrite Hvu. split; [|lia]. apply orb_prop in X2 as [X2|X2]; [apply Z.leb_le in X2; lia|].
    apply andb_prop in X2 as [X2 X4]. apply Z.leb_le in X2.
    assert (SM : n <= 4096).
    { unfold small_ok in X4. destruct (lit_of ne) as [z|] eqn:LN.
      - apply Z.leb_le in X4. destruct (lit_of_sound ne z LN) as (_ & LN'). rewrite <- Hn, (LN' E'). exact X4.
      - rewrite <- Hn. apply orb_prop in X4 as [F|F]; [pose proof (APS.fact_ok_sound (hl_segs L) E' _ cells _ HK F) as Y | pose proof (CX.fact2_ok_sound (hl_segs L) E' _ cells _ HK F) as Y];
          cbn [kentry_ok] in Y; unfold elenZ; lia. }
    exact (Z.le_trans _ _ _ X2 (PmHeapIfaceA.aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2 (u, n) Hin2 SM)).
  -
    destruct (bobj_of a0v ne a n') as [kd|] eqn:Ho; [|discriminate]. destruct (DEFV kd a n' Ho) as (DF & FL). cbn [kentry_ok]. split; [exact FL|].
    intros dd mm Hdd Hmm. exact (kunk_store_ok (hl_segs L) E2 _ a n' dd mm (conj FL DF) Hdd Hmm).
  -
    cbn [kentry_ok].
    assert (NE : forall kd ao no, bobj_of a0v ne ao no = Some kd -> (match kd with BShAll => CH2.nonempty cells no | _ => true end) = true -> 0 < snd (ivl u n kd)).
    { intros kd ao no Ho Hne. destruct (obj_sem ao no kd Ho) as (_ & O2 & _ & _ & _ & O6 & _). destruct kd; try exact O6.
      rewrite <- O2. unfold elenZ. rewrite <- (SR.edenot_agree_AP nx E' E2 no Hag2); [exact (CRA.nonempty_sound (hl_segs L) E' _ cells no HK Hne)|].

      unfold bobj_of in Ho. destruct ao as [b off].
      assert (SH : forall b', shad_of a0v ne b' off no = Some BShAll -> no = CHA.SRL3 ne).
      { intros b' Hs. unfold shad_of in Hs. destruct (base_off a0v b'); [|discriminate]. destruct (negb _); [discriminate|].
        destruct (lit_of ne); [destruct (lit_of no)|].
        - destruct (_ && _ && _)%bool; discriminate.
        - destruct (Z.eqb z 0 && Z.eqb off SB && expr_eqb no (CHA.SRL3 ne))%bool eqn:C4; [|discriminate]. apply andb_prop in C4 as [_ X3]. apply expr_eqb_eq in X3. exact X3.
        - destruct (Z.eqb z 0 && Z.eqb off SB && expr_eqb no (CHA.SRL3 ne))%bool eqn:C4; [|discriminate]. apply andb_prop in C4 as [_ X3]. apply expr_eqb_eq in X3. exact X3. }
      assert (PL : forall b', plain_of a0v ne b' off no = Some BShAll -> False).
      { intros b' Hs. unfold plain_of in Hs. destruct (base_off a0v b'); [|discriminate]. destruct (negb _); [discriminate|]. destruct (_ && _)%bool; [discriminate|].
        destruct (lit_of ne); [|discriminate]. destruct (lit_of no); [|discriminate]. destruct (_ && _ && _)%bool; discriminate. }
      assert (EQ : no = CHA.SRL3 ne).
      { destruct b as [z|v|op e1 e2| | | | |]; try (exfalso; exact (PL _ Ho)). destruct op; try (exfalso; exact (PL _ Ho)).
        destruct e2 as [z| | | | | | |]; try (exfalso; exact (PL _ Ho)). destruct z as [|p|]; try (exfalso; exact (PL _ Ho)).
        destruct p as [p|p|]; try (exfalso; exact (PL _ Ho)). destruct p as [p|p|]; try (exfalso; exact (PL _ Ho)). exact (SH e1 Ho). }
      subst no. unfold CHA.SRL3. cbn [APC.expr_vars_lt]. rewrite Hnv. reflexivity. }
    assert (PO : forall kd ao no ap np, bobj_of a0v ne ao no = Some kd -> (match kd with BShAll => CH2.nonempty cells no | _ => true end) = true ->
                 CRA.partner_ok d cells nx BLi FLi ap np = true ->
                 estart E2 ao + elenZ E2 no <= estart E2 ap \/ estart E2 ap + elenZ E2 np <= estart E2 ao).
    { intros kd ao no ap np Ho Hne Hp. destruct (obj_sem ao no kd Ho) as (O1 & O2 & O3 & O4 & O5 & _). pose proof (NE kd ao no Ho Hne) as O6. rewrite O1, O2.
      pose proof (CRA.partner_sem L ar C HI HIok NF E0 LBrest FFrest sp0 d Wo STK SCR_pos NF32 SP0 Wo_ok CRS_ok WRS_ok E' E2 nx cells BLi FLi 0 M' A model' LB FF LK cr 0
                    HagE' Hag2 HK HH HLB HFF ap np) as PS.
      destruct (PS 0 Hp) as (PN & _). apply CRA.ivl_disj; [exact O6 | exact PN |]. intros x Hx1 Hx2.
      destruct (PS x Hp) as (_ & PC). apply (obj_not_cl kd ao no x Ho Hx1). apply PC; [exact Hx2 | lia]. }
    destruct (bobj_of a0v ne a1 n1) as [k1|] eqn:Ho1; destruct (bobj_of a0v ne a2 n2) as [k2|] eqn:Ho2; try discriminate.
    + apply andb_prop in H as [Hne Hp]. exact (PO k1 a1 n1 a2 n2 Ho1 Hne Hp).
    + apply andb_prop in H as [Hne H]. apply orb_prop in H as [Hp|H]; [pose proof (PO k2 a2 n2 a1 n1 Ho2 Hne Hp) as G; lia|].
      apply andb_prop in H as [H1 H2]. apply negb_true_iff in H2.
      destruct (obj_sem a2 n2 k2 Ho2) as (O1 & O2 & O3 & O4 & O5 & O6 & IN). rewrite H2 in IN. rewrite O1, O2.
      assert (LO : u <= fst (ivl u n k2) /\ fst (ivl u n k2) + snd (ivl u n k2) <= u + n).
      { pose proof (NE k2 a2 n2 Ho2 Hne) as O7. pose proof (IN (fst (ivl u n k2)) ltac:(lia)). pose proof (IN (fst (ivl u n k2) + snd (ivl u n k2) - 1) ltac:(lia)). lia. }
      destruct a1 as [b1 o1]. destruct b1 as [z| | | | | | |]; try (cbn in H1; discriminate). destruct z; try (cbn in H1; discriminate).
      destruct n1 as [m1| | | | | | |]; try (cbn in H1; destruct (Z.eqb o1 BIGSHADOW_LO); discriminate).
      apply orb_prop in H1 as [H1|H1].
      * cbn [CRA.is_bigsh] in H1. apply andb_prop in H1 as [X1 X2]. apply Z.eqb_eq in X1, X2. subst o1 m1.
        unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0) by lia. rewrite u64_of_Z by (unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
        unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
      * cbn [is_img] in H1. apply andb_prop in H1 as [H1 X3]. apply andb_prop in H1 as [X1 X2]. apply Z.leb_le in X1, X3. apply Z.ltb_lt in X2.
        destruct LY_hull as (I1 & I2). destruct LY_img as (I3 & I4). unfold BIGSHADOW_LO in *.
        unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0) by lia. rewrite u64_of_Z by lia. lia.
  -
    destruct (bobj_of a0v ne a n') as [kd|] eqn:Ho; [|discriminate]. destruct (DEFV kd a n' Ho) as (DF & FL). cbn [kentry_ok]. split; [exact FL | exact DF].
Qed.
End Sound.

Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.
Definition fresh_news_ok (cells : list kentry) (nx : nat) (BLi : CA.blocks) (FLi : list (expr * Z * Z)) (a0v : nat) (ne : expr) (news : list kentry) : bool :=
  forallb (fun X => (CHA.static_chk SCELLS GLO GHI X || ablock_fact_ok cells nx BLi FLi a0v ne X)%bool) news.
Lemma news_sound : forall (E' E2 : env) (nx : nat) (cells : list kentry) (BLi : CA.blocks) (FLi : list (expr * Z * Z)) (a0v : nat) (ne : expr)
    (M' M2 : mem) (A A2 : list (Z * Z)) (model' model2 : Model) (LB LB2 : list (Z * Z)) (FF FF2 LK LK2 : list fframe) (cr cr2 : credit) (u n : Z) (news : list kentry),
  env_agree NF E0 E' -> env_agree nx E' E2 -> know_ok (hl_segs L) E' (CCA.vis A model' M') cells ->
  ri_inv HI LB FF LK cr A M' (vml_of model') -> LB = CH2.den E' BLi ++ LBrest -> FF = CHA.denF sp0 E' FLi ++ FFrest ->
  CL5A.uv E2 (EVar a0v) = u -> APC.expr_vars_lt nx ne = true -> elenZ E' ne = n ->
  ablock_range L ar u n -> blocks_apart u n LB -> fframes_apart u n FF -> L5.defined M2 u n -> shadow_blk M2 u n ->
  ri_inv HI LB2 FF2 LK2 cr2 A2 M2 (vml_of model2) -> In (u, n) LB2 ->
  fresh_news_ok cells nx BLi FLi a0v ne news = true ->
  forall X, In X news -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X.
Proof.
  intros E' E2 nx cells BLi FLi a0v ne M' M2 A A2 model' model2 LB LB2 FF FF2 LK LK2 cr cr2 u n news HagE' Hag2 HK HH HLB HFF Hvu Hnv Hn P1 P2 P3 P4 P5 HH2 Hin2 Hok X HX.
  unfold fresh_news_ok in Hok. rewrite forallb_forall in Hok. specialize (Hok X HX). apply orb_prop in Hok as [Hs|Hs].
  - exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 Hs).
  - exact (ablock_fact_sound E' E2 nx cells BLi FLi a0v ne M' M2 A A2 model' model2 LB LB2 FF FF2 LK LK2 cr cr2 u n HagE' Hag2 HK HH HLB HFF Hvu Hnv Hn P1 P2 P3 P4 P5 HH2 Hin2 X Hs).
Qed.
End Inst.

Lemma ahpres_trans : forall (L : asan_layout) (ar : asan_run) LBk LBk1 LBk2 FF sp scr1 scr2 (W W1 W2 : list L5.range) (M0 M1 M2 : mem),
  CHA.ahpres L ar LBk1 FF sp scr1 W1 M0 M1 -> CHA.ahpres L ar LBk2 FF sp scr2 W2 M1 M2 ->
  incl LBk LBk1 -> incl LBk LBk2 -> 0 <= scr2 <= scr1 -> sp <= 2 ^ 47 -> 0x7fff7f800000 <= ahl_ceil ar -> ahl_ceil ar + scr1 <= sp ->
  (forall w a, In w W1 -> L5.in_rng w a -> exists w', In w' W /\ L5.in_rng w' a) -> (forall w a, In w W2 -> L5.in_rng w a -> exists w', In w' W /\ L5.in_rng w' a) ->
  CHA.ahpres L ar LBk FF sp scr1 W M0 M2.
Proof.
  intros L ar LBk LBk1 LBk2 FF sp scr1 scr2 W W1 W2 M0 M1 M2 (A1 & A2 & A3) (B1 & B2 & B3) I1 I2 Hs SPT CL Hc HW1 HW2.
  assert (OUT : forall Wx, (forall w a, In w Wx -> L5.in_rng w a -> exists w', In w' W /\ L5.in_rng w' a) -> forall a, L5.outside W a -> L5.outside Wx a).
  { intros Wx HWx a Ho w Hw Hin. destruct (HWx w a Hw Hin) as (w' & Hw' & Hin'). exact (Ho w' Hw' Hin'). }
  assert (CLI : forall a, aclient L ar LBk FF sp scr1 a -> aclient L ar LBk2 FF sp scr2 a).
  { intros a Ha. eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [exact I2 | apply incl_refl | exact Ha] | intros x Hx; lia]. }
  split; [|split].
  - intros a (Ha & Hcl & Ho). rewrite (B1 a (conj Ha (conj (CLI a Hcl) (OUT W2 HW2 a Ho)))).
    apply A1. split; [exact Ha|]. split; [eapply CHA.aclient_incl; [exact I1 | apply incl_refl | exact Hcl] | exact (OUT W1 HW1 a Ho)].
  - intros k Hk. destruct (Z_lt_dec (sp - scr1 + k) (sp - scr2)) as [Hlt|Hge].
    + apply (B3 (sp - scr1 + k)); [lia | right; left; split; lia | exact (A2 k Hk)].
    + replace (sp - scr1 + k) with (sp - scr2 + (k - (scr1 - scr2))) by lia. apply B2. lia.
  - intros a Ha Hcl Hd. apply (B3 a Ha (CLI a Hcl)). apply (A3 a Ha); [eapply CHA.aclient_incl; [exact I1 | apply incl_refl | exact Hcl] | exact Hd].
Qed.

Section Tail.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable Cred : nat -> env -> credit -> Prop.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FFrest sp0.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M0 sp0 (ar_stack_top ar - sp0).
Hypothesis KNIL : K [].
Variable R0 : bvmap 5 word.
Variable ra0 : Z.
Hypothesis EV0 : forall x : reg, ev E0 (ridx x) = getr R0 x.
Hypothesis RA0 : getr R0 1%bv = Z_to_bv 64 ra0.
Hypothesis RA0ok : L5.ra_ok ra0.

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation curB := (CHA.curB LBrest BLS).

Definition tail_base_chk (pc : Z) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (Z.eqb (SR.ps_pc ps) pc && CL.ps_keeps ps CL5.CSAVED && Nat.leb NF (CC.cp_nx c))%bool.

Lemma tail_leaf : forall pc scr dc i c ps,
  tail_base_chk pc c ps = true -> CHA.foot_chk NF d c (nth i BLS []) (nth i FFS []) = true -> nth i FFS [] = [] -> 0 <= scr <= SCR -> dc <= D0 ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
    (forall cr LK,
        regs_preserved R0 R' -> CHA.ahpres L ar LBrest FFrest sp0 SCR W M0 M1 -> ri_inv HI (curB i E) FFrest LK cr A M1 (vml_of model1) -> incl LK LK0 -> Cred i E cr ->
        env_agree NF E0 E' -> AAMB i E A M1 model1 ->
        exists (Pre : bvmap 5 word -> mem -> Prop)
               (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop),
          CBA.cps_asanG L ar HI FPI pc ra0 sp0 scr (curB i E) FFrest LK cr A dc Pre Post /\ Pre R' M1 /\
          forall (fx2 : FPState) R2 M2 model2 LB' cr' LBk Wc LK2 A2, FPI fx2 -> Post R' M1 R2 M2 LB' cr' LBk Wc -> regs_preserved R0 R2 ->
            CHA.ahpres L ar LBk FFrest sp0 scr Wc M1 M2 -> model_rt model0 model2 -> incl A0 A2 -> CHA.amodel_ok A2 model2 -> incl LK2 LK0 ->
            ri_inv HI LB' FFrest LK2 cr' A2 M2 (vml_of model2) ->
            srealizes (hl_segs L) SCFG (mkCfg (@mkst fx2 R2 (Z_to_bv 64 ra0) M2 (seg_rom (hl_segs L))) model2) K) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros pc scr dc i c ps Hchk Hfoot HFi Hscr Hdc fx' E R A M model E' R' M1 model1 HAt HA HFP Hag HLF USER.
  unfold tail_base_chk in Hchk. apply andb_prop in Hchk as [Hchk C3]. apply andb_prop in Hchk as [C1 C2]. apply Z.eqb_eq in C1. apply Nat.leb_le in C3.
  pose proof (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
                i c ps E E' R R' A M model M1 model1 Hfoot HAt HA Hag HLF) as HA'.
  pose proof HA' as (Hmo1 & Hrt1 & HA01 & HagE & (cr & LK & HH1 & HLK1 & HC1 & HRoom1) & Hfr1 & Hdf1).
  pose proof (CBA.leaf_agree0 L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i c E E' A M model HA C3 Hag) as HagE'.
  assert (KEEP : forall x : reg, In (ridx x) CL5.CSAVED -> getr R' x = getr R0 x).
  { intros x Hx. assert (Hx32 : (ridx x < NF)%nat).
    { apply (Nat.lt_le_trans _ 32); [|exact NF32]. unfold CL5.CSAVED in Hx. cbn [In] in Hx. clear - Hx.
      repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; apply Nat.ltb_lt; reflexivity|]). destruct Hx. }
    rewrite (CL.ps_keeps_sound (hl_segs L) c ps E0 E' R' _ _ CL5.CSAVED NF x (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) C2 HagE' Hx Hx32). exact (EV0 x). }
  assert (HRP : regs_preserved R0 R') by (intros x Hx; apply KEEP; exact (CL5.csaved_in x Hx)).
  assert (Hra' : getr R' 1%bv = Z_to_bv 64 ra0) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact RA0).
  assert (Hsp' : getr R' 2%bv = Z_to_bv 64 sp0).
  { rewrite (KEEP 2%bv ltac:(right; left; reflexivity)). rewrite <- (EV0 2%bv). change (ridx 2%bv) with 2%nat. rewrite <- SP0. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (Htp' : getr R' 4%bv = Z_to_bv 64 (hl_tp L)).
  { rewrite (KEEP 4%bv ltac:(right; right; right; left; reflexivity)). rewrite <- (EV0 4%bv). exact TP0. }
  assert (HFx : CHA.curF FFrest sp0 FFS i E = FFrest) by (unfold CHA.curF; rewrite HFi; reflexivity).
  rewrite HFx in HH1, HRoom1. rewrite HFi in HRoom1. cbn [length] in HRoom1. rewrite Z.sub_0_r in HRoom1.
  pose proof (CBA.exit_post L ar C HI HIok NF M0 model0 A0 LBrest FFrest sp0 d W BLS STK NF32 DEF0 i E A M1 model1 cr LK FFrest Hmo1 Hrt1 HA01 Hfr1 Hdf1 HH1) as HP.
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1)) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & _). destruct STK as (S1 & S2 & S3).
  assert (HSTK : CHA.astk ar M1 sp0 scr).
  { split; [exact S1|]. split; [lia|]. split; [exact S3|]. split; [exact SP1|]. split.
    - intros k Hk. destruct HP as (_ & P2 & _). replace (sp0 - scr + k) with (sp0 - SCR + (SCR - scr + k)) by lia. apply P2. lia.
    - intros k Hk. pose proof (CHA.wf_top _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1)) as TOP.
      apply (Hdf1 (sp0 + k)); [lia | right; left; split; lia | apply DEFUP; exact Hk]. }
  destruct (USER cr LK HRP HP HH1 HLK1 HC1 HagE' HA') as (Pre & Post & SPEC & HPre & HPost).
  rewrite C1.
  apply (SPEC fx' R' M1 model1 K HH1 Hmo1 KNIL HFP Hra' RA0ok Hsp' Htp' HSTK); [apply (CHA.ffroom_le _ _ _ _ HRoom1); exact Hdc | exact FFRS0 | exact HPre |].
  intros fx2 R2 M2 model2 LB' cr' LBk Wc LK2 A2 HFP2 HPo HRP2 HP2 Hrt2 HA2 Hmo2 HLK2 HH2.
  apply (HPost fx2 R2 M2 model2 LB' cr' LBk Wc LK2 A2 HFP2 HPo); [| exact HP2 | exact (L5LZ.model_rt_trans _ _ _ Hrt1 Hrt2) | exact (incl_tran HA01 HA2) | exact Hmo2 | exact (incl_tran HLK2 HLK1) | exact HH2].
  intros x Hx. rewrite (HRP2 x Hx). exact (HRP x Hx).
Qed.
End Tail.

Lemma ffroom_own : forall (own FFrest LK0 LK : list fframe) D0, CHA.ffroom FFrest LK0 D0 -> incl LK LK0 -> base.NoDup (map ff_addr ((own ++ FFrest) ++ LK)) ->
  CHA.ffroom (own ++ FFrest) LK (D0 - Z.of_nat (length own)).
Proof.
  induction own as [|f own IH]; intros FFrest LK0 LK D0 Hr HI0 ND.
  - cbn [app length]. rewrite Z.sub_0_r. exact (CHA.ffroom_sub 32 0 (le_n 32) _ _ _ _ Hr HI0 ND).
  - assert (ND' : base.NoDup (map ff_addr ((own ++ FFrest) ++ LK))).
    { change ((f :: own) ++ FFrest) with (f :: (own ++ FFrest)) in ND. cbn [app map] in ND. apply list_relations.list.NoDup_cons in ND as [_ ND]. exact ND. }
    pose proof (CHA.ffroom_push 32 0 (le_n 32) _ _ _ f _ (IH FFrest LK0 LK D0 Hr HI0 ND') (incl_refl _) ND) as G.
    replace (D0 - Z.of_nat (length (f :: own))) with (D0 - Z.of_nat (length own) - 1) by (cbn [length]; lia). exact G.
Qed.

Section SFree.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Variable PC5 PAT : Z.
Hypothesis SF5 : PmHeapIfaceA.astack_free_spec L ar SCFG HI PC5 PAT 5.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable Cred : nat -> env -> credit -> Prop.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FFrest sp0.
Hypothesis ROOM0 : CHA.ffroom FFrest LK0 D0.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LBrest FFrest sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M0 sp0 (ar_stack_top ar - sp0).
Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.
Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.
Hypothesis KNIL : K [].

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).
Abbreviation curB := (CHA.curB LBrest BLS).
Abbreviation curF := (CHA.curF FFrest sp0 FFS).

Lemma sfree5_leaf : forall news i c ps j cj ci Fe c0,
  nth_error CPS j = Some cj ->
  CHA.custom_chk NF d SCELLS GLO GHI (hl_scr_stack_malloc L) 0 (nth i BLS []) (nth j FFS []) [] news None c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  SR.ps_pc ps = PC5 ->
  nth i FFS [] = (Fe, 5, c0) :: nth j FFS [] ->
  CH2.blocks_eqb (nth j BLS []) (nth i BLS []) = true ->
  CL.ps_reg_is ps 10 Fe = true ->
  forallb (CHA.static_chk SCELLS GLO GHI) news = true ->
  (forall E E2 cr, Cred i E cr -> env_agree NF E E2 -> Cred j E2 cr) ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AMBX i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> CCA.IH (hl_segs L) CPS AMBX K FPI (CC.meas c E) ->
    (forall a, PAT <= a < PAT + 8 -> M1 (Z_to_bv 64 a) = None) ->
    (forall R2 M2 model2 LK' cr, regs_preserved R' R2 ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (curB i E) (curF i E) (sp0 + CH2.ci_csp ci) (hl_scr_stack_malloc L) a ->
                   ~ in_shadow_of (CL5A.uv E Fe) (ff_bytes 5) a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
        ri_inv HI (curB i E) (ff_remove (CL5A.uv E Fe) (curF i E)) LK' cr A M2 (vml_of model2) ->
        XI j (CH2.retEx E' (CH2.ci_nx ci) [] R2) A M2 model2) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros news i c ps j cj ci Fe c0 Hcj Hchk Hpc HFi Hbeq Ha0 Hnews HCred fx' E R A M model E' R' M1 model1 HAt [HA HX] HFP Hag HLF HIH HPAT HXI.
  destruct (CHA.custom_ret L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0
              CRS_ok WRS_ok IMG_ok CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XI (hl_scr_stack_malloc L) 0%nat (nth i BLS []) (nth j FFS []) [] news None i c ps j cj ci Hcj Hchk
              E R A M model E' R' M1 model1 HAt HA Hag HLF HIH) as [CF CONT].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  pose proof HA' as (Hmo1 & Hrt1 & HA01 & HagE & (cr & LK & HH1 & HLK1 & HC1 & HRoom1) & Hfr1 & Hdf1).
  apply CH2.blocks_eqb_eq in Hbeq.
  assert (CHK2 : CH2.blocks_vars_lt (CH2.ci_nx ci) (nth i BLS []) = true /\ CHA.frames_vars_lt (CH2.ci_nx ci) (nth j FFS []) = true).
  { unfold CHA.custom_chk in Hchk. destruct (CHA.common_chk NF d (hl_scr_stack_malloc L) 0 c ps cj (nth i BLS []) (nth i FFS [])) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb Z5].
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Z2]. split; assumption. }
  destruct CHK2 as [BV FV].
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as WF1. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF1) as RF1.
  destruct (CHA.rf_ceil _ _ _ _ RF1) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RF1) as (SP1 & _). pose proof Hstk as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (USP : bv_unsigned (getr R' 2%bv) = sp0 + CH2.ci_csp ci) by (rewrite Hsp; apply u64_of_Z; lia).
  set (F := CL5A.uv E Fe) in *. set (FFj := CHA.denF sp0 E (nth j FFS []) ++ FFrest).
  assert (HFcur : curF i E = (F, 5, sp0 + c0 + 32) :: FFj) by (unfold CHA.curF; rewrite HFi; reflexivity).
  assert (HinF : In (F, 5, sp0 + c0 + 32) (curF i E)) by (rewrite HFcur; left; reflexivity).
  assert (Hrm : ff_remove F (curF i E) = FFj) by (rewrite HFcur; cbn [ff_remove ff_addr fst]; rewrite Z.eqb_refl; reflexivity).
  assert (HFE' : CL5A.uv E' Fe = F).
  { rewrite HFi in HdenF. cbn [CHA.denF map fst snd] in HdenF. injection HdenF as HF1 _. exact HF1. }
  assert (Ha0' : getr R' 10%bv = Z_to_bv 64 F).
  { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
    rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Ha0). unfold CL5A.uv in HFE'. rewrite <- HFE'. rewrite Z_to_bv_bv_unsigned. reflexivity. }

  destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WF1 _ HinF) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). cbn [ff_addr ff_class fst snd] in Q1, Q2, Q3, Q5, Q6. rewrite Hrm in Q6.
  destruct (CHA.frm_align L ar _ _ _ _ _ _ _ WF1 HinF) as (FA & FB & FC). cbn [ff_addr ff_class fst snd] in FA, FB, FC.
  destruct (CHA.wf_fs _ _ _ _ _ _ _ _ WF1) as ((S0a & S0b & S0c) & S1a & S1b).
  assert (RFj : CHA.rng_facts L ar (curB i E) FFj) by (apply (CHA.rng_incl L ar _ _ _ _ RF1); [apply incl_refl | rewrite HFcur; apply incl_tl, incl_refl]).
  assert (NOTCL : forall a, in_shadow_of F (ff_bytes 5) a -> ~ aclient L ar (curB i E) FFj (sp0 + CH2.ci_csp ci) (hl_scr_stack_malloc L) a).
  { intros a Ha. apply (CHA.obj_not_client L ar LY_img (curB i E) FFj _ _ F (ff_bytes 5) a RFj); [| lia | exact (CHA.mod8_of_64 _ FA) | unfold FS_BYTES in *; lia | | | | right; exact Ha].
    - unfold app_mem, FS_BYTES in *. repeat split; lia.
    - destruct S1b as [S1b|S1b]; [left | right]; unfold FS_BYTES in *; lia.
    - intros b Hb. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF1 b Hb) as (_ & _ & _ & _ & BF). specialize (BF _ (in_or_app _ _ _ (or_introl HinF))). cbn [ff_addr ff_class fst snd] in BF. lia.
    - intros f Hf. apply Q6. apply in_or_app. left. exact Hf. }
  rewrite Hpc.
  apply (SF5 fx' R' M1 model1 (curB i E) (curF i E) LK cr A F (sp0 + c0 + 32) K HH1 (proj1 Hmo1) (proj2 Hmo1) HinF Ha0' Htp).
  - rewrite Hra. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'.
  - rewrite USP. split; [exact K1|]. split; [lia|]. split; [lia|]. split; [exact K4|]. split; [|exact K6].
    intros dd m Hdd Hm. exact (L5C.writable_of_defined (hl_segs L) M1 _ _ K5 ltac:(lia) ltac:(lia) dd m Hdd Hm).
  - exact HPAT.
  - exact KNIL.
  - rewrite USP. intros R2 M2 model2 HRP _ HKEEP HDEF HGROW Hrt2 HMI2 HH2. rewrite Hra. rewrite Hrm in HH2.
    assert (Hmo2 : CHA.amodel_ok A model2) by (split; [rewrite (L5LZ.model_rt_halted _ _ Hrt2); exact (proj1 Hmo1) | exact HMI2]).
    set (nx := CH2.ci_nx ci) in *. set (E2 := CH2.retEx E' nx [] R2).
    pose proof (CH2.retEx_agree E' nx [] R2 : env_agree nx E' E2) as Hag2.
    assert (HagEE2 : env_agree NF E E2).
    { eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4]|]. eapply CC.env_agree_le; [exact Hag2 | lia]. }
    assert (HBj : curB j E2 = curB i E).
    { unfold CHA.curB. rewrite Hbeq. rewrite (CH2.den_agree nx E' E2 _ Hag2 BV), HdenB. reflexivity. }
    assert (HdenFj : CHA.denF sp0 E' (nth j FFS []) = CHA.denF sp0 E (nth j FFS [])).
    { rewrite HFi in HdenF. cbn [CHA.denF map] in HdenF. injection HdenF as _ HF2. exact HF2. }
    assert (HFj : curF j E2 = FFj).
    { unfold CHA.curF, FFj. rewrite (CHA.denF_agree sp0 nx E' E2 _ Hag2 FV), HdenFj. reflexivity. }
    assert (HP : CHA.ahpres L ar (curB i E) FFj (sp0 + CH2.ci_csp ci) (hl_scr_stack_malloc L) [] M1 M2).
    { split; [|split].
      - intros a (Ha & Hcl & _). apply (HKEEP a Ha); [|exact (fun X => NOTCL a X Hcl)].
        eapply CHA.aclient_incl; [apply incl_refl | | exact Hcl]. rewrite HFcur. apply incl_tl, incl_refl.
      - intros k Hk. apply HDEF. lia.
      - intros a _ _ Hd. exact (HGROW _ Hd). }
    apply (CONT fx' R2 A M2 model2 [] (curB i E) FFj [] eq_refl HFP (CH2.regs_preserved_kept R' R2 HRP) I HP).
    + unfold CHA.curB. rewrite HdenB. apply incl_refl.
    + unfold FFj. rewrite HdenFj. apply incl_refl.
    + intros w a [].
    + split.
      * apply (CHA.amb_callee L ar C HI HIok NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 STK SCR_pos NF32 i j E E2 A A M1 M2 model1 model2
                 (CH2.ci_csp ci) (hl_scr_stack_malloc L) (curB i E) FFj [] cr LK HA' HP).
        -- unfold CHA.curB. apply incl_appr, incl_refl.
        -- unfold FFj. apply incl_appr, incl_refl.
        -- exact Hc1.
        -- exact Hs0.
        -- exact Hc2.
        -- intros w a [].
        -- exact Hrt2.
        -- exact Hmo2.
        -- apply incl_refl.
        -- rewrite HBj, HFj. exact HH2.
        -- exact HLK1.
        -- exact HagEE2.
        -- exact (HCred E E2 cr HC1 HagEE2).
        -- rewrite HFj. unfold FFj.
           pose proof (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2)) as [_ ND].
           pose proof (ffroom_own (CHA.denF sp0 E (nth j FFS [])) FFrest LK0 LK D0 ROOM0 HLK1 ND) as G.
           unfold CHA.denF in G at 2. rewrite length_map in G. exact G.
      * apply (HXI R2 M2 model2 LK cr HRP); [|rewrite Hrm; exact HH2].
        intros a Ha Hcl Hns. exact (HKEEP a Ha Hcl Hns).
    + intros X HXn _. rewrite forallb_forall in Hnews.
      exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 (Hnews X HXn)).
Qed.
End SFree.
End CRB.
