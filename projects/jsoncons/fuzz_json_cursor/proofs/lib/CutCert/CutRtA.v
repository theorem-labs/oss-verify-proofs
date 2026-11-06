(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CRA.
Definition mem := (word -> option byte).

Lemma ivl_disj : forall A1 n1 A2 n2, 0 < n1 -> 0 < n2 -> (forall a, A1 <= a < A1 + n1 -> A2 <= a < A2 + n2 -> False) -> A1 + n1 <= A2 \/ A2 + n2 <= A1.
Proof.
  intros A1 n1 A2 n2 H1 H2 H. destruct (Z_le_dec (A1 + n1) A2) as [G|G]; [left; exact G|]. destruct (Z_le_dec (A2 + n2) A1) as [G'|G']; [right; exact G'|].
  exfalso. apply (H (Z.max A1 A2)); lia.
Qed.

Lemma nonempty_sound : forall segs E (M : mem) cells m, know_ok segs E M cells -> CH2.nonempty cells m = true -> 0 < elenZ E m.
Proof.
  intros segs E M cells m HK H. unfold CH2.nonempty in H.
  assert (G : (APC.fact_ok cells (KRange m 1 18446744073709551615) || CX.fact2_ok cells (KRange m 1 18446744073709551615))%bool = true -> 0 < elenZ E m).
  { intros F. apply orb_prop in F as [F|F]; [pose proof (APS.fact_ok_sound segs E M cells _ HK F) as X | pose proof (CX.fact2_ok_sound segs E M cells _ HK F) as X];
      cbn [kentry_ok] in X; unfold elenZ; lia. }
  destruct m; try exact (G H). apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1, H2. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
Qed.

Inductive okind : Type := OFrame (o m : Z) | OShadow (o m : Z) | OFlag.
Definition obj_of (k : Z) (a0v flv : nat) (a : saddr) (n : expr) : option okind :=
  match a, n with
  | SA (EVar v) o, ELit m =>
      if (Nat.eqb v a0v && Z.leb 0 o && Z.ltb 0 m && Z.leb (o + m) (ff_bytes k))%bool then Some (OFrame o m)
      else if (Nat.eqb v flv && Z.eqb o 0 && Z.eqb m 1)%bool then Some OFlag else None
  | SA (EAlu Instr.ALU_SRL (EVar v) (ELit 3)) o, ELit m =>
      if (Nat.eqb v a0v && Z.leb SB o && Z.ltb 0 m && Z.leb (o - SB + m) (ff_bytes k / 8))%bool then Some (OShadow (o - SB) m) else None
  | _, _ => None
  end.
Lemma obj_sh_bounds : forall k a0v flv a n o m, obj_of k a0v flv a n = Some (OShadow o m) -> 0 <= o /\ 0 < m /\ o + m <= ff_bytes k / 8.
Proof.
  intros k a0v flv [b ao] n o m H. unfold obj_of in H. destruct b as [z0|v|op e1 e2| | | | |]; try discriminate.
  - destruct n as [mm| | | | | | |]; try discriminate.
    destruct (Nat.eqb v a0v && Z.leb 0 ao && Z.ltb 0 mm && Z.leb (ao + mm) (ff_bytes k))%bool; [discriminate|].
    destruct (Nat.eqb v flv && Z.eqb ao 0 && Z.eqb mm 1)%bool; discriminate.
  - destruct op; try discriminate. destruct e1 as [|v| | | | | |]; try discriminate. destruct e2 as [z| | | | | | |]; try discriminate.
    destruct z as [|p|]; try discriminate. destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate.
    destruct n as [mm| | | | | | |]; try discriminate.
    destruct (Nat.eqb v a0v && Z.leb SB ao && Z.ltb 0 mm && Z.leb (ao - SB + mm) (ff_bytes k / 8))%bool eqn:C1; [|discriminate]. injection H as <- <-.
    apply andb_prop in C1 as [C1 X4]. apply andb_prop in C1 as [C1 X3]. apply andb_prop in C1 as [X1 X2]. apply Z.leb_le in X2, X4. apply Z.ltb_lt in X3. lia.
Qed.
Definition ivl (F fl : Z) (kd : okind) : Z * Z :=
  match kd with OFrame o m => (F + o, m) | OShadow o m => (S F + o, m) | OFlag => (fl, 1) end.
Definition is_bigsh (a : saddr) (n : expr) : bool :=
  match a, n with SA (ELit 0) lo, ELit m => (Z.eqb lo BIGSHADOW_LO && Z.eqb m (BIGSHADOW_HI - BIGSHADOW_LO))%bool | _, _ => false end.

Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable IMGHI : Z.
Hypothesis LY_imghi : IMGHI <= hl_img_hi L /\ hl_img_lo L < FS_BYTES.
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
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LBrest FFrest sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.

Definition partner_ok (cells : list kentry) (nx : nat) (BLi : CA.blocks) (FLi : list (expr * Z * Z)) (a : saddr) (n : expr) : bool :=
  let '(SA b o) := a in
  (CH2.nonempty cells n && APC.expr_vars_lt nx b && APC.expr_vars_lt nx n && CH.within cells (CHA.keepc_regs d 0 0 BLi FLi) b o n)%bool.
Definition isS {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition smalloc_fact_ok (cells : list kentry) (nx : nat) (BLi : CA.blocks) (FLi : list (expr * Z * Z)) (k : Z) (a0v flv : nat) (X : kentry) : bool :=
  let B := ff_bytes k in
  match X with
  | KRange (EVar v) lo hi => ((Nat.eqb v a0v && Z.leb lo IMGHI && Z.leb (2 ^ 47 - 8388608 - B) hi) || (Nat.eqb v flv && Z.leb lo IMGHI && Z.leb (2 ^ 47 - 8388608 - 1) hi))%bool
  | KAlign (EVar v) m => (Nat.eqb v a0v && Z.ltb 0 m && Z.eqb (B mod m) 0)%bool
  | KUnk a n | KWr a n => isS (obj_of k a0v flv a n)
  | KZero a n => match obj_of k a0v flv a n with Some (OShadow _ _) => true | _ => false end
  | KWord (SA (EVar v) o) 8 (EVar w) => (Nat.eqb v a0v && Z.eqb o (B - 8) && Nat.eqb w flv)%bool
  | KDisj a1 n1 a2 n2 =>
      match obj_of k a0v flv a1 n1, obj_of k a0v flv a2 n2 with
      | Some (OFrame _ _), Some OFlag | Some OFlag, Some (OFrame _ _) => true
      | Some _, None => partner_ok cells nx BLi FLi a2 n2
      | None, Some kd => (partner_ok cells nx BLi FLi a1 n1 || (is_bigsh a1 n1 && match kd with OShadow _ _ => false | _ => true end))%bool
      | _, _ => false
      end
  | _ => false
  end.

Section Sound.
Variables (E' E2 : env) (nx : nat) (cells : list kentry) (BLi : CA.blocks) (FLi : list (expr * Z * Z)) (k : Z) (a0v flv : nat).
Variables (M' M2 : mem) (A A2 : list (Z * Z)) (model' model2 : Model) (LB : list (Z * Z)) (FF LK LK' : list fframe) (cr : credit) (F fl rs : Z).
Hypothesis HagE' : env_agree NF E0 E'.
Hypothesis Hag2 : env_agree nx E' E2.
Hypothesis HK : know_ok (hl_segs L) E' (CCA.vis A model' M') cells.
Hypothesis HH : ri_inv HI LB FF LK cr A M' (vml_of model').
Hypothesis HLB : LB = CH2.den E' BLi ++ LBrest.
Hypothesis HFF : FF = CHA.denF sp0 E' FLi ++ FFrest.
Hypothesis Hk : In k PM_FS_CLASSES.
Hypothesis HvF : CL5A.uv E2 (EVar a0v) = F.
Hypothesis Hvfl : CL5A.uv E2 (EVar flv) = fl.
Hypothesis P1 : ar_fs ar <= F /\ F + ff_bytes k <= ar_fs ar + FS_BYTES /\ F mod ff_bytes k = 0 /\ app_mem F (ff_bytes k) /\ F + ff_bytes k <= ahl_ceil ar.
Hypothesis P2 : F + ff_bytes k <= hl_img_lo L \/ hl_img_hi L <= F.
Hypothesis P3 : fframes_apart F (ff_bytes k) (FF ++ LK').
Hypothesis P4 : forall b, In b LB -> F + ff_bytes k <= fst b \/ fst b + snd b <= F.
Hypothesis P5 : HeapIface.defined M2 F (ff_bytes k).
Hypothesis P6 : cell_is (hl_segs L) M2 (F + ff_bytes k - 8) 8 fl.
Hypothesis P7 : ar_fs ar <= fl < ar_fs ar + FS_BYTES.
Hypothesis P8 : ~ aclient L ar LB ((F, k, rs) :: FF) 0 0 fl.
Hypothesis P9 : F + ff_bytes k <= fl \/ fl + 1 <= F.
Hypothesis P10 : shadow_zero M2 F (ff_bytes k / 8).
Hypothesis HH2 : ri_inv HI LB ((F, k, rs) :: FF) LK' cr A2 M2 (vml_of model2).

Let B := ff_bytes k.
Lemma Bfacts : 64 <= B <= 2048 /\ B mod 64 = 0.
Proof. exact (CHA.frame_class_facts k Hk). Qed.
Lemma fs_facts : 0 <= ar_fs ar /\ hl_img_hi L <= ar_fs ar /\ ar_fs ar + FS_BYTES <= ahl_ceil ar /\ (ar_fs ar + FS_BYTES <= BIGSHADOW_LO \/ BIGSHADOW_HI <= ar_fs ar)
  /\ 0x7fff7f800000 <= ahl_ceil ar /\ ar_sptop ar <= 2 ^ 47 /\ ahl_ceil ar mod 8 = 0.
Proof.
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as RFx.
  destruct (CHA.rf_fs _ _ _ _ RFx) as ((F0 & F1 & F2) & F3 & F4). destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & _).
  destruct LY_imghi as (_ & I2). unfold FS_BYTES in *. repeat split; lia.
Qed.
Lemma F8 : F mod 8 = 0.
Proof.
  destruct P1 as (_ & _ & FB & _). destruct Bfacts as (_ & B64). fold B in FB. apply Z.mod_divide in FB; [|pose proof Bfacts; lia]. destruct FB as [q Hq].
  apply Z.mod_divide in B64; [|lia]. destruct B64 as [p Hp]. rewrite Hq, Hp. replace (q * (p * 64)) with ((q * p * 8) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma obj_sem : forall a n kd, obj_of k a0v flv a n = Some kd ->
  let '(lo, len) := ivl F fl kd in
  estart E2 a = lo /\ elenZ E2 n = len /\ 0 < len /\ 0 <= lo /\ lo + len <= 2 ^ 64.
Proof.
  intros [b o] n kd H. pose proof Bfacts as (BR & _). destruct fs_facts as (S0 & S1 & S2 & S3 & S4 & S5 & S6). destruct P1 as (Q1 & Q2 & _ & _ & Q5). fold B in Q2, Q5.
  unfold obj_of in H. destruct b as [z0|v|op e1 e2| | | | |]; try discriminate.
  - destruct n as [m| | | | | | |]; try discriminate.
    destruct (Nat.eqb v a0v && Z.leb 0 o && Z.ltb 0 m && Z.leb (o + m) (ff_bytes k))%bool eqn:C1.
    + injection H as <-. apply andb_prop in C1 as [C1 X4]. apply andb_prop in C1 as [C1 X3]. apply andb_prop in C1 as [X1 X2].
      apply Nat.eqb_eq in X1. apply Z.leb_le in X2, X4. apply Z.ltb_lt in X3. subst v. fold B in X4. cbn [ivl].
      unfold estart, elenZ. cbn [a_base a_off edenot]. unfold CL5A.uv in HvF. cbn [edenot] in HvF. rewrite HvF. rewrite u64_of_Z by lia. repeat split; lia.
    + destruct (Nat.eqb v flv && Z.eqb o 0 && Z.eqb m 1)%bool eqn:C2; [|discriminate]. injection H as <-.
      apply andb_prop in C2 as [C2 X3]. apply andb_prop in C2 as [X1 X2]. apply Nat.eqb_eq in X1. apply Z.eqb_eq in X2, X3. subst v o m. cbn [ivl].
      unfold estart, elenZ. cbn [a_base a_off edenot]. unfold CL5A.uv in Hvfl. cbn [edenot] in Hvfl. rewrite Hvfl. rewrite u64_of_Z by lia. unfold FS_BYTES in *. repeat split; lia.
  - destruct op; try discriminate. destruct e1 as [|v| | | | | |]; try discriminate. destruct e2 as [z| | | | | | |]; try discriminate.
    destruct z as [|p|]; try discriminate. destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate.
    destruct n as [m| | | | | | |]; try discriminate.
    destruct (Nat.eqb v a0v && Z.leb SB o && Z.ltb 0 m && Z.leb (o - SB + m) (ff_bytes k / 8))%bool eqn:C1; [|discriminate]. injection H as <-.
    apply andb_prop in C1 as [C1 X4]. apply andb_prop in C1 as [C1 X3]. apply andb_prop in C1 as [X1 X2].
    apply Nat.eqb_eq in X1. apply Z.leb_le in X2, X4. apply Z.ltb_lt in X3. subst v. fold B in X4. cbn [ivl].
    pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). assert (F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    assert (B / 8 <= 256) by (apply Z.div_le_upper_bound; lia).
    change (EAlu ALU_SRL (EVar a0v) (ELit 3)) with (CHA.SRL3 (EVar a0v)). rewrite CL5A.estart_srl3, HvF. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by (unfold SB in *; lia).
    unfold S, SB in *. repeat split; lia.
Qed.

Lemma obj_in : forall kd a n x, obj_of k a0v flv a n = Some kd -> fst (ivl F fl kd) <= x < fst (ivl F fl kd) + snd (ivl F fl kd) ->
  match kd with OFrame _ _ => F <= x < F + B | OShadow _ _ => in_shadow_of F B x | OFlag => x = fl end.
Proof.
  intros kd [b o] n x H Hx. pose proof Bfacts as (BR & B64). unfold obj_of in H. destruct b as [z0|v|op e1 e2| | | | |]; try discriminate.
  - destruct n as [m| | | | | | |]; try discriminate.
    destruct (Nat.eqb v a0v && Z.leb 0 o && Z.ltb 0 m && Z.leb (o + m) (ff_bytes k))%bool eqn:C1.
    + injection H as <-. apply andb_prop in C1 as [C1 X4]. apply andb_prop in C1 as [C1 X3]. apply andb_prop in C1 as [X1 X2].
      apply Z.leb_le in X2, X4. apply Z.ltb_lt in X3. fold B in X4. cbn [ivl fst snd] in Hx. lia.
    + destruct (Nat.eqb v flv && Z.eqb o 0 && Z.eqb m 1)%bool; [|discriminate]. injection H as <-. cbn [ivl fst snd] in Hx. lia.
  - destruct op; try discriminate. destruct e1 as [|v| | | | | |]; try discriminate. destruct e2 as [z| | | | | | |]; try discriminate.
    destruct z as [|p|]; try discriminate. destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate.
    destruct n as [m| | | | | | |]; try discriminate.
    destruct (Nat.eqb v a0v && Z.leb SB o && Z.ltb 0 m && Z.leb (o - SB + m) (ff_bytes k / 8))%bool eqn:C1; [|discriminate]. injection H as <-.
    apply andb_prop in C1 as [C1 X4]. apply andb_prop in C1 as [C1 X3]. apply andb_prop in C1 as [X1 X2].
    apply Z.leb_le in X2, X4. apply Z.ltb_lt in X3. fold B in X4. cbn [ivl fst snd] in Hx.
    replace B with (8 * (B / 8)) by (apply Z.mod_divide in B64; [|lia]; destruct B64 as [q ->]; replace (q * 64) with ((q * 8) * 8) by lia; rewrite Z.div_mul by lia; lia).
    apply (CL5A.shreg_in_shadow F (B / 8) x F8); [apply Z.div_str_pos; lia | unfold S in Hx; lia].
Qed.

Lemma in_new_ff : In (F, k, rs) ((F, k, rs) :: FF). Proof. left; reflexivity. Qed.
Lemma obj_defvis : forall kd a n x, obj_of k a0v flv a n = Some kd -> fst (ivl F fl kd) <= x < fst (ivl F fl kd) + snd (ivl F fl kd) ->
  M2 (Z_to_bv 64 x) <> None /\ ahid A2 model2 (Z_to_bv 64 x) = false.
Proof.
  intros kd a n x H Hx. pose proof (obj_in kd a n x H Hx) as HI'. pose proof Bfacts as (BR & B64). destruct fs_facts as (S0 & S1 & S2 & S3 & S4 & S5 & S6).
  destruct P1 as (Q1 & Q2 & _ & _ & Q5). fold B in Q2, Q5. pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) as WF2.
  destruct kd as [o m|o m|].
  - split; [replace x with (F + (x - F)) by lia; apply P5; fold B; lia|]. apply (CHA.fs_vis L ar C HI HIok NF 0 NF32 _ _ _ _ _ _ model2 x HH2); unfold FS_BYTES in *; lia.
  - pose proof (CHA.shadow_range F B x ltac:(lia) ltac:(lia) ltac:(lia) HI') as SRx. split.
    + destruct HI' as [I1 I2]. assert (Hj : 0 <= x - S F < B / 8).
      { split; [lia|]. unfold S in *. apply Z.mod_divide in B64; [|lia]. destruct B64 as [q Hq]. pose proof F8 as F8'. apply Z.mod_divide in F8'; [|lia]. destruct F8' as [p Hp].
        assert (E1 : (F + B - 1) / 8 = p + q * 8 - 1) by (symmetry; apply (Zdiv_unique _ 8 _ 7); lia).
        assert (E2' : F / 8 = p) by (rewrite Hp; apply Z.div_mul; lia). assert (E3 : B / 8 = q * 8) by (rewrite Hq; replace (q * 64) with ((q * 8) * 8) by lia; apply Z.div_mul; lia). lia. }
      pose proof (P10 (x - S F) Hj) as Bz. unfold byte_at in Bz. replace (S F + (x - S F)) with x in Bz by lia. rewrite Bz. discriminate.
    + apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model2 0 0 x HH2); [lia | | ].
      * right; right; right; right; right; left. exists (F, k, rs). split; [exact in_new_ff | exact HI'].
      * apply (CL5A.not_stk_shadow_sh L ar LB ((F, k, rs) :: FF) F B x (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF2)); [lia | lia | lia | exact HI'].
  - subst x. split; [|apply (CHA.fs_vis L ar C HI HIok NF 0 NF32 _ _ _ _ _ _ model2 fl HH2); unfold FS_BYTES in *; lia].
    pose proof (CHA.wf_fs_def _ _ _ _ _ _ _ _ WF2) as FD. replace fl with (ar_fs ar + (fl - ar_fs ar)) by lia. apply FD. lia.
Qed.

Lemma obj_not_cl : forall kd a n x, obj_of k a0v flv a n = Some kd -> fst (ivl F fl kd) <= x < fst (ivl F fl kd) + snd (ivl F fl kd) -> ~ aclient L ar LB FF 0 0 x.
Proof.
  intros kd a n x H Hx. pose proof (obj_in kd a n x H Hx) as HI'. pose proof Bfacts as (BR & B64). destruct fs_facts as (S0 & S1 & S2 & S3 & S4 & S5 & S6).
  destruct P1 as (Q1 & Q2 & _ & Q4 & Q5). fold B in Q2, Q4, Q5. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as RFx.
  assert (FA : fframes_apart F B FF) by (intros f Hf; apply P3; apply in_or_app; left; exact Hf).
  destruct kd as [o m|o m|].
  - exact (CHA.obj_not_client L ar LY_img LB FF 0 0 F B x RFx Q4 ltac:(lia) F8 Q5 P2 P4 FA (or_introl HI')).
  - exact (CHA.obj_not_client L ar LY_img LB FF 0 0 F B x RFx Q4 ltac:(lia) F8 Q5 P2 P4 FA (or_intror HI')).
  - subst x. intros Hc. apply P8. eapply CHA.aclient_incl; [apply incl_refl | apply incl_tl, incl_refl | exact Hc].
Qed.

Lemma partner_sem : forall a n x, partner_ok cells nx BLi FLi a n = true ->
  0 < elenZ E2 n /\ (estart E2 a <= x < estart E2 a + elenZ E2 n -> 0 <= x < 2 ^ 64 -> aclient L ar LB FF 0 0 x).
Proof.
  intros [b o] n x H. unfold partner_ok in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  assert (Eb : estart E2 (SA b o) = estart E' (SA b o)) by (exact (CL5A.estart_agree nx E' E2 b o Hag2 H2)).
  assert (En : elenZ E2 n = elenZ E' n) by (unfold elenZ; rewrite (SR.edenot_agree_AP nx E' E2 n Hag2 H3); reflexivity).
  rewrite Eb, En. split; [exact (nonempty_sound (hl_segs L) E' _ cells n HK H1)|]. intros Hx Hr.
  destruct (CHA.within_sem L NF 0 NF32 E' _ cells _ b o n HK H4) as (r & Hr' & Hs). specialize (Hs x Hx).
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as RFx.
  destruct (CHA.keepc_regs_sem L ar NF E0 LBrest FFrest sp0 d Wo STK SCR_pos NF32 SP0 Wo_ok CRS_ok WRS_ok E' BLi FLi LB FF 0 0 r x HagE' RFx
              ltac:(rewrite HLB; apply incl_refl) ltac:(rewrite HFF; apply incl_refl) ltac:(lia) ltac:(lia) ltac:(lia) Hr Hr' Hs) as (G & _).
  rewrite <- HLB, <- HFF in G. eapply CHA.aclient_scr; [exact G | intros y Hy; lia].
Qed.

Lemma smalloc_fact_sound : forall X, smalloc_fact_ok cells nx BLi FLi k a0v flv X = true -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X.
Proof.
  intros X H. pose proof Bfacts as (BR & B64). destruct fs_facts as (S0 & S1 & S2 & S3 & S4 & S5 & S6). pose proof P1 as (Q1 & Q2 & Q3 & Q4 & Q5). fold B in Q2, Q3, Q4, Q5.
  destruct LY_imghi as (I1 & I2). unfold smalloc_fact_ok in H. fold B in H.
  assert (DEFV : forall kd a n, obj_of k a0v flv a n = Some kd -> L5.defined (CCA.vis A2 model2 M2) (estart E2 a) (elenZ E2 n) /\ flat E2 a (elenZ E2 n)).
  { intros kd a n Ho. pose proof (obj_sem a n kd Ho) as OS. destruct (ivl F fl kd) as [lo len] eqn:Ei. destruct OS as (O1 & O2 & O3 & O4 & O5). rewrite O1, O2. split.
    - intros i Hi. destruct (obj_defvis kd a n (lo + i) Ho ltac:(rewrite Ei; cbn [fst snd]; lia)) as (G1 & G2). unfold CCA.vis. rewrite (CL5A.vis_eq _ M2 _ G2). exact G1.
    - unfold flat. rewrite O1. lia. }
  destruct X as [[b o] w v|a n|a n kk|lo hi|e m|e lo hi|a n|a1 n1 a2 n2|a n c0|a n]; try discriminate.
  -
    destruct b as [|vb| | | | | |]; try discriminate. destruct w as [|[|[|[|[|[|[|[|[|w]]]]]]]]]; try discriminate. destruct v as [|vw| | | | | |]; try discriminate.
    apply andb_prop in H as [H X3]. apply andb_prop in H as [X1 X2]. apply Nat.eqb_eq in X1, X3. apply Z.eqb_eq in X2. subst vb o vw.
    eapply CL5.kword64_intro with (A := F + B - 8) (z := fl).
    + unfold estart. cbn [a_base a_off edenot]. unfold CL5A.uv in HvF. cbn [edenot] in HvF. rewrite HvF. lia.
    + lia.
    + lia.
    + cbn [edenot]. unfold CL5A.uv in Hvfl. cbn [edenot] in Hvfl. rewrite <- Hvfl. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + apply (CL5A.u64_vis (hl_segs L)); [lia | lia | | exact P6]. intros i Hi.
      apply (CHA.fs_vis L ar C HI HIok NF 0 NF32 _ _ _ _ _ _ model2 (F + B - 8 + i) HH2); unfold FS_BYTES in *; lia.
  -
    destruct (obj_of k a0v flv a n) as [[o m|o m|]|] eqn:Ho; try discriminate.
    pose proof (obj_sem a n _ Ho) as OS. cbn [ivl] in OS. destruct OS as (O1 & O2 & O3 & O4 & O5). destruct (DEFV _ a n Ho) as (_ & FL).
    cbn [kentry_ok]. split; [exact FL|]. rewrite O1, O2. intros i Hi.
    destruct (obj_defvis _ a n (S F + o + i) Ho ltac:(cbn [ivl fst snd]; lia)) as (_ & G2). unfold CCA.vis. rewrite (CL5A.vis_eq _ M2 _ G2).
    assert (Hj : 0 <= o + i < B / 8) by (destruct (obj_sh_bounds k a0v flv a n o m Ho) as (J1 & J2 & J3); fold B in J3; lia).
    pose proof (P10 (o + i) Hj) as Bz. unfold byte_at in Bz. replace (S F + (o + i)) with (S F + o + i) in Bz by lia. exact Bz.
  -
    destruct e as [|v| | | | | |]; try discriminate. apply andb_prop in H as [H X3]. apply andb_prop in H as [X1 X2]. apply Nat.eqb_eq in X1. apply Z.ltb_lt in X2. apply Z.eqb_eq in X3. subst v.
    cbn [kentry_ok]. split; [exact X2|]. unfold CL5A.uv in HvF. rewrite HvF.
    apply Z.mod_divide in X3; [|lia]. destruct X3 as [q Hq]. apply Z.mod_divide in Q3; [|lia]. destruct Q3 as [p Hp]. rewrite Hp, Hq. replace (p * (q * m)) with ((p * q) * m) by lia. apply Z_mod_mult.
  -
    destruct e as [|v| | | | | |]; try discriminate. cbn [kentry_ok edenot]. apply orb_prop in H as [H|H]; apply andb_prop in H as [H X3]; apply andb_prop in H as [X1 X2];
      apply Nat.eqb_eq in X1; apply Z.leb_le in X2, X3; subst v.
    + unfold CL5A.uv in HvF. cbn [edenot] in HvF. rewrite HvF. lia.
    + unfold CL5A.uv in Hvfl. cbn [edenot] in Hvfl. rewrite Hvfl. unfold FS_BYTES in *. lia.
  -
    destruct (obj_of k a0v flv a n) as [kd|] eqn:Ho; [|discriminate]. destruct (DEFV kd a n Ho) as (DF & FL). cbn [kentry_ok]. split; [exact FL|].
    intros dd mm Hdd Hmm. exact (kunk_store_ok (hl_segs L) E2 _ a n dd mm (conj FL DF) Hdd Hmm).
  -
    cbn [kentry_ok].
    assert (PO : forall kd ao no ap np, obj_of k a0v flv ao no = Some kd -> partner_ok cells nx BLi FLi ap np = true ->
                 estart E2 ao + elenZ E2 no <= estart E2 ap \/ estart E2 ap + elenZ E2 np <= estart E2 ao).
    { intros kd ao no ap np Ho Hp. pose proof (obj_sem ao no kd Ho) as OS. destruct (ivl F fl kd) as [lo len] eqn:Ei. destruct OS as (O1 & O2 & O3 & O4 & O5).
      destruct (partner_sem ap np 0 Hp) as (PN & _). apply ivl_disj; [lia | exact PN |]. intros x Hx1 Hx2.
      destruct (partner_sem ap np x Hp) as (_ & PC). apply (obj_not_cl kd ao no x Ho ltac:(rewrite Ei; cbn [fst snd]; lia)). apply PC; [exact Hx2 | lia]. }
    destruct (obj_of k a0v flv a1 n1) as [k1|] eqn:Ho1; destruct (obj_of k a0v flv a2 n2) as [k2|] eqn:Ho2.
    +
      pose proof (obj_sem a1 n1 k1 Ho1) as OS1. pose proof (obj_sem a2 n2 k2 Ho2) as OS2.
      destruct k1 as [o1 m1|o1 m1|]; destruct k2 as [o2 m2|o2 m2|]; try discriminate; cbn [ivl] in OS1, OS2;
        destruct OS1 as (O1 & O2 & _); destruct OS2 as (O1' & O2' & _); rewrite O1, O2, O1', O2'.
      * pose proof (obj_in _ a1 n1 (F + o1) Ho1 ltac:(cbn [ivl fst snd]; pose proof (obj_sem a1 n1 _ Ho1) as Z0; cbn [ivl] in Z0; lia)) as I1'.
        pose proof (obj_in _ a1 n1 (F + o1 + m1 - 1) Ho1 ltac:(cbn [ivl fst snd]; pose proof (obj_sem a1 n1 _ Ho1) as Z0; cbn [ivl] in Z0; lia)) as I2'. cbn beta iota in I1', I2'. fold B in P9. lia.
      * pose proof (obj_in _ a2 n2 (F + o2) Ho2 ltac:(cbn [ivl fst snd]; pose proof (obj_sem a2 n2 _ Ho2) as Z0; cbn [ivl] in Z0; lia)) as I1'.
        pose proof (obj_in _ a2 n2 (F + o2 + m2 - 1) Ho2 ltac:(cbn [ivl fst snd]; pose proof (obj_sem a2 n2 _ Ho2) as Z0; cbn [ivl] in Z0; lia)) as I2'. cbn beta iota in I1', I2'. fold B in P9. lia.
    + destruct k1; exact (PO _ a1 n1 a2 n2 Ho1 H).
    + apply orb_prop in H as [H|H]; [pose proof (PO _ a2 n2 a1 n1 Ho2 H) as G; lia|]. apply andb_prop in H as [H1 H2].
      destruct a1 as [b1 o1]. destruct b1 as [z| | | | | | |]; try discriminate. destruct z; try discriminate. destruct n1 as [m1| | | | | | |]; try discriminate.
      cbn [is_bigsh] in H1. apply andb_prop in H1 as [X1 X2]. apply Z.eqb_eq in X1, X2. subst o1 m1.
      pose proof (obj_sem a2 n2 k2 Ho2) as OS2. unfold estart at 1 4, elenZ at 1. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0) by lia. rewrite u64_of_Z by (unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
      destruct Q4 as (_ & Q4' & _). unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
      destruct k2 as [o2 m2|o2 m2|]; try discriminate; cbn [ivl] in OS2; destruct OS2 as (O1' & O2' & O3' & _); rewrite O1', O2'.
      * pose proof (obj_in _ a2 n2 (F + o2) Ho2 ltac:(cbn [ivl fst snd]; lia)) as I1'. pose proof (obj_in _ a2 n2 (F + o2 + m2 - 1) Ho2 ltac:(cbn [ivl fst snd]; lia)) as I2'. cbn beta iota in I1', I2'. lia.
      * lia.
    + discriminate.
  -
    destruct (obj_of k a0v flv a n) as [kd|] eqn:Ho; [|discriminate]. destruct (DEFV kd a n Ho) as (DF & FL). cbn [kentry_ok]. split; [exact FL | exact DF].
Qed.
End Sound.

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

Record sm_facts (k : Z) (LB : list (Z * Z)) (FF LK' : list fframe) (sp scr : Z) (M1 M2 : mem) (F fl : Z) : Prop := SMF {
  smf_rng : ar_fs ar <= F /\ F + ff_bytes k <= ar_fs ar + FS_BYTES /\ F mod ff_bytes k = 0 /\ app_mem F (ff_bytes k) /\ F + ff_bytes k <= ahl_ceil ar;
  smf_img : F + ff_bytes k <= hl_img_lo L \/ hl_img_hi L <= F;
  smf_fap : fframes_apart F (ff_bytes k) (FF ++ LK');
  smf_bap : forall b, In b LB -> F + ff_bytes k <= fst b \/ fst b + snd b <= F;
  smf_def : HeapIface.defined M2 F (ff_bytes k);
  smf_cell : cell_is (hl_segs L) M2 (F + ff_bytes k - 8) 8 fl;
  smf_flr : ar_fs ar <= fl < ar_fs ar + FS_BYTES;
  smf_flnc : ~ aclient L ar LB ((F, k, sp + 32) :: FF) 0 0 fl;
  smf_flap : F + ff_bytes k <= fl \/ fl + 1 <= F;
  smf_shz : shadow_zero M2 F (ff_bytes k / 8);
  smf_pres : aheap_pres L ar LB FF sp scr M1 M2 }.

Lemma smalloc_leaf : forall k news i c ps j cj ci,
  In k PM_FS_CLASSES -> nth_error CPS j = Some cj ->
  CHA.custom_chk NF d SCELLS GLO GHI (hl_scr_stack_malloc L) 1 (nth i BLS []) (nth i FFS []) [] news None c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  SR.ps_pc ps = hl_stack_malloc L k ->
  CHA.frames_eqb (nth j FFS []) ((EVar (CH2.ci_nx ci + 5), k, CH2.ci_csp ci) :: nth i FFS []) = true ->
  CH2.blocks_eqb (nth j BLS []) (nth i BLS []) = true ->
  forallb (fun X => (CHA.static_chk SCELLS GLO GHI X || smalloc_fact_ok (SR.ps_cells ps) (CH2.ci_nx ci) (nth i BLS []) (nth i FFS []) k (CH2.ci_nx ci + 5) (CH2.ci_nx ci) X)%bool) news = true ->
  2 <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (forall E E2 cr, Cred i E cr -> env_agree NF E E2 -> Cred j E2 cr) ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AMBX i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> CCA.IH (hl_segs L) CPS AMBX K FPI (CC.meas c E) ->
    (forall R2 M2 model2 F fl LK' cr, regs_preserved R' R2 -> getr R2 10%bv = Z_to_bv 64 F ->
        sm_facts k (curB i E) (curF i E) LK' (sp0 + CH2.ci_csp ci) (hl_scr_stack_malloc L) M1 M2 F fl ->
        ri_inv HI (curB i E) ((F, k, sp0 + CH2.ci_csp ci + 32) :: curF i E) LK' cr A M2 (vml_of model2) ->
        XI j (CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 fl] R2) A M2 model2) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros k news i c ps j cj ci Hk Hcj Hchk Hpc Hfeq Hbeq Hnews Hroom HCred fx' E R A M model E' R' M1 model1 HAt [HA HX] HFP Hag HLF HIH HXI.
  destruct (CHA.custom_ret L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0
              CRS_ok WRS_ok IMG_ok CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XI (hl_scr_stack_malloc L) 1%nat (nth i BLS []) (nth i FFS []) [] news None i c ps j cj ci Hcj Hchk
              E R A M model E' R' M1 model1 HAt HA Hag HLF HIH) as [CF CONT].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  pose proof HA' as (Hmo1 & Hrt1 & HA01 & HagE & (cr & LK & HH1 & HLK1 & HC1 & HRoom1) & Hfr1 & Hdf1).
  apply CHA.frames_eqb_eq in Hfeq. apply CH2.blocks_eqb_eq in Hbeq.
  assert (CHK2 : CH2.blocks_vars_lt (CH2.ci_nx ci) (nth i BLS []) = true /\ CHA.frames_vars_lt (CH2.ci_nx ci) (nth i FFS []) = true).
  { unfold CHA.custom_chk in Hchk. destruct (CHA.common_chk NF d (hl_scr_stack_malloc L) 1 c ps cj (nth i BLS []) (nth i FFS [])) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb Z5].
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Z2]. split; assumption. }
  destruct CHK2 as [BV FV].
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1)) as RF1.
  destruct (CHA.rf_ceil _ _ _ _ RF1) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RF1) as (SP1 & _). pose proof Hstk as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (USP : bv_unsigned (getr R' 2%bv) = sp0 + CH2.ci_csp ci) by (rewrite Hsp; apply u64_of_Z; lia).
  rewrite Hpc.
  apply (PmHeapIfaceA.aio_stack_malloc _ _ _ _ _ HIok k Hk fx' R' M1 model1 (curB i E) (curF i E) LK cr A K HH1 (proj1 Hmo1) (proj2 Hmo1) Htp).
  - rewrite Hra. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'.
  - rewrite USP. split; [exact K1|]. split; [lia|]. split; [lia|]. split; [exact K4|]. split; [|exact K6].
    intros dd m Hdd Hm. exact (L5C.writable_of_defined (hl_segs L) M1 _ _ K5 ltac:(lia) ltac:(lia) dd m Hdd Hm).
  - unfold ff_room. specialize (HRoom1 k Hk). lia.
  - rewrite USP. exact Hffrs.
  - exact KNIL.
  - rewrite USP. intros R2 M2 model2 F fl LK' Ha0 HRP Q1 Q2 Q3 Q4 HLK' Q5 Q6 Q7 Q8 Q9 Qst Q10 HPres Hrt2 HMI2 HH2. rewrite Hra.
    assert (Hmo2 : CHA.amodel_ok A model2) by (split; [rewrite (L5LZ.model_rt_halted _ _ Hrt2); exact (proj1 Hmo1) | exact HMI2]).
    set (nx := CH2.ci_nx ci) in *. set (E2 := CH2.retEx E' nx [Z_to_bv 64 fl] R2).
    pose proof (CH2.retEx_agree E' nx [Z_to_bv 64 fl] R2 : env_agree nx E' E2) as Hag2.
    assert (HagEE2 : env_agree NF E E2).
    { eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4]|]. eapply CC.env_agree_le; [exact Hag2 | lia]. }
    assert (FR : 0 <= F < 2 ^ 64) by (destruct Q1 as (G1 & G2 & _ & (G0 & _) & G5); pose proof (CHA.frame_class_facts k Hk); lia).
    assert (HvF : CL5A.uv E2 (EVar (nx + 5)) = F).
    { unfold CL5A.uv. cbn [edenot]. pose proof (CH2.retEx_a0 E' nx [Z_to_bv 64 fl] R2) as G. cbn [length] in G. replace (nx + 1 + 4)%nat with (nx + 5)%nat in G by lia.
      unfold E2. rewrite G, Ha0. apply u64_of_Z. exact FR. }
    assert (Hvfl : CL5A.uv E2 (EVar nx) = fl).
    { unfold CL5A.uv. cbn [edenot]. pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 fl] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. cbn [nth] in G.
      unfold E2. rewrite G. apply u64_of_Z. destruct (CHA.rf_fs _ _ _ _ RF1) as ((G0 & _) & G3 & _). unfold FS_BYTES in *. lia. }
    assert (HBj : curB j E2 = curB i E).
    { unfold CHA.curB. rewrite Hbeq. rewrite (CH2.den_agree nx E' E2 _ Hag2 BV), HdenB. reflexivity. }
    assert (HFj : curF j E2 = (F, k, sp0 + CH2.ci_csp ci + 32) :: curF i E).
    { unfold CHA.curF. rewrite Hfeq. unfold CHA.denF at 1. cbn [map fst snd app]. fold (CHA.denF sp0 E2 (nth i FFS [])).
      unfold CL5A.uv in HvF. rewrite HvF. rewrite (CHA.denF_agree sp0 nx E' E2 _ Hag2 FV), HdenF. reflexivity. }
    apply (CONT fx' R2 A M2 model2 [Z_to_bv 64 fl] (curB i E) (curF i E) [] eq_refl HFP (CH2.regs_preserved_kept R' R2 HRP) I (CHA.ahpres_of_aheap_pres _ _ _ _ _ _ _ _ HPres)).
    + unfold CHA.curB. rewrite HdenB. apply incl_refl.
    + unfold CHA.curF. rewrite HdenF. apply incl_refl.
    + intros w a [].
    + split.
      * apply (CHA.amb_callee L ar C HI HIok NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 STK SCR_pos NF32 i j E E2 A A M1 M2 model1 model2
                 (CH2.ci_csp ci) (hl_scr_stack_malloc L) (curB i E) (curF i E) [] cr LK' HA' (CHA.ahpres_of_aheap_pres _ _ _ _ _ _ _ _ HPres)).
        -- unfold CHA.curB. apply incl_appr, incl_refl.
        -- unfold CHA.curF. apply incl_appr, incl_refl.
        -- exact Hc1.
        -- exact Hs0.
        -- exact Hc2.
        -- intros w a [].
        -- exact Hrt2.
        -- exact Hmo2.
        -- apply incl_refl.
        -- rewrite HBj, HFj. exact HH2.
        -- exact (incl_tran HLK' HLK1).
        -- exact HagEE2.
        -- exact (HCred E E2 cr HC1 HagEE2).
        -- rewrite HFj, Hfeq. cbn [length]. pose proof (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2)) as [_ ND].
           pose proof (CHA.ffroom_push NF 0 NF32 _ _ _ (F, k, sp0 + CH2.ci_csp ci + 32) _ HRoom1 HLK' ND) as G.
           replace (D0 - Z.of_nat (Datatypes.S (length (nth i FFS [])))) with (D0 - Z.of_nat (length (nth i FFS [])) - 1) by lia. exact G.
      * apply (HXI R2 M2 model2 F fl LK' cr HRP Ha0); [|exact HH2]. constructor; assumption.
    + intros X HXn _. rewrite forallb_forall in Hnews. specialize (Hnews X HXn). apply orb_prop in Hnews as [Hs|Hs].
      * exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 Hs).
      * apply (smalloc_fact_sound E' E2 nx (SR.ps_cells ps) (nth i BLS []) (nth i FFS []) k (nx + 5)%nat nx M1 M2 A A model1 model2 (curB i E) (curF i E) LK LK' cr F fl (sp0 + CH2.ci_csp ci + 32)
                 HagE' Hag2 HK HH1); try assumption.
        -- unfold CHA.curB. rewrite HdenB. reflexivity.
        -- unfold CHA.curF. rewrite HdenF. reflexivity.
Qed.

Lemma smalloc_leaf_u : forall (UN : kentry -> Prop) k news i c ps j cj ci,
  In k PM_FS_CLASSES -> nth_error CPS j = Some cj ->
  CHA.custom_chk NF d SCELLS GLO GHI (hl_scr_stack_malloc L) 1 (nth i BLS []) (nth i FFS []) [] news None c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  SR.ps_pc ps = hl_stack_malloc L k ->
  CHA.frames_eqb (nth j FFS []) ((EVar (CH2.ci_nx ci + 5), k, CH2.ci_csp ci) :: nth i FFS []) = true ->
  CH2.blocks_eqb (nth j BLS []) (nth i BLS []) = true ->
  (forall X, In X news -> (CHA.static_chk SCELLS GLO GHI X || smalloc_fact_ok (SR.ps_cells ps) (CH2.ci_nx ci) (nth i BLS []) (nth i FFS []) k (CH2.ci_nx ci + 5) (CH2.ci_nx ci) X)%bool = true \/ UN X) ->
  (forall X E2 LB2 FF2 LK2 cr2 A2 M2 model2, UN X -> ri_inv HI LB2 FF2 LK2 cr2 A2 M2 (vml_of model2) -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X) ->
  2 <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (forall E E2 cr, Cred i E cr -> env_agree NF E E2 -> Cred j E2 cr) ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AMBX i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> CCA.IH (hl_segs L) CPS AMBX K FPI (CC.meas c E) ->
    (forall R2 M2 model2 F fl LK' cr, regs_preserved R' R2 -> getr R2 10%bv = Z_to_bv 64 F ->
        sm_facts k (curB i E) (curF i E) LK' (sp0 + CH2.ci_csp ci) (hl_scr_stack_malloc L) M1 M2 F fl ->
        ri_inv HI (curB i E) ((F, k, sp0 + CH2.ci_csp ci + 32) :: curF i E) LK' cr A M2 (vml_of model2) ->
        XI j (CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 fl] R2) A M2 model2) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros UN k news i c ps j cj ci Hk Hcj Hchk Hpc Hfeq Hbeq Hnews HU Hroom HCred fx' E R A M model E' R' M1 model1 HAt [HA HX] HFP Hag HLF HIH HXI.
  destruct (CHA.custom_ret L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0
              CRS_ok WRS_ok IMG_ok CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XI (hl_scr_stack_malloc L) 1%nat (nth i BLS []) (nth i FFS []) [] news None i c ps j cj ci Hcj Hchk
              E R A M model E' R' M1 model1 HAt HA Hag HLF HIH) as [CF CONT].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  pose proof HA' as (Hmo1 & Hrt1 & HA01 & HagE & (cr & LK & HH1 & HLK1 & HC1 & HRoom1) & Hfr1 & Hdf1).
  apply CHA.frames_eqb_eq in Hfeq. apply CH2.blocks_eqb_eq in Hbeq.
  assert (CHK2 : CH2.blocks_vars_lt (CH2.ci_nx ci) (nth i BLS []) = true /\ CHA.frames_vars_lt (CH2.ci_nx ci) (nth i FFS []) = true).
  { unfold CHA.custom_chk in Hchk. destruct (CHA.common_chk NF d (hl_scr_stack_malloc L) 1 c ps cj (nth i BLS []) (nth i FFS [])) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb Z5].
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Z2]. split; assumption. }
  destruct CHK2 as [BV FV].
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1)) as RF1.
  destruct (CHA.rf_ceil _ _ _ _ RF1) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RF1) as (SP1 & _). pose proof Hstk as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (USP : bv_unsigned (getr R' 2%bv) = sp0 + CH2.ci_csp ci) by (rewrite Hsp; apply u64_of_Z; lia).
  rewrite Hpc.
  apply (PmHeapIfaceA.aio_stack_malloc _ _ _ _ _ HIok k Hk fx' R' M1 model1 (curB i E) (curF i E) LK cr A K HH1 (proj1 Hmo1) (proj2 Hmo1) Htp).
  - rewrite Hra. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'.
  - rewrite USP. split; [exact K1|]. split; [lia|]. split; [lia|]. split; [exact K4|]. split; [|exact K6].
    intros dd m Hdd Hm. exact (L5C.writable_of_defined (hl_segs L) M1 _ _ K5 ltac:(lia) ltac:(lia) dd m Hdd Hm).
  - unfold ff_room. specialize (HRoom1 k Hk). lia.
  - rewrite USP. exact Hffrs.
  - exact KNIL.
  - rewrite USP. intros R2 M2 model2 F fl LK' Ha0 HRP Q1 Q2 Q3 Q4 HLK' Q5 Q6 Q7 Q8 Q9 Qst Q10 HPres Hrt2 HMI2 HH2. rewrite Hra.
    assert (Hmo2 : CHA.amodel_ok A model2) by (split; [rewrite (L5LZ.model_rt_halted _ _ Hrt2); exact (proj1 Hmo1) | exact HMI2]).
    set (nx := CH2.ci_nx ci) in *. set (E2 := CH2.retEx E' nx [Z_to_bv 64 fl] R2).
    pose proof (CH2.retEx_agree E' nx [Z_to_bv 64 fl] R2 : env_agree nx E' E2) as Hag2.
    assert (HagEE2 : env_agree NF E E2).
    { eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4]|]. eapply CC.env_agree_le; [exact Hag2 | lia]. }
    assert (FR : 0 <= F < 2 ^ 64) by (destruct Q1 as (G1 & G2 & _ & (G0 & _) & G5); pose proof (CHA.frame_class_facts k Hk); lia).
    assert (HvF : CL5A.uv E2 (EVar (nx + 5)) = F).
    { unfold CL5A.uv. cbn [edenot]. pose proof (CH2.retEx_a0 E' nx [Z_to_bv 64 fl] R2) as G. cbn [length] in G. replace (nx + 1 + 4)%nat with (nx + 5)%nat in G by lia.
      unfold E2. rewrite G, Ha0. apply u64_of_Z. exact FR. }
    assert (Hvfl : CL5A.uv E2 (EVar nx) = fl).
    { unfold CL5A.uv. cbn [edenot]. pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 fl] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. cbn [nth] in G.
      unfold E2. rewrite G. apply u64_of_Z. destruct (CHA.rf_fs _ _ _ _ RF1) as ((G0 & _) & G3 & _). unfold FS_BYTES in *. lia. }
    assert (HBj : curB j E2 = curB i E).
    { unfold CHA.curB. rewrite Hbeq. rewrite (CH2.den_agree nx E' E2 _ Hag2 BV), HdenB. reflexivity. }
    assert (HFj : curF j E2 = (F, k, sp0 + CH2.ci_csp ci + 32) :: curF i E).
    { unfold CHA.curF. rewrite Hfeq. unfold CHA.denF at 1. cbn [map fst snd app]. fold (CHA.denF sp0 E2 (nth i FFS [])).
      unfold CL5A.uv in HvF. rewrite HvF. rewrite (CHA.denF_agree sp0 nx E' E2 _ Hag2 FV), HdenF. reflexivity. }
    apply (CONT fx' R2 A M2 model2 [Z_to_bv 64 fl] (curB i E) (curF i E) [] eq_refl HFP (CH2.regs_preserved_kept R' R2 HRP) I (CHA.ahpres_of_aheap_pres _ _ _ _ _ _ _ _ HPres)).
    + unfold CHA.curB. rewrite HdenB. apply incl_refl.
    + unfold CHA.curF. rewrite HdenF. apply incl_refl.
    + intros w a [].
    + split.
      * apply (CHA.amb_callee L ar C HI HIok NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 STK SCR_pos NF32 i j E E2 A A M1 M2 model1 model2
                 (CH2.ci_csp ci) (hl_scr_stack_malloc L) (curB i E) (curF i E) [] cr LK' HA' (CHA.ahpres_of_aheap_pres _ _ _ _ _ _ _ _ HPres)).
        -- unfold CHA.curB. apply incl_appr, incl_refl.
        -- unfold CHA.curF. apply incl_appr, incl_refl.
        -- exact Hc1.
        -- exact Hs0.
        -- exact Hc2.
        -- intros w a [].
        -- exact Hrt2.
        -- exact Hmo2.
        -- apply incl_refl.
        -- rewrite HBj, HFj. exact HH2.
        -- exact (incl_tran HLK' HLK1).
        -- exact HagEE2.
        -- exact (HCred E E2 cr HC1 HagEE2).
        -- rewrite HFj, Hfeq. cbn [length]. pose proof (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2)) as [_ ND].
           pose proof (CHA.ffroom_push NF 0 NF32 _ _ _ (F, k, sp0 + CH2.ci_csp ci + 32) _ HRoom1 HLK' ND) as G.
           replace (D0 - Z.of_nat (Datatypes.S (length (nth i FFS [])))) with (D0 - Z.of_nat (length (nth i FFS [])) - 1) by lia. exact G.
      * apply (HXI R2 M2 model2 F fl LK' cr HRP Ha0); [|exact HH2]. constructor; assumption.
    + intros X HXn _. destruct (Hnews X HXn) as [Hnews'|Hu]; [|exact (HU X E2 _ _ _ _ _ _ _ Hu HH2)]. apply orb_prop in Hnews' as [Hs|Hs].
      * exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 Hs).
      * apply (smalloc_fact_sound E' E2 nx (SR.ps_cells ps) (nth i BLS []) (nth i FFS []) k (nx + 5)%nat nx M1 M2 A A model1 model2 (curB i E) (curF i E) LK LK' cr F fl (sp0 + CH2.ci_csp ci + 32)
                 HagE' Hag2 HK HH1); try assumption.
        -- unfold CHA.curB. rewrite HdenB. reflexivity.
        -- unfold CHA.curF. rewrite HdenF. reflexivity.
Qed.

Variable R0 : bvmap 5 word.
Variable ra0 : Z.
Hypothesis EV0 : forall x : reg, ev E0 (ridx x) = getr R0 x.
Hypothesis RA0 : getr R0 1%bv = Z_to_bv 64 ra0.
Hypothesis RA0ok : L5.ra_ok ra0.

Lemma exit_retire : forall retpc i c ps fle Fe k c0,
  CL.is_ret_at (hl_segs L) retpc -> CBA.exit_base_chk NF retpc c ps = true ->
  nth i FFS [] = [(Fe, k, c0)] -> CHA.retire_chk NF d c (nth i BLS []) (nth i FFS []) = Some fle ->
  CC.has_cell (SR.ps_cells ps) (KWord (SA fle 0) 1 (ELit 0)) = true ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
    ar_fs ar <= CL5A.uv E fle < ar_fs ar + FS_BYTES -> ~ aclient L ar LBrest FFrest sp0 SCR (CL5A.uv E fle) ->
    (forall model2 cr LK,
        regs_preserved R0 R' -> CHA.ahpres L ar LBrest FFrest sp0 SCR W M0 M1 -> model_rt model0 model2 -> incl A0 A -> CHA.amodel_ok A model2 -> incl LK LK0 ->
        ri_inv HI (curB i E) FFrest LK cr A M1 (vml_of model2) -> Cred i E cr -> env_agree NF E0 E' ->
        srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 ra0) M1 (seg_rom (hl_segs L))) model2) K) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros retpc i c ps fle Fe k c0 Hret Hchk HFi Hrchk Hcell fx' E R A M model E' R' M1 model1 HAt HA Hag HLF Hflr Hflnc Hcont.
  unfold CBA.exit_base_chk in Hchk. apply andb_prop in Hchk as [Hchk C3]. apply andb_prop in Hchk as [C1 C2]. apply Z.eqb_eq in C1. apply Nat.leb_le in C3.
  apply CC.has_cell_In in Hcell.
  destruct (CHA.retire_exit L ar C HI HIok LY_img NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
              i c ps fle Fe k c0 E E' R R' A M model M1 model1 HFi Hrchk HAt HA Hag HLF Hcell Hflr Hflnc) as (Hmo1 & Hrt1 & HA01 & (cr & LK & HH1 & HLK1 & HC1) & Hfr1 & Hdf1).
  pose proof (CBA.leaf_agree0 L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i c E E' A M model HA C3 Hag) as HagE'.
  assert (KEEP : forall x : reg, In (ridx x) CL5.CSAVED -> getr R' x = getr R0 x).
  { intros x Hx. assert (Hx32 : (ridx x < NF)%nat).
    { apply (Nat.lt_le_trans _ 32); [|exact NF32]. unfold CL5.CSAVED in Hx. cbn [In] in Hx. clear - Hx.
      repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; apply Nat.ltb_lt; reflexivity|]). destruct Hx. }
    rewrite (CL.ps_keeps_sound (hl_segs L) c ps E0 E' R' _ _ CL5.CSAVED NF x (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) C2 HagE' Hx Hx32). exact (EV0 x). }
  assert (HRP : regs_preserved R0 R') by (intros x Hx; apply KEEP; exact (CL5.csaved_in x Hx)).
  assert (Hra' : getr R' 1%bv = Z_to_bv 64 ra0) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact RA0).
  pose proof (CBA.exit_post L ar C HI HIok NF M0 model0 A0 LBrest FFrest sp0 d W BLS STK NF32 DEF0 i E A M1 model1 cr LK FFrest Hmo1 Hrt1 HA01 Hfr1 Hdf1 HH1) as HP.
  assert (Hoff : H_off_segments (hl_segs L) (ahid A model1)) by exact (CHA.vis_off_segments L ar C HI HIok LY_below _ _ _ _ _ _ model1 HH1).
  rewrite C1. eapply (CCA.ret_cps (hl_segs L) fx' R' retpc M1 model1 A K Hret (proj1 Hmo1) (proj2 Hmo1) (proj1 (PmHeapIfaceA.aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1)) Hoff LY_nowrap).
  { rewrite Hra'. apply Hoare.ret_ok_even. destruct RA0ok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
  intros model2 HMI2 HS. rewrite Hra'.
  assert (VML : vml_of model2 = vml_of model1) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ HS), (L5LZ.sbm_lazy _ _ HS); reflexivity).
  apply (Hcont model2 cr LK HRP HP); [exact (L5LZ.model_rt_trans _ _ _ Hrt1 (L5LZ.sbm_model_rt _ _ HS)) | exact HA01 | | exact HLK1 | rewrite VML; exact HH1 | exact HC1 | exact HagE'].
  split; [rewrite (L5LZ.sbm_halted _ _ HS); exact (proj1 Hmo1) | exact HMI2].
Qed.

End Inst.
End CRA.
