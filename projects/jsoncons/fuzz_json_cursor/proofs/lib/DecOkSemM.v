(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan L5Defs L5Core FrmInv FpBridge CutVFXM DecIface DecScanPure DecOkDefsM.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutL5 CutOpsD CutAutoD DecAssume.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DOS.
Section Cert.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable DKINDS : list kind.
Variable SCANEXP ERRNO : Z.

Definition ret_kind (ks : list kind) (rt : nat * nat * nat * Z) : kind :=
  let '(j, s, _, pc) := rt in
  if Z.eqb pc SCANEXP then (match reg_e (nth j CPS CA.dummy_cp) 10 with ELit _ => KRXa | _ => KPost end) else nth s ks KDead.
Definition kinds : list kind := fold_left (fun ks rt => ks ++ [ret_kind ks rt]) RETS DKINDS.
Definition kind_of (i : nat) : kind := nth i kinds KDead.

Definition FOOT : list SGP.region := [(EVar 2, -256, ELit 8672); (EVar 21, 8, ELit 8); (ELit 0, ERRNO, ELit 4)].
Definition FOOT2 : list SGP.region := [(EVar 2, -256, ELit 8672); (ELit 0, ERRNO, ELit 4)].

Definition F0x : list SGP.region := [(EVar 2, -256, ELit 256); (EVar 2, 0, ELit 8416); (EVar 21, 8, ELit 8); (ELit 0, ERRNO, ELit 4)].

Definition rng_in (kn : list kentry) (e : expr) (lo hi : Z) : bool :=
  existsb (fun K => match K with KRange e' l h => (expr_eqb e' e && Z.leb lo l && Z.leb h hi)%bool | _ => false end) kn.
Definition cls_chk (cl : cls) (c : CC.cutpoint) (cv : expr) : bool :=
  let kn := CC.cp_know c in
  match cl with
  | CDig => rng_in kn cv 48 57
  | CDot => rng_in kn cv 46 46
  | CStopS => (rng_in kn cv 0 255 && has kn (KRange (DAS.nd_of cv) 0 0) && has kn (KRange (DAS.np_of cv) 0 0))%bool
  | CStopN => (rng_in kn cv 0 255 && has kn (KRange (DAS.nd_of cv) 0 0) && has kn (KRange (DAS.np_of cv) 0 0) && has kn (KRange (DAS.ne_of cv) 0 0))%bool
  | CStop2 => rng_in kn cv 46 46
  end.

Definition lit_or_fact (c : CC.cutpoint) (z : Z) : bool := (expr_eqb (reg_e c 20) (ELit z) || has (CC.cp_know c) (KRange (reg_e c 20) z z))%bool.
Definition sc_chk (f : flg) (cl : cls) (c : CC.cutpoint) : bool :=
  let kn := CC.cp_know c in
  (Nat.ltb 48 (CC.cp_nx c) && has kn (KWord rpos_a 8 rpos_e) && has kn (KRange nk_e 0 (4 * NMAX))
   && match reg_e c 10 with
      | EVar cv => has kn (KWord named_a 1 (EVar cv)) && has kn (KRange (EVar 48) 1 NMAX) && cls_chk cl c (EVar cv)
      | ELit 0 => has kn (KRange (EVar 48) 0 0) && match cl with CStopS | CStopN => true | _ => false end
      | _ => false
      end
   && match f with GS4 => APC.expr_vars_lt (CC.cp_nx c) (reg_e c 20) | _ => true end
   && match cl, f with CDot, GS4 => lit_or_fact c 0 | CStop2, GS4 => lit_or_fact c 1 | CStop2, _ => false | _, _ => true end)%bool.
Definition cut_chk (i : nat) (c : CC.cutpoint) : bool :=
  (Nat.leb NF (CC.cp_nx c) && (regions_eqb (CC.cp_F c) FOOT || regions_eqb (CC.cp_F c) FOOT2)
   && match kind_of i with
      | KSc f cl => sc_chk f cl c
      | KPost => regions_eqb (CC.cp_F c) FOOT2
      | KRXa => match find_cell (CC.cp_know c) with Some v => APC.expr_vars_lt (CC.cp_nx c) v | None => false end
      | KEnt => true
      | KDead => false
      end)%bool.

Definition is_lit (e : expr) (z : Z) : bool := expr_eqb e (ELit z).

Definition flag_rel (srcf : option flg) (cl : cls) (c : CC.cutpoint) (f' : flg) (e20' : expr) : bool :=
  let src_false := match srcf with None | Some G0 => true | Some G1 => false | Some GS4 => lit_or_fact c 0 end in
  let src_true := match srcf with Some G1 => true | Some GS4 => lit_or_fact c 1 | _ => false end in
  let tgt_false := match f' with G0 => true | G1 => false | GS4 => is_lit e20' 0 end in
  let tgt_true := match f' with G1 => true | G0 => false | GS4 => is_lit e20' 1 end in
  let same := match srcf, f' with Some GS4, GS4 => (expr_eqb e20' (reg_e c 20) && APC.expr_vars_lt (CC.cp_nx c) (reg_e c 20))%bool | _, _ => false end in
  match cl with
  | CDig => ((src_false && tgt_false) || (src_true && tgt_true) || same)%bool
  | CDot => (src_false && tgt_true)%bool
  | _ => false
  end.
Definition cell_dec (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  match find_cell (CC.cp_know c), find_cell (SR.ps_cells ps) with
  | Some vs, Some vl => (expr_eqb vl (APC.eaddz vs (-1)) && APC.expr_vars_lt (CC.cp_nx c) vs)%bool
  | _, _ => false
  end.
Definition goto_chk2 (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (j : nat) (cj : CC.cutpoint) (s : CC.subst) : bool :=
  let k' := CC.slook s 48 in
  let e20' := CC.esubstL NF s (reg_e cj 20) in
  match kind_of i with
  | KEnt => match kind_of j with
            | KEnt => true
            | KSc f' _ => ((expr_eqb k' (APC.eaddz (EVar 47) (-1)) && flag_rel None CDig c f' e20')
                           || (expr_eqb k' (EVar 47) && match f' with GS4 => is_lit e20' 0 | G0 => true | G1 => false end))%bool
            | _ => false
            end
  | KSc f cl => match kind_of j with
                | KSc f' cl' =>
                    ((expr_eqb k' (APC.eaddz (EVar 48) (-1)) && flag_rel (Some f) cl c f' e20')
                     || (expr_eqb k' (EVar 48) && match cl, cl', f, f' with
                                                  | CStopS, CStopN, GS4, GS4 => (expr_eqb e20' (reg_e c 20) && APC.expr_vars_lt (CC.cp_nx c) (reg_e c 20))%bool
                                                  | _, _, _, _ => false
                                                  end))%bool
                | KPost => match cl with CStop2 | CStopN => cell_dec c ps | _ => false end
                | _ => false
                end
  | KRXa => match kind_of j with KPost => cell_dec c ps | _ => false end
  | KPost => match kind_of j with KPost => true | _ => false end
  | KDead => false
  end.

Definition raw_e (e : expr) : expr := EAlu ALU_SLTU (EAlu ALU_SUB (EAlu ALU_AND e (ELit (-33))) (ELit 69)) (ELit 1).
Variable RET_PC SCALBNL TPV : Z.
Variable INL : list (Z * (Z * list nat * option Z)).
Variable CALLEES : list (Z * (Z * option (Z * Z))).
Definition SAVE_VARS : list (nat * nat) :=
  [(1, 34); (8, 35); (9, 36); (18, 37); (19, 38); (20, 39); (21, 40); (22, 41); (23, 42); (24, 43); (25, 44); (26, 45); (27, 46)]%nat.

Definition exit_regs_chk (ps : SR.post_spec) : bool :=
  (forallb (fun rv : nat * nat => CL.ps_reg_is ps (fst rv) (EVar (snd rv))) SAVE_VARS
   && CL.ps_reg_is ps 2 (APC.eaddz (EVar 2) 8416) && CL.ps_reg_is ps 3 (EVar 3) && CL.ps_reg_is ps 4 (ELit TPV))%bool.
Definition kind_eqb (a b : kind) : bool :=
  match a, b with KEnt, KEnt | KPost, KPost => true | _, _ => false end.

Variable IMG_LO IMG_HI : Z.
Definition LMIN : Z := 9223372036854775808.
Definition scx_kn1 (ps : SR.post_spec) : list kentry := APC.kn_havoc (APC.kn_havoc (SR.ps_cells ps) (EVar 21) 8 (ELit 8)) (EVar 2) (-80) (ELit 80).
Definition scx_ret_chk (lmin : bool) (c : CC.cutpoint) (ps : SR.post_spec) (ra : Z) (cj : CC.cutpoint) : bool :=
  let regs := CA.ps_reglist ps in
  let nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps) in
  let regs1 := APC.sr_fresh regs APC.caller_saved nx in
  let kn := KWord rpos_a 8 (EVar (nx + 16)) :: KUnk (SA (EVar 2) (-80)) (ELit 80) :: scx_kn1 ps in
  (Z.eqb (CC.cp_pc cj) ra && CA.regs_eqb (CC.cp_regs cj) (if lmin then sr_upd regs1 10 (ELit LMIN) else regs1)
   && CVF.kn_eqb (CC.cp_know cj) (if lmin then kn else KRange (DAS.nmin_of (nth 10 regs1 (ELit 0))) 0 0 :: kn)
   && Nat.eqb (CC.cp_nx cj) (nx + 17) && expr_eqb (CC.cp_meas cj) (APC.esub (CC.cp_meas c) (ELit 1)))%bool.
Definition scx_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let regs := CA.ps_reglist ps in
  let nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps) in
  let cells := SR.ps_cells ps in
  match kind_of i, reg_e c 10, nth 1 regs (ELit 1) with
  | KSc GS4 CStopS, EVar cv, ELit ra =>
      (has cells (KRange (raw_e (EVar cv)) 1 1) && Nat.ltb cv (CC.cp_nx c)
       && has cells (KWord rpos_a 8 rpos_e) && has cells (KWord (SA (EVar 21) 184) 8 (ELit 18446744073709551615)) && has cells (KWord (SA (EVar 21) 192) 8 (ELit 0))
       && has cells (KRange (CC.cp_meas c) 1 CC.MB) && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c) && has cells (KImg IMG_LO IMG_HI)
       && CVF.all_regs_chk ps && expr_eqb (nth 10 regs (ELit 0)) (EVar 21) && expr_eqb (nth 11 regs (ELit 0)) (ELit 1) && expr_eqb (nth 2 regs (ELit 0)) (EVar 2)
       && Z.leb 0 ra && Z.ltb ra (2 ^ 47) && Z.eqb (ra mod 2) 0
       && APC.sr_vars_lt nx regs && APC.kn_vars_lt nx (scx_kn1 ps) && APC.sr_vars_lt (nx + 16) (APC.sr_fresh regs APC.caller_saved nx)
       && existsb (fun rt : nat * nat * nat * Z => let '(ja, i', _, pc) := rt in
             (Nat.eqb i' i && Z.eqb pc SCANEXP
              && match kind_of ja, kind_of (S ja) with KRXa, KPost => true | _, _ => false end
              && match nth_error CPS ja, nth_error CPS (S ja) with Some cja, Some cjb => scx_ret_chk true c ps ra cja && scx_ret_chk false c ps ra cjb | _, _ => false end)%bool) RETS)%bool
  | _, _, _ => false
  end.
Definition other_chk (i : nat) (ps : SR.post_spec) (id : Z) : bool :=
  match nth_error CPS i with
  | None => false
  | Some c =>
      (((Z.eqb (SR.ps_pc ps) RET_PC || Z.eqb (SR.ps_pc ps) SCALBNL) && exit_regs_chk ps && kind_eqb (kind_of i) KPost)
       || (Z.eqb (SR.ps_pc ps) SCANEXP && scx_chk i c ps)
       || existsb (fun rt : nat * nat * nat * Z => let '(j, i', _, pc) := rt in
             (Nat.eqb i' i && Z.eqb pc id && Z.eqb (SR.ps_pc ps) id && negb (Z.eqb pc SCANEXP) && kind_eqb (kind_of i) (kind_of j)
              && match nth_error CPS j with
                 | Some cj =>
                     match find (fun e : Z * (Z * list nat * option Z) => Z.eqb (fst e) pc) INL with
                     | Some (_, (len, hv, a0)) => CVF.inl_chk c ps cj len hv a0
                     | None => match find (fun e : Z * (Z * option (Z * Z)) => Z.eqb (fst e) pc) CALLEES with
                               | Some (_, (SCRc, IMGc)) => CVF.call_chk 256 c ps cj SCRc IMGc
                               | None => false
                               end
                     end
                 | None => false
                 end)%bool) RETS)%bool
  end.

Variable txt : list Z.
Variables Q F SP : Z.
Variable E0 : env.
Variable M0 : word -> option byte.
Variable model0 : Model.
Definition N : Z := Z.of_nat (length txt).
Definition txt' : list Z := txt ++ [0].
Definition D : Z := PDS.contD false txt'.
Hypothesis E0_sp : bv_unsigned (ev E0 2) = SP.
Hypothesis E0_F : bv_unsigned (ev E0 21) = F.
Hypothesis E0_Q : bv_unsigned (ev E0 32) = Q.
Hypothesis E0_N : bv_unsigned (ev E0 47) = N.
Hypothesis R_SP : PDC.STK_FLOOR + 256 <= SP /\ SP + 8416 <= 2 ^ 47.
Hypothesis R_F : PDC.STK_FLOOR <= F /\ F + 256 <= 2 ^ 47.
Hypothesis R_Q : 4096 <= Q /\ Q + N < 2 ^ 47 /\ N < 2 ^ 26.
Hypothesis R_ERR : 0 <= ERRNO /\ ERRNO + 4 <= PDC.STK_FLOOR.
Hypothesis T_bytes : L5.bytes_at segs M0 Q txt.
Hypothesis T_nul : L5.u8_at segs M0 (Q + N) 0.
Hypothesis T_rng : Forall (fun c => 0 <= c < 256) txt.
Hypothesis T_dig : exists c r, txt = c :: r /\ PD.is_dig c = true.
Hypothesis AP_TS : PDC.apart Q (N + 1) (SP - 256) 8672.
Hypothesis AP_TF : PDC.apart Q (N + 1) (F + 8) 192.
Hypothesis AP_TE : PDC.apart Q (N + 1) ERRNO 4.
Hypothesis AP_FS : PDC.apart (F + 8) 192 (SP - 256) 8672.

Definition flag (f : flg) (c : CC.cutpoint) (E : env) : bool :=
  match f with G0 => false | G1 => true | GS4 => negb (uE E (reg_e c 20) =? 0) end.
Definition XI_sc (f : flg) (c : CC.cutpoint) (E : env) (M : word -> option byte) : Prop :=
  let k := bv_unsigned (ev E 48) in
  0 <= k <= N /\ L5.u64_at segs M (F + 8) (Q + N + 1 - k) /\ nth (Z.to_nat (N - k)) txt' 0 = uE E (reg_e c 10)
  /\ D = (N - k) + PDS.contD (flag f c E) (skipn (Z.to_nat (N - k)) txt').
Definition XI (i : nat) (E : env) (M : word -> option byte) : Prop :=
  match kind_of i, nth_error CPS i with
  | KEnt, _ => True
  | KSc f _, Some c => XI_sc f c E M
  | KRXa, _ => L5.u64_at segs M (F + 8) (Q + D + 1)
  | KPost, _ => L5.u64_at segs M (F + 8) (Q + D)
  | _, _ => False
  end.

Lemma N_nonneg : 0 <= N. Proof. unfold N. lia. Qed.
Lemma len_txt' : Z.of_nat (length txt') = N + 1. Proof. unfold txt', N. rewrite length_app. cbn. lia. Qed.
Lemma D_range : 0 <= D <= N + 1.
Proof.
  unfold D. assert (G : forall l g, 0 <= PDS.contD g l <= Z.of_nat (length l)).
  { assert (Gs : forall p l, 0 <= fst (PD.span p l) <= Z.of_nat (length l)).
    { intros p l. induction l as [|c r IH]; cbn [PD.span length]; [cbn; lia|]. destruct (p c); [|cbn [fst]; lia]. destruct (PD.span p r) as [n r']. cbn [fst] in *. lia. }
    assert (Ge : forall l, 0 <= PDS.expo l <= Z.of_nat (length l)).
    { intros [|c r]; cbn [PDS.expo length]; [lia|]. destruct ((c =? 101) || (c =? 69)); [|lia]. unfold PD.exp_scan.
      destruct r as [|c1 r1]; [cbn; lia|]. destruct ((c1 =? 43) || (c1 =? 45)).
      - pose proof (Gs PD.is_dig r1) as B. destruct (PD.span PD.is_dig r1) as [n r']. cbn [fst] in B. destruct (n =? 0); cbn [length]; lia.
      - pose proof (Gs PD.is_dig (c1 :: r1)) as B. destruct (PD.span PD.is_dig (c1 :: r1)) as [n r']. cbn [fst] in B. destruct (n =? 0); cbn [length] in *; lia. }
    induction l as [|c r IH]; intros g; [cbn; lia|]. cbn [PDS.contD]. destruct (PD.is_dig c).
    - specialize (IH g). cbn [length]. lia.
    - destruct ((c =? 46) && negb g); [specialize (IH true); cbn [length]; lia | exact (Ge (c :: r))]. }
  specialize (G txt' false). rewrite len_txt' in G. exact G.
Qed.

Lemma text_byte : forall i, 0 <= i <= N -> L5.u8_at segs M0 (Q + i) (nth (Z.to_nat i) txt' 0) /\ 0 <= nth (Z.to_nat i) txt' 0 < 256.
Proof.
  intros i Hi. unfold txt'. destruct (Z.eq_dec i N) as [->|Hne].
  - rewrite app_nth2 by (unfold N; lia). replace (Z.to_nat N - length txt)%nat with 0%nat by (unfold N; lia). cbn [nth]. split; [exact T_nul | lia].
  - assert (Hlt : (Z.to_nat i < length txt)%nat) by (unfold N in *; lia). rewrite app_nth1 by exact Hlt. split.
    + pose proof (T_bytes (Z.to_nat i) Hlt) as B. rewrite Z2Nat.id in B by lia. exact B.
    + rewrite Forall_forall in T_rng. apply T_rng. apply nth_In. exact Hlt.
Qed.

Lemma ev_frozen : forall E n, env_agree NF E0 E -> (n < 48)%nat -> ev E n = ev E0 n.
Proof. intros E n [H _] Hn. symmetry. apply H. exact Hn. Qed.
Lemma estart_reg : forall E r o z, bv_unsigned (ev E r) = z -> estart E (SA (EVar r) o) = z + o.
Proof. intros E r o z H. unfold estart. cbn [a_base a_off edenot]. rewrite H. reflexivity. Qed.
Lemma estart_lit : forall E a o, 0 <= a < 2 ^ 64 -> estart E (SA (ELit a) o) = a + o.
Proof. intros E a o H. unfold estart. cbn [a_base a_off edenot]. rewrite u64_of_Z by lia. reflexivity. Qed.
Lemma elen_lit : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof. intros E z H. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. reflexivity. Qed.

Definition out3 (a : Z) : Prop := ~ (SP - 256 <= a < SP + 8416) /\ ~ (F + 8 <= a < F + 16) /\ ~ (ERRNO <= a < ERRNO + 4).
Lemma outside_F0x : forall x : word, out3 (bv_unsigned x) -> SGP.outside E0 F0x x.
Proof.
  intros x (H1 & H2 & H3). unfold SGP.outside, F0x. pose proof R_SP. pose proof R_F. pose proof R_ERR. unfold PDC.STK_FLOOR in *.
  repeat (apply Forall_cons); [| | | | apply Forall_nil];
    rewrite ?(estart_reg E0 2 _ SP E0_sp), ?(estart_reg E0 21 _ F E0_F), ?(estart_lit E0 0) by lia; rewrite !elen_lit by lia; lia.
Qed.
Lemma F0x_out3 : forall x : word, SGP.outside E0 F0x x -> out3 (bv_unsigned x).
Proof.
  intros x H. unfold SGP.outside, F0x in H. pose proof R_SP. pose proof R_F. pose proof R_ERR. unfold PDC.STK_FLOOR in *.
  apply Forall_cons_iff in H as [A1 H]. apply Forall_cons_iff in H as [A2 H]. apply Forall_cons_iff in H as [A3 H]. apply Forall_cons_iff in H as [A4 _].
  rewrite ?(estart_reg E0 2 _ SP E0_sp), ?(estart_reg E0 21 _ F E0_F), ?(estart_lit E0 0) in * by lia. rewrite !elen_lit in * by lia.
  unfold out3. lia.
Qed.
Lemma F0x_vars : forallb (SGP.region_vars_lt NF) F0x = true.
Proof. reflexivity. Qed.
Lemma sub_F_ok : forall i c, cut_chk i c = true -> CL.sub_F NF E0 F0x c.
Proof.
  intros i c H. unfold cut_chk in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  intros E x Hag Ho. apply F0x_out3 in Ho. destruct Ho as (H1 & H2 & H3).
  pose proof R_SP. pose proof R_F. pose proof R_ERR. unfold PDC.STK_FLOOR in *.
  assert (U2 : bv_unsigned (ev E 2) = SP) by (rewrite (ev_frozen E 2 Hag) by lia; exact E0_sp).
  assert (U21 : bv_unsigned (ev E 21) = F) by (rewrite (ev_frozen E 21 Hag) by lia; exact E0_F).
  apply orb_prop in H as [H|H]; apply regions_eqb_eq in H; rewrite H; unfold SGP.outside, FOOT, FOOT2;
    repeat (apply Forall_cons); try apply Forall_nil;
    rewrite ?(estart_reg E 2 _ SP U2), ?(estart_reg E 21 _ F U21), ?(estart_lit E 0) by lia; rewrite !elen_lit by lia; lia.
Qed.

Lemma foot2_rpos : forall c E (M M' : word -> option byte), regions_eqb (CC.cp_F c) FOOT2 = true -> env_agree NF E0 E ->
  (forall a : word, SGP.outside E (CC.cp_F c) a -> M' a = M a) -> forall v, L5.u64_at segs M (F + 8) v -> L5.u64_at segs M' (F + 8) v.
Proof.
  intros c E M M' HF Hag Hfr v Hu. apply regions_eqb_eq in HF. pose proof R_SP. pose proof R_F. pose proof R_ERR. unfold PDC.STK_FLOOR in *.
  assert (U2 : bv_unsigned (ev E 2) = SP) by (rewrite (ev_frozen E 2 Hag) by lia; exact E0_sp).
  apply (u64_at_same segs M M' (F + 8) v); [lia | lia | | exact Hu].
  intros x Hx. apply Hfr. rewrite HF. unfold SGP.outside, FOOT2. destruct AP_FS as [A|A];
    repeat (apply Forall_cons); try apply Forall_nil; rewrite ?(estart_reg E 2 _ SP U2), ?(estart_lit E 0) by lia; rewrite !elen_lit by lia; lia.
Qed.

Lemma know_in : forall E M kn K, know_ok segs E M kn -> has kn K = true -> kentry_ok segs E M K.
Proof. intros E M kn K HK H. apply has_In in H. exact (proj1 (Forall_forall _ _) HK K H). Qed.
Lemma u_lit : forall E z, 0 <= z < 2 ^ 64 -> uE E (ELit z) = z.
Proof. intros E z H. unfold uE. cbn [edenot]. apply u64_of_Z. lia. Qed.

Lemma rng_in_sem : forall E M kn e lo hi, know_ok segs E M kn -> rng_in kn e lo hi = true -> lo <= uE E e <= hi.
Proof.
  intros E M kn e lo hi HK H. unfold rng_in in H. apply existsb_exists in H as (K & Hin & Hb).
  destruct K as [| | | | |e' l h| | | |]; try discriminate. do 2 (apply andb_prop in Hb as [Hb ?X]). apply expr_eqb_eq in Hb. subst e'.
  apply Z.leb_le in X, X0. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as Y. cbn [kentry_ok] in Y. unfold uE. lia.
Qed.
Lemma cls_range : forall cl c cv E M, cls_chk cl c cv = true -> know_ok segs E M (CC.cp_know c) -> 0 <= uE E cv <= 255.
Proof.
  intros cl c cv E M H HK.
  assert (G : forall lo hi, 0 <= lo -> hi <= 255 -> rng_in (CC.cp_know c) cv lo hi = true -> 0 <= uE E cv <= 255).
  { intros lo hi Hlo Hhi Hh. pose proof (rng_in_sem E M _ _ _ _ HK Hh). lia. }
  destruct cl; cbn [cls_chk] in H.
  - exact (G 48 57 ltac:(lia) ltac:(lia) H).
  - exact (G 46 46 ltac:(lia) ltac:(lia) H).
  - do 2 (apply andb_prop in H as [H _]). exact (G 0 255 ltac:(lia) ltac:(lia) H).
  - do 3 (apply andb_prop in H as [H _]). exact (G 0 255 ltac:(lia) ltac:(lia) H).
  - exact (G 46 46 ltac:(lia) ltac:(lia) H).
Qed.

Lemma sc_arrive : forall f cl c E R (M : word -> option byte), sc_chk f cl c = true -> CC.At segs c E R M -> env_agree NF E0 E ->
  (forall a : word, SGP.outside E0 F0x a -> M a = M0 a) ->
  let k := bv_unsigned (ev E 48) in
  0 <= k <= N /\ L5.u64_at segs M (F + 8) (Q + N + 1 - k) /\ nth (Z.to_nat (N - k)) txt' 0 = uE E (reg_e c 10).
Proof.
  intros f cl c E R M H [_ HK] Hag Hfr k. unfold sc_chk in H. do 5 (apply andb_prop in H as [H ?X]). clear X X0. rename X1 into Hc.
  pose proof (know_in E M _ _ HK X2) as Hnk. pose proof (know_in E M _ _ HK X3) as Hrp. clear X2 X3 H.
  pose proof R_SP. pose proof R_F. pose proof R_Q as (RQ1 & RQ2 & RQ3). pose proof R_ERR. pose proof N_nonneg. unfold PDC.STK_FLOOR in *.
  assert (UQ : bv_unsigned (ev E 32) = Q) by (rewrite (ev_frozen E 32 Hag) by lia; exact E0_Q).
  assert (UN : bv_unsigned (ev E 47) = N) by (rewrite (ev_frozen E 47 Hag) by lia; exact E0_N).
  assert (UF : bv_unsigned (ev E 21) = F) by (rewrite (ev_frozen E 21 Hag) by lia; exact E0_F).
  assert (Bk : 0 <= k < 2 ^ 64) by (pose proof (u64_range (ev E 48)) as B; unfold two64 in B; exact B).

  cbn [kentry_ok] in Hnk. unfold nk_e, APC.esub in Hnk. rewrite mkAlu_denot, u_sub64 in Hnk. cbn [edenot] in Hnk. rewrite UN in Hnk. fold k in Hnk. unfold NMAX in Hnk.
  assert (Hk : 0 <= k <= N /\ (match reg_e c 10 with EVar _ => 1 <= k | _ => k = 0 end)).
  { destruct (reg_e c 10) as [z|cv| | | | | |] eqn:Ea0; try discriminate.
    - destruct z; try discriminate. apply andb_prop in Hc as [Hc _]. pose proof (know_in E M _ _ HK Hc) as X. cbn [kentry_ok edenot] in X. fold k in X. lia.
    - apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hc]. pose proof (know_in E M _ _ HK Hc) as X. cbn [kentry_ok edenot] in X. fold k in X. unfold NMAX in X.
      destruct (Z_le_gt_dec k N) as [Hle|Hgt]; [lia|]. exfalso.
      replace (N - k) with (N - k + 2 ^ 64 + (-1) * 2 ^ 64) in Hnk by lia. rewrite Z.mod_add in Hnk by lia. rewrite Z.mod_small in Hnk by lia. lia. }
  destruct Hk as [Hk Hk1]. split; [exact Hk|].
  assert (Hrpos : L5.u64_at segs M (F + 8) (Q + N + 1 - k)).
  { apply (CL5.kword64_elim segs E M rpos_a rpos_e (F + 8) _ Hrp); [apply (estart_reg E 21 8 F UF)|].
    unfold rpos_e, APC.esub, APC.eaddz, APC.eadd. rewrite !mkAlu_denot, u_sub64, !u_add64. cbn [edenot]. rewrite UQ, UN. fold k. rewrite u64_of_Z by lia.
    rewrite (Z.mod_small (Q + N)) by lia. rewrite (Z.mod_small (Q + N + 1)) by lia. apply Z.mod_small. lia. }
  split; [exact Hrpos|].
  destruct (reg_e c 10) as [z|cv| | | | | |] eqn:Ea0; try discriminate.
  - destruct z; try discriminate. rewrite Hk1, Z.sub_0_r. rewrite u_lit by lia.
    unfold txt'. rewrite app_nth2 by (unfold N; lia). replace (Z.to_nat N - length txt)%nat with 0%nat by (unfold N; lia). reflexivity.
  - do 2 (apply andb_prop in Hc as [Hc ?Y]). pose proof (know_in E M _ _ HK Hc) as Hnb. pose proof (cls_range cl c (EVar cv) E M Y HK) as Rc.
    apply (kword8_elim segs E M named_a (EVar cv) (Q + (N - k))) in Hnb.
    2:{ unfold named_a, estart. cbn [a_base a_off]. unfold APC.esub, APC.eaddz, APC.eadd. rewrite !mkAlu_denot, u_add64, u_sub64, u_add64. cbn [edenot]. rewrite UQ, UN. fold k.
        change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1).
        rewrite (Z.mod_small (Q + N)) by lia. rewrite (Z.mod_small (Q + N - k)) by lia.
        replace (Q + N - k + (2 ^ 64 - 1)) with (Q + N - k - 1 + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
    unfold uE in *. rewrite Z.mod_small in Hnb by lia.
    destruct (text_byte (N - k) ltac:(lia)) as [Ht Rt].
    assert (Hm0 : L5.u8_at segs M0 (Q + (N - k)) (bv_unsigned (edenot E (EVar cv)))).
    { apply (u8_at_same segs M M0 (Q + (N - k)) _ ltac:(lia) ltac:(lia)); [|exact Hnb].
      intros x Hx. symmetry. apply Hfr. apply outside_F0x. unfold out3. rewrite Hx.
      destruct AP_TS as [A|A], AP_TF as [B|B], AP_TE as [C|C]; lia. }
    exact (u8_at_inj segs M0 _ _ _ Ht Hm0 Rt ltac:(lia)).
Qed.

Lemma byte_enum : forall P : Z -> bool, forallb P (map Z.of_nat (seq 0 256)) = true -> forall c, 0 <= c <= 255 -> P c = true.
Proof.
  intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma nd_sem : forall E e, 0 <= uE E e <= 255 -> uE E (DAS.nd_of e) = 0 -> PD.is_dig (uE E e) = false.
Proof.
  intros E e Hr H. unfold uE, DAS.nd_of in *. rewrite !mkAlu_denot, u_sltu64, u_add64 in H. cbn [edenot] in H.
  change (bv_unsigned (Z_to_bv 64 (-48))) with (2 ^ 64 - 48) in H. change (bv_unsigned (Z_to_bv 64 10)) with 10 in H.
  set (c := bv_unsigned (edenot E e)) in *.
  pose proof (byte_enum (fun c => if (c + (2 ^ 64 - 48)) mod 2 ^ 64 <? 10 then true else negb (PD.is_dig c)) ltac:(vm_compute; reflexivity) c Hr) as X. cbv beta in X.
  destruct ((c + (2 ^ 64 - 48)) mod 2 ^ 64 <? 10); [discriminate|]. apply negb_true_iff in X. exact X.
Qed.
Lemma np_sem : forall E e, 0 <= uE E e <= 255 -> uE E (DAS.np_of e) = 0 -> uE E e <> 46.
Proof.
  intros E e Hr H. unfold uE, DAS.np_of in *. rewrite !mkAlu_denot, u_sltu64, u_sub64 in H. cbn [edenot] in H.
  change (bv_unsigned (Z_to_bv 64 46)) with 46 in H. change (bv_unsigned (Z_to_bv 64 1)) with 1 in H.
  intros Heq. rewrite Heq in H. discriminate H.
Qed.
Definition land_e (c : Z) : bool := Z.land c (2 ^ 64 - 33) =? 69.
Lemma land_e_spec : forall c, 0 <= c <= 255 -> land_e c = true <-> (c = 69 \/ c = 101).
Proof.
  intros c Hc. pose proof (byte_enum (fun c => Bool.eqb (land_e c) ((c =? 69) || (c =? 101))) ltac:(vm_compute; reflexivity) c Hc) as X. cbv beta in X.
  apply Bool.eqb_prop in X. rewrite X. rewrite orb_true_iff, !Z.eqb_eq. reflexivity.
Qed.
Lemma ne_sem : forall E e, 0 <= uE E e <= 255 -> uE E (DAS.ne_of e) = 0 -> uE E e <> 69 /\ uE E e <> 101.
Proof.
  intros E e Hr H. unfold uE, DAS.ne_of in *. rewrite !mkAlu_denot, u_sltu64, u_sub64, u_and64 in H. cbn [edenot] in H.
  change (bv_unsigned (Z_to_bv 64 (-33))) with (2 ^ 64 - 33) in H. change (bv_unsigned (Z_to_bv 64 69)) with 69 in H. change (bv_unsigned (Z_to_bv 64 1)) with 1 in H.
  set (c := bv_unsigned (edenot E e)) in *. pose proof (land_e_spec c Hr) as S. unfold land_e in S.
  destruct (Z.eqb_spec (Z.land c (2 ^ 64 - 33)) 69) as [Heq|Hne].
  - rewrite Heq in H. discriminate H.
  - assert (X : ~ (c = 69 \/ c = 101)) by (intros Y; apply S in Y; discriminate Y). lia.
Qed.

Lemma raw_e_sem : forall E e, 0 <= uE E e <= 255 -> uE E (raw_e e) = 1 -> uE E e = 69 \/ uE E e = 101.
Proof.
  intros E e Hr H. unfold uE, raw_e in *. cbn [edenot] in H. rewrite u_sltu64, u_sub64, u_and64 in H.
  change (bv_unsigned (Z_to_bv 64 (-33))) with (2 ^ 64 - 33) in H. change (bv_unsigned (Z_to_bv 64 69)) with 69 in H. change (bv_unsigned (Z_to_bv 64 1)) with 1 in H.
  set (c := bv_unsigned (edenot E e)) in *. apply (land_e_spec c Hr).
  pose proof (byte_enum (fun c => if (Z.land c (2 ^ 64 - 33) - 69) mod 2 ^ 64 <? 1 then land_e c else true) ltac:(vm_compute; reflexivity) c Hr) as X. cbv beta in X.
  destruct ((Z.land c (2 ^ 64 - 33) - 69) mod 2 ^ 64 <? 1); [exact X | discriminate H].
Qed.

Lemma dig_sem : forall c cv E M, cls_chk CDig c cv = true -> know_ok segs E M (CC.cp_know c) -> PD.is_dig (uE E cv) = true.
Proof.
  intros c cv E M H HK. cbn [cls_chk] in H. pose proof (rng_in_sem E M _ _ _ _ HK H) as X. unfold PD.is_dig.
  apply andb_true_intro; split; apply Z.leb_le; lia.
Qed.
Lemma dot_sem : forall c cv E M, cls_chk CDot c cv = true -> know_ok segs E M (CC.cp_know c) -> uE E cv = 46.
Proof. intros c cv E M H HK. cbn [cls_chk] in H. pose proof (rng_in_sem E M _ _ _ _ HK H) as X. lia. Qed.

Lemma inv_read : forall g g' idx c, 0 <= idx < N + 1 -> nth (Z.to_nat idx) txt' 0 = c ->
  D = idx + PDS.contD g (skipn (Z.to_nat idx) txt') ->
  ((PD.is_dig c = true /\ g' = g) \/ (c = 46 /\ g = false /\ g' = true)) ->
  D = (idx + 1) + PDS.contD g' (skipn (Z.to_nat (idx + 1)) txt').
Proof.
  intros g g' idx c Hi Hc HD Hcl. pose proof len_txt' as L.
  rewrite (PDS.skipn_nth txt' (Z.to_nat idx) 0) in HD by lia. rewrite Hc in HD.
  replace (Z.to_nat (idx + 1)) with (S (Z.to_nat idx)) by lia.
  destruct Hcl as [[Hd ->] | (-> & -> & ->)].
  - rewrite PDS.contD_dig in HD by exact Hd. lia.
  - rewrite PDS.contD_dot in HD. lia.
Qed.

Lemma inv_stop : forall g idx c, 0 <= idx < N + 1 -> nth (Z.to_nat idx) txt' 0 = c ->
  D = idx + PDS.contD g (skipn (Z.to_nat idx) txt') ->
  ((c = 46 /\ g = true) \/ (PD.is_dig c = false /\ c <> 46 /\ c <> 69 /\ c <> 101)) -> D = idx.
Proof.
  intros g idx c Hi Hc HD Hcl. pose proof len_txt' as L.
  rewrite (PDS.skipn_nth txt' (Z.to_nat idx) 0) in HD by lia. rewrite Hc in HD.
  destruct Hcl as [(-> & ->) | (H1 & H2 & H3 & H4)].
  - rewrite PDS.contD_stop_dot in HD. lia.
  - rewrite PDS.contD_stop in HD by assumption. lia.
Qed.

Lemma lit_or_fact_sem : forall c z E M, lit_or_fact c z = true -> know_ok segs E M (CC.cp_know c) -> 0 <= z < 2 ^ 64 -> uE E (reg_e c 20) = z.
Proof.
  intros c z E M H HK Hz. unfold lit_or_fact in H. apply orb_prop in H as [H|H].
  - apply expr_eqb_eq in H. rewrite H. apply u_lit. exact Hz.
  - pose proof (know_in E M _ _ HK H) as X. cbn [kentry_ok] in X. unfold uE. lia.
Qed.
Lemma flag_rel_sem : forall srcf cl c f' cj s E E' M, flag_rel srcf cl c f' (CC.esubstL NF s (reg_e cj 20)) = true -> env_agree (CC.cp_nx c) E E' -> know_ok segs E M (CC.cp_know c) ->
  let g := match srcf with None => false | Some f => flag f c E end in
  let g' := flag f' cj (CC.env_over NF s E') in
  match cl with CDig => g' = g | CDot => g = false /\ g' = true | _ => False end.
Proof.
  intros srcf cl c f' cj s E E' M H Hag HK g g'. unfold flag_rel in H.
  assert (Ev : uE (CC.env_over NF s E') (reg_e cj 20) = uE E' (CC.esubstL NF s (reg_e cj 20))) by (unfold uE; rewrite CC.esubstL_denot; reflexivity).
  set (e20' := CC.esubstL NF s (reg_e cj 20)) in *.
  assert (SF : match srcf with None | Some G0 => true | Some G1 => false | Some GS4 => lit_or_fact c 0 end = true -> g = false).
  { intros X. unfold g. destruct srcf as [[| |]|]; try reflexivity; try discriminate. unfold flag. rewrite (lit_or_fact_sem c 0 E M X HK) by lia. reflexivity. }
  assert (ST : match srcf with Some G1 => true | Some GS4 => lit_or_fact c 1 | _ => false end = true -> g = true).
  { intros X. unfold g. destruct srcf as [[| |]|]; try reflexivity; try discriminate. unfold flag. rewrite (lit_or_fact_sem c 1 E M X HK) by lia. reflexivity. }
  assert (TF : match f' with G0 => true | G1 => false | GS4 => is_lit e20' 0 end = true -> g' = false).
  { intros X. unfold g'. destruct f'; try reflexivity; try discriminate. unfold flag, is_lit in *. apply expr_eqb_eq in X. rewrite Ev, X, u_lit by lia. reflexivity. }
  assert (TT : match f' with G1 => true | G0 => false | GS4 => is_lit e20' 1 end = true -> g' = true).
  { intros X. unfold g'. destruct f'; try reflexivity; try discriminate. unfold flag, is_lit in *. apply expr_eqb_eq in X. rewrite Ev, X, u_lit by lia. reflexivity. }
  destruct cl; try discriminate.
  - apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
    + apply andb_prop in H as [H1 H2]. rewrite (SF H1), (TF H2). reflexivity.
    + apply andb_prop in H as [H1 H2]. rewrite (ST H1), (TT H2). reflexivity.
    + destruct srcf as [[| |]|]; try discriminate. destruct f'; try discriminate. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1.
      unfold g, g', flag. rewrite Ev, H1. unfold uE. rewrite (SR.edenot_agree_AP _ E E' _ Hag H2). reflexivity.
  - apply andb_prop in H as [H1 H2]. split; [exact (SF H1) | exact (TT H2)].
Qed.

Lemma eaddz_m1 : forall E e v, uE E e = v -> 1 <= v < 2 ^ 64 -> uE E (APC.eaddz e (-1)) = v - 1.
Proof.
  intros E e v H Hv. unfold uE, APC.eaddz in *. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite H.
  change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1). replace (v + (2 ^ 64 - 1)) with (v - 1 + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma eaddz_m1_0 : forall E e, uE E e = 0 -> uE E (APC.eaddz e (-1)) = 2 ^ 64 - 1.
Proof.
  intros E e H. unfold uE, APC.eaddz in *. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite H. reflexivity.
Qed.

Lemma cell_dec_sem : forall c ps E E' R R' (M M' : word -> option byte) W, cell_dec c ps = true -> CC.At segs c E R M ->
  env_agree NF E0 E -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts segs c ps E' R' M M' ->
  L5.u64_at segs M (F + 8) W -> 1 <= W < 2 ^ 64 -> L5.u64_at segs M' (F + 8) (W - 1).
Proof.
  intros c ps E E' R R' M M' W H [_ HK] Hag0 Hag0' Hag HLF HW RW. unfold cell_dec in H.
  destruct (find_cell (CC.cp_know c)) as [vs|] eqn:F1; [|discriminate]. destruct (find_cell (SR.ps_cells ps)) as [vl|] eqn:F2; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. subst vl.
  apply find_cell_In in F1, F2.
  assert (UF : bv_unsigned (ev E 21) = F) by (rewrite (ev_frozen E 21 Hag0) by lia; exact E0_F).
  assert (UF' : bv_unsigned (ev E' 21) = F) by (rewrite (ev_frozen E' 21 Hag0') by lia; exact E0_F).
  pose proof (CL5.kword64_elim segs E M rpos_a vs (F + 8) _ (proj1 (Forall_forall _ _) HK _ F1) (estart_reg E 21 8 F UF) eq_refl) as X1.
  assert (Bv : 0 <= bv_unsigned (edenot E vs) < 2 ^ 64) by (pose proof (u64_range (edenot E vs)) as B; unfold two64 in B; exact B).
  pose proof (u64_at_inj segs M (F + 8) _ _ X1 HW Bv ltac:(lia)) as Ev.
  pose proof (CL5.kword64_elim segs E' M' rpos_a _ (F + 8) _ (CC.lf_cells _ _ _ _ _ _ _ HLF _ F2) (estart_reg E' 21 8 F UF') eq_refl) as X2.
  assert (Ev' : uE E' vs = W) by (unfold uE; rewrite <- (SR.edenot_agree_AP _ E E' _ Hag H2); exact Ev).
  fold (uE E' (APC.eaddz vs (-1))) in X2. rewrite (eaddz_m1 E' vs W Ev' RW) in X2. exact X2.
Qed.

Lemma xi_goto : forall i c ps j cj s E R (M : word -> option byte) model E' R' M',
  nth_error CPS i = Some c -> nth_error CPS j = Some cj -> cut_chk i c = true -> cut_chk j cj = true ->
  CC.goto_chk NF c ps cj s = true -> goto_chk2 i c ps j cj s = true ->
  CC.At segs c E R M -> CL.pure_amb NF E0 M0 model0 F0x i E M model -> XI i E M ->
  env_agree (CC.cp_nx c) E E' -> CC.leaf_facts segs c ps E' R' M M' ->
  XI j (CC.env_over NF s E') M'.
Proof.
  intros i c ps j cj s E R M model E' R' M' Hc Hcj Ci Cj Hg H2 HAt HAmb HX Hag HLF.
  destruct (CC.goto_chk_sound segs NF c ps cj s E E' R' M M' Hg Hag HLF) as (_ & HAt' & _ & HagE2).
  set (E2 := CC.env_over NF s E') in *.
  assert (Hnf : (NF <= CC.cp_nx c)%nat) by (unfold cut_chk in Ci; do 2 (apply andb_prop in Ci as [Ci _]); apply Nat.leb_le; exact Ci).
  assert (HAmb' : CL.pure_amb NF E0 M0 model0 F0x j E2 M' model).
  { eapply CL.pure_amb_step with (c := c); [exact (sub_F_ok i c Ci) | exact Hnf | exact HAmb | exact Hag | exact HLF | apply CC.env_over_agree]. }
  destruct HAmb as (_ & Hag0 & _ & _). destruct HAmb' as (_ & Hag02 & Hfr' & _).
  assert (Hag0' : env_agree NF E0 E') by (eapply CC.env_agree_trans; [exact Hag0 | eapply CC.env_agree_le; [exact Hag | exact Hnf]]).
  pose proof R_Q as (RQ1 & RQ2 & RQ3). pose proof N_nonneg as HN0. pose proof D_range as HD.
  assert (HN1 : 1 <= N) by (destruct T_dig as (c0 & r0 & Et & _); unfold N; rewrite Et; cbn [length]; lia).
  unfold goto_chk2 in H2. unfold XI in HX |- *. rewrite Hc in HX. rewrite Hcj.
  pose proof Ci as Ci'. pose proof Cj as Cj'. unfold cut_chk in Ci', Cj'. apply andb_prop in Ci' as [_ Ci']. apply andb_prop in Cj' as [_ Cj'].
  assert (K48 : bv_unsigned (ev E2 48) = uE E' (CC.slook s 48)) by reflexivity.
  destruct (kind_of i) as [|f cl| | |] eqn:Ki; destruct (kind_of j) as [|f' cl'| | |] eqn:Kj; try discriminate H2; try exact I.
  -
    pose proof (sc_arrive f' cl' cj E2 R' M' Cj' HAt' Hag02 Hfr') as (A1 & A2 & A3). cbv zeta in A1, A2, A3.
    unfold XI_sc. cbv zeta. split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
    assert (U47 : uE E' (EVar 47) = N) by (unfold uE; cbn [edenot]; rewrite (ev_frozen E' 47 Hag0') by lia; exact E0_N).
    destruct T_dig as (c0 & r0 & Et & Hd0).
    apply orb_prop in H2 as [H2|H2]; apply andb_prop in H2 as [Hk Hf]; apply expr_eqb_eq in Hk.
    + pose proof (flag_rel_sem None CDig c f' cj s E E' M Hf Hag (proj2 HAt)) as G. cbv zeta in G. fold E2 in G.
      rewrite K48, Hk, (eaddz_m1 E' (EVar 47) N U47) by lia. rewrite G. replace (N - (N - 1)) with (0 + 1) by lia.
      apply (inv_read false false 0 c0); [lia | unfold txt'; rewrite Et; reflexivity | reflexivity | left; split; [exact Hd0 | reflexivity]].
    + rewrite K48, Hk, U47. rewrite Z.sub_diag. cbn [Z.to_nat skipn].
      assert (G : flag f' cj E2 = false).
      { unfold flag. destruct f'; try reflexivity; try discriminate. unfold is_lit in Hf. apply expr_eqb_eq in Hf.
        assert (Ev : uE E2 (reg_e cj 20) = uE E' (CC.esubstL NF s (reg_e cj 20))) by (unfold uE, E2; rewrite CC.esubstL_denot; reflexivity).
        rewrite Ev, Hf, u_lit by lia. reflexivity. }
      rewrite G. unfold D. change (Z.to_nat 0) with 0%nat. change (skipn 0 txt') with txt'. lia.
  -
    pose proof (sc_arrive f' cl' cj E2 R' M' Cj' HAt' Hag02 Hfr') as (A1 & A2 & A3). cbv zeta in A1, A2, A3.
    unfold XI_sc in HX |- *. cbv zeta in HX |- *. destruct HX as (B1 & B2 & B3 & B4).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
    pose proof Ci' as Sc. unfold sc_chk in Sc. do 5 (apply andb_prop in Sc as [Sc ?Y]). apply Nat.ltb_lt in Sc.
    assert (U48 : uE E' (EVar 48) = bv_unsigned (ev E 48)) by (unfold uE; cbn [edenot]; rewrite <- (proj1 Hag 48%nat Sc); reflexivity).
    set (k := bv_unsigned (ev E 48)) in *.
    apply orb_prop in H2 as [H2|H2]; apply andb_prop in H2 as [Hk Hf]; apply expr_eqb_eq in Hk.
    +
      assert (Hk1 : 1 <= k).
      { destruct (Z_le_gt_dec 1 k) as [?|Hk0]; [assumption|]. exfalso. assert (k = 0) by lia.
        rewrite K48, Hk, (eaddz_m1_0 E' (EVar 48)) in A1 by lia. lia. }
      rewrite K48, Hk, (eaddz_m1 E' (EVar 48) k U48) by lia.
      pose proof (flag_rel_sem (Some f) cl c f' cj s E E' M Hf Hag (proj2 HAt)) as G. cbv zeta in G. fold E2 in G.
      replace (N - (k - 1)) with (N - k + 1) by lia.
      apply (inv_read (flag f c E) (flag f' cj E2) (N - k) (uE E (reg_e c 10))); [lia | exact B3 | exact B4 |].
      destruct (reg_e c 10) as [z|cv| | | | | |] eqn:Ea0; try discriminate Y1.
      { destruct z; try discriminate Y1. apply andb_prop in Y1 as [_ Y1]. destruct cl; try discriminate Y1; contradiction. }
      apply andb_prop in Y1 as [_ Y1]. destruct HAt as [_ HK].
      destruct cl; try contradiction.
      * left. split; [exact (dig_sem c (EVar cv) E M Y1 HK) | exact G].
      * right. split; [exact (dot_sem c (EVar cv) E M Y1 HK) | exact G].
    +
      rewrite K48, Hk, U48.
      destruct cl; try discriminate Hf. destruct cl'; try discriminate Hf. destruct f; try discriminate Hf. destruct f'; try discriminate Hf.
      apply andb_prop in Hf as [Hf1 Hf2]. apply expr_eqb_eq in Hf1.
      assert (G : flag GS4 cj E2 = flag GS4 c E).
      { unfold flag. assert (Ev : uE E2 (reg_e cj 20) = uE E' (CC.esubstL NF s (reg_e cj 20))) by (unfold uE, E2; rewrite CC.esubstL_denot; reflexivity).
        rewrite Ev, Hf1. unfold uE. rewrite (SR.edenot_agree_AP _ E E' _ Hag Hf2). reflexivity. }
      rewrite G. exact B4.
  -
    unfold XI_sc in HX. cbv zeta in HX. destruct HX as (B1 & B2 & B3 & B4). set (k := bv_unsigned (ev E 48)) in *.
    assert (HDk : D = N - k).
    { pose proof Ci' as Sc. unfold sc_chk in Sc. do 5 (apply andb_prop in Sc as [Sc ?Y]). destruct HAt as [_ HK].
      apply (inv_stop (flag f c E) (N - k) (uE E (reg_e c 10))); [lia | exact B3 | exact B4 |].
      destruct (reg_e c 10) as [z|cv| | | | | |] eqn:Ea0; try discriminate Y1.
      - destruct z; try discriminate Y1. right. rewrite u_lit by lia. split; [reflexivity|]. lia.
      - apply andb_prop in Y1 as [_ Y1]. destruct cl; try discriminate H2.
        + right. cbn [cls_chk] in Y1. do 3 (apply andb_prop in Y1 as [Y1 ?Z]).
          pose proof (rng_in_sem E M _ _ _ _ HK Y1) as Rc.
          pose proof (know_in E M _ _ HK Z1) as F1. pose proof (know_in E M _ _ HK Z0) as F2. pose proof (know_in E M _ _ HK Z) as F3.
          cbn [kentry_ok] in F1, F2, F3.
          split; [apply nd_sem; [exact Rc | unfold uE; lia]|]. split; [apply np_sem; [exact Rc | unfold uE; lia]|]. apply ne_sem; [exact Rc | unfold uE; lia].
        + left. pose proof Y1 as Y1'. cbn [cls_chk] in Y1'. pose proof (rng_in_sem E M _ _ _ _ HK Y1') as Rc.
          split; [lia|]. destruct f; try discriminate Y. unfold flag. rewrite (lit_or_fact_sem c 1 E M Y HK) by lia. reflexivity. }
    replace (Q + D) with (Q + N + 1 - k - 1) by lia.
    assert (Hcd : cell_dec c ps = true) by (destruct cl; try discriminate H2; exact H2).
    apply (cell_dec_sem c ps E E' R R' M M' _ Hcd HAt Hag0 Hag0' Hag HLF B2). lia.
  -
    replace (Q + D) with (Q + D + 1 - 1) by lia. apply (cell_dec_sem c ps E E' R R' M M' _ H2 HAt Hag0 Hag0' Hag HLF HX). lia.
  -
    exact (foot2_rpos c E' M M' Ci' Hag0' (CC.lf_frame _ _ _ _ _ _ _ HLF) _ HX).
Qed.

Definition Amb := CVX.AmbX NF E0 M0 model0 F0x XI.

Lemma xi_leaf_ok : forall i j c, kind_eqb (kind_of i) (kind_of j) = true -> cut_chk i c = true -> CVX.xi_leaf NF E0 XI i j c.
Proof.
  intros i j c Hk Ci E E' E2 M M' HX Hag0 Hag Hfr _. unfold XI in *. unfold cut_chk in Ci. apply andb_prop in Ci as [Ci Ck]. apply andb_prop in Ci as [Ci _]. apply Nat.leb_le in Ci.
  destruct (kind_of i) eqn:Ki; destruct (kind_of j) eqn:Kj; try discriminate Hk; [exact I|].
  assert (Hag0' : env_agree NF E0 E') by (eapply CC.env_agree_trans; [exact Hag0 | eapply CC.env_agree_le; [exact Hag | exact Ci]]).
  exact (foot2_rpos c E' M M' Ck Hag0' Hfr _ HX).
Qed.
Lemma xi_call_ok : forall i j c, kind_eqb (kind_of i) (kind_of j) = true -> cut_chk i c = true -> CVX.xi_call NF E0 XI i j c (SP - 256) SP.
Proof.
  intros i j c Hk Ci E E' E2 M M' M2 HX Hag0 Hag Hfr Hgr Hfr2 _.
  pose proof (xi_leaf_ok i j c Hk Ci E E' E2 M M' HX Hag0 Hag Hfr Hgr) as HX'. unfold XI in *.
  destruct (kind_of i) eqn:Ki; destruct (kind_of j) eqn:Kj; try discriminate Hk; [exact I|]. pose proof R_SP. pose proof R_F. unfold PDC.STK_FLOOR in *.
  apply (u64_at_same segs M' M2 (F + 8) _ ltac:(lia) ltac:(lia)); [|exact HX'].
  intros x Hx. apply Hfr2. destruct AP_FS as [A|A]; lia.
Qed.

Lemma exit_facts : forall i c ps E R (M : word -> option byte) model E' R' M',
  nth_error CPS i = Some c -> cut_chk i c = true -> kind_eqb (kind_of i) KPost = true -> exit_regs_chk ps = true ->
  CC.At segs c E R M -> Amb i E M model -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts segs c ps E' R' M M' ->
  model = model0 /\ (forall r v, In (r, v) SAVE_VARS -> getr R' (Z_to_bv 5 (Z.of_nat r)) = ev E0 v)
  /\ bv_unsigned (getr R' 2%bv) = SP + 8416 /\ getr R' 3%bv = ev E0 3 /\ getr R' 4%bv = Z_to_bv 64 TPV
  /\ (forall a : word, out3 (bv_unsigned a) -> M' a = M0 a) /\ mem_grows M0 M' /\ L5.u64_at segs M' (F + 8) (Q + D).
Proof.
  intros i c ps E R M model E' R' M' Hc Ci Hk Hx HAt [HAmb HX] Hag HLF.
  pose proof Ci as Ci'. unfold cut_chk in Ci'. apply andb_prop in Ci' as [Ci' Ck]. apply andb_prop in Ci' as [Hnf _]. apply Nat.leb_le in Hnf.
  assert (HA' : CL.pure_amb NF E0 M0 model0 F0x 0%nat E' M' model).
  { eapply CL.pure_amb_step with (c := c); [exact (sub_F_ok i c Ci) | exact Hnf | exact HAmb | exact Hag | exact HLF | apply CC.env_agree_refl]. }
  destruct HA' as (Hm & Hag0' & Hfr & Hgr). split; [exact Hm|].
  unfold exit_regs_chk in Hx. do 3 (apply andb_prop in Hx as [Hx ?X]).
  pose proof R_SP. unfold PDC.STK_FLOOR in *.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros r v Hin. rewrite forallb_forall in Hx. specialize (Hx _ Hin). cbn [fst snd] in Hx.
    rewrite (CL.ps_reg_is_sound segs c ps E' R' M M' r (EVar v) HLF Hx). cbn [edenot]. apply (ev_frozen E' v Hag0').
    unfold SAVE_VARS in Hin. cbn in Hin. intuition (match goal with H : (_, _) = (_, _) |- _ => injection H as <- <- end; lia).
  - replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). rewrite (CL.ps_reg_is_sound segs c ps E' R' M M' 2 _ HLF X1).
    unfold APC.eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite (ev_frozen E' 2 Hag0') by lia. rewrite E0_sp. rewrite u64_of_Z by lia. apply Z.mod_small. lia.
  - replace (3%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 3)) by (apply bv_eq; reflexivity). rewrite (CL.ps_reg_is_sound segs c ps E' R' M M' 3 _ HLF X0). cbn [edenot]. apply (ev_frozen E' 3 Hag0'). lia.
  - replace (4%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 4)) by (apply bv_eq; reflexivity). rewrite (CL.ps_reg_is_sound segs c ps E' R' M M' 4 _ HLF X). reflexivity.
  - intros a Ha. apply Hfr. apply outside_F0x. exact Ha.
  - exact Hgr.
  - unfold XI in HX. destruct (kind_of i); try discriminate Hk. exact (foot2_rpos c E' M M' Ck Hag0' (CC.lf_frame _ _ _ _ _ _ _ HLF) _ HX).
Qed.

Variable K : ShapeAlg.TSet.
Variable A : PDC.addrs.
Hypothesis Hhalt : m_halted model0 = None.
Hypothesis Hlazy : m_vm_lazy model0 = [].
Hypothesis A_scx : PDC.a_scanexp A = SCANEXP.
Hypothesis A_tp : PDC.a_TP A - 164 = ERRNO.
Hypothesis A_img : PDC.a_img_lo A = IMG_LO /\ PDC.a_img_hi A = IMG_HI.
Hypothesis SCX : PDC.scanexp_contract segs A.
Hypothesis SP_al : SP mod 16 = 0.
Hypothesis D_STK : L5.defined M0 (SP - 256) 8672.
Hypothesis W_F : L5.writable segs M0 (F + 8) 8.
Hypothesis D_TXT : L5.defined M0 Q (N + 1).

Lemma ext_list_app : forall a b E n, APS.ext_list E n (a ++ b) = APS.ext_list (APS.ext_list E n a) (n + length a) b.
Proof.
  induction a as [|x a IH]; intros b E n; cbn [app APS.ext_list length]; [rewrite Nat.add_0_r; reflexivity|].
  rewrite IH. f_equal. lia.
Qed.
Lemma nmin_sem : forall E e, uE E e <> LMIN -> uE E (DAS.nmin_of e) = 0.
Proof.
  intros E e H. unfold uE, DAS.nmin_of, LMIN in *. cbn [edenot]. rewrite u_sltu64, u_sub64.
  change (bv_unsigned (Z_to_bv 64 9223372036854775808)) with 9223372036854775808. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  pose proof (u64_range (edenot E e)) as B. unfold two64 in B. set (x := bv_unsigned (edenot E e)) in *.
  destruct (Z.ltb_spec ((x - 9223372036854775808) mod 2 ^ 64) 1) as [Hl|Hl]; [|reflexivity]. exfalso.
  destruct (Z_lt_le_dec x 9223372036854775808).
  - replace (x - 9223372036854775808) with (x - 9223372036854775808 + 2 ^ 64 + (-1) * 2 ^ 64) in Hl by lia. rewrite Z.mod_add in Hl by lia. rewrite Z.mod_small in Hl by lia. lia.
  - rewrite Z.mod_small in Hl by lia. lia.
Qed.
Lemma skipn_app0 : forall (l : list Z) n, (n <= length l)%nat -> skipn n (l ++ [0]) = skipn n l ++ [0].
Proof. intros l n H. rewrite skipn_app. replace (n - length l)%nat with 0%nat by lia. reflexivity. Qed.

Lemma scx_ret_at : forall lmin c ps ra cj E' R' (M M' M2 : word -> option byte) R2 rposv,
  scx_ret_chk lmin c ps ra cj = true -> CVF.all_regs_chk ps = true -> CC.leaf_facts segs c ps E' R' M M' -> env_agree NF E0 E' -> (NF <= CC.cp_nx c)%nat ->
  let nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps) in
  APC.sr_vars_lt nx (CA.ps_reglist ps) = true -> APC.kn_vars_lt nx (scx_kn1 ps) = true -> APC.sr_vars_lt (nx + 16) (APC.sr_fresh (CA.ps_reglist ps) APC.caller_saved nx) = true ->
  (forall x : reg, In (ridx x) CVF.CSAVED -> getr R2 x = getr R' x) ->
  (forall a : word, ~ (SP - 80 <= bv_unsigned a < SP) -> ~ (F + 8 <= bv_unsigned a < F + 16) -> M2 a = M' a) -> mem_grows M' M2 ->
  L5.defined M' (SP - 80) 80 ->
  L5.u64_at segs M2 (F + 8) rposv -> 0 <= rposv < 2 ^ 64 ->
  (if lmin then getr R2 10%bv = Z_to_bv 64 LMIN else bv_unsigned (getr R2 10%bv) <> LMIN) ->
  let E2 := APS.ext_list E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) APC.caller_saved ++ [Z_to_bv 64 rposv]) in
  CC.At segs cj E2 R2 M2 /\ env_agree nx E' E2.
Proof.
  intros lmin c ps ra cj E' R' M M' M2 R2 rposv Hchk Xall HLF Hag0' Hnf nx V1 V2 V3 Hcs Hfr2 Hgr2 DEF' Hrp Rrp Ha0 E2.
  assert (Hnx : (48 <= nx)%nat) by (unfold nx, NF in *; lia).
  unfold scx_ret_chk in Hchk. fold nx in Hchk. do 4 (apply andb_prop in Hchk as [Hchk ?X]). apply CVF.regs_eqb_eq in X2. apply CVF.kn_eqb_eq in X1.
  set (regs := CA.ps_reglist ps) in *. set (vals := map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) APC.caller_saved) in *.
  pose proof (CVF.leaf_regs_ok segs c ps E' R' M M' Xall HLF) as HR. fold regs in HR.
  assert (Hag2 : env_agree nx E' E2) by apply APS.ext_list_agree.
  set (E2a := APS.ext_list E' nx vals).
  assert (EE : E2 = APS.ext_list E2a (nx + 16) [Z_to_bv 64 rposv]) by (unfold E2, E2a; rewrite ext_list_app; reflexivity).
  assert (Hag3 : env_agree (nx + 16) E2a E2) by (rewrite EE; apply APS.ext_list_agree).
  assert (HR1 : regs_ok E2 (APC.sr_fresh regs APC.caller_saved nx) R2).
  { apply (APS.regs_ok_agree' (nx + 16) E2a E2 _ R2 Hag3 V3). apply CH.fresh_regs_ok; [| exact V1 | repeat constructor; lia].
    intros r Hn. destruct (bv_eqb r 0) eqn:Er0.
    { assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er0; apply Z.eqb_eq in Er0; exact Er0).
      unfold sr_get. change (bv_eqb (0%bv : bv 5) 0) with true. cbn [edenot]. apply getr_zero. }
    assert (Hr0 : r <> 0%bv) by (intros ->; unfold bv_eqb in Er0; rewrite Z.eqb_refl in Er0; discriminate).
    rewrite (Hcs r (CVF.csaved_partition r Hr0 Hn)). exact (HR r). }
  assert (U2' : bv_unsigned (ev E' 2) = SP) by (rewrite (ev_frozen E' 2 Hag0') by lia; exact E0_sp).
  assert (UF' : bv_unsigned (ev E' 21) = F) by (rewrite (ev_frozen E' 21 Hag0') by lia; exact E0_F).
  pose proof R_SP. pose proof R_F. unfold PDC.STK_FLOOR in *.
  assert (U2 : bv_unsigned (ev E2 2) = SP) by (rewrite <- (proj1 Hag2 2%nat) by lia; exact U2').
  assert (HKN : know_ok segs E2 M2 (KWord rpos_a 8 (EVar (nx + 16)) :: KUnk (SA (EVar 2) (-80)) (ELit 80) :: scx_kn1 ps)).
  { apply Forall_cons; [|apply Forall_cons].
    - assert (U21 : bv_unsigned (ev E2 21) = F) by (rewrite <- (proj1 Hag2 21%nat) by lia; exact UF').
      apply (CL5.kword64_intro segs E2 M2 rpos_a (EVar (nx + 16)) (F + 8) rposv); [apply (estart_reg E2 21 8 F U21) | lia | lia | | exact Hrp].
      cbn [edenot]. unfold E2. replace (nx + 16)%nat with (nx + length vals)%nat by (unfold vals; rewrite length_map; reflexivity).
      rewrite APS.ext_list_at by (rewrite length_app; cbn; lia). rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
    - apply (CL5.kunk_intro segs E2 M2 _ _ (SP - 80) 80); [rewrite (estart_reg E2 2 (-80) SP U2); lia | apply elen_lit; lia | lia | lia | lia |].
      intros k Hk. apply Hgr2. apply DEF'. exact Hk.
    - assert (HK' : know_ok segs E' M' (SR.ps_cells ps)) by (apply Forall_forall; intros Y HY; exact (CC.lf_cells _ _ _ _ _ _ _ HLF Y HY)).

      set (M1 := fun x : word => if ((F + 8 <=? bv_unsigned x) && (bv_unsigned x <? F + 16))%bool then M2 x else M' x).
      assert (G1 : mem_grows M' M1) by (intros x Hx; unfold M1; destruct ((F + 8 <=? bv_unsigned x) && (bv_unsigned x <? F + 16))%bool; [apply Hgr2; exact Hx | exact Hx]).
      assert (G2 : mem_grows M1 M2).
      { intros x Hx. unfold M1 in Hx. destruct ((F + 8 <=? bv_unsigned x) && (bv_unsigned x <? F + 16))%bool eqn:Eb; [exact Hx | apply Hgr2; exact Hx]. }
      assert (HK1 : know_ok segs E' M1 (APC.kn_havoc (SR.ps_cells ps) (EVar 21) 8 (ELit 8))).
      { apply (APS.know_ok_havoc segs E' M' M1 _ _ _ _ HK'); [|exact G1]. intros x Hx. rewrite (estart_reg E' 21 8 F UF'), elen_lit in Hx by lia.
        unfold M1. destruct ((F + 8 <=? bv_unsigned x) && (bv_unsigned x <? F + 16))%bool eqn:Eb; [|reflexivity].
        apply andb_prop in Eb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. lia. }
      assert (HK2 : know_ok segs E' M2 (scx_kn1 ps)).
      { unfold scx_kn1. apply (APS.know_ok_havoc segs E' M1 M2 _ _ _ _ HK1); [|exact G2]. intros x Hx. rewrite (estart_reg E' 2 (-80) SP U2'), elen_lit in Hx by lia.
        unfold M1. destruct ((F + 8 <=? bv_unsigned x) && (bv_unsigned x <? F + 16))%bool eqn:Eb; [reflexivity|].
        apply Hfr2; [lia|]. apply andb_false_iff in Eb as [B|B]; [apply Z.leb_gt in B | apply Z.ltb_ge in B]; lia. }
      apply Forall_forall. intros Y HY.
      eapply SGP.kentry_ok_agree1; [exact Hag2 | exact (SGP.kn_vars_lt_In nx _ Y V2 HY) | exact (proj1 (Forall_forall _ _) HK2 Y HY)]. }
  split; [|exact Hag2]. split.
  - rewrite X2. destruct lmin; [|exact HR1].
    intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er0.
    { assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er0; apply Z.eqb_eq in Er0; exact Er0). cbn [edenot]. apply getr_zero. }
    rewrite nth_sr_upd. destruct (bv_eqb r 10) eqn:Er10.
    { assert (r = 10%bv) as -> by (apply bv_eq; unfold bv_eqb in Er10; apply Z.eqb_eq in Er10; exact Er10).
      change (ridx 10%bv) with 10%nat. cbn [Nat.eqb edenot]. exact Ha0. }
    assert (Hne : Nat.eqb (ridx r) 10 = false).
    { apply Nat.eqb_neq. intros Hx. unfold bv_eqb in Er10. apply Z.eqb_neq in Er10. apply Er10.
      unfold ridx in Hx. pose proof (bv_unsigned_in_range _ r). change (bv_unsigned (10%bv : bv 5)) with 10. lia. }
    rewrite Hne. rewrite (HR1 r). unfold sr_get. rewrite Er0. reflexivity.
  - rewrite X1. destruct lmin; [exact HKN|]. apply Forall_cons; [|exact HKN].
    cbn [kentry_ok]. fold (uE E2 (DAS.nmin_of (nth 10 (APC.sr_fresh regs APC.caller_saved nx) (ELit 0)))). rewrite nmin_sem; [lia|].
    unfold uE. pose proof (HR1 10%bv) as H10. unfold sr_get in H10. change (bv_eqb (10%bv : bv 5) 0) with false in H10. cbv iota in H10.
    change (ridx 10%bv) with 10%nat in H10. rewrite <- H10. exact Ha0.
Qed.

Lemma rpos_val : forall E k, bv_unsigned (ev E 32) = Q -> bv_unsigned (ev E 47) = N -> bv_unsigned (ev E 48) = k -> 0 <= k <= N -> uE E rpos_e = Q + N + 1 - k.
Proof.
  intros E k UQ UN Uk Hk. pose proof R_Q as (RQ1 & RQ2 & RQ3). pose proof N_nonneg.
  unfold uE, rpos_e, APC.esub, APC.eaddz, APC.eadd. rewrite !mkAlu_denot, u_sub64, !u_add64. cbn [edenot]. rewrite UQ, UN, Uk. rewrite u64_of_Z by lia.
  rewrite (Z.mod_small (Q + N)) by lia. rewrite (Z.mod_small (Q + N + 1)) by lia. apply Z.mod_small. lia.
Qed.
Lemma reg_read : forall regs E' R' n e, regs_ok E' regs R' -> (0 < n < 32)%nat -> nth n regs (ELit 0) = e -> getr R' (PDC.reg_of n) = edenot E' e.
Proof.
  intros regs E' R' n e HR Hn He. rewrite (HR (PDC.reg_of n)). unfold sr_get.
  assert (Hu : bv_unsigned (PDC.reg_of n) = Z.of_nat n) by (unfold PDC.reg_of; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; lia).
  assert (Hb : bv_eqb (PDC.reg_of n) 0 = false) by (unfold bv_eqb; rewrite Hu; change (bv_unsigned (0%bv : bv 5)) with 0; apply Z.eqb_neq; lia).
  rewrite Hb. unfold ridx. rewrite Hu, Nat2Z.id, He. reflexivity.
Qed.

Theorem scx_leaf_ok : forall i c ps, nth_error CPS i = Some c -> cut_chk i c = true -> SR.ps_pc ps = SCANEXP -> scx_chk i c ps = true ->
  CC.leaf_ok segs CPS Amb K FrmInv.fp_ok i c ps.
Proof.
  intros i c ps Hc Ci Hpc H fx' E R M model E' R' M' HAt [HAmb HX] HFP Hag HLF HIH.
  unfold scx_chk in H. set (regs := CA.ps_reglist ps) in *. set (nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps)) in *.
  destruct (kind_of i) as [|f cl| | |] eqn:Ki; try discriminate H. destruct f; try discriminate H. destruct cl; try discriminate H.
  destruct (reg_e c 10) as [|cv| | | | | |] eqn:Ea0; try discriminate H. destruct (nth 1 regs (ELit 1)) as [ra| | | | | | |] eqn:Era; try discriminate H.
  do 18 (apply andb_prop in H as [H ?X]). rename H into Xraw. apply Nat.ltb_lt in X16.
  apply expr_eqb_eq in X8, X7, X6. apply Z.leb_le in X5. apply Z.ltb_lt in X4. apply Z.eqb_eq in X3.
  apply existsb_exists in X as ([[[ja i'] k'] pc] & _ & X). do 3 (apply andb_prop in X as [X ?Y]). clear X Y1.
  destruct (kind_of ja) eqn:Kja; try discriminate Y0. destruct (kind_of (S ja)) eqn:Kjb; try discriminate Y0. clear Y0.
  destruct (nth_error CPS ja) as [cja|] eqn:Hcja; [|discriminate Y]. destruct (nth_error CPS (S ja)) as [cjb|] eqn:Hcjb; [|discriminate Y].
  apply andb_prop in Y as [Ya Yb].

  pose proof Ci as Ci'. unfold cut_chk in Ci'. apply andb_prop in Ci' as [Ci' Csc]. apply andb_prop in Ci' as [Hnf _]. apply Nat.leb_le in Hnf. rewrite Ki in Csc.
  assert (HA' : CL.pure_amb NF E0 M0 model0 F0x 0%nat E' M' model).
  { eapply CL.pure_amb_step with (c := c); [exact (sub_F_ok i c Ci) | exact Hnf | exact HAmb | exact Hag | exact HLF | apply CC.env_agree_refl]. }
  destruct HA' as (-> & Hag0' & Hfr & Hgr).
  unfold XI in HX. rewrite Ki, Hc in HX. unfold XI_sc in HX. cbv zeta in HX. destruct HX as (B1 & B2 & B3 & B4). rewrite Ea0 in B3.
  set (k := bv_unsigned (ev E 48)) in *.
  pose proof R_SP. pose proof R_F. pose proof R_Q as (RQ1 & RQ2 & RQ3). pose proof R_ERR. pose proof N_nonneg as HN0. pose proof len_txt' as Ltxt. unfold PDC.STK_FLOOR in *.
  pose proof (CVF.leaf_regs_ok segs c ps E' R' M M' X9 HLF) as HR. fold regs in HR.
  assert (HK' : know_ok segs E' M' (SR.ps_cells ps)) by (apply Forall_forall; intros Y HY; exact (CC.lf_cells _ _ _ _ _ _ _ HLF Y HY)).
  assert (U2' : bv_unsigned (ev E' 2) = SP) by (rewrite (ev_frozen E' 2 Hag0') by lia; exact E0_sp).
  assert (UF' : bv_unsigned (ev E' 21) = F) by (rewrite (ev_frozen E' 21 Hag0') by lia; exact E0_F).
  assert (UQ' : bv_unsigned (ev E' 32) = Q) by (rewrite (ev_frozen E' 32 Hag0') by lia; exact E0_Q).
  assert (UN' : bv_unsigned (ev E' 47) = N) by (rewrite (ev_frozen E' 47 Hag0') by lia; exact E0_N).
  assert (Uk' : bv_unsigned (ev E' 48) = k) by (unfold k; rewrite (proj1 Hag 48%nat); [reflexivity | unfold sc_chk in Csc; do 5 (apply andb_prop in Csc as [Csc _]); apply Nat.ltb_lt in Csc; exact Csc]).

  set (ch := uE E (EVar cv)) in *.
  assert (Ech : uE E' (EVar cv) = ch) by (unfold ch, uE; cbn [edenot]; rewrite (proj1 Hag cv X16); reflexivity).
  assert (Rch : 0 <= ch <= 255).
  { unfold sc_chk in Csc. do 3 (apply andb_prop in Csc as [Csc ?Z]). rewrite Ea0 in Z1. apply andb_prop in Z1 as [_ Z1]. exact (cls_range CStopS c (EVar cv) E M Z1 (proj2 HAt)). }
  assert (Hce : ch = 69 \/ ch = 101).
  { rewrite <- Ech. apply raw_e_sem; [rewrite Ech; exact Rch|]. pose proof (know_in E' M' _ _ HK' Xraw) as Y. cbn [kentry_ok] in Y. unfold uE. lia. }
  assert (Hk1 : 1 <= k).
  { destruct (Z_le_gt_dec 1 k) as [?|Hk0]; [assumption|]. exfalso. assert (k = 0) by lia. replace (N - k) with N in B3 by lia.
    unfold txt' in B3. rewrite app_nth2 in B3 by (unfold N; lia). replace (Z.to_nat N - length txt)%nat with 0%nat in B3 by (unfold N; lia). cbn [nth] in B3. lia. }
  set (idx := N - k) in *. set (P' := Q + N + 1 - k).
  set (txe := skipn (Z.to_nat (idx + 1)) txt).
  assert (Ltxe : Z.of_nat (length txe) = k - 1) by (unfold txe; rewrite length_skipn; unfold idx, N in *; lia).

  assert (HD : D = idx + match PD.exp_scan txe with Some k2 => 1 + k2 | None => 0 end).
  { rewrite B4. f_equal. rewrite (PDS.skipn_nth txt' (Z.to_nat idx) 0) by lia. rewrite B3. rewrite (PDS.contD_exp _ ch _ Hce).
    replace (S (Z.to_nat idx)) with (Z.to_nat (idx + 1)) by lia. unfold txt'. rewrite skipn_app0 by (unfold idx, N in *; lia). fold txe. rewrite PDS.exp_scan_app0. reflexivity. }

  assert (G10 : PDC.rz R' 10 = F) by (unfold PDC.rz; rewrite (reg_read regs E' R' 10 _ HR ltac:(lia) X8); exact UF').
  assert (G11 : PDC.rz R' 11 = 1) by (unfold PDC.rz; rewrite (reg_read regs E' R' 11 _ HR ltac:(lia) X7); cbn [edenot]; apply u64_of_Z; lia).
  assert (G2 : PDC.rz R' 2 = SP) by (unfold PDC.rz; rewrite (reg_read regs E' R' 2 _ HR ltac:(lia) X6); exact U2').
  assert (G1 : getr R' (PDC.reg_of 1) = Z_to_bv 64 ra).
  { apply (reg_read regs E' R' 1 (ELit ra) HR ltac:(lia)). rewrite (nth_indep regs (ELit 0) (ELit 1)) by (unfold regs; rewrite CVF.reglist_len; lia). exact Era. }
  assert (DEF' : L5.defined M' (SP - 80) 80).
  { intros d Hd. apply Hgr. replace (SP - 80 + d) with (SP - 256 + (176 + d)) by lia. apply D_STK. lia. }

  assert (TXT' : forall j, 0 <= j <= N -> L5.u8_at segs M' (Q + j) (nth (Z.to_nat j) txt' 0)).
  { intros j Hj. apply (u8_at_same segs M0 M' (Q + j) _ ltac:(lia) ltac:(lia)); [|exact (proj1 (text_byte j Hj))].
    intros x Hx. apply Hfr. apply outside_F0x. unfold out3. rewrite Hx. destruct AP_TS as [?|?], AP_TF as [?|?], AP_TE as [?|?]; lia. }
  assert (Hrp' : L5.u64_at segs M' (F + 8) P').
  { pose proof (know_in E' M' _ _ HK' X15) as Y. apply (CL5.kword64_elim segs E' M' rpos_a rpos_e (F + 8) _ Y (estart_reg E' 21 8 F UF')).
    exact (rpos_val E' k UQ' UN' Uk' B1). }
  destruct A_img as [AI1 AI2].
  assert (Rtx : Forall (fun c0 => 0 <= c0 < 256) txe).
  { apply Forall_forall. intros x Hx. rewrite Forall_forall in T_rng. apply T_rng. unfold txe in Hx. rewrite <- (firstn_skipn (Z.to_nat (idx + 1)) txt). apply in_or_app. right. exact Hx. }
  rewrite Hpc, <- A_scx.
  eapply (SCX fx' R' M' model0 K SP F P' txe Hhalt Hlazy HFP G2 SP_al).
  - unfold PDC.STK_FLOOR. lia.
  - exact DEF'.
  - apply (L5C.writable_of_defined segs M' (SP - 80) 80 DEF'); lia.
  - exact G10.
  - exact G11.
  - rewrite G1. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact X3.
  -
    unfold PDC.file_ok, PDC.STK_FLOOR. split; [exact Hrp'|]. split; [|split; [|split; [|lia]]].
    + pose proof (know_in E' M' _ _ HK' X14) as Y. apply (CL5.kword64_elim segs E' M' _ _ (F + 184) _ Y (estart_reg E' 21 184 F UF')). cbn [edenot]. apply u64_of_Z. lia.
    + pose proof (know_in E' M' _ _ HK' X13) as Y. apply (CL5.kword64_elim segs E' M' _ _ (F + 192) _ Y (estart_reg E' 21 192 F UF')). cbn [edenot]. apply u64_of_Z. lia.
    + exact (L5.writable_grows segs M0 M' _ _ Hgr W_F).
  - unfold PDC.apart. destruct AP_FS as [?|?]; lia.
  -
    unfold PDC.text_ok. rewrite Ltxe. split; [|split; [|split; [lia | split; [unfold P'; lia | split; [lia | split; [|exact Rtx]]]]]].
    + intros j Hj. pose proof (TXT' (idx + 1 + Z.of_nat j) ltac:(lia)) as Y. replace (P' + Z.of_nat j) with (Q + (idx + 1 + Z.of_nat j)) by (unfold P', idx; lia).
      replace (nth j txe 0) with (nth (Z.to_nat (idx + 1 + Z.of_nat j)) txt' 0); [exact Y|].
      unfold txe, txt'. rewrite nth_skipn. rewrite app_nth1 by (unfold idx, N in *; lia). f_equal. lia.
    + replace (P' + (k - 1)) with (Q + N) by (unfold P'; lia). pose proof (TXT' N ltac:(lia)) as Y.
      unfold txt' in Y. rewrite app_nth2 in Y by (unfold N; lia). replace (Z.to_nat N - length txt)%nat with 0%nat in Y by (unfold N; lia). exact Y.
    + intros d Hd. apply Hgr. replace (P' + d) with (Q + (idx + 1 + d)) by (unfold P', idx; lia). apply D_TXT. unfold idx. lia.
  - unfold PDC.text_apart, PDC.apart. rewrite Ltxe, A_tp. cbv zeta. unfold P'. destruct AP_TS as [?|?], AP_TF as [?|?], AP_TE as [?|?]; lia.
  - rewrite AI1, AI2. pose proof (know_in E' M' _ _ HK' X10) as Y. cbn [kentry_ok] in Y. exact (proj2 (proj2 Y)).
  -
    intros fx2 R2 M2 HFP2 Hfr2 Hgr2 Hcs2 Hres.
    assert (Hcs : forall x : reg, In (ridx x) CVF.CSAVED -> getr R2 x = getr R' x).
    { intros x Hx. rewrite <- (CC.reg_of_ridx x). apply (Hcs2 (ridx x)). exact Hx. }
    rewrite G1.
    assert (COMMON : forall lmin j cj rposv, nth_error CPS j = Some cj -> scx_ret_chk lmin c ps ra cj = true ->
               L5.u64_at segs M2 (F + 8) rposv -> 0 <= rposv < 2 ^ 64 ->
               (if lmin then getr R2 10%bv = Z_to_bv 64 LMIN else bv_unsigned (getr R2 10%bv) <> LMIN) ->
               (forall E2, XI j E2 M2) ->
               srealizes segs SCFG (mkCfg (@mkst fx2 R2 (Z_to_bv 64 ra) M2 (seg_rom segs)) model0) K).
    { intros lmin j cj rposv Hcj Hrc Hrp2 Rrp2 Ha0 HXj.
      destruct (scx_ret_at lmin c ps ra cj E' R' M M' M2 R2 rposv Hrc X9 HLF Hag0' Hnf X2 X1 X0 Hcs Hfr2 Hgr2 DEF' Hrp2 Rrp2 Ha0) as [HAtj Hag2].
      fold nx in Hag2. set (E2 := APS.ext_list E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) APC.caller_saved ++ [Z_to_bv 64 rposv])) in *.
      pose proof Hrc as Hrc'. unfold scx_ret_chk in Hrc'. do 4 (apply andb_prop in Hrc' as [Hrc' ?Z]). apply Z.eqb_eq in Hrc'. apply expr_eqb_eq in Z.
      rewrite <- Hrc'. apply (HIH j cj fx2 E2 R2 M2 model0 Hcj HAtj).
      - split; [|exact (HXj E2)]. split; [reflexivity|]. split.
        + eapply CC.env_agree_trans; [exact Hag0' | eapply CC.env_agree_le; [exact Hag2 | unfold nx; lia]].
        + split; [|eapply mem_grows_trans; [exact Hgr | exact Hgr2]].
          intros a Ha. apply F0x_out3 in Ha. destruct Ha as (O1 & O2 & O3). rewrite Hfr2 by lia. apply Hfr. apply outside_F0x. unfold out3. lia.
      - exact HFP2.
      - unfold CC.meas. rewrite Z. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
        assert (Hnxc : (CC.cp_nx c <= nx)%nat) by (unfold nx; lia).
        assert (Em : edenot E2 (CC.cp_meas c) = edenot E (CC.cp_meas c)).
        { rewrite <- (SR.edenot_agree_AP _ E' E2 _ (CC.env_agree_le _ _ _ _ Hag2 Hnxc) X11). symmetry. exact (SR.edenot_agree_AP _ E E' _ Hag X11). }
        rewrite Em. pose proof (know_in E' M' _ _ HK' X12) as HM. cbn [kentry_ok] in HM.
        rewrite <- (SR.edenot_agree_AP _ E E' _ Hag X11) in HM. unfold CC.MB in HM.
        rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia. }
    pose proof D_range as HDr.
    destruct (PD.exp_scan txe) as [k2|] eqn:Eexp.
    + destruct Hres as [Hr1 Hr2].
      assert (Rk2 : 0 <= P' + k2 < 2 ^ 64) by (unfold P'; lia).
      apply (COMMON false (S ja) cjb (P' + k2) Hcjb Yb Hr1 Rk2).
      * unfold PDC.rz in Hr2. replace (10%bv : bv 5) with (PDC.reg_of 10) by (apply bv_eq; reflexivity). exact Hr2.
      * intros E2. unfold XI. rewrite Kjb. replace (Q + D) with (P' + k2) by (unfold P', idx in *; lia). exact Hr1.
    + destruct Hres as [Hr1 Hr2].
      apply (COMMON true ja cja P' Hcja Ya Hr1 ltac:(unfold P'; lia)).
      * unfold PDC.rz in Hr2. replace (10%bv : bv 5) with (PDC.reg_of 10) by (apply bv_eq; reflexivity).
        apply bv_eq. rewrite Hr2. unfold LMIN. rewrite u64_of_Z by lia. reflexivity.
      * intros E2. unfold XI. rewrite Kja. replace (Q + D + 1) with P' by (unfold P', idx in *; lia). exact Hr1.
Qed.

End Cert.
End DOS.
