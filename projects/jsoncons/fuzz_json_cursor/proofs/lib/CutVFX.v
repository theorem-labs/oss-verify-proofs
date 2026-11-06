(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan L5Defs L5Core FrmInv FpBridge CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutHeap CutAuto CutLib.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CVX.
Section WithSegs.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Variable CPS : list CC.cutpoint.
Variable NF : nat.
Variable E0 : env.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variable F0x : list SGP.region.
Variable K : ShapeAlg.TSet.
Variable XI : nat -> env -> (word -> option byte) -> Prop.
Hypothesis Hhalt : m_halted model0 = None.
Hypothesis Hlazy : m_vm_lazy model0 = [].
Hypothesis SAFE : FrmInv.text_safe segs.

Definition AmbX (i : nat) (E : env) (M : word -> option byte) (model : Model) : Prop :=
  CL.pure_amb NF E0 M0 model0 F0x i E M model /\ XI i E M.
Abbreviation mk fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).

Lemma ambx_model : forall i E M model, AmbX i E M model -> m_halted model = None /\ m_vm_lazy model = [].
Proof. intros i E M model [H _]. exact (CL.pure_amb_model NF E0 M0 model0 F0x i E M model Hhalt Hlazy H). Qed.

Definition xi_leaf (i j : nat) (c : CC.cutpoint) : Prop :=
  forall E E' E2 M M', XI i E M -> env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' ->
    (forall a : word, SGP.outside E' (CC.cp_F c) a -> M' a = M a) -> mem_grows M M' -> XI j E2 M'.

Definition xi_call (i j : nat) (c : CC.cutpoint) (lo hi : Z) : Prop :=
  forall E E' E2 M M' M2, XI i E M -> env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' ->
    (forall a : word, SGP.outside E' (CC.cp_F c) a -> M' a = M a) -> mem_grows M M' ->
    (forall a : word, ~ (lo <= bv_unsigned a < hi) -> M2 a = M' a) -> mem_grows M' M2 -> XI j E2 M2.

Lemma ambx_goto : forall i c ps j s,
  CL.sub_F NF E0 F0x c -> (NF <= CC.cp_nx c)%nat ->
  (forall E R M model E' R' M', CC.At segs c E R M -> AmbX i E M model -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts segs c ps E' R' M M' ->
       XI j (CC.env_over NF s E') M') ->
  CC.amb_goto segs AmbX NF i c ps j s.
Proof.
  intros i c ps j s Hsub Hnf HX E R M model E' R' M' HAt HAmb Hag HLF. split.
  - exact (CL.pure_amb_goto segs NF E0 M0 model0 F0x i c ps j s Hsub Hnf E R M model E' R' M' HAt (proj1 HAmb) Hag HLF).
  - exact (HX E R M model E' R' M' HAt HAmb Hag HLF).
Qed.

Lemma inl_commonX : forall i c ps j cj len hv a0,
  nth_error CPS j = Some cj -> CVF.inl_chk c ps cj len hv a0 = true -> CL.sub_F NF E0 F0x c -> (NF <= CC.cp_nx c)%nat -> xi_leaf i j c ->
  forall (fx2 : FPState) E R M model E' R' R2 M',
    CC.At segs c E R M -> AmbX i E M model -> FrmInv.fp_ok fx2 ->
    env_agree (CC.cp_nx c) E E' -> CC.leaf_facts segs c ps E' R' M M' ->
    CC.IH segs CPS AmbX K FrmInv.fp_ok (CC.meas c E) ->
    (forall r : reg, ~ In (ridx r) hv -> getr R2 r = match a0 with Some z => if bv_eqb r 10 then Z_to_bv 64 z else getr R' r | None => getr R' r end) ->
    srealizes segs SCFG (mkCfg (mk fx2 R2 (SR.ps_pc ps + len) M') model) K.
Proof.
  intros i c ps j cj len hv a0 Hcj Hchk Hsub Hnf HXI fx2 E R M model E' R' R2 M' HAt [HAmb HX] HFP Hag HLF HIH Hkeep.
  unfold CVF.inl_chk in Hchk. do 11 (apply andb_prop in Hchk as [Hchk ?X]).
  rename Hchk into Xall. apply Z.eqb_eq in X9. apply CVF.regs_eqb_eq in X8. apply CVF.kn_eqb_eq in X7. apply Nat.eqb_eq in X6. apply AX2S.expr_eqb_eq in X5.
  set (nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps)) in *.
  set (regs := CA.ps_reglist ps) in *.
  pose proof (CVF.leaf_regs_ok segs c ps E' R' M M' Xall HLF) as HR. fold regs in HR.
  set (E2 := APS.ext_list E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) hv)).
  pose proof (APS.ext_list_agree E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) hv) : env_agree nx E' E2) as Hag2.
  assert (Hnxc : (CC.cp_nx c <= nx)%nat) by (unfold nx; lia).
  assert (HagNF : env_agree NF E' E2) by (eapply CC.env_agree_le; [exact Hag2 | lia]).
  assert (Hhv : Forall (fun r => (0 < r < 32)%nat) hv).
  { apply Forall_forall. intros r Hr. rewrite forallb_forall in X0. specialize (X0 r Hr). apply andb_prop in X0 as [A B].
    apply Nat.ltb_lt in A. apply Nat.ltb_lt in B. lia. }
  rewrite <- X9.
  apply (HIH j cj fx2 E2 R2 M' model Hcj).
  -
    split.
    + rewrite X8. destruct a0 as [z|].
      * apply andb_prop in X as [X Xhv]. apply andb_prop in X as [Xz0 Xz1]. apply Z.leb_le in Xz0. apply Z.ltb_lt in Xz1.
        destruct hv; [|discriminate]. cbn [APC.sr_fresh].
        intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er0.
        { assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er0; apply Z.eqb_eq in Er0; exact Er0). cbn [edenot]. apply getr_zero. }
        rewrite nth_sr_upd. rewrite (Hkeep r (fun X => X)).
        destruct (bv_eqb r 10) eqn:Er10.
        { assert (r = 10%bv) as -> by (apply bv_eq; unfold bv_eqb in Er10; apply Z.eqb_eq in Er10; exact Er10).
          change (ridx 10%bv) with 10%nat. cbn [Nat.eqb edenot]. reflexivity. }
        assert (Hne : Nat.eqb (ridx r) 10 = false).
        { apply Nat.eqb_neq. intros Hx. unfold bv_eqb in Er10. apply Z.eqb_neq in Er10. apply Er10.
          unfold ridx in Hx. pose proof (bv_unsigned_in_range _ r). change (bv_unsigned (10%bv : bv 5)) with 10. lia. }
        rewrite Hne. rewrite (HR r). unfold sr_get. rewrite Er0.
        apply (SR.edenot_agree_AP nx); [exact Hag2 | apply CH.nth_vars_lt; exact X3].
      * apply CH.fresh_regs_ok; [| exact X3 | exact Hhv].
        intros r Hn. rewrite (Hkeep r Hn). exact (HR r).
    + rewrite X7. unfold know_ok. apply Forall_forall. intros Y HY.
      eapply SGP.kentry_ok_agree1; [exact Hag2 | exact (SGP.kn_vars_lt_In nx _ Y X2 HY) | exact (CC.lf_cells _ _ _ _ _ _ _ HLF Y HY)].
  -
    split.
    + eapply CL.pure_amb_step; [exact Hsub | exact Hnf | exact HAmb | exact Hag | exact HLF | exact HagNF].
    + exact (HXI E E' E2 M M' HX (proj1 (proj2 HAmb)) Hag (CC.lf_frame _ _ _ _ _ _ _ HLF) (CC.lf_grows _ _ _ _ _ _ _ HLF)).
  - exact HFP.
  -
    unfold CC.meas. rewrite X5. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
    assert (Em : edenot E2 (CC.cp_meas c) = edenot E (CC.cp_meas c)).
    { rewrite <- (SR.edenot_agree_AP _ E' E2 _ (CC.env_agree_le _ _ _ _ Hag2 Hnxc) X1). symmetry. exact (SR.edenot_agree_AP _ E E' _ Hag X1). }
    rewrite Em. unfold CA.has in X4. apply existsb_exists in X4 as (Y & HY & Heq). apply APS.kentry_eqb_eq in Heq. subst Y.
    pose proof (CC.lf_cells _ _ _ _ _ _ _ HLF _ HY) as HM. cbn [kentry_ok] in HM.
    rewrite <- (SR.edenot_agree_AP _ E E' _ Hag X1) in HM. unfold CC.MB in HM.
    rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
Qed.

Theorem inl_leaf_okX : forall i c ps j cj len hv,
  nth_error CPS j = Some cj -> CVF.inl_chk c ps cj len hv None = true -> CL.sub_F NF E0 F0x c -> (NF <= CC.cp_nx c)%nat -> xi_leaf i j c ->
  FPB.inl_step segs (SR.ps_pc ps) len hv ->
  CC.leaf_ok segs CPS AmbX K FrmInv.fp_ok i c ps.
Proof.
  intros i c ps j cj len hv Hcj Hchk Hsub Hnf HXI Hstep fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct (Hstep fx' R' M' HFP) as (fx2 & R2 & Hms & Hkeep).
  pose proof HAmb as ((-> & _) & _).
  eapply L5.cps_of_msteps; [exact Hhalt | exact Hlazy | exact Hms |].
  eapply (inl_commonX i c ps j cj len hv None Hcj Hchk Hsub Hnf HXI fx2 E R M model0 E' R' R2 M'); try eassumption.
  exact (FrmInv.msteps_fp_ok segs SAFE _ _ _ _ _ _ _ _ _ _ Hms HFP).
Qed.

Theorem inl_leaf_ok_a0X : forall i c ps j cj len z,
  nth_error CPS j = Some cj -> CVF.inl_chk c ps cj len [] (Some z) = true -> CL.sub_F NF E0 F0x c -> (NF <= CC.cp_nx c)%nat -> xi_leaf i j c ->
  FPB.inl_step_a0 segs (SR.ps_pc ps) len z ->
  CC.leaf_ok segs CPS AmbX K FrmInv.fp_ok i c ps.
Proof.
  intros i c ps j cj len z Hcj Hchk Hsub Hnf HXI Hstep fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct (Hstep fx' R' M' HFP) as (fx2 & Hms).
  pose proof HAmb as ((-> & _) & _).
  eapply L5.cps_of_msteps; [exact Hhalt | exact Hlazy | exact Hms |].
  eapply (inl_commonX i c ps j cj len [] (Some z) Hcj Hchk Hsub Hnf HXI fx2 E R M model0 E' R' _ M'); try eassumption.
  - exact (FrmInv.msteps_fp_ok segs SAFE _ _ _ _ _ _ _ _ _ _ Hms HFP).
  - intros r _. destruct (bv_eqb r 10) eqn:Er.
    + assert (r = 10%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er). apply getr_same. discriminate.
    + apply getr_other. intros ->. unfold bv_eqb in Er. rewrite Z.eqb_refl in Er. discriminate.
Qed.

Theorem call_leaf_okX : forall (SCR sp0 : Z) (XF : list SGP.region) i c ps j cj SCRc IMGc,
  (32 <= NF)%nat -> 0 < SCR -> F0x = (EVar 2, - SCR, ELit SCR) :: XF ->
  bv_unsigned (ev E0 2) = sp0 -> sp0 mod 16 = 0 -> 140735332483072 + SCR <= sp0 <= 140737488355328 -> L5.defined M0 (sp0 - SCR) SCR ->
  nth_error CPS j = Some cj -> CVF.call_chk SCR c ps cj SCRc IMGc = true -> CVF.vf_contract segs (SR.ps_pc ps) SCRc IMGc ->
  CL.sub_F NF E0 F0x c -> (NF <= CC.cp_nx c)%nat -> xi_call i j c (sp0 - SCR) sp0 ->
  CC.leaf_ok segs CPS AmbX K FrmInv.fp_ok i c ps.
Proof.
  intros SCR sp0 XF i c ps j cj SCRc IMGc HNF32 HSCR EF0 U2 Hal Hrange Hdef Hcj Hchk Hcallee Hsub Hnf HXI
         fx' E R M model E' R' M' HAt [HAmb HX] HFP Hag HLF HIH.
  unfold CVF.call_chk in Hchk.
  set (regs := CA.ps_reglist ps) in *. set (nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps)) in *.
  destruct (nth 1 regs (ELit 1)) as [ra| | | | | | |] eqn:Era; try discriminate.
  destruct (split_lit (nth 2 regs (ELit 0))) as [spb spo] eqn:Esp.
  do 18 (apply andb_prop in Hchk as [Hchk ?X]). rename Hchk into Xall.
  apply Z.eqb_eq in X16. apply Z.leb_le in X15. apply Z.ltb_lt in X14. apply Z.eqb_eq in X13. apply AX2S.expr_eqb_eq in X12. subst spb.
  apply Z.leb_le in X11. apply Z.leb_le in X10. apply Z.eqb_eq in X9. apply Z.ltb_lt in X8.
  apply CVF.regs_eqb_eq in X7. apply CVF.kn_eqb_eq in X6. apply Nat.eqb_eq in X5. apply AX2S.expr_eqb_eq in X4.
  assert (Hnxc : (CC.cp_nx c <= nx)%nat) by (unfold nx; lia).
  pose proof (CVF.leaf_regs_ok segs c ps E' R' M M' Xall HLF) as HR. fold regs in HR.
  assert (HA' : CL.pure_amb NF E0 M0 model0 F0x 0%nat E' M' model).
  { eapply CL.pure_amb_step with (c := c); [exact Hsub | exact Hnf | exact HAmb | exact Hag | exact HLF | apply CC.env_agree_refl]. }
  pose proof (proj1 (proj2 HAmb)) as HagE0.
  destruct HA' as (-> & HagE & Hfr & Hgr).
  assert (E2v : forall Ex, env_agree NF E0 Ex -> bv_unsigned (ev Ex 2) = sp0).
  { intros Ex [Hv _]. rewrite <- (Hv 2%nat) by lia. exact U2. }
  set (spc := sp0 + spo).
  assert (Hra : getr R' 1%bv = Z_to_bv 64 ra).
  { rewrite (HR 1%bv). unfold sr_get. change (bv_eqb (1%bv : bv 5) 0) with false. cbv iota. change (ridx 1%bv) with 1%nat.
    rewrite (nth_indep regs (ELit 0) (ELit 1)) by (unfold regs; rewrite CVF.reglist_len; lia). rewrite Era. reflexivity. }
  assert (Hspv : getr R' 2%bv = Z_to_bv 64 spc).
  { rewrite (HR 2%bv). unfold sr_get. change (bv_eqb (2%bv : bv 5) 0) with false. cbv iota. change (ridx 2%bv) with 2%nat.
    rewrite (APS.split_lit_denot E' _ _ _ Esp). cbn [edenot]. rewrite (E2v E' HagE). reflexivity. }
  assert (DEF' : L5.defined M' (spc - SCRc) SCRc).
  { intros k Hk. apply Hgr. replace (spc - SCRc + k) with (sp0 - SCR + (spc - SCRc + k - (sp0 - SCR))) by lia. apply Hdef. unfold spc. lia. }
  eapply (Hcallee fx' R' M' model0 K spc Hhalt Hlazy HFP Hspv).
  - unfold spc. rewrite Z.add_mod by lia. rewrite Hal, X9. reflexivity.
  - unfold spc. lia.
  - exact DEF'.
  - unfold CVF.img_pre_of. destruct IMGc as [[lo hi]|]; [|exact I].
    unfold CA.has in X. apply existsb_exists in X as (Y & HY & Heq). apply APS.kentry_eqb_eq in Heq. subst Y.
    exact (CC.lf_cells _ _ _ _ _ _ _ HLF _ HY).
  - rewrite Hra. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact X13.
  - intros fx2 R2 M2 HFP2 Hfr2 Hgr2 Hcs2.
    rewrite Hra, <- X16.
    set (E2 := APS.ext_list E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) APC.caller_saved)).
    pose proof (APS.ext_list_agree E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) APC.caller_saved) : env_agree nx E' E2) as Hag2.
    assert (HagNF : env_agree NF E' E2) by (eapply CC.env_agree_le; [exact Hag2 | lia]).
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE | exact HagNF]).
    apply (HIH j cj fx2 E2 R2 M2 model0 Hcj).
    + split.
      * rewrite X7. apply CH.fresh_regs_ok; [| exact X2 | repeat constructor; lia].
        intros r Hn. destruct (bv_eqb r 0) eqn:Er0.
        { assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er0; apply Z.eqb_eq in Er0; exact Er0).
          unfold sr_get. change (bv_eqb (0%bv : bv 5) 0) with true. cbn [edenot]. apply getr_zero. }
        assert (Hr0 : r <> 0%bv) by (intros ->; unfold bv_eqb in Er0; rewrite Z.eqb_refl in Er0; discriminate).
        rewrite (Hcs2 r (CVF.csaved_partition r Hr0 Hn)). exact (HR r).
      * rewrite X6. unfold know_ok. apply Forall_cons.
        { cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite (E2v E2 HagE2). rewrite u64_of_Z by lia.
          split; [lia|]. intros k Hk. apply Hgr2. replace (sp0 + (spo - SCRc) + k) with (spc - SCRc + k) by (unfold spc; lia). apply DEF'. exact Hk. }
        assert (HK' : know_ok segs E' M' (SR.ps_cells ps)).
        { unfold know_ok. apply Forall_forall. intros Y HY. exact (CC.lf_cells _ _ _ _ _ _ _ HLF Y HY). }
        assert (HKh : know_ok segs E' M2 (APC.kn_havoc (SR.ps_cells ps) (EVar 2) (spo - SCRc) (ELit SCRc))).
        { apply (APS.know_ok_havoc segs E' M' M2 _ _ _ _ HK'); [|exact Hgr2].
          intros x Hx. apply Hfr2. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite (E2v E' HagE) in Hx.
          rewrite u64_of_Z in Hx by lia. unfold spc. lia. }
        unfold know_ok in *. apply Forall_forall. intros Y HY.
        eapply SGP.kentry_ok_agree1; [exact Hag2 | exact (SGP.kn_vars_lt_In nx _ Y X1 HY) | exact (proj1 (Forall_forall _ _) HKh Y HY)].
    + split.
      * split; [reflexivity|]. split; [exact HagE2|]. split.
        -- intros a Ha. assert (Ha' : bv_unsigned a < sp0 - SCR \/ sp0 <= bv_unsigned a).
           { rewrite EF0 in Ha. apply Forall_inv in Ha. unfold estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U2 in Ha.
             rewrite u64_of_Z in Ha by lia. lia. }
           rewrite Hfr2 by (unfold spc; lia). apply Hfr. exact Ha.
        -- eapply mem_grows_trans; [exact Hgr | exact Hgr2].
      * apply (HXI E E' E2 M M' M2 HX HagE0 Hag (CC.lf_frame _ _ _ _ _ _ _ HLF) (CC.lf_grows _ _ _ _ _ _ _ HLF)); [|exact Hgr2].
        intros a Ha. apply Hfr2. unfold spc. lia.
    + exact HFP2.
    + unfold CC.meas. rewrite X4. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
      assert (Em : edenot E2 (CC.cp_meas c) = edenot E (CC.cp_meas c)).
      { rewrite <- (SR.edenot_agree_AP _ E' E2 _ (CC.env_agree_le _ _ _ _ Hag2 Hnxc) X0). symmetry. exact (SR.edenot_agree_AP _ E E' _ Hag X0). }
      rewrite Em. unfold CA.has in X3. apply existsb_exists in X3 as (Y & HY & Heq). apply APS.kentry_eqb_eq in Heq. subst Y.
      pose proof (CC.lf_cells _ _ _ _ _ _ _ HLF _ HY) as HM. cbn [kentry_ok] in HM.
      rewrite <- (SR.edenot_agree_AP _ E E' _ Hag X0) in HM. unfold CC.MB in HM.
      rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
Qed.
End WithSegs.
End CVX.
