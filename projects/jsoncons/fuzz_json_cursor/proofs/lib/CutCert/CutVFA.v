(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA FrmInv FpBridge.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutRtA CutRtB CutPureA CutVF.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CVFA.
Definition mem := (word -> option byte).

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
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LB : list (Z * Z).
Variable FF : list fframe.
Variable LK0 : list fframe.
Variable cr0 : credit.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FF sp0.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LB FF sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
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
Variable R0 : bvmap 5 word.
Variable ra0 : Z.
Hypothesis EV0 : forall x : reg, ev E0 (ridx x) = getr R0 x.
Hypothesis RA0 : getr R0 1%bv = Z_to_bv 64 ra0.
Hypothesis RA0ok : L5.ra_ok ra0.

Abbreviation NOB := (CPA.NOB CPS).
Abbreviation NOF := (CPA.NOF CPS).
Abbreviation Cred0 := (CPA.Cred0 cr0).

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LB FF LK0 sp0 d W NOB NOF Cred0 D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LB FF LK0 sp0 d W NOB NOF Cred0 D0 XI).

Abbreviation segs := (hl_segs L).
Abbreviation mk fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))).

Definition xi_leafA (i j : nat) (c : CC.cutpoint) : Prop :=
  forall E E' E2 A A2 M M' model model2, XI i E A M model -> env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' ->
    (forall a : word, SGP.outside E' (CC.cp_F c) a -> M' a = M a) -> mem_grows M M' -> XI j E2 A2 M' model2.

Definition xi_callA (i j : nat) (c : CC.cutpoint) (scr : Z) : Prop :=
  forall E E' E2 A A2 M M' M2 model model2 csp, XI i E A M model -> env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' ->
    (forall a : word, SGP.outside E' (CC.cp_F c) a -> M' a = M a) -> mem_grows M M' ->
    csp <= 0 -> 0 <= scr -> - SCR <= csp - scr ->
    (forall a : Z, CHA.akept L ar LB FF (sp0 + csp) scr [] a -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)) -> XI j E2 A2 M2 model2.

Lemma inl_commonA : forall i c ps j cj len hv a0,
  nth_error CPS j = Some cj -> CVF.inl_chk c ps cj len hv a0 = true -> CHA.foot_chk NF d c [] [] = true -> (NF <= CC.cp_nx c)%nat -> xi_leafA i j c ->
  forall (fx2 : FPState) E R A M model E' R' R2 M1 model1 model2,
    CCA.AtV segs c E R A M model -> AMBX i E A M model -> FPI fx2 ->
    env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA segs c ps E' R' A M model M1 model1 ->
    CCA.IH segs CPS AMBX K FPI (CC.meas c E) ->
    same_but_materialized model1 model2 -> MInv A model2 ->
    (forall r : reg, ~ In (ridx r) hv -> getr R2 r = match a0 with Some z => if bv_eqb r 10 then Z_to_bv 64 z else getr R' r | None => getr R' r end) ->
    srealizes segs SCFG (mkCfg (mk fx2 R2 (SR.ps_pc ps + len) M1) model2) K.
Proof.
  intros i c ps j cj len hv a0 Hcj Hchk Hfoot Hnf HXI fx2 E R A M model E' R' R2 M1 model1 model2 HAt HAmb HFP Hag HLFA HIH Hsbm2 Hminv2 Hkeep.
  pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLFA) as HLF.
  set (M' := CCA.vis A model1 M1) in HLF.
  unfold CVF.inl_chk in Hchk. do 11 (apply andb_prop in Hchk as [Hchk ?X]).
  rename Hchk into Xall. apply Z.eqb_eq in X9. apply CVF.regs_eqb_eq in X8. apply CVF.kn_eqb_eq in X7. apply Nat.eqb_eq in X6. apply AX2S.expr_eqb_eq in X5.
  set (nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps)) in *.
  set (regs := CA.ps_reglist ps) in *.
  pose proof (CVF.leaf_regs_ok segs c ps E' R' _ M' Xall HLF) as HR. fold regs in HR.
  set (E2 := APS.ext_list E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) hv)).
  pose proof (APS.ext_list_agree E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) hv) : env_agree nx E' E2) as Hag2.
  assert (Hnxc : (CC.cp_nx c <= nx)%nat) by (unfold nx; lia).
  assert (HagNF : env_agree NF E' E2) by (eapply CC.env_agree_le; [exact Hag2 | lia]).
  assert (HagE : env_agree NF E E2) by (eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact Hnf] | exact HagNF]).
  assert (Hhv : Forall (fun r => (0 < r < 32)%nat) hv).
  { apply Forall_forall. intros r Hr. rewrite forallb_forall in X0. specialize (X0 r Hr). apply andb_prop in X0 as [A1 B1].
    apply Nat.ltb_lt in A1. apply Nat.ltb_lt in B1. lia. }
  rewrite <- X9.
  apply (HIH j cj fx2 E2 R2 A M1 model2 Hcj).
  -
    unfold CCA.AtV. rewrite (CCA.vis_sbm A model1 model2 M1 Hsbm2). fold M'.
    split.
    + rewrite X8. destruct a0 as [z|].
      * destruct hv; [|exfalso; clear - X; destruct (0 <=? z), (z <? 2 ^ 64); discriminate X]. cbn [APC.sr_fresh].
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
    pose proof HAmb as [HA HX].
    split; [| pose proof HA as (_ & _ & _ & HagE0 & _);
              exact (HXI E E' E2 A A M M1 model model2 HX HagE0 Hag (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLFA) (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLFA))].
    assert (HA1 : AAMB i E A M1 model1).
    { refine (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LB FF LK0 sp0 d W Wo NOB NOF Cred0 D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
                i c ps E E' R R' A M model M1 model1 _ HAt HA Hag HLFA).
      rewrite CPA.NOBnil, CPA.NOFnil. exact Hfoot. }
    refine (CHA.amb_step L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LB FF LK0 sp0 d W Wo NOB NOF Cred0 D0 STK SCR_pos NF32 Wo_incl Wo_ok
              i j E E2 A M1 M1 model1 model2 HA1 _ _ Hsbm2 Hminv2 HagE _ _ _ _).
    + intros a _. reflexivity.
    + apply mem_grows_refl.
    + rewrite !CPA.NOBnil. reflexivity.
    + rewrite !CPA.NOFnil. reflexivity.
    + rewrite !CPA.NOFnil. reflexivity.
    + intros cr Hc. exact Hc.
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

Hypothesis FPI_to : forall fx : FPState, FPI fx -> FrmInv.fp_ok fx.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps segs (mk fx R pc M) (mk fx' R' pc' M') -> FPI fx -> FPI fx'.

Theorem inl_leaf_okA : forall i c ps j cj len hv,
  nth_error CPS j = Some cj -> CVF.inl_chk c ps cj len hv None = true -> CHA.foot_chk NF d c [] [] = true -> (NF <= CC.cp_nx c)%nat -> xi_leafA i j c ->
  FPB.inl_step segs (SR.ps_pc ps) len hv ->
  CCA.leaf_ok segs CPS AMBX K FPI i c ps.
Proof.
  intros i c ps j cj len hv Hcj Hchk Hfoot Hnf HXI Hstep fx' E R A M model E' R' M1 model1 HAt HAmb HFP Hag HLFA HIH.
  pose proof HAmb as [HA _].
  assert (HA1 : AAMB i E A M1 model1).
  { refine (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LB FF LK0 sp0 d W Wo NOB NOF Cred0 D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
              i c ps E E' R R' A M model M1 model1 _ HAt HA Hag HLFA). rewrite CPA.NOBnil, CPA.NOFnil. exact Hfoot. }
  destruct (CHA.aamb_model L ar C HI HIok LY_below NF E0 M0 model0 A0 LB FF LK0 sp0 d W NOB NOF Cred0 D0 i E A M1 model1 HA1) as (Hh1 & HMI1 & HAwf & Hoff1).
  set (H := ahid A model1).
  destruct (Hstep fx' R' (mrestrict H M1) (FPI_to _ HFP)) as (fx2 & R2 & Hms & Hkeep).
  eapply (L5LZ.cps_of_msteps_lazy segs H A fx' fx2 R' _ M1 R2 _ (mrestrict H M1) model1 K Hoff1 LY_nowrap (L5LZ.lazy_cover_ahid A model1) HAwf HMI1 Hh1 Hms).
  intros model2 HMI2 Hsbm2 _.
  replace (munrestrict H M1 (mrestrict H M1)) with M1
    by (apply FunctionalExtensionality.functional_extensionality; intros a; unfold munrestrict, mrestrict; destruct (H a); reflexivity).
  eapply (inl_commonA i c ps j cj len hv None Hcj Hchk Hfoot Hnf HXI fx2 E R A M model E' R' R2 M1 model1 model2 HAt HAmb _ Hag HLFA HIH Hsbm2 HMI2 Hkeep).
  Unshelve. exact (FPM _ _ _ _ _ _ _ _ Hms HFP).
Qed.

Theorem inl_leaf_ok_a0A : forall i c ps j cj len z,
  nth_error CPS j = Some cj -> CVF.inl_chk c ps cj len [] (Some z) = true -> CHA.foot_chk NF d c [] [] = true -> (NF <= CC.cp_nx c)%nat -> xi_leafA i j c ->
  FPB.inl_step_a0 segs (SR.ps_pc ps) len z ->
  CCA.leaf_ok segs CPS AMBX K FPI i c ps.
Proof.
  intros i c ps j cj len z Hcj Hchk Hfoot Hnf HXI Hstep fx' E R A M model E' R' M1 model1 HAt HAmb HFP Hag HLFA HIH.
  pose proof HAmb as [HA _].
  assert (HA1 : AAMB i E A M1 model1).
  { refine (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LB FF LK0 sp0 d W Wo NOB NOF Cred0 D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
              i c ps E E' R R' A M model M1 model1 _ HAt HA Hag HLFA). rewrite CPA.NOBnil, CPA.NOFnil. exact Hfoot. }
  destruct (CHA.aamb_model L ar C HI HIok LY_below NF E0 M0 model0 A0 LB FF LK0 sp0 d W NOB NOF Cred0 D0 i E A M1 model1 HA1) as (Hh1 & HMI1 & HAwf & Hoff1).
  set (H := ahid A model1).
  destruct (Hstep fx' R' (mrestrict H M1) (FPI_to _ HFP)) as (fx2 & Hms).
  eapply (L5LZ.cps_of_msteps_lazy segs H A fx' fx2 R' _ M1 _ _ (mrestrict H M1) model1 K Hoff1 LY_nowrap (L5LZ.lazy_cover_ahid A model1) HAwf HMI1 Hh1 Hms).
  intros model2 HMI2 Hsbm2 _.
  replace (munrestrict H M1 (mrestrict H M1)) with M1
    by (apply FunctionalExtensionality.functional_extensionality; intros a; unfold munrestrict, mrestrict; destruct (H a); reflexivity).
  eapply (inl_commonA i c ps j cj len [] (Some z) Hcj Hchk Hfoot Hnf HXI fx2 E R A M model E' R' _ M1 model1 model2 HAt HAmb _ Hag HLFA HIH Hsbm2 HMI2 _).
  Unshelve.
  - exact (FPM _ _ _ _ _ _ _ _ Hms HFP).
  - intros r _. destruct (bv_eqb r 10) eqn:Er.
    + assert (r = 10%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er). apply getr_same. discriminate.
    + apply getr_other. intros ->. unfold bv_eqb in Er. rewrite Z.eqb_refl in Er. discriminate.
Qed.

Definition call_chkA (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (SCRc : Z) (IMGc : option (Z * Z)) : bool :=
  match CHA.custom_chk NF d SCELLS GLO GHI SCRc 0 [] [] [] [] None c ps cj [] [] [] [] with
  | Some _ => match IMGc with
              | Some (lo, hi) => (CC.has_cell (SR.ps_cells ps) (KImg lo hi)
                                 && existsb (fun r : Z * Z => (Z.leb (fst r) lo && Z.leb hi (snd r))%bool) (CH.hd_img d))%bool
              | None => true
              end
  | None => false
  end.

Theorem call_leaf_okA : forall i c ps j cj SCRc IMGc,
  nth_error CPS j = Some cj -> call_chkA c ps cj SCRc IMGc = true -> 0 <= D0 -> xi_callA i j c SCRc ->
  (forall r sp, CPA.cps_pureA L ar HI FPI (SR.ps_pc ps) r sp SCRc 0 [] (fun _ M => CVF.img_pre_of IMGc M) (fun _ _ _ _ => True)) ->
  CCA.leaf_ok segs CPS AMBX K FPI i c ps.
Proof.
  intros i c ps j cj SCRc IMGc Hcj Hchk HD0 HXC SPEC fx' E R A M model E' R' M1 model1 HAt HAmb HFP Hag HLFA HIH.
  unfold call_chkA in Hchk.
  destruct (CHA.custom_chk NF d SCELLS GLO GHI SCRc 0 [] [] [] [] None c ps cj [] [] [] []) as [ci|] eqn:Hcu; [|discriminate].
  refine (CPA.pure_callee_leaf L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LB FF LK0 cr0 sp0 d W Wo D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0 CRS_ok WRS_ok IMG_ok
            CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XI KNIL (SR.ps_pc ps) SCRc 0 [] [] [] None i c ps j cj ci
            (fun _ M => CVF.img_pre_of IMGc M) (fun _ _ _ _ => True) Hcj Hcu eq_refl HD0 fx' E R A M model E' R' M1 model1 HAt HAmb HFP Hag HLFA HIH
            (SPEC (CC.cp_pc cj) (sp0 + CH2.ci_csp ci)) _).
  intros LK CF HH1 HLK. split.
  -
    unfold CVF.img_pre_of. destruct IMGc as [[lo hi]|]; [|exact I].
    apply andb_prop in Hchk as [Hhas Hex]. apply CC.has_cell_In in Hhas.
    apply existsb_exists in Hex as ([rlo rhi] & Hrin & Hr). apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1, Hr2. cbn [fst snd] in Hr1, Hr2.
    pose proof (CHA.ca_know L ar HI NF E0 M0 model0 A0 LB FF LK0 sp0 d W NOB NOF Cred0 D0 SCRc 0 c ps cj ci i E E' R' A M1 model1 CF) as HK.
    pose proof (proj1 (Forall_forall _ _) HK _ Hhas) as HX. cbn [kentry_ok] in HX. destruct HX as (I1 & I2 & I3).
    split; [exact I1|]. split; [exact I2|]. intros a Ha.
    specialize (I3 a Ha). unfold CCA.vis, mrestrict in I3.
    destruct (IMG_ok (rlo, rhi) a Hrin ltac:(cbn [fst snd]; lia)) as [Hlh _].
    rewrite (CHA.img_vis L ar C HI HIok LY_img NF sp0 NF32 _ _ _ _ _ _ _ a HH1 ltac:(lia)) in I3. exact I3.
  - intros R2 M2 model2 LK2 A2 _ _ HP _. split; [exact I|]. split; [intros w a0 [] |]. split; [intros w a0 [] |]. split; [| intros X []].
    pose proof HAmb as [HA HX]. pose proof HA as (_ & _ & _ & HagE0 & _).
    destruct (CHA.ca_sp L ar HI NF E0 M0 model0 A0 LB FF LK0 sp0 d W NOB NOF Cred0 D0 SCRc 0 c ps cj ci i E E' R' A M1 model1 CF) as (_ & C1 & C2 & C3).
    exact (HXC E E' _ A A2 M M1 M2 model model2 (CH2.ci_csp ci) HX HagE0 Hag (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLFA) (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLFA) C1 C2 C3 (proj1 HP)).
Qed.

Lemma callee_leafLB : forall pc scr (ng : nat) dc Wc wregs news a0x i c ps j cj ci
    (Pre : list (Z * Z) -> list fframe -> bvmap 5 word -> mem -> Prop) (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> Prop),
  nth_error CPS j = Some cj ->
  CHA.custom_chk NF d SCELLS GLO GHI scr ng [] [] wregs news a0x c ps cj [] [] [] [] = Some ci ->
  SR.ps_pc ps = pc -> dc <= D0 ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV segs c E R A M model -> AMBX i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA segs c ps E' R' A M model M1 model1 -> CCA.IH segs CPS AMBX K FPI (CC.meas c E) ->
    (forall LB' FF' LK' cr' A', CBA.cps_asanG L ar HI FPI pc (CC.cp_pc cj) (sp0 + CH2.ci_csp ci) scr LB' FF' LK' cr' A' dc (Pre LB' FF')
                              (fun R M R' M' LB2 cr2 LBk W' => Post R M R' M' /\ LB2 = LB' /\ cr2 = cr' /\ LBk = LB' /\ W' = Wc)) ->
    (forall LK, CHA.common_facts L ar HI NF E0 M0 model0 A0 LB FF LK0 sp0 d W NOB NOF Cred0 D0 scr ng c ps cj ci i E E' R' A M1 model1 ->
       ri_inv HI LB FF LK cr0 A M1 (vml_of model1) -> incl LK LK0 ->
       Pre LB FF R' M1 /\
       forall R2 M2 model2 LK2 A2,
         Post R' M1 R2 M2 -> regs_preserved R' R2 -> CHA.ahpres L ar LB FF (sp0 + CH2.ci_csp ci) scr Wc M1 M2 -> ri_inv HI LB FF LK2 cr0 A2 M2 (vml_of model2) ->
         exists ghosts, length ghosts = ng /\
         let E2 := CH2.retEx E' (CH2.ci_nx ci) ghosts R2 in
         match a0x with Some e => getr R2 10%bv = edenot E2 e | None => True end /\
         (forall w a, In w Wc -> L5.in_rng w a -> exists r, In r wregs /\ CHA.in_reg E' r a) /\
         (forall w a, In w Wc -> L5.in_rng w a -> ~ CHA.akept L ar LB FF sp0 SCR W a) /\
         XI j E2 A2 M2 model2 /\
         (forall X, In X news -> In X (CC.cp_know cj) -> kentry_ok segs E2 (CCA.vis A2 model2 M2) X)) ->
    srealizes segs SCFG (mkCfg (mk fx' R' (SR.ps_pc ps) M1) model1) K.
Proof.
  intros pc scr ng dc Wc wregs news a0x i c ps j cj ci Pre Post Hcj Hchk Hpc Hdc fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH SPEC USER.
  refine (CBA.callee_leaf L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LB FF LK0 sp0 d W Wo NOB NOF Cred0 D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0 CRS_ok WRS_ok IMG_ok
            CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XI KNIL pc scr ng [] wregs news a0x dc i c ps j cj ci Hcj _ Hpc _ _ fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH _);
    [rewrite !CPA.NOBnil, !CPA.NOFnil; exact Hchk | rewrite !CPA.NOFnil; reflexivity | rewrite CPA.NOFnil; cbn [length]; lia |].
  unfold CHA.curB, CHA.curF. rewrite !CPA.NOBnil, !CPA.NOFnil. cbn [CH2.den CHA.denF map app].
  intros cr LK CF HH1 HLK1 HC1. unfold CPA.Cred0 in HC1. subst cr. destruct (USER LK CF HH1 HLK1) as [HPre HPost].
  eexists. eexists. split; [exact (SPEC LB FF LK cr0 A)|]. split; [exact HPre|].
  intros R2 M2 model2 LB' cr' LBk Wc' LK2 A2 (HPo & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  destruct (HPost R2 M2 model2 LK2 A2 HPo HRP HP HH2) as (ghosts & Hlen & Ha0 & HWr & HWk & HXj & Hnews).
  exists ghosts. split; [exact Hlen|]. cbv zeta. split; [exact Ha0|]. split; [cbn [CH2.den map app]; apply incl_refl|]. split; [exact HWr|]. split; [exact HWk|].
  split; [try rewrite CPA.NOBnil; cbn [CH2.den map app]; exact HH2|]. split; [reflexivity|]. split; [exact HXj | exact Hnews].
Qed.
End Inst.

Definition tag_pc_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto _ _ => true | CC.TOther pc => Z.eqb (SR.ps_pc ps) pc end.
Definition E0of (R : bvmap 5 word) : env := Env (reg_ev R (fun v => Z_to_bv 64 0)) (fun id => []).

Lemma csaved_of_idx : forall x : reg, In (bv_unsigned x) callee_saved_idx -> In (ridx x) CVF.CSAVED.
Proof.
  intros x Hx. unfold ridx. unfold callee_saved_idx in Hx.
  repeat (destruct Hx as [E|Hx]; [rewrite <- E; cbn; tauto|]). destruct Hx.
Qed.

Section LeafA.
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
Variable FPI : FPState -> Prop.
Hypothesis FPI_to : forall fx : FPState, FPI fx -> FrmInv.fp_ok fx.
Abbreviation segs := (hl_segs L).
Abbreviation mk fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))).
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M', msteps segs (mk fx R pc M) (mk fx' R' pc' M') -> FPI fx -> FPI fx'.

Definition vf_contractA (entry SCR : Z) (IMG : option (Z * Z)) : Prop :=
  forall r sp, CPA.cps_pureA L ar HI FPI entry r sp SCR 0 [] (fun _ M => CVF.img_pre_of IMG M) (fun _ _ _ _ => True).

Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable d : CH.hdecl.
Variable entry SCR : Z.
Variable ENDS : list Z.
Variable RETS : list (nat * nat * nat * Z).
Variable INL : list (Z * (Z * list nat * option Z)).
Variable IMG : option (Z * Z).
Variable CALLEES : list (Z * (Z * option (Z * Z))).
Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Abbreviation NF := CVF.NF.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.

Definition leaf_chkA (i : nat) (ps : SR.post_spec) (id : Z) : bool :=
  ((CL.ps_at ps ENDS && CL.ps_keeps ps CVF.CSAVED)
   || existsb (fun rt : nat * nat * nat * Z => let '(j, i', _, pc) := rt in
                 (Nat.eqb i' i && Z.eqb pc id && Z.eqb (SR.ps_pc ps) id &&
                  match nth_error CPS i, nth_error CPS j with
                  | Some c, Some cj =>
                      match find (fun e : Z * (Z * list nat * option Z) => Z.eqb (fst e) pc) INL with
                      | Some (_, (len, hv, a0)) => CVF.inl_chk c ps cj len hv a0
                      | None => match find (fun e : Z * (Z * option (Z * Z)) => Z.eqb (fst e) pc) CALLEES with
                                | Some (_, (SCRc, IMGc)) => call_chkA NF d SCELLS GLO GHI c ps cj SCRc IMGc
                                | None => false
                                end
                      end
                  | _, _ => false
                  end)%bool) RETS)%bool.
Definition vf_chkA : bool :=
  (CVF.entry_chk CPS entry SCR IMG && CC.cps_all CPS (CVF.cut_chk SCR) && CC.others_all CPS TAGS leaf_chkA && Z.leb 0 SCR && Z.ltb SCR (2 ^ 32))%bool.

Hypothesis HSCR : CH.hd_scr d = SCR.
Hypothesis HCRS : CH.hd_crs d = [].
Hypothesis HWRS : CH.hd_wrs d = [].
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Hypothesis PLANS : forall i c, nth_error CPS i = Some c -> CC.plan_sound segs c.
Hypothesis TAGS_OK : CC.tags_chk CPS TAGS NF = true.
Hypothesis CHK : vf_chkA = true.
Hypothesis HEAP_OK : CHA.heap_chkA NF d (CPA.NOB CPS) (CPA.NOF CPS) CPS TAGS = true.
Hypothesis PURE_OK : CH2.leaves_all CPS TAGS (CPA.pure_leaf_chk NF d ENDS) = true.
Hypothesis TAGPC_OK : CH2.leaves_all CPS TAGS tag_pc_chk = true.
Hypothesis FOOT_OK : CC.cps_all CPS (fun _ c => CHA.foot_chk NF d c [] []) = true.
Hypothesis RETS_OK : forall pc, In pc ENDS -> CL.is_ret_at segs pc.
Hypothesis INL_OK : forall e, In e INL -> CVF.inl_sem segs e.
Hypothesis CALLEES_OK : forall pc SCRc IMGc, In (pc, (SCRc, IMGc)) CALLEES -> vf_contractA pc SCRc IMGc.

Theorem vf_leaf_soundA : vf_contractA entry SCR IMG.
Proof.
  intros r sp LB FF LK cr A fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Himg Hcont.
  pose proof CHK as CHK'. unfold vf_chkA in CHK'. do 4 (apply andb_prop in CHK' as [CHK' ?C0]). rename CHK' into Centry. apply Z.leb_le in C1. apply Z.ltb_lt in C0.
  assert (HC0 : exists c0, nth_error CPS 0 = Some c0 /\ CC.cp_pc c0 = entry /\ CC.cp_regs c0 = sr_id /\ CC.cp_know c0 = CVF.KN0 SCR IMG).
  { unfold CVF.entry_chk in Centry. destruct CPS as [|c0 CPSr]; [discriminate|]. exists c0.
    do 3 (apply andb_prop in Centry as [Centry ?D]).
    apply Z.eqb_eq in Centry. apply CVF.regs_eqb_eq in D1. apply CVF.kn_eqb_eq in D0. repeat split; assumption. }
  destruct HC0 as (c0 & ECPS & Centry' & D1 & D0). clear Centry.
  assert (NFle : forall i c, nth_error CPS i = Some c -> (NF <= CC.cp_nx c)%nat).
  { intros i c Hc. pose proof (CC.cps_all_sound _ _ C3 i c Hc) as X. apply andb_prop in X as [X _]. apply Nat.leb_le. exact X. }
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  set (E0 := E0of R).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr d <= sp /\ sp <= ar_sptop ar) by (rewrite HSCR; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr d) by (rewrite HSCR; lia).
  assert (NF32 : (32 <= NF)%nat) by (unfold CVF.NF; lia).
  assert (WOK : forall (w : L5.range) (a : Z), In w (@nil L5.range) -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr d) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))) by (intros w a []).
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs d) -> SGP.region_vars_lt NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w (@nil L5.range) /\ L5.in_rng w a))
    by (rewrite HWRS; intros rg []).
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs d) -> SGP.region_vars_lt NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp d a))
    by (rewrite HCRS; intros rg []).
  assert (DEF0 : L5.defined M (sp - CH.hd_scr d) (CH.hd_scr d)) by (rewrite HSCR; exact S5).
  assert (VS : CL5A.visr (ahid A model) (sp - SCR) SCR).
  { intros k Hk. apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 _ HH); [clear - Hk S2 S3 CL SP1 C1; lia | right; left; split; [clear - Hk S2 S3 SP1 C1; lia | clear; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL C1. lia. }
  rewrite <- Centry'.
  eapply (CPA.pure_cert_soundA L ar C HI HIok LY_img LY_ro LY_below LY_nowrap NF E0 M model A LB FF LK cr sp d [] [] 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            CPS TAGS K FPI DEF0 (fun _ _ _ _ _ => True) R r EV Hra Hraok ENDS FPM) with (i := 0%nat).
  - exact PLANS.
  - exact TAGS_OK.
  - exact HEAP_OK.
  - exact PURE_OK.
  - exact RETS_OK.
  -   intros; exact I.
  -
    intros i c k ps pc IL Hne.
    pose proof IL as IL'. destruct IL' as (tags & Hc & Htags & Hps & Htag).
    pose proof (CC.others_all_sound _ _ _ C2 i c tags k ps pc Hc Htags Hps Htag) as X. unfold leaf_chkA in X.
    pose proof (CH2.leaves_all_sound _ _ _ TAGPC_OK _ _ _ _ _ IL) as XP. unfold tag_pc_chk in XP. apply Z.eqb_eq in XP.
    apply orb_prop in X as [X|X].
    +
      exfalso. apply andb_prop in X as [Xpc _]. pose proof (CL.ps_at_sound _ _ Xpc) as Hin. rewrite XP in Hin.
      apply Bool.not_true_iff_false in Hne. apply Hne. apply existsb_exists. exists pc. split; [exact Hin | apply Z.eqb_refl].
    + apply existsb_exists in X as ([[[j i'] k'] pc'] & Hin & X). do 3 (apply andb_prop in X as [X ?Y]).
      apply Nat.eqb_eq in X. apply Z.eqb_eq in Y1, Y0. subst i' pc'. rewrite Hc in Y.
      destruct (nth_error CPS j) as [cj|] eqn:Hcj; [|discriminate].
      destruct (find (fun e : Z * (Z * list nat * option Z) => Z.eqb (fst e) pc) INL) as [[pc' [[len hv] a0]]|] eqn:Hf.
      2:{
          destruct (find (fun e : Z * (Z * option (Z * Z)) => Z.eqb (fst e) pc) CALLEES) as [[pc' [SCRc IMGc]]|] eqn:Hg; [|discriminate Y].
          apply find_some in Hg as [HinC Hpc']. cbn [fst] in Hpc'. apply Z.eqb_eq in Hpc'. subst pc'.
          pose proof (CALLEES_OK _ _ _ HinC) as Hct. rewrite <- Y0 in Hct.
          exact (call_leaf_okA L ar C HI HIok LY_img LY_ro NF E0 M model A LB FF LK cr sp d [] [] 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_ok
                   CPS K FPI DEF0 S6 SCELLS GLO GHI SCELLS_ok GOT_ok (fun _ _ _ _ _ => True) HKnil i c ps j cj SCRc IMGc Hcj Y (Z.le_refl 0) ltac:(unfold xi_callA; intros; exact I) Hct). }
      apply find_some in Hf as [HinI Hpc']. cbn [fst] in Hpc'. apply Z.eqb_eq in Hpc'. subst pc'.
      pose proof (INL_OK _ HinI) as Hsem. cbn in Hsem. rewrite <- Y0 in Hsem.
      pose proof (CC.cps_all_sound _ _ FOOT_OK i c Hc) as Hfoot. cbn beta in Hfoot.
      destruct a0 as [z|].
      * destruct Hsem as [-> Hst].
        exact (inl_leaf_ok_a0A L ar C HI HIok LY_img LY_ro LY_below LY_nowrap NF E0 M model A LB FF LK cr sp d [] [] 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                 CPS K FPI (fun _ _ _ _ _ => True) FPI_to FPM i c ps j cj len z Hcj Y Hfoot (NFle i c Hc) ltac:(unfold xi_leafA; intros; exact I) Hst).
      * exact (inl_leaf_okA L ar C HI HIok LY_img LY_ro LY_below LY_nowrap NF E0 M model A LB FF LK cr sp d [] [] 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                 CPS K FPI (fun _ _ _ _ _ => True) FPI_to FPM i c ps j cj len hv Hcj Y Hfoot (NFle i c Hc) ltac:(unfold xi_leafA; intros; exact I) Hsem).
  -
    intros i c k ps pc IL Hin fx' E R1 A1 M1 m1 E' R' M' m' HAt1 HAX HFP1 Hag HLF model2 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HagE' HA'.
    rewrite HSCR in HP.
    exact (Hcont fx' R' M' model2 LB cr LB [] LK1 A1 HFP1 (conj I (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))) HRP HP Hrt HA0 Hmo2 HLK1 HH1).
  - exact ECPS.
  -
    unfold CCA.AtV. split; [rewrite D1; exact (regs_ok_id R _ _)|]. rewrite D0. unfold CVF.KN0.
    unfold know_ok. apply Forall_app. split; [|apply Forall_app; split].
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; lia | lia | lia].
      * eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; lia | lia | lia | exact S1].
    + unfold CVF.img_pre_of in Himg. destruct IMG as [[lo hi]|]; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok].
      destruct Himg as (I1 & I2 & I3). split; [exact I1|]. split; [exact I2|].
      intros a Ha. unfold CCA.vis, mrestrict. destruct (ahid A model (Z_to_bv 64 a)); [reflexivity | exact (I3 a Ha)].
    + destruct (Z.eqb_spec SCR 0) as [Z0|NZ]; [apply Forall_nil|].
      pose proof (CL5A.defined_vis (ahid A model) M _ _ VS S5) as DS.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * eapply CL5.kwr_intro with (A := sp - SCR) (N := SCR); [ | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; reflexivity | lia | lia | lia | exact DS].
        unfold estart. cbn [a_base a_off edenot]. rewrite V2. rewrite u64_of_Z by lia. lia.
      * eapply CL5.kunk_intro with (A := sp - SCR) (N := SCR); [ | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; reflexivity | lia | lia | lia | exact DS].
        unfold estart. cbn [a_base a_off edenot]. rewrite V2. rewrite u64_of_Z by lia. lia.
  - exact I.
  - exact HH.
  - exact Hmo.
  - exact Hroom.
  - exact Hfp.
Qed.

Theorem vf_leaf_soundA_pre : forall (entry0 : Z) (hv : list nat),
  entry = entry0 + 4 -> FPB.inl_step segs entry0 4 hv -> (forall x, In x hv -> ~ In x CVF.CSAVED) ->
  vf_contractA entry0 SCR IMG.
Proof.
  intros entry0 hv He Hstep Hhv r sp LB FF LK cr A fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Himg Hcont.
  set (H := ahid A model).
  destruct (Hstep fx R (mrestrict H M) (FPI_to _ Hfp)) as (fx1 & R1 & Hms & Hkeep).
  assert (KEEP : forall x : reg, In (ridx x) CVF.CSAVED -> getr R1 x = getr R x).
  { intros x Hx. apply Hkeep. intros X. exact (Hhv _ X Hx). }
  pose proof Hmo as [Hh HMI].
  pose proof (proj1 (PmHeapIfaceA.aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH)) as HAwf.
  eapply (L5LZ.cps_of_msteps_lazy segs H A fx fx1 R _ M R1 _ (mrestrict H M) model K (CHA.vis_off_segments L ar C HI HIok LY_below _ _ _ _ _ _ _ HH) LY_nowrap
            (L5LZ.lazy_cover_ahid A model) HAwf HMI Hh Hms).
  intros model1 HMI1 HS _.
  replace (munrestrict H M (mrestrict H M)) with M
    by (apply FunctionalExtensionality.functional_extensionality; intros a; unfold munrestrict, mrestrict; destruct (H a); reflexivity).
  rewrite <- He.
  assert (VML : vml_of model1 = vml_of model) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ HS), (L5LZ.sbm_lazy _ _ HS); reflexivity).
  apply (vf_leaf_soundA r sp LB FF LK cr A fx1 R1 M model1 K); try assumption.
  - rewrite VML. exact HH.
  - split; [rewrite (L5LZ.sbm_halted _ _ HS); exact Hh | exact HMI1].
  - exact (FPM _ _ _ _ _ _ _ _ Hms Hfp).
  - rewrite (KEEP 1%bv ltac:(left; reflexivity)). exact Hra.
  - rewrite (KEEP 2%bv ltac:(right; left; reflexivity)). exact Hsp.
  - rewrite (KEEP 4%bv ltac:(right; right; right; left; reflexivity)). exact Htp.
  - intros fx' R' M' model' LB' cr' LBk W LK' A' F1 F2 F3 F4 F5 F6 F7 F8 F9.
    apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' F1 F2); try assumption.
    + intros x Hx. rewrite <- (KEEP x (csaved_of_idx x Hx)). exact (F3 x Hx).
    + exact (L5LZ.model_rt_trans _ _ _ (L5LZ.sbm_model_rt _ _ HS) F5).
Qed.
End LeafA.

End CVFA.
