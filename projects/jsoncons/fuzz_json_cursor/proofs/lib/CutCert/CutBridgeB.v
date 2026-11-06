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

Module CBB.
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
Abbreviation CFACTS := (CHA.common_facts L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).

Definition CSAVED_nosp : list nat := [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition exit_base_chk_sp (retpc : Z) (spE : expr) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (Z.eqb (SR.ps_pc ps) retpc && CL.ps_keeps ps CSAVED_nosp && CL.ps_reg_is ps 2 spE && APC.expr_vars_lt NF spE && Nat.leb NF (CC.cp_nx c))%bool.
Lemma exit_ret_sp : forall (R0' : bvmap 5 word) (ra0' : Z) (spE : expr) retpc i c ps,
  (forall x : reg, In (ridx x) CSAVED_nosp -> ev E0 (ridx x) = getr R0' x) -> getr R0' 1%bv = Z_to_bv 64 ra0' -> L5.ra_ok ra0' -> edenot E0 spE = getr R0' 2%bv ->
  CL.is_ret_at (hl_segs L) retpc -> exit_base_chk_sp retpc spE c ps = true ->
  CHA.foot_chk NF d c (nth i BLS []) (nth i FFS []) = true -> nth i FFS [] = [] ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
    (forall model2 cr LK,
        regs_preserved R0' R' -> CHA.ahpres L ar LBrest FFrest sp0 SCR W M0 M1 -> model_rt model0 model2 -> incl A0 A -> CHA.amodel_ok A model2 -> incl LK LK0 ->
        ri_inv HI (curB i E) FFrest LK cr A M1 (vml_of model2) -> Cred i E cr -> env_agree NF E0 E' -> AAMB i E A M1 model1 ->
        srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 ra0') M1 (seg_rom (hl_segs L))) model2) K) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros R0' ra0' spE retpc i c ps EV0' RA0' RA0ok' SPE Hret Hchk Hfoot HFi fx' E R A M model E' R' M1 model1 HAt HA Hag HLF Hcont.
  unfold exit_base_chk_sp in Hchk. apply andb_prop in Hchk as [Hchk C3]. apply andb_prop in Hchk as [Hchk CV]. apply andb_prop in Hchk as [Hchk CS]. apply andb_prop in Hchk as [C1 C2].
  apply Z.eqb_eq in C1. apply Nat.leb_le in C3.
  pose proof (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
                i c ps E E' R R' A M model M1 model1 Hfoot HAt HA Hag HLF) as HA'.
  pose proof HA' as (Hmo1 & Hrt1 & HA01 & HagE & (cr & LK & HH1 & HLK1 & HC1 & HRoom1) & Hfr1 & Hdf1).
  pose proof (CBA.leaf_agree0 L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i c E E' A M model HA C3 Hag) as HagE'.
  assert (KEEP : forall x : reg, In (ridx x) CSAVED_nosp -> getr R' x = getr R0' x).
  { intros x Hx. assert (Hx32 : (ridx x < NF)%nat).
    { apply (Nat.lt_le_trans _ 32); [|exact NF32]. unfold CSAVED_nosp in Hx. cbn [In] in Hx. clear - Hx.
      repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; apply Nat.ltb_lt; reflexivity|]). destruct Hx. }
    rewrite (CL.ps_keeps_sound (hl_segs L) c ps E0 E' R' _ _ CSAVED_nosp NF x (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) C2 HagE' Hx Hx32). exact (EV0' x Hx). }
  assert (KSP : getr R' 2%bv = getr R0' 2%bv).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity).
    rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 2 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) CS). rewrite <- (SR.edenot_agree_AP _ E0 E' spE HagE' CV). exact SPE. }
  assert (HRP : regs_preserved R0' R').
  { intros x Hx. destruct (bv_eq_dec _ x 2%bv) as [->|NE]; [exact KSP|]. apply KEEP. pose proof (CL5.csaved_in x Hx) as IN.
    unfold CL5.CSAVED in IN. unfold CSAVED_nosp. cbn [In] in IN |- *.
    assert (N2 : ridx x <> 2%nat) by (intros HX; apply NE; apply bv_eq; unfold ridx in HX; change (bv_unsigned (2%bv : bv 5)) with 2; clear - HX; lia).
    clear - IN N2. intuition lia. }
  assert (Hra' : getr R' 1%bv = Z_to_bv 64 ra0') by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact RA0').
  assert (HFx : curF i E = FFrest) by (unfold CHA.curF; rewrite HFi; reflexivity).
  rewrite HFx in HH1.
  pose proof (CBA.exit_post L ar C HI HIok NF M0 model0 A0 LBrest FFrest sp0 d W BLS STK NF32 DEF0 i E A M1 model1 cr LK FFrest Hmo1 Hrt1 HA01 Hfr1 Hdf1 HH1) as HP.
  destruct (CHA.aamb_model L ar C HI HIok LY_below NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i E A M1 model1 HA') as (Hh & HMI & HAwf & Hoff).
  rewrite C1. eapply (CCA.ret_cps (hl_segs L) fx' R' retpc M1 model1 A K Hret Hh HMI HAwf Hoff LY_nowrap).
  { rewrite Hra'. apply Hoare.ret_ok_even. destruct RA0ok' as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
  intros model2 HMI2 HS. rewrite Hra'.
  assert (VML : vml_of model2 = vml_of model1) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ HS), (L5LZ.sbm_lazy _ _ HS); reflexivity).
  apply (Hcont model2 cr LK HRP HP); [exact (L5LZ.model_rt_trans _ _ _ Hrt1 (L5LZ.sbm_model_rt _ _ HS)) | exact HA01 | | exact HLK1 | rewrite VML; exact HH1 | exact HC1 | exact HagE' | exact HA'].
  split; [rewrite (L5LZ.sbm_halted _ _ HS); exact (proj1 Hmo1) | exact HMI2].
Qed.

Lemma amb_mo : forall i E A M model, AAMB i E A M model -> CHA.amodel_ok A model.
Proof. intros i E A M model H. exact (proj1 H). Qed.
Lemma amb_rt : forall i E A M model, AAMB i E A M model -> model_rt model0 model.
Proof. intros i E A M model H. exact (proj1 (proj2 H)). Qed.
Lemma amb_incl : forall i E A M model, AAMB i E A M model -> incl A0 A.
Proof. intros i E A M model H. exact (proj1 (proj2 (proj2 H))). Qed.
Lemma amb_agree : forall i E A M model, AAMB i E A M model -> env_agree NF E0 E.
Proof. intros i E A M model H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.
Lemma amb_ri : forall i E A M model, AAMB i E A M model ->
  exists cr LK, ri_inv HI (curB i E) (curF i E) LK cr A M (vml_of model) /\ incl LK LK0 /\ Cred i E cr /\ CHA.ffroom (curF i E) LK (D0 - Z.of_nat (length (nth i FFS []))).
Proof. intros i E A M model H. exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))). Qed.
Lemma amb_kept : forall i E A M model, AAMB i E A M model -> forall a, CHA.akept L ar LBrest FFrest sp0 SCR W a -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a).
Proof. intros i E A M model H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.
Lemma amb_def : forall i E A M model, AAMB i E A M model ->
  forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBrest FFrest sp0 0 a -> M0 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None.
Proof. intros i E A M model H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.

Record ambR (i : nat) (E : env) (A : list (Z * Z)) (M : mem) (model : Model) : Prop := AMBR {
  ar_mo : CHA.amodel_ok A model;
  ar_agree : env_agree NF E0 E;
  ar_kept : forall a, CHA.akept L ar LBrest FFrest sp0 SCR W a -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a);
  ar_def : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBrest FFrest sp0 0 a -> M0 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None }.
Lemma amb_R : forall i E A M model, AAMB i E A M model -> ambR i E A M model.
Proof. intros i E A M model H. exact (AMBR i E A M model (amb_mo _ _ _ _ _ H) (amb_agree _ _ _ _ _ H) (amb_kept _ _ _ _ _ H) (amb_def _ _ _ _ _ H)). Qed.

Lemma exit_retire_sp : forall (R0' : bvmap 5 word) (ra0' : Z) (spE : expr) retpc i c ps fle Fe k c0,
  (forall x : reg, In (ridx x) CSAVED_nosp -> ev E0 (ridx x) = getr R0' x) -> getr R0' 1%bv = Z_to_bv 64 ra0' -> L5.ra_ok ra0' -> edenot E0 spE = getr R0' 2%bv ->
  CL.is_ret_at (hl_segs L) retpc -> exit_base_chk_sp retpc spE c ps = true ->
  nth i FFS [] = [(Fe, k, c0)] -> CHA.retire_chk NF d c (nth i BLS []) (nth i FFS []) = Some fle ->
  CC.has_cell (SR.ps_cells ps) (KWord (SA fle 0) 1 (ELit 0)) = true ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
    ar_fs ar <= CL5A.uv E fle < ar_fs ar + FS_BYTES -> ~ aclient L ar LBrest FFrest sp0 SCR (CL5A.uv E fle) ->
    (forall model2 cr LK,
        regs_preserved R0' R' -> CHA.ahpres L ar LBrest FFrest sp0 SCR W M0 M1 -> model_rt model0 model2 -> incl A0 A -> CHA.amodel_ok A model2 -> incl LK LK0 ->
        ri_inv HI (curB i E) FFrest LK cr A M1 (vml_of model2) -> Cred i E cr -> env_agree NF E0 E' ->
        srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 ra0') M1 (seg_rom (hl_segs L))) model2) K) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros R0' ra0' spE retpc i c ps fle Fe k c0 EV0' RA0' RA0ok' SPE Hret Hchk HFi Hrchk Hcell fx' E R A M model E' R' M1 model1 HAt HA Hag HLF Hflr Hflnc Hcont.
  unfold exit_base_chk_sp in Hchk. apply andb_prop in Hchk as [Hchk C3]. apply andb_prop in Hchk as [Hchk CV]. apply andb_prop in Hchk as [Hchk CS]. apply andb_prop in Hchk as [C1 C2].
  apply Z.eqb_eq in C1. apply Nat.leb_le in C3.
  apply CC.has_cell_In in Hcell.
  destruct (CHA.retire_exit L ar C HI HIok LY_img NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
              i c ps fle Fe k c0 E E' R R' A M model M1 model1 HFi Hrchk HAt HA Hag HLF Hcell Hflr Hflnc) as (Hmo1 & Hrt1 & HA01 & (cr & LK & HH1 & HLK1 & HC1) & Hfr1 & Hdf1).
  pose proof (CBA.leaf_agree0 L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i c E E' A M model HA C3 Hag) as HagE'.
  assert (KEEP : forall x : reg, In (ridx x) CSAVED_nosp -> getr R' x = getr R0' x).
  { intros x Hx. assert (Hx32 : (ridx x < NF)%nat).
    { apply (Nat.lt_le_trans _ 32); [|exact NF32]. unfold CSAVED_nosp in Hx. cbn [In] in Hx. clear - Hx.
      repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; apply Nat.ltb_lt; reflexivity|]). destruct Hx. }
    rewrite (CL.ps_keeps_sound (hl_segs L) c ps E0 E' R' _ _ CSAVED_nosp NF x (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) C2 HagE' Hx Hx32). exact (EV0' x Hx). }
  assert (KSP : getr R' 2%bv = getr R0' 2%bv).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity).
    rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 2 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) CS). rewrite <- (SR.edenot_agree_AP _ E0 E' spE HagE' CV). exact SPE. }
  assert (HRP : regs_preserved R0' R').
  { intros x Hx. destruct (bv_eq_dec _ x 2%bv) as [->|NE]; [exact KSP|]. apply KEEP. pose proof (CL5.csaved_in x Hx) as IN.
    unfold CL5.CSAVED in IN. unfold CSAVED_nosp. cbn [In] in IN |- *.
    assert (N2 : ridx x <> 2%nat) by (intros HX; apply NE; apply bv_eq; unfold ridx in HX; change (bv_unsigned (2%bv : bv 5)) with 2; clear - HX; lia).
    clear - IN N2. intuition lia. }
  assert (Hra' : getr R' 1%bv = Z_to_bv 64 ra0') by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact RA0').
  pose proof (CBA.exit_post L ar C HI HIok NF M0 model0 A0 LBrest FFrest sp0 d W BLS STK NF32 DEF0 i E A M1 model1 cr LK FFrest Hmo1 Hrt1 HA01 Hfr1 Hdf1 HH1) as HP.
  assert (Hoff : H_off_segments (hl_segs L) (ahid A model1)) by exact (CHA.vis_off_segments L ar C HI HIok LY_below _ _ _ _ _ _ model1 HH1).
  rewrite C1. eapply (CCA.ret_cps (hl_segs L) fx' R' retpc M1 model1 A K Hret (proj1 Hmo1) (proj2 Hmo1) (proj1 (PmHeapIfaceA.aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1)) Hoff LY_nowrap).
  { rewrite Hra'. apply Hoare.ret_ok_even. destruct RA0ok' as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
  intros model2 HMI2 HS. rewrite Hra'.
  assert (VML : vml_of model2 = vml_of model1) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ HS), (L5LZ.sbm_lazy _ _ HS); reflexivity).
  apply (Hcont model2 cr LK HRP HP); [exact (L5LZ.model_rt_trans _ _ _ Hrt1 (L5LZ.sbm_model_rt _ _ HS)) | exact HA01 | | exact HLK1 | rewrite VML; exact HH1 | exact HC1 | exact HagE'].
  split; [rewrite (L5LZ.sbm_halted _ _ HS); exact (proj1 Hmo1) | exact HMI2].
Qed.

End Inst.
End CBB.
