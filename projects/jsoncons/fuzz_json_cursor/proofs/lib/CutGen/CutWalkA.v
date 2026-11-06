(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Exec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FloatCA Require Import CjCpsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CWA.
Definition mem := (word -> option byte).

Lemma unrestrict_mkst : forall H (M : mem) ms, ms_svc_pending ms = None -> ms_resv ms = None ->
  unrestrict H M ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (ms_pc_val ms) (munrestrict H M (ms_mem ms)) (ms_rom ms).
Proof. intros H M [r f pc sv rv fc m rom] H1 H2. cbn in *. subst. reflexivity. Qed.
Lemma regs_ok_eqv : forall E regs R R', regs_eqv R R' -> regs_ok E regs R -> regs_ok E regs R'.
Proof.
  intros E regs R R' HE HR r. rewrite <- (HR r). unfold getr. destruct (bv_eqb r 0) eqn:Hr; [reflexivity|].
  symmetry. apply HE. unfold is_x0. unfold bv_eqb in Hr. exact Hr.
Qed.

Lemma vis_unrestrict : forall H (M m : mem), (forall a, H a = true -> m a = None) -> mrestrict H (munrestrict H M m) = m.
Proof.
  intros H M m Hc. apply FunctionalExtensionality.functional_extensionality. intros a. unfold mrestrict, munrestrict.
  destruct (H a) eqn:Ha; [symmetry; exact (Hc a Ha) | reflexivity].
Qed.

Lemma munr_frame : forall H (M m : mem) a, (H a = false -> m a = mrestrict H M a) -> munrestrict H M m a = M a.
Proof. intros H M m a Hm. unfold munrestrict. destruct (H a) eqn:Ha; [reflexivity|]. rewrite (Hm eq_refl). unfold mrestrict. rewrite Ha. reflexivity. Qed.
Lemma munr_grows : forall H (M m : mem), mem_grows (mrestrict H M) m -> mem_grows M (munrestrict H M m).
Proof.
  intros H M m Hg a Ha. unfold munrestrict. destruct (H a) eqn:Hh; [exact Ha|]. apply Hg. unfold mrestrict. rewrite Hh. exact Ha.
Qed.

Section Leaf.
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
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).

Definition walk_end (i : nat) (c : CC.cutpoint) (E : env) (A : list (Z * Z)) (H1 : word -> bool) (M1 : mem) (model1 : Model) (ms1 : machine_state) : Prop :=
  ms_svc_pending ms1 = None /\ ms_resv ms1 = None /\ ms_rom ms1 = seg_rom (hl_segs L) /\
  exists j cj E2, nth_error CPS j = Some cj /\ ms_pc_val ms1 = Z_to_bv 64 (CC.cp_pc cj) /\
    FPI (mkFP (ms_fregs ms1) (ms_fcsr ms1)) /\
    regs_ok E2 (CC.cp_regs cj) (ms_regs ms1) /\ know_ok (hl_segs L) E2 (ms_mem ms1) (CC.cp_know cj) /\
    (forall a : word, ~ CHA.afoot_sem sp0 d Wo (CH2.den E (nth i BLS [])) (CHA.denF sp0 E (nth i FFS [])) (bv_unsigned a) -> ms_mem ms1 a = mrestrict H1 M1 a) /\
    mem_grows (mrestrict H1 M1) (ms_mem ms1) /\
    env_agree NF E E2 /\ CH2.den E2 (nth j BLS []) = CH2.den E (nth i BLS []) /\ CHA.denF sp0 E2 (nth j FFS []) = CHA.denF sp0 E (nth i FFS []) /\
    length (nth j FFS []) = length (nth i FFS []) /\ (forall cr, Cred i E cr -> Cred j E2 cr) /\ CC.meas cj E2 < CC.meas c E /\
    (forall model2, same_but_materialized model1 model2 -> MInv A model2 -> XI j E2 A (munrestrict H1 M1 (ms_mem ms1)) model2).

Theorem walk_leaf : forall i c ps,
  CHA.foot_chk NF d c (nth i BLS []) (nth i FFS []) = true ->
  (forall (fx' : FPState) E R A M model E' R' M1 model1,
     CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> XI i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
     exists Q : machine_state -> Prop,
       evt (hl_segs L) Q (MS (canon_regs R') (@fp_regs fx') (Z_to_bv 64 (SR.ps_pc ps)) (@fp_csr fx') None (mrestrict (ahid A model1) M1) (seg_rom (hl_segs L)))
       /\ forall ms1, Q ms1 -> walk_end i c E A (ahid A model1) M1 model1 ms1) ->
  CCA.leaf_ok (hl_segs L) CPS AMBX K FPI i c ps.
Proof.
  intros i c ps Hfoot USER fx' E R A M model E' R' M1 model1 HAt [HA HXI] HFP Hag HLF HIH.
  pose proof (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
                i c ps E E' R R' A M model M1 model1 Hfoot HAt HA Hag HLF) as HA1.
  destruct (CHA.aamb_model L ar C HI HIok LY_below NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i E A M1 model1 HA1) as (Hh1 & HMI1 & HAwf & Hoff1).
  set (H1 := ahid A model1) in *.
  destruct (USER fx' E R A M model E' R' M1 model1 HAt HA HXI HFP Hag HLF) as (Q & EVT & ENDS).
  apply (@cj_evt_srzA fx' (hl_segs L) SCFG H1 Hoff1 LY_nowrap R' _ M1 _ A model1 K Q (L5LZ.lazy_cover_ahid A model1) HAwf HMI1 Hh1 EVT).
  intros ms1 ms1' HQ Heqv model2 HMI2 HS12 Hcl.
  destruct (ENDS ms1 HQ) as (Hsv & Hrv & Hrom & j & cj & E2 & Hcj & Hpc & HFP2 & HR2 & HK2 & HFR & HGR & HagNF & HdB & HdF & Hlen & HCr & Hmeas & HXj).
  destruct Heqv as (Qr & Qf & Qpc & Qsv & Qrv & Qfc & Qm & Qrom).
  assert (Hsv' : ms_svc_pending ms1' = None) by (rewrite <- Qsv; exact Hsv). assert (Hrv' : ms_resv ms1' = None) by (rewrite <- Qrv; exact Hrv).
  rewrite (unrestrict_mkst H1 M1 ms1' Hsv' Hrv').
  rewrite <- Qf, <- Qfc, <- Qpc, <- Qm, <- Qrom, Hpc, Hrom.
  set (M2 := munrestrict H1 M1 (ms_mem ms1)).
  assert (Hcl1 : forall a, H1 a = true -> ms_mem ms1 a = None) by (intros a Ha; rewrite Qm; exact (Hcl a Ha)).
  apply (HIH j cj (mkFP (ms_fregs ms1) (ms_fcsr ms1)) E2 (ms_regs ms1') A M2 model2 Hcj).
  -
    split; [exact (regs_ok_eqv E2 _ _ _ Qr HR2)|].
    unfold CCA.vis. rewrite (L5LZ.sbm_ahid A model1 model2 HS12). fold H1. unfold M2. rewrite (vis_unrestrict H1 M1 (ms_mem ms1) Hcl1). exact HK2.
  -
    split; [|exact (HXj model2 HS12 HMI2)].
    apply (CHA.amb_step L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 Wo_incl Wo_ok
             i j E E2 A M1 M2 model1 model2 HA1); [| | exact HS12 | exact HMI2 | exact HagNF | exact HdB | exact HdF | exact Hlen | exact HCr].
    + intros a Ha. exact (munr_frame H1 M1 (ms_mem ms1) a (fun _ => HFR a Ha)).
    + exact (munr_grows H1 M1 (ms_mem ms1) HGR).
  - exact HFP2.
  - exact Hmeas.
Qed.
End Leaf.
End CWA.
