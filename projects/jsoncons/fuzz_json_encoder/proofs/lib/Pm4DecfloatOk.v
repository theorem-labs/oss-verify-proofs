(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core L5LazyA
  Pm4PlanKit Pm4L5DefsA FrmInv Pm4FrmInv PmHeapIfaceA PmLibDefsA PmLibSpecsA CutVFXM DecIface DecScanPure DecOkDefsM DecOkSemM DecOkSemA DecIfaceA FloatLazyA DecOkLazyA
  Pm4DecKinds5 Pm4DecfloatPre Pm4DecfloatAt Pm4ScanexpOk.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD CutCertA CutHeapA CutL5A CutBridgeA CutPureA CutVFA Pm4CutKitD DecAssume Pm4Leaf_scalbnl.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_decfloat5_xasan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK. Import DFOA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DFTA.
Section Final.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout. Variable ar : asan_run. Variable C : asan_statics_cells. Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FL : PDCA.float_layoutA L AD.

Theorem decfloat_okA : forall e2, PDCA.decfloat_contractA L ar HI PMSA.fp_ok AD e2.
Proof.
  intros e2 LB FF LK cr A fx R M model K SP F P Q CAN sv txt HH Hmo HKnil Hfp Hstk Hroom Hffrs Hpre Hcont.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (FPM : forall (fx fx' : FPState) R0 pc M0 R' pc' M', msteps (hl_segs L) (@mkst fx R0 (Z_to_bv 64 pc) M0 (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx').
  { rewrite LS. intros fx0 fx' R0 pc M0 R' pc' M' H Hf. exact (Pm4FrmInv.msteps_fp_ok fx0 fx' R0 _ M0 _ R' _ M' _ H Hf). }
  destruct FL as [TP CELLS]. cbn [PDC.a_TP PDC.a_G PDC.a_img_lo PDC.a_img_hi AD PDCA.xasan] in TP, CELLS.
  set (N := Z.of_nat (length txt)).
  destruct (DFAA.entry_ok e2 N) as (Hci & Hki & Hpc). rewrite <- Hpc.
  pose proof (DFAA.entry_at L ar C HI HIok LAY e2 LB FF LK cr A R M model SP F P Q CAN sv txt HH Hstk Hpre) as HAt. cbv zeta in HAt. fold N in HAt.
  destruct hd_ok as (H1 & H2 & H3 & H4).
  assert (SC_OK : incl (@nil (Z * Z * Z)) (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) (@nil (Z * Z * Z)))
    by (split; [intros x [] | apply Forall_nil]).
  assert (GOT_OK : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L)
    by (unfold GLO, GHI; rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI; lia).
  assert (IMGR : hl_img_lo L <= PDC.a_img_lo AD /\ PDC.a_img_hi AD <= hl_img_hi L /\ forall a, PDC.a_img_lo AD <= a < PDC.a_img_hi AD -> ~ hl_rt_static L a).
  { cbn [PDC.a_img_lo PDC.a_img_hi AD PDCA.xasan]. rewrite ILO, IHI. split; [lia|]. split; [lia|]. intros a Ha Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). lia. }
  refine (DOLA.decfloat_runA L ar C HI HIok LYI LYR LYB LYN PMSA.fp_ok (fun fx H => H) FPM AD CPS TAGS RETS DK5.DKINDS HDECL RET_PC SCALBNL INL CALLEES [] GLO GHI
            _ tags_ok heap_ok foot_ok cuts_ok gotos_ok others_ok H1 H2 H3 H4 _ _ (callees_ok L ar C HI HIok LAY) (SXOA.scanexp_okA L ar C HI HIok LAY) (Leaf_scalbnl_xasan.ok L ar C HI HIok LAY)
            SC_OK GOT_OK IMGR TP CELLS e2 (DFAA.entry_ix e2 N) (DFAA.entry_cp e2 N) LB FF LK cr A fx R M model K SP F P Q CAN sv txt _ Hci Hki Hpc HH Hmo HKnil Hfp Hstk Hroom Hffrs Hpre
            (DFAA.mkE0_ok _ _ _ _ _ _) HAt Hcont).
  - rewrite LS. exact (plans lems).
  - rewrite LS. exact ret_pc_ok.
  - rewrite LS. exact inl_ok.
Qed.
End Final.
End DFTA.
