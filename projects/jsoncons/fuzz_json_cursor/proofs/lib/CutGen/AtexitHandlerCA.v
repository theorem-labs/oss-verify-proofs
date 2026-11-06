(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefsA PmLibSpecsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module AHA.
Definition PC : Z := 981280.
Lemma ret_handler : CL.is_ret_at RSEGS PC. Proof. CL.solve_is_ret. Qed.
End AHA.

Section AtexitHandlerOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_casan.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.

Theorem atexit_handler_ok : forall ILX : icpt_layout_x, PMSA.atexit_handler_specA L ar HI IC ILX.
Proof.
  intros ILX. unfold PMSA.atexit_handler_specA, PmIcptIfaceA.ahandler_spec. cbv zeta. intros a fx R M model LB FF LK cr A Kt HH Hh HMI Ha0 Htp Hret Hstk HK Hcont.
  change (PMLA.ATEXIT_HANDLER IC) with AHA.PC.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _).
  assert (AWF : A_wf A) by exact (proj1 (PmHeapIfaceA.aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH)).
  pose proof (CHA.vis_off_segments L ar C HI HIok LYB _ _ _ _ _ _ _ HH) as HOFF.
  destruct Hstk as (S16 & SHI & SLE & STOP & SWR & SDEF).
  rewrite LS. rewrite LS in HOFF, SWR.
  apply (CCA.ret_cps RSEGS fx R AHA.PC M model A Kt AHA.ret_handler Hh HMI AWF HOFF L5A.wx_nowrap Hret).
  intros model1 HMI1 HS. rewrite LS in Hcont.
  apply (Hcont R M model1 (L5.regs_preserved_refl R)).
  - intros a' _ _. reflexivity.
  -
    intros a' Ha'.
    set (sp := bv_unsigned (getr R 2%bv)) in *.
    assert (D0 : 0 <= a' - (sp - iclx_scr_handler ILX)) by (clear - Ha'; lia).
    assert (D1 : a' - (sp - iclx_scr_handler ILX) + Z.of_nat 1 <= iclx_scr_handler ILX) by (clear - Ha'; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    pose proof (SWR (a' - (sp - iclx_scr_handler ILX)) 1%nat D0 D1) as OK.
    replace (sp - iclx_scr_handler ILX + (a' - (sp - iclx_scr_handler ILX))) with a' in OK by (clear; lia).
    cbn [store_ok] in OK. unfold wview in OK.
    destruct (M (Z_to_bv 64 a')) as [b|] eqn:HM; [discriminate|].
    rewrite (find_segment1_none_above RSEGS (hl_img_hi L) (bv_unsigned (Z_to_bv 64 a'))) in OK; [discriminate | rewrite <- LS; exact LYB |].
    rewrite u64_of_Z by (clear - Ha' SHI CL STOP SLE; lia). rewrite IHI. clear - Ha' SHI CL. lia.
  - intros a' Hd. exact Hd.
  - exact (L5LZ.sbm_model_rt _ _ HS).
  - exact HMI1.
  - assert (VML : vml_of model1 = vml_of model) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ HS), (L5LZ.sbm_lazy _ _ HS); reflexivity).
    rewrite VML. exact HH.
Qed.
End AtexitHandlerOk.

