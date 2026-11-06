(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA PmEncSpecs2A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PushSlowR0XB PushSlowR1XB PushSlowR2XB PushSlowN0XB PushSlowN1XB PushSlowN2XB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import PMES.

Section PushSlowXB.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Variable onmax : Z.
Hypothesis OPNEW_OK : PMESA.opnew_x_specA L ar HI onmax 1429232.       (* [comment removed for export] *)
Hypothesis ANN : aannotate_spec L ar SCFG HI 542968 4096.                (* [comment removed for export] *)
Hypothesis OPDEL_OK : PMSA.opdel_specA L ar HI 1046256.                    (* [comment removed for export] *)

Lemma depth_cases : forall es : estate, es = [] \/ depth es = 1 \/ 2 <= depth es.
Proof. intros es. unfold depth. destruct es as [|c [|c' es']]; [left; reflexivity | right; left; reflexivity | right; right; cbn [length]; lia]. Qed.

Theorem push_slow_root_ok : PMES2A.push_slow_specXB L ar HI onmax PMES2A.PC_PUSH_SLOW_ROOT_xboth.
Proof.
  intros LBo FF LK cr A sp r V es b capb arr ib. destruct (depth_cases es) as [D|[D|D]].
  - exact (push_slow_root_d0_ok L ar C HI HIok LAY FPM onmax OPNEW_OK ANN LBo FF LK cr A sp r V es b capb arr ib D).
  - exact (push_slow_root_d1_ok L ar C HI HIok LAY FPM onmax OPNEW_OK ANN OPDEL_OK LBo FF LK cr A sp r V es b capb arr ib D).
  - exact (push_slow_root_d2_ok L ar C HI HIok LAY FPM onmax OPNEW_OK ANN OPDEL_OK LBo FF LK cr A sp r V es b capb arr ib D).
Qed.

Theorem push_slow_nested_ok : PMES2A.push_slow_specXB L ar HI onmax PMES2A.PC_PUSH_SLOW_NESTED_xboth.
Proof.
  intros LBo FF LK cr A sp r V es b capb arr ib. destruct (depth_cases es) as [D|[D|D]].
  - exact (push_slow_nested_d0_ok L ar C HI HIok LAY FPM onmax OPNEW_OK ANN LBo FF LK cr A sp r V es b capb arr ib D).
  - exact (push_slow_nested_d1_ok L ar C HI HIok LAY FPM onmax OPNEW_OK ANN OPDEL_OK LBo FF LK cr A sp r V es b capb arr ib D).
  - exact (push_slow_nested_d2_ok L ar C HI HIok LAY FPM onmax OPNEW_OK ANN OPDEL_OK LBo FF LK cr A sp r V es b capb arr ib D).
Qed.
Print Assumptions push_slow_root_ok.
End PushSlowXB.
