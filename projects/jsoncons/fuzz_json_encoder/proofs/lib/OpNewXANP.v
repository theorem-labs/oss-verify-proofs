(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec HeapIface HeapIfaceA L5Defs L5Core PmHeapIfaceA HeapIfaceN Pm4PlanKit PmLibDefsA PmLibSpecsA PmEncSpecsA Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import Pm4CutKit CutL5A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require OpNewXAN.
Open Scope Z_scope.

Section OpNewOkNP.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps Pm4PlanKit.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Pm4PlanKit.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom Pm4PlanKit.RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis MALLOCN : amalloc_specN L ar SCFG HI.

Theorem opnewN_x_ok : PMESA.opnew_x_specA L ar HI NB 0x1594d8.
Proof. exact (OpNewXAN.opnewN_ok L ar C HI HIok LAY FPM MALLOCN). Qed.

Print Assumptions opnewN_x_ok.
End OpNewOkNP.
