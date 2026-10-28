(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim ShapeAlg SpinAlg HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLayout_u PmFloatCSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TU Require Import WdHead_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTU Require Import TuWd_u TuWdC_u TuWdS_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module TWDF.
Section F.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  CatSim.msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis SNP : PMFC.snprintf_g_spec L.
Hypothesis DSG : PMFC.decstr_to_double_g_spec L PML.STRTOD_SCR_V.

Theorem write_double_ok : PMFC.write_double_spec L HI PML.STRTOD_SCR_V.
Proof.
  unfold PMFC.write_double_spec, PML.cps_heap. intros LB cr wd o dp0 sp r fx R M model K HH Hmo HK Hfp PRE Hcont.
  apply (TWD.main_entry L cr wd o dp0 sp r fx R M model K Hmo Hfp PRE).
  intros ms1 ms1' WP EQV. destruct WP as [HW | [HW | [HW | HW]]].
  - exact (TWD.case_A L HI HIok LAY FPM LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont ms1 ms1' HW EQV).
  - exact (TWDC.case_A2 L HI HIok LAY FPM LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont ms1 ms1' HW EQV).
  - exact (TWDC.case_C L HI HIok LAY FPM LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont ms1 ms1' HW EQV).
  - exact (TWDS.case_SN L HI HIok LAY FPM SNP DSG LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont ms1 ms1' HW EQV).
Qed.
End F.
End TWDF.
