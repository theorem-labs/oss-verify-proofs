(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim L5Defs HeapIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u PmFloatCSpecs_u Pm10StrtodGSpec_u Pm10StrtodG_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import Pm10DecstrG_u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DSGC.
Section Closed.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Theorem decstr_to_double_g_closed : PMFC.decstr_to_double_g_spec L PML.STRTOD_SCR_V.
Proof. exact (DecstrGProof.decstr_to_double_g_ok L FPM (STGC.strtod_g_closed L)). Qed.
End Closed.
End DSGC.

