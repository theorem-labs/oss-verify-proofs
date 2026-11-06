(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim L5Defs HeapIface PmLibDefs PmLibSpecs PmFloatCSpecs Pm10StrtodGSpec Pm10StrtodG.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import Pm10DecstrG.
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

