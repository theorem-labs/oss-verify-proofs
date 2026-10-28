(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The float writer closed over the U specs of the ubsan build: dump_buffer, prettify, dtoa_false, dtoa_true and
   write_double, each from its walk file, given the push_back, snprintf and decstr_to_double specs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim ShapeAlg HeapIface L5Defs L5Core.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmFloatXSpecs_u5 PmFloatXTu_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require Import DumpBufXU PrettifyXU DtoaFalseXU DtoaTrueXU WriteDoubleXU.
Open Scope Z_scope.

Module WDCU.
Section C.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  CatSim.msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PUSHB_OK : PMES.str_push_back_x_specU L HI.
Hypothesis SNP : PMFX.snprintf_g_spec L.
Hypothesis DSG : PMFX.decstr_to_double_g_spec L PML.STRTOD_SCR_V.

Theorem dump_buffer_closed : PMFXT.dump_buffer_x_specU L HI.
Proof. apply DBXU.dump_buffer_x_ok; assumption. Qed.
Theorem prettify_closed : PMFXT.prettify_x_specU L HI.
Proof. apply PRXU.prettify_x_ok; assumption. Qed.
Theorem dtoa_false_closed : PMFXT.dtoa_false_x_specU L HI PML.STRTOD_SCR_V.
Proof. apply DFXU.dtoa_false_x_ok; first [assumption | exact dump_buffer_closed]. Qed.
Theorem dtoa_true_closed : PMFXT.dtoa_true_x_specU L HI PML.STRTOD_SCR_V.
Proof. apply DTXU.dtoa_true_x_ok; first [assumption | exact prettify_closed | exact dtoa_false_closed]. Qed.
Theorem write_double_closed : PMES.write_double_x_specU L HI PMES.WD_SCR_X.
Proof. apply WDXU.write_double_x_ok; first [assumption | exact dtoa_true_closed]. Qed.
End C.
End WDCU.
Print Assumptions WDCU.write_double_closed.
