(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim ShapeAlg HeapIface L5Defs L5Core PmLibDefs PmLibSpecs PmLayout PmEncSpecs PmFloatXSpecs PmFloatXTu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import DumpBufX PrettifyX DtoaFalseX DtoaTrueX WriteDoubleX.
Open Scope Z_scope.

Module WDC.
Section C.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  CatSim.msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PUSHB_OK : PMES.str_push_back_x_spec L HI.
Hypothesis SNP : PMFX.snprintf_g_spec L.
Hypothesis DSG : PMFX.decstr_to_double_g_spec L PML.STRTOD_SCR_V.

Theorem dump_buffer_closed : PMFXT.dump_buffer_x_spec L HI.
Proof. exact (DBX.dump_buffer_x_ok L HI HIok LAY FPM PUSHB_OK). Qed.
Theorem prettify_closed : PMFXT.prettify_x_spec L HI.
Proof. exact (PRX.prettify_x_ok L HI HIok LAY FPM PUSHB_OK). Qed.
Theorem dtoa_false_closed : PMFXT.dtoa_false_x_spec L HI PML.STRTOD_SCR_V.
Proof. exact (DFX.dtoa_false_x_ok L HI HIok LAY FPM PUSHB_OK SNP DSG dump_buffer_closed). Qed.
Theorem dtoa_true_closed : PMFXT.dtoa_true_x_spec L HI PML.STRTOD_SCR_V.
Proof. exact (DTX.dtoa_true_x_ok L HI HIok LAY FPM PUSHB_OK prettify_closed dtoa_false_closed). Qed.
Theorem write_double_closed : PMES.write_double_x_spec L HI PMES.WD_SCR_X.
Proof. exact (WDX.write_double_x_ok L HI HIok LAY FPM dtoa_true_closed). Qed.
End C.
End WDC.
Print Assumptions WDC.write_double_closed.
