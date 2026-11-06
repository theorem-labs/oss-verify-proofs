(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim ShapeAlg HeapIface HeapIfaceA L5Defs L5Core Pm5L5DefsA PmHeapIfaceA IcptIfaceA PmIcptIfaceA
  PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmFloatXSpecsA PmEncSpecsA PmFloatXTuA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.TUXB Require G3PureXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXB Require Import DumpBufXB PrettifyXB DtoaFalseXB DtoaTrueXB WriteDoubleXB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module WDCA.
Section C.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis SM2 : hl_stack_malloc L 2 = DFXB.PC_SM.          (* [comment removed for export] *)
Hypothesis SM4 : hl_stack_malloc L 4 = WDXB.PC_SM.          (* [comment removed for export] *)
Hypothesis TPV : hl_tp L = DFXB.TP.                         (* [comment removed for export] *)
Variable CL : Z.                                            (* [comment removed for export] *)
Abbreviation IC := PMLA.C_xboth.
Hypothesis PUSHB_OK : PMESA.str_push_back_x_specA L ar HI CL DFXB.PUSHB.                 (* [comment removed for export] *)
Hypothesis SNP : PMFXA.snprintf_g_specA L ar HI IC DFXB.PC_SNP DFXB.FMT.                  (* [comment removed for export] *)
Hypothesis DSG : PMFXA.decstr_to_double_g_specA L ar HI IC DFXB.PC_DEC.                  (* [comment removed for export] *)
Hypothesis SETSH : aset_shadow_spec L ar SCFG HI WDXB.PC_SETSH 245 256.                   (* [comment removed for export] *)
Variable IL0 : icpt_layout.
Hypothesis RTG : rt_globals IL0 HI.
Hypothesis GLT : In (G3PureXB.PT_BASE, 8 * 687) (icl_globals IL0).
Hypothesis GLE : In (G3PureXB.PE_BASE, 4 * 687) (icl_globals IL0).

Theorem dump_buffer_closed : PMFXTA.dump_buffer_x_specA L ar HI IC CL DBXB.PC.
Proof. exact (dump_buffer_x_ok L ar C HI HIok LAY FPM CL PUSHB_OK). Qed.
Theorem prettify_closed : PMFXTA.prettify_x_specA L ar HI IC CL PRXB.PC.
Proof. exact (prettify_x_ok L ar C HI HIok LAY FPM CL PUSHB_OK). Qed.
Theorem dtoa_false_closed : PMFXTA.dtoa_false_x_specA L ar HI IC CL DFXB.PC.
Proof. exact (dtoa_false_x_ok L ar C HI HIok LAY SM2 TPV FPM CL SNP DSG dump_buffer_closed PUSHB_OK). Qed.
Theorem dtoa_true_closed : PMFXTA.dtoa_true_x_specA L ar HI IC CL DTXB.PC.
Proof. exact (dtoa_true_x_ok L ar C HI HIok LAY SM2 TPV FPM CL dtoa_false_closed prettify_closed PUSHB_OK IL0 RTG GLT GLE). Qed.
Theorem write_double_closed : PMESA.write_double_x_specA L ar HI IC PMFXA.WD_SCR_XA CL WDXB.PC.
Proof. exact (write_double_x_ok L ar C HI HIok LAY SM4 TPV FPM CL dtoa_true_closed SETSH). Qed.
End C.
End WDCA.
