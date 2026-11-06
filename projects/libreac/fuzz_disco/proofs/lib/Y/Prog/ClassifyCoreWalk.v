(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v, with its module paths changed; 1096 of its 1159 lines of code are new or changed and 428 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ClassifyCoreSw.v; 28 of its 69 lines of code are new or changed and 1118 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacPortsParse ClassifyCore ClassifyCoreSeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
ClassifyCoreLib ClassifyCoreCall ClassifyCoreHead ClassifyCoreM1 ClassifyCoreM2 ClassifyCoreSw
ClassifyCoreM3 ClassifyCoreM4 ClassifyCoreEpi.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ABCMP : forall fq, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis AMEMCPY : forall fq, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis AMEMSET : forall fq, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis ASM2 : forall fq, astack_malloc_realizes (fx := fq) SEGS B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TPORTS : treac_ports_parse_spec B.
Hypothesis ROM : cls_rom_ok B.

Theorem pb_classify_core_of_needs : tparse_need B -> tchk_need B -> tclassify_core_spec B.
Proof.
intros TPN TCN.
pose proof (cls_now B LAWS) as NOW. pose proof (cls_achain B LAWS) as ACH.
pose proof (cls_kept_step B LAWS) as KS.
assert (HX : cls_from_X B) by (eapply cls_epi; eassumption).
assert (HR3 : cls_from_R3 B) by (eapply cls_m4; eassumption).
assert (HQ : cls_from_Q B) by (eapply cls_call_Q; eassumption).
assert (HROLE : cls_from_ROLE B) by (eapply cls_m3; eassumption).
assert (HSW : cls_from_SW B) by (eapply cls_sw; eassumption).
assert (HR2 : cls_from_R2 B) by (eapply cls_m2; eassumption).
assert (HK : cls_from_K B) by (eapply cls_call_K; eassumption).
assert (HR1 : cls_from_R1 B) by (eapply cls_m1; eassumption).
assert (HP : cls_from_P B) by (eapply cls_call_P; eassumption).
unfold tclassify_core_spec. apply tcls_entry_of_pre. intros cx Hpre.
eapply cls_head; eassumption.
Qed.

End h.
End f.
End d.
