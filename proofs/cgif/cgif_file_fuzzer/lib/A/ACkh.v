(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YI09 YK04 YA0n YG00 YG01 YG0f YG0n YG0d YM05 YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej AD2l ACeh ACei.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0x YI0y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AI12.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC1f YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YCbp YC7z YC7y YC7x YC21.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgo ACfz ACed ACee.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {rc : YM05.RunCeil} {fx : YK11.FPState}.
Lemma tfib_af_xnums : af_xnums ameter_triv XN0.
Proof. repeat split; xn0_tac. Qed.
Theorem tfib_addframeX_closed :
@tflush_specX fx rc tfib_sink_head tfibsegs tfib_K TfibB ameter_triv XN0 0x82b00 CTX_flushFrame 0x81a18 0x9da38 0x9eca8 ->
@taddframe_specX fx rc tfib_sink_head tfibsegs tfib_K TfibB ameter_triv XN0 A_cgif_addframe CTX_cgif_addframe 0x81a18 0x9da38 0x9eca8.
Proof.
intros FLUSHX.
refine (@ACfz.pb_cgif_addframeX fx rc tfib_sink_head PB_tfib tfibX_RO0 TfibB tfib_K ameter_triv XN0 0x81a18 CTX_cgif_addframe
tfibX_PALib0 tfibX_LAWS tfibX_AIL ameter_triv_laws tfib_af_xnums tfibX_AMALLOC4 tfibX_AFREE4 tfibX_AMEMCPY _ CTX_flushFrame _ FLUSHX
tfibX_AMEMCMP tfibX_ABCMP).
-
unfold af_sites. cbn [pa_val PB_tfib PI0_of pa2_val0 PB2_tfib A_TEXT nth Z.add].
tfibX_universe.
-
cbn. left. reflexivity.
Qed.
Theorem tfib_addframeX_all :
@taddframe_specX fx rc tfib_sink_head tfibsegs tfib_K TfibB ameter_triv XN0 A_cgif_addframe CTX_cgif_addframe 0x81a18 0x9da38 0x9eca8.
Proof. exact (tfib_addframeX_closed tfib_flushX_closed). Qed.
End a.
