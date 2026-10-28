(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YI09 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq YCbp.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0m AF0l ACej AD2l ACeh.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AE28 AE2e AE24.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0x YI0y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AI12.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC1f YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChc.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7x YC21.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACed ACee.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACh6 ACh5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Remark tfib_cgif_closeX_pc : @pa_val _ _ PB_tfib A_TEXT + AChc.A_cgif_close = 0x83f54.   Proof. reflexivity. Qed.
Remark tfib_cgif_closeX_wfn : @pa_val _ _ PB_tfib A_TEXT + AChc.WFN_OFF = 0x81a18.   Proof. reflexivity. Qed.
Remark tfib_cgif_closeX_flush_pc : @pa_val _ _ PB_tfib A_TEXT + AChc.A_flushFrame = 0x82b00.   Proof. reflexivity. Qed.
Remark tfib_cgif_closeX_sigma_rc : @pa_sigma _ _ PB_tfib AS_cgif_raw_close = 0x86684.   Proof. reflexivity. Qed.
Remark tfib_cgif_closeX_sigma_fclose : @pa_sigma _ _ PB_tfib AS_fclose = IC_ENTRY.   Proof. reflexivity. Qed.
Definition tfib_cgif_closeX := @ACh5.pb_cgif_closeX fx rc tfib_sink_head PB_tfib.
Check tfib_cgif_closeX.
Lemma afile_meter_trivB : forall segs B, afile_meter segs B ameter_triv.
Proof. intros segs B. constructor; intros; exact I. Qed.
Theorem tfib_closeX_of_flush :
tflush_specX tfibsegs tfib_K TfibB ameter_triv XN0 0x82b00 CTX_flushFrame 0x81a18 0x9da38 0x9eca8 ->
tclose_specX tfibsegs tfib_K TfibB ameter_triv XN0 0x83f54 CTX_cgif_close 0x81a18 0x9da38 0x9eca8.
Proof.
intros FLUSHX.
refine (@ACh5.pb_cgif_closeX fx rc tfib_sink_head PB_tfib tfibX_RO0 TfibB tfibX_LAWS tfibX_PALib0 CTX_cgif_close
tfib_K tfibX_AIL ameter_triv ameter_triv_laws tfibX_AFREE4 (afile_meter_trivB _ _) XN0 _ _ _ _ _ _ _ _ _ _
[pc_free_ra0 (as_code TfibB); 0x86720] tfibX_raw_close_trace tfib_raw_closeX_closed
FC_FREE1_RA FC_JOIN (tfib_afclose_spec TfibB tfibX_LAWS TfibB_syms tfibX_AIL tfibX_env tfibX_ML tfibX_AFREE) _ _
CTX_flushFrame _ FLUSHX).
1-5: (intros; unfold cl_msum, cl_macc_fr, cl_macc_b; cbn; lia).
all: try (apply memZL_In; vm_compute; reflexivity).
Qed.
Theorem tfib_closeX_closed :
tclose_specX tfibsegs tfib_K TfibB ameter_triv XN0 0x83f54 CTX_cgif_close 0x81a18 0x9da38 0x9eca8.
Proof. exact (tfib_closeX_of_flush tfib_flushX_closed). Qed.
End a.
