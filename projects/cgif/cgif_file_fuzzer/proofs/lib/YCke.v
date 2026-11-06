(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YI09 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq YCbp.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1v YCef YF0m YF0l YCej YD2l YCeh.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YE2k YE28 YE2e YE24.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0z YI10 YI12 YC4a YC8i YCbj YC1f YC20 YC8g YChc.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7x YC21.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5n YCed YCee.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCh6 YCh5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Remark tfib_cgif_closeX_pc : @pa_val _ _ PB_tfib A_TEXT + YChc.A_cgif_close = 0x83b90.   Proof. reflexivity. Qed.
Remark tfib_cgif_closeX_wfn : @pa_val _ _ PB_tfib A_TEXT + YChc.WFN_OFF = 0x8131c.   Proof. reflexivity. Qed.
Remark tfib_cgif_closeX_flush_pc : @pa_val _ _ PB_tfib A_TEXT + YChc.A_flushFrame = 0x826f4.   Proof. reflexivity. Qed.
Remark tfib_cgif_closeX_sigma_rc : @pa_sigma _ _ PB_tfib AS_cgif_raw_close = 0x8656c.   Proof. reflexivity. Qed.
Remark tfib_cgif_closeX_sigma_fclose : @pa_sigma _ _ PB_tfib AS_fclose = IC_ENTRY.   Proof. reflexivity. Qed.
Definition tfib_cgif_closeX := @YCh5.pb_cgif_closeX fx rc tfib_sink_head PB_tfib.
Check tfib_cgif_closeX.
Lemma afile_meter_trivB : forall segs B, afile_meter segs B ameter_triv.
Proof. intros segs B. constructor; intros; exact I. Qed.
Theorem tfib_closeX_of_flush :
tflush_specX tfibsegs tfib_K TfibB ameter_triv XN0 0x826f4 CTX_flushFrame 0x8131c 0x9dca8 0x9ef18 ->
tclose_specX tfibsegs tfib_K TfibB ameter_triv XN0 0x83b90 CTX_cgif_close 0x8131c 0x9dca8 0x9ef18.
Proof.
intros FLUSHX.
refine (@YCh5.pb_cgif_closeX fx rc tfib_sink_head PB_tfib tfibX_RO0 TfibB tfibX_LAWS tfibX_PALib0 CTX_cgif_close
tfib_K tfibX_AIL ameter_triv ameter_triv_laws tfibX_AFREE4 (afile_meter_trivB _ _) XN0 _ _ _ _ _ _ _ _ _ _
[pc_free_ra0 (as_code TfibB); 0x86614] tfibX_raw_close_trace tfib_raw_closeX_closed
FC_FREE1_RA FC_JOIN (tfib_afclose_spec TfibB tfibX_LAWS TfibB_syms tfibX_AIL tfibX_env tfibX_ML tfibX_AFREE) _ _
CTX_flushFrame _ FLUSHX).
1-5: (intros; unfold cl_msum, cl_macc_fr, cl_macc_b; cbn; lia).
all: try (apply memZL_In; vm_compute; reflexivity).
Qed.
Theorem tfib_closeX_closed :
tclose_specX tfibsegs tfib_K TfibB ameter_triv XN0 0x83b90 CTX_cgif_close 0x8131c 0x9dca8 0x9ef18.
Proof. exact (tfib_closeX_of_flush tfib_flushX_closed). Qed.
End a.
