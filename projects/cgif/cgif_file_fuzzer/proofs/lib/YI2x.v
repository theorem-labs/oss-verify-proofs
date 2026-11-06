(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YI06 YI5b YI09 YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI2z YI3a YI1s YI1r.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI src0_msyms.
Hypothesis IMG : img_laws src0_msyms (aa_MR API).
Lemma src0_cbb_specV : cbb_specV API.
Proof. unfold cbb_specV. intros. eapply (src0_cbbV API IMG); eassumption. Qed.
Lemma src0_cbl_specV : cbl_specV API.
Proof. unfold cbl_specV. intros. eapply (src0_cblV API IMG); eassumption. Qed.
Theorem src0_lzwV_closed : lzw_specV API.
Proof. exact (src0_lzwV API IMG src0_cbl_specV src0_cbb_specV). Qed.
End S.
End a.
