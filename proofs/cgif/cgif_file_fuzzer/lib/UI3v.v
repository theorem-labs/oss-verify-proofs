(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI5d UI2y UI4e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Hypothesis IMG : img_laws ubs0_msyms (aa_MR API).
Hypothesis FWRITE : fwrite_spec ubs0_msyms (aa_MR API) ubs0_A_fwrite.
Theorem ubs0_rawadd_specX : rawadd_specX API.
Proof using FWRITE IMG. exact (ubs0_cgif_raw_addframe_X API IMG FWRITE (ubs0_lzw_specX API IMG)). Qed.
End S.
End a.
