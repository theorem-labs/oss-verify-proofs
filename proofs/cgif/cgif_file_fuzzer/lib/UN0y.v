(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YM06 YM02 YP09 YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YN03 YN2b YN00
UN0i UN11 UN24 UN0f UN33.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem ubs0_malloc_realizes_g_closed : malloc_realizes_g ubs0_msyms (MRx ubs0_msyms).
Proof using. exact (ubs0_malloc_realizes_g ubs0_alloc_meta (ubs0_malloc_small_g ubs0_alloc_slot_g)). Qed.
Corollary ubs0_API_malloc_g : forall AMH MSH NTA, malloc_realizes_g ubs0_msyms (aa_MR (ubs0_API AMH MSH NTA)).
Proof using. intros. exact ubs0_malloc_realizes_g_closed. Qed.
End a.
