(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YM06 YM02 YP09 YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN03 YN2b YN00
YN0i YN11 YN24 YN0f YN33.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem src0_malloc_realizes_g_closed : malloc_realizes_g src0_msyms (MRx src0_msyms).
Proof. exact (src0_malloc_realizes_g src0_alloc_meta (src0_malloc_small_g src0_alloc_slot_g)). Qed.
Corollary src0_API_malloc_g : forall AMH MSH NTA, malloc_realizes_g src0_msyms (aa_MR (src0_API AMH MSH NTA)).
Proof. intros. exact src0_malloc_realizes_g_closed. Qed.
End a.
