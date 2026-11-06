(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1m5 X1le X1kx X1lp.

Theorem rrealloc_spec {RCEIL : RunCeiling} : rrealloc_stmt.
Proof. exact (rrealloc_spec_proof rlibc_malloc_spec rlibc_free_spec_proof). Qed.

Theorem rlibc_realloc_spec {RCEIL : RunCeiling} : rlibc_realloc_stmt.
Proof. exact (rlibc_realloc_spec_proof rlibc_malloc_spec rlibc_free_spec_proof). Qed.
