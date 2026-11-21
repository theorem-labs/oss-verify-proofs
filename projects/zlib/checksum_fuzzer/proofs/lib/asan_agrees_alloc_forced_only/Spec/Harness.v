(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section Harness.
Context {St : Type}.

Definition fuzz_one (data : list Z) : M St Z := mret 0.

End Harness.
