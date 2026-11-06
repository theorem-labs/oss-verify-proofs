(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LaLibA AsMallocA BnA_cbd3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem lib_A : lib_stmt_A.
Proof.
  apply lib_A_of_hand; [|exact cbd_A].
  intros k [-> | [-> | ->]]; [exact malloc_1 | exact malloc_4 | exact malloc_5].
Qed.
