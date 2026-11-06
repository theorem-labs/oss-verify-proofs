(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceB LbLibB AsMallocB BnB_cbd3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem lib_B : lib_stmt_B.
Proof.
  apply lib_B_of_hand; [|exact cbd_B].
  intros k [-> | [-> | ->]]; [exact mallocB_1 | exact mallocB_4 | exact mallocB_5].
Qed.
