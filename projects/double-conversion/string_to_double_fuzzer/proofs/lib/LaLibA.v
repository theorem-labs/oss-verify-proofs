(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LaCheck LaGlue LaFinal LaUnitA16p LaUnitA0p.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem lib_A_of_hand : (forall k, (k = 1 \/ k = 4 \/ k = 5) -> malloc_stmt k) -> cbd_stmt_A -> lib_stmt_A.
Proof.
  intros HM HC. exact (LAF.lxa_lib_stmt4 _ _ _ _ UNIT_A16p_obl UNIT_A16s_obl UNIT_A0p_obl UNIT_A0s_obl HM HC).
Qed.
