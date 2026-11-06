(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceB LaCheck LbGlue LbFinal LaUnitB16p LaUnitB0p.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem lib_B_of_hand : (forall k, (k = 1 \/ k = 4 \/ k = 5) -> malloc_stmt_B k) -> cbd_stmt_B -> lib_stmt_B.
Proof.
  intros HM HC. exact (LBF.lxa_lib_stmt4 _ _ _ _ UNIT_B16p_obl UNIT_B16s_obl UNIT_B0p_obl UNIT_B0s_obl HM HC).
Qed.
