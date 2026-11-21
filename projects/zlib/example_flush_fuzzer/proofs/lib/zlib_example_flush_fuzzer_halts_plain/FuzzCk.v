(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec FuzzZ.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).















Lemma mod_mod_pow2 : forall a i j, 0 <= i <= j -> (a mod 2 ^ j) mod 2 ^ i = a mod 2 ^ i.
Proof.
  intros a i j Hij. pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) ltac:(lia)).
  pose proof (Z.pow_pos_nonneg 2 (j - i) ltac:(lia) ltac:(lia)).
  replace (2 ^ j) with (2 ^ i * 2 ^ (j - i)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.


























