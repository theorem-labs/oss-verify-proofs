(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma pow10_step : forall w j, 1 <= j -> 0 <= w < 10 ^ j -> 0 <= w / 10 < 10 ^ (j - 1).
Proof.
  intros w j Hj Hw. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  replace (10 * 10 ^ (j - 1)) with (10 ^ j); [lia|]. rewrite <- Z.pow_succ_r by lia. f_equal. lia.
Qed.

Lemma pow10_ge2 : forall w j, 10 <= w < 10 ^ j -> 2 <= j.
Proof.
  intros w j H. destruct (Z_lt_le_dec j 2) as [L|]; [|assumption]. exfalso.
  destruct (Z_lt_le_dec j 0); [rewrite Z.pow_neg_r in H by lia; lia|].
  assert (j = 0 \/ j = 1) as [-> | ->] by lia; cbn in H; lia.
Qed.

Lemma u64_lt_pow10_20 : forall w, 0 <= w < 18446744073709551616 -> 0 <= w < 10 ^ 20.
Proof. intros w H. change (10 ^ 20) with 100000000000000000000. lia. Qed.

Lemma div10_ge10 : forall w, 0 <= w -> (99 < w <-> 10 <= w / 10).
Proof. intros w H. split; intros; Z.div_mod_to_equations; lia. Qed.

Lemma neg64_range : forall x, 0 <= x < 18446744073709551616 -> 0 <= (0 - x) mod 18446744073709551616 < 18446744073709551616.
Proof. intros x H. apply Z.mod_pos_bound. lia. Qed.
