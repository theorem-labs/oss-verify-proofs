(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition szwrap (k a : Z) : Z := (a + 2 ^ (k - 1)) mod 2 ^ k - 2 ^ (k - 1).

Lemma szwrap_eqm : forall k a, 0 < k -> (szwrap k a) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros k a Hk. unfold szwrap.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Zminus_mod_idemp_l.
  replace (a + 2 ^ (k - 1) - 2 ^ (k - 1)) with a by lia. reflexivity.
Qed.

