(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition cdiv8 (v : Z) : Z := (v + 7) / 8.

Lemma cdiv8_nonneg : forall v, 0 <= v -> 0 <= cdiv8 v.
Proof. intros v H. unfold cdiv8. apply Z.div_pos; lia. Qed.
Lemma cdiv8_le : forall a b, a <= b -> cdiv8 a <= cdiv8 b.
Proof. intros a b H. unfold cdiv8. apply Z.div_le_mono; lia. Qed.
Lemma cdiv8_add : forall a b, 0 <= a -> 0 <= b -> cdiv8 (a + b) <= cdiv8 a + cdiv8 b.
Proof. intros a b Ha Hb. unfold cdiv8. Z.to_euclidean_division_equations. lia. Qed.
Lemma cdiv8_mul8 : forall a k, cdiv8 (a + 8 * k) = cdiv8 a + k.
Proof. intros a k. unfold cdiv8. Z.to_euclidean_division_equations. lia. Qed.

Lemma cdiv8_shiftr : forall x, 0 <= x -> Z.shiftr (x + 3 + 7) 3 = cdiv8 (x + 3).
Proof. intros x H. rewrite Z.shiftr_div_pow2 by lia. unfold cdiv8. change (2 ^ 3) with 8. f_equal. Qed.

Definition KBLK : Z := 16383.
Definition cb_budget (n : Z) : Z := n + 11 + 5 * (n / KBLK).
Definition cbound (n : Z) : Z := n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 13.

Lemma cbound_range : forall n, 0 <= n <= 2 ^ 20 -> n + 13 <= cbound n <= 2 * n + 13.
Proof.
  intros n H. unfold cbound. rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 12) with 4096; change (2 ^ 14) with 16384; change (2 ^ 25) with 33554432; change (2 ^ 20) with 1048576 in H.
  Z.to_euclidean_division_equations. lia.
Qed.

Lemma cb_budget_le : forall n, 0 <= n <= 2 ^ 20 -> cb_budget n <= cbound n.
Proof.
  intros n H. unfold cb_budget, cbound, KBLK. rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 12) with 4096; change (2 ^ 14) with 16384; change (2 ^ 25) with 33554432; change (2 ^ 20) with 1048576 in H.
  Z.to_euclidean_division_equations. lia.
Qed.

Definition phi0 (a : Z) : Z := a + 5 * (a / KBLK).
Lemma phi0_mono : forall a b, 0 <= a <= b -> phi0 a <= phi0 b.
Proof. intros a b H. unfold phi0, KBLK. pose proof (Z.div_le_mono a b 16383 ltac:(lia) ltac:(lia)). lia. Qed.
Lemma phi0_step : forall a L, 0 <= a -> KBLK <= L -> phi0 a + L + 5 <= phi0 (a + L).
Proof. intros a L Ha HL. unfold phi0, KBLK in *. Z.to_euclidean_division_equations. lia. Qed.
Lemma phi0_budget : forall a n, 0 <= a <= n -> phi0 a + 11 <= cb_budget n.
Proof. intros a n H. pose proof (phi0_mono a n H). unfold phi0, cb_budget in *. lia. Qed.

