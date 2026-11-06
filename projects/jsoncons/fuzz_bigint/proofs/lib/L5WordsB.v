(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsOps.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5Words.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5WB.
Import L5W.
Notation val := BigFactsBase.val.

Lemma M_val : BigModel.W.M = 2 ^ 64. Proof. rewrite BigFactsBase.M_val. reflexivity. Qed.

Lemma reduce_loop_is_firstn ws : BigModel.reduce_loop (length ws) ws = firstn (rlen ws) ws.
Proof.
  unfold rlen. destruct (reduce_loop_drops_zeros (length ws) ws) as (m & E & Hm & _).
  rewrite E. rewrite length_firstn. f_equal. lia.
Qed.
Lemma val_firstn_rlen ws : val (firstn (rlen ws) ws) = val ws.
Proof. rewrite <- reduce_loop_is_firstn. apply BigFactsOps.reduce_loop_val. Qed.

Lemma val_pos_of_nonzero ws j : words_ok ws -> (j < length ws)%nat -> nth_w ws j <> 0 -> 0 < val ws.
Proof.
  intros W Hj Hnz. pose proof (proj1 (words_ok_BF ws) W) as WB.
  rewrite (BigFactsBase.val_single_nth ws j Hj).
  pose proof (BigFactsBase.val_nonneg (firstn j ws) (BigFactsBase.words_ok_firstn _ _ WB)).
  pose proof (BigFactsBase.val_nonneg (skipn (S j) ws) (BigFactsBase.words_ok_skipn _ _ WB)).
  pose proof (words_ok_nth ws j W). unfold nth_w in *. unfold BigModel.nth_w.
  pose proof (Z.pow_pos_nonneg BigModel.W.M (Z.of_nat j) ltac:(rewrite M_val; lia) ltac:(lia)). rewrite M_val in *. nia.
Qed.

Lemma rlen_pos_of_val ws : 0 < val ws -> (1 <= rlen ws)%nat.
Proof.
  intros V. destruct (Nat.eq_dec (rlen ws) 0) as [E|NE]; [|lia]. exfalso.
  pose proof (val_firstn_rlen ws) as X. rewrite E in X. cbn [firstn] in X. rewrite BigFactsBase.val_nil in X. lia.
Qed.

(* [comment removed for export] *)
Lemma val_lt_pow_rlen ws : words_ok ws -> val ws < 2 ^ (64 * Z.of_nat (rlen ws)).
Proof.
  intros W. rewrite <- val_firstn_rlen.
  pose proof (BigFactsBase.val_bound (firstn (rlen ws) ws) (BigFactsBase.words_ok_firstn _ _ (proj1 (words_ok_BF ws) W))) as [_ B].
  rewrite length_firstn, M_val in B. pose proof (rlen_le ws). rewrite Nat.min_l in B by lia. rewrite <- Z.pow_mul_r in B by lia. exact B.
Qed.
Lemma pow_rlen_le_val ws : words_ok ws -> (1 <= rlen ws)%nat -> 2 ^ (64 * (Z.of_nat (rlen ws) - 1)) <= val ws.
Proof.
  intros W H1. pose proof (rlen_le ws) as RL. pose proof (rlen_top ws H1) as TOP.
  pose proof (proj1 (words_ok_BF ws) W) as WB.
  rewrite (BigFactsBase.val_single_nth ws (rlen ws - 1) ltac:(lia)).
  pose proof (BigFactsBase.val_nonneg (firstn (rlen ws - 1) ws) (BigFactsBase.words_ok_firstn _ _ WB)).
  pose proof (BigFactsBase.val_nonneg (skipn (S (rlen ws - 1)) ws) (BigFactsBase.words_ok_skipn _ _ WB)).
  pose proof (words_ok_nth ws (rlen ws - 1) W). unfold nth_w in *. unfold BigModel.nth_w.
  rewrite M_val. rewrite <- Z.pow_mul_r by lia. replace (64 * Z.of_nat (rlen ws - 1)) with (64 * (Z.of_nat (rlen ws) - 1)) by lia.
  pose proof (Z.pow_pos_nonneg 2 (64 * (Z.of_nat (rlen ws) - 1)) ltac:(lia) ltac:(lia)). nia.
Qed.
(* [comment removed for export] *)
Lemma rlen_mono a b : words_ok a -> words_ok b -> val a <= val b -> (rlen a <= rlen b)%nat.
Proof.
  intros Wa Wb Hv. destruct (Nat.lt_ge_cases (rlen b) (rlen a)) as [LT|GE]; [|exact GE]. exfalso.
  pose proof (val_lt_pow_rlen b Wb) as B. pose proof (pow_rlen_le_val a Wa ltac:(lia)) as A.
  assert (2 ^ (64 * Z.of_nat (rlen b)) <= 2 ^ (64 * (Z.of_nat (rlen a) - 1))) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma rlen_app_zero ws : rlen (ws ++ [0]) = rlen ws.
Proof.
  destruct (Nat.eq_dec (rlen ws) 0) as [Z0|NZ].
  - apply rlen_charact. rewrite length_app; cbn; lia.
    + intros i Hi. rewrite length_app in Hi; cbn in Hi. unfold nth_w. destruct (Nat.lt_ge_cases i (length ws)).
      rewrite app_nth1 by lia. apply (rlen_zeros ws). lia. rewrite app_nth2 by lia. destruct (i - length ws)%nat; [reflexivity|]. cbn. destruct n; reflexivity.
    + left. exact Z0.
  - pose proof (rlen_le ws). apply rlen_charact. rewrite length_app; cbn; lia.
    + intros i Hi. rewrite length_app in Hi; cbn in Hi. unfold nth_w. destruct (Nat.lt_ge_cases i (length ws)).
      rewrite app_nth1 by lia. apply (rlen_zeros ws). lia. rewrite app_nth2 by lia. destruct (i - length ws)%nat; [reflexivity|]. cbn. destruct n; reflexivity.
    + right. unfold nth_w. rewrite app_nth1 by lia. apply (rlen_top ws). lia.
Qed.
End L5WB.
