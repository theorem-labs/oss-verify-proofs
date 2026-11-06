(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnDivCorrect BnDivLoop BnInv BnSpecs BnSpecs2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma div_values : forall m v0 sh, 0 <= m -> 0 < v0 -> 0 <= sh ->
  (m * 2 ^ sh) / (v0 * 2 ^ sh) = m / v0 /\ ((m * 2 ^ sh) mod (v0 * 2 ^ sh)) / 2 ^ sh = m mod v0.
Proof.
  intros m v0 sh Hm Hv Hsh. assert (Hp : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_mul_cancel_r; lia|]. rewrite Z.mul_mod_distr_r by lia. apply Z.div_mul. lia.
Qed.

Lemma div_top_cond : forall snum loop div_n top1 v,
  limbs snum -> (loop + div_n <= length snum)%nat -> (1 <= div_n)%nat -> (top1 <= loop + div_n - 1)%nat ->
  lval (firstn (loop + div_n) snum) < Bp top1 * 2 ^ 63 -> Bp (div_n - 1) * 2 ^ 63 <= v ->
  lval (slice snum loop div_n) < v.
Proof.
  intros snum loop div_n top1 v Hs Hlen Hdn Htop HN Hv.
  assert (E : lval (firstn (loop + div_n) snum) = lval (firstn loop snum) + Bp loop * lval (slice snum loop div_n)).
  { rewrite firstn_add, lval_app, firstn_length_le by lia. reflexivity. }
  pose proof (lval_nonneg _ (limbs_firstn loop snum Hs)) as Hlo.
  pose proof (lval_nonneg _ (slice_limbs snum loop div_n Hs)) as Hhi.
  pose proof (Bp_mono top1 (loop + div_n - 1) Htop) as Hm.
  assert (EB : Bp (loop + div_n - 1) = Bp loop * Bp (div_n - 1)) by (rewrite <- Bp_add; f_equal; lia).
  pose proof (Bp_pos loop) as Hbl. pose proof (Bp_pos (div_n - 1)) as Hbd.
  set (hi := lval (slice snum loop div_n)) in *.
  assert (Hx : Bp loop * hi < Bp loop * (Bp (div_n - 1) * 2 ^ 63)).
  { assert (Bp top1 * 2 ^ 63 <= Bp (loop + div_n - 1) * 2 ^ 63) by (apply Z.mul_le_mono_nonneg_r; lia).
    rewrite EB in H. lia. }
  apply Z.mul_lt_mono_pos_l in Hx; lia.
Qed.

Lemma firstn_pad_zeros : forall (buf : list Z) m k, (m + k <= length buf)%nat ->
  firstn (m + k) (splice buf m (repeat 0 k)) = firstn m buf ++ repeat 0 k.
Proof.
  intros buf m k H. rewrite firstn_add. rewrite firstn_splice_below by lia. f_equal.
  change (firstn k (skipn m (splice buf m (repeat 0 k)))) with (slice (splice buf m (repeat 0 k)) m k).
  apply slice_splice_eq; [apply repeat_length|lia].
Qed.

Section DivSpec.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Ltac other := rewrite ?getbn_setbn_other by congruence.

End DivSpec.
