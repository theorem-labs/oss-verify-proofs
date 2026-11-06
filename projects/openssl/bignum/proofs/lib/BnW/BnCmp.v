(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition cmp1 (x y : Z) : Z := if x =? y then 0 else if y <? x then 1 else -1.

Lemma cmp_words_cons : forall x y a b, cmp_words (x :: a) (y :: b) = if cmp_words a b =? 0 then cmp1 x y else cmp_words a b.
Proof. reflexivity. Qed.

Lemma cmp_words_snoc : forall a b x y, length a = length b ->
  cmp_words (a ++ [x]) (b ++ [y]) = if x =? y then cmp_words a b else cmp1 x y.
Proof.
  induction a as [|u a IH]; intros [|v b] x y H; cbn [length] in H; try discriminate.
  - cbn [app]. rewrite cmp_words_cons. cbn [cmp_words]. unfold cmp1. destruct (x =? y); reflexivity.
  - cbn [app]. rewrite !cmp_words_cons. rewrite (IH b x y) by lia.
    destruct (Z.eqb_spec x y) as [E|E]; [reflexivity|].
    unfold cmp1. destruct (Z.eqb_spec x y) as [E'|_]; [contradiction|]. destruct (y <? x); reflexivity.
Qed.

Lemma firstn_S_nth_error : forall (l : list Z) k x, nth_error l k = Some x -> firstn (S k) l = firstn k l ++ [x].
Proof.
  induction l as [|u l IH]; intros [|k] x H; cbn in H; try discriminate.
  - inversion H. reflexivity.
  - cbn [firstn app]. f_equal. apply IH. exact H.
Qed.

Lemma cmp_words_top : forall a b k x y, length a = length b -> nth_error a k = Some x -> nth_error b k = Some y ->
  cmp_words (firstn (S k) a) (firstn (S k) b) = if x =? y then cmp_words (firstn k a) (firstn k b) else cmp1 x y.
Proof.
  intros a b k x y L Ha Hb. rewrite (firstn_S_nth_error a k x Ha), (firstn_S_nth_error b k y Hb).
  apply cmp_words_snoc. rewrite !length_firstn. lia.
Qed.

Lemma limbs_nth_error_lit : forall l k x, limbs l -> nth_error l k = Some x -> 0 <= x < 18446744073709551616.
Proof.
  intros l k x H E. unfold limbs in H. rewrite Forall_forall in H. apply nth_error_In in E. exact (H x E).
Qed.

Definition zeros_above (l : list Z) (j : nat) : Prop := forall i y, (j <= i)%nat -> nth_error l i = Some y -> y = 0.

Lemma zeros_above_len : forall l, zeros_above l (length l).
Proof. intros l i y Hi E. exfalso. assert (nth_error l i <> None) by congruence. apply nth_error_Some in H. lia. Qed.

Lemma zeros_above_step : forall l j, zeros_above l (S j) -> nth_error l j = Some 0 -> zeros_above l j.
Proof.
  intros l j H E i y Hi Ey. destruct (Nat.eq_dec i j) as [->|N]; [congruence|]. apply (H i y); [lia | exact Ey].
Qed.

Lemma existsb_nonzero_zeros : forall l, zeros_above l 0 -> existsb nonzero l = false.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. cbn [existsb].
  rewrite (H 0%nat x ltac:(lia) eq_refl). cbn. apply IH. intros i y Hi E. apply (H (S i) y); [lia | exact E].
Qed.

Lemma existsb_nonzero_nth : forall l j y, nth_error l j = Some y -> y <> 0 -> existsb nonzero l = true.
Proof.
  induction l as [|x l IH]; intros [|j] y E N; cbn in E; try discriminate.
  - inversion E; subst. cbn [existsb]. unfold nonzero. destruct (Z.eqb_spec y 0); [contradiction | reflexivity].
  - cbn [existsb]. rewrite (IH j y E N). apply orb_true_r.
Qed.
