(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Fixpoint decval_n (data : list Z) (s : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S k => 10 * decval_n data s k + (byte_at data (s + Z.of_nat k) - 48)
  end.

Definition decval (data : list Z) (s p : Z) : Z := decval_n data s (Z.to_nat (p - s)).

Definition isdig (c : Z) : Prop := 48 <= c <= 57.

Lemma decval_nil : forall data s, decval data s s = 0.
Proof. intros data s. unfold decval. rewrite Z.sub_diag. reflexivity. Qed.

Lemma decval_step : forall data s p, s <= p -> decval data s (p + 1) = 10 * decval data s p + (byte_at data p - 48).
Proof.
  intros data s p H. unfold decval. replace (Z.to_nat (p + 1 - s)) with (S (Z.to_nat (p - s))) by lia.
  cbn [decval_n]. f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma decval_n_zero_head : forall data s n, byte_at data s = 48 -> decval_n data s (S n) = decval_n data (s + 1) n.
Proof.
  intros data s n Hz. induction n as [|n IH].
  - cbn [decval_n]. rewrite Z.add_0_r, Hz. reflexivity.
  - cbn [decval_n] in *. rewrite IH. f_equal. f_equal. f_equal. lia.
Qed.

Lemma decval_zero_head : forall data s p, s < p -> byte_at data s = 48 -> decval data s p = decval data (s + 1) p.
Proof.
  intros data s p H Hz. unfold decval. replace (Z.to_nat (p - s)) with (S (Z.to_nat (p - (s + 1)))) by lia.
  apply decval_n_zero_head. exact Hz.
Qed.

(* [comment removed for export] *)
Lemma decval_n_bound : forall data s n, (forall i, s <= i < s + Z.of_nat n -> isdig (byte_at data i)) ->
  0 <= decval_n data s n < 10 ^ Z.of_nat n.
Proof.
  intros data s n. induction n as [|n IH]; intros HD.
  - cbn. lia.
  - cbn [decval_n]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    assert (IH' : 0 <= decval_n data s n < 10 ^ Z.of_nat n) by (apply IH; intros i Hi; apply HD; lia).
    pose proof (HD (s + Z.of_nat n) ltac:(lia)) as Hd. unfold isdig in Hd. nia.
Qed.

Lemma decval_bound : forall data s p, s <= p -> (forall i, s <= i < p -> isdig (byte_at data i)) ->
  0 <= decval data s p < 10 ^ (p - s).
Proof.
  intros data s p H HD. unfold decval. pose proof (decval_n_bound data s (Z.to_nat (p - s))) as B.
  rewrite Z2Nat.id in B by lia. apply B. intros i Hi. apply HD. lia.
Qed.

Lemma decval_18 : forall data s p, s <= p -> p - s <= 18 -> (forall i, s <= i < p -> isdig (byte_at data i)) ->
  0 <= decval data s p <= 999999999999999999.
Proof.
  intros data s p H H18 HD. pose proof (decval_bound data s p H HD) as [B0 B1].
  assert (10 ^ (p - s) <= 10 ^ 18) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma decval_zeros : forall data s s2 p, s <= s2 <= p -> (forall i, s <= i < s2 -> byte_at data i = 48) ->
  decval data s p = decval data s2 p.
Proof.
  intros data s s2 p H HZ. remember (Z.to_nat (s2 - s)) as k eqn:Hk. revert s H HZ Hk.
  induction k as [|k IH]; intros s H HZ Hk.
  - assert (s2 = s) by lia. subst. reflexivity.
  - rewrite (decval_zero_head data s p) by (try lia; apply HZ; lia).
    apply IH; [lia | intros i Hi; apply HZ; lia | lia].
Qed.
