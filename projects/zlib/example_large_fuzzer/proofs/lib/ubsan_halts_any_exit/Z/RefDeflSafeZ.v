(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Fixpoint zsum (f : Z -> Z) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S k => zsum f lo k + f (lo + Z.of_nat k)
  end.

Definition zind (b : bool) : Z := if b then 1 else 0.

Lemma zind_le1 : forall b, 0 <= zind b <= 1.
Proof. intros [|]; cbn; lia. Qed.

Lemma zsum_ext : forall f g lo n, (forall i, lo <= i < lo + Z.of_nat n -> f i = g i) -> zsum f lo n = zsum g lo n.
Proof.
  induction n as [|n IH]; intros Hfg; cbn [zsum]; [reflexivity|].
  rewrite IH by (intros; apply Hfg; lia). rewrite Hfg by lia. reflexivity.
Qed.

Lemma zsum_add : forall f g lo n, zsum (fun i => f i + g i) lo n = zsum f lo n + zsum g lo n.
Proof. induction n as [|n IH]; cbn [zsum]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma zsum_scale : forall c f lo n, zsum (fun i => c * f i) lo n = c * zsum f lo n.
Proof. induction n as [|n IH]; cbn [zsum]; [lia|]. rewrite IH. lia. Qed.

Lemma zsum_0 : forall f lo n, (forall i, lo <= i < lo + Z.of_nat n -> f i = 0) -> zsum f lo n = 0.
Proof. induction n as [|n IH]; intros H; cbn [zsum]; [reflexivity|]. rewrite IH by (intros; apply H; lia). rewrite H by lia. lia. Qed.

Lemma zsum_nonneg : forall f lo n, (forall i, lo <= i < lo + Z.of_nat n -> 0 <= f i) -> 0 <= zsum f lo n.
Proof. induction n as [|n IH]; intros H; cbn [zsum]; [lia|]. pose proof (IH ltac:(intros; apply H; lia)). pose proof (H (lo + Z.of_nat n) ltac:(lia)). lia. Qed.

Lemma zsum_mono : forall f g lo n, (forall i, lo <= i < lo + Z.of_nat n -> f i <= g i) -> zsum f lo n <= zsum g lo n.
Proof. induction n as [|n IH]; intros H; cbn [zsum]; [lia|]. pose proof (IH ltac:(intros; apply H; lia)). pose proof (H (lo + Z.of_nat n) ltac:(lia)). lia. Qed.

Lemma zsum_single : forall f lo n a, lo <= a < lo + Z.of_nat n ->
  (forall i, lo <= i < lo + Z.of_nat n -> i <> a -> f i = 0) -> zsum f lo n = f a.
Proof.
  induction n as [|n IH]; intros a Ha H; cbn [zsum]; [lia|].
  destruct (Z.eq_dec a (lo + Z.of_nat n)) as [->|N].
  - rewrite zsum_0 by (intros; apply H; lia). lia.
  - rewrite (IH a) by (try lia; intros; apply H; lia). rewrite (H (lo + Z.of_nat n)) by lia. lia.
Qed.

Lemma zsum_two : forall f lo n a b, lo <= a < lo + Z.of_nat n -> lo <= b < lo + Z.of_nat n -> a <> b ->
  (forall i, lo <= i < lo + Z.of_nat n -> i <> a -> i <> b -> f i = 0) -> zsum f lo n = f a + f b.
Proof.
  induction n as [|n IH]; intros a b Ha Hb Nab H; cbn [zsum]; [lia|].
  destruct (Z.eq_dec a (lo + Z.of_nat n)) as [->|Na].
  - rewrite (zsum_single f lo n b) by (try lia; intros; apply H; lia). lia.
  - destruct (Z.eq_dec b (lo + Z.of_nat n)) as [->|Nb].
    + rewrite (zsum_single f lo n a) by (try lia; intros; apply H; lia). lia.
    + rewrite (IH a b) by (try lia; intros; apply H; lia). rewrite (H (lo + Z.of_nat n)) by lia. lia.
Qed.

Lemma zsum_ind_ge1 : forall (P : Z -> bool) lo n a, lo <= a < lo + Z.of_nat n -> P a = true ->
  1 <= zsum (fun i => zind (P i)) lo n.
Proof.
  induction n as [|k IHk]; cbn [zsum]; intros a Ha Ea; [lia|].
  pose proof (zsum_nonneg (fun i => zind (P i)) lo k ltac:(intros i0 Hi0; pose proof (zind_le1 (P i0)); lia)).
  destruct (Z.eq_dec a (lo + Z.of_nat k)) as [->|N]; [rewrite Ea; change (zind true) with 1; lia|].
  pose proof (IHk a ltac:(lia) Ea). pose proof (zind_le1 (P (lo + Z.of_nat k))). lia.
Qed.

Lemma zsum_pos_has : forall (P : Z -> bool) lo n, 0 < zsum (fun i => zind (P i)) lo n ->
  exists a, lo <= a < lo + Z.of_nat n /\ P a = true /\ (forall i, lo <= i < a -> P i = false).
Proof.
  induction n as [|n IH]; cbn [zsum]; intros H; [lia|].
  destruct (Z_lt_le_dec 0 (zsum (fun i => zind (P i)) lo n)) as [C|C].
  - destruct (IH C) as (a & A & B & D). exists a. split; [lia|]. split; [exact B | exact D].
  - pose proof (zsum_nonneg (fun i => zind (P i)) lo n ltac:(intros i0 Hi0; pose proof (zind_le1 (P i0)); lia)).
    destruct (P (lo + Z.of_nat n)) eqn:E; [| try rewrite E in H; change (zind false) with 0 in H; lia].
    exists (lo + Z.of_nat n). split; [lia|]. split; [exact E|].
    intros i Hi. destruct (P i) eqn:Ei; [|reflexivity]. exfalso.
    pose proof (zsum_ind_ge1 P lo n i ltac:(lia) Ei). lia.
Qed.



Lemma zsum_snoc : forall f lo n, zsum f lo (S n) = zsum f lo n + f (lo + Z.of_nat n).
Proof. reflexivity. Qed.

Lemma zsum_shift : forall f lo n, zsum f lo (S n) = f lo + zsum f (lo + 1) n.
Proof.
  intros f lo n. induction n as [|n IHn].
  - cbn [zsum Z.of_nat]. rewrite Z.add_0_r. lia.
  - rewrite zsum_snoc, IHn, zsum_snoc. replace (lo + Z.of_nat (S n)) with (lo + 1 + Z.of_nat n) by lia. lia.
Qed.

Lemma zsum_swap : forall (F : Z -> Z -> Z) lo n lo' m,
  zsum (fun b => zsum (F b) lo n) lo' m = zsum (fun p => zsum (fun b => F b p) lo' m) lo n.
Proof.
  intros F lo n lo'. induction m as [|m IH].
  - cbn [zsum]. symmetry. apply zsum_0. intros; reflexivity.
  - rewrite zsum_snoc. rewrite IH. rewrite <- zsum_add. apply zsum_ext. intros; reflexivity.
Qed.

Lemma zsum_split : forall f lo n m, zsum f lo (n + m) = zsum f lo n + zsum f (lo + Z.of_nat n) m.
Proof.
  intros f lo n m. induction m as [|m IH].
  - rewrite Nat.add_0_r. cbn [zsum]. lia.
  - rewrite Nat.add_succ_r. rewrite !zsum_snoc, IH. replace (lo + Z.of_nat (n + m)) with (lo + Z.of_nat n + Z.of_nat m) by lia. lia.
Qed.

Lemma zsum_ge_point : forall f lo n a, (forall i, lo <= i < lo + Z.of_nat n -> 0 <= f i) -> lo <= a < lo + Z.of_nat n ->
  f a <= zsum f lo n.
Proof.
  intros f lo n a Hnn Ha.
  assert (E1 : zsum (fun i => if i =? a then f i else 0) lo n = f a).
  { rewrite (zsum_single (fun i => if i =? a then f i else 0) lo n a); [| exact Ha | intros i Hi Ni; replace (i =? a) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity].
    rewrite Z.eqb_refl. reflexivity. }
  rewrite <- E1. apply zsum_mono. intros i Hi. destruct (Z.eqb_spec i a) as [->|]; [lia | apply Hnn; exact Hi].
Qed.

Lemma zsum_const1 : forall n lo, zsum (fun _ => 1) lo n = Z.of_nat n.
Proof. induction n as [|n IH]; intros lo; [reflexivity|]. rewrite zsum_snoc, IH. lia. Qed.
