(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith PArith List Lia Bool Arith FunctionalExtensionality.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Module CXNAT.

Fixpoint eqbF (a b : nat) {struct a} : bool :=
  match a, b with
  | S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (a')))))))))))))))), S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (b')))))))))))))))) => eqbF a' b'
  | _, _ => Nat.eqb a b
  end.
Fixpoint lebF (a b : nat) {struct a} : bool :=
  match a, b with
  | S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (a')))))))))))))))), S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (b')))))))))))))))) => lebF a' b'
  | _, _ => Nat.leb a b
  end.
Definition ltbF (a b : nat) : bool := lebF (S a) b.
Fixpoint compareF (a b : nat) {struct a} : comparison :=
  match a, b with
  | S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (a')))))))))))))))), S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (b')))))))))))))))) => compareF a' b'
  | _, _ => Nat.compare a b
  end.
Fixpoint nthF {A : Type} (n : nat) (l : list A) (d : A) {struct n} : A :=
  match n, l with
  | S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (n')))))))))))))))), _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: l' => nthF n' l' d
  | _, _ => nth n l d
  end.
Fixpoint osnF (n : nat) (acc : positive) {struct n} : positive :=
  match n with
  | S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (n')))))))))))))))))))))))))))))))) => osnF n' (Pos.add acc 32)
  | S n' => osnF n' (Pos.succ acc)
  | O => acc
  end.
Definition of_succ_natF (n : nat) : positive := osnF n 1%positive.

Ltac peel_a k := do k (match goal with a : nat |- _ => destruct a as [|a]; [reflexivity|] end).
Lemma eqbF_eq : forall a b, eqbF a b = Nat.eqb a b.
Proof.
  induction a as [a IH] using lt_wf_ind. intros b.
  do 16 (destruct a as [|a]; [reflexivity|]). do 16 (destruct b as [|b]; [reflexivity|]).
  cbn [eqbF Nat.eqb]. apply IH. lia.
Qed.
Lemma lebF_eq : forall a b, lebF a b = Nat.leb a b.
Proof.
  induction a as [a IH] using lt_wf_ind. intros b.
  do 16 (destruct a as [|a]; [reflexivity|]). do 16 (destruct b as [|b]; [reflexivity|]).
  cbn [lebF Nat.leb]. apply IH. lia.
Qed.
Lemma compareF_eq : forall a b, compareF a b = Nat.compare a b.
Proof.
  induction a as [a IH] using lt_wf_ind. intros b.
  do 16 (destruct a as [|a]; [reflexivity|]). do 16 (destruct b as [|b]; [reflexivity|]).
  cbn [compareF Nat.compare]. apply IH. lia.
Qed.
Lemma nthF_eq : forall (A : Type) n (l : list A) d, nthF n l d = nth n l d.
Proof.
  intros A. induction n as [n IH] using lt_wf_ind. intros l d.
  do 16 (destruct n as [|n]; [reflexivity|]). do 16 (destruct l as [|? l]; [reflexivity|]).
  cbn [nthF nth]. apply IH. lia.
Qed.
Lemma osnF_eq : forall n acc, Zpos (osnF n acc) = (Zpos acc + Z.of_nat n)%Z.
Proof.
  induction n as [n IH] using lt_wf_ind. intros acc.
  do 32 (destruct n as [|n]; [cbn [osnF]; lia|]).
  cbn [osnF]. rewrite IH by lia. lia.
Qed.
Lemma of_succ_natF_eq : forall n, of_succ_natF n = Pos.of_succ_nat n.
Proof.
  intros n. unfold of_succ_natF. apply Pos2Z.inj. rewrite osnF_eq. rewrite Zpos_P_of_succ_nat. lia.
Qed.

(* [comment removed for export] *)
Lemma eqbF_eqf : eqbF = Nat.eqb.
Proof. apply functional_extensionality; intros a. apply functional_extensionality; intros b. apply eqbF_eq. Qed.
Lemma lebF_eqf : lebF = Nat.leb.
Proof. apply functional_extensionality; intros a. apply functional_extensionality; intros b. apply lebF_eq. Qed.
Lemma ltbF_eqf : ltbF = Nat.ltb.
Proof. apply functional_extensionality; intros a. apply functional_extensionality; intros b. unfold ltbF, Nat.ltb. apply lebF_eq. Qed.
Lemma compareF_eqf : compareF = Nat.compare.
Proof. apply functional_extensionality; intros a. apply functional_extensionality; intros b. apply compareF_eq. Qed.
Lemma nthF_eqf : @nthF = @nth.
Proof. apply functional_extensionality_dep; intros A. apply functional_extensionality; intros n. apply functional_extensionality; intros l. apply functional_extensionality; intros d. apply nthF_eq. Qed.
Lemma of_succ_natF_eqf : of_succ_natF = Pos.of_succ_nat.
Proof. apply functional_extensionality; intros n. apply of_succ_natF_eq. Qed.
End CXNAT.
