(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import Bool List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Notation "a &&& b" := (if a then b else false) (at level 40, left associativity, only parsing) : bool_scope.
Notation "a ||| b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.

Lemma land_eq (a b : bool) : (a &&& b) = (a && b).
Proof. reflexivity. Qed.

Lemma land_true (a b : bool) : (a &&& b) = true -> a = true /\ b = true.
Proof. destruct a; [intros H; split; [reflexivity | exact H] | discriminate]. Qed.

Lemma land_intro (a b : bool) : a = true -> b = true -> (a &&& b) = true.
Proof. intros -> ->. reflexivity. Qed.

Lemma lor_true (a b : bool) : (a ||| b) = true -> a = true \/ b = true.
Proof. destruct a; [left; reflexivity | right; assumption]. Qed.

Lemma lor_false (a b : bool) : (a ||| b) = false -> a = false /\ b = false.
Proof. destruct a; [discriminate | intros H; split; [reflexivity | exact H]]. Qed.

Fixpoint lexists {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: r => if f x then true else lexists f r
  end.

Fixpoint lforall {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: r => if f x then lforall f r else false
  end.

Lemma lexists_eq {A : Type} (f : A -> bool) (l : list A) : lexists f l = existsb f l.
Proof. induction l as [|x r IH]; [reflexivity|]. cbn [lexists existsb]. rewrite IH. destruct (f x); reflexivity. Qed.

Lemma lforall_eq {A : Type} (f : A -> bool) (l : list A) : lforall f l = forallb f l.
Proof. induction l as [|x r IH]; [reflexivity|]. cbn [lforall forallb]. rewrite IH. destruct (f x); reflexivity. Qed.

Lemma lexists_exists {A : Type} (f : A -> bool) (l : list A) : lexists f l = true -> exists x, In x l /\ f x = true.
Proof. rewrite lexists_eq. apply existsb_exists. Qed.

Lemma lforall_forall {A : Type} (f : A -> bool) (l : list A) : lforall f l = true -> forall x, In x l -> f x = true.
Proof. rewrite lforall_eq. apply forallb_forall. Qed.

Lemma lforall_intro {A : Type} (f : A -> bool) (l : list A) : (forall x, In x l -> f x = true) -> lforall f l = true.
Proof. intros H. rewrite lforall_eq. apply forallb_forall. exact H. Qed.

