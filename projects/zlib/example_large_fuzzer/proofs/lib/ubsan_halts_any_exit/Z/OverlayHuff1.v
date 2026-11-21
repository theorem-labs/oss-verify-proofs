(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Fixpoint lsum (f : Z -> Z) (l : list Z) : Z :=
  match l with [] => 0 | x :: r => f x + lsum f r end.

Lemma lsum_app f l1 l2 : lsum f (l1 ++ l2) = lsum f l1 + lsum f l2.
Proof. induction l1; cbn; lia. Qed.

Lemma lsum_ext f g l : (forall x, In x l -> f x = g x) -> lsum f l = lsum g l.
Proof.
  induction l as [|x r IH]; cbn; intros H; [reflexivity|].
  rewrite (H x) by (left; reflexivity). rewrite IH by (intros; apply H; right; assumption). reflexivity.
Qed.

Lemma lsum_le f g l : (forall x, In x l -> f x <= g x) -> lsum f l <= lsum g l.
Proof.
  induction l as [|x r IH]; cbn; intros H; [lia|].
  pose proof (H x (or_introl eq_refl)). specialize (IH ltac:(intros; apply H; right; assumption)). lia.
Qed.

Lemma lsum_zero l : lsum (fun _ => 0) l = 0.
Proof. induction l; cbn; lia. Qed.

Lemma lsum_nonneg f l : (forall x, In x l -> 0 <= f x) -> 0 <= lsum f l.
Proof. intros H. pose proof (lsum_le (fun _ => 0) f l H). rewrite lsum_zero in H0. exact H0. Qed.

Lemma lsum_add f g l : lsum (fun x => f x + g x) l = lsum f l + lsum g l.
Proof. induction l; cbn; lia. Qed.

Lemma lsum_scale c f l : lsum (fun x => c * f x) l = c * lsum f l.
Proof. induction l; cbn; lia. Qed.

Lemma lsum_in_split (l : list Z) (x : Z) : In x l -> NoDup l ->
  exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l1 /\ ~ In x l2.
Proof.
  intros I ND. destruct (in_split x l I) as (l1 & l2 & E). subst l.
  pose proof (NoDup_remove_2 _ _ _ ND) as A. exists l1, l2. split; [reflexivity|].
  split; intros C; [apply A, in_or_app; left; exact C | apply A, in_or_app; right; exact C].
Qed.


Lemma lsum_ge_member f l x : (forall y, In y l -> 0 <= f y) -> In x l -> f x <= lsum f l.
Proof.
  intros P I. induction l as [|y r IH]; [destruct I|]. cbn. destruct I as [->|I].
  - pose proof (lsum_nonneg f r ltac:(intros; apply P; right; assumption)). lia.
  - specialize (IH ltac:(intros; apply P; right; assumption) I). pose proof (P y (or_introl eq_refl)). lia.
Qed.




Section Kraft.
Variable K : Z.
Hypothesis Kpos : 0 <= K.

Definition ksum (sg : Z -> Z) (F : list Z) : Z := lsum (fun x => 2 ^ (K - sg x)) F.
Definition csum (w sg : Z -> Z) (F : list Z) : Z := lsum (fun x => w x * sg x) F.

Definition code_ok (sg : Z -> Z) (F : list Z) : Prop :=
  (forall x, In x F -> 0 <= sg x <= K) /\ ksum sg F <= 2 ^ K.


Fixpoint lmax (sg : Z -> Z) (F : list Z) : Z :=
  match F with [] => 0 | x :: r => Z.max (sg x) (lmax sg r) end.

Lemma lmax_ge sg F x : In x F -> sg x <= lmax sg F.
Proof. induction F as [|y r IH]; cbn; [tauto|]. intros [->|I]; [lia|]. specialize (IH I). lia. Qed.

Lemma lmax_in sg F : F <> [] -> (forall x, In x F -> 0 <= sg x) -> exists x, In x F /\ sg x = lmax sg F.
Proof.
  induction F as [|y r IH]; [congruence|]. intros _ NN. cbn.
  destruct r as [|z r'].
  - exists y. cbn. pose proof (NN y (or_introl eq_refl)). split; [tauto|lia].
  - destruct (IH ltac:(congruence) ltac:(intros; apply NN; right; assumption)) as (x & I & E).
    destruct (Z_le_gt_dec (sg y) (lmax sg (z :: r'))).
    + exists x. split; [right; exact I|]. rewrite E. lia.
    + exists y. split; [left; reflexivity|lia].
Qed.

Definition cnt (sg : Z -> Z) (v : Z) (F : list Z) : Z := lsum (fun x => if sg x =? v then 1 else 0) F.

Lemma cnt_nonneg sg v F : 0 <= cnt sg v F.
Proof. unfold cnt. apply lsum_nonneg. intros. destruct (_ =? _); lia. Qed.



Definition upd (sg : Z -> Z) (x v : Z) : Z -> Z := fun y => if y =? x then v else sg y.



End Kraft.
