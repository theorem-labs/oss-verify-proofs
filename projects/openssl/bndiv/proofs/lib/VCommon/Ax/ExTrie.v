(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Inductive itrie (A : Type) : Type :=
| IEmpty
| ILeaf (v : A)
| INode (l r : itrie A).
Arguments IEmpty {A}.
Arguments ILeaf {A} v.
Arguments INode {A} l r.

Definition iodd (k : int) : bool := (k land 1 =? 1)%uint63.

Section Trie.
Context {A : Type}.

Fixpoint iget (d : nat) (t : itrie A) (k : int) : option A :=
  match t with
  | IEmpty => None
  | ILeaf v => match d with O => Some v | S _ => None end
  | INode l r =>
      match d with
      | O => None
      | S d' => if iodd k then iget d' r (k >> 1)%uint63 else iget d' l (k >> 1)%uint63
      end
  end.

Fixpoint iset (d : nat) (t : itrie A) (k : int) (v : A) : itrie A :=
  match d with
  | O => ILeaf v
  | S d' =>
      match t with
      | INode l r => if iodd k then INode l (iset d' r (k >> 1)%uint63 v) else INode (iset d' l (k >> 1)%uint63 v) r
      | _ => if iodd k then INode IEmpty (iset d' IEmpty (k >> 1)%uint63 v) else INode (iset d' IEmpty (k >> 1)%uint63 v) IEmpty
      end
  end.

(* [comment removed for export] *)
Fixpoint iall (f : A -> bool) (t : itrie A) : bool :=
  match t with
  | IEmpty => true
  | ILeaf v => f v
  | INode l r => iall f l && iall f r
  end.

(* [comment removed for export] *)
Fixpoint imap {B} (f : A -> B) (t : itrie A) : itrie B :=
  match t with
  | IEmpty => IEmpty
  | ILeaf v => ILeaf (f v)
  | INode l r => INode (imap f l) (imap f r)
  end.

(* [comment removed for export] *)
Fixpoint iremove (p : Z -> bool) (t : itrie A) (acc wgt : Z) : itrie A :=
  match t with
  | IEmpty => IEmpty
  | ILeaf v => if p acc then IEmpty else ILeaf v
  | INode l r => INode (iremove p l acc (2 * wgt)) (iremove p r (acc + wgt) (2 * wgt))
  end.

(* [comment removed for export] *)
Fixpoint imapo (f : Z -> A -> option A) (t : itrie A) (acc wgt : Z) : itrie A :=
  match t with
  | IEmpty => IEmpty
  | ILeaf v => match f acc v with Some v' => ILeaf v' | None => IEmpty end
  | INode l r => INode (imapo f l acc (2 * wgt)) (imapo f r (acc + wgt) (2 * wgt))
  end.

End Trie.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iodd_spec (k : int) : iodd k = (to_Z k mod 2 =? 1).
Proof.
  unfold iodd. destruct (eqbP (k land 1) 1) as [E|E]; rewrite land_spec' in E;
    change (to_Z 1%uint63) with (Z.ones 1) in E; rewrite Z.land_ones in E by lia; change (2 ^ 1) with 2 in E;
    change (Z.ones 1) with 1 in E; symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; exact E.
Qed.

Lemma phi_half (k : int) : to_Z (k >> 1)%uint63 = to_Z k / 2.
Proof. rewrite lsr_spec. reflexivity. Qed.

Lemma mod_pow2_succ (x : Z) (d : nat) : 0 <= x ->
  x mod 2 ^ Z.of_nat (S d) = 2 * ((x / 2) mod 2 ^ Z.of_nat d) + x mod 2.
Proof.
  intros Hx. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  rewrite Z.rem_mul_r by (try lia; apply Z.pow_pos_nonneg; lia). ring.
Qed.

Lemma mod_pow2_eqb_succ (x y : Z) (d : nat) : 0 <= x -> 0 <= y ->
  (x mod 2 ^ Z.of_nat (S d) =? y mod 2 ^ Z.of_nat (S d))
  = ((x mod 2 =? y mod 2) && ((x / 2) mod 2 ^ Z.of_nat d =? (y / 2) mod 2 ^ Z.of_nat d)).
Proof.
  intros Hx Hy. rewrite !mod_pow2_succ by lia.
  pose proof (Z.mod_pos_bound x 2 ltac:(lia)). pose proof (Z.mod_pos_bound y 2 ltac:(lia)).
  destruct (Z.eqb_spec (x mod 2) (y mod 2)) as [E1|E1];
  destruct (Z.eqb_spec ((x / 2) mod 2 ^ Z.of_nat d) ((y / 2) mod 2 ^ Z.of_nat d)) as [E2|E2]; cbn [andb];
    [apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | apply Z.eqb_neq; lia | apply Z.eqb_neq; lia].
Qed.

Section TrieLemmas.
Context {A : Type}.

Lemma iget_empty (d : nat) (k : int) : @iget A d IEmpty k = None.
Proof. destruct d; reflexivity. Qed.

Lemma iget_iset (d : nat) : forall (t : itrie A) (k k' : int) (v : A),
  iget d (iset d t k v) k' =
  if (to_Z k mod 2 ^ Z.of_nat d =? to_Z k' mod 2 ^ Z.of_nat d) then Some v else iget d t k'.
Proof.
  induction d as [|d IH]; intros t k k' v.
  - cbn [Z.of_nat Z.pow]. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. cbn. reflexivity.
  - pose proof (to_Z_bounded k) as Hk. pose proof (to_Z_bounded k') as Hk'.
    rewrite mod_pow2_eqb_succ by lia. rewrite <- !phi_half.
    assert (Hodd : forall x y : int, (to_Z x mod 2 =? to_Z y mod 2) = Bool.eqb (iodd x) (iodd y)).
    { intros x y. rewrite !iodd_spec. pose proof (Z.mod_pos_bound (to_Z x) 2 ltac:(lia)).
      pose proof (Z.mod_pos_bound (to_Z y) 2 ltac:(lia)).
      destruct (Z.eqb_spec (to_Z x mod 2) (to_Z y mod 2)), (Z.eqb_spec (to_Z x mod 2) 1), (Z.eqb_spec (to_Z y mod 2) 1);
        cbn; try reflexivity; lia. }
    rewrite Hodd.
    destruct t as [| w | l r]; cbn [iset iget].
    + destruct (iodd k) eqn:Ek, (iodd k') eqn:Ek'; cbn [iget Bool.eqb andb]; rewrite ?IH, ?iget_empty;
        try (destruct (_ =? _)); reflexivity.
    + destruct (iodd k) eqn:Ek, (iodd k') eqn:Ek'; cbn [iget Bool.eqb andb]; rewrite ?IH, ?iget_empty;
        try (destruct (_ =? _)); reflexivity.
    + destruct (iodd k) eqn:Ek, (iodd k') eqn:Ek'; cbn [iget Bool.eqb andb]; rewrite ?IH; reflexivity.
Qed.

Lemma iget_iset_same (d : nat) (t : itrie A) (k : int) (v : A) : iget d (iset d t k v) k = Some v.
Proof. rewrite iget_iset. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma iall_iget (f : A -> bool) (d : nat) : forall (t : itrie A) (k : int) (v : A),
  iall f t = true -> iget d t k = Some v -> f v = true.
Proof.
  induction d as [|d IH]; intros t k v Ha Hg; destruct t as [| w | l r]; cbn [iget iall] in *; try discriminate.
  - injection Hg as <-. exact Ha.
  - apply andb_prop in Ha as [Hl Hr]. destruct (iodd k); eauto.
Qed.

Lemma iget_imap {B} (f : A -> B) (d : nat) : forall (t : itrie A) (k : int),
  iget d (imap f t) k = option_map f (iget d t k).
Proof.
  induction d as [|d IH]; intros t k; destruct t as [| w | l r]; cbn [iget imap]; try reflexivity.
  destruct (iodd k); apply IH.
Qed.

Lemma iget_iremove (p : Z -> bool) (d : nat) : forall (t : itrie A) (acc wgt : Z) (k : int),
  iget d (iremove p t acc wgt) k =
  match iget d t k with
  | Some v => if p (acc + wgt * (to_Z k mod 2 ^ Z.of_nat d)) then None else Some v
  | None => None
  end.
Proof.
  induction d as [|d IH]; intros t acc wgt k; destruct t as [| w | l r]; cbn [iget iremove]; try reflexivity.
  - change (2 ^ Z.of_nat 0) with 1. rewrite Z.mod_1_r, Z.mul_0_r, Z.add_0_r. destruct (p acc); reflexivity.
  - destruct (p acc); reflexivity.
  - pose proof (to_Z_bounded k) as Hk. rewrite mod_pow2_succ by lia. rewrite <- phi_half.
    pose proof (Z.mod_pos_bound (to_Z k) 2 ltac:(lia)).
    destruct (iodd k) eqn:Eo; rewrite iodd_spec in Eo.
    + apply Z.eqb_eq in Eo. rewrite IH. rewrite Eo. destruct (iget d r (k >> 1)%uint63); [|reflexivity].
      replace (acc + wgt + 2 * wgt * (to_Z (k >> 1)%uint63 mod 2 ^ Z.of_nat d))
        with (acc + wgt * (2 * (to_Z (k >> 1)%uint63 mod 2 ^ Z.of_nat d) + 1)) by ring. reflexivity.
    + apply Z.eqb_neq in Eo. rewrite IH. replace (to_Z k mod 2) with 0 by lia. destruct (iget d l (k >> 1)%uint63); [|reflexivity].
      replace (acc + 2 * wgt * (to_Z (k >> 1)%uint63 mod 2 ^ Z.of_nat d))
        with (acc + wgt * (2 * (to_Z (k >> 1)%uint63 mod 2 ^ Z.of_nat d) + 0)) by ring. reflexivity.
Qed.

Lemma iget_imapo (f : Z -> A -> option A) (d : nat) : forall (t : itrie A) (acc wgt : Z) (k : int),
  iget d (imapo f t acc wgt) k =
  match iget d t k with
  | Some v => f (acc + wgt * (to_Z k mod 2 ^ Z.of_nat d)) v
  | None => None
  end.
Proof.
  induction d as [|d IH]; intros t acc wgt k; destruct t as [| w | l r]; cbn [iget imapo]; try reflexivity.
  - change (2 ^ Z.of_nat 0) with 1. rewrite Z.mod_1_r, Z.mul_0_r, Z.add_0_r. destruct (f acc w); reflexivity.
  - destruct (f acc w); reflexivity.
  - pose proof (to_Z_bounded k) as Hk. rewrite mod_pow2_succ by lia. rewrite <- phi_half.
    pose proof (Z.mod_pos_bound (to_Z k) 2 ltac:(lia)).
    destruct (iodd k) eqn:Eo; rewrite iodd_spec in Eo.
    + apply Z.eqb_eq in Eo. rewrite IH. rewrite Eo. destruct (iget d r (k >> 1)%uint63); [|reflexivity].
      replace (acc + wgt + 2 * wgt * (to_Z (k >> 1)%uint63 mod 2 ^ Z.of_nat d))
        with (acc + wgt * (2 * (to_Z (k >> 1)%uint63 mod 2 ^ Z.of_nat d) + 1)) by ring. reflexivity.
    + apply Z.eqb_neq in Eo. rewrite IH. replace (to_Z k mod 2) with 0 by lia. destruct (iget d l (k >> 1)%uint63); [|reflexivity].
      replace (acc + 2 * wgt * (to_Z (k >> 1)%uint63 mod 2 ^ Z.of_nat d))
        with (acc + wgt * (2 * (to_Z (k >> 1)%uint63 mod 2 ^ Z.of_nat d) + 0)) by ring. reflexivity.
Qed.

End TrieLemmas.
