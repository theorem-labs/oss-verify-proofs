(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive ptrie : Type :=
  | PTleaf : ptrie
  | PTnode : ptrie -> option Z -> ptrie -> ptrie.

Fixpoint pget (t : ptrie) (p : positive) {struct p} : option Z :=
  match t with
  | PTleaf => None
  | PTnode l o r =>
      match p with
      | xH => o
      | xO q => pget l q
      | xI q => pget r q
      end
  end.

Fixpoint pset (t : ptrie) (p : positive) (v : Z) {struct p} : ptrie :=
  match t with
  | PTleaf =>
      match p with
      | xH => PTnode PTleaf (Some v) PTleaf
      | xO q => PTnode (pset PTleaf q v) None PTleaf
      | xI q => PTnode PTleaf None (pset PTleaf q v)
      end
  | PTnode l o r =>
      match p with
      | xH => PTnode l (Some v) r
      | xO q => PTnode (pset l q v) o r
      | xI q => PTnode l o (pset r q v)
      end
  end.

Lemma pget_leaf : forall p, pget PTleaf p = None.
Proof. destruct p; reflexivity. Qed.

Lemma pget_pset_same : forall p t v, pget (pset t p v) p = Some v.
Proof.
  induction p as [p IH|p IH|]; intros t v; destruct t; cbn; try reflexivity; apply IH.
Qed.

Lemma pget_pset_other : forall p q t v, p <> q -> pget (pset t q v) p = pget t p.
Proof.
  induction p as [p IH|p IH|]; intros q t v H; destruct t, q; cbn; try reflexivity;
    try (rewrite IH by congruence); try rewrite pget_leaf; try reflexivity; try congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pos_of_Z (i : Z) : positive :=
  match i with
  | Z0 => xH
  | Zpos p => xO p
  | Zneg p => xI p
  end.

Lemma pos_of_Z_inj : forall i j, pos_of_Z i = pos_of_Z j -> i = j.
Proof. intros [|p|p] [|q|q] H; cbn in H; congruence. Qed.

Definition zarr : Type := ptrie.
Definition znew : zarr := PTleaf.
Definition zget (a : zarr) (i : Z) : Z :=
  match pget a (pos_of_Z i) with Some v => v | None => 0 end.
Definition zset (a : zarr) (i v : Z) : zarr := pset a (pos_of_Z i) v.

Lemma zget_znew : forall i, zget znew i = 0.
Proof. intros i. unfold zget, znew. rewrite pget_leaf. reflexivity. Qed.

Lemma zget_zset_same : forall a i v, zget (zset a i v) i = v.
Proof. intros. unfold zget, zset. rewrite pget_pset_same. reflexivity. Qed.

Lemma zget_zset_other : forall a i v j, j <> i -> zget (zset a i v) j = zget a j.
Proof.
  intros a i v j H. unfold zget, zset. rewrite pget_pset_other; [reflexivity|].
  intros E. apply H. apply pos_of_Z_inj. exact E.
Qed.

Lemma zget_zset : forall a i v j, zget (zset a i v) j = (if j =? i then v else zget a j).
Proof.
  intros. destruct (Z.eqb_spec j i) as [->|H]; [apply zget_zset_same | apply zget_zset_other; exact H].
Qed.

(* [comment removed for export] *)
Definition zincr (a : zarr) (i : Z) : zarr := zset a i (zget a i + 1).
Lemma zget_zincr : forall a i j, zget (zincr a i) j = (if j =? i then zget a i + 1 else zget a j).
Proof. intros. unfold zincr. apply zget_zset. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zarr_to_list (a : zarr) (lo : Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => zget a lo :: zarr_to_list a (lo + 1) n'
  end.

Fixpoint zarr_of_list_at (a : zarr) (lo : Z) (l : list Z) : zarr :=
  match l with
  | [] => a
  | x :: l' => zarr_of_list_at (zset a lo x) (lo + 1) l'
  end.
Definition zarr_of_list (l : list Z) : zarr := zarr_of_list_at znew 0 l.

Lemma zarr_to_list_length : forall a lo n, length (zarr_to_list a lo n) = n.
Proof. intros a lo n. revert lo. induction n; intros; cbn; [reflexivity| now rewrite IHn]. Qed.

Lemma zarr_to_list_nth : forall a lo n k, (k < n)%nat ->
  nth_error (zarr_to_list a lo n) k = Some (zget a (lo + Z.of_nat k)).
Proof.
  intros a lo n. revert lo. induction n as [|n IH]; intros lo k Hk; [lia|].
  destruct k as [|k]; cbn; [f_equal; f_equal; lia|].
  rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma zget_of_list_at_below : forall l a lo j, j < lo -> zget (zarr_of_list_at a lo l) j = zget a j.
Proof.
  induction l as [|x l IH]; intros a lo j Hj; cbn; [reflexivity|].
  rewrite IH by lia. apply zget_zset_other. lia.
Qed.

Lemma zget_of_list_at : forall l a lo k, (k < length l)%nat ->
  zget (zarr_of_list_at a lo l) (lo + Z.of_nat k) = nth k l 0.
Proof.
  induction l as [|x l IH]; intros a lo k Hk; cbn in Hk; [lia|].
  cbn [zarr_of_list_at]. destruct k as [|k].
  - cbn [nth]. rewrite zget_of_list_at_below by lia. rewrite Z.add_0_r. apply zget_zset_same.
  - cbn [nth]. replace (lo + Z.of_nat (S k)) with (lo + 1 + Z.of_nat k) by lia. apply IH. lia.
Qed.

Lemma zget_of_list : forall l k, (k < length l)%nat -> zget (zarr_of_list l) (Z.of_nat k) = nth k l 0.
Proof. intros. unfold zarr_of_list. rewrite <- (Z.add_0_l (Z.of_nat k)). apply zget_of_list_at. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
