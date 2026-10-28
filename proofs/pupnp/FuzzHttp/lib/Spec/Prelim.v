(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition u8  (x : Z) : Z := x mod 2^8.
Definition u16 (x : Z) : Z := x mod 2^16.
Definition u32 (x : Z) : Z := x mod 2^32.
Definition u64 (x : Z) : Z := x mod 2^64.

Definition s32 (x : Z) : Z := (x + 2^31) mod 2^32 - 2^31.
Definition s64 (x : Z) : Z := (x + 2^63) mod 2^64 - 2^63.

Definition zlength {A} (l : list A) : Z := Z.of_nat (length l).

Definition znth (l : list Z) (i : Z) : Z :=
  if i <? 0 then 0 else nth (Z.to_nat i) l 0.

Fixpoint upd_nat (l : list Z) (i : nat) (v : Z) : list Z :=
  match l, i with
  | [], _ => []
  | _ :: t, O => v :: t
  | h :: t, S i' => h :: upd_nat t i' v
  end.

Definition zupd (l : list Z) (i : Z) (v : Z) : list Z :=
  if i <? 0 then l else upd_nat l (Z.to_nat i) v.

Lemma upd_nat_length : forall l i v, length (upd_nat l i v) = length l.
Proof. induction l; intros [|i] v; cbn; auto. Qed.

Lemma zupd_length : forall l i v, length (zupd l i v) = length l.
Proof. intros. unfold zupd. destruct (i <? 0); auto using upd_nat_length. Qed.

Lemma zlength_zupd : forall l i v, zlength (zupd l i v) = zlength l.
Proof. intros. unfold zlength. rewrite zupd_length. reflexivity. Qed.

Lemma nth_upd_nat_same : forall l i v, (i < length l)%nat -> nth i (upd_nat l i v) 0 = v.
Proof. induction l; intros [|i] v H; cbn in *; try lia; auto. apply IHl. lia. Qed.

Lemma nth_upd_nat_other : forall l i j v, i <> j -> nth j (upd_nat l i v) 0 = nth j l 0.
Proof. induction l; intros [|i] [|j] v H; cbn; auto; try congruence. Qed.

Lemma znth_zupd_eq : forall l i v, 0 <= i < zlength l -> znth (zupd l i v) i = v.
Proof.
  intros l i v H. unfold znth, zupd, zlength in *.
  destruct (Z.ltb_spec i 0); [lia|]. apply nth_upd_nat_same. lia.
Qed.

Lemma znth_zupd_neq : forall l i j v, i <> j -> znth (zupd l i v) j = znth l j.
Proof.
  intros l i j v H. unfold znth, zupd.
  destruct (Z.ltb_spec j 0); [reflexivity|]. destruct (Z.ltb_spec i 0); [reflexivity|].
  apply nth_upd_nat_other. intros E. apply H. lia.
Qed.

Lemma znth_range : forall l i, 0 <= i < zlength l -> In (znth l i) l.
Proof.
  intros l i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [lia|].
  apply nth_In. lia.
Qed.

Definition zrepeat (v : Z) (n : Z) : list Z := repeat v (Z.to_nat n).
Lemma zlength_zrepeat : forall v n, 0 <= n -> zlength (zrepeat v n) = n.
Proof. intros. unfold zlength, zrepeat. rewrite repeat_length. lia. Qed.
