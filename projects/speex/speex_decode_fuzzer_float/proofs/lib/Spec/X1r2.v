(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.

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

Definition ztake (n : Z) (l : list Z) : list Z := firstn (Z.to_nat n) l.
Definition zdrop (n : Z) (l : list Z) : list Z := skipn (Z.to_nat n) l.

Definition zslice (off len : Z) (l : list Z) : list Z := ztake len (zdrop off l).

Lemma zlength_app : forall (l1 l2 : list Z), zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_ztake : forall n l, 0 <= n <= zlength l -> zlength (ztake n l) = n.
Proof. intros. unfold zlength, ztake in *. rewrite length_firstn. lia. Qed.
Lemma zlength_ztake_le : forall n l, zlength (ztake n l) <= zlength l.
Proof. intros. unfold zlength, ztake. rewrite length_firstn. lia. Qed.
Lemma zlength_ztake_le_n : forall n l, 0 <= n -> zlength (ztake n l) <= n.
Proof. intros. unfold zlength, ztake. rewrite length_firstn. lia. Qed.
Lemma zlength_zdrop : forall n l, 0 <= n <= zlength l -> zlength (zdrop n l) = zlength l - n.
Proof. intros. unfold zlength, zdrop in *. rewrite length_skipn. lia. Qed.
Lemma zlength_zslice : forall off len l,
0 <= off -> 0 <= len -> off + len <= zlength l -> zlength (zslice off len l) = len.
Proof. intros. unfold zslice. apply zlength_ztake. rewrite zlength_zdrop; lia. Qed.
Lemma zlength_nil : zlength (@nil Z) = 0.
Proof. reflexivity. Qed.
Lemma zlength_cons : forall (x : Z) l, zlength (x :: l) = zlength l + 1.
Proof. intros. unfold zlength. cbn [length]. lia. Qed.
Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Fixpoint zsum (l : list Z) : Z := match l with [] => 0 | x :: l' => x + zsum l' end.
Lemma zsum_app : forall l1 l2, zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof. induction l1; intros; cbn; [lia|]. rewrite IHl1. lia. Qed.
Lemma zsum_nonneg : forall l, Forall (fun x => 0 <= x) l -> 0 <= zsum l.
Proof. induction 1; cbn; lia. Qed.

Fixpoint le_val (bs : list Z) : Z := match bs with [] => 0 | b :: bs' => b + 256 * le_val bs' end.
Lemma le_val_bound : forall bs, Forall (fun b => 0 <= b < 256) bs -> 0 <= le_val bs < 256 ^ zlength bs.
Proof.
induction 1 as [|b bs Hb H IH]; cbn [le_val]; [cbn; lia|].
rewrite zlength_cons, Z.pow_add_r, Z.pow_1_r; [nia| apply zlength_nonneg| lia].
Qed.

Definition le32_at (l : list Z) (i : Z) : Z := le_val (zslice i 4 l).
Definition le64_at (l : list Z) (i : Z) : Z := le_val (zslice i 8 l).

From Stdlib Require Import Strings.String Strings.Ascii.
Definition str_bytes (s : string) : list Z :=
map (fun a => Z.of_N (N_of_ascii a)) (list_ascii_of_string s).

Fixpoint list_eqb (l1 l2 : list Z) : bool :=
match l1, l2 with
| [], [] => true
| x :: l1', y :: l2' => (x =? y) && list_eqb l1' l2'
| _, _ => false
end.
Lemma list_eqb_eq : forall l1 l2, list_eqb l1 l2 = true <-> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2]; cbn; split; intros H; try discriminate; auto.
- apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst; auto.
- inversion H; subst. rewrite Z.eqb_refl. cbn. apply IH. reflexivity.
Qed.

Definition MMAP_THRESHOLD : Z := 131052.
