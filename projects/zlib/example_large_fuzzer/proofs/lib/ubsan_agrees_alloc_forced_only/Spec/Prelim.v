(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition u8  (x : Z) : Z := x mod 2^8.
Definition u16 (x : Z) : Z := x mod 2^16.
Definition u32 (x : Z) : Z := x mod 2^32.
Definition u64 (x : Z) : Z := x mod 2^64.
(* [comment removed for export] *)
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

Lemma znth_range : forall l i, 0 <= i < zlength l -> In (znth l i) l.
Proof.
  intros l i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [lia|].
  apply nth_In. lia.
Qed.

(* [comment removed for export] *)
Definition zrepeat (v : Z) (n : Z) : list Z := repeat v (Z.to_nat n).
Lemma zlength_zrepeat : forall v n, 0 <= n -> zlength (zrepeat v n) = n.
Proof. intros. unfold zlength, zrepeat. rewrite repeat_length. lia. Qed.

(* [comment removed for export] *)
Definition ztake (n : Z) (l : list Z) : list Z := firstn (Z.to_nat n) l.
Definition zdrop (n : Z) (l : list Z) : list Z := skipn (Z.to_nat n) l.

Lemma zlength_zdrop : forall n l, 0 <= n <= zlength l -> zlength (zdrop n l) = zlength l - n.
Proof. intros. unfold zlength, zdrop in *. rewrite length_skipn. lia. Qed.

(* [comment removed for export] *)
From Stdlib Require Import String Ascii.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition str (s : string) : list Z :=
  map (fun a => Z.of_N (N_of_ascii a)) (list_ascii_of_string s).
