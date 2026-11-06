(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import List Lia.
From stdpp Require Import list.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Lemma firstn_S_nth (A : Type) (l : list A) (i : nat) (d : A) :
  (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  intros Hi.
  pose proof (lookup_lt_is_Some_2 l i Hi) as [x Hx].
  rewrite (nth_lookup l i d), Hx. cbn.
  exact (take_S_r _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma In_firstn {A} (x : A) (n : nat) (l : list A) :
  In x (firstn n l) -> In x l.
Proof.
  intros H. apply list_elem_of_In. apply list_elem_of_In in H.
  apply elem_of_take in H as (i & Hl & _).
  eapply list_elem_of_lookup_2. exact Hl.
Qed.

(* [comment removed for export] *)
Lemma skipn_cons_nth {A} (l : list A) (i : nat) (d : A) :
  (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof.
  intros Hi.
  pose proof (lookup_lt_is_Some_2 l i Hi) as [x Hx].
  rewrite (nth_lookup l i d), Hx. cbn.
  exact (drop_S l x i Hx).
Qed.

(* [comment removed for export] *)
Lemma firstn_all_len {A} (l : list A) : firstn (length l) l = l.
Proof. apply firstn_all. Qed.
