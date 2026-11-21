(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import List.
From Stdlib Require Import Lia.
From stdpp Require Import list.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma firstn_S_nth (A : Type) (l : list A) (i : nat) (d : A) :
  (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  intros Hi.
  pose proof (lookup_lt_is_Some_2 l i Hi) as [x Hx].
  rewrite (nth_lookup l i d), Hx. cbn.
  exact (take_S_r _ _ _ Hx).
Qed.

