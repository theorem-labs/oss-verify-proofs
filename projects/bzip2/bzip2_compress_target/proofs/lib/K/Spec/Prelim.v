(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition u8  (x : Z) : Z := x mod 2^8.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zlength {A} (l : list A) : Z := Z.of_nat (length l).

Definition znth (l : list Z) (i : Z) : Z :=
  if i <? 0 then 0 else nth (Z.to_nat i) l 0.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zrepeat (v : Z) (n : Z) : list Z := repeat v (Z.to_nat n).
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zdrop (n : Z) (l : list Z) : list Z := skipn (Z.to_nat n) l.
(* [comment removed for export] *)
Lemma zlength_zdrop : forall n l, 0 <= n <= zlength l -> zlength (zdrop n l) = zlength l - n.
Proof. intros. unfold zlength, zdrop in *. rewrite length_skipn. lia. Qed.

(* [comment removed for export] *)
From Stdlib Require Import String Ascii.
Definition str (s : string) : list Z :=
  map (fun a => Z.of_N (N_of_ascii a)) (list_ascii_of_string s).
