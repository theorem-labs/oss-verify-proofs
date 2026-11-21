(* SPDX-License-Identifier: LGPL-2.1-or-later *)
(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU Lesser General Public License for more details.                *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)
(* Modified by Theorem Labs, 2026-11: the logical path of one Require line changed (From Huffman to the logical path of the folder that holds this file), and 3 lines added (Unset Lia Cache, Unset Nia Cache, Unset Nra Cache). *)

(** * Ordered covers and some of their properties

- Key definitions: [ordered_cover]
- Initial author: Laurent.Thery@inria.fr (2003)

*)

From Coq Require Import Sorting.Permutation.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Huffman Require Export Cover.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Set Default Proof Using "Type".
 
Section OrderedCover.
Variable A : Type.

#[local] Hint Constructors Permutation : core.
#[local] Hint Resolve Permutation_refl : core.
#[local] Hint Resolve Permutation_app : core.
#[local] Hint Resolve Permutation_app_swap : core.

(**
  An ordered cover is a cover where the positions of the elements in
  the list are fixed
*)
Inductive ordered_cover : list (btree A) -> btree A -> Prop :=
  | ordered_cover_one :
      forall (t : btree A) (l : list (btree A)), ordered_cover (t :: []) t
  | ordered_cover_node :
      forall (t1 t2 : btree A) (l1 l2 l3 : list (btree A)),
      ordered_cover l1 t1 ->
      ordered_cover l2 t2 -> ordered_cover (l1 ++ l2) (node t1 t2).
#[local] Hint Resolve ordered_cover_one ordered_cover_node : core.

(** Ordered covers are special cases of covers *)
Theorem ordered_cover_cover :
 forall (l : list (btree A)) (t : btree A), ordered_cover l t -> cover l t.
intros l t H; elim H; auto.
intros t1 t2 l1 l2 l3 H0 H1 H2 H3.
Proof.
apply cover_app; auto.
Qed.

(** It is always possible to get an ordered cover from a cover *)
Theorem cover_ordered_cover :
 forall (l1 : list (btree A)) (t : btree A),
 cover l1 t -> exists l2, Permutation l1 l2 /\ ordered_cover l2 t.
Proof.
intros l1; elim l1 using list_length_ind.
intros l0 H t; case t.
intros a H1; rewrite cover_inv_leaf with (1 := H1).
exists (leaf a :: []); auto.
intros t1 t2 H1; case cover_inv_app with (1 := H1).
intros H2; exists l0; split; auto; rewrite H2; auto.
intros (l2, (l3, ((HH1, HH2), HH3))).
case H with (2 := HH1); auto.
rewrite Permutation_length with (1 := HH3).
generalize HH2; rewrite app_length; case l3; simpl in |- *; auto with arith.
intros HH4; case cover_not_nil with (1 := HH4); auto.
intros; rewrite Nat.add_comm; simpl in |- *; auto with arith.
intros l4 (HP1, HP2).
case H with (2 := HH2); auto.
rewrite Permutation_length with (1 := HH3).
generalize HH1; rewrite app_length; case l2; simpl in |- *; auto with arith.
intros HH4; case cover_not_nil with (1 := HH4); auto.
intros l5 (HP3, HP4).
exists (l4 ++ l5); split; auto.
apply Permutation_trans with (1 := HH3); auto.
Qed.

(**
  If the ordered cover is composed of only leaves, they are the
  exact leaves of the tree
*) 
Theorem NoDup_ordered_cover :
 forall l1 l2 t,
 ordered_cover l1 t ->
 NoDup l2 -> l1 = map (fun x : A => leaf x) l2 -> all_leaves t = l2.
Proof.
intros l1 l2 t H; generalize l2; elim H; clear H l1 l2 t; simpl in |- *; auto.
intros t l l2; case l2; simpl in |- *; auto.
intros; discriminate.
intros a0 l0 H H0; injection H0; intros H1 H2; rewrite H2; auto.
generalize H1; case l0; simpl in |- *; auto.
intros; discriminate.
intros t1 t2 l1 l2 l3 H H0 H1 H2 l0 H3 H4.
cut
 ((exists l3 : list A, l1 = map (fun x : A => leaf x) l3) /\
  (exists l4 : list A, l2 = map (fun x : A => leaf x) l4)).
intros ((l4, HH1), (l5, HH2)).
cut (l0 = l4 ++ l5); [ intros HH3 | idtac ].
rewrite HH3.
apply f_equal2 with (f := app (A:=A)).
apply H0; auto.
apply NoDup_app_inv_l with (l2 := l5); rewrite <- HH3; auto.
apply H2; auto.
apply NoDup_app_inv_r with (l1 := l4); rewrite <- HH3; auto.
rewrite HH2 in H4; rewrite HH1 in H4.
rewrite <- map_app in H4.
generalize H4; generalize (l4 ++ l5); elim l0; simpl in |- *; auto.
intros l; case l; simpl in |- *; auto.
intros; discriminate.
intros a0 l H5 l6; case l6; simpl in |- *; auto.
intros; discriminate.
intros a1 l7 H6; apply f_equal2 with (f := cons (A:=A)); auto.
injection H6; auto.
injection H6; auto.
generalize H4; generalize l2 l0; elim l1; simpl in |- *; auto.
intros l4 l5 H5; split; [ exists [] | exists l5 ]; auto.
intros a0 l H5 l4 l5; case l5; simpl in |- *; auto.
intros; discriminate.
intros a1 l6 H6; case (H5 l4 l6); auto.
injection H6; auto.
intros (l7, HH5) (l8, HH6); split; [ exists (a1 :: l7) | exists l8 ];
 simpl in |- *; auto.
apply f_equal2 with (f := cons (A:=btree A)); auto.
injection H6; auto.
Qed.

End OrderedCover.
Arguments ordered_cover [A].
#[export] Hint Resolve ordered_cover_one ordered_cover_node : core.
