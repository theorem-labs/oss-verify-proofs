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

(** * Weights of binary trees

- Key definitions: [sum_leaves]
- Initial author: Laurent.Thery@inria.fr (2003)

*)

From Coq Require Import ArithRing Sorting.Permutation.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Huffman Require Export BTree Ordered.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Set Default Proof Using "Type".
 
Section WeightTree.
Variable A : Type.
Variable f : A -> nat.

Fixpoint sum_leaves (t : btree A) : nat :=
  match t with
  | leaf n => f n
  | node t1 t2 => sum_leaves t1 + sum_leaves t2
  end.

Definition sum_order x y := sum_leaves x <= sum_leaves y.

Definition le_sum x y := sum_leaves x <=? sum_leaves y.
 
Theorem le_sum_correct1 :
 forall a b1 : btree A, le_sum a b1 = true -> sum_order a b1.
Proof.
intros a b1; apply (leb_complete (sum_leaves a) (sum_leaves b1)).
Qed.
 
Theorem le_sum_correct2 :
 forall a b1 : btree A, le_sum a b1 = false -> sum_order b1 a.
Proof.
intros a b1 Hsum; apply Nat.leb_gt in Hsum.
unfold sum_order; auto with arith.
Qed.
 
Fixpoint weight_tree (t : btree A) : nat :=
  match t with
  | leaf n => 0
  | node t1 t2 =>
      sum_leaves t1 + weight_tree t1 + (sum_leaves t2 + weight_tree t2)
  end.
 
Definition weight_tree_list : list (btree A) -> nat :=
  fold_right (fun x : btree A => plus (weight_tree x)) 0.
 
Theorem weight_tree_list_node :
 forall (t1 t2 : btree A) (l : list (btree A)),
 weight_tree_list (node t1 t2 :: l) =
 sum_leaves t1 + sum_leaves t2 + weight_tree_list (t1 :: t2 :: l).
Proof.
intros t1 t2 l; simpl in |- *; ring.
Qed.
 
Theorem weight_tree_list_permutation :
 forall l1 l2 : list (btree A),
 Permutation l1 l2 -> weight_tree_list l1 = weight_tree_list l2.
Proof.
intros l1 l2 H; elim H; auto.
simpl in |- *; auto; intros; ring.
simpl in |- *; auto; intros; ring.
intros l0 l3 l4 H0 H1 H2 H3; apply trans_equal with (1 := H1); auto.
Qed.
 
End WeightTree.
Arguments sum_leaves [A].
Arguments sum_order [A].
Arguments le_sum [A].
Arguments weight_tree [A].
Arguments weight_tree_list [A].

(** 
  sum_leaves are the same for ordered list that are permutations
  one from the other
*)
Theorem ordered_sum_leaves_eq :
 forall (A : Type) (f : A -> nat) (l1 l2 : list (btree A)),
 Permutation l1 l2 ->
 ordered (sum_order f) l1 ->
 ordered (sum_order f) l2 -> map (sum_leaves f) l1 = map (sum_leaves f) l2.
Proof.
intros A f l1 l2 H H0 H1.
apply ordered_perm_antisym_eq with (order := le).
exact Nat.le_trans.
exact Nat.le_antisymm.
apply Permutation_map; auto.
apply ordered_map_inv; auto.
apply ordered_map_inv; auto.
Qed.
