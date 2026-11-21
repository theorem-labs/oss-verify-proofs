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

(** * Properties of products between an integer list and a list of trees

- Key definitions: [prod2list]
- Initial author: Laurent.Thery@inria.fr (2003)

*)

From Coq Require Import ArithRing Sorting.Permutation.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Huffman Require Export WeightTree Ordered.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Set Default Proof Using "Type".

Section Prod2List.
Variable A : Type.
Variable f : A -> nat.

#[local] Hint Constructors Permutation : core.
#[local] Hint Resolve Permutation_refl : core.
#[local] Hint Resolve Permutation_app : core.
#[local] Hint Resolve Permutation_app_swap : core.

(**
 In the product, the sum of the leaves is multiplied by the integer
 and added to the weight of the tree
*)
Definition prod2list l1 l2 :=
  fold_left plus
    (map2 (fun a b => a * sum_leaves f b + weight_tree f b) l1 l2) 0.

(** The product of the appended list is the sum of the product *)
Theorem prod2list_app :
 forall l1 l2 l3 l4,
 length l1 = length l2 ->
 prod2list (l1 ++ l3) (l2 ++ l4) = prod2list l1 l2 + prod2list l3 l4.
Proof.
intros l1 l2 l3 l4 H; unfold prod2list in |- *.
rewrite map2_app; auto.
rewrite fold_left_app.
rewrite Nat.add_comm.
apply sym_equal.
repeat
 rewrite
  fold_left_eta with (f := plus) (f1 := fun a b : nat => a + (fun x => x) b);
 auto.
apply sym_equal; rewrite <- fold_plus_split with (f := fun x : nat => x);
 auto.
apply Nat.add_comm.
Qed.

(** Permuting two choosen elements lower the product *)
Theorem prod2list_le_l :
 forall a b c d l1 l2 l3 l4 l5 l6,
 length l1 = length l4 ->
 length l2 = length l5 ->
 length l3 = length l6 ->
 sum_leaves f c <= sum_leaves f d ->
 a <= b ->
 prod2list (l1 ++ a :: l2 ++ b :: l3) (l4 ++ d :: l5 ++ c :: l6) <=
 prod2list (l1 ++ a :: l2 ++ b :: l3) (l4 ++ c :: l5 ++ d :: l6).
Proof.
intros a b c d l1 l2 l3 l4 l5 l6 H H0 H1 H2 H3;
 change
   (prod2list (l1 ++ (a :: []) ++ l2 ++ (b :: []) ++ l3)
      (l4 ++ (d :: []) ++ l5 ++ (c :: []) ++ l6) <=
    prod2list (l1 ++ (a :: []) ++ l2 ++ (b :: []) ++ l3)
      (l4 ++ (c :: []) ++ l5 ++ (d :: []) ++ l6)) 
  in |- *.
repeat rewrite prod2list_app; auto.
apply Nat.add_le_mono; auto with arith.
repeat rewrite Nat.add_assoc; apply Nat.add_le_mono; auto.
repeat rewrite (fun x y z => Nat.add_comm (prod2list (x :: y) z)).
repeat rewrite <- Nat.add_assoc; apply Nat.add_le_mono; auto.
unfold prod2list in |- *; simpl in |- *.
rewrite <- Nat.sub_add with (1 := H3); auto.
rewrite <- Nat.sub_add with (1 := H2); auto.
replace
  (a * (sum_leaves f d - sum_leaves f c + sum_leaves f c) + weight_tree f d +
  ((b - a + a) * sum_leaves f c + weight_tree f c)) with
(a * sum_leaves f c + weight_tree f c +
  (a * (sum_leaves f d - sum_leaves f c) + (a + (b - a)) * sum_leaves f c +
   weight_tree f d)); [ idtac | ring ].
apply Nat.add_le_mono; auto with arith.
apply Nat.add_le_mono; auto with arith.
repeat rewrite Nat.mul_add_distr_l || rewrite Nat.mul_add_distr_r;
 auto with arith.
replace
 (a * (sum_leaves f d - sum_leaves f c) +
  (a * sum_leaves f c + (b - a) * sum_leaves f c)) with
 (a * sum_leaves f c + (b - a) * sum_leaves f c +
  (a * (sum_leaves f d - sum_leaves f c) + 0)); [ ring_simplify | ring ].
auto with arith.
Qed.

(** Permuting two choosen elements lower the product *)
Theorem prod2list_le_r :
 forall a b c d l1 l2 l3 l4 l5 l6,
 length l1 = length l4 ->
 length l2 = length l5 ->
 length l3 = length l6 ->
 sum_leaves f d <= sum_leaves f c ->
 b <= a ->
 prod2list (l1 ++ a :: l2 ++ b :: l3) (l4 ++ d :: l5 ++ c :: l6) <=
 prod2list (l1 ++ a :: l2 ++ b :: l3) (l4 ++ c :: l5 ++ d :: l6).
Proof.
intros a b c d l1 l2 l3 l4 l5 l6 H H0 H1 H2 H3;
 change
   (prod2list (l1 ++ (a :: []) ++ l2 ++ (b :: []) ++ l3)
      (l4 ++ (d :: []) ++ l5 ++ (c :: []) ++ l6) <=
    prod2list (l1 ++ (a :: []) ++ l2 ++ (b :: []) ++ l3)
      (l4 ++ (c :: []) ++ l5 ++ (d :: []) ++ l6)) 
  in |- *.
repeat rewrite prod2list_app; auto.
apply Nat.add_le_mono; auto with arith.
repeat rewrite Nat.add_assoc; apply Nat.add_le_mono; auto.
repeat rewrite (fun x y z => Nat.add_comm (prod2list (x :: y) z)).
repeat rewrite <- Nat.add_assoc; apply Nat.add_le_mono; auto.
unfold prod2list in |- *; simpl in |- *.
rewrite <- Nat.sub_add with (1 := H3); auto.
rewrite <- Nat.sub_add with (1 := H2); auto.
replace
 ((a - b + b) * (sum_leaves f c - sum_leaves f d + sum_leaves f d) +
  weight_tree f c + (b * sum_leaves f d + weight_tree f d)) with
 ((b + (a - b)) * sum_leaves f d + weight_tree f d +
  ((b + (a - b)) * (sum_leaves f c - sum_leaves f d) + b * sum_leaves f d +
   weight_tree f c)); [ idtac | ring ].
ring_simplify; auto with arith.
Qed.

(** Permuting two choosen elements with same integer does not change the product *)
Theorem prod2list_eq :
 forall a b c l1 l2 l3 l4 l5 l6,
 length l1 = length l4 ->
 length l2 = length l5 ->
 length l3 = length l6 ->
 prod2list (l1 ++ a :: l2 ++ a :: l3) (l4 ++ b :: l5 ++ c :: l6) =
 prod2list (l1 ++ a :: l2 ++ a :: l3) (l4 ++ c :: l5 ++ b :: l6).
Proof.
intros a b c l1 l2 l3 l4 l5 l6 H H0 H1;
 change
   (prod2list (l1 ++ (a :: []) ++ l2 ++ (a :: []) ++ l3)
      (l4 ++ (b :: []) ++ l5 ++ (c :: []) ++ l6) =
    prod2list (l1 ++ (a :: []) ++ l2 ++ (a :: []) ++ l3)
      (l4 ++ (c :: []) ++ l5 ++ (b :: []) ++ l6)) 
  in |- *.
repeat rewrite prod2list_app; auto with arith.
ring.
Qed.

(** Putting the smallest tree with the smallest integer lower the product *)
Theorem prod2list_reorder :
 forall a b b1 l1 l2 l3 l4 l5,
 length l1 = length l3 ->
 length l2 = length l4 ->
 (forall b, In b l1 -> b <= a) ->
 (forall b, In b l2 -> b <= a) ->
 Permutation (l3 ++ b :: l4) (b1 :: l5) ->
 ordered (sum_order f) (b1 :: l5) ->
 exists l6,
   (exists l7,
      length l1 = length l6 /\
      length l2 = length l7 /\
      Permutation (b1 :: l5) (l6 ++ b1 :: l7) /\
      prod2list (l1 ++ a :: l2) (l6 ++ b1 :: l7) <=
      prod2list (l1 ++ a :: l2) (l3 ++ b :: l4)).
Proof.
intros a b b1 l1 l2 l3 l4 l5 H H0 H1 H2 H3 H4.
cut (In b (b1 :: l5));
 [ simpl in |- *; intros [HH0| HH0]
 | apply Permutation_in with (1 := H3); auto with datatypes ].
exists l3; exists l4; repeat (split; auto).
pattern b1 at 2 in |- *; rewrite HH0; apply Permutation_sym; auto.
rewrite HH0; auto.
cut (In b1 (l3 ++ b :: l4));
 [ intros HH1
 | apply Permutation_in with (1 := Permutation_sym H3);
    auto with datatypes ].
case in_app_or with (1 := HH1); intros HH2.
case in_split with (1 := HH2).
intros l6 (l7, HH3); exists (l6 ++ b :: l7); exists l4; repeat (split; auto).
apply trans_equal with (1 := H).
rewrite HH3; repeat rewrite app_length; simpl in |- *; auto with arith.
apply Permutation_sym; apply Permutation_trans with (2 := H3); auto.
rewrite HH3.
repeat rewrite <- app_assoc.
simpl in |- *; apply Permutation_app; auto.
apply Permutation_transposition.
rewrite HH3; auto.
repeat rewrite <- app_assoc.
case (same_length_ex _ _ b1 l6 l7 l1); auto.
rewrite <- HH3; auto.
intros l8 (l9, (b2, (HH4, (HH5, HH6)))).
rewrite HH6.
repeat rewrite <- app_assoc; simpl in |- *.
apply prod2list_le_l; auto.
change (sum_order f b1 b) in |- *.
apply ordered_trans with (2 := H4); auto.
unfold sum_order in |- *; intros a0 b0 c H5 H6; apply Nat.le_trans with (1 := H5);
 auto.
apply H1; rewrite HH6; auto with datatypes.
simpl in HH2; case HH2; intros HH3.
exists l3; exists l4; repeat (split; auto); try (rewrite <- HH3; auto; fail).
pattern b1 at 2 in |- *; rewrite <- HH3; apply Permutation_sym; auto.
case in_split with (1 := HH3).
intros l6 (l7, HH4); exists l3; exists (l6 ++ b :: l7); repeat (split; auto).
apply trans_equal with (1 := H0).
rewrite HH4; repeat rewrite app_length; simpl in |- *; auto with arith.
apply Permutation_sym; apply Permutation_trans with (2 := H3); auto.
rewrite HH4.
simpl in |- *; apply Permutation_app; auto. 
apply Permutation_transposition.
rewrite HH4; auto.
case (same_length_ex _ _ b1 l6 l7 l2); auto.
rewrite <- HH4; auto.
intros l8 (l9, (b2, (HH5, (HH6, HH7)))).
rewrite HH7.
apply prod2list_le_r; auto.
change (sum_order f b1 b) in |- *.
apply ordered_trans with (2 := H4); auto.
unfold sum_order in |- *; intros a0 b0 c H5 H6; apply Nat.le_trans with (1 := H5);
 auto.
apply H2; rewrite HH7; auto with datatypes.
Qed.

(** Putting the smallest tree with the smallest integer lower the product *) 
Theorem prod2list_reorder2 :
 forall a b c b1 c1 l1 l2 l3 l4 l5,
 length l1 = length l3 ->
 length l2 = length l4 ->
 (forall b, In b l1 -> b <= a) ->
 (forall b, In b l2 -> b <= a) ->
 Permutation (l3 ++ b :: c :: l4) (b1 :: c1 :: l5) ->
 ordered (sum_order f) (b1 :: c1 :: l5) ->
 exists l6,
   (exists l7,
      length l1 = length l6 /\
      length l2 = length l7 /\
      Permutation (b1 :: c1 :: l5) (l6 ++ b1 :: c1 :: l7) /\
      prod2list (l1 ++ a :: a :: l2) (l6 ++ b1 :: c1 :: l7) <=
      prod2list (l1 ++ a :: a :: l2) (l3 ++ b :: c :: l4)).
Proof.
intros a b c b1 c1 l1 l2 l3 l4 l5 H H0 H1 H2 H3 H4.
case (prod2list_reorder a b b1 l1 (a :: l2) l3 (c :: l4) (c1 :: l5));
 simpl in |- *; auto.
intros b0 [H5| H5]; auto.
rewrite H5; auto.
intros l6 (l7, (HH1, (HH2, (HH3, HH4)))).
generalize HH2 HH3 HH4; case l7; clear HH2 HH3 HH4 l7.
intros; discriminate.
intros c2 l7 HH2 HH3 HH4.
case (prod2list_reorder a c2 c1 l1 l2 l6 l7 l5); simpl in |- *; auto.
apply Permutation_cons_inv with (a := b1); auto.
apply Permutation_sym; apply Permutation_trans with (1 := HH3).
change
  (Permutation (l6 ++ (b1 :: []) ++ c2 :: l7)
     (((b1 :: []) ++ l6) ++ c2 :: l7)) in |- *.
repeat rewrite app_assoc.
apply Permutation_app; auto.
apply ordered_inv with (1 := H4); auto.
intros l8 (l9, (HH5, (HH6, (HH7, HH8)))).
exists l8; exists l9; repeat (split; auto).
apply Permutation_trans with ((b1 :: c1 :: l9) ++ l8); auto.
simpl in |- *; apply perm_skip; auto.
apply Permutation_trans with (1 := HH7).
apply Permutation_trans with ((c1 :: l9) ++ l8); auto.
apply Nat.le_trans with (2 := HH4).
change
  (prod2list (l1 ++ (a :: []) ++ a :: l2) (l8 ++ (b1 :: []) ++ c1 :: l9) <=
   prod2list (l1 ++ (a :: []) ++ a :: l2) (l6 ++ (b1 :: []) ++ c2 :: l7))
 in |- *.
generalize HH8; repeat rewrite prod2list_app; auto with arith.
intros HH9.
repeat rewrite Nat.add_assoc.
repeat rewrite (fun x => Nat.add_comm (prod2list l1 x)).
repeat rewrite <- Nat.add_assoc; auto with arith.
Qed.
 
End Prod2List.

Arguments prod2list [A].
