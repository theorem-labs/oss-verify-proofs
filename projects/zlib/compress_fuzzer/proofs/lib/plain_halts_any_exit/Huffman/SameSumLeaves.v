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

(** * Equality of sum leaves

- Key definitions: [same_sum_leaves]
- Initial author: Laurent.Thery@inria.fr (2003)

*)

From Coq Require Import Sorting.Permutation.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Huffman Require Export Cover WeightTree.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Set Default Proof Using "Type".

Section SameSumLeaves.
Variable A : Type.
Variable f : A -> nat.

(** the sum leaves are the same upto permutation *)
Definition same_sum_leaves (l1 l2 : list (btree A)) : Prop :=
  exists l3 : list (btree A),
    (exists l4 : list (btree A),
       Permutation l1 l3 /\
       Permutation l2 l4 /\ 
       map (sum_leaves f) l3 = map (sum_leaves f) l4).

(** if the sum leaves are the same, the list are of same length *)
Theorem same_sum_leaves_length :
 forall l1 l2 : list (btree A),
 same_sum_leaves l1 l2 -> length l1 = length l2.
Proof.
intros l1 l2 (l3, (l4, (H0, (H1, H2)))).
rewrite (Permutation_length H0).
rewrite (Permutation_length H1).
repeat rewrite <- (map_length (sum_leaves f)); auto.
apply f_equal with (f := length (A:=nat)); auto.
Qed.
 
End SameSumLeaves.

Arguments same_sum_leaves [A].
