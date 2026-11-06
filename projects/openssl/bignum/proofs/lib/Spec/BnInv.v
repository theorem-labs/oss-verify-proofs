(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Inv.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Definition DMAX_MAX : Z := 65536.

Definition bn_ok (b : BN) : Prop :=
  limbs (bn_buf b) /\ (bn_top b <= bn_dmax b)%nat /\ Z.of_nat (bn_dmax b) <= DMAX_MAX /\ (bn_flags b = 0 \/ bn_flags b = 1).

Definition pool_ok (vals : list BN) : Prop :=
  vals = [] \/ exists p0 p1 p2, vals = p0 :: p1 :: p2 :: repeat (bn_nil 0) 13 /\ bn_ok p0 /\ bn_ok p1 /\ bn_ok p2.

Definition st_ok (s : LS) : Prop :=
  bn_ok (ls_b1 s) /\ bn_ok (ls_b2 s) /\ bn_ok (ls_b3 s) /\ bn_ok (ls_b4 s) /\ bn_ok (ls_b5 s) /\
  pool_ok (cx_vals (ls_ctx s)).

Definition bn_blocks (b : BN) : blocks :=
  match bn_d b with Some p => [(p, 8 * Z.of_nat (bn_dmax b))] | None => [] end.

Definition opt_block (p : option ptr) (n : Z) : blocks := match p with Some q => [(q, n)] | None => [] end.

Definition blocks_of (s : LS) : blocks :=
  bn_blocks (ls_b1 s) ++ bn_blocks (ls_b2 s) ++ bn_blocks (ls_b3 s) ++ bn_blocks (ls_b4 s) ++ bn_blocks (ls_b5 s) ++
  concat (map bn_blocks (cx_vals (ls_ctx s))) ++
  opt_block (cx_head (ls_ctx s)) POOL_ITEM_BYTES ++ opt_block (cx_indexes (ls_ctx s)) (4 * Z.of_nat BN_CTX_START_FRAMES).

Definition own (s : LS) (X : blocks) : Prop := Permutation X (blocks_of s).

Definition valid_ref (r : bnref) (s : LS) : Prop :=
  match r with RPool i => (i < 3)%nat /\ cx_vals (ls_ctx s) <> [] | _ => True end.

Lemma bn_blocks_nil : forall f, bn_blocks (bn_nil f : BN) = [].
Proof. reflexivity. Qed.

Definition bwp {A} (m : BM (M:=btree ptr) (ptr:=ptr) A) (s : LS) (X : blocks) (Q : A -> LS -> blocks -> Prop) : Prop :=
  wp (m s) X (fun p X' => Q (fst p) (snd p) X').

Lemma perm_pick : forall (L1 M L2 W : list (ptr * Z)), W = L1 ++ M ++ L2 -> Permutation W (M ++ L1 ++ L2).
Proof. intros L1 M L2 W ->. apply Permutation_app_swap_app. Qed.

Definition expanded (b : BN) (words : nat) (b' : BN) : Prop :=
  bn_top b' = bn_top b /\ bn_neg b' = bn_neg b /\ bn_flags b' = bn_flags b /\
  bn_buf b' = (if (words <=? bn_dmax b)%nat then bn_buf b
               else firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) /\
  bn_ok b' /\ (words <= bn_dmax b')%nat /\ (bn_dmax b <= bn_dmax b')%nat.

End Inv.
