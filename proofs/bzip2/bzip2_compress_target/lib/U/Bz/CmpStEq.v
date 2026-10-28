(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import MState Frame.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma st_eq_intro : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) F (pc pc' : word) fc rv (m m' : word -> option byte) ro,
  x31 = y31 -> x15 = y15 -> x7 = y7 -> x23 = y23 -> x3 = y3 -> x19 = y19 -> x11 = y11 -> x27 = y27 -> x1 = y1 -> x17 = y17 -> x9 = y9 -> x25 = y25 -> x5 = y5 -> x21 = y21 -> x13 = y13 -> x29 = y29 -> x16 = y16 -> x8 = y8 -> x24 = y24 -> x4 = y4 -> x20 = y20 -> x12 = y12 -> x28 = y28 -> x2 = y2 -> x18 = y18 -> x10 = y10 -> x26 = y26 -> x6 = y6 -> x22 = y22 -> x14 = y14 -> x30 = y30 -> pc = pc' -> m = m' ->
  MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m ro = MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F pc' fc rv m' ro.
Proof. intros. subst. reflexivity. Qed.

(* [comment removed for export] *)
Ltac st_eq_leaf :=
  repeat first [ reflexivity
               | lazymatch goal with
                 | |- @eq Z _ _ => lia
                 | |- Z_to_bv _ _ = Z_to_bv _ _ => f_equal
                 | |- _ => progress f_equal
                 end ].

(* [comment removed for export] *)
Ltac st_eq_with_leaves R k :=
  lazymatch R with
  | mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 => k x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
  | TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty))) (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2) (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))) => k x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
  end.

Ltac st_eq_fast_core :=
  lazymatch goal with
  | |- MS ?R ?F ?pc ?fc ?rv ?m ?ro = MS ?R' ?F' ?pc' ?fc' ?rv' ?m' ?ro' =>
      unify F F'; unify fc fc'; unify rv rv'; unify ro ro';
      st_eq_with_leaves R ltac:(fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 =>
      st_eq_with_leaves R' ltac:(fun y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 =>
        simple refine (st_eq_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 F pc pc' fc rv m m' ro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        st_eq_leaf))
  end.

(* [comment removed for export] *)
Ltac st_eq_orig :=
  cbv delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with
                 | |- @eq Z _ _ => lia
                 | |- Z_to_bv _ _ = Z_to_bv _ _ => f_equal
                 | |- _ => progress f_equal
                 end ].
Ltac st_eq_fast := first [ st_eq_fast_core | st_eq_orig ].
