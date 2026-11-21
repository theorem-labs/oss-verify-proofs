(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.

Module TreeMem.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Export TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithSegs.

Fixpoint layout_gap (L : list (Z * nat)) (lo hi : Z) : bool :=
  match L with
  | [] => true
  | (o, w) :: L' => ((o + Z.of_nat w <=? lo) || (hi <=? o)) && layout_gap L' lo hi
  end.

Lemma dsl_gap_trees : layout_gap dsl_layout 212 2904 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dsl_gap_heap : layout_gap dsl_layout 2976 5300 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dsl_gap_depth : layout_gap dsl_layout 5308 5881 = true. Proof. vm_compute. reflexivity. Qed.

Section Scalars.
Variables SL SD SB : Z.
End Scalars.

End WithSegs.

Definition hv (h : arr) (i : Z) : Z := (arr_get h i) mod 573.
Lemma hv_range : forall h i, 0 <= hv h i < 573.
Proof. intros. unfold hv. apply Z.mod_pos_bound. lia. Qed.
Lemma hv_get : forall h i, 0 <= arr_get h i < 573 -> hv h i = arr_get h i.
Proof. intros h i H. unfold hv. apply Z.mod_small. exact H. Qed.

Section Reads.
End Reads.

Ltac arr_range_auto :=
  first [ lia
        | match goal with
          | R : forall j, _ -> 0 <= arr_get ?a j < _ |- 0 <= arr_get ?a _ < _ => apply R; lia
          | R : forall j, _ -> 0 <= arr_get ?a j < _ |- 0 <= arr_get ?a _ < _ =>
              eapply (fun j H => proj1 (conj (R j H) I)); lia
          end
        | match goal with
          | R : forall j, _ -> 0 <= arr_get ?a j < ?B |- 0 <= arr_get ?a ?i < ?C =>
              let H := fresh in pose proof (R i) as H; lia
          end ].
End TreeMem.

Module RefBitsLib.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section Rel.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Local Notation PB := (p_pending_buf p).

End Rel.

Lemma set_tree_fc_twice : forall s t a b, set_tree_fc (set_tree_fc s t a) t b = set_tree_fc s t b.
Proof. intros s [| |] a b; reflexivity. Qed.
Lemma tree_fc_set_tree_fc : forall s t a, tree_fc (set_tree_fc s t a) t = a.
Proof. intros s [| |] a; reflexivity. Qed.
Lemma set_tree_dl_twice : forall s t a b, set_tree_dl (set_tree_dl s t a) t b = set_tree_dl s t b.
Proof. intros s [| |] a b; reflexivity. Qed.
Lemma tree_dl_set_tree_dl : forall s t a, tree_dl (set_tree_dl s t a) t = a.
Proof. intros s [| |] a; reflexivity. Qed.

Section Rel2.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Local Notation PB := (p_pending_buf p).

End Rel2.

Lemma franges_apart : forall F a n b k,
  sub_franges F a n -> disj_franges F b k -> 0 < n -> 0 < k -> a + n <= b \/ b + k <= a.
Proof.
  intros F a n b k Hs Hd Hn Hk.
  destruct (Z_le_gt_dec (a + n) b) as [|H1]; [left; lia|].
  destruct (Z_le_gt_dec (b + k) a) as [|H2]; [right; lia|].
  exfalso. destruct (Z_le_gt_dec a b).
  - apply (Hd b ltac:(lia)). apply Hs. lia.
  - apply (Hd a ltac:(lia)). apply Hs. lia.
Qed.

Lemma sub_franges_mono : forall F a n b k,
  sub_franges F a n -> a <= b -> b + k <= a + n -> sub_franges F b k.
Proof. intros F a n b k H H1 H2 x Hx. apply H. lia. Qed.

Lemma upd4_congr : forall s A A' P P' B B' V V',
  A = A' -> P = P' -> B = B' -> V = V' -> upd4 s A P B V = upd4 s A' P' B' V'.
Proof. intros; subst; reflexivity. Qed.

Ltac u4 t :=
  lazymatch t with
  | set_bi_valid ?t1 ?v =>
      let r := u4 t1 in lazymatch r with upd4 ?s ?A ?P ?B ?V => constr:(upd4 s A P B v) end
  | set_bi_buf ?t1 ?v =>
      let r := u4 t1 in lazymatch r with upd4 ?s ?A ?P ?B ?V => constr:(upd4 s A P v V) end
  | set_pending ?t1 ?v =>
      let r := u4 t1 in lazymatch r with upd4 ?s ?A ?P ?B ?V => constr:(upd4 s A v B V) end
  | set_pending_buf ?t1 ?v =>
      let r := u4 t1 in lazymatch r with upd4 ?s ?A ?P ?B ?V => constr:(upd4 s v P B V) end
  | upd4 _ _ _ _ _ => t
  | ?s => constr:(upd4 s (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s))
  end.

Ltac st_eq :=
  lazymatch goal with
  | |- ?a = ?b =>
      let a' := u4 a in let b' := u4 b in
      change (a' = b'); apply upd4_congr; dsred
  end.
End RefBitsLib.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition TFB_FRAME : Z := 272.

Definition dsc_off (t : tree_id) : Z := match t with TL => 2904 | TD => 2928 | TB => 2952 end.
