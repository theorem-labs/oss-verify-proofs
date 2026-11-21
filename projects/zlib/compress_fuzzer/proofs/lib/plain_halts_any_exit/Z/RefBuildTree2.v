(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeRod.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTreeLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable (t : tree_id).
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
Local Notation E := (sd_elems t).
Local Notation SP := (sp - 192).
Local Notation U := (bt_upd ds t).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Local Notation stree_dl := (RefBuildTree1.stree_dl t).
Local Notation stF := (RefBuildTree1.stF t).
Local Notation X0 := (RefBuildTree1.X0 ds t).
Local Notation L1 := (RefBuildTree1.L1 t).
Local Notation tsize_elems := (RefBuildTree1.tsize_elems t).
Local Notation elems_range := (RefBuildTree1.elems_range t).
Local Notation dsc_off_val := (RefBuildTree1.dsc_off_val t).
Local Notation SDA_range := (RefBuildTree1.SDA_range t).
Local Notation STP_range := (RefBuildTree1.STP_range t).

Local Ltac nf := cbn [RefBuildTree1.stF].

Lemma stree_has_STP : stree_has t = true <-> STP t <> 0.
Proof. destruct t; cbn; unfold A_static_ltree, A_static_dtree; split; intros; try congruence; lia. Qed.

Definition slen : Z := match t with TL => 288 | TD => 30 | TB => 1 end.

Lemma stree_Len_dl : forall n, stree_Len t n = arr_get stree_dl n.
Proof. intros n. unfold RefBuildTree1.stree_dl. destruct t; cbn [stree_Len]; rewrite ?arr_get_make; reflexivity. Qed.

Lemma stree_dl_bound : forall n, 0 <= n < slen -> 0 <= arr_get stree_dl n < 16.
Proof.
  intros n _. unfold RefBuildTree1.stree_dl. destruct t.
  - pose proof (static_ltree_dl_bound n). lia.
  - pose proof (static_dtree_dl_bound n). lia.
  - rewrite arr_get_make. lia.
Qed.

Lemma slen_ge : STP t <> 0 -> 3 <= slen.
Proof. unfold slen. destruct t; cbn; intros; lia. Qed.

Section PhaseC.
Variable DL : arr.
Variable HM : Z.
Variable BC : arr.
Variable MC : Z.
Local Notation W FC HP HL DP OL SL := (U FC DL HP HL HM DP BC OL SL MC).

Definition l2node (mc : Z) : Z * Z := if mc <? 2 then (mc + 1, mc + 1) else (0, mc).

Definition L2 (X : deflate_state) (mc : Z) : deflate_state * Z := build_tree_loop2 2 X t mc.

Lemma L2_out : forall f FC HP HL DP OL SL mc, 2 <= HL ->
  build_tree_loop2 f (W FC HP HL DP OL SL) t mc = (W FC HP HL DP OL SL, mc).
Proof.
  intros [|f] FC HP HL DP OL SL mc Hhl; [reflexivity|]. cbn [build_tree_loop2]. autorewrite with btupd.
  replace (HL <? 2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma L2_step : forall f FC HP HL DP OL SL mc, HL < 2 ->
  build_tree_loop2 (Datatypes.S f) (W FC HP HL DP OL SL) t mc =
    (let '(node, mc') := l2node mc in
     build_tree_loop2 f
       (W (arr_set FC node (wrap16 1)) (arr_set HP (HL + 1) node) (HL + 1) (arr_set DP node (wrap8 0)) (wrap64 (OL - 1))
          (if stree_has t then wrap64 (SL - stree_Len t node) else SL)) t mc').
Proof.
  intros f FC HP HL DP OL SL mc Hhl. cbn [build_tree_loop2]. autorewrite with btupd.
  replace (HL <? 2) with true by (symmetry; apply Z.ltb_lt; lia). unfold l2node.
  destruct (mc <? 2); autorewrite with btupd; destruct (stree_has t); autorewrite with btupd; reflexivity.
Qed.

Lemma stree_pb : forall n, 0 <= n < slen -> pb stree_dl n = arr_get stree_dl n.
Proof. intros n Hn. unfold pb. apply Z.mod_small. pose proof (stree_dl_bound n Hn). lia. Qed.

Lemma STP_rod : STP t <> 0 -> 191376 <= STP t /\ STP t + 2 + 4 * slen <= 194092.
Proof. unfold slen. destruct t; cbn; unfold A_static_ltree, A_static_dtree; intros; lia. Qed.

Local Ltac ceq :=
  first [ reflexivity
        | rewrite ?arr_set_set_same; reflexivity
        | nf; rewrite ?stree_pb by lia; rewrite ?wrap64_sub_l; first [reflexivity | f_equal; lia] ].
End PhaseC.

End Walk.
