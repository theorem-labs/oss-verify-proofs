(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition bt_upd (s : deflate_state) (t : tree_id) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z)
  : deflate_state :=
  match t with
  | TL => mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) FC DL (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) MC (ds_d_max_code s) (ds_bl_max_code s) BC HP HL HM DP (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) OL SL (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s)
  | TD => mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) FC DL (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) MC (ds_bl_max_code s) BC HP HL HM DP (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) OL SL (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s)
  | TB => mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) FC DL (ds_l_max_code s) (ds_d_max_code s) MC BC HP HL HM DP (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) OL SL (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s)
  end.

Lemma bt_upd_setters : forall s t FC DL HP HL HM DP BC OL SL MC,
  bt_upd s t FC DL HP HL HM DP BC OL SL MC =
  set_max_code
    (set_static_len
      (set_opt_len
        (set_bl_count
          (set_depth (set_heap_max (set_heap_len (set_heap (set_tree_dl (set_tree_fc s t FC) t DL) HP) HL) HM) DP)
          BC) OL) SL) t MC.
Proof. intros. destruct t; reflexivity. Qed.

Lemma bt_upd_self : forall s t,
  bt_upd s t (tree_fc s t) (tree_dl s t) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s)
         (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t) = s.
Proof. intros s t. destruct s, t; reflexivity. Qed.

Lemma bt_upd_congr : forall s t FC FC' DL DL' HP HP' HL HL' HM HM' DP DP' BC BC' OL OL' SL SL' MC MC',
  FC = FC' -> DL = DL' -> HP = HP' -> HL = HL' -> HM = HM' -> DP = DP' -> BC = BC' -> OL = OL' -> SL = SL' -> MC = MC' ->
  bt_upd s t FC DL HP HL HM DP BC OL SL MC = bt_upd s t FC' DL' HP' HL' HM' DP' BC' OL' SL' MC'.
Proof. intros; subst; reflexivity. Qed.

Section Algebra.
Variable s : deflate_state.
Variable t : tree_id.
Variable FC : arr.
Variable DL : arr.
Variable HP : arr.
Variable HL : Z.
Variable HM : Z.
Variable DP : arr.
Variable BC : arr.
Variable OL : Z.
Variable SL : Z.
Variable MC : Z.
Local Notation U := (bt_upd s t FC DL HP HL HM DP BC OL SL MC).

Lemma bt_tree_fc : tree_fc U t = FC.        Proof. destruct t; reflexivity. Qed.
Lemma bt_tree_dl : tree_dl U t = DL.        Proof. destruct t; reflexivity. Qed.
Lemma bt_heap : ds_heap U = HP.             Proof. destruct t; reflexivity. Qed.
Lemma bt_heap_len : ds_heap_len U = HL.     Proof. destruct t; reflexivity. Qed.
Lemma bt_heap_max : ds_heap_max U = HM.     Proof. destruct t; reflexivity. Qed.
Lemma bt_depth : ds_depth U = DP.           Proof. destruct t; reflexivity. Qed.
Lemma bt_bl_count : ds_bl_count U = BC.     Proof. destruct t; reflexivity. Qed.
Lemma bt_opt_len : ds_opt_len U = OL.       Proof. destruct t; reflexivity. Qed.
Lemma bt_static_len : ds_static_len U = SL. Proof. destruct t; reflexivity. Qed.
Lemma bt_max_code : max_code U t = MC.      Proof. destruct t; reflexivity. Qed.

Lemma bt_Freq : forall i, Freq U t i = arr_get FC i.       Proof. intros. unfold Freq. rewrite bt_tree_fc. reflexivity. Qed.
Lemma bt_Len : forall i, Len U t i = arr_get DL i.         Proof. intros. unfold Len. rewrite bt_tree_dl. reflexivity. Qed.
Lemma bt_Dad : forall i, Dad U t i = arr_get DL i.         Proof. intros. unfold Dad. rewrite bt_tree_dl. reflexivity. Qed.
Lemma bt_heap_get : forall i, heap_get U i = arr_get HP i. Proof. intros. unfold heap_get. rewrite bt_heap. reflexivity. Qed.
Lemma bt_depth_get : forall i, depth_get U i = arr_get DP i. Proof. intros. unfold depth_get. rewrite bt_depth. reflexivity. Qed.
Lemma bt_bl_count_get : forall i, bl_count_get U i = arr_get BC i.
Proof. intros. unfold bl_count_get. rewrite bt_bl_count. reflexivity. Qed.

Lemma bt_pending_buf : ds_pending_buf U = ds_pending_buf s. Proof. destruct t; reflexivity. Qed.
Lemma bt_pending : ds_pending U = ds_pending s.             Proof. destruct t; reflexivity. Qed.
Lemma bt_bi_buf : ds_bi_buf U = ds_bi_buf s.                Proof. destruct t; reflexivity. Qed.
Lemma bt_bi_valid : ds_bi_valid U = ds_bi_valid s.          Proof. destruct t; reflexivity. Qed.

Lemma bt_set_tree_fc : forall a, set_tree_fc U t a = bt_upd s t a DL HP HL HM DP BC OL SL MC.
Proof. intros. destruct t; reflexivity. Qed.
Lemma bt_set_tree_dl : forall a, set_tree_dl U t a = bt_upd s t FC a HP HL HM DP BC OL SL MC.
Proof. intros. destruct t; reflexivity. Qed.
Lemma bt_set_heap : forall a, set_heap U a = bt_upd s t FC DL a HL HM DP BC OL SL MC.
Proof. intros. destruct t; reflexivity. Qed.
Lemma bt_set_heap_len : forall v, set_heap_len U v = bt_upd s t FC DL HP v HM DP BC OL SL MC.
Proof. intros. destruct t; reflexivity. Qed.
Lemma bt_set_heap_max : forall v, set_heap_max U v = bt_upd s t FC DL HP HL v DP BC OL SL MC.
Proof. intros. destruct t; reflexivity. Qed.
Lemma bt_set_depth : forall a, set_depth U a = bt_upd s t FC DL HP HL HM a BC OL SL MC.
Proof. intros. destruct t; reflexivity. Qed.
Lemma bt_set_bl_count : forall a, set_bl_count U a = bt_upd s t FC DL HP HL HM DP a OL SL MC.
Proof. intros. destruct t; reflexivity. Qed.
Lemma bt_set_opt_len : forall v, set_opt_len U v = bt_upd s t FC DL HP HL HM DP BC v SL MC.
Proof. intros. destruct t; reflexivity. Qed.
Lemma bt_set_static_len : forall v, set_static_len U v = bt_upd s t FC DL HP HL HM DP BC OL v MC.
Proof. intros. destruct t; reflexivity. Qed.
Lemma bt_set_max_code : forall v, set_max_code U t v = bt_upd s t FC DL HP HL HM DP BC OL SL v.
Proof. intros. destruct t; reflexivity. Qed.

Lemma bt_set_Freq : forall i v, set_Freq U t i v = bt_upd s t (arr_set FC i (wrap16 v)) DL HP HL HM DP BC OL SL MC.
Proof. intros. unfold set_Freq. rewrite bt_tree_fc. apply bt_set_tree_fc. Qed.
Lemma bt_set_Dad : forall i v, set_Dad U t i v = bt_upd s t FC (arr_set DL i (wrap16 v)) HP HL HM DP BC OL SL MC.
Proof. intros. unfold set_Dad. rewrite bt_tree_dl. apply bt_set_tree_dl. Qed.
Lemma bt_set_Len : forall i v, set_Len U t i v = bt_upd s t FC (arr_set DL i (wrap16 v)) HP HL HM DP BC OL SL MC.
Proof. exact bt_set_Dad. Qed.
Lemma bt_heap_set : forall i v, heap_set U i v = bt_upd s t FC DL (arr_set HP i v) HL HM DP BC OL SL MC.
Proof. intros. unfold heap_set. rewrite bt_heap. apply bt_set_heap. Qed.
Lemma bt_depth_set : forall i v, depth_set U i v = bt_upd s t FC DL HP HL HM (arr_set DP i (wrap8 v)) BC OL SL MC.
Proof. intros. unfold depth_set. rewrite bt_depth. apply bt_set_depth. Qed.
Lemma bt_bl_count_set : forall i v, bl_count_set U i v = bt_upd s t FC DL HP HL HM DP (arr_set BC i (wrap16 v)) OL SL MC.
Proof. intros. unfold bl_count_set. rewrite bt_bl_count. apply bt_set_bl_count. Qed.

Lemma bt_tree_lens : tree_lens s ->
  arr_len FC = tsize t -> arr_len DL = tsize t -> arr_len HP = 573 -> arr_len DP = 573 -> arr_len BC = 16 ->
  tree_lens U.
Proof.
  intros H LFC LDL LHP LDP LBC. unfold tree_lens in *. destruct t; cbn in *; repeat split; try lia; tauto.
Qed.
End Algebra.

Lemma bt_upd_upd : forall s t FC DL HP HL HM DP BC OL SL MC FC' DL' HP' HL' HM' DP' BC' OL' SL' MC',
  bt_upd (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t FC' DL' HP' HL' HM' DP' BC' OL' SL' MC'
  = bt_upd s t FC' DL' HP' HL' HM' DP' BC' OL' SL' MC'.
Proof. intros. destruct s, t; reflexivity. Qed.

Lemma bt_tree_fc_other : forall s t t' FC DL HP HL HM DP BC OL SL MC, t' <> t ->
  tree_fc (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t' = tree_fc s t'.
Proof. intros s t t'; destruct t, t'; intros; try congruence; reflexivity. Qed.
Lemma bt_tree_dl_other : forall s t t' FC DL HP HL HM DP BC OL SL MC, t' <> t ->
  tree_dl (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t' = tree_dl s t'.
Proof. intros s t t'; destruct t, t'; intros; try congruence; reflexivity. Qed.

Create HintDb btupd.
#[export] Hint Rewrite bt_tree_fc bt_tree_dl bt_heap bt_heap_len bt_heap_max bt_depth bt_bl_count bt_opt_len
  bt_static_len bt_max_code bt_Freq bt_Len bt_Dad bt_heap_get bt_depth_get bt_bl_count_get
  bt_pending_buf bt_pending bt_bi_buf bt_bi_valid
  bt_set_tree_fc bt_set_tree_dl bt_set_heap bt_set_heap_len bt_set_heap_max bt_set_depth bt_set_bl_count
  bt_set_opt_len bt_set_static_len bt_set_max_code
  bt_set_Freq bt_set_Dad bt_set_Len bt_heap_set bt_depth_set bt_bl_count_set bt_upd_upd : btupd.

Lemma pm_add_add : forall (A : Type) k (v v' : A) m,
  PositiveMap.add k v (PositiveMap.add k v' m) = PositiveMap.add k v m.
Proof.
  intros A k. induction k as [k IH|k IH|]; intros v v' m; destruct m; cbn; rewrite ?IH; reflexivity.
Qed.

Lemma arr_set_set_same : forall {A} (a : parr A) i (v v' : A), arr_set (arr_set a i v) i v' = arr_set a i v'.
Proof.
  intros A [[n d] m] i v v'. unfold arr_set. cbn.
  destruct ((0 <=? i) && (i <? n)) eqn:E; cbn; rewrite ?E; [|reflexivity].
  rewrite pm_add_add. reflexivity.
Qed.

Lemma wrap64_sub_l : forall a b, wrap64 (wrap64 a - b) = wrap64 (a - b).
Proof. intros. rewrite !wrap64_mod. rewrite Zminus_mod_idemp_l. reflexivity. Qed.
Lemma wrap64_add_l : forall a b, wrap64 (wrap64 a + b) = wrap64 (a + b).
Proof. intros. rewrite !wrap64_mod. rewrite Zplus_mod_idemp_l. reflexivity. Qed.

Lemma pqdownheap_heap_len : forall s t k, ds_heap_len (pqdownheap s t k) = ds_heap_len s.
Proof. intros. rewrite (pqdownheap_shape s t k). rewrite sh_heap_len. reflexivity. Qed.
