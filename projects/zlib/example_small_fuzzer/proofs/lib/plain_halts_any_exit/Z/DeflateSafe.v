(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.

Module RefDeflateDictM.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition sdput (s t : deflate_state) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap t) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window t) (ds_window_size s) (ds_prev t) (ds_head t) (ds_ins_h t) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start t) (ds_match_length t) (ds_prev_match s) (ds_match_available t) (ds_strstart t) (ds_match_start t) (ds_lookahead t) (ds_prev_length t) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert t) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water t) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm t).

Definition SDK (s t : deflate_state) : Prop := t = sdput s t.

Lemma sdput_self : forall s, sdput s s = s.
Proof. intros s; destruct s; reflexivity. Qed.
Lemma SDK_refl : forall s, SDK s s.
Proof. intros s. unfold SDK. symmetry. apply sdput_self. Qed.
Lemma sdput_l : forall s t u, sdput (sdput s t) u = sdput s u.
Proof. intros. reflexivity. Qed.
Lemma sdput_r : forall s t u, sdput s (sdput t u) = sdput s u.
Proof. intros. reflexivity. Qed.
Lemma SDK_trans : forall s t u, SDK s t -> SDK t u -> SDK s u.
Proof. intros s t u Ht Hu. unfold SDK in *. rewrite Hu, Ht, sdput_l, sdput_r. reflexivity. Qed.
Lemma SDK_if : forall s (b : bool) t u, SDK s t -> SDK s u -> SDK s (if b then t else u).
Proof. intros s b t u Ht Hu. destruct b; assumption. Qed.

Definition cset_ao (s : deflate_state) (v : Z) : deflate_state := set_strm s (cset_avail_out (ds_strm s) v).

Lemma SDK_wrap : forall s v, SDK s (set_wrap s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_window : forall s v, SDK s (set_window s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_prev : forall s v, SDK s (set_prev s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_head : forall s v, SDK s (set_head s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_ins_h : forall s v, SDK s (set_ins_h s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_block_start : forall s v, SDK s (set_block_start s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_match_length : forall s v, SDK s (set_match_length s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_match_available : forall s v, SDK s (set_match_available s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_strstart : forall s v, SDK s (set_strstart s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_match_start : forall s v, SDK s (set_match_start s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_lookahead : forall s v, SDK s (set_lookahead s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_prev_length : forall s v, SDK s (set_prev_length s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_insert : forall s v, SDK s (set_insert s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_high_water : forall s v, SDK s (set_high_water s v).
Proof. intros. reflexivity. Qed.
Lemma SDK_strm : forall s v, SDK s (set_strm s v).
Proof. intros. reflexivity. Qed.
Lemma cao_set_status : forall s v w, set_status (cset_ao s v) w = cset_ao (set_status s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_pending_buf : forall s v w, set_pending_buf (cset_ao s v) w = cset_ao (set_pending_buf s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_pending_buf_size : forall s v w, set_pending_buf_size (cset_ao s v) w = cset_ao (set_pending_buf_size s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_pending_out : forall s v w, set_pending_out (cset_ao s v) w = cset_ao (set_pending_out s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_pending : forall s v w, set_pending (cset_ao s v) w = cset_ao (set_pending s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_wrap : forall s v w, set_wrap (cset_ao s v) w = cset_ao (set_wrap s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_gzhead : forall s v w, set_gzhead (cset_ao s v) w = cset_ao (set_gzhead s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_gzindex : forall s v w, set_gzindex (cset_ao s v) w = cset_ao (set_gzindex s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_method : forall s v w, set_method (cset_ao s v) w = cset_ao (set_method s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_last_flush : forall s v w, set_last_flush (cset_ao s v) w = cset_ao (set_last_flush s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_w_size : forall s v w, set_w_size (cset_ao s v) w = cset_ao (set_w_size s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_w_bits : forall s v w, set_w_bits (cset_ao s v) w = cset_ao (set_w_bits s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_w_mask : forall s v w, set_w_mask (cset_ao s v) w = cset_ao (set_w_mask s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_window : forall s v w, set_window (cset_ao s v) w = cset_ao (set_window s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_window_size : forall s v w, set_window_size (cset_ao s v) w = cset_ao (set_window_size s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_prev : forall s v w, set_prev (cset_ao s v) w = cset_ao (set_prev s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_head : forall s v w, set_head (cset_ao s v) w = cset_ao (set_head s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_ins_h : forall s v w, set_ins_h (cset_ao s v) w = cset_ao (set_ins_h s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_hash_size : forall s v w, set_hash_size (cset_ao s v) w = cset_ao (set_hash_size s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_hash_bits : forall s v w, set_hash_bits (cset_ao s v) w = cset_ao (set_hash_bits s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_hash_mask : forall s v w, set_hash_mask (cset_ao s v) w = cset_ao (set_hash_mask s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_hash_shift : forall s v w, set_hash_shift (cset_ao s v) w = cset_ao (set_hash_shift s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_block_start : forall s v w, set_block_start (cset_ao s v) w = cset_ao (set_block_start s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_match_length : forall s v w, set_match_length (cset_ao s v) w = cset_ao (set_match_length s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_prev_match : forall s v w, set_prev_match (cset_ao s v) w = cset_ao (set_prev_match s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_match_available : forall s v w, set_match_available (cset_ao s v) w = cset_ao (set_match_available s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_strstart : forall s v w, set_strstart (cset_ao s v) w = cset_ao (set_strstart s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_match_start : forall s v w, set_match_start (cset_ao s v) w = cset_ao (set_match_start s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_lookahead : forall s v w, set_lookahead (cset_ao s v) w = cset_ao (set_lookahead s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_prev_length : forall s v w, set_prev_length (cset_ao s v) w = cset_ao (set_prev_length s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_max_chain_length : forall s v w, set_max_chain_length (cset_ao s v) w = cset_ao (set_max_chain_length s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_max_lazy_match : forall s v w, set_max_lazy_match (cset_ao s v) w = cset_ao (set_max_lazy_match s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_level : forall s v w, set_level (cset_ao s v) w = cset_ao (set_level s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_strategy : forall s v w, set_strategy (cset_ao s v) w = cset_ao (set_strategy s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_good_match : forall s v w, set_good_match (cset_ao s v) w = cset_ao (set_good_match s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_nice_match : forall s v w, set_nice_match (cset_ao s v) w = cset_ao (set_nice_match s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_dyn_ltree_fc : forall s v w, set_dyn_ltree_fc (cset_ao s v) w = cset_ao (set_dyn_ltree_fc s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_dyn_ltree_dl : forall s v w, set_dyn_ltree_dl (cset_ao s v) w = cset_ao (set_dyn_ltree_dl s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_dyn_dtree_fc : forall s v w, set_dyn_dtree_fc (cset_ao s v) w = cset_ao (set_dyn_dtree_fc s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_dyn_dtree_dl : forall s v w, set_dyn_dtree_dl (cset_ao s v) w = cset_ao (set_dyn_dtree_dl s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_bl_tree_fc : forall s v w, set_bl_tree_fc (cset_ao s v) w = cset_ao (set_bl_tree_fc s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_bl_tree_dl : forall s v w, set_bl_tree_dl (cset_ao s v) w = cset_ao (set_bl_tree_dl s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_l_max_code : forall s v w, set_l_max_code (cset_ao s v) w = cset_ao (set_l_max_code s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_d_max_code : forall s v w, set_d_max_code (cset_ao s v) w = cset_ao (set_d_max_code s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_bl_max_code : forall s v w, set_bl_max_code (cset_ao s v) w = cset_ao (set_bl_max_code s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_bl_count : forall s v w, set_bl_count (cset_ao s v) w = cset_ao (set_bl_count s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_heap : forall s v w, set_heap (cset_ao s v) w = cset_ao (set_heap s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_heap_len : forall s v w, set_heap_len (cset_ao s v) w = cset_ao (set_heap_len s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_heap_max : forall s v w, set_heap_max (cset_ao s v) w = cset_ao (set_heap_max s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_depth : forall s v w, set_depth (cset_ao s v) w = cset_ao (set_depth s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_lit_bufsize : forall s v w, set_lit_bufsize (cset_ao s v) w = cset_ao (set_lit_bufsize s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_sym_next : forall s v w, set_sym_next (cset_ao s v) w = cset_ao (set_sym_next s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_sym_end : forall s v w, set_sym_end (cset_ao s v) w = cset_ao (set_sym_end s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_opt_len : forall s v w, set_opt_len (cset_ao s v) w = cset_ao (set_opt_len s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_static_len : forall s v w, set_static_len (cset_ao s v) w = cset_ao (set_static_len s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_matches : forall s v w, set_matches (cset_ao s v) w = cset_ao (set_matches s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_insert : forall s v w, set_insert (cset_ao s v) w = cset_ao (set_insert s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_bi_buf : forall s v w, set_bi_buf (cset_ao s v) w = cset_ao (set_bi_buf s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_bi_valid : forall s v w, set_bi_valid (cset_ao s v) w = cset_ao (set_bi_valid s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_high_water : forall s v w, set_high_water (cset_ao s v) w = cset_ao (set_high_water s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_self_blk : forall s v w, set_self_blk (cset_ao s v) w = cset_ao (set_self_blk s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_window_blk : forall s v w, set_window_blk (cset_ao s v) w = cset_ao (set_window_blk s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_prev_blk : forall s v w, set_prev_blk (cset_ao s v) w = cset_ao (set_prev_blk s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_head_blk : forall s v w, set_head_blk (cset_ao s v) w = cset_ao (set_head_blk s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_set_pending_buf_blk : forall s v w, set_pending_buf_blk (cset_ao s v) w = cset_ao (set_pending_buf_blk s w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_status : forall s v, ds_status (cset_ao s v) = ds_status s.
Proof. intros. reflexivity. Qed.
Lemma cao_pending_buf : forall s v, ds_pending_buf (cset_ao s v) = ds_pending_buf s.
Proof. intros. reflexivity. Qed.
Lemma cao_pending_buf_size : forall s v, ds_pending_buf_size (cset_ao s v) = ds_pending_buf_size s.
Proof. intros. reflexivity. Qed.
Lemma cao_pending_out : forall s v, ds_pending_out (cset_ao s v) = ds_pending_out s.
Proof. intros. reflexivity. Qed.
Lemma cao_pending : forall s v, ds_pending (cset_ao s v) = ds_pending s.
Proof. intros. reflexivity. Qed.
Lemma cao_wrap : forall s v, ds_wrap (cset_ao s v) = ds_wrap s.
Proof. intros. reflexivity. Qed.
Lemma cao_gzhead : forall s v, ds_gzhead (cset_ao s v) = ds_gzhead s.
Proof. intros. reflexivity. Qed.
Lemma cao_gzindex : forall s v, ds_gzindex (cset_ao s v) = ds_gzindex s.
Proof. intros. reflexivity. Qed.
Lemma cao_method : forall s v, ds_method (cset_ao s v) = ds_method s.
Proof. intros. reflexivity. Qed.
Lemma cao_last_flush : forall s v, ds_last_flush (cset_ao s v) = ds_last_flush s.
Proof. intros. reflexivity. Qed.
Lemma cao_w_size : forall s v, ds_w_size (cset_ao s v) = ds_w_size s.
Proof. intros. reflexivity. Qed.
Lemma cao_w_bits : forall s v, ds_w_bits (cset_ao s v) = ds_w_bits s.
Proof. intros. reflexivity. Qed.
Lemma cao_w_mask : forall s v, ds_w_mask (cset_ao s v) = ds_w_mask s.
Proof. intros. reflexivity. Qed.
Lemma cao_window : forall s v, ds_window (cset_ao s v) = ds_window s.
Proof. intros. reflexivity. Qed.
Lemma cao_window_size : forall s v, ds_window_size (cset_ao s v) = ds_window_size s.
Proof. intros. reflexivity. Qed.
Lemma cao_prev : forall s v, ds_prev (cset_ao s v) = ds_prev s.
Proof. intros. reflexivity. Qed.
Lemma cao_head : forall s v, ds_head (cset_ao s v) = ds_head s.
Proof. intros. reflexivity. Qed.
Lemma cao_ins_h : forall s v, ds_ins_h (cset_ao s v) = ds_ins_h s.
Proof. intros. reflexivity. Qed.
Lemma cao_hash_size : forall s v, ds_hash_size (cset_ao s v) = ds_hash_size s.
Proof. intros. reflexivity. Qed.
Lemma cao_hash_bits : forall s v, ds_hash_bits (cset_ao s v) = ds_hash_bits s.
Proof. intros. reflexivity. Qed.
Lemma cao_hash_mask : forall s v, ds_hash_mask (cset_ao s v) = ds_hash_mask s.
Proof. intros. reflexivity. Qed.
Lemma cao_hash_shift : forall s v, ds_hash_shift (cset_ao s v) = ds_hash_shift s.
Proof. intros. reflexivity. Qed.
Lemma cao_block_start : forall s v, ds_block_start (cset_ao s v) = ds_block_start s.
Proof. intros. reflexivity. Qed.
Lemma cao_match_length : forall s v, ds_match_length (cset_ao s v) = ds_match_length s.
Proof. intros. reflexivity. Qed.
Lemma cao_prev_match : forall s v, ds_prev_match (cset_ao s v) = ds_prev_match s.
Proof. intros. reflexivity. Qed.
Lemma cao_match_available : forall s v, ds_match_available (cset_ao s v) = ds_match_available s.
Proof. intros. reflexivity. Qed.
Lemma cao_strstart : forall s v, ds_strstart (cset_ao s v) = ds_strstart s.
Proof. intros. reflexivity. Qed.
Lemma cao_match_start : forall s v, ds_match_start (cset_ao s v) = ds_match_start s.
Proof. intros. reflexivity. Qed.
Lemma cao_lookahead : forall s v, ds_lookahead (cset_ao s v) = ds_lookahead s.
Proof. intros. reflexivity. Qed.
Lemma cao_prev_length : forall s v, ds_prev_length (cset_ao s v) = ds_prev_length s.
Proof. intros. reflexivity. Qed.
Lemma cao_max_chain_length : forall s v, ds_max_chain_length (cset_ao s v) = ds_max_chain_length s.
Proof. intros. reflexivity. Qed.
Lemma cao_max_lazy_match : forall s v, ds_max_lazy_match (cset_ao s v) = ds_max_lazy_match s.
Proof. intros. reflexivity. Qed.
Lemma cao_level : forall s v, ds_level (cset_ao s v) = ds_level s.
Proof. intros. reflexivity. Qed.
Lemma cao_strategy : forall s v, ds_strategy (cset_ao s v) = ds_strategy s.
Proof. intros. reflexivity. Qed.
Lemma cao_good_match : forall s v, ds_good_match (cset_ao s v) = ds_good_match s.
Proof. intros. reflexivity. Qed.
Lemma cao_nice_match : forall s v, ds_nice_match (cset_ao s v) = ds_nice_match s.
Proof. intros. reflexivity. Qed.
Lemma cao_dyn_ltree_fc : forall s v, ds_dyn_ltree_fc (cset_ao s v) = ds_dyn_ltree_fc s.
Proof. intros. reflexivity. Qed.
Lemma cao_dyn_ltree_dl : forall s v, ds_dyn_ltree_dl (cset_ao s v) = ds_dyn_ltree_dl s.
Proof. intros. reflexivity. Qed.
Lemma cao_dyn_dtree_fc : forall s v, ds_dyn_dtree_fc (cset_ao s v) = ds_dyn_dtree_fc s.
Proof. intros. reflexivity. Qed.
Lemma cao_dyn_dtree_dl : forall s v, ds_dyn_dtree_dl (cset_ao s v) = ds_dyn_dtree_dl s.
Proof. intros. reflexivity. Qed.
Lemma cao_bl_tree_fc : forall s v, ds_bl_tree_fc (cset_ao s v) = ds_bl_tree_fc s.
Proof. intros. reflexivity. Qed.
Lemma cao_bl_tree_dl : forall s v, ds_bl_tree_dl (cset_ao s v) = ds_bl_tree_dl s.
Proof. intros. reflexivity. Qed.
Lemma cao_l_max_code : forall s v, ds_l_max_code (cset_ao s v) = ds_l_max_code s.
Proof. intros. reflexivity. Qed.
Lemma cao_d_max_code : forall s v, ds_d_max_code (cset_ao s v) = ds_d_max_code s.
Proof. intros. reflexivity. Qed.
Lemma cao_bl_max_code : forall s v, ds_bl_max_code (cset_ao s v) = ds_bl_max_code s.
Proof. intros. reflexivity. Qed.
Lemma cao_bl_count : forall s v, ds_bl_count (cset_ao s v) = ds_bl_count s.
Proof. intros. reflexivity. Qed.
Lemma cao_heap : forall s v, ds_heap (cset_ao s v) = ds_heap s.
Proof. intros. reflexivity. Qed.
Lemma cao_heap_len : forall s v, ds_heap_len (cset_ao s v) = ds_heap_len s.
Proof. intros. reflexivity. Qed.
Lemma cao_heap_max : forall s v, ds_heap_max (cset_ao s v) = ds_heap_max s.
Proof. intros. reflexivity. Qed.
Lemma cao_depth : forall s v, ds_depth (cset_ao s v) = ds_depth s.
Proof. intros. reflexivity. Qed.
Lemma cao_lit_bufsize : forall s v, ds_lit_bufsize (cset_ao s v) = ds_lit_bufsize s.
Proof. intros. reflexivity. Qed.
Lemma cao_sym_next : forall s v, ds_sym_next (cset_ao s v) = ds_sym_next s.
Proof. intros. reflexivity. Qed.
Lemma cao_sym_end : forall s v, ds_sym_end (cset_ao s v) = ds_sym_end s.
Proof. intros. reflexivity. Qed.
Lemma cao_opt_len : forall s v, ds_opt_len (cset_ao s v) = ds_opt_len s.
Proof. intros. reflexivity. Qed.
Lemma cao_static_len : forall s v, ds_static_len (cset_ao s v) = ds_static_len s.
Proof. intros. reflexivity. Qed.
Lemma cao_matches : forall s v, ds_matches (cset_ao s v) = ds_matches s.
Proof. intros. reflexivity. Qed.
Lemma cao_insert : forall s v, ds_insert (cset_ao s v) = ds_insert s.
Proof. intros. reflexivity. Qed.
Lemma cao_bi_buf : forall s v, ds_bi_buf (cset_ao s v) = ds_bi_buf s.
Proof. intros. reflexivity. Qed.
Lemma cao_bi_valid : forall s v, ds_bi_valid (cset_ao s v) = ds_bi_valid s.
Proof. intros. reflexivity. Qed.
Lemma cao_high_water : forall s v, ds_high_water (cset_ao s v) = ds_high_water s.
Proof. intros. reflexivity. Qed.
Lemma cao_self_blk : forall s v, ds_self_blk (cset_ao s v) = ds_self_blk s.
Proof. intros. reflexivity. Qed.
Lemma cao_window_blk : forall s v, ds_window_blk (cset_ao s v) = ds_window_blk s.
Proof. intros. reflexivity. Qed.
Lemma cao_prev_blk : forall s v, ds_prev_blk (cset_ao s v) = ds_prev_blk s.
Proof. intros. reflexivity. Qed.
Lemma cao_head_blk : forall s v, ds_head_blk (cset_ao s v) = ds_head_blk s.
Proof. intros. reflexivity. Qed.
Lemma cao_pending_buf_blk : forall s v, ds_pending_buf_blk (cset_ao s v) = ds_pending_buf_blk s.
Proof. intros. reflexivity. Qed.
Lemma cao_strm : forall s v, ds_strm (cset_ao s v) = cset_avail_out (ds_strm s) v.
Proof. intros. reflexivity. Qed.
Lemma cao_cs_input : forall st v, cs_input (cset_avail_out st v) = cs_input st.
Proof. intros. reflexivity. Qed.
Lemma cao_cset_input : forall st v w, cset_input (cset_avail_out st v) w = cset_avail_out (cset_input st w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_cs_next_in : forall st v, cs_next_in (cset_avail_out st v) = cs_next_in st.
Proof. intros. reflexivity. Qed.
Lemma cao_cset_next_in : forall st v w, cset_next_in (cset_avail_out st v) w = cset_avail_out (cset_next_in st w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_cs_avail_in : forall st v, cs_avail_in (cset_avail_out st v) = cs_avail_in st.
Proof. intros. reflexivity. Qed.
Lemma cao_cset_avail_in : forall st v w, cset_avail_in (cset_avail_out st v) w = cset_avail_out (cset_avail_in st w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_cs_out_rev : forall st v, cs_out_rev (cset_avail_out st v) = cs_out_rev st.
Proof. intros. reflexivity. Qed.
Lemma cao_cset_out_rev : forall st v w, cset_out_rev (cset_avail_out st v) w = cset_avail_out (cset_out_rev st w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_cs_total_in : forall st v, cs_total_in (cset_avail_out st v) = cs_total_in st.
Proof. intros. reflexivity. Qed.
Lemma cao_cset_total_in : forall st v w, cset_total_in (cset_avail_out st v) w = cset_avail_out (cset_total_in st w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_cs_total_out : forall st v, cs_total_out (cset_avail_out st v) = cs_total_out st.
Proof. intros. reflexivity. Qed.
Lemma cao_cset_total_out : forall st v w, cset_total_out (cset_avail_out st v) w = cset_avail_out (cset_total_out st w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_cs_msg : forall st v, cs_msg (cset_avail_out st v) = cs_msg st.
Proof. intros. reflexivity. Qed.
Lemma cao_cset_msg : forall st v w, cset_msg (cset_avail_out st v) w = cset_avail_out (cset_msg st w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_cs_data_type : forall st v, cs_data_type (cset_avail_out st v) = cs_data_type st.
Proof. intros. reflexivity. Qed.
Lemma cao_cset_data_type : forall st v w, cset_data_type (cset_avail_out st v) w = cset_avail_out (cset_data_type st w) v.
Proof. intros. reflexivity. Qed.
Lemma cao_cs_adler : forall st v, cs_adler (cset_avail_out st v) = cs_adler st.
Proof. intros. reflexivity. Qed.
Lemma cao_cset_adler : forall st v w, cset_adler (cset_avail_out st v) w = cset_avail_out (cset_adler st w) v.
Proof. intros. reflexivity. Qed.





Lemma set_strm_cao : forall s v st, set_strm (cset_ao s v) (cset_avail_out st v) = cset_ao (set_strm s st) v.
Proof. intros. reflexivity. Qed.
Lemma update_hash_cao : forall s v h c, update_hash (cset_ao s v) h c = update_hash s h c.
Proof. intros. reflexivity. Qed.
Lemma deflateStateCheck_cao : forall s v, deflateStateCheck (cset_ao s v) = deflateStateCheck s.
Proof. intros. reflexivity. Qed.


Lemma slide_hash_SDK : forall s, SDK s (slide_hash s).
Proof. intros s. unfold slide_hash. eapply SDK_trans; [apply SDK_head | apply SDK_prev]. Qed.

Lemma clear_hash_SDK : forall s, SDK s (clear_hash s).
Proof. intros s. unfold clear_hash. eapply SDK_trans; [apply SDK_head | apply SDK_head]. Qed.

Ltac sdk1 :=
  lazymatch goal with
  | |- SDK ?s ?s => apply SDK_refl
  | |- SDK ?s (if ?b then _ else _) => apply SDK_if
  | |- SDK ?s (set_wrap ?t ?v) => apply (SDK_trans s t); [| apply SDK_wrap]
  | |- SDK ?s (set_window ?t ?v) => apply (SDK_trans s t); [| apply SDK_window]
  | |- SDK ?s (set_prev ?t ?v) => apply (SDK_trans s t); [| apply SDK_prev]
  | |- SDK ?s (set_head ?t ?v) => apply (SDK_trans s t); [| apply SDK_head]
  | |- SDK ?s (set_ins_h ?t ?v) => apply (SDK_trans s t); [| apply SDK_ins_h]
  | |- SDK ?s (set_block_start ?t ?v) => apply (SDK_trans s t); [| apply SDK_block_start]
  | |- SDK ?s (set_match_length ?t ?v) => apply (SDK_trans s t); [| apply SDK_match_length]
  | |- SDK ?s (set_match_available ?t ?v) => apply (SDK_trans s t); [| apply SDK_match_available]
  | |- SDK ?s (set_strstart ?t ?v) => apply (SDK_trans s t); [| apply SDK_strstart]
  | |- SDK ?s (set_match_start ?t ?v) => apply (SDK_trans s t); [| apply SDK_match_start]
  | |- SDK ?s (set_lookahead ?t ?v) => apply (SDK_trans s t); [| apply SDK_lookahead]
  | |- SDK ?s (set_prev_length ?t ?v) => apply (SDK_trans s t); [| apply SDK_prev_length]
  | |- SDK ?s (set_insert ?t ?v) => apply (SDK_trans s t); [| apply SDK_insert]
  | |- SDK ?s (set_high_water ?t ?v) => apply (SDK_trans s t); [| apply SDK_high_water]
  | |- SDK ?s (set_strm ?t ?v) => apply (SDK_trans s t); [| apply SDK_strm]
  | |- SDK ?s (slide_hash ?t) => apply (SDK_trans s t); [| apply slide_hash_SDK]
  | |- SDK ?s (clear_hash ?t) => apply (SDK_trans s t); [| apply clear_hash_SDK]
  end.
Ltac sdk := repeat sdk1.

Lemma read_buf_SDK : forall s off more, SDK s (fst (read_buf s (RB_window off) more)).
Proof.
  intros s off more. unfold read_buf. cbv zeta.
  destruct (_ =? 0); [apply SDK_refl|]. cbn [fst]. sdk.
Qed.

Lemma fill_window_insert_SDK : forall n s str, SDK s (fill_window_insert n s str).
Proof.
  induction n as [|n IH]; intros s str; cbn [fill_window_insert]; [apply SDK_refl|].
  destruct (negb _); [|apply SDK_refl]. cbv zeta.
  destruct (_ <? _); [sdk|].
  match goal with |- SDK _ (fill_window_insert _ ?t _) => apply (SDK_trans s t); [sdk | apply IH] end.
Qed.

Lemma fill_window_body_SDK : forall s ws, SDK s (fst (fill_window_body s ws)).
Proof.
  intros s ws. unfold fill_window_body. cbv zeta.
  destruct (_ <=? ds_strstart s).
  - destruct (cs_avail_in _ =? 0); [cbn [fst]; sdk|].
    match goal with |- SDK _ (fst (let '(a, b) := read_buf ?t (RB_window ?off) ?m in _)) =>
      pose proof (read_buf_SDK t off m) as HR; destruct (read_buf t (RB_window off) m) as [s2 n] end.
    cbn [fst] in *. apply (SDK_trans s s2); [lazymatch type of HR with SDK ?t _ => apply (SDK_trans s t s2); [sdk | exact HR] end|].
    sdk. match goal with |- SDK _ (fill_window_insert ?k ?t ?str) => apply (SDK_trans s2 t); [sdk | apply fill_window_insert_SDK] end.
  - destruct (cs_avail_in _ =? 0); [cbn [fst]; sdk|].
    match goal with |- SDK _ (fst (let '(a, b) := read_buf ?t (RB_window ?off) ?m in _)) =>
      pose proof (read_buf_SDK t off m) as HR; destruct (read_buf t (RB_window off) m) as [s2 n] end.
    cbn [fst] in *. apply (SDK_trans s s2); [exact HR|].
    sdk. match goal with |- SDK _ (fill_window_insert ?k ?t ?str) => apply (SDK_trans s2 t); [sdk | apply fill_window_insert_SDK] end.
Qed.

Lemma fill_window_loop_SDK : forall f s ws, SDK s (fill_window_loop f s ws).
Proof.
  induction f as [|f IH]; intros s ws; cbn [fill_window_loop]; [apply SDK_refl|].
  pose proof (fill_window_body_SDK s ws) as HB. destruct (fill_window_body s ws) as [s1 brk]. cbn [fst] in HB.
  destruct brk; [exact HB|]. destruct (_ && _); [|exact HB].
  apply (SDK_trans s s1); [exact HB | apply IH].
Qed.

Lemma fill_window_high_SDK : forall s, SDK s (fill_window_high s).
Proof.
  intros s. unfold fill_window_high. cbv zeta.
  destruct (_ <? ds_window_size s); [|apply SDK_refl].
  destruct (_ <? ds_strstart s + ds_lookahead s); [sdk|].
  destruct (_ <? _); [sdk | apply SDK_refl].
Qed.

Lemma fill_window_SDK : forall s, SDK s (fill_window s).
Proof.
  intros s. unfold fill_window. cbv zeta.
  eapply SDK_trans; [apply fill_window_loop_SDK | apply fill_window_high_SDK].
Qed.

Lemma setdict_inner_SDK : forall f s str n, SDK s (fst (setdict_inner f s str n)).
Proof.
  induction f as [|f IH]; intros s str n; cbn [setdict_inner]; [apply SDK_refl|]. cbv zeta.
  destruct (negb _).
  - match goal with |- SDK _ (fst (setdict_inner _ ?t ?a ?b)) => apply (SDK_trans s t); [sdk | apply IH] end.
  - cbn [fst]. sdk.
Qed.

Lemma setdict_outer_SDK : forall f s, SDK s (setdict_outer f s).
Proof.
  induction f as [|f IH]; intros s; cbn [setdict_outer]; [apply SDK_refl|]. cbv zeta.
  destruct (_ <=? _); [|apply SDK_refl].
  pose proof (setdict_inner_SDK (Z.to_nat (ds_lookahead s - (MIN_MATCH - 1))) s (ds_strstart s) (ds_lookahead s - (MIN_MATCH - 1))) as HI.
  destruct (setdict_inner _ s _ _) as [s1 str1]. cbn [fst] in HI.
  eapply SDK_trans; [| apply IH]. eapply SDK_trans; [| apply fill_window_SDK]. sdk. exact HI.
Qed.



Lemma slide_hash_cao : forall s v, slide_hash (cset_ao s v) = cset_ao (slide_hash s) v.
Proof. intros. reflexivity. Qed.
Lemma clear_hash_cao : forall s v, clear_hash (cset_ao s v) = cset_ao (clear_hash s) v.
Proof. intros. reflexivity. Qed.


Ltac cao1 :=
  match goal with
  | |- context [ds_status (cset_ao ?s ?v)] => rewrite (cao_status s v)
  | |- context [ds_pending_buf (cset_ao ?s ?v)] => rewrite (cao_pending_buf s v)
  | |- context [ds_pending_buf_size (cset_ao ?s ?v)] => rewrite (cao_pending_buf_size s v)
  | |- context [ds_pending_out (cset_ao ?s ?v)] => rewrite (cao_pending_out s v)
  | |- context [ds_pending (cset_ao ?s ?v)] => rewrite (cao_pending s v)
  | |- context [ds_wrap (cset_ao ?s ?v)] => rewrite (cao_wrap s v)
  | |- context [ds_gzhead (cset_ao ?s ?v)] => rewrite (cao_gzhead s v)
  | |- context [ds_gzindex (cset_ao ?s ?v)] => rewrite (cao_gzindex s v)
  | |- context [ds_method (cset_ao ?s ?v)] => rewrite (cao_method s v)
  | |- context [ds_last_flush (cset_ao ?s ?v)] => rewrite (cao_last_flush s v)
  | |- context [ds_w_size (cset_ao ?s ?v)] => rewrite (cao_w_size s v)
  | |- context [ds_w_bits (cset_ao ?s ?v)] => rewrite (cao_w_bits s v)
  | |- context [ds_w_mask (cset_ao ?s ?v)] => rewrite (cao_w_mask s v)
  | |- context [ds_window (cset_ao ?s ?v)] => rewrite (cao_window s v)
  | |- context [ds_window_size (cset_ao ?s ?v)] => rewrite (cao_window_size s v)
  | |- context [ds_prev (cset_ao ?s ?v)] => rewrite (cao_prev s v)
  | |- context [ds_head (cset_ao ?s ?v)] => rewrite (cao_head s v)
  | |- context [ds_ins_h (cset_ao ?s ?v)] => rewrite (cao_ins_h s v)
  | |- context [ds_hash_size (cset_ao ?s ?v)] => rewrite (cao_hash_size s v)
  | |- context [ds_hash_bits (cset_ao ?s ?v)] => rewrite (cao_hash_bits s v)
  | |- context [ds_hash_mask (cset_ao ?s ?v)] => rewrite (cao_hash_mask s v)
  | |- context [ds_hash_shift (cset_ao ?s ?v)] => rewrite (cao_hash_shift s v)
  | |- context [ds_block_start (cset_ao ?s ?v)] => rewrite (cao_block_start s v)
  | |- context [ds_match_length (cset_ao ?s ?v)] => rewrite (cao_match_length s v)
  | |- context [ds_prev_match (cset_ao ?s ?v)] => rewrite (cao_prev_match s v)
  | |- context [ds_match_available (cset_ao ?s ?v)] => rewrite (cao_match_available s v)
  | |- context [ds_strstart (cset_ao ?s ?v)] => rewrite (cao_strstart s v)
  | |- context [ds_match_start (cset_ao ?s ?v)] => rewrite (cao_match_start s v)
  | |- context [ds_lookahead (cset_ao ?s ?v)] => rewrite (cao_lookahead s v)
  | |- context [ds_prev_length (cset_ao ?s ?v)] => rewrite (cao_prev_length s v)
  | |- context [ds_max_chain_length (cset_ao ?s ?v)] => rewrite (cao_max_chain_length s v)
  | |- context [ds_max_lazy_match (cset_ao ?s ?v)] => rewrite (cao_max_lazy_match s v)
  | |- context [ds_level (cset_ao ?s ?v)] => rewrite (cao_level s v)
  | |- context [ds_strategy (cset_ao ?s ?v)] => rewrite (cao_strategy s v)
  | |- context [ds_good_match (cset_ao ?s ?v)] => rewrite (cao_good_match s v)
  | |- context [ds_nice_match (cset_ao ?s ?v)] => rewrite (cao_nice_match s v)
  | |- context [ds_dyn_ltree_fc (cset_ao ?s ?v)] => rewrite (cao_dyn_ltree_fc s v)
  | |- context [ds_dyn_ltree_dl (cset_ao ?s ?v)] => rewrite (cao_dyn_ltree_dl s v)
  | |- context [ds_dyn_dtree_fc (cset_ao ?s ?v)] => rewrite (cao_dyn_dtree_fc s v)
  | |- context [ds_dyn_dtree_dl (cset_ao ?s ?v)] => rewrite (cao_dyn_dtree_dl s v)
  | |- context [ds_bl_tree_fc (cset_ao ?s ?v)] => rewrite (cao_bl_tree_fc s v)
  | |- context [ds_bl_tree_dl (cset_ao ?s ?v)] => rewrite (cao_bl_tree_dl s v)
  | |- context [ds_l_max_code (cset_ao ?s ?v)] => rewrite (cao_l_max_code s v)
  | |- context [ds_d_max_code (cset_ao ?s ?v)] => rewrite (cao_d_max_code s v)
  | |- context [ds_bl_max_code (cset_ao ?s ?v)] => rewrite (cao_bl_max_code s v)
  | |- context [ds_bl_count (cset_ao ?s ?v)] => rewrite (cao_bl_count s v)
  | |- context [ds_heap (cset_ao ?s ?v)] => rewrite (cao_heap s v)
  | |- context [ds_heap_len (cset_ao ?s ?v)] => rewrite (cao_heap_len s v)
  | |- context [ds_heap_max (cset_ao ?s ?v)] => rewrite (cao_heap_max s v)
  | |- context [ds_depth (cset_ao ?s ?v)] => rewrite (cao_depth s v)
  | |- context [ds_lit_bufsize (cset_ao ?s ?v)] => rewrite (cao_lit_bufsize s v)
  | |- context [ds_sym_next (cset_ao ?s ?v)] => rewrite (cao_sym_next s v)
  | |- context [ds_sym_end (cset_ao ?s ?v)] => rewrite (cao_sym_end s v)
  | |- context [ds_opt_len (cset_ao ?s ?v)] => rewrite (cao_opt_len s v)
  | |- context [ds_static_len (cset_ao ?s ?v)] => rewrite (cao_static_len s v)
  | |- context [ds_matches (cset_ao ?s ?v)] => rewrite (cao_matches s v)
  | |- context [ds_insert (cset_ao ?s ?v)] => rewrite (cao_insert s v)
  | |- context [ds_bi_buf (cset_ao ?s ?v)] => rewrite (cao_bi_buf s v)
  | |- context [ds_bi_valid (cset_ao ?s ?v)] => rewrite (cao_bi_valid s v)
  | |- context [ds_high_water (cset_ao ?s ?v)] => rewrite (cao_high_water s v)
  | |- context [ds_self_blk (cset_ao ?s ?v)] => rewrite (cao_self_blk s v)
  | |- context [ds_window_blk (cset_ao ?s ?v)] => rewrite (cao_window_blk s v)
  | |- context [ds_prev_blk (cset_ao ?s ?v)] => rewrite (cao_prev_blk s v)
  | |- context [ds_head_blk (cset_ao ?s ?v)] => rewrite (cao_head_blk s v)
  | |- context [ds_pending_buf_blk (cset_ao ?s ?v)] => rewrite (cao_pending_buf_blk s v)
  | |- context [ds_strm (cset_ao ?s ?v)] => rewrite (cao_strm s v)
  | |- context [cs_input (cset_avail_out ?st ?v)] => rewrite (cao_cs_input st v)
  | |- context [cs_next_in (cset_avail_out ?st ?v)] => rewrite (cao_cs_next_in st v)
  | |- context [cs_avail_in (cset_avail_out ?st ?v)] => rewrite (cao_cs_avail_in st v)
  | |- context [cs_out_rev (cset_avail_out ?st ?v)] => rewrite (cao_cs_out_rev st v)
  | |- context [cs_total_in (cset_avail_out ?st ?v)] => rewrite (cao_cs_total_in st v)
  | |- context [cs_total_out (cset_avail_out ?st ?v)] => rewrite (cao_cs_total_out st v)
  | |- context [cs_msg (cset_avail_out ?st ?v)] => rewrite (cao_cs_msg st v)
  | |- context [cs_data_type (cset_avail_out ?st ?v)] => rewrite (cao_cs_data_type st v)
  | |- context [cs_adler (cset_avail_out ?st ?v)] => rewrite (cao_cs_adler st v)
  | |- context [set_status (cset_ao ?s ?v) ?w] => rewrite (cao_set_status s v w)
  | |- context [set_pending_buf (cset_ao ?s ?v) ?w] => rewrite (cao_set_pending_buf s v w)
  | |- context [set_pending_buf_size (cset_ao ?s ?v) ?w] => rewrite (cao_set_pending_buf_size s v w)
  | |- context [set_pending_out (cset_ao ?s ?v) ?w] => rewrite (cao_set_pending_out s v w)
  | |- context [set_pending (cset_ao ?s ?v) ?w] => rewrite (cao_set_pending s v w)
  | |- context [set_wrap (cset_ao ?s ?v) ?w] => rewrite (cao_set_wrap s v w)
  | |- context [set_gzhead (cset_ao ?s ?v) ?w] => rewrite (cao_set_gzhead s v w)
  | |- context [set_gzindex (cset_ao ?s ?v) ?w] => rewrite (cao_set_gzindex s v w)
  | |- context [set_method (cset_ao ?s ?v) ?w] => rewrite (cao_set_method s v w)
  | |- context [set_last_flush (cset_ao ?s ?v) ?w] => rewrite (cao_set_last_flush s v w)
  | |- context [set_w_size (cset_ao ?s ?v) ?w] => rewrite (cao_set_w_size s v w)
  | |- context [set_w_bits (cset_ao ?s ?v) ?w] => rewrite (cao_set_w_bits s v w)
  | |- context [set_w_mask (cset_ao ?s ?v) ?w] => rewrite (cao_set_w_mask s v w)
  | |- context [set_window (cset_ao ?s ?v) ?w] => rewrite (cao_set_window s v w)
  | |- context [set_window_size (cset_ao ?s ?v) ?w] => rewrite (cao_set_window_size s v w)
  | |- context [set_prev (cset_ao ?s ?v) ?w] => rewrite (cao_set_prev s v w)
  | |- context [set_head (cset_ao ?s ?v) ?w] => rewrite (cao_set_head s v w)
  | |- context [set_ins_h (cset_ao ?s ?v) ?w] => rewrite (cao_set_ins_h s v w)
  | |- context [set_hash_size (cset_ao ?s ?v) ?w] => rewrite (cao_set_hash_size s v w)
  | |- context [set_hash_bits (cset_ao ?s ?v) ?w] => rewrite (cao_set_hash_bits s v w)
  | |- context [set_hash_mask (cset_ao ?s ?v) ?w] => rewrite (cao_set_hash_mask s v w)
  | |- context [set_hash_shift (cset_ao ?s ?v) ?w] => rewrite (cao_set_hash_shift s v w)
  | |- context [set_block_start (cset_ao ?s ?v) ?w] => rewrite (cao_set_block_start s v w)
  | |- context [set_match_length (cset_ao ?s ?v) ?w] => rewrite (cao_set_match_length s v w)
  | |- context [set_prev_match (cset_ao ?s ?v) ?w] => rewrite (cao_set_prev_match s v w)
  | |- context [set_match_available (cset_ao ?s ?v) ?w] => rewrite (cao_set_match_available s v w)
  | |- context [set_strstart (cset_ao ?s ?v) ?w] => rewrite (cao_set_strstart s v w)
  | |- context [set_match_start (cset_ao ?s ?v) ?w] => rewrite (cao_set_match_start s v w)
  | |- context [set_lookahead (cset_ao ?s ?v) ?w] => rewrite (cao_set_lookahead s v w)
  | |- context [set_prev_length (cset_ao ?s ?v) ?w] => rewrite (cao_set_prev_length s v w)
  | |- context [set_max_chain_length (cset_ao ?s ?v) ?w] => rewrite (cao_set_max_chain_length s v w)
  | |- context [set_max_lazy_match (cset_ao ?s ?v) ?w] => rewrite (cao_set_max_lazy_match s v w)
  | |- context [set_level (cset_ao ?s ?v) ?w] => rewrite (cao_set_level s v w)
  | |- context [set_strategy (cset_ao ?s ?v) ?w] => rewrite (cao_set_strategy s v w)
  | |- context [set_good_match (cset_ao ?s ?v) ?w] => rewrite (cao_set_good_match s v w)
  | |- context [set_nice_match (cset_ao ?s ?v) ?w] => rewrite (cao_set_nice_match s v w)
  | |- context [set_dyn_ltree_fc (cset_ao ?s ?v) ?w] => rewrite (cao_set_dyn_ltree_fc s v w)
  | |- context [set_dyn_ltree_dl (cset_ao ?s ?v) ?w] => rewrite (cao_set_dyn_ltree_dl s v w)
  | |- context [set_dyn_dtree_fc (cset_ao ?s ?v) ?w] => rewrite (cao_set_dyn_dtree_fc s v w)
  | |- context [set_dyn_dtree_dl (cset_ao ?s ?v) ?w] => rewrite (cao_set_dyn_dtree_dl s v w)
  | |- context [set_bl_tree_fc (cset_ao ?s ?v) ?w] => rewrite (cao_set_bl_tree_fc s v w)
  | |- context [set_bl_tree_dl (cset_ao ?s ?v) ?w] => rewrite (cao_set_bl_tree_dl s v w)
  | |- context [set_l_max_code (cset_ao ?s ?v) ?w] => rewrite (cao_set_l_max_code s v w)
  | |- context [set_d_max_code (cset_ao ?s ?v) ?w] => rewrite (cao_set_d_max_code s v w)
  | |- context [set_bl_max_code (cset_ao ?s ?v) ?w] => rewrite (cao_set_bl_max_code s v w)
  | |- context [set_bl_count (cset_ao ?s ?v) ?w] => rewrite (cao_set_bl_count s v w)
  | |- context [set_heap (cset_ao ?s ?v) ?w] => rewrite (cao_set_heap s v w)
  | |- context [set_heap_len (cset_ao ?s ?v) ?w] => rewrite (cao_set_heap_len s v w)
  | |- context [set_heap_max (cset_ao ?s ?v) ?w] => rewrite (cao_set_heap_max s v w)
  | |- context [set_depth (cset_ao ?s ?v) ?w] => rewrite (cao_set_depth s v w)
  | |- context [set_lit_bufsize (cset_ao ?s ?v) ?w] => rewrite (cao_set_lit_bufsize s v w)
  | |- context [set_sym_next (cset_ao ?s ?v) ?w] => rewrite (cao_set_sym_next s v w)
  | |- context [set_sym_end (cset_ao ?s ?v) ?w] => rewrite (cao_set_sym_end s v w)
  | |- context [set_opt_len (cset_ao ?s ?v) ?w] => rewrite (cao_set_opt_len s v w)
  | |- context [set_static_len (cset_ao ?s ?v) ?w] => rewrite (cao_set_static_len s v w)
  | |- context [set_matches (cset_ao ?s ?v) ?w] => rewrite (cao_set_matches s v w)
  | |- context [set_insert (cset_ao ?s ?v) ?w] => rewrite (cao_set_insert s v w)
  | |- context [set_bi_buf (cset_ao ?s ?v) ?w] => rewrite (cao_set_bi_buf s v w)
  | |- context [set_bi_valid (cset_ao ?s ?v) ?w] => rewrite (cao_set_bi_valid s v w)
  | |- context [set_high_water (cset_ao ?s ?v) ?w] => rewrite (cao_set_high_water s v w)
  | |- context [set_self_blk (cset_ao ?s ?v) ?w] => rewrite (cao_set_self_blk s v w)
  | |- context [set_window_blk (cset_ao ?s ?v) ?w] => rewrite (cao_set_window_blk s v w)
  | |- context [set_prev_blk (cset_ao ?s ?v) ?w] => rewrite (cao_set_prev_blk s v w)
  | |- context [set_head_blk (cset_ao ?s ?v) ?w] => rewrite (cao_set_head_blk s v w)
  | |- context [set_pending_buf_blk (cset_ao ?s ?v) ?w] => rewrite (cao_set_pending_buf_blk s v w)
  | |- context [cset_input (cset_avail_out ?st ?v) ?w] => rewrite (cao_cset_input st v w)
  | |- context [cset_next_in (cset_avail_out ?st ?v) ?w] => rewrite (cao_cset_next_in st v w)
  | |- context [cset_avail_in (cset_avail_out ?st ?v) ?w] => rewrite (cao_cset_avail_in st v w)
  | |- context [cset_out_rev (cset_avail_out ?st ?v) ?w] => rewrite (cao_cset_out_rev st v w)
  | |- context [cset_total_in (cset_avail_out ?st ?v) ?w] => rewrite (cao_cset_total_in st v w)
  | |- context [cset_total_out (cset_avail_out ?st ?v) ?w] => rewrite (cao_cset_total_out st v w)
  | |- context [cset_msg (cset_avail_out ?st ?v) ?w] => rewrite (cao_cset_msg st v w)
  | |- context [cset_data_type (cset_avail_out ?st ?v) ?w] => rewrite (cao_cset_data_type st v w)
  | |- context [cset_adler (cset_avail_out ?st ?v) ?w] => rewrite (cao_cset_adler st v w)
  | |- context [set_strm (cset_ao ?s ?v) (cset_avail_out ?st ?v)] => rewrite (set_strm_cao s v st)
  | |- context [update_hash (cset_ao ?s ?v) ?h ?c] => rewrite (update_hash_cao s v h c)
  | |- context [deflateStateCheck (cset_ao ?s ?v)] => rewrite (deflateStateCheck_cao s v)
  | |- context [slide_hash (cset_ao ?s ?v)] => rewrite (slide_hash_cao s v)
  | |- context [clear_hash (cset_ao ?s ?v)] => rewrite (clear_hash_cao s v)
  end.
Ltac cao := repeat cao1.




Lemma read_buf_cao : forall s v off more,
  read_buf (cset_ao s v) (RB_window off) more
  = (cset_ao (fst (read_buf s (RB_window off) more)) v, snd (read_buf s (RB_window off) more)).
Proof.
  intros s v off more. unfold read_buf. cbv zeta. cao.
  destruct (_ =? 0); [reflexivity|]. cbn [fst snd]. cao.
  destruct (ds_wrap _ =? 1); [cao; reflexivity|].
  destruct (ds_wrap _ =? 2); cao; reflexivity.
Qed.

Lemma fill_window_insert_cao : forall n s v str,
  fill_window_insert n (cset_ao s v) str = cset_ao (fill_window_insert n s str) v.
Proof.
  induction n as [|n IH]; intros s v str; cbn [fill_window_insert]; [reflexivity|].
  cao. destruct (negb _); [|reflexivity]. cbv zeta. cao.
  destruct (_ <? _); [reflexivity|]. apply IH.
Qed.

Lemma fill_window_body_cao : forall s v ws,
  fill_window_body (cset_ao s v) ws
  = (cset_ao (fst (fill_window_body s ws)) v, snd (fill_window_body s ws)).
Proof.
  intros s v ws. unfold fill_window_body. cbv zeta. cao.
  destruct (_ <=? ds_strstart s).
  - destruct (ds_strstart _ <? ds_insert _); cao.
    + destruct (cs_avail_in _ =? 0); [reflexivity|].
      rewrite read_buf_cao. destruct (read_buf _ (RB_window _) _) as [s2 n]. cbn [fst snd]. cao.
      destruct (_ <=? _); [| reflexivity]. rewrite fill_window_insert_cao. reflexivity.
    + destruct (cs_avail_in _ =? 0); [reflexivity|].
      rewrite read_buf_cao. destruct (read_buf _ (RB_window _) _) as [s2 n]. cbn [fst snd]. cao.
      destruct (_ <=? _); [| reflexivity]. rewrite fill_window_insert_cao. reflexivity.
  - destruct (cs_avail_in _ =? 0); [reflexivity|].
    rewrite read_buf_cao. destruct (read_buf _ (RB_window _) _) as [s2 n]. cbn [fst snd]. cao.
    destruct (_ <=? _); [| reflexivity]. rewrite fill_window_insert_cao. reflexivity.
Qed.

Lemma fill_window_loop_cao : forall f s v ws,
  fill_window_loop f (cset_ao s v) ws = cset_ao (fill_window_loop f s ws) v.
Proof.
  induction f as [|f IH]; intros s v ws; cbn [fill_window_loop]; [reflexivity|].
  rewrite fill_window_body_cao. destruct (fill_window_body s ws) as [s1 brk]. cbn [fst snd].
  destruct brk; [reflexivity|]. cao. destruct (_ && _); [apply IH | reflexivity].
Qed.

Lemma fill_window_high_cao : forall s v, fill_window_high (cset_ao s v) = cset_ao (fill_window_high s) v.
Proof.
  intros s v. unfold fill_window_high. cbv zeta. cao.
  destruct (_ <? ds_window_size s); [|reflexivity].
  destruct (_ <? ds_strstart s + ds_lookahead s); [reflexivity|].
  destruct (_ <? _); reflexivity.
Qed.

Lemma fill_window_cao : forall s v, fill_window (cset_ao s v) = cset_ao (fill_window s) v.
Proof.
  intros s v. unfold fill_window. cbv zeta. cao. rewrite fill_window_loop_cao. apply fill_window_high_cao.
Qed.

Lemma setdict_inner_cao : forall f s v str n,
  setdict_inner f (cset_ao s v) str n = (cset_ao (fst (setdict_inner f s str n)) v, snd (setdict_inner f s str n)).
Proof.
  induction f as [|f IH]; intros s v str n; cbn [setdict_inner]; [reflexivity|]. cbv zeta. cao.
  destruct (negb _); [apply IH | reflexivity].
Qed.

Lemma setdict_outer_cao : forall f s v, setdict_outer f (cset_ao s v) = cset_ao (setdict_outer f s) v.
Proof.
  induction f as [|f IH]; intros s v; cbn [setdict_outer]; [reflexivity|]. cbv zeta. cao.
  destruct (_ <=? _); [|reflexivity].
  rewrite setdict_inner_cao. destruct (setdict_inner _ s _ _) as [s1 str1]. cbn [fst snd].
  cao. rewrite fill_window_cao. apply IH.
Qed.

Definition zc_ao (zc : ZCall) (ao : Z) : ZCall := mkZCall (zc_input zc) ao (zc_strm zc).

Lemma cstrm_of_call_ao : forall zc ao s,
  set_strm s (cstrm_of_call (zc_ao zc ao)) = cset_ao (set_strm s (cstrm_of_call zc)) ao.
Proof. intros. reflexivity. Qed.
Lemma zret_of_cs_ao : forall st ao rc, zret_of_cs (cset_avail_out st ao) rc = zret_of_cs st rc.
Proof. intros. reflexivity. Qed.
Lemma zret_of_call_ao : forall zc ao rc, zret_of_cs (cstrm_of_call (zc_ao zc ao)) rc = zret_of_cs (cstrm_of_call zc) rc.
Proof. intros. reflexivity. Qed.


Definition sd_bad (s0 : deflate_state) : bool :=
  (ds_wrap s0 =? 2) || ((ds_wrap s0 =? 1) && negb (ds_status s0 =? INIT_STATE)) || negb (ds_lookahead s0 =? 0).
Definition sd_s2 (s0 : deflate_state) (dict : list Z) : deflate_state :=
  set_wrap (if ds_wrap s0 =? 1
            then set_strm s0 (cset_adler (ds_strm s0) (adler32_upd (cs_adler (ds_strm s0)) dict))
            else s0) 0.
Definition sd_clear (s2 : deflate_state) : deflate_state :=
  set_insert (set_block_start (set_strstart (clear_hash s2) 0) 0) 0.
Definition sd_split (wrap : Z) (s2 : deflate_state) (dict : list Z) : deflate_state * list Z :=
  if ds_w_size s2 <=? zlength dict
  then (let s := if wrap =? 0 then sd_clear s2 else s2 in (s, zskipn (zlength dict - ds_w_size s) dict))
  else (s2, dict).
Definition sd_s4 (s3 : deflate_state) (dict' : list Z) : deflate_state :=
  set_strm s3 (cset_avail_in (cset_next_in (cset_input (ds_strm s3) (arr_of_list dict')) 0) (zlength dict')).
Definition sd_fin (wrap : Z) (saved : cstrm) (s6 : deflate_state) : deflate_state * ZRet :=
  let s := set_strstart s6 (ds_strstart s6 + ds_lookahead s6) in
  let s := set_block_start s (ds_strstart s) in
  let s := set_insert s (ds_lookahead s) in
  let s := set_lookahead s 0 in
  let s := set_prev_length s (MIN_MATCH - 1) in
  let s := set_match_length s (MIN_MATCH - 1) in
  let s := set_match_available s 0 in
  let st := ds_strm s in
  let st := cset_input (cset_next_in (cset_avail_in st (cs_avail_in saved)) (cs_next_in saved)) (cs_input saved) in
  let s := set_strm s st in
  let s := set_wrap s wrap in
  (s, zret_of_cs (ds_strm s) Z_OK).
Definition sd_tail (wrap : Z) (s3 : deflate_state) (dict' : list Z) : deflate_state * ZRet :=
  sd_fin wrap (ds_strm s3) (setdict_outer (Z.to_nat (zlength dict' + 2)) (fill_window (sd_s4 s3 dict'))).

Lemma sdm_unfold : forall s zc dict,
  deflateSetDictionary_m s zc dict =
  let s0 := set_strm s (cstrm_of_call zc) in
  if deflateStateCheck s0 then (s0, zret_of_cs (cstrm_of_call zc) Z_STREAM_ERROR)
  else if sd_bad s0 then (s0, zret_of_cs (cstrm_of_call zc) Z_STREAM_ERROR)
  else let '(s3, dict') := sd_split (ds_wrap s0) (sd_s2 s0 dict) dict in sd_tail (ds_wrap s0) s3 dict'.
Proof.
  intros s zc dict. unfold deflateSetDictionary_m, sd_split, sd_tail, sd_s4, sd_fin, sd_s2, sd_bad, sd_clear. cbv zeta.
  destruct (deflateStateCheck _); [reflexivity|].
  destruct (_ || _); [reflexivity|].
  destruct (ds_w_size _ <=? zlength dict); reflexivity.
Qed.

Lemma sd_s2_cao : forall s0 ao dict, sd_s2 (cset_ao s0 ao) dict = cset_ao (sd_s2 s0 dict) ao.
Proof. intros. unfold sd_s2. cao. destruct (ds_wrap s0 =? 1); cao; reflexivity. Qed.
Lemma sd_clear_cao : forall s ao, sd_clear (cset_ao s ao) = cset_ao (sd_clear s) ao.
Proof. intros. reflexivity. Qed.
Lemma sd_split_cao : forall w s ao dict,
  sd_split w (cset_ao s ao) dict = (cset_ao (fst (sd_split w s dict)) ao, snd (sd_split w s dict)).
Proof.
  intros. unfold sd_split. cao. destruct (_ <=? _); [|reflexivity]. destruct (w =? 0); cbv zeta; [|cao; reflexivity].
  rewrite sd_clear_cao. cao. reflexivity.
Qed.
Lemma sd_s4_cao : forall s ao d, sd_s4 (cset_ao s ao) d = cset_ao (sd_s4 s d) ao.
Proof. intros. unfold sd_s4. cao. reflexivity. Qed.
Lemma sd_fin_cao : forall w st ao s,
  sd_fin w (cset_avail_out st ao) (cset_ao s ao) = (cset_ao (fst (sd_fin w st s)) ao, snd (sd_fin w st s)).
Proof. intros. unfold sd_fin. cbv zeta. cao. cbn [fst snd]. rewrite zret_of_cs_ao. reflexivity. Qed.
Lemma sd_tail_cao : forall w s ao d,
  sd_tail w (cset_ao s ao) d = (cset_ao (fst (sd_tail w s d)) ao, snd (sd_tail w s d)).
Proof.
  intros. unfold sd_tail. rewrite sd_s4_cao, fill_window_cao, setdict_outer_cao. cao. apply sd_fin_cao.
Qed.

Lemma sdm_ao : forall s zc dict ao,
  deflateSetDictionary_m s (zc_ao zc ao) dict
  = (cset_ao (fst (deflateSetDictionary_m s zc dict)) ao, snd (deflateSetDictionary_m s zc dict)).
Proof.
  intros s zc dict ao. rewrite !sdm_unfold. cbv zeta.
  rewrite cstrm_of_call_ao, zret_of_call_ao. cao.
  destruct (deflateStateCheck _); [reflexivity|].
  unfold sd_bad at 1. cao. fold (sd_bad (set_strm s (cstrm_of_call zc))).
  destruct (sd_bad _); [reflexivity|].
  rewrite sd_s2_cao, sd_split_cao. destruct (sd_split _ _ dict) as [s3 dict']. cbn [fst snd].
  apply sd_tail_cao.
Qed.


Definition LA (s : deflate_state) : Z := ds_lookahead s + cs_avail_in (ds_strm s).
Definition AI (s : deflate_state) : Z := cs_avail_in (ds_strm s).

Lemma fill_window_insert_LA : forall n s str,
  ds_lookahead (fill_window_insert n s str) = ds_lookahead s /\ ds_strm (fill_window_insert n s str) = ds_strm s.
Proof.
  induction n as [|n IH]; intros s str; cbn [fill_window_insert]; [split; reflexivity|].
  destruct (negb _); [|split; reflexivity]. cbv zeta.
  destruct (_ <? _); [split; reflexivity|].
  match goal with |- _ (fill_window_insert _ ?t _) = _ /\ _ => destruct (IH t (str + 1)) as [A B]; rewrite A, B end.
  split; reflexivity.
Qed.

Lemma fw_slide_LA : forall s ws m,
  ds_lookahead (fw_slide s ws m) = ds_lookahead s /\ ds_strm (fw_slide s ws m) = ds_strm s.
Proof. intros. unfold fw_slide. cbv zeta. destruct (_ <? _); split; reflexivity. Qed.

Lemma fw_insert_LA : forall s, ds_lookahead (fw_insert s) = ds_lookahead s /\ ds_strm (fw_insert s) = ds_strm s.
Proof.
  intros s. unfold fw_insert. cbv zeta. destruct (_ <=? _); [|split; reflexivity].
  match goal with |- context [fill_window_insert ?n ?t ?str] => destruct (fill_window_insert_LA n t str) as [A B]; rewrite A, B end.
  split; reflexivity.
Qed.

Lemma read_buf_LA : forall s off m, 0 <= AI s -> 0 <= m ->
  ds_lookahead (fst (read_buf s (RB_window off) m)) = ds_lookahead s
  /\ AI (fst (read_buf s (RB_window off) m)) = AI s - snd (read_buf s (RB_window off) m)
  /\ 0 <= snd (read_buf s (RB_window off) m) <= AI s.
Proof.
  intros s off m Hai Hm. unfold AI in *. unfold read_buf. cbv zeta.
  set (len := if _ <? cs_avail_in (ds_strm s) then _ else _).
  assert (Hlen : 0 <= len <= cs_avail_in (ds_strm s)).
  { subst len. destruct (Z.ltb_spec m (cs_avail_in (ds_strm s))); lia. }
  destruct (Z.eqb_spec len 0) as [L0|L0]; [cbn [fst snd]; lia|].
  cbn [fst snd]. destruct (ds_wrap _ =? 1); [|destruct (ds_wrap _ =? 2)]; dsred; lia.
Qed.

Lemma fill_window_body_LA : forall s ws, 0 <= AI s ->
  LA (fst (fill_window_body s ws)) = LA s /\ 0 <= AI (fst (fill_window_body s ws)) <= AI s.
Proof.
  intros s ws Hai. rewrite fill_window_body_eq.
  match goal with |- context [fw_slide s ws ?m] =>
    destruct (fw_slide_LA s ws m) as [E1l E1s]; revert E1l E1s; generalize (fw_slide s ws m) as s1; intros s1 E1l E1s end.
  unfold LA, AI in *.
  destruct (_ <=? ds_strstart s).
  - rewrite E1s. destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [A0|A0]; [cbn [fst]; rewrite E1l, E1s; lia|].
    match goal with |- context [read_buf s1 (RB_window ?off) ?m] =>
      destruct (read_buf_LA s1 off m ltac:(unfold AI; rewrite E1s; lia) ltac:(apply wrap32_range)) as (R1 & R2 & R3);
      destruct (read_buf s1 (RB_window off) m) as [s2 n] end.
    unfold AI in *. cbn [fst snd] in *.
    destruct (fw_insert_LA (set_lookahead s2 (ds_lookahead s2 + n))) as [F1 F2]. rewrite F1, F2. dsred. rewrite E1s in R2, R3. lia.
  - destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [A0|A0]; [cbn [fst]; lia|].
    match goal with |- context [read_buf s (RB_window ?off) ?m] =>
      destruct (read_buf_LA s off m ltac:(unfold AI; lia) ltac:(apply wrap32_range)) as (R1 & R2 & R3);
      destruct (read_buf s (RB_window off) m) as [s2 n] end.
    unfold AI in *. cbn [fst snd] in *.
    destruct (fw_insert_LA (set_lookahead s2 (ds_lookahead s2 + n))) as [F1 F2]. rewrite F1, F2. dsred. lia.
Qed.

Lemma fill_window_loop_LA : forall f s ws, 0 <= AI s ->
  LA (fill_window_loop f s ws) = LA s /\ 0 <= AI (fill_window_loop f s ws) <= AI s.
Proof.
  induction f as [|f IH]; intros s ws Hai; cbn [fill_window_loop]; [lia|].
  destruct (fill_window_body_LA s ws Hai) as [B1 B2].
  destruct (fill_window_body s ws) as [s1 brk]. cbn [fst] in B1, B2.
  destruct brk; [lia|]. destruct (_ && _); [|lia].
  destruct (IH s1 ws ltac:(lia)) as [C1 C2]. lia.
Qed.

Lemma fill_window_high_LA : forall s, LA (fill_window_high s) = LA s /\ AI (fill_window_high s) = AI s.
Proof.
  intros s. unfold fill_window_high. cbv zeta.
  destruct (_ <? ds_window_size s); [|split; reflexivity].
  destruct (_ <? ds_strstart s + ds_lookahead s); [split; reflexivity|].
  destruct (_ <? _); split; reflexivity.
Qed.

Lemma fill_window_LA : forall s, 0 <= AI s ->
  LA (fill_window s) = LA s /\ 0 <= AI (fill_window s) <= AI s.
Proof.
  intros s Hai. unfold fill_window. cbv zeta.
  destruct (fill_window_high_LA (fill_window_loop 263 s (ds_w_size s))) as [A B]. rewrite A, B.
  apply fill_window_loop_LA. exact Hai.
Qed.


Definition sdput3 (s t : deflate_state) : deflate_state :=
  set_head (set_prev (set_ins_h s (ds_ins_h t)) (ds_prev t)) (ds_head t).

Lemma setdict_inner_eq : forall k s str n,
  fst (setdict_inner k s str n) = sdput3 s (fst (setdict_inner k s str n))
  /\ (k = Z.to_nat n -> 1 <= n -> snd (setdict_inner k s str n) = str + n).
Proof.
  induction k as [|k IH]; intros s str n; cbn [setdict_inner].
  - split; [destruct s; reflexivity | intros; lia].
  - cbv zeta. destruct (Z.eqb_spec (n - 1) 0) as [E|E]; cbn [negb fst snd].
    + split; [reflexivity | intros; lia].
    + match goal with |- fst (setdict_inner k ?t ?a ?b) = _ /\ _ => destruct (IH t a b) as [A B] end.
      split; [| intros; rewrite B; lia].
      rewrite A at 1. reflexivity.
Qed.

Lemma setdict_outer_S : forall f s,
  setdict_outer (S f) s =
  if MIN_MATCH <=? ds_lookahead s
  then let n := ds_lookahead s - (MIN_MATCH - 1) in
       let r := setdict_inner (Z.to_nat n) s (ds_strstart s) n in
       setdict_outer f (fill_window (set_lookahead (set_strstart (fst r) (snd r)) (MIN_MATCH - 1)))
  else s.
Proof.
  intros f s. cbn [setdict_outer]. destruct (_ <=? _); [|reflexivity].
  cbv zeta. destruct (setdict_inner _ _ _ _); reflexivity.
Qed.

Lemma setdict_outer_exit : forall f s, ds_lookahead s < MIN_MATCH -> setdict_outer f s = s.
Proof.
  intros f s H. destruct f; [reflexivity|]. rewrite setdict_outer_S.
  destruct (Z.leb_spec MIN_MATCH (ds_lookahead s)); [lia | reflexivity].
Qed.


Definition csput0 (c d : cstrm) : cstrm :=
  mkCS (cs_input c) (cs_next_in d) (cs_avail_in d) (cs_out_rev c) (cs_avail_out c) (cs_total_in d)
       (cs_total_out c) (cs_msg c) (cs_data_type c) (cs_adler c).

Definition CSK0 (s t : deflate_state) : Prop := ds_strm t = csput0 (ds_strm s) (ds_strm t) /\ ds_wrap t = 0.

Lemma CSK0_refl : forall s, ds_wrap s = 0 -> CSK0 s s.
Proof. intros s H. split; [destruct s as [? ? ? ? ?]; cbn; destruct ds_strm; reflexivity | exact H]. Qed.
Lemma CSK0_trans : forall s t u, CSK0 s t -> CSK0 t u -> CSK0 s u.
Proof.
  intros s t u [A B] [C D]. split; [|exact D]. rewrite C, A. reflexivity.
Qed.
Lemma CSK0_same : forall s t u, CSK0 s t -> ds_strm u = ds_strm t -> ds_wrap u = ds_wrap t -> CSK0 s u.
Proof. intros s t u [A B] C D. split; [rewrite C; exact A | rewrite D; exact B]. Qed.

Lemma read_buf_CSK0 : forall s off more, ds_wrap s = 0 -> CSK0 s (fst (read_buf s (RB_window off) more)).
Proof.
  intros s off more W. unfold read_buf. cbv zeta.
  destruct (_ =? 0); [apply CSK0_refl; exact W|]. cbn [fst].
  unfold CSK0. dsred. rewrite W. cbn [Z.eqb]. split; reflexivity.
Qed.

Lemma fill_window_insert_CSK0 : forall n s str t, CSK0 t s -> CSK0 t (fill_window_insert n s str).
Proof.
  induction n as [|n IH]; intros s str t H; cbn [fill_window_insert]; [exact H|].
  destruct (negb _); [|exact H]. cbv zeta.
  destruct (_ <? _).
  - apply (CSK0_same t s); [exact H | reflexivity | reflexivity].
  - apply IH. apply (CSK0_same t s); [exact H | reflexivity | reflexivity].
Qed.

Lemma fw_slide_CSK0 : forall s ws m t, CSK0 t s -> CSK0 t (fw_slide s ws m).
Proof.
  intros s ws m t H. unfold fw_slide. cbv zeta.
  destruct (_ <? _); (apply (CSK0_same t s); [exact H | reflexivity | reflexivity]).
Qed.

Lemma fw_insert_CSK0 : forall s t, CSK0 t s -> CSK0 t (fw_insert s).
Proof.
  intros s t H. unfold fw_insert. cbv zeta. destruct (_ <=? _); [|exact H].
  apply fill_window_insert_CSK0. apply (CSK0_same t s); [exact H | reflexivity | reflexivity].
Qed.

Lemma fill_window_body_CSK0 : forall s ws t, CSK0 t s -> CSK0 t (fst (fill_window_body s ws)).
Proof.
  intros s ws t H. rewrite fill_window_body_eq.
  match goal with |- context [fw_slide s ws ?m] =>
    pose proof (fw_slide_CSK0 s ws m t H) as H1; revert H1; generalize (fw_slide s ws m) as s1; intros s1 H1 end.
  destruct (_ <=? ds_strstart s).
  - destruct (cs_avail_in _ =? 0); [cbn [fst]; exact H1|].
    match goal with |- context [read_buf s1 (RB_window ?off) ?m] =>
      pose proof (read_buf_CSK0 s1 off m (proj2 H1)) as H2; destruct (read_buf s1 (RB_window off) m) as [s2 k] end.
    cbn [fst snd] in *. apply fw_insert_CSK0. apply (CSK0_same t s2); [exact (CSK0_trans _ _ _ H1 H2) | reflexivity | reflexivity].
  - destruct (cs_avail_in _ =? 0); [cbn [fst]; exact H|].
    match goal with |- context [read_buf s (RB_window ?off) ?m] =>
      pose proof (read_buf_CSK0 s off m (proj2 H)) as H2; destruct (read_buf s (RB_window off) m) as [s2 k] end.
    cbn [fst snd] in *. apply fw_insert_CSK0. apply (CSK0_same t s2); [exact (CSK0_trans _ _ _ H H2) | reflexivity | reflexivity].
Qed.

Lemma fill_window_loop_CSK0 : forall f s ws t, CSK0 t s -> CSK0 t (fill_window_loop f s ws).
Proof.
  induction f as [|f IH]; intros s ws t H; cbn [fill_window_loop]; [exact H|].
  pose proof (fill_window_body_CSK0 s ws t H) as HB. destruct (fill_window_body s ws) as [s1 brk]. cbn [fst] in HB.
  destruct brk; [exact HB|]. destruct (_ && _); [apply IH; exact HB | exact HB].
Qed.

Lemma fill_window_high_CSK0 : forall s t, CSK0 t s -> CSK0 t (fill_window_high s).
Proof.
  intros s t H. unfold fill_window_high. cbv zeta.
  destruct (_ <? ds_window_size s); [|exact H].
  destruct (_ <? ds_strstart s + ds_lookahead s); [apply (CSK0_same t s); [exact H | reflexivity | reflexivity]|].
  destruct (_ <? _); [apply (CSK0_same t s); [exact H | reflexivity | reflexivity] | exact H].
Qed.

Lemma fill_window_CSK0 : forall s t, CSK0 t s -> CSK0 t (fill_window s).
Proof.
  intros s t H. unfold fill_window. cbv zeta. apply fill_window_high_CSK0. apply fill_window_loop_CSK0. exact H.
Qed.

Lemma setdict_outer_CSK0 : forall f s t, CSK0 t s -> CSK0 t (setdict_outer f s).
Proof.
  induction f as [|f IH]; intros s t H; [exact H|]. rewrite setdict_outer_S.
  destruct (_ <=? _); [|exact H]. cbv zeta. apply IH. apply fill_window_CSK0.
  pose proof (proj1 (setdict_inner_eq (Z.to_nat (ds_lookahead s - (MIN_MATCH - 1))) s (ds_strstart s) (ds_lookahead s - (MIN_MATCH - 1)))) as E.
  apply (CSK0_same t s); [exact H | |]; dsred; rewrite E; reflexivity.
Qed.
End RefDeflateDictM.

Module RefDeflateM.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma put_byte_pending : forall s c, ds_pending (put_byte s c) = ds_pending s + 1.
Proof. intros s c. reflexivity. Qed.


Ltac is_ds_getter f := lazymatch f with ds_status => idtac | ds_pending_buf => idtac | ds_pending_buf_size => idtac | ds_pending_out => idtac | ds_pending => idtac | ds_wrap => idtac | ds_gzhead => idtac | ds_gzindex => idtac | ds_method => idtac | ds_last_flush => idtac | ds_w_size => idtac | ds_w_bits => idtac | ds_w_mask => idtac | ds_window => idtac | ds_window_size => idtac | ds_prev => idtac | ds_head => idtac | ds_ins_h => idtac | ds_hash_size => idtac | ds_hash_bits => idtac | ds_hash_mask => idtac | ds_hash_shift => idtac | ds_block_start => idtac | ds_match_length => idtac | ds_prev_match => idtac | ds_match_available => idtac | ds_strstart => idtac | ds_match_start => idtac | ds_lookahead => idtac | ds_prev_length => idtac | ds_max_chain_length => idtac | ds_max_lazy_match => idtac | ds_level => idtac | ds_strategy => idtac | ds_good_match => idtac | ds_nice_match => idtac | ds_dyn_ltree_fc => idtac | ds_dyn_ltree_dl => idtac | ds_dyn_dtree_fc => idtac | ds_dyn_dtree_dl => idtac | ds_bl_tree_fc => idtac | ds_bl_tree_dl => idtac | ds_l_max_code => idtac | ds_d_max_code => idtac | ds_bl_max_code => idtac | ds_bl_count => idtac | ds_heap => idtac | ds_heap_len => idtac | ds_heap_max => idtac | ds_depth => idtac | ds_lit_bufsize => idtac | ds_sym_next => idtac | ds_sym_end => idtac | ds_opt_len => idtac | ds_static_len => idtac | ds_matches => idtac | ds_insert => idtac | ds_bi_buf => idtac | ds_bi_valid => idtac | ds_high_water => idtac | ds_self_blk => idtac | ds_window_blk => idtac | ds_prev_blk => idtac | ds_head_blk => idtac | ds_pending_buf_blk => idtac | ds_strm => idtac end.
Ltac is_ds_setter f := lazymatch f with set_status => idtac | set_pending_buf => idtac | set_pending_buf_size => idtac | set_pending_out => idtac | set_pending => idtac | set_wrap => idtac | set_gzhead => idtac | set_gzindex => idtac | set_method => idtac | set_last_flush => idtac | set_w_size => idtac | set_w_bits => idtac | set_w_mask => idtac | set_window => idtac | set_window_size => idtac | set_prev => idtac | set_head => idtac | set_ins_h => idtac | set_hash_size => idtac | set_hash_bits => idtac | set_hash_mask => idtac | set_hash_shift => idtac | set_block_start => idtac | set_match_length => idtac | set_prev_match => idtac | set_match_available => idtac | set_strstart => idtac | set_match_start => idtac | set_lookahead => idtac | set_prev_length => idtac | set_max_chain_length => idtac | set_max_lazy_match => idtac | set_level => idtac | set_strategy => idtac | set_good_match => idtac | set_nice_match => idtac | set_dyn_ltree_fc => idtac | set_dyn_ltree_dl => idtac | set_dyn_dtree_fc => idtac | set_dyn_dtree_dl => idtac | set_bl_tree_fc => idtac | set_bl_tree_dl => idtac | set_l_max_code => idtac | set_d_max_code => idtac | set_bl_max_code => idtac | set_bl_count => idtac | set_heap => idtac | set_heap_len => idtac | set_heap_max => idtac | set_depth => idtac | set_lit_bufsize => idtac | set_sym_next => idtac | set_sym_end => idtac | set_opt_len => idtac | set_static_len => idtac | set_matches => idtac | set_insert => idtac | set_bi_buf => idtac | set_bi_valid => idtac | set_high_water => idtac | set_self_blk => idtac | set_window_blk => idtac | set_prev_blk => idtac | set_head_blk => idtac | set_pending_buf_blk => idtac | set_strm => idtac end.

Ltac gs_rw f st tac :=
  let E := fresh "GSE" in
  first [ assert (E : forall s' v', f (st s' v') = v') by (intros; reflexivity)
        | assert (E : forall s' v', f (st s' v') = f s') by (intros; reflexivity) ];
  tac E; clear E.
Ltac gs_pb f tac :=
  let E := fresh "GSE" in
  first [ assert (E : forall s' c', f (put_byte s' c') = f s') by (intros; reflexivity)
        | constr_eq f ds_pending; pose proof put_byte_pending as E ];
  tac E; clear E.
Ltac gs1 :=
  match goal with
  | |- context [?f (?st ?s ?v)] =>
      is_ds_getter f;
      first [ is_ds_setter st; gs_rw f st ltac:(fun E => rewrite !E)
            | constr_eq st put_byte; gs_pb f ltac:(fun E => rewrite !E) ]
  end.
Ltac gs := repeat gs1.
Ltac gs1_in H :=
  match type of H with
  | context [?f (?st ?s ?v)] =>
      is_ds_getter f;
      first [ is_ds_setter st; gs_rw f st ltac:(fun E => rewrite !E in H)
            | constr_eq st put_byte; gs_pb f ltac:(fun E => rewrite !E in H) ]
  end.
Ltac gs_in H := repeat (gs1_in H).


Definition mput (s : deflate_state) (i c pn : Z) : deflate_state :=
  set_pending_buf (set_pending s pn) (arr_set (ds_pending_buf s) i (wrap8 c)).

Lemma mput_put : forall s i c pn c',
  i = ds_pending s -> pn = ds_pending s + 1 -> wrap8 c = wrap8 c' -> mput s i c pn = put_byte s c'.
Proof. intros s i c pn c' -> -> E. unfold mput, put_byte. rewrite E. destruct s; reflexivity. Qed.

Lemma mput_strm : forall s i c pn, ds_strm (mput s i c pn) = ds_strm s.
Proof. intros. reflexivity. Qed.
Lemma mput_pending : forall s i c pn, ds_pending (mput s i c pn) = pn.
Proof. intros. reflexivity. Qed.

Definition mput2 (s : deflate_state) (i c pn : Z) : deflate_state :=
  set_pending_buf (set_pending s pn) (arr_set (ds_pending_buf (set_pending s pn)) i (wrap8 c)).

Lemma mput2_put : forall s i c pn c',
  i = ds_pending s -> pn = ds_pending s + 1 -> wrap8 c = wrap8 c' -> mput2 s i c pn = put_byte s c'.
Proof. intros s i c pn c' -> -> E. unfold mput2, put_byte. rewrite E. destruct s; reflexivity. Qed.

Fixpoint mputl2 (s : deflate_state) (l : list (Z * Z * Z)) : deflate_state :=
  match l with [] => s | (i, c, pn) :: l' => mputl2 (mput2 s i c pn) l' end.

Ltac mput_step c' :=
  match goal with
  | |- context [mput ?s ?i ?c ?pn] =>
      lazymatch s with
      | context [mput _ _ _ _] => fail
      | _ => rewrite (mput_put s i c pn c'); [| dsred; rewrite ?put_byte_pending; dsred; lia | dsred; rewrite ?put_byte_pending; dsred; lia | ]
      end
  end.
Ltac mput_steps cs :=
  lazymatch cs with
  | nil => idtac
  | ?c' :: ?rest => mput_step c'; [mput_steps rest | ]
  end.



Definition hfix (h : Z) : Z :=
  ((h - h * 138547333 / 2 ^ 32) mod 2 ^ 32 / 2 ^ 1 + h * 138547333 / 2 ^ 32) / 2 ^ 4 * 2 ^ 5
  - ((h - h * 138547333 / 2 ^ 32) mod 2 ^ 32 / 2 ^ 1 + h * 138547333 / 2 ^ 32) / 2 ^ 4 + 31.

Definition hdiv31 (h : Z) : Z := ((h - h * 138547333 / 2 ^ 32) mod 2 ^ 32 / 2 ^ 1 + h * 138547333 / 2 ^ 32) / 2 ^ 4.

Fixpoint hdiv31_chk (fuel : nat) (h : Z) : bool :=
  match fuel with O => true | S f => Z.eqb (hdiv31 h) (h / 31) && hdiv31_chk f (h + 1) end.

Lemma hdiv31_all : hdiv31_chk (Z.to_nat 65536) 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma hdiv31_chk_ok : forall n h, hdiv31_chk n h = true -> forall k, h <= k < h + Z.of_nat n -> hdiv31 k = k / 31.
Proof.
  induction n as [|n IH]; intros h Hc k Hk; [lia|].
  cbn [hdiv31_chk] in Hc. apply andb_prop in Hc as [H1 H2].
  destruct (Z.eq_dec k h) as [->|Hne]; [apply Z.eqb_eq; exact H1|].
  apply (IH (h + 1) H2). lia.
Qed.

Lemma hdiv31_ok : forall h, 0 <= h < 65536 -> hdiv31 h = h / 31.
Proof. intros h Hh. apply (hdiv31_chk_ok (Z.to_nat 65536) 0 hdiv31_all). lia. Qed.

Lemma hfix_ok : forall h, 0 <= h < 65536 ->
  ((h - h * 138547333 / 2 ^ 32) mod 2 ^ 32 / 2 ^ 1 + h * 138547333 / 2 ^ 32) / 2 ^ 4 * 2 ^ 5
  - ((h - h * 138547333 / 2 ^ 32) mod 2 ^ 32 / 2 ^ 1 + h * 138547333 / 2 ^ 32) / 2 ^ 4 + 31
  = h + (31 - h mod 31).
Proof.
  intros h Hh. change (hdiv31 h * 2 ^ 5 - hdiv31 h + 31 = h + (31 - h mod 31)).
  rewrite hdiv31_ok by lia. pose proof (Z.div_mod h 31 ltac:(lia)). lia.
Qed.


Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma b8_hi32 : forall a, 0 <= a -> (a mod 2 ^ 32 / 2 ^ 8) mod 2 ^ 8 = (Z.land a 65535 / 2 ^ 8) mod 2 ^ 8.
Proof.
  intros a Ha. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  change (2 ^ 32) with 4294967296. change (2 ^ 16) with 65536. change (2 ^ 8) with 256. lia.
Qed.

Lemma b8_lo : forall a, 0 <= a -> a mod 2 ^ 8 = (Z.land (Z.land a 65535) 255) mod 2 ^ 8.
Proof.
  intros a Ha. change 65535 with (Z.ones 16). change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
  change (2 ^ 16) with 65536. change (2 ^ 8) with 256. lia.
Qed.

Lemma b8_land255 : forall a, (Z.land a 255) mod 2 ^ 8 = a mod 2 ^ 8.
Proof. intros a. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_mod. lia. Qed.

Lemma b8_mod32 : forall a, (a mod 2 ^ 32) mod 2 ^ 8 = a mod 2 ^ 8.
Proof. intros a. change (2 ^ 32) with 4294967296. change (2 ^ 8) with 256. lia. Qed.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition zh_lf (X : deflate_state) : Z :=
  if Z.leb Z_HUFFMAN_ONLY (ds_strategy X) || Z.ltb (ds_level X) 2 then 0
  else if Z.ltb (ds_level X) 6 then 1 else if Z.eqb (ds_level X) 6 then 2 else 3.
Definition zh_h0 (X : deflate_state) : Z := Z.shiftl (Z_DEFLATED + Z.shiftl (ds_w_bits X - 8) 4) 8.
Definition zh_h1 (X : deflate_state) : Z := Z.lor (zh_h0 X) (Z.shiftl (zh_lf X) 6).
Definition zh_h2 (X : deflate_state) : Z := if ds_strstart X =? 0 then zh_h1 X else Z.lor (zh_h1 X) PRESET_DICT.
Definition zh_hdr (X : deflate_state) : Z := zh_h2 X + (31 - zh_h2 X mod 31).

Lemma zh_h1_val : forall wb lf fl, 9 <= wb <= 15 -> 0 <= lf <= 3 -> fl = lf * 64 ->
  Z.lor (Z.shiftl (Z_DEFLATED + Z.shiftl (wb - 8) 4) 8) (Z.shiftl lf 6) = wb * 4096 - 30720 + lf * 64
  /\ Z.lor (wb * 4096 + -30720) fl = wb * 4096 - 30720 + lf * 64
  /\ Z.lor (wb * 4096 - 30720 + lf * 64) PRESET_DICT = wb * 4096 - 30720 + lf * 64 + 32.
Proof.
  intros wb lf fl Hwb Hlf ->.
  assert (Hw : wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  assert (Hl : lf = 0 \/ lf = 1 \/ lf = 2 \/ lf = 3) by lia.
  destruct Hw as [-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]; destruct Hl as [-> |[-> |[-> | ->]]]; repeat split; reflexivity.
Qed.

Lemma zh_lf_range : forall X, 0 <= zh_lf X <= 3.
Proof. intros X. unfold zh_lf. repeat destruct (_ : bool); lia. Qed.

Lemma zh_h1_eq : forall X, 9 <= ds_w_bits X <= 15 -> zh_h1 X = ds_w_bits X * 4096 - 30720 + zh_lf X * 64.
Proof.
  intros X Hwb. unfold zh_h1, zh_h0.
  destruct (zh_h1_val (ds_w_bits X) (zh_lf X) (zh_lf X * 64) Hwb (zh_lf_range X) eq_refl) as (E1 & _ & _). exact E1.
Qed.

Lemma zh_h2_eq : forall X, 9 <= ds_w_bits X <= 15 ->
  zh_h2 X = zh_h1 X + (if ds_strstart X =? 0 then 0 else 32) /\ 0 <= zh_h2 X < 2 ^ 15.
Proof.
  intros X Hwb. pose proof (zh_h1_eq X Hwb) as E1. pose proof (zh_lf_range X) as Hl.
  destruct (zh_h1_val (ds_w_bits X) (zh_lf X) (zh_lf X * 64) Hwb Hl eq_refl) as (_ & _ & E3).
  unfold zh_h2. rewrite E1. destruct (ds_strstart X =? 0); [lia|]. rewrite E3. lia.
Qed.

Lemma zh_hdr_range : forall X, 9 <= ds_w_bits X <= 15 -> 0 <= zh_hdr X < 2 ^ 16.
Proof.
  intros X Hwb. destruct (zh_h2_eq X Hwb) as [_ H2]. unfold zh_hdr.
  pose proof (Z.mod_pos_bound (zh_h2 X) 31 ltac:(lia)). lia.
Qed.

Definition zh_st (X : deflate_state) : deflate_state :=
  let s := putShortMSB X (zh_hdr X) in
  if negb (ds_strstart X =? 0) then
    let adler := cs_adler (ds_strm s) in
    putShortMSB (putShortMSB s (wrap32 (Z.shiftr adler 16))) (Z.land adler 65535)
  else s.

Definition zh_stM (X : deflate_state) : deflate_state :=
  let p := ds_pending X in
  let h := hfix (zh_h2 X) in
  let ad := cs_adler (ds_strm X) in
  let s2 := mput (mput X p (h mod 2 ^ 32 / 2 ^ 8) (p + 1)) (p + 1) (szwrap 32 h) (p + 2) in
  if ds_strstart X =? 0 then s2
  else mput (mput (mput (mput s2 (p + 2) ((ad / 2 ^ 16) mod 2 ^ 32 / 2 ^ 8) (p + 3)) (p + 3) (ad / 2 ^ 16) (p + 4))
                  (p + 4) (ad mod 2 ^ 32 / 2 ^ 8) (p + 5)) (p + 5) ad (p + 6).

Lemma hfix_hdr : forall X, 9 <= ds_w_bits X <= 15 -> hfix (zh_h2 X) = zh_hdr X.
Proof.
  intros X Hwb. destruct (zh_h2_eq X Hwb) as [_ H2]. unfold hfix, zh_hdr. apply hfix_ok. lia.
Qed.

Lemma zh_stM_eq : forall X, 9 <= ds_w_bits X <= 15 -> 0 <= cs_adler (ds_strm X) -> zh_stM X = zh_st X.
Proof.
  intros X Hwb Had. pose proof (zh_hdr_range X Hwb) as Hr.
  unfold zh_stM, zh_st, putShortMSB. rewrite hfix_hdr by exact Hwb. cbv zeta.
  revert Hr. generalize (zh_hdr X) as hdr. intros hdr Hr.
  change (cs_adler (ds_strm (put_byte (put_byte X (Z.shiftr hdr 8)) (Z.land hdr 255)))) with (cs_adler (ds_strm X)).
  revert Had. generalize (cs_adler (ds_strm X)) as ad. intros ad Had.
  mput_step (Z.shiftr hdr 8).
  2:{ rewrite !wrap8_mod', Z.shiftr_div_pow2 by lia. rewrite (Z.mod_small hdr) by lia. reflexivity. }
  mput_step (Z.land hdr 255).
  2:{ rewrite !wrap8_mod', (szwrap_small 32) by lia. symmetry. apply b8_land255. }
  destruct (ds_strstart X =? 0); cbn [negb]; [reflexivity|].
  mput_step (Z.shiftr (wrap32 (Z.shiftr ad 16)) 8).
  2:{ rewrite !wrap8_mod', !Z.shiftr_div_pow2, wrap32_mod by lia. reflexivity. }
  mput_step (Z.land (wrap32 (Z.shiftr ad 16)) 255).
  2:{ rewrite !wrap8_mod', !Z.shiftr_div_pow2, wrap32_mod by lia. rewrite b8_land255, b8_mod32. reflexivity. }
  mput_step (Z.shiftr (Z.land ad 65535) 8).
  2:{ rewrite !wrap8_mod', !Z.shiftr_div_pow2 by lia. apply b8_hi32. exact Had. }
  mput_step (Z.land (Z.land ad 65535) 255).
  2:{ rewrite !wrap8_mod'. apply b8_lo. exact Had. }
  reflexivity.
Qed.

Lemma zh_st_pending : forall X, ds_pending (zh_st X) = ds_pending X + (if ds_strstart X =? 0 then 2 else 6).
Proof.
  intros X. unfold zh_st, putShortMSB. destruct (ds_strstart X =? 0); cbn [negb]; rewrite !put_byte_pending; lia.
Qed.
Lemma zh_st_strm : forall X, ds_strm (zh_st X) = ds_strm X.
Proof. intros X. unfold zh_st, putShortMSB. destruct (ds_strstart X =? 0); reflexivity. Qed.


Definition gz_xfl (X : deflate_state) : Z :=
  if Z.eqb (ds_level X) 9 then 2
  else if Z.leb Z_HUFFMAN_ONLY (ds_strategy X) || Z.ltb (ds_level X) 2 then 4 else 0.

Definition gz_st (X : deflate_state) : deflate_state :=
  let s := set_strm X (cset_adler (ds_strm X) crc32_init) in
  let s := put_byte s 31 in let s := put_byte s 139 in let s := put_byte s 8 in
  let s := put_byte s 0 in let s := put_byte s 0 in let s := put_byte s 0 in let s := put_byte s 0 in let s := put_byte s 0 in
  let s := put_byte s (gz_xfl X) in
  let s := put_byte s OS_CODE in
  set_status s BUSY_STATE.

Definition gz_xflM (X : deflate_state) : Z :=
  Z.lor (if 1 <? ds_strategy X then 1 else 0) (if ds_level X <? 2 then 1 else 0) * 2 ^ 2.

Definition gz_stM (X : deflate_state) (xfl : Z) : deflate_state :=
  let p := ds_pending X in
  let s := set_strm X (cset_adler (ds_strm X) 0) in
  let s := mput2 s p 31 (p + 1) in let s := mput2 s (p + 1) (-117) (p + 2) in let s := mput2 s (p + 2) 8 (p + 3) in
  let s := mput2 s (p + 3) 0 (p + 4) in let s := mput2 s (p + 4) 0 (p + 5) in let s := mput2 s (p + 5) 0 (p + 6) in
  let s := mput2 s (p + 6) 0 (p + 7) in let s := mput2 s (p + 7) 0 (p + 8) in
  let s := mput2 s (p + 8) xfl (p + 9) in
  let s := mput2 s (p + 9) 3 (p + 10) in
  set_status s 113.

Fixpoint mputl (s : deflate_state) (l : list (Z * Z * Z)) : deflate_state :=
  match l with [] => s | (i, c, pn) :: l' => mputl (mput s i c pn) l' end.
Fixpoint putl (s : deflate_state) (cs : list Z) : deflate_state :=
  match cs with [] => s | c :: cs' => putl (put_byte s c) cs' end.
Fixpoint MOK (p : Z) (l : list (Z * Z * Z)) (cs : list Z) : Prop :=
  match l, cs with
  | [], [] => True
  | (i, c, pn) :: l', c' :: cs' => i = p /\ pn = p + 1 /\ wrap8 c = wrap8 c' /\ MOK (p + 1) l' cs'
  | _, _ => False
  end.
Lemma mputl_putl : forall l cs s, MOK (ds_pending s) l cs -> mputl s l = putl s cs.
Proof.
  induction l as [|[[i c] pn] l IH]; intros [|c' cs] s H; cbn [MOK] in H; try contradiction; [reflexivity|].
  destruct H as (Hi & Hpn & Hc & H). cbn [mputl putl].
  rewrite (mput_put s i c pn c' Hi Hpn Hc). apply IH. rewrite put_byte_pending. exact H.
Qed.
Lemma mputl2_putl : forall l cs s, MOK (ds_pending s) l cs -> mputl2 s l = putl s cs.
Proof.
  induction l as [|[[i c] pn] l IH]; intros [|c' cs] s H; cbn [MOK] in H; try contradiction; [reflexivity|].
  destruct H as (Hi & Hpn & Hc & H). cbn [mputl2 putl].
  rewrite (mput2_put s i c pn c' Hi Hpn Hc). apply IH. rewrite put_byte_pending. exact H.
Qed.

Lemma gz_stM_eq : forall X xfl,
  wrap8 xfl = wrap8 (gz_xfl X) -> gz_stM X xfl = gz_st X.
Proof.
  intros X xfl Hx. unfold gz_stM, gz_st, crc32_init, OS_CODE, BUSY_STATE. cbv zeta.
  set (s0 := set_strm X (cset_adler (ds_strm X) 0)).
  set (p := ds_pending X).
  change (set_status (mputl2 s0 [(p, 31, p + 1); (p + 1, -117, p + 2); (p + 2, 8, p + 3); (p + 3, 0, p + 4);
                                (p + 4, 0, p + 5); (p + 5, 0, p + 6); (p + 6, 0, p + 7); (p + 7, 0, p + 8);
                                (p + 8, xfl, p + 9); (p + 9, 3, p + 10)]) 113
          = set_status (putl s0 [31; 139; 8; 0; 0; 0; 0; 0; gz_xfl X; 3]) 113).
  rewrite (mputl2_putl _ [31; 139; 8; 0; 0; 0; 0; 0; gz_xfl X; 3]); [reflexivity|].
  assert (Ep : ds_pending s0 = p) by reflexivity. rewrite Ep.
  cbn [MOK]. repeat split; first [exact Hx | lia].
Qed.

Lemma gz_xflM_ok : forall X, ds_level X <> 9 -> wrap8 (gz_xflM X) = wrap8 (gz_xfl X).
Proof.
  intros X H9. unfold gz_xflM, gz_xfl, Z_HUFFMAN_ONLY. replace (ds_level X =? 9) with false by (symmetry; apply Z.eqb_neq; exact H9).
  destruct (Z.ltb_spec 1 (ds_strategy X)); destruct (Z.leb_spec 2 (ds_strategy X)); try lia;
    destruct (ds_level X <? 2); reflexivity.
Qed.

Lemma gz_xfl9 : forall X, ds_level X = 9 -> wrap8 2 = wrap8 (gz_xfl X).
Proof. intros X H9. unfold gz_xfl. rewrite (proj2 (Z.eqb_eq _ _) H9). reflexivity. Qed.

Lemma putl_pending : forall cs s, ds_pending (putl s cs) = ds_pending s + Z.of_nat (length cs).
Proof.
  induction cs as [|c cs IH]; intros s; cbn [putl length]; [lia|].
  rewrite IH, put_byte_pending. lia.
Qed.
Lemma putl_keeps : forall {A} (g : deflate_state -> A) wi, keeps g true wi -> forall cs s, g (putl s cs) = g s.
Proof.
  intros A g wi K. induction cs as [|c cs IH]; intros s; cbn [putl]; [reflexivity|].
  rewrite IH. apply (k_put_byte g true wi K eq_refl).
Qed.

Lemma gz_st_putl : forall X,
  gz_st X = set_status (putl (set_strm X (cset_adler (ds_strm X) crc32_init)) [31; 139; 8; 0; 0; 0; 0; 0; gz_xfl X; OS_CODE]) BUSY_STATE.
Proof. intros X. reflexivity. Qed.

Lemma gz_st_facts : forall X,
  ds_pending (gz_st X) = ds_pending X + 10 /\ ds_strm (gz_st X) = cset_adler (ds_strm X) crc32_init /\ ds_status (gz_st X) = BUSY_STATE.
Proof.
  intros X. rewrite gz_st_putl.
  split; [|split].
  - gs. rewrite putl_pending. gs. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. reflexivity.
  - gs. rewrite (putl_keeps ds_strm true keeps_strm). gs. reflexivity.
  - gs. reflexivity.
Qed.
End RefDeflateM.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition bytes_okP (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.
Definition zstrm_okP (z : zstrm) : Prop :=
  0 <= zs_total_in z < 2 ^ 64 /\ 0 <= zs_total_out z < 2 ^ 64 /\ 0 <= zs_adler z < 2 ^ 64
  /\ - 2 ^ 31 <= zs_data_type z < 2 ^ 31.
Definition dcall_wf (zc : ZCall) : Prop :=
  zstrm_okP (zc_strm zc) /\ 0 <= zc_avail_out zc < 2 ^ 32 /\ zlength (zc_input zc) < 2 ^ 32 /\ bytes_okP (zc_input zc).

Definition DCH : Type := list (option (blk * (Z -> Z))).
Definition dhooks : zhooks DCH :=
  mkHooks (fun _ _ => fun chs : DCH => match chs with
                                      | [] => MRet (None, [])
                                      | c :: chs' => MRet (c, chs')
                                      end)
          (fun _ => fun chs : DCH => MRet (tt, chs)).
Definition dpure {A} (m : SM DCH A) (chs : DCH) : option A :=
  match m chs with MRet p => Some (fst p) | _ => None end.

Inductive dreach : deflate_state -> Prop :=
| DR_init : forall zc level method wb memlevel strategy chs s zr,
    5 <= memlevel ->
    dpure (deflateInit2_m dhooks zc level method wb memlevel strategy) chs = Some (Some s, zr) -> dreach s
| DR_deflate : forall s zc flush s' zr,
    dreach s -> dcall_wf zc -> 0 <= flush < 16 ->
    deflate_m s zc flush = (s', zr) -> dreach s'
| DR_setdict : forall s zc dict s' zr,
    dreach s -> zstrm_okP (zc_strm zc) -> bytes_okP dict -> 0 < zlength dict < 2 ^ 32 ->
    deflateSetDictionary_m s zc dict = (s', zr) -> dreach s'.

Definition reach (ds : deflate_state) (zc : ZCall) (flush : Z) : Prop :=
  dreach ds /\ dcall_wf zc /\ 0 <= flush < 16.


Definition st4 (st : Z) : Prop := st = INIT_STATE \/ st = GZIP_STATE \/ st = BUSY_STATE \/ st = FINISH_STATE.

Section Obligations.
  Variable SAFEs : deflate_state -> Z -> Prop.
Variable SAFEf : deflate_state -> Z -> Prop.
Variable SAFEw : deflate_state -> Z -> Prop.
  Variable FB : deflate_state -> option Z -> Z -> Z -> Prop.
  Variable WF : deflate_state -> Prop.

Record DOK (X : deflate_state) : Prop := {
  ok_st : st4 (ds_status X);
  ok_wrap : - 2 <= ds_wrap X <= 2;
  ok_lf : - 2 ^ 31 <= ds_last_flush X < 2 ^ 31;
  ok_gzhead : ds_gzhead X = 0;
  ok_level : 0 <= ds_level X <= 9;
  ok_strategy : 0 <= ds_strategy X <= 4;
  ok_wbits : 9 <= ds_w_bits X <= 15;
  ok_pend : 0 <= ds_pending_out X /\ 0 <= ds_pending X /\ ds_pending_out X + ds_pending X <= ds_lit_bufsize X * 4;
  ok_bi : 0 <= ds_bi_valid X <= 16 /\ 0 <= ds_bi_buf X < 2 ^ 16;
  ok_strstart : 0 <= ds_strstart X < 2 ^ 32;
  ok_look : 0 <= ds_lookahead X < 2 ^ 32;
  ok_bs : - 2 ^ 63 <= ds_block_start X < 2 ^ 63;
  ok_ins : 0 <= ds_insert X < 2 ^ 32;
  ok_sn : 0 <= ds_sym_next X < 2 ^ 32;
  ok_ain : 0 <= cs_avail_in (ds_strm X) < 2 ^ 32;
  ok_aout : 0 <= cs_avail_out (ds_strm X) < 2 ^ 32;
  ok_nin : 0 <= cs_next_in (ds_strm X) /\ cs_next_in (ds_strm X) + cs_avail_in (ds_strm X) = arr_len (cs_input (ds_strm X));
  ok_tin : 0 <= cs_total_in (ds_strm X) < 2 ^ 64;
  ok_tout : 0 <= cs_total_out (ds_strm X) < 2 ^ 64;
  ok_adler : 0 <= cs_adler (ds_strm X) < 2 ^ 64;
  ok_dt : - 2 ^ 31 <= cs_data_type (ds_strm X) < 2 ^ 31 }.

Definition fp_ok (X : deflate_state) : Prop :=
  let PBL := ds_lit_bufsize X * 4 in
  BINV PBL X
  /\ (let X1 := tr_flush_bits X in
      0 <= ds_pending X1 < 2 ^ 31 /\ ds_pending X1 <= PBL /\ 0 <= ds_pending_out X1 /\ ds_pending_out X1 + fp_len X1 <= PBL
      /\ 0 <= cs_total_out (ds_strm X1) < 2 ^ 64).

Definition lz_keeps (X X' : deflate_state) : Prop :=
  (ds_w_size X', ds_hash_size X', ds_lit_bufsize X') = (ds_w_size X, ds_hash_size X, ds_lit_bufsize X)
  /\ arr_len (ds_window X') = arr_len (ds_window X) /\ arr_len (ds_prev X') = arr_len (ds_prev X)
  /\ arr_len (ds_head X') = arr_len (ds_head X) /\ arr_len (ds_pending_buf X') = arr_len (ds_pending_buf X)
  /\ cs_input (ds_strm X') = cs_input (ds_strm X)
  /\ Z.of_nat (length (cs_out_rev (ds_strm X'))) + cs_avail_out (ds_strm X')
     = Z.of_nat (length (cs_out_rev (ds_strm X))) + cs_avail_out (ds_strm X)
  /\ 0 <= cs_avail_out (ds_strm X')
  /\ (length (cs_out_rev (ds_strm X)) <= length (cs_out_rev (ds_strm X')))%nat.

Definition fblk_ok (s : deflate_state) (last : Z) : Prop :=
  let PBL := ds_lit_bufsize s * 4 in
  let buf := if Z.leb 0 (ds_block_start s) then Some (wrap32 (ds_block_start s)) else None in
  let len := wrap64 (ds_strstart s - ds_block_start s) in
  FB s buf len last /\ BINV PBL s /\ 0 <= ds_strstart s - ds_block_start s < 2 ^ 32
  /\ - 2 ^ 63 <= ds_block_start s /\ 0 <= ds_strstart s <= 2 * ds_w_size s /\ 0 <= ds_lookahead s <= 2 * ds_w_size s
  /\ (forall j, 0 <= j < 2 * ds_w_size s -> 0 <= arr_get (ds_window s) j < 256)
  /\ let s8 := tr_flush_block s buf len last in
     let s9 := set_block_start s8 (ds_strstart s8) in
     BINV PBL s9 /\ ds_pending (tr_flush_bits s9) <= PBL
     /\ let s10 := tr_flush_bits s9 in
        0 <= ds_pending s10 < 2 ^ 31 /\ 0 <= ds_pending_out s10 /\ ds_pending_out s10 + fp_len s10 <= PBL
        /\ 0 <= cs_total_out (ds_strm s10) < 2 ^ 64
        /\ 0 <= cs_avail_out (ds_strm (flush_block_only s last)) < 2 ^ 32
        /\ lz_keeps s (flush_block_only s last).


Definition hf_fill (s : deflate_state) (flush : Z) : deflate_state * option loop_out :=
  if Z.eqb (ds_lookahead s) 0 then
    let s := fill_window s in
    if Z.eqb (ds_lookahead s) 0 then
      if Z.eqb flush Z_NO_FLUSH then (s, Some (LRet need_more)) else (s, Some LBreak)
    else (s, None)
  else (s, None).

Definition hf_tally (s : deflate_state) : deflate_state * bool :=
  let s := set_match_length s 0 in
  let '(s, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s)) in
  let s := set_lookahead s (ds_lookahead s - 1) in
  let s := set_strstart s (ds_strstart s + 1) in
  (s, bflush).

Definition st_bflush0 (s : deflate_state) (bflush : bool) : deflate_state * loop_out :=
  if bflush then
    let '(s, r) := flush_block s 0 in
    match r with Some bs => (s, LRet bs) | None => (s, LCont) end
  else (s, LCont).

Definition hf_body (s : deflate_state) (flush : Z) : deflate_state * loop_out :=
  let '(s1, e) := hf_fill s flush in
  match e with
  | Some o => (s1, o)
  | None => let '(s2, b) := hf_tally s1 in st_bflush0 s2 b
  end.

Definition hf_tally_ok (s1 : deflate_state) : Prop :=
  DOK s1 /\ 1 <= ds_lookahead s1 /\ ds_strstart s1 + ds_lookahead s1 <= 2 * ds_w_size s1
  /\ 0 <= ds_sym_next s1 /\ ds_sym_next s1 + 3 <= 3 * ds_lit_bufsize s1 /\ 0 <= ds_sym_end s1 < 2 ^ 32
  /\ (forall j, 0 <= j < 2 * ds_w_size s1 -> 0 <= arr_get (ds_window s1) j < 256)
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s1) i < 65536)
  /\ (snd (hf_tally s1) = true -> fblk_ok (fst (hf_tally s1)) 0).

Definition hf_trip_ok (s : deflate_state) (flush : Z) : Prop :=
  DOK s
  /\ (ds_lookahead s = 0 -> fw_wf (ds_w_size s) (ds_hash_size s) s /\ DOK (fill_window s) /\ lz_keeps s (fill_window s))
  /\ (snd (hf_fill s flush) = None -> hf_tally_ok (fst (hf_fill s flush))).

Fixpoint hf_loop_ok (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => False
  | S f => hf_trip_ok s flush
           /\ match snd (hf_body s flush) with
              | LCont => hf_loop_ok f (fst (hf_body s flush)) flush
              | _ => True
              end
  end.

Definition tail0 (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  deflate_tail (set_insert s 0) flush.

Definition tail0_ok (s : deflate_state) (flush : Z) : Prop :=
  let s := set_insert s 0 in
  DOK s
  /\ (flush = Z_FINISH -> fblk_ok s 1)
  /\ (flush <> Z_FINISH -> ds_sym_next s <> 0 -> fblk_ok s 0).

Definition huff_ok (s : deflate_state) (flush : Z) : Prop :=
  hf_loop_ok (lz_fuel s) s flush
  /\ match snd (deflate_huff_loop (lz_fuel s) s flush) with
     | Some _ => True
     | None => tail0_ok (fst (deflate_huff_loop (lz_fuel s) s flush)) flush
     end
  /\ lz_keeps s (fst (deflate_huff s flush)) /\ DOK (fst (deflate_huff s flush)).


Definition rl_fill (s : deflate_state) (flush : Z) : deflate_state * option loop_out :=
  if Z.leb (ds_lookahead s) MAX_MATCH then
    let s := fill_window s in
    if Z.leb (ds_lookahead s) MAX_MATCH && Z.eqb flush Z_NO_FLUSH then (s, Some (LRet need_more))
    else if Z.eqb (ds_lookahead s) 0 then (s, Some LBreak)
    else (s, None)
  else (s, None).

Definition rl_run (s : deflate_state) : deflate_state :=
  let s := set_match_length s 0 in
  if Z.leb MIN_MATCH (ds_lookahead s) && Z.ltb 0 (ds_strstart s) then
    let w := ds_window s in
    let scan := ds_strstart s - 1 in
    let prev := arr_get w scan in
    let '(scan, ok) := rle_cmpk 3%nat w prev scan in
    if ok then
      let strend := ds_strstart s + MAX_MATCH in
      let scan := rle_cmp_loop 33%nat w prev scan strend in
      let s := set_match_length s (MAX_MATCH - (strend - scan)) in
      if Z.ltb (ds_lookahead s) (ds_match_length s) then set_match_length s (ds_lookahead s) else s
    else s
  else s.

Definition rl_tally (s : deflate_state) : deflate_state * bool :=
  if Z.leb MIN_MATCH (ds_match_length s) then
    let '(s, bflush) := tr_tally_dist s 1 (ds_match_length s - MIN_MATCH) in
    let s := set_lookahead s (ds_lookahead s - ds_match_length s) in
    let s := set_strstart s (ds_strstart s + ds_match_length s) in
    let s := set_match_length s 0 in
    (s, bflush)
  else
    let '(s, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s)) in
    let s := set_lookahead s (ds_lookahead s - 1) in
    let s := set_strstart s (ds_strstart s + 1) in
    (s, bflush).

Definition rl_body (s : deflate_state) (flush : Z) : deflate_state * loop_out :=
  let '(s1, e) := rl_fill s flush in
  match e with
  | Some o => (s1, o)
  | None => let '(s3, b) := rl_tally (rl_run s1) in st_bflush0 s3 b
  end.

Definition rl_tally_ok (s2 : deflate_state) : Prop :=
  DOK s2 /\ 1 <= ds_lookahead s2 /\ ds_strstart s2 + ds_lookahead s2 <= 2 * ds_w_size s2
  /\ 0 <= ds_match_length s2 <= ds_lookahead s2 /\ ds_match_length s2 <= MAX_MATCH
  /\ 0 <= ds_sym_next s2 /\ ds_sym_next s2 + 3 <= 3 * ds_lit_bufsize s2 /\ 0 <= ds_sym_end s2 < 2 ^ 32
  /\ (forall j, 0 <= j < 2 * ds_w_size s2 -> 0 <= arr_get (ds_window s2) j < 256)
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s2) i < 65536)
  /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc s2) i < 65536)
  /\ (snd (rl_tally s2) = true -> fblk_ok (fst (rl_tally s2)) 0).

Definition rl_run_ok (s1 : deflate_state) : Prop :=
  DOK s1 /\ 1 <= ds_lookahead s1 /\ ds_strstart s1 + ds_lookahead s1 <= 2 * ds_w_size s1
  /\ (MIN_MATCH <= ds_lookahead s1 -> 0 < ds_strstart s1 -> ds_strstart s1 + MAX_MATCH < 2 * ds_w_size s1)
  /\ (forall j, 0 <= j < 2 * ds_w_size s1 -> 0 <= arr_get (ds_window s1) j < 256).

Definition rl_trip_ok (s : deflate_state) (flush : Z) : Prop :=
  DOK s
  /\ (ds_lookahead s <= MAX_MATCH -> fw_wf (ds_w_size s) (ds_hash_size s) s /\ DOK (fill_window s) /\ lz_keeps s (fill_window s))
  /\ (snd (rl_fill s flush) = None ->
      rl_run_ok (fst (rl_fill s flush)) /\ rl_tally_ok (rl_run (fst (rl_fill s flush)))).

Fixpoint rl_loop_ok (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => False
  | S f => rl_trip_ok s flush
           /\ match snd (rl_body s flush) with
              | LCont => rl_loop_ok f (fst (rl_body s flush)) flush
              | _ => True
              end
  end.

Definition rle_ok (s : deflate_state) (flush : Z) : Prop :=
  rl_loop_ok (lz_fuel s) s flush
  /\ match snd (deflate_rle_loop (lz_fuel s) s flush) with
     | Some _ => True
     | None => tail0_ok (fst (deflate_rle_loop (lz_fuel s) s flush)) flush
     end
  /\ lz_keeps s (fst (deflate_rle s flush)) /\ DOK (fst (deflate_rle s flush)).


Definition blk_keeps (s0 s' : deflate_state) : Prop :=
  (ds_self_blk s', ds_window_blk s', ds_prev_blk s', ds_head_blk s', ds_pending_buf_blk s')
  = (ds_self_blk s0, ds_window_blk s0, ds_prev_blk s0, ds_head_blk s0, ds_pending_buf_blk s0)
  /\ lz_keeps s0 s'.

Definition dpost_ok (s0 s' : deflate_state) (rc : Z) : Prop :=
  let st0 := ds_strm s0 in let st := ds_strm s' in
  WF s' /\ DOK s' /\ blk_keeps s0 s'
  /\ 0 <= cs_next_in st <= arr_len (cs_input st0)
  /\ cs_next_in st + cs_avail_in st = arr_len (cs_input st0)
  /\ Z.of_nat (length (cs_out_rev st)) + cs_avail_out st = Z.of_nat (length (cs_out_rev st0)) + cs_avail_out st0
  /\ 0 <= cs_avail_out st
  /\ Forall (fun b => 0 <= b < 256) (cs_output st)
  /\ - 2 ^ 31 <= rc < 2 ^ 31
  /\ (cs_total_out st = wrap64 (cs_total_out st0 + Z.of_nat (length (cs_out_rev st)) - Z.of_nat (length (cs_out_rev st0)))
      \/ (rc = Z_MEM_ERROR /\ cs_total_out st = cs_total_out st0)).

Definition blocks_call_ok (s : deflate_state) (flush : Z) : Prop :=
  let s' := fst (run_compress_func s flush) in
  lz_keeps s s' /\ DOK s'
  /\ (if Z.eqb (ds_level s) 0 then SAFEs s flush
      else if Z.eqb (ds_strategy s) Z_HUFFMAN_ONLY then huff_ok s flush
      else if Z.eqb (ds_strategy s) Z_RLE then rle_ok s flush
      else if Z.leb (ds_level s) 3 then SAFEf s flush
      else SAFEw s flush).

Definition bdone_st (s : deflate_state) (flush : Z) : deflate_state :=
  if Z.eqb flush Z_PARTIAL_FLUSH then tr_align s
  else if negb (Z.eqb flush Z_BLOCK) then
    let s := tr_stored_block s None 0 0 in
    if Z.eqb flush Z_FULL_FLUSH then
      let s := clear_hash s in
      if Z.eqb (ds_lookahead s) 0 then set_insert (set_block_start (set_strstart s 0) 0) 0 else s
    else s
  else s.

Definition bdone_ok (s : deflate_state) (flush : Z) : Prop :=
  let PBL := ds_lit_bufsize s * 4 in
  DOK s /\ BINV PBL s
  /\ (flush = Z_PARTIAL_FLUSH -> ds_pending (tr_align s) <= PBL)
  /\ (flush <> Z_PARTIAL_FLUSH -> flush <> Z_BLOCK -> ds_pending (tr_stored_block s None 0 0) <= PBL)
  /\ DOK (bdone_st s flush) /\ fp_ok (bdone_st s flush)
  /\ DOK (flush_pending (bdone_st s flush)).

Definition blocks_ok (s0 s : deflate_state) (flush : Z) : Prop :=
  DOK s
  /\ (negb (Z.eqb (cs_avail_in (ds_strm s)) 0) || negb (Z.eqb (ds_lookahead s) 0)
      || (negb (Z.eqb flush Z_NO_FLUSH) && negb (Z.eqb (ds_status s) FINISH_STATE)) = true ->
      blocks_call_ok s flush
      /\ let '(s1, bstate) := run_compress_func s flush in
         let s2 := if block_state_eqb bstate finish_started || block_state_eqb bstate finish_done
                   then set_status s1 FINISH_STATE else s1 in
         DOK s2
         /\ (block_state_eqb bstate need_more || block_state_eqb bstate finish_started = true ->
             dpost_ok s0 (if Z.eqb (cs_avail_out (ds_strm s2)) 0 then set_last_flush s2 (-1) else s2) Z_OK)
         /\ (bstate = block_done ->
             bdone_ok s2 flush
             /\ (Z.eqb (cs_avail_out (ds_strm (flush_pending (bdone_st s2 flush)))) 0 = true ->
                 dpost_ok s0 (set_last_flush (flush_pending (bdone_st s2 flush)) (-1)) Z_OK))).

Definition trailer_st (s : deflate_state) : deflate_state :=
  let st := ds_strm s in
  if Z.eqb (ds_wrap s) 2 then
    let a := cs_adler st in let t := cs_total_in st in
    let s := put_byte s (Z.land a 255) in
    let s := put_byte s (Z.land (Z.shiftr a 8) 255) in
    let s := put_byte s (Z.land (Z.shiftr a 16) 255) in
    let s := put_byte s (Z.land (Z.shiftr a 24) 255) in
    let s := put_byte s (Z.land t 255) in
    let s := put_byte s (Z.land (Z.shiftr t 8) 255) in
    let s := put_byte s (Z.land (Z.shiftr t 16) 255) in
    put_byte s (Z.land (Z.shiftr t 24) 255)
  else
    let a := cs_adler st in
    putShortMSB (putShortMSB s (wrap32 (Z.shiftr a 16))) (Z.land a 65535).

Definition trailer_ok (s0 s : deflate_state) : Prop :=
  let PBL := ds_lit_bufsize s * 4 in
  DOK s /\ 0 < ds_wrap s
  /\ ds_pending s + (if Z.eqb (ds_wrap s) 2 then 8 else 4) <= PBL
  /\ DOK (trailer_st s) /\ fp_ok (trailer_st s)
  /\ let s2 := flush_pending (trailer_st s) in
     DOK s2 /\ 0 <= ds_pending s2 < 2 ^ 64 /\ 0 < ds_wrap s2
     /\ dpost_ok s0 (set_wrap s2 (- ds_wrap s2)) (if negb (Z.eqb (ds_pending s2) 0) then Z_OK else Z_STREAM_END).

Definition zhdr_st (s : deflate_state) : deflate_state :=
  let header := Z.shiftl (Z_DEFLATED + Z.shiftl (ds_w_bits s - 8) 4) 8 in
  let level_flags :=
    if Z.leb Z_HUFFMAN_ONLY (ds_strategy s) || Z.ltb (ds_level s) 2 then 0
    else if Z.ltb (ds_level s) 6 then 1
    else if Z.eqb (ds_level s) 6 then 2
    else 3 in
  let header := Z.lor header (Z.shiftl level_flags 6) in
  let header := if negb (Z.eqb (ds_strstart s) 0) then Z.lor header PRESET_DICT else header in
  let header := header + (31 - header mod 31) in
  let s := putShortMSB s header in
  let s :=
    if negb (Z.eqb (ds_strstart s) 0) then
      let adler := cs_adler (ds_strm s) in
      let s := putShortMSB s (wrap32 (Z.shiftr adler 16)) in
      putShortMSB s (Z.land adler 65535)
    else s in
  let s := set_strm s (cset_adler (ds_strm s) adler32_init) in
  set_status s BUSY_STATE.

Definition gzhdr_st (s : deflate_state) : deflate_state :=
  let s := set_strm s (cset_adler (ds_strm s) crc32_init) in
  let s := put_byte s 31 in
  let s := put_byte s 139 in
  let s := put_byte s 8 in
  let s := put_byte s 0 in
  let s := put_byte s 0 in
  let s := put_byte s 0 in
  let s := put_byte s 0 in
  let s := put_byte s 0 in
  let s := put_byte s (if Z.eqb (ds_level s) 9 then 2
                       else if Z.leb Z_HUFFMAN_ONLY (ds_strategy s) || Z.ltb (ds_level s) 2 then 4
                       else 0) in
  let s := put_byte s OS_CODE in
  set_status s BUSY_STATE.

Definition hdr_ok (s0 s : deflate_state) (hst : deflate_state) (room : Z) : Prop :=
  DOK s /\ ds_pending s + room <= ds_lit_bufsize s * 4
  /\ DOK hst /\ fp_ok hst
  /\ let s2 := flush_pending hst in
     DOK s2 /\ 0 <= ds_pending s2 < 2 ^ 64
     /\ (ds_pending s2 <> 0 -> dpost_ok s0 (set_last_flush s2 (-1)) Z_OK).

Definition finish_ok (s0 s : deflate_state) (flush : Z) : Prop :=
  DOK s
  /\ (flush <> Z_FINISH -> dpost_ok s0 s Z_OK)
  /\ (flush = Z_FINISH -> ds_wrap s <= 0 -> dpost_ok s0 s Z_STREAM_END)
  /\ (flush = Z_FINISH -> 0 < ds_wrap s -> trailer_ok s0 s).

Definition body_ok (s0 s : deflate_state) (flush : Z) : Prop :=
  DOK s
  /\ (ds_status s = FINISH_STATE /\ cs_avail_in (ds_strm s) <> 0 ->
      dpost_ok s0 (fst (err_return s Z_BUF_ERROR)) Z_BUF_ERROR)
  /\ (~ (ds_status s = FINISH_STATE /\ cs_avail_in (ds_strm s) <> 0) ->
      let s4 := if Z.eqb (ds_status s) INIT_STATE && Z.eqb (ds_wrap s) 0 then set_status s BUSY_STATE else s in
      DOK s4
      /\ (ds_status s4 = INIT_STATE -> hdr_ok s0 s4 (zhdr_st s4) 6)
      /\ let s5 := if Z.eqb (ds_status s4) INIT_STATE then flush_pending (zhdr_st s4) else s4 in
         ((ds_status s4 = INIT_STATE -> ds_pending s5 = 0) ->
          (ds_status s5 = GZIP_STATE -> hdr_ok s0 s5 (gzhdr_st s5) 10)
          /\ let s6 := if Z.eqb (ds_status s5) GZIP_STATE then flush_pending (gzhdr_st s5) else s5 in
             ((ds_status s5 = GZIP_STATE -> ds_pending s6 = 0) ->
              blocks_ok s0 s6 flush
              /\ (snd (deflate_blocks s6 flush) = None -> finish_ok s0 (fst (deflate_blocks s6 flush)) flush)))).

Definition rank_err (s0 : deflate_state) (flush : Z) : Prop :=
  cs_avail_in (ds_strm s0) = 0 /\ RANK flush <= RANK (ds_last_flush s0) /\ flush <> Z_FINISH.

Definition deflate_safe (ds : deflate_state) (zc : ZCall) (flush : Z) : Prop :=
  let s0 := set_strm ds (cstrm_of_call zc) in
  DOK s0 /\ deflateStateCheck s0 = false /\ - 2 <= ds_last_flush s0 <= 5
  /\
     dpost_ok s0 s0 Z_STREAM_ERROR
  /\ dpost_ok s0 (fst (err_return s0 Z_STREAM_ERROR)) Z_STREAM_ERROR
  /\ dpost_ok s0 (fst (err_return s0 Z_BUF_ERROR)) Z_BUF_ERROR
  /\ (flush <= 5 -> ~ (ds_status s0 = FINISH_STATE /\ flush <> Z_FINISH) -> cs_avail_out (ds_strm s0) <> 0 ->
      let s1 := set_last_flush s0 flush in
      DOK s1
      /\ (ds_pending s1 <> 0 ->
          fp_ok s1
          /\ let s2 := flush_pending s1 in
             DOK s2
             /\ (cs_avail_out (ds_strm s2) = 0 -> dpost_ok s0 (set_last_flush s2 (-1)) Z_OK)
             /\ (cs_avail_out (ds_strm s2) <> 0 -> body_ok s0 s2 flush))
      /\ (ds_pending s1 = 0 ->
          (rank_err s0 flush -> dpost_ok s0 (fst (err_return s1 Z_BUF_ERROR)) Z_BUF_ERROR)
          /\ (~ rank_err s0 flush -> body_ok s0 s1 flush))).

End Obligations.


Lemma hf_body_eq : forall s flush, deflate_huff_body s flush = hf_body s flush.
Proof.
  intros s flush. unfold deflate_huff_body, hf_body, hf_fill, hf_tally, st_bflush0.
  destruct (ds_lookahead s =? 0).
  - destruct (ds_lookahead (fill_window s) =? 0); [destruct (flush =? Z_NO_FLUSH); reflexivity|].
    destruct (tr_tally_lit _ _) as [s2 b]. reflexivity.
  - destruct (tr_tally_lit _ _) as [s2 b]. reflexivity.
Qed.

Lemma rl_body_eq : forall s flush, deflate_rle_body s flush = rl_body s flush.
Proof.
  intros s flush. unfold deflate_rle_body, rl_body, rl_fill, rl_run, rl_tally, st_bflush0.
  destruct (ds_lookahead s <=? MAX_MATCH).
  - destruct (_ && (flush =? Z_NO_FLUSH)); [reflexivity|].
    destruct (ds_lookahead (fill_window s) =? 0); [reflexivity|].
    set (s1 := set_match_length (fill_window s) 0). clearbody s1.
    destruct (_ && _); [destruct (rle_cmpk 3 _ _ _) as [sc ok]; destruct ok|];
      (destruct (MIN_MATCH <=? _); [destruct (tr_tally_dist _ _ _) as [s3 b] | destruct (tr_tally_lit _ _) as [s3 b]]; reflexivity).
  - set (s1 := set_match_length s 0). clearbody s1.
    destruct (_ && _); [destruct (rle_cmpk 3 _ _ _) as [sc ok]; destruct ok|];
      (destruct (MIN_MATCH <=? _); [destruct (tr_tally_dist _ _ _) as [s3 b] | destruct (tr_tally_lit _ _) as [s3 b]]; reflexivity).
Qed.

Lemma deflate_huff_tail0 : forall s flush,
  deflate_huff s flush = match deflate_huff_loop (lz_fuel s) s flush with
                         | (s', Some bs) => (s', bs)
                         | (s', None) => tail0 s' flush
                         end.
Proof. intros s flush. unfold deflate_huff, tail0. destruct (deflate_huff_loop _ _ _) as [s' [bs|]]; reflexivity. Qed.

Lemma deflate_rle_tail0 : forall s flush,
  deflate_rle s flush = match deflate_rle_loop (lz_fuel s) s flush with
                        | (s', Some bs) => (s', bs)
                        | (s', None) => tail0 s' flush
                        end.
Proof. intros s flush. unfold deflate_rle, tail0. destruct (deflate_rle_loop _ _ _) as [s' [bs|]]; reflexivity. Qed.

Lemma deflate_zlib_header_eq : forall s,
  deflate_zlib_header s =
  (let s2 := flush_pending (zhdr_st s) in
   if negb (Z.eqb (ds_pending s2) 0) then (set_last_flush s2 (-1), Some Z_OK) else (s2, None)).
Proof. intros s. reflexivity. Qed.

Lemma deflate_gzip_header_eq : forall s,
  deflate_gzip_header s =
  (let s2 := flush_pending (gzhdr_st s) in
   if negb (Z.eqb (ds_pending s2) 0) then (set_last_flush s2 (-1), Some Z_OK) else (s2, None)).
Proof. intros s. reflexivity. Qed.

Lemma deflate_trailer_eq : forall s,
  deflate_trailer s =
  (let s2 := flush_pending (trailer_st s) in
   let s3 := if Z.ltb 0 (ds_wrap s2) then set_wrap s2 (- ds_wrap s2) else s2 in
   (s3, if negb (Z.eqb (ds_pending s3) 0) then Z_OK else Z_STREAM_END)).
Proof. intros s. reflexivity. Qed.

Lemma hf_loop_ok_S : forall FB f s flush,
  hf_loop_ok FB (S f) s flush
  = (hf_trip_ok FB s flush /\ match snd (hf_body s flush) with LCont => hf_loop_ok FB f (fst (hf_body s flush)) flush | _ => True end).
Proof. reflexivity. Qed.
Lemma rl_loop_ok_S : forall FB f s flush,
  rl_loop_ok FB (S f) s flush
  = (rl_trip_ok FB s flush /\ match snd (rl_body s flush) with LCont => rl_loop_ok FB f (fst (rl_body s flush)) flush | _ => True end).
Proof. reflexivity. Qed.
