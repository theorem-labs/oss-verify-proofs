(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Create HintDb dsf discriminated.

Lemma status_set_pending_buf : forall s v, ds_status (set_pending_buf s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_pending_buf : forall s v, ds_pending_buf (set_pending_buf s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_pending_buf : forall s v, ds_pending_buf_size (set_pending_buf s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_pending_buf : forall s v, ds_pending_out (set_pending_buf s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_pending_buf : forall s v, ds_pending (set_pending_buf s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_pending_buf : forall s v, ds_wrap (set_pending_buf s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_pending_buf : forall s v, ds_gzhead (set_pending_buf s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_pending_buf : forall s v, ds_gzindex (set_pending_buf s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_pending_buf : forall s v, ds_method (set_pending_buf s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_pending_buf : forall s v, ds_last_flush (set_pending_buf s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_pending_buf : forall s v, ds_w_size (set_pending_buf s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_pending_buf : forall s v, ds_w_bits (set_pending_buf s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_pending_buf : forall s v, ds_w_mask (set_pending_buf s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_pending_buf : forall s v, ds_window (set_pending_buf s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_pending_buf : forall s v, ds_window_size (set_pending_buf s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_pending_buf : forall s v, ds_prev (set_pending_buf s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_pending_buf : forall s v, ds_head (set_pending_buf s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_pending_buf : forall s v, ds_ins_h (set_pending_buf s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_pending_buf : forall s v, ds_hash_size (set_pending_buf s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_pending_buf : forall s v, ds_hash_bits (set_pending_buf s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_pending_buf : forall s v, ds_hash_mask (set_pending_buf s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_pending_buf : forall s v, ds_hash_shift (set_pending_buf s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_pending_buf : forall s v, ds_block_start (set_pending_buf s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_pending_buf : forall s v, ds_match_length (set_pending_buf s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_pending_buf : forall s v, ds_prev_match (set_pending_buf s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_pending_buf : forall s v, ds_match_available (set_pending_buf s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_pending_buf : forall s v, ds_strstart (set_pending_buf s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_pending_buf : forall s v, ds_match_start (set_pending_buf s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_pending_buf : forall s v, ds_lookahead (set_pending_buf s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_pending_buf : forall s v, ds_prev_length (set_pending_buf s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_pending_buf : forall s v, ds_max_chain_length (set_pending_buf s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_pending_buf : forall s v, ds_max_lazy_match (set_pending_buf s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_pending_buf : forall s v, ds_level (set_pending_buf s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_pending_buf : forall s v, ds_strategy (set_pending_buf s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_pending_buf : forall s v, ds_good_match (set_pending_buf s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_pending_buf : forall s v, ds_nice_match (set_pending_buf s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_pending_buf : forall s v, ds_dyn_ltree_fc (set_pending_buf s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_pending_buf : forall s v, ds_dyn_ltree_dl (set_pending_buf s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_pending_buf : forall s v, ds_dyn_dtree_fc (set_pending_buf s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_pending_buf : forall s v, ds_dyn_dtree_dl (set_pending_buf s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_pending_buf : forall s v, ds_bl_tree_fc (set_pending_buf s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_pending_buf : forall s v, ds_bl_tree_dl (set_pending_buf s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_pending_buf : forall s v, ds_l_max_code (set_pending_buf s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_pending_buf : forall s v, ds_d_max_code (set_pending_buf s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_pending_buf : forall s v, ds_bl_max_code (set_pending_buf s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_pending_buf : forall s v, ds_bl_count (set_pending_buf s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_pending_buf : forall s v, ds_heap (set_pending_buf s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_pending_buf : forall s v, ds_heap_len (set_pending_buf s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_pending_buf : forall s v, ds_heap_max (set_pending_buf s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_pending_buf : forall s v, ds_depth (set_pending_buf s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_pending_buf : forall s v, ds_lit_bufsize (set_pending_buf s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_pending_buf : forall s v, ds_sym_next (set_pending_buf s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_pending_buf : forall s v, ds_sym_end (set_pending_buf s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_pending_buf : forall s v, ds_opt_len (set_pending_buf s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_pending_buf : forall s v, ds_static_len (set_pending_buf s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_pending_buf : forall s v, ds_matches (set_pending_buf s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_pending_buf : forall s v, ds_insert (set_pending_buf s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_pending_buf : forall s v, ds_bi_buf (set_pending_buf s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_pending_buf : forall s v, ds_bi_valid (set_pending_buf s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_pending_buf : forall s v, ds_high_water (set_pending_buf s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_pending_buf : forall s v, ds_self_blk (set_pending_buf s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_pending_buf : forall s v, ds_window_blk (set_pending_buf s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_pending_buf : forall s v, ds_prev_blk (set_pending_buf s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_pending_buf : forall s v, ds_head_blk (set_pending_buf s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_pending_buf : forall s v, ds_pending_buf_blk (set_pending_buf s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_pending_buf : forall s v, ds_strm (set_pending_buf s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_pending_buf pending_buf_set_pending_buf pending_buf_size_set_pending_buf pending_out_set_pending_buf pending_set_pending_buf wrap_set_pending_buf gzhead_set_pending_buf gzindex_set_pending_buf method_set_pending_buf last_flush_set_pending_buf w_size_set_pending_buf w_bits_set_pending_buf w_mask_set_pending_buf window_set_pending_buf window_size_set_pending_buf prev_set_pending_buf head_set_pending_buf ins_h_set_pending_buf hash_size_set_pending_buf hash_bits_set_pending_buf hash_mask_set_pending_buf hash_shift_set_pending_buf block_start_set_pending_buf match_length_set_pending_buf prev_match_set_pending_buf match_available_set_pending_buf strstart_set_pending_buf match_start_set_pending_buf lookahead_set_pending_buf prev_length_set_pending_buf max_chain_length_set_pending_buf max_lazy_match_set_pending_buf level_set_pending_buf strategy_set_pending_buf good_match_set_pending_buf nice_match_set_pending_buf dyn_ltree_fc_set_pending_buf dyn_ltree_dl_set_pending_buf dyn_dtree_fc_set_pending_buf dyn_dtree_dl_set_pending_buf bl_tree_fc_set_pending_buf bl_tree_dl_set_pending_buf l_max_code_set_pending_buf d_max_code_set_pending_buf bl_max_code_set_pending_buf bl_count_set_pending_buf heap_set_pending_buf heap_len_set_pending_buf heap_max_set_pending_buf depth_set_pending_buf lit_bufsize_set_pending_buf sym_next_set_pending_buf sym_end_set_pending_buf opt_len_set_pending_buf static_len_set_pending_buf matches_set_pending_buf insert_set_pending_buf bi_buf_set_pending_buf bi_valid_set_pending_buf high_water_set_pending_buf self_blk_set_pending_buf window_blk_set_pending_buf prev_blk_set_pending_buf head_blk_set_pending_buf pending_buf_blk_set_pending_buf strm_set_pending_buf : dsf.
Lemma status_set_pending : forall s v, ds_status (set_pending s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_pending : forall s v, ds_pending_buf (set_pending s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_pending : forall s v, ds_pending_buf_size (set_pending s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_pending : forall s v, ds_pending_out (set_pending s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_pending : forall s v, ds_pending (set_pending s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_pending : forall s v, ds_wrap (set_pending s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_pending : forall s v, ds_gzhead (set_pending s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_pending : forall s v, ds_gzindex (set_pending s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_pending : forall s v, ds_method (set_pending s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_pending : forall s v, ds_last_flush (set_pending s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_pending : forall s v, ds_w_size (set_pending s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_pending : forall s v, ds_w_bits (set_pending s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_pending : forall s v, ds_w_mask (set_pending s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_pending : forall s v, ds_window (set_pending s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_pending : forall s v, ds_window_size (set_pending s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_pending : forall s v, ds_prev (set_pending s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_pending : forall s v, ds_head (set_pending s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_pending : forall s v, ds_ins_h (set_pending s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_pending : forall s v, ds_hash_size (set_pending s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_pending : forall s v, ds_hash_bits (set_pending s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_pending : forall s v, ds_hash_mask (set_pending s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_pending : forall s v, ds_hash_shift (set_pending s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_pending : forall s v, ds_block_start (set_pending s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_pending : forall s v, ds_match_length (set_pending s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_pending : forall s v, ds_prev_match (set_pending s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_pending : forall s v, ds_match_available (set_pending s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_pending : forall s v, ds_strstart (set_pending s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_pending : forall s v, ds_match_start (set_pending s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_pending : forall s v, ds_lookahead (set_pending s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_pending : forall s v, ds_prev_length (set_pending s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_pending : forall s v, ds_max_chain_length (set_pending s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_pending : forall s v, ds_max_lazy_match (set_pending s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_pending : forall s v, ds_level (set_pending s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_pending : forall s v, ds_strategy (set_pending s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_pending : forall s v, ds_good_match (set_pending s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_pending : forall s v, ds_nice_match (set_pending s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_pending : forall s v, ds_dyn_ltree_fc (set_pending s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_pending : forall s v, ds_dyn_ltree_dl (set_pending s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_pending : forall s v, ds_dyn_dtree_fc (set_pending s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_pending : forall s v, ds_dyn_dtree_dl (set_pending s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_pending : forall s v, ds_bl_tree_fc (set_pending s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_pending : forall s v, ds_bl_tree_dl (set_pending s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_pending : forall s v, ds_l_max_code (set_pending s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_pending : forall s v, ds_d_max_code (set_pending s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_pending : forall s v, ds_bl_max_code (set_pending s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_pending : forall s v, ds_bl_count (set_pending s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_pending : forall s v, ds_heap (set_pending s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_pending : forall s v, ds_heap_len (set_pending s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_pending : forall s v, ds_heap_max (set_pending s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_pending : forall s v, ds_depth (set_pending s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_pending : forall s v, ds_lit_bufsize (set_pending s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_pending : forall s v, ds_sym_next (set_pending s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_pending : forall s v, ds_sym_end (set_pending s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_pending : forall s v, ds_opt_len (set_pending s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_pending : forall s v, ds_static_len (set_pending s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_pending : forall s v, ds_matches (set_pending s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_pending : forall s v, ds_insert (set_pending s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_pending : forall s v, ds_bi_buf (set_pending s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_pending : forall s v, ds_bi_valid (set_pending s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_pending : forall s v, ds_high_water (set_pending s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_pending : forall s v, ds_self_blk (set_pending s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_pending : forall s v, ds_window_blk (set_pending s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_pending : forall s v, ds_prev_blk (set_pending s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_pending : forall s v, ds_head_blk (set_pending s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_pending : forall s v, ds_pending_buf_blk (set_pending s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_pending : forall s v, ds_strm (set_pending s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_pending pending_buf_set_pending pending_buf_size_set_pending pending_out_set_pending pending_set_pending wrap_set_pending gzhead_set_pending gzindex_set_pending method_set_pending last_flush_set_pending w_size_set_pending w_bits_set_pending w_mask_set_pending window_set_pending window_size_set_pending prev_set_pending head_set_pending ins_h_set_pending hash_size_set_pending hash_bits_set_pending hash_mask_set_pending hash_shift_set_pending block_start_set_pending match_length_set_pending prev_match_set_pending match_available_set_pending strstart_set_pending match_start_set_pending lookahead_set_pending prev_length_set_pending max_chain_length_set_pending max_lazy_match_set_pending level_set_pending strategy_set_pending good_match_set_pending nice_match_set_pending dyn_ltree_fc_set_pending dyn_ltree_dl_set_pending dyn_dtree_fc_set_pending dyn_dtree_dl_set_pending bl_tree_fc_set_pending bl_tree_dl_set_pending l_max_code_set_pending d_max_code_set_pending bl_max_code_set_pending bl_count_set_pending heap_set_pending heap_len_set_pending heap_max_set_pending depth_set_pending lit_bufsize_set_pending sym_next_set_pending sym_end_set_pending opt_len_set_pending static_len_set_pending matches_set_pending insert_set_pending bi_buf_set_pending bi_valid_set_pending high_water_set_pending self_blk_set_pending window_blk_set_pending prev_blk_set_pending head_blk_set_pending pending_buf_blk_set_pending strm_set_pending : dsf.
Lemma status_set_pending_out : forall s v, ds_status (set_pending_out s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_pending_out : forall s v, ds_pending_buf (set_pending_out s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_pending_out : forall s v, ds_pending_buf_size (set_pending_out s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_pending_out : forall s v, ds_pending_out (set_pending_out s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_pending_out : forall s v, ds_pending (set_pending_out s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_pending_out : forall s v, ds_wrap (set_pending_out s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_pending_out : forall s v, ds_gzhead (set_pending_out s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_pending_out : forall s v, ds_gzindex (set_pending_out s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_pending_out : forall s v, ds_method (set_pending_out s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_pending_out : forall s v, ds_last_flush (set_pending_out s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_pending_out : forall s v, ds_w_size (set_pending_out s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_pending_out : forall s v, ds_w_bits (set_pending_out s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_pending_out : forall s v, ds_w_mask (set_pending_out s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_pending_out : forall s v, ds_window (set_pending_out s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_pending_out : forall s v, ds_window_size (set_pending_out s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_pending_out : forall s v, ds_prev (set_pending_out s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_pending_out : forall s v, ds_head (set_pending_out s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_pending_out : forall s v, ds_ins_h (set_pending_out s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_pending_out : forall s v, ds_hash_size (set_pending_out s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_pending_out : forall s v, ds_hash_bits (set_pending_out s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_pending_out : forall s v, ds_hash_mask (set_pending_out s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_pending_out : forall s v, ds_hash_shift (set_pending_out s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_pending_out : forall s v, ds_block_start (set_pending_out s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_pending_out : forall s v, ds_match_length (set_pending_out s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_pending_out : forall s v, ds_prev_match (set_pending_out s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_pending_out : forall s v, ds_match_available (set_pending_out s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_pending_out : forall s v, ds_strstart (set_pending_out s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_pending_out : forall s v, ds_match_start (set_pending_out s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_pending_out : forall s v, ds_lookahead (set_pending_out s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_pending_out : forall s v, ds_prev_length (set_pending_out s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_pending_out : forall s v, ds_max_chain_length (set_pending_out s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_pending_out : forall s v, ds_max_lazy_match (set_pending_out s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_pending_out : forall s v, ds_level (set_pending_out s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_pending_out : forall s v, ds_strategy (set_pending_out s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_pending_out : forall s v, ds_good_match (set_pending_out s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_pending_out : forall s v, ds_nice_match (set_pending_out s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_pending_out : forall s v, ds_dyn_ltree_fc (set_pending_out s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_pending_out : forall s v, ds_dyn_ltree_dl (set_pending_out s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_pending_out : forall s v, ds_dyn_dtree_fc (set_pending_out s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_pending_out : forall s v, ds_dyn_dtree_dl (set_pending_out s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_pending_out : forall s v, ds_bl_tree_fc (set_pending_out s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_pending_out : forall s v, ds_bl_tree_dl (set_pending_out s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_pending_out : forall s v, ds_l_max_code (set_pending_out s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_pending_out : forall s v, ds_d_max_code (set_pending_out s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_pending_out : forall s v, ds_bl_max_code (set_pending_out s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_pending_out : forall s v, ds_bl_count (set_pending_out s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_pending_out : forall s v, ds_heap (set_pending_out s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_pending_out : forall s v, ds_heap_len (set_pending_out s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_pending_out : forall s v, ds_heap_max (set_pending_out s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_pending_out : forall s v, ds_depth (set_pending_out s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_pending_out : forall s v, ds_lit_bufsize (set_pending_out s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_pending_out : forall s v, ds_sym_next (set_pending_out s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_pending_out : forall s v, ds_sym_end (set_pending_out s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_pending_out : forall s v, ds_opt_len (set_pending_out s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_pending_out : forall s v, ds_static_len (set_pending_out s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_pending_out : forall s v, ds_matches (set_pending_out s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_pending_out : forall s v, ds_insert (set_pending_out s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_pending_out : forall s v, ds_bi_buf (set_pending_out s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_pending_out : forall s v, ds_bi_valid (set_pending_out s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_pending_out : forall s v, ds_high_water (set_pending_out s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_pending_out : forall s v, ds_self_blk (set_pending_out s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_pending_out : forall s v, ds_window_blk (set_pending_out s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_pending_out : forall s v, ds_prev_blk (set_pending_out s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_pending_out : forall s v, ds_head_blk (set_pending_out s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_pending_out : forall s v, ds_pending_buf_blk (set_pending_out s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_pending_out : forall s v, ds_strm (set_pending_out s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_pending_out pending_buf_set_pending_out pending_buf_size_set_pending_out pending_out_set_pending_out pending_set_pending_out wrap_set_pending_out gzhead_set_pending_out gzindex_set_pending_out method_set_pending_out last_flush_set_pending_out w_size_set_pending_out w_bits_set_pending_out w_mask_set_pending_out window_set_pending_out window_size_set_pending_out prev_set_pending_out head_set_pending_out ins_h_set_pending_out hash_size_set_pending_out hash_bits_set_pending_out hash_mask_set_pending_out hash_shift_set_pending_out block_start_set_pending_out match_length_set_pending_out prev_match_set_pending_out match_available_set_pending_out strstart_set_pending_out match_start_set_pending_out lookahead_set_pending_out prev_length_set_pending_out max_chain_length_set_pending_out max_lazy_match_set_pending_out level_set_pending_out strategy_set_pending_out good_match_set_pending_out nice_match_set_pending_out dyn_ltree_fc_set_pending_out dyn_ltree_dl_set_pending_out dyn_dtree_fc_set_pending_out dyn_dtree_dl_set_pending_out bl_tree_fc_set_pending_out bl_tree_dl_set_pending_out l_max_code_set_pending_out d_max_code_set_pending_out bl_max_code_set_pending_out bl_count_set_pending_out heap_set_pending_out heap_len_set_pending_out heap_max_set_pending_out depth_set_pending_out lit_bufsize_set_pending_out sym_next_set_pending_out sym_end_set_pending_out opt_len_set_pending_out static_len_set_pending_out matches_set_pending_out insert_set_pending_out bi_buf_set_pending_out bi_valid_set_pending_out high_water_set_pending_out self_blk_set_pending_out window_blk_set_pending_out prev_blk_set_pending_out head_blk_set_pending_out pending_buf_blk_set_pending_out strm_set_pending_out : dsf.
Lemma status_set_bi_buf : forall s v, ds_status (set_bi_buf s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_bi_buf : forall s v, ds_pending_buf (set_bi_buf s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_bi_buf : forall s v, ds_pending_buf_size (set_bi_buf s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_bi_buf : forall s v, ds_pending_out (set_bi_buf s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_bi_buf : forall s v, ds_pending (set_bi_buf s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_bi_buf : forall s v, ds_wrap (set_bi_buf s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_bi_buf : forall s v, ds_gzhead (set_bi_buf s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_bi_buf : forall s v, ds_gzindex (set_bi_buf s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_bi_buf : forall s v, ds_method (set_bi_buf s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_bi_buf : forall s v, ds_last_flush (set_bi_buf s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_bi_buf : forall s v, ds_w_size (set_bi_buf s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_bi_buf : forall s v, ds_w_bits (set_bi_buf s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_bi_buf : forall s v, ds_w_mask (set_bi_buf s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_bi_buf : forall s v, ds_window (set_bi_buf s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_bi_buf : forall s v, ds_window_size (set_bi_buf s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_bi_buf : forall s v, ds_prev (set_bi_buf s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_bi_buf : forall s v, ds_head (set_bi_buf s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_bi_buf : forall s v, ds_ins_h (set_bi_buf s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_bi_buf : forall s v, ds_hash_size (set_bi_buf s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_bi_buf : forall s v, ds_hash_bits (set_bi_buf s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_bi_buf : forall s v, ds_hash_mask (set_bi_buf s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_bi_buf : forall s v, ds_hash_shift (set_bi_buf s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_bi_buf : forall s v, ds_block_start (set_bi_buf s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_bi_buf : forall s v, ds_match_length (set_bi_buf s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_bi_buf : forall s v, ds_prev_match (set_bi_buf s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_bi_buf : forall s v, ds_match_available (set_bi_buf s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_bi_buf : forall s v, ds_strstart (set_bi_buf s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_bi_buf : forall s v, ds_match_start (set_bi_buf s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_bi_buf : forall s v, ds_lookahead (set_bi_buf s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_bi_buf : forall s v, ds_prev_length (set_bi_buf s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_bi_buf : forall s v, ds_max_chain_length (set_bi_buf s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_bi_buf : forall s v, ds_max_lazy_match (set_bi_buf s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_bi_buf : forall s v, ds_level (set_bi_buf s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_bi_buf : forall s v, ds_strategy (set_bi_buf s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_bi_buf : forall s v, ds_good_match (set_bi_buf s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_bi_buf : forall s v, ds_nice_match (set_bi_buf s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_bi_buf : forall s v, ds_dyn_ltree_fc (set_bi_buf s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_bi_buf : forall s v, ds_dyn_ltree_dl (set_bi_buf s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_bi_buf : forall s v, ds_dyn_dtree_fc (set_bi_buf s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_bi_buf : forall s v, ds_dyn_dtree_dl (set_bi_buf s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_bi_buf : forall s v, ds_bl_tree_fc (set_bi_buf s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_bi_buf : forall s v, ds_bl_tree_dl (set_bi_buf s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_bi_buf : forall s v, ds_l_max_code (set_bi_buf s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_bi_buf : forall s v, ds_d_max_code (set_bi_buf s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_bi_buf : forall s v, ds_bl_max_code (set_bi_buf s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_bi_buf : forall s v, ds_bl_count (set_bi_buf s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_bi_buf : forall s v, ds_heap (set_bi_buf s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_bi_buf : forall s v, ds_heap_len (set_bi_buf s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_bi_buf : forall s v, ds_heap_max (set_bi_buf s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_bi_buf : forall s v, ds_depth (set_bi_buf s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_bi_buf : forall s v, ds_lit_bufsize (set_bi_buf s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_bi_buf : forall s v, ds_sym_next (set_bi_buf s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_bi_buf : forall s v, ds_sym_end (set_bi_buf s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_bi_buf : forall s v, ds_opt_len (set_bi_buf s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_bi_buf : forall s v, ds_static_len (set_bi_buf s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_bi_buf : forall s v, ds_matches (set_bi_buf s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_bi_buf : forall s v, ds_insert (set_bi_buf s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_bi_buf : forall s v, ds_bi_buf (set_bi_buf s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_bi_buf : forall s v, ds_bi_valid (set_bi_buf s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_bi_buf : forall s v, ds_high_water (set_bi_buf s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_bi_buf : forall s v, ds_self_blk (set_bi_buf s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_bi_buf : forall s v, ds_window_blk (set_bi_buf s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_bi_buf : forall s v, ds_prev_blk (set_bi_buf s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_bi_buf : forall s v, ds_head_blk (set_bi_buf s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_bi_buf : forall s v, ds_pending_buf_blk (set_bi_buf s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_bi_buf : forall s v, ds_strm (set_bi_buf s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_bi_buf pending_buf_set_bi_buf pending_buf_size_set_bi_buf pending_out_set_bi_buf pending_set_bi_buf wrap_set_bi_buf gzhead_set_bi_buf gzindex_set_bi_buf method_set_bi_buf last_flush_set_bi_buf w_size_set_bi_buf w_bits_set_bi_buf w_mask_set_bi_buf window_set_bi_buf window_size_set_bi_buf prev_set_bi_buf head_set_bi_buf ins_h_set_bi_buf hash_size_set_bi_buf hash_bits_set_bi_buf hash_mask_set_bi_buf hash_shift_set_bi_buf block_start_set_bi_buf match_length_set_bi_buf prev_match_set_bi_buf match_available_set_bi_buf strstart_set_bi_buf match_start_set_bi_buf lookahead_set_bi_buf prev_length_set_bi_buf max_chain_length_set_bi_buf max_lazy_match_set_bi_buf level_set_bi_buf strategy_set_bi_buf good_match_set_bi_buf nice_match_set_bi_buf dyn_ltree_fc_set_bi_buf dyn_ltree_dl_set_bi_buf dyn_dtree_fc_set_bi_buf dyn_dtree_dl_set_bi_buf bl_tree_fc_set_bi_buf bl_tree_dl_set_bi_buf l_max_code_set_bi_buf d_max_code_set_bi_buf bl_max_code_set_bi_buf bl_count_set_bi_buf heap_set_bi_buf heap_len_set_bi_buf heap_max_set_bi_buf depth_set_bi_buf lit_bufsize_set_bi_buf sym_next_set_bi_buf sym_end_set_bi_buf opt_len_set_bi_buf static_len_set_bi_buf matches_set_bi_buf insert_set_bi_buf bi_buf_set_bi_buf bi_valid_set_bi_buf high_water_set_bi_buf self_blk_set_bi_buf window_blk_set_bi_buf prev_blk_set_bi_buf head_blk_set_bi_buf pending_buf_blk_set_bi_buf strm_set_bi_buf : dsf.
Lemma status_set_bi_valid : forall s v, ds_status (set_bi_valid s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_bi_valid : forall s v, ds_pending_buf (set_bi_valid s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_bi_valid : forall s v, ds_pending_buf_size (set_bi_valid s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_bi_valid : forall s v, ds_pending_out (set_bi_valid s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_bi_valid : forall s v, ds_pending (set_bi_valid s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_bi_valid : forall s v, ds_wrap (set_bi_valid s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_bi_valid : forall s v, ds_gzhead (set_bi_valid s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_bi_valid : forall s v, ds_gzindex (set_bi_valid s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_bi_valid : forall s v, ds_method (set_bi_valid s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_bi_valid : forall s v, ds_last_flush (set_bi_valid s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_bi_valid : forall s v, ds_w_size (set_bi_valid s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_bi_valid : forall s v, ds_w_bits (set_bi_valid s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_bi_valid : forall s v, ds_w_mask (set_bi_valid s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_bi_valid : forall s v, ds_window (set_bi_valid s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_bi_valid : forall s v, ds_window_size (set_bi_valid s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_bi_valid : forall s v, ds_prev (set_bi_valid s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_bi_valid : forall s v, ds_head (set_bi_valid s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_bi_valid : forall s v, ds_ins_h (set_bi_valid s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_bi_valid : forall s v, ds_hash_size (set_bi_valid s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_bi_valid : forall s v, ds_hash_bits (set_bi_valid s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_bi_valid : forall s v, ds_hash_mask (set_bi_valid s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_bi_valid : forall s v, ds_hash_shift (set_bi_valid s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_bi_valid : forall s v, ds_block_start (set_bi_valid s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_bi_valid : forall s v, ds_match_length (set_bi_valid s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_bi_valid : forall s v, ds_prev_match (set_bi_valid s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_bi_valid : forall s v, ds_match_available (set_bi_valid s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_bi_valid : forall s v, ds_strstart (set_bi_valid s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_bi_valid : forall s v, ds_match_start (set_bi_valid s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_bi_valid : forall s v, ds_lookahead (set_bi_valid s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_bi_valid : forall s v, ds_prev_length (set_bi_valid s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_bi_valid : forall s v, ds_max_chain_length (set_bi_valid s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_bi_valid : forall s v, ds_max_lazy_match (set_bi_valid s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_bi_valid : forall s v, ds_level (set_bi_valid s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_bi_valid : forall s v, ds_strategy (set_bi_valid s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_bi_valid : forall s v, ds_good_match (set_bi_valid s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_bi_valid : forall s v, ds_nice_match (set_bi_valid s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_bi_valid : forall s v, ds_dyn_ltree_fc (set_bi_valid s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_bi_valid : forall s v, ds_dyn_ltree_dl (set_bi_valid s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_bi_valid : forall s v, ds_dyn_dtree_fc (set_bi_valid s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_bi_valid : forall s v, ds_dyn_dtree_dl (set_bi_valid s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_bi_valid : forall s v, ds_bl_tree_fc (set_bi_valid s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_bi_valid : forall s v, ds_bl_tree_dl (set_bi_valid s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_bi_valid : forall s v, ds_l_max_code (set_bi_valid s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_bi_valid : forall s v, ds_d_max_code (set_bi_valid s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_bi_valid : forall s v, ds_bl_max_code (set_bi_valid s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_bi_valid : forall s v, ds_bl_count (set_bi_valid s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_bi_valid : forall s v, ds_heap (set_bi_valid s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_bi_valid : forall s v, ds_heap_len (set_bi_valid s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_bi_valid : forall s v, ds_heap_max (set_bi_valid s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_bi_valid : forall s v, ds_depth (set_bi_valid s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_bi_valid : forall s v, ds_lit_bufsize (set_bi_valid s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_bi_valid : forall s v, ds_sym_next (set_bi_valid s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_bi_valid : forall s v, ds_sym_end (set_bi_valid s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_bi_valid : forall s v, ds_opt_len (set_bi_valid s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_bi_valid : forall s v, ds_static_len (set_bi_valid s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_bi_valid : forall s v, ds_matches (set_bi_valid s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_bi_valid : forall s v, ds_insert (set_bi_valid s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_bi_valid : forall s v, ds_bi_buf (set_bi_valid s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_bi_valid : forall s v, ds_bi_valid (set_bi_valid s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_bi_valid : forall s v, ds_high_water (set_bi_valid s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_bi_valid : forall s v, ds_self_blk (set_bi_valid s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_bi_valid : forall s v, ds_window_blk (set_bi_valid s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_bi_valid : forall s v, ds_prev_blk (set_bi_valid s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_bi_valid : forall s v, ds_head_blk (set_bi_valid s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_bi_valid : forall s v, ds_pending_buf_blk (set_bi_valid s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_bi_valid : forall s v, ds_strm (set_bi_valid s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_bi_valid pending_buf_set_bi_valid pending_buf_size_set_bi_valid pending_out_set_bi_valid pending_set_bi_valid wrap_set_bi_valid gzhead_set_bi_valid gzindex_set_bi_valid method_set_bi_valid last_flush_set_bi_valid w_size_set_bi_valid w_bits_set_bi_valid w_mask_set_bi_valid window_set_bi_valid window_size_set_bi_valid prev_set_bi_valid head_set_bi_valid ins_h_set_bi_valid hash_size_set_bi_valid hash_bits_set_bi_valid hash_mask_set_bi_valid hash_shift_set_bi_valid block_start_set_bi_valid match_length_set_bi_valid prev_match_set_bi_valid match_available_set_bi_valid strstart_set_bi_valid match_start_set_bi_valid lookahead_set_bi_valid prev_length_set_bi_valid max_chain_length_set_bi_valid max_lazy_match_set_bi_valid level_set_bi_valid strategy_set_bi_valid good_match_set_bi_valid nice_match_set_bi_valid dyn_ltree_fc_set_bi_valid dyn_ltree_dl_set_bi_valid dyn_dtree_fc_set_bi_valid dyn_dtree_dl_set_bi_valid bl_tree_fc_set_bi_valid bl_tree_dl_set_bi_valid l_max_code_set_bi_valid d_max_code_set_bi_valid bl_max_code_set_bi_valid bl_count_set_bi_valid heap_set_bi_valid heap_len_set_bi_valid heap_max_set_bi_valid depth_set_bi_valid lit_bufsize_set_bi_valid sym_next_set_bi_valid sym_end_set_bi_valid opt_len_set_bi_valid static_len_set_bi_valid matches_set_bi_valid insert_set_bi_valid bi_buf_set_bi_valid bi_valid_set_bi_valid high_water_set_bi_valid self_blk_set_bi_valid window_blk_set_bi_valid prev_blk_set_bi_valid head_blk_set_bi_valid pending_buf_blk_set_bi_valid strm_set_bi_valid : dsf.
Lemma status_set_strm : forall s v, ds_status (set_strm s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_strm : forall s v, ds_pending_buf (set_strm s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_strm : forall s v, ds_pending_buf_size (set_strm s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_strm : forall s v, ds_pending_out (set_strm s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_strm : forall s v, ds_pending (set_strm s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_strm : forall s v, ds_wrap (set_strm s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_strm : forall s v, ds_gzhead (set_strm s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_strm : forall s v, ds_gzindex (set_strm s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_strm : forall s v, ds_method (set_strm s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_strm : forall s v, ds_last_flush (set_strm s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_strm : forall s v, ds_w_size (set_strm s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_strm : forall s v, ds_w_bits (set_strm s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_strm : forall s v, ds_w_mask (set_strm s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_strm : forall s v, ds_window (set_strm s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_strm : forall s v, ds_window_size (set_strm s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_strm : forall s v, ds_prev (set_strm s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_strm : forall s v, ds_head (set_strm s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_strm : forall s v, ds_ins_h (set_strm s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_strm : forall s v, ds_hash_size (set_strm s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_strm : forall s v, ds_hash_bits (set_strm s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_strm : forall s v, ds_hash_mask (set_strm s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_strm : forall s v, ds_hash_shift (set_strm s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_strm : forall s v, ds_block_start (set_strm s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_strm : forall s v, ds_match_length (set_strm s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_strm : forall s v, ds_prev_match (set_strm s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_strm : forall s v, ds_match_available (set_strm s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_strm : forall s v, ds_strstart (set_strm s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_strm : forall s v, ds_match_start (set_strm s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_strm : forall s v, ds_lookahead (set_strm s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_strm : forall s v, ds_prev_length (set_strm s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_strm : forall s v, ds_max_chain_length (set_strm s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_strm : forall s v, ds_max_lazy_match (set_strm s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_strm : forall s v, ds_level (set_strm s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_strm : forall s v, ds_strategy (set_strm s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_strm : forall s v, ds_good_match (set_strm s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_strm : forall s v, ds_nice_match (set_strm s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_strm : forall s v, ds_dyn_ltree_fc (set_strm s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_strm : forall s v, ds_dyn_ltree_dl (set_strm s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_strm : forall s v, ds_dyn_dtree_fc (set_strm s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_strm : forall s v, ds_dyn_dtree_dl (set_strm s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_strm : forall s v, ds_bl_tree_fc (set_strm s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_strm : forall s v, ds_bl_tree_dl (set_strm s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_strm : forall s v, ds_l_max_code (set_strm s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_strm : forall s v, ds_d_max_code (set_strm s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_strm : forall s v, ds_bl_max_code (set_strm s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_strm : forall s v, ds_bl_count (set_strm s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_strm : forall s v, ds_heap (set_strm s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_strm : forall s v, ds_heap_len (set_strm s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_strm : forall s v, ds_heap_max (set_strm s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_strm : forall s v, ds_depth (set_strm s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_strm : forall s v, ds_lit_bufsize (set_strm s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_strm : forall s v, ds_sym_next (set_strm s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_strm : forall s v, ds_sym_end (set_strm s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_strm : forall s v, ds_opt_len (set_strm s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_strm : forall s v, ds_static_len (set_strm s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_strm : forall s v, ds_matches (set_strm s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_strm : forall s v, ds_insert (set_strm s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_strm : forall s v, ds_bi_buf (set_strm s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_strm : forall s v, ds_bi_valid (set_strm s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_strm : forall s v, ds_high_water (set_strm s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_strm : forall s v, ds_self_blk (set_strm s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_strm : forall s v, ds_window_blk (set_strm s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_strm : forall s v, ds_prev_blk (set_strm s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_strm : forall s v, ds_head_blk (set_strm s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_strm : forall s v, ds_pending_buf_blk (set_strm s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_strm : forall s v, ds_strm (set_strm s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_strm pending_buf_set_strm pending_buf_size_set_strm pending_out_set_strm pending_set_strm wrap_set_strm gzhead_set_strm gzindex_set_strm method_set_strm last_flush_set_strm w_size_set_strm w_bits_set_strm w_mask_set_strm window_set_strm window_size_set_strm prev_set_strm head_set_strm ins_h_set_strm hash_size_set_strm hash_bits_set_strm hash_mask_set_strm hash_shift_set_strm block_start_set_strm match_length_set_strm prev_match_set_strm match_available_set_strm strstart_set_strm match_start_set_strm lookahead_set_strm prev_length_set_strm max_chain_length_set_strm max_lazy_match_set_strm level_set_strm strategy_set_strm good_match_set_strm nice_match_set_strm dyn_ltree_fc_set_strm dyn_ltree_dl_set_strm dyn_dtree_fc_set_strm dyn_dtree_dl_set_strm bl_tree_fc_set_strm bl_tree_dl_set_strm l_max_code_set_strm d_max_code_set_strm bl_max_code_set_strm bl_count_set_strm heap_set_strm heap_len_set_strm heap_max_set_strm depth_set_strm lit_bufsize_set_strm sym_next_set_strm sym_end_set_strm opt_len_set_strm static_len_set_strm matches_set_strm insert_set_strm bi_buf_set_strm bi_valid_set_strm high_water_set_strm self_blk_set_strm window_blk_set_strm prev_blk_set_strm head_blk_set_strm pending_buf_blk_set_strm strm_set_strm : dsf.
Lemma status_set_status : forall s v, ds_status (set_status s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_status : forall s v, ds_pending_buf (set_status s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_status : forall s v, ds_pending_buf_size (set_status s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_status : forall s v, ds_pending_out (set_status s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_status : forall s v, ds_pending (set_status s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_status : forall s v, ds_wrap (set_status s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_status : forall s v, ds_gzhead (set_status s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_status : forall s v, ds_gzindex (set_status s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_status : forall s v, ds_method (set_status s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_status : forall s v, ds_last_flush (set_status s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_status : forall s v, ds_w_size (set_status s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_status : forall s v, ds_w_bits (set_status s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_status : forall s v, ds_w_mask (set_status s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_status : forall s v, ds_window (set_status s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_status : forall s v, ds_window_size (set_status s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_status : forall s v, ds_prev (set_status s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_status : forall s v, ds_head (set_status s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_status : forall s v, ds_ins_h (set_status s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_status : forall s v, ds_hash_size (set_status s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_status : forall s v, ds_hash_bits (set_status s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_status : forall s v, ds_hash_mask (set_status s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_status : forall s v, ds_hash_shift (set_status s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_status : forall s v, ds_block_start (set_status s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_status : forall s v, ds_match_length (set_status s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_status : forall s v, ds_prev_match (set_status s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_status : forall s v, ds_match_available (set_status s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_status : forall s v, ds_strstart (set_status s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_status : forall s v, ds_match_start (set_status s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_status : forall s v, ds_lookahead (set_status s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_status : forall s v, ds_prev_length (set_status s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_status : forall s v, ds_max_chain_length (set_status s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_status : forall s v, ds_max_lazy_match (set_status s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_status : forall s v, ds_level (set_status s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_status : forall s v, ds_strategy (set_status s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_status : forall s v, ds_good_match (set_status s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_status : forall s v, ds_nice_match (set_status s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_status : forall s v, ds_dyn_ltree_fc (set_status s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_status : forall s v, ds_dyn_ltree_dl (set_status s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_status : forall s v, ds_dyn_dtree_fc (set_status s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_status : forall s v, ds_dyn_dtree_dl (set_status s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_status : forall s v, ds_bl_tree_fc (set_status s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_status : forall s v, ds_bl_tree_dl (set_status s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_status : forall s v, ds_l_max_code (set_status s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_status : forall s v, ds_d_max_code (set_status s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_status : forall s v, ds_bl_max_code (set_status s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_status : forall s v, ds_bl_count (set_status s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_status : forall s v, ds_heap (set_status s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_status : forall s v, ds_heap_len (set_status s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_status : forall s v, ds_heap_max (set_status s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_status : forall s v, ds_depth (set_status s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_status : forall s v, ds_lit_bufsize (set_status s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_status : forall s v, ds_sym_next (set_status s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_status : forall s v, ds_sym_end (set_status s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_status : forall s v, ds_opt_len (set_status s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_status : forall s v, ds_static_len (set_status s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_status : forall s v, ds_matches (set_status s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_status : forall s v, ds_insert (set_status s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_status : forall s v, ds_bi_buf (set_status s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_status : forall s v, ds_bi_valid (set_status s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_status : forall s v, ds_high_water (set_status s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_status : forall s v, ds_self_blk (set_status s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_status : forall s v, ds_window_blk (set_status s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_status : forall s v, ds_prev_blk (set_status s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_status : forall s v, ds_head_blk (set_status s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_status : forall s v, ds_pending_buf_blk (set_status s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_status : forall s v, ds_strm (set_status s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_status pending_buf_set_status pending_buf_size_set_status pending_out_set_status pending_set_status wrap_set_status gzhead_set_status gzindex_set_status method_set_status last_flush_set_status w_size_set_status w_bits_set_status w_mask_set_status window_set_status window_size_set_status prev_set_status head_set_status ins_h_set_status hash_size_set_status hash_bits_set_status hash_mask_set_status hash_shift_set_status block_start_set_status match_length_set_status prev_match_set_status match_available_set_status strstart_set_status match_start_set_status lookahead_set_status prev_length_set_status max_chain_length_set_status max_lazy_match_set_status level_set_status strategy_set_status good_match_set_status nice_match_set_status dyn_ltree_fc_set_status dyn_ltree_dl_set_status dyn_dtree_fc_set_status dyn_dtree_dl_set_status bl_tree_fc_set_status bl_tree_dl_set_status l_max_code_set_status d_max_code_set_status bl_max_code_set_status bl_count_set_status heap_set_status heap_len_set_status heap_max_set_status depth_set_status lit_bufsize_set_status sym_next_set_status sym_end_set_status opt_len_set_status static_len_set_status matches_set_status insert_set_status bi_buf_set_status bi_valid_set_status high_water_set_status self_blk_set_status window_blk_set_status prev_blk_set_status head_blk_set_status pending_buf_blk_set_status strm_set_status : dsf.
Lemma status_set_last_flush : forall s v, ds_status (set_last_flush s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_last_flush : forall s v, ds_pending_buf (set_last_flush s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_last_flush : forall s v, ds_pending_buf_size (set_last_flush s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_last_flush : forall s v, ds_pending_out (set_last_flush s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_last_flush : forall s v, ds_pending (set_last_flush s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_last_flush : forall s v, ds_wrap (set_last_flush s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_last_flush : forall s v, ds_gzhead (set_last_flush s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_last_flush : forall s v, ds_gzindex (set_last_flush s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_last_flush : forall s v, ds_method (set_last_flush s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_last_flush : forall s v, ds_last_flush (set_last_flush s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_last_flush : forall s v, ds_w_size (set_last_flush s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_last_flush : forall s v, ds_w_bits (set_last_flush s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_last_flush : forall s v, ds_w_mask (set_last_flush s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_last_flush : forall s v, ds_window (set_last_flush s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_last_flush : forall s v, ds_window_size (set_last_flush s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_last_flush : forall s v, ds_prev (set_last_flush s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_last_flush : forall s v, ds_head (set_last_flush s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_last_flush : forall s v, ds_ins_h (set_last_flush s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_last_flush : forall s v, ds_hash_size (set_last_flush s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_last_flush : forall s v, ds_hash_bits (set_last_flush s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_last_flush : forall s v, ds_hash_mask (set_last_flush s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_last_flush : forall s v, ds_hash_shift (set_last_flush s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_last_flush : forall s v, ds_block_start (set_last_flush s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_last_flush : forall s v, ds_match_length (set_last_flush s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_last_flush : forall s v, ds_prev_match (set_last_flush s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_last_flush : forall s v, ds_match_available (set_last_flush s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_last_flush : forall s v, ds_strstart (set_last_flush s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_last_flush : forall s v, ds_match_start (set_last_flush s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_last_flush : forall s v, ds_lookahead (set_last_flush s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_last_flush : forall s v, ds_prev_length (set_last_flush s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_last_flush : forall s v, ds_max_chain_length (set_last_flush s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_last_flush : forall s v, ds_max_lazy_match (set_last_flush s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_last_flush : forall s v, ds_level (set_last_flush s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_last_flush : forall s v, ds_strategy (set_last_flush s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_last_flush : forall s v, ds_good_match (set_last_flush s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_last_flush : forall s v, ds_nice_match (set_last_flush s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_last_flush : forall s v, ds_dyn_ltree_fc (set_last_flush s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_last_flush : forall s v, ds_dyn_ltree_dl (set_last_flush s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_last_flush : forall s v, ds_dyn_dtree_fc (set_last_flush s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_last_flush : forall s v, ds_dyn_dtree_dl (set_last_flush s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_last_flush : forall s v, ds_bl_tree_fc (set_last_flush s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_last_flush : forall s v, ds_bl_tree_dl (set_last_flush s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_last_flush : forall s v, ds_l_max_code (set_last_flush s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_last_flush : forall s v, ds_d_max_code (set_last_flush s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_last_flush : forall s v, ds_bl_max_code (set_last_flush s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_last_flush : forall s v, ds_bl_count (set_last_flush s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_last_flush : forall s v, ds_heap (set_last_flush s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_last_flush : forall s v, ds_heap_len (set_last_flush s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_last_flush : forall s v, ds_heap_max (set_last_flush s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_last_flush : forall s v, ds_depth (set_last_flush s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_last_flush : forall s v, ds_lit_bufsize (set_last_flush s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_last_flush : forall s v, ds_sym_next (set_last_flush s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_last_flush : forall s v, ds_sym_end (set_last_flush s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_last_flush : forall s v, ds_opt_len (set_last_flush s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_last_flush : forall s v, ds_static_len (set_last_flush s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_last_flush : forall s v, ds_matches (set_last_flush s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_last_flush : forall s v, ds_insert (set_last_flush s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_last_flush : forall s v, ds_bi_buf (set_last_flush s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_last_flush : forall s v, ds_bi_valid (set_last_flush s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_last_flush : forall s v, ds_high_water (set_last_flush s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_last_flush : forall s v, ds_self_blk (set_last_flush s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_last_flush : forall s v, ds_window_blk (set_last_flush s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_last_flush : forall s v, ds_prev_blk (set_last_flush s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_last_flush : forall s v, ds_head_blk (set_last_flush s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_last_flush : forall s v, ds_pending_buf_blk (set_last_flush s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_last_flush : forall s v, ds_strm (set_last_flush s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_last_flush pending_buf_set_last_flush pending_buf_size_set_last_flush pending_out_set_last_flush pending_set_last_flush wrap_set_last_flush gzhead_set_last_flush gzindex_set_last_flush method_set_last_flush last_flush_set_last_flush w_size_set_last_flush w_bits_set_last_flush w_mask_set_last_flush window_set_last_flush window_size_set_last_flush prev_set_last_flush head_set_last_flush ins_h_set_last_flush hash_size_set_last_flush hash_bits_set_last_flush hash_mask_set_last_flush hash_shift_set_last_flush block_start_set_last_flush match_length_set_last_flush prev_match_set_last_flush match_available_set_last_flush strstart_set_last_flush match_start_set_last_flush lookahead_set_last_flush prev_length_set_last_flush max_chain_length_set_last_flush max_lazy_match_set_last_flush level_set_last_flush strategy_set_last_flush good_match_set_last_flush nice_match_set_last_flush dyn_ltree_fc_set_last_flush dyn_ltree_dl_set_last_flush dyn_dtree_fc_set_last_flush dyn_dtree_dl_set_last_flush bl_tree_fc_set_last_flush bl_tree_dl_set_last_flush l_max_code_set_last_flush d_max_code_set_last_flush bl_max_code_set_last_flush bl_count_set_last_flush heap_set_last_flush heap_len_set_last_flush heap_max_set_last_flush depth_set_last_flush lit_bufsize_set_last_flush sym_next_set_last_flush sym_end_set_last_flush opt_len_set_last_flush static_len_set_last_flush matches_set_last_flush insert_set_last_flush bi_buf_set_last_flush bi_valid_set_last_flush high_water_set_last_flush self_blk_set_last_flush window_blk_set_last_flush prev_blk_set_last_flush head_blk_set_last_flush pending_buf_blk_set_last_flush strm_set_last_flush : dsf.
Lemma status_set_wrap : forall s v, ds_status (set_wrap s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_wrap : forall s v, ds_pending_buf (set_wrap s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_wrap : forall s v, ds_pending_buf_size (set_wrap s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_wrap : forall s v, ds_pending_out (set_wrap s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_wrap : forall s v, ds_pending (set_wrap s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_wrap : forall s v, ds_wrap (set_wrap s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_wrap : forall s v, ds_gzhead (set_wrap s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_wrap : forall s v, ds_gzindex (set_wrap s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_wrap : forall s v, ds_method (set_wrap s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_wrap : forall s v, ds_last_flush (set_wrap s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_wrap : forall s v, ds_w_size (set_wrap s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_wrap : forall s v, ds_w_bits (set_wrap s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_wrap : forall s v, ds_w_mask (set_wrap s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_wrap : forall s v, ds_window (set_wrap s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_wrap : forall s v, ds_window_size (set_wrap s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_wrap : forall s v, ds_prev (set_wrap s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_wrap : forall s v, ds_head (set_wrap s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_wrap : forall s v, ds_ins_h (set_wrap s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_wrap : forall s v, ds_hash_size (set_wrap s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_wrap : forall s v, ds_hash_bits (set_wrap s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_wrap : forall s v, ds_hash_mask (set_wrap s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_wrap : forall s v, ds_hash_shift (set_wrap s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_wrap : forall s v, ds_block_start (set_wrap s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_wrap : forall s v, ds_match_length (set_wrap s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_wrap : forall s v, ds_prev_match (set_wrap s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_wrap : forall s v, ds_match_available (set_wrap s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_wrap : forall s v, ds_strstart (set_wrap s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_wrap : forall s v, ds_match_start (set_wrap s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_wrap : forall s v, ds_lookahead (set_wrap s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_wrap : forall s v, ds_prev_length (set_wrap s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_wrap : forall s v, ds_max_chain_length (set_wrap s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_wrap : forall s v, ds_max_lazy_match (set_wrap s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_wrap : forall s v, ds_level (set_wrap s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_wrap : forall s v, ds_strategy (set_wrap s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_wrap : forall s v, ds_good_match (set_wrap s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_wrap : forall s v, ds_nice_match (set_wrap s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_wrap : forall s v, ds_dyn_ltree_fc (set_wrap s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_wrap : forall s v, ds_dyn_ltree_dl (set_wrap s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_wrap : forall s v, ds_dyn_dtree_fc (set_wrap s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_wrap : forall s v, ds_dyn_dtree_dl (set_wrap s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_wrap : forall s v, ds_bl_tree_fc (set_wrap s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_wrap : forall s v, ds_bl_tree_dl (set_wrap s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_wrap : forall s v, ds_l_max_code (set_wrap s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_wrap : forall s v, ds_d_max_code (set_wrap s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_wrap : forall s v, ds_bl_max_code (set_wrap s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_wrap : forall s v, ds_bl_count (set_wrap s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_wrap : forall s v, ds_heap (set_wrap s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_wrap : forall s v, ds_heap_len (set_wrap s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_wrap : forall s v, ds_heap_max (set_wrap s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_wrap : forall s v, ds_depth (set_wrap s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_wrap : forall s v, ds_lit_bufsize (set_wrap s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_wrap : forall s v, ds_sym_next (set_wrap s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_wrap : forall s v, ds_sym_end (set_wrap s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_wrap : forall s v, ds_opt_len (set_wrap s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_wrap : forall s v, ds_static_len (set_wrap s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_wrap : forall s v, ds_matches (set_wrap s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_wrap : forall s v, ds_insert (set_wrap s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_wrap : forall s v, ds_bi_buf (set_wrap s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_wrap : forall s v, ds_bi_valid (set_wrap s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_wrap : forall s v, ds_high_water (set_wrap s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_wrap : forall s v, ds_self_blk (set_wrap s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_wrap : forall s v, ds_window_blk (set_wrap s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_wrap : forall s v, ds_prev_blk (set_wrap s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_wrap : forall s v, ds_head_blk (set_wrap s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_wrap : forall s v, ds_pending_buf_blk (set_wrap s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_wrap : forall s v, ds_strm (set_wrap s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_wrap pending_buf_set_wrap pending_buf_size_set_wrap pending_out_set_wrap pending_set_wrap wrap_set_wrap gzhead_set_wrap gzindex_set_wrap method_set_wrap last_flush_set_wrap w_size_set_wrap w_bits_set_wrap w_mask_set_wrap window_set_wrap window_size_set_wrap prev_set_wrap head_set_wrap ins_h_set_wrap hash_size_set_wrap hash_bits_set_wrap hash_mask_set_wrap hash_shift_set_wrap block_start_set_wrap match_length_set_wrap prev_match_set_wrap match_available_set_wrap strstart_set_wrap match_start_set_wrap lookahead_set_wrap prev_length_set_wrap max_chain_length_set_wrap max_lazy_match_set_wrap level_set_wrap strategy_set_wrap good_match_set_wrap nice_match_set_wrap dyn_ltree_fc_set_wrap dyn_ltree_dl_set_wrap dyn_dtree_fc_set_wrap dyn_dtree_dl_set_wrap bl_tree_fc_set_wrap bl_tree_dl_set_wrap l_max_code_set_wrap d_max_code_set_wrap bl_max_code_set_wrap bl_count_set_wrap heap_set_wrap heap_len_set_wrap heap_max_set_wrap depth_set_wrap lit_bufsize_set_wrap sym_next_set_wrap sym_end_set_wrap opt_len_set_wrap static_len_set_wrap matches_set_wrap insert_set_wrap bi_buf_set_wrap bi_valid_set_wrap high_water_set_wrap self_blk_set_wrap window_blk_set_wrap prev_blk_set_wrap head_blk_set_wrap pending_buf_blk_set_wrap strm_set_wrap : dsf.
Lemma status_set_window : forall s v, ds_status (set_window s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_window : forall s v, ds_pending_buf (set_window s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_window : forall s v, ds_pending_buf_size (set_window s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_window : forall s v, ds_pending_out (set_window s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_window : forall s v, ds_pending (set_window s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_window : forall s v, ds_wrap (set_window s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_window : forall s v, ds_gzhead (set_window s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_window : forall s v, ds_gzindex (set_window s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_window : forall s v, ds_method (set_window s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_window : forall s v, ds_last_flush (set_window s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_window : forall s v, ds_w_size (set_window s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_window : forall s v, ds_w_bits (set_window s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_window : forall s v, ds_w_mask (set_window s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_window : forall s v, ds_window (set_window s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_window : forall s v, ds_window_size (set_window s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_window : forall s v, ds_prev (set_window s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_window : forall s v, ds_head (set_window s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_window : forall s v, ds_ins_h (set_window s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_window : forall s v, ds_hash_size (set_window s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_window : forall s v, ds_hash_bits (set_window s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_window : forall s v, ds_hash_mask (set_window s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_window : forall s v, ds_hash_shift (set_window s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_window : forall s v, ds_block_start (set_window s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_window : forall s v, ds_match_length (set_window s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_window : forall s v, ds_prev_match (set_window s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_window : forall s v, ds_match_available (set_window s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_window : forall s v, ds_strstart (set_window s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_window : forall s v, ds_match_start (set_window s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_window : forall s v, ds_lookahead (set_window s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_window : forall s v, ds_prev_length (set_window s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_window : forall s v, ds_max_chain_length (set_window s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_window : forall s v, ds_max_lazy_match (set_window s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_window : forall s v, ds_level (set_window s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_window : forall s v, ds_strategy (set_window s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_window : forall s v, ds_good_match (set_window s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_window : forall s v, ds_nice_match (set_window s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_window : forall s v, ds_dyn_ltree_fc (set_window s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_window : forall s v, ds_dyn_ltree_dl (set_window s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_window : forall s v, ds_dyn_dtree_fc (set_window s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_window : forall s v, ds_dyn_dtree_dl (set_window s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_window : forall s v, ds_bl_tree_fc (set_window s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_window : forall s v, ds_bl_tree_dl (set_window s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_window : forall s v, ds_l_max_code (set_window s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_window : forall s v, ds_d_max_code (set_window s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_window : forall s v, ds_bl_max_code (set_window s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_window : forall s v, ds_bl_count (set_window s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_window : forall s v, ds_heap (set_window s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_window : forall s v, ds_heap_len (set_window s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_window : forall s v, ds_heap_max (set_window s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_window : forall s v, ds_depth (set_window s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_window : forall s v, ds_lit_bufsize (set_window s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_window : forall s v, ds_sym_next (set_window s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_window : forall s v, ds_sym_end (set_window s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_window : forall s v, ds_opt_len (set_window s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_window : forall s v, ds_static_len (set_window s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_window : forall s v, ds_matches (set_window s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_window : forall s v, ds_insert (set_window s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_window : forall s v, ds_bi_buf (set_window s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_window : forall s v, ds_bi_valid (set_window s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_window : forall s v, ds_high_water (set_window s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_window : forall s v, ds_self_blk (set_window s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_window : forall s v, ds_window_blk (set_window s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_window : forall s v, ds_prev_blk (set_window s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_window : forall s v, ds_head_blk (set_window s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_window : forall s v, ds_pending_buf_blk (set_window s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_window : forall s v, ds_strm (set_window s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_window pending_buf_set_window pending_buf_size_set_window pending_out_set_window pending_set_window wrap_set_window gzhead_set_window gzindex_set_window method_set_window last_flush_set_window w_size_set_window w_bits_set_window w_mask_set_window window_set_window window_size_set_window prev_set_window head_set_window ins_h_set_window hash_size_set_window hash_bits_set_window hash_mask_set_window hash_shift_set_window block_start_set_window match_length_set_window prev_match_set_window match_available_set_window strstart_set_window match_start_set_window lookahead_set_window prev_length_set_window max_chain_length_set_window max_lazy_match_set_window level_set_window strategy_set_window good_match_set_window nice_match_set_window dyn_ltree_fc_set_window dyn_ltree_dl_set_window dyn_dtree_fc_set_window dyn_dtree_dl_set_window bl_tree_fc_set_window bl_tree_dl_set_window l_max_code_set_window d_max_code_set_window bl_max_code_set_window bl_count_set_window heap_set_window heap_len_set_window heap_max_set_window depth_set_window lit_bufsize_set_window sym_next_set_window sym_end_set_window opt_len_set_window static_len_set_window matches_set_window insert_set_window bi_buf_set_window bi_valid_set_window high_water_set_window self_blk_set_window window_blk_set_window prev_blk_set_window head_blk_set_window pending_buf_blk_set_window strm_set_window : dsf.
Lemma status_set_prev : forall s v, ds_status (set_prev s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_prev : forall s v, ds_pending_buf (set_prev s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_prev : forall s v, ds_pending_buf_size (set_prev s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_prev : forall s v, ds_pending_out (set_prev s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_prev : forall s v, ds_pending (set_prev s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_prev : forall s v, ds_wrap (set_prev s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_prev : forall s v, ds_gzhead (set_prev s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_prev : forall s v, ds_gzindex (set_prev s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_prev : forall s v, ds_method (set_prev s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_prev : forall s v, ds_last_flush (set_prev s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_prev : forall s v, ds_w_size (set_prev s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_prev : forall s v, ds_w_bits (set_prev s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_prev : forall s v, ds_w_mask (set_prev s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_prev : forall s v, ds_window (set_prev s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_prev : forall s v, ds_window_size (set_prev s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_prev : forall s v, ds_prev (set_prev s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_prev : forall s v, ds_head (set_prev s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_prev : forall s v, ds_ins_h (set_prev s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_prev : forall s v, ds_hash_size (set_prev s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_prev : forall s v, ds_hash_bits (set_prev s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_prev : forall s v, ds_hash_mask (set_prev s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_prev : forall s v, ds_hash_shift (set_prev s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_prev : forall s v, ds_block_start (set_prev s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_prev : forall s v, ds_match_length (set_prev s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_prev : forall s v, ds_prev_match (set_prev s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_prev : forall s v, ds_match_available (set_prev s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_prev : forall s v, ds_strstart (set_prev s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_prev : forall s v, ds_match_start (set_prev s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_prev : forall s v, ds_lookahead (set_prev s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_prev : forall s v, ds_prev_length (set_prev s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_prev : forall s v, ds_max_chain_length (set_prev s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_prev : forall s v, ds_max_lazy_match (set_prev s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_prev : forall s v, ds_level (set_prev s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_prev : forall s v, ds_strategy (set_prev s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_prev : forall s v, ds_good_match (set_prev s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_prev : forall s v, ds_nice_match (set_prev s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_prev : forall s v, ds_dyn_ltree_fc (set_prev s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_prev : forall s v, ds_dyn_ltree_dl (set_prev s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_prev : forall s v, ds_dyn_dtree_fc (set_prev s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_prev : forall s v, ds_dyn_dtree_dl (set_prev s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_prev : forall s v, ds_bl_tree_fc (set_prev s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_prev : forall s v, ds_bl_tree_dl (set_prev s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_prev : forall s v, ds_l_max_code (set_prev s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_prev : forall s v, ds_d_max_code (set_prev s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_prev : forall s v, ds_bl_max_code (set_prev s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_prev : forall s v, ds_bl_count (set_prev s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_prev : forall s v, ds_heap (set_prev s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_prev : forall s v, ds_heap_len (set_prev s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_prev : forall s v, ds_heap_max (set_prev s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_prev : forall s v, ds_depth (set_prev s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_prev : forall s v, ds_lit_bufsize (set_prev s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_prev : forall s v, ds_sym_next (set_prev s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_prev : forall s v, ds_sym_end (set_prev s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_prev : forall s v, ds_opt_len (set_prev s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_prev : forall s v, ds_static_len (set_prev s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_prev : forall s v, ds_matches (set_prev s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_prev : forall s v, ds_insert (set_prev s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_prev : forall s v, ds_bi_buf (set_prev s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_prev : forall s v, ds_bi_valid (set_prev s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_prev : forall s v, ds_high_water (set_prev s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_prev : forall s v, ds_self_blk (set_prev s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_prev : forall s v, ds_window_blk (set_prev s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_prev : forall s v, ds_prev_blk (set_prev s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_prev : forall s v, ds_head_blk (set_prev s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_prev : forall s v, ds_pending_buf_blk (set_prev s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_prev : forall s v, ds_strm (set_prev s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_prev pending_buf_set_prev pending_buf_size_set_prev pending_out_set_prev pending_set_prev wrap_set_prev gzhead_set_prev gzindex_set_prev method_set_prev last_flush_set_prev w_size_set_prev w_bits_set_prev w_mask_set_prev window_set_prev window_size_set_prev prev_set_prev head_set_prev ins_h_set_prev hash_size_set_prev hash_bits_set_prev hash_mask_set_prev hash_shift_set_prev block_start_set_prev match_length_set_prev prev_match_set_prev match_available_set_prev strstart_set_prev match_start_set_prev lookahead_set_prev prev_length_set_prev max_chain_length_set_prev max_lazy_match_set_prev level_set_prev strategy_set_prev good_match_set_prev nice_match_set_prev dyn_ltree_fc_set_prev dyn_ltree_dl_set_prev dyn_dtree_fc_set_prev dyn_dtree_dl_set_prev bl_tree_fc_set_prev bl_tree_dl_set_prev l_max_code_set_prev d_max_code_set_prev bl_max_code_set_prev bl_count_set_prev heap_set_prev heap_len_set_prev heap_max_set_prev depth_set_prev lit_bufsize_set_prev sym_next_set_prev sym_end_set_prev opt_len_set_prev static_len_set_prev matches_set_prev insert_set_prev bi_buf_set_prev bi_valid_set_prev high_water_set_prev self_blk_set_prev window_blk_set_prev prev_blk_set_prev head_blk_set_prev pending_buf_blk_set_prev strm_set_prev : dsf.
Lemma status_set_head : forall s v, ds_status (set_head s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_head : forall s v, ds_pending_buf (set_head s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_head : forall s v, ds_pending_buf_size (set_head s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_head : forall s v, ds_pending_out (set_head s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_head : forall s v, ds_pending (set_head s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_head : forall s v, ds_wrap (set_head s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_head : forall s v, ds_gzhead (set_head s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_head : forall s v, ds_gzindex (set_head s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_head : forall s v, ds_method (set_head s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_head : forall s v, ds_last_flush (set_head s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_head : forall s v, ds_w_size (set_head s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_head : forall s v, ds_w_bits (set_head s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_head : forall s v, ds_w_mask (set_head s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_head : forall s v, ds_window (set_head s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_head : forall s v, ds_window_size (set_head s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_head : forall s v, ds_prev (set_head s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_head : forall s v, ds_head (set_head s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_head : forall s v, ds_ins_h (set_head s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_head : forall s v, ds_hash_size (set_head s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_head : forall s v, ds_hash_bits (set_head s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_head : forall s v, ds_hash_mask (set_head s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_head : forall s v, ds_hash_shift (set_head s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_head : forall s v, ds_block_start (set_head s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_head : forall s v, ds_match_length (set_head s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_head : forall s v, ds_prev_match (set_head s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_head : forall s v, ds_match_available (set_head s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_head : forall s v, ds_strstart (set_head s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_head : forall s v, ds_match_start (set_head s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_head : forall s v, ds_lookahead (set_head s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_head : forall s v, ds_prev_length (set_head s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_head : forall s v, ds_max_chain_length (set_head s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_head : forall s v, ds_max_lazy_match (set_head s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_head : forall s v, ds_level (set_head s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_head : forall s v, ds_strategy (set_head s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_head : forall s v, ds_good_match (set_head s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_head : forall s v, ds_nice_match (set_head s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_head : forall s v, ds_dyn_ltree_fc (set_head s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_head : forall s v, ds_dyn_ltree_dl (set_head s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_head : forall s v, ds_dyn_dtree_fc (set_head s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_head : forall s v, ds_dyn_dtree_dl (set_head s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_head : forall s v, ds_bl_tree_fc (set_head s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_head : forall s v, ds_bl_tree_dl (set_head s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_head : forall s v, ds_l_max_code (set_head s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_head : forall s v, ds_d_max_code (set_head s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_head : forall s v, ds_bl_max_code (set_head s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_head : forall s v, ds_bl_count (set_head s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_head : forall s v, ds_heap (set_head s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_head : forall s v, ds_heap_len (set_head s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_head : forall s v, ds_heap_max (set_head s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_head : forall s v, ds_depth (set_head s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_head : forall s v, ds_lit_bufsize (set_head s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_head : forall s v, ds_sym_next (set_head s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_head : forall s v, ds_sym_end (set_head s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_head : forall s v, ds_opt_len (set_head s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_head : forall s v, ds_static_len (set_head s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_head : forall s v, ds_matches (set_head s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_head : forall s v, ds_insert (set_head s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_head : forall s v, ds_bi_buf (set_head s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_head : forall s v, ds_bi_valid (set_head s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_head : forall s v, ds_high_water (set_head s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_head : forall s v, ds_self_blk (set_head s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_head : forall s v, ds_window_blk (set_head s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_head : forall s v, ds_prev_blk (set_head s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_head : forall s v, ds_head_blk (set_head s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_head : forall s v, ds_pending_buf_blk (set_head s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_head : forall s v, ds_strm (set_head s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_head pending_buf_set_head pending_buf_size_set_head pending_out_set_head pending_set_head wrap_set_head gzhead_set_head gzindex_set_head method_set_head last_flush_set_head w_size_set_head w_bits_set_head w_mask_set_head window_set_head window_size_set_head prev_set_head head_set_head ins_h_set_head hash_size_set_head hash_bits_set_head hash_mask_set_head hash_shift_set_head block_start_set_head match_length_set_head prev_match_set_head match_available_set_head strstart_set_head match_start_set_head lookahead_set_head prev_length_set_head max_chain_length_set_head max_lazy_match_set_head level_set_head strategy_set_head good_match_set_head nice_match_set_head dyn_ltree_fc_set_head dyn_ltree_dl_set_head dyn_dtree_fc_set_head dyn_dtree_dl_set_head bl_tree_fc_set_head bl_tree_dl_set_head l_max_code_set_head d_max_code_set_head bl_max_code_set_head bl_count_set_head heap_set_head heap_len_set_head heap_max_set_head depth_set_head lit_bufsize_set_head sym_next_set_head sym_end_set_head opt_len_set_head static_len_set_head matches_set_head insert_set_head bi_buf_set_head bi_valid_set_head high_water_set_head self_blk_set_head window_blk_set_head prev_blk_set_head head_blk_set_head pending_buf_blk_set_head strm_set_head : dsf.
Lemma status_set_ins_h : forall s v, ds_status (set_ins_h s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_ins_h : forall s v, ds_pending_buf (set_ins_h s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_ins_h : forall s v, ds_pending_buf_size (set_ins_h s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_ins_h : forall s v, ds_pending_out (set_ins_h s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_ins_h : forall s v, ds_pending (set_ins_h s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_ins_h : forall s v, ds_wrap (set_ins_h s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_ins_h : forall s v, ds_gzhead (set_ins_h s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_ins_h : forall s v, ds_gzindex (set_ins_h s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_ins_h : forall s v, ds_method (set_ins_h s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_ins_h : forall s v, ds_last_flush (set_ins_h s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_ins_h : forall s v, ds_w_size (set_ins_h s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_ins_h : forall s v, ds_w_bits (set_ins_h s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_ins_h : forall s v, ds_w_mask (set_ins_h s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_ins_h : forall s v, ds_window (set_ins_h s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_ins_h : forall s v, ds_window_size (set_ins_h s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_ins_h : forall s v, ds_prev (set_ins_h s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_ins_h : forall s v, ds_head (set_ins_h s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_ins_h : forall s v, ds_ins_h (set_ins_h s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_ins_h : forall s v, ds_hash_size (set_ins_h s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_ins_h : forall s v, ds_hash_bits (set_ins_h s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_ins_h : forall s v, ds_hash_mask (set_ins_h s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_ins_h : forall s v, ds_hash_shift (set_ins_h s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_ins_h : forall s v, ds_block_start (set_ins_h s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_ins_h : forall s v, ds_match_length (set_ins_h s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_ins_h : forall s v, ds_prev_match (set_ins_h s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_ins_h : forall s v, ds_match_available (set_ins_h s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_ins_h : forall s v, ds_strstart (set_ins_h s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_ins_h : forall s v, ds_match_start (set_ins_h s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_ins_h : forall s v, ds_lookahead (set_ins_h s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_ins_h : forall s v, ds_prev_length (set_ins_h s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_ins_h : forall s v, ds_max_chain_length (set_ins_h s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_ins_h : forall s v, ds_max_lazy_match (set_ins_h s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_ins_h : forall s v, ds_level (set_ins_h s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_ins_h : forall s v, ds_strategy (set_ins_h s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_ins_h : forall s v, ds_good_match (set_ins_h s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_ins_h : forall s v, ds_nice_match (set_ins_h s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_ins_h : forall s v, ds_dyn_ltree_fc (set_ins_h s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_ins_h : forall s v, ds_dyn_ltree_dl (set_ins_h s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_ins_h : forall s v, ds_dyn_dtree_fc (set_ins_h s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_ins_h : forall s v, ds_dyn_dtree_dl (set_ins_h s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_ins_h : forall s v, ds_bl_tree_fc (set_ins_h s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_ins_h : forall s v, ds_bl_tree_dl (set_ins_h s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_ins_h : forall s v, ds_l_max_code (set_ins_h s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_ins_h : forall s v, ds_d_max_code (set_ins_h s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_ins_h : forall s v, ds_bl_max_code (set_ins_h s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_ins_h : forall s v, ds_bl_count (set_ins_h s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_ins_h : forall s v, ds_heap (set_ins_h s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_ins_h : forall s v, ds_heap_len (set_ins_h s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_ins_h : forall s v, ds_heap_max (set_ins_h s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_ins_h : forall s v, ds_depth (set_ins_h s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_ins_h : forall s v, ds_lit_bufsize (set_ins_h s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_ins_h : forall s v, ds_sym_next (set_ins_h s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_ins_h : forall s v, ds_sym_end (set_ins_h s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_ins_h : forall s v, ds_opt_len (set_ins_h s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_ins_h : forall s v, ds_static_len (set_ins_h s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_ins_h : forall s v, ds_matches (set_ins_h s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_ins_h : forall s v, ds_insert (set_ins_h s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_ins_h : forall s v, ds_bi_buf (set_ins_h s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_ins_h : forall s v, ds_bi_valid (set_ins_h s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_ins_h : forall s v, ds_high_water (set_ins_h s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_ins_h : forall s v, ds_self_blk (set_ins_h s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_ins_h : forall s v, ds_window_blk (set_ins_h s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_ins_h : forall s v, ds_prev_blk (set_ins_h s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_ins_h : forall s v, ds_head_blk (set_ins_h s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_ins_h : forall s v, ds_pending_buf_blk (set_ins_h s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_ins_h : forall s v, ds_strm (set_ins_h s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_ins_h pending_buf_set_ins_h pending_buf_size_set_ins_h pending_out_set_ins_h pending_set_ins_h wrap_set_ins_h gzhead_set_ins_h gzindex_set_ins_h method_set_ins_h last_flush_set_ins_h w_size_set_ins_h w_bits_set_ins_h w_mask_set_ins_h window_set_ins_h window_size_set_ins_h prev_set_ins_h head_set_ins_h ins_h_set_ins_h hash_size_set_ins_h hash_bits_set_ins_h hash_mask_set_ins_h hash_shift_set_ins_h block_start_set_ins_h match_length_set_ins_h prev_match_set_ins_h match_available_set_ins_h strstart_set_ins_h match_start_set_ins_h lookahead_set_ins_h prev_length_set_ins_h max_chain_length_set_ins_h max_lazy_match_set_ins_h level_set_ins_h strategy_set_ins_h good_match_set_ins_h nice_match_set_ins_h dyn_ltree_fc_set_ins_h dyn_ltree_dl_set_ins_h dyn_dtree_fc_set_ins_h dyn_dtree_dl_set_ins_h bl_tree_fc_set_ins_h bl_tree_dl_set_ins_h l_max_code_set_ins_h d_max_code_set_ins_h bl_max_code_set_ins_h bl_count_set_ins_h heap_set_ins_h heap_len_set_ins_h heap_max_set_ins_h depth_set_ins_h lit_bufsize_set_ins_h sym_next_set_ins_h sym_end_set_ins_h opt_len_set_ins_h static_len_set_ins_h matches_set_ins_h insert_set_ins_h bi_buf_set_ins_h bi_valid_set_ins_h high_water_set_ins_h self_blk_set_ins_h window_blk_set_ins_h prev_blk_set_ins_h head_blk_set_ins_h pending_buf_blk_set_ins_h strm_set_ins_h : dsf.
Lemma status_set_strstart : forall s v, ds_status (set_strstart s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_strstart : forall s v, ds_pending_buf (set_strstart s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_strstart : forall s v, ds_pending_buf_size (set_strstart s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_strstart : forall s v, ds_pending_out (set_strstart s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_strstart : forall s v, ds_pending (set_strstart s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_strstart : forall s v, ds_wrap (set_strstart s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_strstart : forall s v, ds_gzhead (set_strstart s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_strstart : forall s v, ds_gzindex (set_strstart s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_strstart : forall s v, ds_method (set_strstart s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_strstart : forall s v, ds_last_flush (set_strstart s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_strstart : forall s v, ds_w_size (set_strstart s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_strstart : forall s v, ds_w_bits (set_strstart s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_strstart : forall s v, ds_w_mask (set_strstart s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_strstart : forall s v, ds_window (set_strstart s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_strstart : forall s v, ds_window_size (set_strstart s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_strstart : forall s v, ds_prev (set_strstart s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_strstart : forall s v, ds_head (set_strstart s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_strstart : forall s v, ds_ins_h (set_strstart s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_strstart : forall s v, ds_hash_size (set_strstart s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_strstart : forall s v, ds_hash_bits (set_strstart s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_strstart : forall s v, ds_hash_mask (set_strstart s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_strstart : forall s v, ds_hash_shift (set_strstart s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_strstart : forall s v, ds_block_start (set_strstart s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_strstart : forall s v, ds_match_length (set_strstart s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_strstart : forall s v, ds_prev_match (set_strstart s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_strstart : forall s v, ds_match_available (set_strstart s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_strstart : forall s v, ds_strstart (set_strstart s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_strstart : forall s v, ds_match_start (set_strstart s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_strstart : forall s v, ds_lookahead (set_strstart s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_strstart : forall s v, ds_prev_length (set_strstart s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_strstart : forall s v, ds_max_chain_length (set_strstart s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_strstart : forall s v, ds_max_lazy_match (set_strstart s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_strstart : forall s v, ds_level (set_strstart s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_strstart : forall s v, ds_strategy (set_strstart s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_strstart : forall s v, ds_good_match (set_strstart s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_strstart : forall s v, ds_nice_match (set_strstart s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_strstart : forall s v, ds_dyn_ltree_fc (set_strstart s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_strstart : forall s v, ds_dyn_ltree_dl (set_strstart s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_strstart : forall s v, ds_dyn_dtree_fc (set_strstart s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_strstart : forall s v, ds_dyn_dtree_dl (set_strstart s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_strstart : forall s v, ds_bl_tree_fc (set_strstart s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_strstart : forall s v, ds_bl_tree_dl (set_strstart s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_strstart : forall s v, ds_l_max_code (set_strstart s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_strstart : forall s v, ds_d_max_code (set_strstart s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_strstart : forall s v, ds_bl_max_code (set_strstart s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_strstart : forall s v, ds_bl_count (set_strstart s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_strstart : forall s v, ds_heap (set_strstart s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_strstart : forall s v, ds_heap_len (set_strstart s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_strstart : forall s v, ds_heap_max (set_strstart s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_strstart : forall s v, ds_depth (set_strstart s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_strstart : forall s v, ds_lit_bufsize (set_strstart s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_strstart : forall s v, ds_sym_next (set_strstart s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_strstart : forall s v, ds_sym_end (set_strstart s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_strstart : forall s v, ds_opt_len (set_strstart s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_strstart : forall s v, ds_static_len (set_strstart s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_strstart : forall s v, ds_matches (set_strstart s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_strstart : forall s v, ds_insert (set_strstart s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_strstart : forall s v, ds_bi_buf (set_strstart s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_strstart : forall s v, ds_bi_valid (set_strstart s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_strstart : forall s v, ds_high_water (set_strstart s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_strstart : forall s v, ds_self_blk (set_strstart s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_strstart : forall s v, ds_window_blk (set_strstart s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_strstart : forall s v, ds_prev_blk (set_strstart s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_strstart : forall s v, ds_head_blk (set_strstart s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_strstart : forall s v, ds_pending_buf_blk (set_strstart s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_strstart : forall s v, ds_strm (set_strstart s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_strstart pending_buf_set_strstart pending_buf_size_set_strstart pending_out_set_strstart pending_set_strstart wrap_set_strstart gzhead_set_strstart gzindex_set_strstart method_set_strstart last_flush_set_strstart w_size_set_strstart w_bits_set_strstart w_mask_set_strstart window_set_strstart window_size_set_strstart prev_set_strstart head_set_strstart ins_h_set_strstart hash_size_set_strstart hash_bits_set_strstart hash_mask_set_strstart hash_shift_set_strstart block_start_set_strstart match_length_set_strstart prev_match_set_strstart match_available_set_strstart strstart_set_strstart match_start_set_strstart lookahead_set_strstart prev_length_set_strstart max_chain_length_set_strstart max_lazy_match_set_strstart level_set_strstart strategy_set_strstart good_match_set_strstart nice_match_set_strstart dyn_ltree_fc_set_strstart dyn_ltree_dl_set_strstart dyn_dtree_fc_set_strstart dyn_dtree_dl_set_strstart bl_tree_fc_set_strstart bl_tree_dl_set_strstart l_max_code_set_strstart d_max_code_set_strstart bl_max_code_set_strstart bl_count_set_strstart heap_set_strstart heap_len_set_strstart heap_max_set_strstart depth_set_strstart lit_bufsize_set_strstart sym_next_set_strstart sym_end_set_strstart opt_len_set_strstart static_len_set_strstart matches_set_strstart insert_set_strstart bi_buf_set_strstart bi_valid_set_strstart high_water_set_strstart self_blk_set_strstart window_blk_set_strstart prev_blk_set_strstart head_blk_set_strstart pending_buf_blk_set_strstart strm_set_strstart : dsf.
Lemma status_set_lookahead : forall s v, ds_status (set_lookahead s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_lookahead : forall s v, ds_pending_buf (set_lookahead s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_lookahead : forall s v, ds_pending_buf_size (set_lookahead s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_lookahead : forall s v, ds_pending_out (set_lookahead s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_lookahead : forall s v, ds_pending (set_lookahead s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_lookahead : forall s v, ds_wrap (set_lookahead s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_lookahead : forall s v, ds_gzhead (set_lookahead s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_lookahead : forall s v, ds_gzindex (set_lookahead s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_lookahead : forall s v, ds_method (set_lookahead s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_lookahead : forall s v, ds_last_flush (set_lookahead s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_lookahead : forall s v, ds_w_size (set_lookahead s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_lookahead : forall s v, ds_w_bits (set_lookahead s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_lookahead : forall s v, ds_w_mask (set_lookahead s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_lookahead : forall s v, ds_window (set_lookahead s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_lookahead : forall s v, ds_window_size (set_lookahead s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_lookahead : forall s v, ds_prev (set_lookahead s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_lookahead : forall s v, ds_head (set_lookahead s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_lookahead : forall s v, ds_ins_h (set_lookahead s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_lookahead : forall s v, ds_hash_size (set_lookahead s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_lookahead : forall s v, ds_hash_bits (set_lookahead s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_lookahead : forall s v, ds_hash_mask (set_lookahead s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_lookahead : forall s v, ds_hash_shift (set_lookahead s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_lookahead : forall s v, ds_block_start (set_lookahead s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_lookahead : forall s v, ds_match_length (set_lookahead s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_lookahead : forall s v, ds_prev_match (set_lookahead s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_lookahead : forall s v, ds_match_available (set_lookahead s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_lookahead : forall s v, ds_strstart (set_lookahead s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_lookahead : forall s v, ds_match_start (set_lookahead s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_lookahead : forall s v, ds_lookahead (set_lookahead s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_lookahead : forall s v, ds_prev_length (set_lookahead s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_lookahead : forall s v, ds_max_chain_length (set_lookahead s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_lookahead : forall s v, ds_max_lazy_match (set_lookahead s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_lookahead : forall s v, ds_level (set_lookahead s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_lookahead : forall s v, ds_strategy (set_lookahead s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_lookahead : forall s v, ds_good_match (set_lookahead s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_lookahead : forall s v, ds_nice_match (set_lookahead s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_lookahead : forall s v, ds_dyn_ltree_fc (set_lookahead s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_lookahead : forall s v, ds_dyn_ltree_dl (set_lookahead s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_lookahead : forall s v, ds_dyn_dtree_fc (set_lookahead s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_lookahead : forall s v, ds_dyn_dtree_dl (set_lookahead s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_lookahead : forall s v, ds_bl_tree_fc (set_lookahead s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_lookahead : forall s v, ds_bl_tree_dl (set_lookahead s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_lookahead : forall s v, ds_l_max_code (set_lookahead s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_lookahead : forall s v, ds_d_max_code (set_lookahead s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_lookahead : forall s v, ds_bl_max_code (set_lookahead s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_lookahead : forall s v, ds_bl_count (set_lookahead s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_lookahead : forall s v, ds_heap (set_lookahead s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_lookahead : forall s v, ds_heap_len (set_lookahead s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_lookahead : forall s v, ds_heap_max (set_lookahead s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_lookahead : forall s v, ds_depth (set_lookahead s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_lookahead : forall s v, ds_lit_bufsize (set_lookahead s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_lookahead : forall s v, ds_sym_next (set_lookahead s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_lookahead : forall s v, ds_sym_end (set_lookahead s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_lookahead : forall s v, ds_opt_len (set_lookahead s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_lookahead : forall s v, ds_static_len (set_lookahead s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_lookahead : forall s v, ds_matches (set_lookahead s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_lookahead : forall s v, ds_insert (set_lookahead s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_lookahead : forall s v, ds_bi_buf (set_lookahead s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_lookahead : forall s v, ds_bi_valid (set_lookahead s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_lookahead : forall s v, ds_high_water (set_lookahead s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_lookahead : forall s v, ds_self_blk (set_lookahead s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_lookahead : forall s v, ds_window_blk (set_lookahead s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_lookahead : forall s v, ds_prev_blk (set_lookahead s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_lookahead : forall s v, ds_head_blk (set_lookahead s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_lookahead : forall s v, ds_pending_buf_blk (set_lookahead s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_lookahead : forall s v, ds_strm (set_lookahead s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_lookahead pending_buf_set_lookahead pending_buf_size_set_lookahead pending_out_set_lookahead pending_set_lookahead wrap_set_lookahead gzhead_set_lookahead gzindex_set_lookahead method_set_lookahead last_flush_set_lookahead w_size_set_lookahead w_bits_set_lookahead w_mask_set_lookahead window_set_lookahead window_size_set_lookahead prev_set_lookahead head_set_lookahead ins_h_set_lookahead hash_size_set_lookahead hash_bits_set_lookahead hash_mask_set_lookahead hash_shift_set_lookahead block_start_set_lookahead match_length_set_lookahead prev_match_set_lookahead match_available_set_lookahead strstart_set_lookahead match_start_set_lookahead lookahead_set_lookahead prev_length_set_lookahead max_chain_length_set_lookahead max_lazy_match_set_lookahead level_set_lookahead strategy_set_lookahead good_match_set_lookahead nice_match_set_lookahead dyn_ltree_fc_set_lookahead dyn_ltree_dl_set_lookahead dyn_dtree_fc_set_lookahead dyn_dtree_dl_set_lookahead bl_tree_fc_set_lookahead bl_tree_dl_set_lookahead l_max_code_set_lookahead d_max_code_set_lookahead bl_max_code_set_lookahead bl_count_set_lookahead heap_set_lookahead heap_len_set_lookahead heap_max_set_lookahead depth_set_lookahead lit_bufsize_set_lookahead sym_next_set_lookahead sym_end_set_lookahead opt_len_set_lookahead static_len_set_lookahead matches_set_lookahead insert_set_lookahead bi_buf_set_lookahead bi_valid_set_lookahead high_water_set_lookahead self_blk_set_lookahead window_blk_set_lookahead prev_blk_set_lookahead head_blk_set_lookahead pending_buf_blk_set_lookahead strm_set_lookahead : dsf.
Lemma status_set_block_start : forall s v, ds_status (set_block_start s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_block_start : forall s v, ds_pending_buf (set_block_start s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_block_start : forall s v, ds_pending_buf_size (set_block_start s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_block_start : forall s v, ds_pending_out (set_block_start s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_block_start : forall s v, ds_pending (set_block_start s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_block_start : forall s v, ds_wrap (set_block_start s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_block_start : forall s v, ds_gzhead (set_block_start s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_block_start : forall s v, ds_gzindex (set_block_start s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_block_start : forall s v, ds_method (set_block_start s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_block_start : forall s v, ds_last_flush (set_block_start s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_block_start : forall s v, ds_w_size (set_block_start s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_block_start : forall s v, ds_w_bits (set_block_start s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_block_start : forall s v, ds_w_mask (set_block_start s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_block_start : forall s v, ds_window (set_block_start s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_block_start : forall s v, ds_window_size (set_block_start s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_block_start : forall s v, ds_prev (set_block_start s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_block_start : forall s v, ds_head (set_block_start s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_block_start : forall s v, ds_ins_h (set_block_start s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_block_start : forall s v, ds_hash_size (set_block_start s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_block_start : forall s v, ds_hash_bits (set_block_start s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_block_start : forall s v, ds_hash_mask (set_block_start s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_block_start : forall s v, ds_hash_shift (set_block_start s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_block_start : forall s v, ds_block_start (set_block_start s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_block_start : forall s v, ds_match_length (set_block_start s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_block_start : forall s v, ds_prev_match (set_block_start s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_block_start : forall s v, ds_match_available (set_block_start s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_block_start : forall s v, ds_strstart (set_block_start s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_block_start : forall s v, ds_match_start (set_block_start s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_block_start : forall s v, ds_lookahead (set_block_start s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_block_start : forall s v, ds_prev_length (set_block_start s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_block_start : forall s v, ds_max_chain_length (set_block_start s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_block_start : forall s v, ds_max_lazy_match (set_block_start s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_block_start : forall s v, ds_level (set_block_start s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_block_start : forall s v, ds_strategy (set_block_start s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_block_start : forall s v, ds_good_match (set_block_start s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_block_start : forall s v, ds_nice_match (set_block_start s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_block_start : forall s v, ds_dyn_ltree_fc (set_block_start s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_block_start : forall s v, ds_dyn_ltree_dl (set_block_start s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_block_start : forall s v, ds_dyn_dtree_fc (set_block_start s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_block_start : forall s v, ds_dyn_dtree_dl (set_block_start s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_block_start : forall s v, ds_bl_tree_fc (set_block_start s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_block_start : forall s v, ds_bl_tree_dl (set_block_start s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_block_start : forall s v, ds_l_max_code (set_block_start s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_block_start : forall s v, ds_d_max_code (set_block_start s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_block_start : forall s v, ds_bl_max_code (set_block_start s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_block_start : forall s v, ds_bl_count (set_block_start s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_block_start : forall s v, ds_heap (set_block_start s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_block_start : forall s v, ds_heap_len (set_block_start s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_block_start : forall s v, ds_heap_max (set_block_start s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_block_start : forall s v, ds_depth (set_block_start s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_block_start : forall s v, ds_lit_bufsize (set_block_start s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_block_start : forall s v, ds_sym_next (set_block_start s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_block_start : forall s v, ds_sym_end (set_block_start s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_block_start : forall s v, ds_opt_len (set_block_start s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_block_start : forall s v, ds_static_len (set_block_start s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_block_start : forall s v, ds_matches (set_block_start s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_block_start : forall s v, ds_insert (set_block_start s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_block_start : forall s v, ds_bi_buf (set_block_start s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_block_start : forall s v, ds_bi_valid (set_block_start s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_block_start : forall s v, ds_high_water (set_block_start s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_block_start : forall s v, ds_self_blk (set_block_start s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_block_start : forall s v, ds_window_blk (set_block_start s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_block_start : forall s v, ds_prev_blk (set_block_start s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_block_start : forall s v, ds_head_blk (set_block_start s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_block_start : forall s v, ds_pending_buf_blk (set_block_start s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_block_start : forall s v, ds_strm (set_block_start s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_block_start pending_buf_set_block_start pending_buf_size_set_block_start pending_out_set_block_start pending_set_block_start wrap_set_block_start gzhead_set_block_start gzindex_set_block_start method_set_block_start last_flush_set_block_start w_size_set_block_start w_bits_set_block_start w_mask_set_block_start window_set_block_start window_size_set_block_start prev_set_block_start head_set_block_start ins_h_set_block_start hash_size_set_block_start hash_bits_set_block_start hash_mask_set_block_start hash_shift_set_block_start block_start_set_block_start match_length_set_block_start prev_match_set_block_start match_available_set_block_start strstart_set_block_start match_start_set_block_start lookahead_set_block_start prev_length_set_block_start max_chain_length_set_block_start max_lazy_match_set_block_start level_set_block_start strategy_set_block_start good_match_set_block_start nice_match_set_block_start dyn_ltree_fc_set_block_start dyn_ltree_dl_set_block_start dyn_dtree_fc_set_block_start dyn_dtree_dl_set_block_start bl_tree_fc_set_block_start bl_tree_dl_set_block_start l_max_code_set_block_start d_max_code_set_block_start bl_max_code_set_block_start bl_count_set_block_start heap_set_block_start heap_len_set_block_start heap_max_set_block_start depth_set_block_start lit_bufsize_set_block_start sym_next_set_block_start sym_end_set_block_start opt_len_set_block_start static_len_set_block_start matches_set_block_start insert_set_block_start bi_buf_set_block_start bi_valid_set_block_start high_water_set_block_start self_blk_set_block_start window_blk_set_block_start prev_blk_set_block_start head_blk_set_block_start pending_buf_blk_set_block_start strm_set_block_start : dsf.
Lemma status_set_insert : forall s v, ds_status (set_insert s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_insert : forall s v, ds_pending_buf (set_insert s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_insert : forall s v, ds_pending_buf_size (set_insert s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_insert : forall s v, ds_pending_out (set_insert s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_insert : forall s v, ds_pending (set_insert s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_insert : forall s v, ds_wrap (set_insert s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_insert : forall s v, ds_gzhead (set_insert s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_insert : forall s v, ds_gzindex (set_insert s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_insert : forall s v, ds_method (set_insert s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_insert : forall s v, ds_last_flush (set_insert s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_insert : forall s v, ds_w_size (set_insert s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_insert : forall s v, ds_w_bits (set_insert s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_insert : forall s v, ds_w_mask (set_insert s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_insert : forall s v, ds_window (set_insert s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_insert : forall s v, ds_window_size (set_insert s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_insert : forall s v, ds_prev (set_insert s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_insert : forall s v, ds_head (set_insert s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_insert : forall s v, ds_ins_h (set_insert s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_insert : forall s v, ds_hash_size (set_insert s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_insert : forall s v, ds_hash_bits (set_insert s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_insert : forall s v, ds_hash_mask (set_insert s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_insert : forall s v, ds_hash_shift (set_insert s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_insert : forall s v, ds_block_start (set_insert s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_insert : forall s v, ds_match_length (set_insert s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_insert : forall s v, ds_prev_match (set_insert s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_insert : forall s v, ds_match_available (set_insert s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_insert : forall s v, ds_strstart (set_insert s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_insert : forall s v, ds_match_start (set_insert s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_insert : forall s v, ds_lookahead (set_insert s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_insert : forall s v, ds_prev_length (set_insert s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_insert : forall s v, ds_max_chain_length (set_insert s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_insert : forall s v, ds_max_lazy_match (set_insert s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_insert : forall s v, ds_level (set_insert s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_insert : forall s v, ds_strategy (set_insert s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_insert : forall s v, ds_good_match (set_insert s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_insert : forall s v, ds_nice_match (set_insert s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_insert : forall s v, ds_dyn_ltree_fc (set_insert s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_insert : forall s v, ds_dyn_ltree_dl (set_insert s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_insert : forall s v, ds_dyn_dtree_fc (set_insert s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_insert : forall s v, ds_dyn_dtree_dl (set_insert s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_insert : forall s v, ds_bl_tree_fc (set_insert s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_insert : forall s v, ds_bl_tree_dl (set_insert s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_insert : forall s v, ds_l_max_code (set_insert s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_insert : forall s v, ds_d_max_code (set_insert s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_insert : forall s v, ds_bl_max_code (set_insert s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_insert : forall s v, ds_bl_count (set_insert s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_insert : forall s v, ds_heap (set_insert s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_insert : forall s v, ds_heap_len (set_insert s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_insert : forall s v, ds_heap_max (set_insert s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_insert : forall s v, ds_depth (set_insert s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_insert : forall s v, ds_lit_bufsize (set_insert s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_insert : forall s v, ds_sym_next (set_insert s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_insert : forall s v, ds_sym_end (set_insert s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_insert : forall s v, ds_opt_len (set_insert s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_insert : forall s v, ds_static_len (set_insert s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_insert : forall s v, ds_matches (set_insert s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_insert : forall s v, ds_insert (set_insert s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_insert : forall s v, ds_bi_buf (set_insert s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_insert : forall s v, ds_bi_valid (set_insert s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_insert : forall s v, ds_high_water (set_insert s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_insert : forall s v, ds_self_blk (set_insert s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_insert : forall s v, ds_window_blk (set_insert s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_insert : forall s v, ds_prev_blk (set_insert s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_insert : forall s v, ds_head_blk (set_insert s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_insert : forall s v, ds_pending_buf_blk (set_insert s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_insert : forall s v, ds_strm (set_insert s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_insert pending_buf_set_insert pending_buf_size_set_insert pending_out_set_insert pending_set_insert wrap_set_insert gzhead_set_insert gzindex_set_insert method_set_insert last_flush_set_insert w_size_set_insert w_bits_set_insert w_mask_set_insert window_set_insert window_size_set_insert prev_set_insert head_set_insert ins_h_set_insert hash_size_set_insert hash_bits_set_insert hash_mask_set_insert hash_shift_set_insert block_start_set_insert match_length_set_insert prev_match_set_insert match_available_set_insert strstart_set_insert match_start_set_insert lookahead_set_insert prev_length_set_insert max_chain_length_set_insert max_lazy_match_set_insert level_set_insert strategy_set_insert good_match_set_insert nice_match_set_insert dyn_ltree_fc_set_insert dyn_ltree_dl_set_insert dyn_dtree_fc_set_insert dyn_dtree_dl_set_insert bl_tree_fc_set_insert bl_tree_dl_set_insert l_max_code_set_insert d_max_code_set_insert bl_max_code_set_insert bl_count_set_insert heap_set_insert heap_len_set_insert heap_max_set_insert depth_set_insert lit_bufsize_set_insert sym_next_set_insert sym_end_set_insert opt_len_set_insert static_len_set_insert matches_set_insert insert_set_insert bi_buf_set_insert bi_valid_set_insert high_water_set_insert self_blk_set_insert window_blk_set_insert prev_blk_set_insert head_blk_set_insert pending_buf_blk_set_insert strm_set_insert : dsf.
Lemma status_set_match_length : forall s v, ds_status (set_match_length s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_match_length : forall s v, ds_pending_buf (set_match_length s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_match_length : forall s v, ds_pending_buf_size (set_match_length s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_match_length : forall s v, ds_pending_out (set_match_length s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_match_length : forall s v, ds_pending (set_match_length s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_match_length : forall s v, ds_wrap (set_match_length s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_match_length : forall s v, ds_gzhead (set_match_length s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_match_length : forall s v, ds_gzindex (set_match_length s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_match_length : forall s v, ds_method (set_match_length s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_match_length : forall s v, ds_last_flush (set_match_length s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_match_length : forall s v, ds_w_size (set_match_length s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_match_length : forall s v, ds_w_bits (set_match_length s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_match_length : forall s v, ds_w_mask (set_match_length s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_match_length : forall s v, ds_window (set_match_length s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_match_length : forall s v, ds_window_size (set_match_length s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_match_length : forall s v, ds_prev (set_match_length s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_match_length : forall s v, ds_head (set_match_length s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_match_length : forall s v, ds_ins_h (set_match_length s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_match_length : forall s v, ds_hash_size (set_match_length s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_match_length : forall s v, ds_hash_bits (set_match_length s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_match_length : forall s v, ds_hash_mask (set_match_length s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_match_length : forall s v, ds_hash_shift (set_match_length s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_match_length : forall s v, ds_block_start (set_match_length s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_match_length : forall s v, ds_match_length (set_match_length s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_match_length : forall s v, ds_prev_match (set_match_length s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_match_length : forall s v, ds_match_available (set_match_length s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_match_length : forall s v, ds_strstart (set_match_length s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_match_length : forall s v, ds_match_start (set_match_length s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_match_length : forall s v, ds_lookahead (set_match_length s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_match_length : forall s v, ds_prev_length (set_match_length s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_match_length : forall s v, ds_max_chain_length (set_match_length s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_match_length : forall s v, ds_max_lazy_match (set_match_length s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_match_length : forall s v, ds_level (set_match_length s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_match_length : forall s v, ds_strategy (set_match_length s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_match_length : forall s v, ds_good_match (set_match_length s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_match_length : forall s v, ds_nice_match (set_match_length s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_match_length : forall s v, ds_dyn_ltree_fc (set_match_length s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_match_length : forall s v, ds_dyn_ltree_dl (set_match_length s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_match_length : forall s v, ds_dyn_dtree_fc (set_match_length s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_match_length : forall s v, ds_dyn_dtree_dl (set_match_length s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_match_length : forall s v, ds_bl_tree_fc (set_match_length s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_match_length : forall s v, ds_bl_tree_dl (set_match_length s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_match_length : forall s v, ds_l_max_code (set_match_length s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_match_length : forall s v, ds_d_max_code (set_match_length s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_match_length : forall s v, ds_bl_max_code (set_match_length s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_match_length : forall s v, ds_bl_count (set_match_length s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_match_length : forall s v, ds_heap (set_match_length s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_match_length : forall s v, ds_heap_len (set_match_length s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_match_length : forall s v, ds_heap_max (set_match_length s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_match_length : forall s v, ds_depth (set_match_length s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_match_length : forall s v, ds_lit_bufsize (set_match_length s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_match_length : forall s v, ds_sym_next (set_match_length s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_match_length : forall s v, ds_sym_end (set_match_length s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_match_length : forall s v, ds_opt_len (set_match_length s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_match_length : forall s v, ds_static_len (set_match_length s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_match_length : forall s v, ds_matches (set_match_length s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_match_length : forall s v, ds_insert (set_match_length s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_match_length : forall s v, ds_bi_buf (set_match_length s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_match_length : forall s v, ds_bi_valid (set_match_length s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_match_length : forall s v, ds_high_water (set_match_length s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_match_length : forall s v, ds_self_blk (set_match_length s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_match_length : forall s v, ds_window_blk (set_match_length s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_match_length : forall s v, ds_prev_blk (set_match_length s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_match_length : forall s v, ds_head_blk (set_match_length s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_match_length : forall s v, ds_pending_buf_blk (set_match_length s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_match_length : forall s v, ds_strm (set_match_length s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_match_length pending_buf_set_match_length pending_buf_size_set_match_length pending_out_set_match_length pending_set_match_length wrap_set_match_length gzhead_set_match_length gzindex_set_match_length method_set_match_length last_flush_set_match_length w_size_set_match_length w_bits_set_match_length w_mask_set_match_length window_set_match_length window_size_set_match_length prev_set_match_length head_set_match_length ins_h_set_match_length hash_size_set_match_length hash_bits_set_match_length hash_mask_set_match_length hash_shift_set_match_length block_start_set_match_length match_length_set_match_length prev_match_set_match_length match_available_set_match_length strstart_set_match_length match_start_set_match_length lookahead_set_match_length prev_length_set_match_length max_chain_length_set_match_length max_lazy_match_set_match_length level_set_match_length strategy_set_match_length good_match_set_match_length nice_match_set_match_length dyn_ltree_fc_set_match_length dyn_ltree_dl_set_match_length dyn_dtree_fc_set_match_length dyn_dtree_dl_set_match_length bl_tree_fc_set_match_length bl_tree_dl_set_match_length l_max_code_set_match_length d_max_code_set_match_length bl_max_code_set_match_length bl_count_set_match_length heap_set_match_length heap_len_set_match_length heap_max_set_match_length depth_set_match_length lit_bufsize_set_match_length sym_next_set_match_length sym_end_set_match_length opt_len_set_match_length static_len_set_match_length matches_set_match_length insert_set_match_length bi_buf_set_match_length bi_valid_set_match_length high_water_set_match_length self_blk_set_match_length window_blk_set_match_length prev_blk_set_match_length head_blk_set_match_length pending_buf_blk_set_match_length strm_set_match_length : dsf.
Lemma status_set_match_start : forall s v, ds_status (set_match_start s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_match_start : forall s v, ds_pending_buf (set_match_start s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_match_start : forall s v, ds_pending_buf_size (set_match_start s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_match_start : forall s v, ds_pending_out (set_match_start s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_match_start : forall s v, ds_pending (set_match_start s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_match_start : forall s v, ds_wrap (set_match_start s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_match_start : forall s v, ds_gzhead (set_match_start s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_match_start : forall s v, ds_gzindex (set_match_start s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_match_start : forall s v, ds_method (set_match_start s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_match_start : forall s v, ds_last_flush (set_match_start s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_match_start : forall s v, ds_w_size (set_match_start s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_match_start : forall s v, ds_w_bits (set_match_start s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_match_start : forall s v, ds_w_mask (set_match_start s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_match_start : forall s v, ds_window (set_match_start s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_match_start : forall s v, ds_window_size (set_match_start s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_match_start : forall s v, ds_prev (set_match_start s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_match_start : forall s v, ds_head (set_match_start s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_match_start : forall s v, ds_ins_h (set_match_start s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_match_start : forall s v, ds_hash_size (set_match_start s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_match_start : forall s v, ds_hash_bits (set_match_start s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_match_start : forall s v, ds_hash_mask (set_match_start s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_match_start : forall s v, ds_hash_shift (set_match_start s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_match_start : forall s v, ds_block_start (set_match_start s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_match_start : forall s v, ds_match_length (set_match_start s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_match_start : forall s v, ds_prev_match (set_match_start s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_match_start : forall s v, ds_match_available (set_match_start s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_match_start : forall s v, ds_strstart (set_match_start s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_match_start : forall s v, ds_match_start (set_match_start s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_match_start : forall s v, ds_lookahead (set_match_start s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_match_start : forall s v, ds_prev_length (set_match_start s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_match_start : forall s v, ds_max_chain_length (set_match_start s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_match_start : forall s v, ds_max_lazy_match (set_match_start s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_match_start : forall s v, ds_level (set_match_start s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_match_start : forall s v, ds_strategy (set_match_start s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_match_start : forall s v, ds_good_match (set_match_start s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_match_start : forall s v, ds_nice_match (set_match_start s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_match_start : forall s v, ds_dyn_ltree_fc (set_match_start s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_match_start : forall s v, ds_dyn_ltree_dl (set_match_start s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_match_start : forall s v, ds_dyn_dtree_fc (set_match_start s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_match_start : forall s v, ds_dyn_dtree_dl (set_match_start s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_match_start : forall s v, ds_bl_tree_fc (set_match_start s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_match_start : forall s v, ds_bl_tree_dl (set_match_start s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_match_start : forall s v, ds_l_max_code (set_match_start s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_match_start : forall s v, ds_d_max_code (set_match_start s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_match_start : forall s v, ds_bl_max_code (set_match_start s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_match_start : forall s v, ds_bl_count (set_match_start s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_match_start : forall s v, ds_heap (set_match_start s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_match_start : forall s v, ds_heap_len (set_match_start s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_match_start : forall s v, ds_heap_max (set_match_start s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_match_start : forall s v, ds_depth (set_match_start s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_match_start : forall s v, ds_lit_bufsize (set_match_start s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_match_start : forall s v, ds_sym_next (set_match_start s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_match_start : forall s v, ds_sym_end (set_match_start s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_match_start : forall s v, ds_opt_len (set_match_start s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_match_start : forall s v, ds_static_len (set_match_start s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_match_start : forall s v, ds_matches (set_match_start s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_match_start : forall s v, ds_insert (set_match_start s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_match_start : forall s v, ds_bi_buf (set_match_start s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_match_start : forall s v, ds_bi_valid (set_match_start s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_match_start : forall s v, ds_high_water (set_match_start s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_match_start : forall s v, ds_self_blk (set_match_start s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_match_start : forall s v, ds_window_blk (set_match_start s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_match_start : forall s v, ds_prev_blk (set_match_start s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_match_start : forall s v, ds_head_blk (set_match_start s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_match_start : forall s v, ds_pending_buf_blk (set_match_start s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_match_start : forall s v, ds_strm (set_match_start s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_match_start pending_buf_set_match_start pending_buf_size_set_match_start pending_out_set_match_start pending_set_match_start wrap_set_match_start gzhead_set_match_start gzindex_set_match_start method_set_match_start last_flush_set_match_start w_size_set_match_start w_bits_set_match_start w_mask_set_match_start window_set_match_start window_size_set_match_start prev_set_match_start head_set_match_start ins_h_set_match_start hash_size_set_match_start hash_bits_set_match_start hash_mask_set_match_start hash_shift_set_match_start block_start_set_match_start match_length_set_match_start prev_match_set_match_start match_available_set_match_start strstart_set_match_start match_start_set_match_start lookahead_set_match_start prev_length_set_match_start max_chain_length_set_match_start max_lazy_match_set_match_start level_set_match_start strategy_set_match_start good_match_set_match_start nice_match_set_match_start dyn_ltree_fc_set_match_start dyn_ltree_dl_set_match_start dyn_dtree_fc_set_match_start dyn_dtree_dl_set_match_start bl_tree_fc_set_match_start bl_tree_dl_set_match_start l_max_code_set_match_start d_max_code_set_match_start bl_max_code_set_match_start bl_count_set_match_start heap_set_match_start heap_len_set_match_start heap_max_set_match_start depth_set_match_start lit_bufsize_set_match_start sym_next_set_match_start sym_end_set_match_start opt_len_set_match_start static_len_set_match_start matches_set_match_start insert_set_match_start bi_buf_set_match_start bi_valid_set_match_start high_water_set_match_start self_blk_set_match_start window_blk_set_match_start prev_blk_set_match_start head_blk_set_match_start pending_buf_blk_set_match_start strm_set_match_start : dsf.
Lemma status_set_prev_length : forall s v, ds_status (set_prev_length s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_prev_length : forall s v, ds_pending_buf (set_prev_length s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_prev_length : forall s v, ds_pending_buf_size (set_prev_length s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_prev_length : forall s v, ds_pending_out (set_prev_length s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_prev_length : forall s v, ds_pending (set_prev_length s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_prev_length : forall s v, ds_wrap (set_prev_length s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_prev_length : forall s v, ds_gzhead (set_prev_length s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_prev_length : forall s v, ds_gzindex (set_prev_length s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_prev_length : forall s v, ds_method (set_prev_length s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_prev_length : forall s v, ds_last_flush (set_prev_length s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_prev_length : forall s v, ds_w_size (set_prev_length s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_prev_length : forall s v, ds_w_bits (set_prev_length s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_prev_length : forall s v, ds_w_mask (set_prev_length s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_prev_length : forall s v, ds_window (set_prev_length s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_prev_length : forall s v, ds_window_size (set_prev_length s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_prev_length : forall s v, ds_prev (set_prev_length s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_prev_length : forall s v, ds_head (set_prev_length s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_prev_length : forall s v, ds_ins_h (set_prev_length s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_prev_length : forall s v, ds_hash_size (set_prev_length s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_prev_length : forall s v, ds_hash_bits (set_prev_length s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_prev_length : forall s v, ds_hash_mask (set_prev_length s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_prev_length : forall s v, ds_hash_shift (set_prev_length s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_prev_length : forall s v, ds_block_start (set_prev_length s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_prev_length : forall s v, ds_match_length (set_prev_length s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_prev_length : forall s v, ds_prev_match (set_prev_length s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_prev_length : forall s v, ds_match_available (set_prev_length s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_prev_length : forall s v, ds_strstart (set_prev_length s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_prev_length : forall s v, ds_match_start (set_prev_length s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_prev_length : forall s v, ds_lookahead (set_prev_length s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_prev_length : forall s v, ds_prev_length (set_prev_length s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_prev_length : forall s v, ds_max_chain_length (set_prev_length s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_prev_length : forall s v, ds_max_lazy_match (set_prev_length s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_prev_length : forall s v, ds_level (set_prev_length s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_prev_length : forall s v, ds_strategy (set_prev_length s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_prev_length : forall s v, ds_good_match (set_prev_length s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_prev_length : forall s v, ds_nice_match (set_prev_length s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_prev_length : forall s v, ds_dyn_ltree_fc (set_prev_length s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_prev_length : forall s v, ds_dyn_ltree_dl (set_prev_length s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_prev_length : forall s v, ds_dyn_dtree_fc (set_prev_length s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_prev_length : forall s v, ds_dyn_dtree_dl (set_prev_length s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_prev_length : forall s v, ds_bl_tree_fc (set_prev_length s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_prev_length : forall s v, ds_bl_tree_dl (set_prev_length s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_prev_length : forall s v, ds_l_max_code (set_prev_length s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_prev_length : forall s v, ds_d_max_code (set_prev_length s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_prev_length : forall s v, ds_bl_max_code (set_prev_length s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_prev_length : forall s v, ds_bl_count (set_prev_length s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_prev_length : forall s v, ds_heap (set_prev_length s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_prev_length : forall s v, ds_heap_len (set_prev_length s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_prev_length : forall s v, ds_heap_max (set_prev_length s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_prev_length : forall s v, ds_depth (set_prev_length s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_prev_length : forall s v, ds_lit_bufsize (set_prev_length s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_prev_length : forall s v, ds_sym_next (set_prev_length s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_prev_length : forall s v, ds_sym_end (set_prev_length s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_prev_length : forall s v, ds_opt_len (set_prev_length s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_prev_length : forall s v, ds_static_len (set_prev_length s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_prev_length : forall s v, ds_matches (set_prev_length s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_prev_length : forall s v, ds_insert (set_prev_length s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_prev_length : forall s v, ds_bi_buf (set_prev_length s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_prev_length : forall s v, ds_bi_valid (set_prev_length s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_prev_length : forall s v, ds_high_water (set_prev_length s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_prev_length : forall s v, ds_self_blk (set_prev_length s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_prev_length : forall s v, ds_window_blk (set_prev_length s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_prev_length : forall s v, ds_prev_blk (set_prev_length s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_prev_length : forall s v, ds_head_blk (set_prev_length s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_prev_length : forall s v, ds_pending_buf_blk (set_prev_length s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_prev_length : forall s v, ds_strm (set_prev_length s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_prev_length pending_buf_set_prev_length pending_buf_size_set_prev_length pending_out_set_prev_length pending_set_prev_length wrap_set_prev_length gzhead_set_prev_length gzindex_set_prev_length method_set_prev_length last_flush_set_prev_length w_size_set_prev_length w_bits_set_prev_length w_mask_set_prev_length window_set_prev_length window_size_set_prev_length prev_set_prev_length head_set_prev_length ins_h_set_prev_length hash_size_set_prev_length hash_bits_set_prev_length hash_mask_set_prev_length hash_shift_set_prev_length block_start_set_prev_length match_length_set_prev_length prev_match_set_prev_length match_available_set_prev_length strstart_set_prev_length match_start_set_prev_length lookahead_set_prev_length prev_length_set_prev_length max_chain_length_set_prev_length max_lazy_match_set_prev_length level_set_prev_length strategy_set_prev_length good_match_set_prev_length nice_match_set_prev_length dyn_ltree_fc_set_prev_length dyn_ltree_dl_set_prev_length dyn_dtree_fc_set_prev_length dyn_dtree_dl_set_prev_length bl_tree_fc_set_prev_length bl_tree_dl_set_prev_length l_max_code_set_prev_length d_max_code_set_prev_length bl_max_code_set_prev_length bl_count_set_prev_length heap_set_prev_length heap_len_set_prev_length heap_max_set_prev_length depth_set_prev_length lit_bufsize_set_prev_length sym_next_set_prev_length sym_end_set_prev_length opt_len_set_prev_length static_len_set_prev_length matches_set_prev_length insert_set_prev_length bi_buf_set_prev_length bi_valid_set_prev_length high_water_set_prev_length self_blk_set_prev_length window_blk_set_prev_length prev_blk_set_prev_length head_blk_set_prev_length pending_buf_blk_set_prev_length strm_set_prev_length : dsf.
Lemma status_set_prev_match : forall s v, ds_status (set_prev_match s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_prev_match : forall s v, ds_pending_buf (set_prev_match s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_prev_match : forall s v, ds_pending_buf_size (set_prev_match s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_prev_match : forall s v, ds_pending_out (set_prev_match s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_prev_match : forall s v, ds_pending (set_prev_match s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_prev_match : forall s v, ds_wrap (set_prev_match s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_prev_match : forall s v, ds_gzhead (set_prev_match s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_prev_match : forall s v, ds_gzindex (set_prev_match s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_prev_match : forall s v, ds_method (set_prev_match s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_prev_match : forall s v, ds_last_flush (set_prev_match s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_prev_match : forall s v, ds_w_size (set_prev_match s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_prev_match : forall s v, ds_w_bits (set_prev_match s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_prev_match : forall s v, ds_w_mask (set_prev_match s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_prev_match : forall s v, ds_window (set_prev_match s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_prev_match : forall s v, ds_window_size (set_prev_match s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_prev_match : forall s v, ds_prev (set_prev_match s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_prev_match : forall s v, ds_head (set_prev_match s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_prev_match : forall s v, ds_ins_h (set_prev_match s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_prev_match : forall s v, ds_hash_size (set_prev_match s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_prev_match : forall s v, ds_hash_bits (set_prev_match s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_prev_match : forall s v, ds_hash_mask (set_prev_match s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_prev_match : forall s v, ds_hash_shift (set_prev_match s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_prev_match : forall s v, ds_block_start (set_prev_match s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_prev_match : forall s v, ds_match_length (set_prev_match s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_prev_match : forall s v, ds_prev_match (set_prev_match s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_prev_match : forall s v, ds_match_available (set_prev_match s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_prev_match : forall s v, ds_strstart (set_prev_match s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_prev_match : forall s v, ds_match_start (set_prev_match s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_prev_match : forall s v, ds_lookahead (set_prev_match s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_prev_match : forall s v, ds_prev_length (set_prev_match s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_prev_match : forall s v, ds_max_chain_length (set_prev_match s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_prev_match : forall s v, ds_max_lazy_match (set_prev_match s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_prev_match : forall s v, ds_level (set_prev_match s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_prev_match : forall s v, ds_strategy (set_prev_match s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_prev_match : forall s v, ds_good_match (set_prev_match s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_prev_match : forall s v, ds_nice_match (set_prev_match s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_prev_match : forall s v, ds_dyn_ltree_fc (set_prev_match s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_prev_match : forall s v, ds_dyn_ltree_dl (set_prev_match s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_prev_match : forall s v, ds_dyn_dtree_fc (set_prev_match s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_prev_match : forall s v, ds_dyn_dtree_dl (set_prev_match s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_prev_match : forall s v, ds_bl_tree_fc (set_prev_match s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_prev_match : forall s v, ds_bl_tree_dl (set_prev_match s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_prev_match : forall s v, ds_l_max_code (set_prev_match s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_prev_match : forall s v, ds_d_max_code (set_prev_match s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_prev_match : forall s v, ds_bl_max_code (set_prev_match s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_prev_match : forall s v, ds_bl_count (set_prev_match s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_prev_match : forall s v, ds_heap (set_prev_match s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_prev_match : forall s v, ds_heap_len (set_prev_match s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_prev_match : forall s v, ds_heap_max (set_prev_match s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_prev_match : forall s v, ds_depth (set_prev_match s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_prev_match : forall s v, ds_lit_bufsize (set_prev_match s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_prev_match : forall s v, ds_sym_next (set_prev_match s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_prev_match : forall s v, ds_sym_end (set_prev_match s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_prev_match : forall s v, ds_opt_len (set_prev_match s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_prev_match : forall s v, ds_static_len (set_prev_match s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_prev_match : forall s v, ds_matches (set_prev_match s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_prev_match : forall s v, ds_insert (set_prev_match s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_prev_match : forall s v, ds_bi_buf (set_prev_match s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_prev_match : forall s v, ds_bi_valid (set_prev_match s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_prev_match : forall s v, ds_high_water (set_prev_match s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_prev_match : forall s v, ds_self_blk (set_prev_match s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_prev_match : forall s v, ds_window_blk (set_prev_match s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_prev_match : forall s v, ds_prev_blk (set_prev_match s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_prev_match : forall s v, ds_head_blk (set_prev_match s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_prev_match : forall s v, ds_pending_buf_blk (set_prev_match s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_prev_match : forall s v, ds_strm (set_prev_match s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_prev_match pending_buf_set_prev_match pending_buf_size_set_prev_match pending_out_set_prev_match pending_set_prev_match wrap_set_prev_match gzhead_set_prev_match gzindex_set_prev_match method_set_prev_match last_flush_set_prev_match w_size_set_prev_match w_bits_set_prev_match w_mask_set_prev_match window_set_prev_match window_size_set_prev_match prev_set_prev_match head_set_prev_match ins_h_set_prev_match hash_size_set_prev_match hash_bits_set_prev_match hash_mask_set_prev_match hash_shift_set_prev_match block_start_set_prev_match match_length_set_prev_match prev_match_set_prev_match match_available_set_prev_match strstart_set_prev_match match_start_set_prev_match lookahead_set_prev_match prev_length_set_prev_match max_chain_length_set_prev_match max_lazy_match_set_prev_match level_set_prev_match strategy_set_prev_match good_match_set_prev_match nice_match_set_prev_match dyn_ltree_fc_set_prev_match dyn_ltree_dl_set_prev_match dyn_dtree_fc_set_prev_match dyn_dtree_dl_set_prev_match bl_tree_fc_set_prev_match bl_tree_dl_set_prev_match l_max_code_set_prev_match d_max_code_set_prev_match bl_max_code_set_prev_match bl_count_set_prev_match heap_set_prev_match heap_len_set_prev_match heap_max_set_prev_match depth_set_prev_match lit_bufsize_set_prev_match sym_next_set_prev_match sym_end_set_prev_match opt_len_set_prev_match static_len_set_prev_match matches_set_prev_match insert_set_prev_match bi_buf_set_prev_match bi_valid_set_prev_match high_water_set_prev_match self_blk_set_prev_match window_blk_set_prev_match prev_blk_set_prev_match head_blk_set_prev_match pending_buf_blk_set_prev_match strm_set_prev_match : dsf.
Lemma status_set_match_available : forall s v, ds_status (set_match_available s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_match_available : forall s v, ds_pending_buf (set_match_available s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_match_available : forall s v, ds_pending_buf_size (set_match_available s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_match_available : forall s v, ds_pending_out (set_match_available s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_match_available : forall s v, ds_pending (set_match_available s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_match_available : forall s v, ds_wrap (set_match_available s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_match_available : forall s v, ds_gzhead (set_match_available s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_match_available : forall s v, ds_gzindex (set_match_available s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_match_available : forall s v, ds_method (set_match_available s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_match_available : forall s v, ds_last_flush (set_match_available s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_match_available : forall s v, ds_w_size (set_match_available s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_match_available : forall s v, ds_w_bits (set_match_available s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_match_available : forall s v, ds_w_mask (set_match_available s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_match_available : forall s v, ds_window (set_match_available s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_match_available : forall s v, ds_window_size (set_match_available s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_match_available : forall s v, ds_prev (set_match_available s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_match_available : forall s v, ds_head (set_match_available s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_match_available : forall s v, ds_ins_h (set_match_available s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_match_available : forall s v, ds_hash_size (set_match_available s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_match_available : forall s v, ds_hash_bits (set_match_available s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_match_available : forall s v, ds_hash_mask (set_match_available s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_match_available : forall s v, ds_hash_shift (set_match_available s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_match_available : forall s v, ds_block_start (set_match_available s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_match_available : forall s v, ds_match_length (set_match_available s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_match_available : forall s v, ds_prev_match (set_match_available s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_match_available : forall s v, ds_match_available (set_match_available s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_match_available : forall s v, ds_strstart (set_match_available s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_match_available : forall s v, ds_match_start (set_match_available s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_match_available : forall s v, ds_lookahead (set_match_available s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_match_available : forall s v, ds_prev_length (set_match_available s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_match_available : forall s v, ds_max_chain_length (set_match_available s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_match_available : forall s v, ds_max_lazy_match (set_match_available s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_match_available : forall s v, ds_level (set_match_available s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_match_available : forall s v, ds_strategy (set_match_available s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_match_available : forall s v, ds_good_match (set_match_available s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_match_available : forall s v, ds_nice_match (set_match_available s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_match_available : forall s v, ds_dyn_ltree_fc (set_match_available s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_match_available : forall s v, ds_dyn_ltree_dl (set_match_available s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_match_available : forall s v, ds_dyn_dtree_fc (set_match_available s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_match_available : forall s v, ds_dyn_dtree_dl (set_match_available s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_match_available : forall s v, ds_bl_tree_fc (set_match_available s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_match_available : forall s v, ds_bl_tree_dl (set_match_available s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_match_available : forall s v, ds_l_max_code (set_match_available s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_match_available : forall s v, ds_d_max_code (set_match_available s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_match_available : forall s v, ds_bl_max_code (set_match_available s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_match_available : forall s v, ds_bl_count (set_match_available s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_match_available : forall s v, ds_heap (set_match_available s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_match_available : forall s v, ds_heap_len (set_match_available s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_match_available : forall s v, ds_heap_max (set_match_available s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_match_available : forall s v, ds_depth (set_match_available s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_match_available : forall s v, ds_lit_bufsize (set_match_available s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_match_available : forall s v, ds_sym_next (set_match_available s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_match_available : forall s v, ds_sym_end (set_match_available s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_match_available : forall s v, ds_opt_len (set_match_available s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_match_available : forall s v, ds_static_len (set_match_available s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_match_available : forall s v, ds_matches (set_match_available s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_match_available : forall s v, ds_insert (set_match_available s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_match_available : forall s v, ds_bi_buf (set_match_available s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_match_available : forall s v, ds_bi_valid (set_match_available s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_match_available : forall s v, ds_high_water (set_match_available s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_match_available : forall s v, ds_self_blk (set_match_available s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_match_available : forall s v, ds_window_blk (set_match_available s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_match_available : forall s v, ds_prev_blk (set_match_available s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_match_available : forall s v, ds_head_blk (set_match_available s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_match_available : forall s v, ds_pending_buf_blk (set_match_available s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_match_available : forall s v, ds_strm (set_match_available s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_match_available pending_buf_set_match_available pending_buf_size_set_match_available pending_out_set_match_available pending_set_match_available wrap_set_match_available gzhead_set_match_available gzindex_set_match_available method_set_match_available last_flush_set_match_available w_size_set_match_available w_bits_set_match_available w_mask_set_match_available window_set_match_available window_size_set_match_available prev_set_match_available head_set_match_available ins_h_set_match_available hash_size_set_match_available hash_bits_set_match_available hash_mask_set_match_available hash_shift_set_match_available block_start_set_match_available match_length_set_match_available prev_match_set_match_available match_available_set_match_available strstart_set_match_available match_start_set_match_available lookahead_set_match_available prev_length_set_match_available max_chain_length_set_match_available max_lazy_match_set_match_available level_set_match_available strategy_set_match_available good_match_set_match_available nice_match_set_match_available dyn_ltree_fc_set_match_available dyn_ltree_dl_set_match_available dyn_dtree_fc_set_match_available dyn_dtree_dl_set_match_available bl_tree_fc_set_match_available bl_tree_dl_set_match_available l_max_code_set_match_available d_max_code_set_match_available bl_max_code_set_match_available bl_count_set_match_available heap_set_match_available heap_len_set_match_available heap_max_set_match_available depth_set_match_available lit_bufsize_set_match_available sym_next_set_match_available sym_end_set_match_available opt_len_set_match_available static_len_set_match_available matches_set_match_available insert_set_match_available bi_buf_set_match_available bi_valid_set_match_available high_water_set_match_available self_blk_set_match_available window_blk_set_match_available prev_blk_set_match_available head_blk_set_match_available pending_buf_blk_set_match_available strm_set_match_available : dsf.
Lemma status_set_high_water : forall s v, ds_status (set_high_water s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_high_water : forall s v, ds_pending_buf (set_high_water s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_high_water : forall s v, ds_pending_buf_size (set_high_water s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_high_water : forall s v, ds_pending_out (set_high_water s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_high_water : forall s v, ds_pending (set_high_water s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_high_water : forall s v, ds_wrap (set_high_water s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_high_water : forall s v, ds_gzhead (set_high_water s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_high_water : forall s v, ds_gzindex (set_high_water s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_high_water : forall s v, ds_method (set_high_water s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_high_water : forall s v, ds_last_flush (set_high_water s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_high_water : forall s v, ds_w_size (set_high_water s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_high_water : forall s v, ds_w_bits (set_high_water s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_high_water : forall s v, ds_w_mask (set_high_water s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_high_water : forall s v, ds_window (set_high_water s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_high_water : forall s v, ds_window_size (set_high_water s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_high_water : forall s v, ds_prev (set_high_water s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_high_water : forall s v, ds_head (set_high_water s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_high_water : forall s v, ds_ins_h (set_high_water s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_high_water : forall s v, ds_hash_size (set_high_water s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_high_water : forall s v, ds_hash_bits (set_high_water s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_high_water : forall s v, ds_hash_mask (set_high_water s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_high_water : forall s v, ds_hash_shift (set_high_water s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_high_water : forall s v, ds_block_start (set_high_water s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_high_water : forall s v, ds_match_length (set_high_water s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_high_water : forall s v, ds_prev_match (set_high_water s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_high_water : forall s v, ds_match_available (set_high_water s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_high_water : forall s v, ds_strstart (set_high_water s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_high_water : forall s v, ds_match_start (set_high_water s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_high_water : forall s v, ds_lookahead (set_high_water s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_high_water : forall s v, ds_prev_length (set_high_water s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_high_water : forall s v, ds_max_chain_length (set_high_water s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_high_water : forall s v, ds_max_lazy_match (set_high_water s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_high_water : forall s v, ds_level (set_high_water s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_high_water : forall s v, ds_strategy (set_high_water s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_high_water : forall s v, ds_good_match (set_high_water s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_high_water : forall s v, ds_nice_match (set_high_water s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_high_water : forall s v, ds_dyn_ltree_fc (set_high_water s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_high_water : forall s v, ds_dyn_ltree_dl (set_high_water s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_high_water : forall s v, ds_dyn_dtree_fc (set_high_water s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_high_water : forall s v, ds_dyn_dtree_dl (set_high_water s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_high_water : forall s v, ds_bl_tree_fc (set_high_water s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_high_water : forall s v, ds_bl_tree_dl (set_high_water s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_high_water : forall s v, ds_l_max_code (set_high_water s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_high_water : forall s v, ds_d_max_code (set_high_water s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_high_water : forall s v, ds_bl_max_code (set_high_water s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_high_water : forall s v, ds_bl_count (set_high_water s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_high_water : forall s v, ds_heap (set_high_water s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_high_water : forall s v, ds_heap_len (set_high_water s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_high_water : forall s v, ds_heap_max (set_high_water s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_high_water : forall s v, ds_depth (set_high_water s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_high_water : forall s v, ds_lit_bufsize (set_high_water s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_high_water : forall s v, ds_sym_next (set_high_water s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_high_water : forall s v, ds_sym_end (set_high_water s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_high_water : forall s v, ds_opt_len (set_high_water s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_high_water : forall s v, ds_static_len (set_high_water s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_high_water : forall s v, ds_matches (set_high_water s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_high_water : forall s v, ds_insert (set_high_water s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_high_water : forall s v, ds_bi_buf (set_high_water s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_high_water : forall s v, ds_bi_valid (set_high_water s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_high_water : forall s v, ds_high_water (set_high_water s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_high_water : forall s v, ds_self_blk (set_high_water s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_high_water : forall s v, ds_window_blk (set_high_water s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_high_water : forall s v, ds_prev_blk (set_high_water s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_high_water : forall s v, ds_head_blk (set_high_water s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_high_water : forall s v, ds_pending_buf_blk (set_high_water s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_high_water : forall s v, ds_strm (set_high_water s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_high_water pending_buf_set_high_water pending_buf_size_set_high_water pending_out_set_high_water pending_set_high_water wrap_set_high_water gzhead_set_high_water gzindex_set_high_water method_set_high_water last_flush_set_high_water w_size_set_high_water w_bits_set_high_water w_mask_set_high_water window_set_high_water window_size_set_high_water prev_set_high_water head_set_high_water ins_h_set_high_water hash_size_set_high_water hash_bits_set_high_water hash_mask_set_high_water hash_shift_set_high_water block_start_set_high_water match_length_set_high_water prev_match_set_high_water match_available_set_high_water strstart_set_high_water match_start_set_high_water lookahead_set_high_water prev_length_set_high_water max_chain_length_set_high_water max_lazy_match_set_high_water level_set_high_water strategy_set_high_water good_match_set_high_water nice_match_set_high_water dyn_ltree_fc_set_high_water dyn_ltree_dl_set_high_water dyn_dtree_fc_set_high_water dyn_dtree_dl_set_high_water bl_tree_fc_set_high_water bl_tree_dl_set_high_water l_max_code_set_high_water d_max_code_set_high_water bl_max_code_set_high_water bl_count_set_high_water heap_set_high_water heap_len_set_high_water heap_max_set_high_water depth_set_high_water lit_bufsize_set_high_water sym_next_set_high_water sym_end_set_high_water opt_len_set_high_water static_len_set_high_water matches_set_high_water insert_set_high_water bi_buf_set_high_water bi_valid_set_high_water high_water_set_high_water self_blk_set_high_water window_blk_set_high_water prev_blk_set_high_water head_blk_set_high_water pending_buf_blk_set_high_water strm_set_high_water : dsf.
Lemma status_set_matches : forall s v, ds_status (set_matches s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_matches : forall s v, ds_pending_buf (set_matches s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_matches : forall s v, ds_pending_buf_size (set_matches s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_matches : forall s v, ds_pending_out (set_matches s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_matches : forall s v, ds_pending (set_matches s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_matches : forall s v, ds_wrap (set_matches s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_matches : forall s v, ds_gzhead (set_matches s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_matches : forall s v, ds_gzindex (set_matches s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_matches : forall s v, ds_method (set_matches s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_matches : forall s v, ds_last_flush (set_matches s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_matches : forall s v, ds_w_size (set_matches s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_matches : forall s v, ds_w_bits (set_matches s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_matches : forall s v, ds_w_mask (set_matches s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_matches : forall s v, ds_window (set_matches s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_matches : forall s v, ds_window_size (set_matches s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_matches : forall s v, ds_prev (set_matches s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_matches : forall s v, ds_head (set_matches s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_matches : forall s v, ds_ins_h (set_matches s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_matches : forall s v, ds_hash_size (set_matches s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_matches : forall s v, ds_hash_bits (set_matches s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_matches : forall s v, ds_hash_mask (set_matches s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_matches : forall s v, ds_hash_shift (set_matches s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_matches : forall s v, ds_block_start (set_matches s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_matches : forall s v, ds_match_length (set_matches s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_matches : forall s v, ds_prev_match (set_matches s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_matches : forall s v, ds_match_available (set_matches s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_matches : forall s v, ds_strstart (set_matches s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_matches : forall s v, ds_match_start (set_matches s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_matches : forall s v, ds_lookahead (set_matches s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_matches : forall s v, ds_prev_length (set_matches s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_matches : forall s v, ds_max_chain_length (set_matches s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_matches : forall s v, ds_max_lazy_match (set_matches s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_matches : forall s v, ds_level (set_matches s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_matches : forall s v, ds_strategy (set_matches s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_matches : forall s v, ds_good_match (set_matches s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_matches : forall s v, ds_nice_match (set_matches s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_matches : forall s v, ds_dyn_ltree_fc (set_matches s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_matches : forall s v, ds_dyn_ltree_dl (set_matches s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_matches : forall s v, ds_dyn_dtree_fc (set_matches s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_matches : forall s v, ds_dyn_dtree_dl (set_matches s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_matches : forall s v, ds_bl_tree_fc (set_matches s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_matches : forall s v, ds_bl_tree_dl (set_matches s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_matches : forall s v, ds_l_max_code (set_matches s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_matches : forall s v, ds_d_max_code (set_matches s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_matches : forall s v, ds_bl_max_code (set_matches s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_matches : forall s v, ds_bl_count (set_matches s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_matches : forall s v, ds_heap (set_matches s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_matches : forall s v, ds_heap_len (set_matches s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_matches : forall s v, ds_heap_max (set_matches s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_matches : forall s v, ds_depth (set_matches s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_matches : forall s v, ds_lit_bufsize (set_matches s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_matches : forall s v, ds_sym_next (set_matches s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_matches : forall s v, ds_sym_end (set_matches s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_matches : forall s v, ds_opt_len (set_matches s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_matches : forall s v, ds_static_len (set_matches s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_matches : forall s v, ds_matches (set_matches s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_matches : forall s v, ds_insert (set_matches s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_matches : forall s v, ds_bi_buf (set_matches s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_matches : forall s v, ds_bi_valid (set_matches s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_matches : forall s v, ds_high_water (set_matches s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_matches : forall s v, ds_self_blk (set_matches s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_matches : forall s v, ds_window_blk (set_matches s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_matches : forall s v, ds_prev_blk (set_matches s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_matches : forall s v, ds_head_blk (set_matches s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_matches : forall s v, ds_pending_buf_blk (set_matches s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_matches : forall s v, ds_strm (set_matches s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_matches pending_buf_set_matches pending_buf_size_set_matches pending_out_set_matches pending_set_matches wrap_set_matches gzhead_set_matches gzindex_set_matches method_set_matches last_flush_set_matches w_size_set_matches w_bits_set_matches w_mask_set_matches window_set_matches window_size_set_matches prev_set_matches head_set_matches ins_h_set_matches hash_size_set_matches hash_bits_set_matches hash_mask_set_matches hash_shift_set_matches block_start_set_matches match_length_set_matches prev_match_set_matches match_available_set_matches strstart_set_matches match_start_set_matches lookahead_set_matches prev_length_set_matches max_chain_length_set_matches max_lazy_match_set_matches level_set_matches strategy_set_matches good_match_set_matches nice_match_set_matches dyn_ltree_fc_set_matches dyn_ltree_dl_set_matches dyn_dtree_fc_set_matches dyn_dtree_dl_set_matches bl_tree_fc_set_matches bl_tree_dl_set_matches l_max_code_set_matches d_max_code_set_matches bl_max_code_set_matches bl_count_set_matches heap_set_matches heap_len_set_matches heap_max_set_matches depth_set_matches lit_bufsize_set_matches sym_next_set_matches sym_end_set_matches opt_len_set_matches static_len_set_matches matches_set_matches insert_set_matches bi_buf_set_matches bi_valid_set_matches high_water_set_matches self_blk_set_matches window_blk_set_matches prev_blk_set_matches head_blk_set_matches pending_buf_blk_set_matches strm_set_matches : dsf.
Lemma status_set_sym_next : forall s v, ds_status (set_sym_next s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_sym_next : forall s v, ds_pending_buf (set_sym_next s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_sym_next : forall s v, ds_pending_buf_size (set_sym_next s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_sym_next : forall s v, ds_pending_out (set_sym_next s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_sym_next : forall s v, ds_pending (set_sym_next s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_sym_next : forall s v, ds_wrap (set_sym_next s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_sym_next : forall s v, ds_gzhead (set_sym_next s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_sym_next : forall s v, ds_gzindex (set_sym_next s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_sym_next : forall s v, ds_method (set_sym_next s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_sym_next : forall s v, ds_last_flush (set_sym_next s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_sym_next : forall s v, ds_w_size (set_sym_next s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_sym_next : forall s v, ds_w_bits (set_sym_next s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_sym_next : forall s v, ds_w_mask (set_sym_next s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_sym_next : forall s v, ds_window (set_sym_next s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_sym_next : forall s v, ds_window_size (set_sym_next s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_sym_next : forall s v, ds_prev (set_sym_next s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_sym_next : forall s v, ds_head (set_sym_next s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_sym_next : forall s v, ds_ins_h (set_sym_next s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_sym_next : forall s v, ds_hash_size (set_sym_next s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_sym_next : forall s v, ds_hash_bits (set_sym_next s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_sym_next : forall s v, ds_hash_mask (set_sym_next s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_sym_next : forall s v, ds_hash_shift (set_sym_next s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_sym_next : forall s v, ds_block_start (set_sym_next s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_sym_next : forall s v, ds_match_length (set_sym_next s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_sym_next : forall s v, ds_prev_match (set_sym_next s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_sym_next : forall s v, ds_match_available (set_sym_next s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_sym_next : forall s v, ds_strstart (set_sym_next s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_sym_next : forall s v, ds_match_start (set_sym_next s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_sym_next : forall s v, ds_lookahead (set_sym_next s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_sym_next : forall s v, ds_prev_length (set_sym_next s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_sym_next : forall s v, ds_max_chain_length (set_sym_next s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_sym_next : forall s v, ds_max_lazy_match (set_sym_next s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_sym_next : forall s v, ds_level (set_sym_next s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_sym_next : forall s v, ds_strategy (set_sym_next s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_sym_next : forall s v, ds_good_match (set_sym_next s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_sym_next : forall s v, ds_nice_match (set_sym_next s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_sym_next : forall s v, ds_dyn_ltree_fc (set_sym_next s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_sym_next : forall s v, ds_dyn_ltree_dl (set_sym_next s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_sym_next : forall s v, ds_dyn_dtree_fc (set_sym_next s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_sym_next : forall s v, ds_dyn_dtree_dl (set_sym_next s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_sym_next : forall s v, ds_bl_tree_fc (set_sym_next s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_sym_next : forall s v, ds_bl_tree_dl (set_sym_next s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_sym_next : forall s v, ds_l_max_code (set_sym_next s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_sym_next : forall s v, ds_d_max_code (set_sym_next s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_sym_next : forall s v, ds_bl_max_code (set_sym_next s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_sym_next : forall s v, ds_bl_count (set_sym_next s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_sym_next : forall s v, ds_heap (set_sym_next s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_sym_next : forall s v, ds_heap_len (set_sym_next s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_sym_next : forall s v, ds_heap_max (set_sym_next s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_sym_next : forall s v, ds_depth (set_sym_next s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_sym_next : forall s v, ds_lit_bufsize (set_sym_next s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_sym_next : forall s v, ds_sym_next (set_sym_next s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_sym_next : forall s v, ds_sym_end (set_sym_next s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_sym_next : forall s v, ds_opt_len (set_sym_next s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_sym_next : forall s v, ds_static_len (set_sym_next s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_sym_next : forall s v, ds_matches (set_sym_next s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_sym_next : forall s v, ds_insert (set_sym_next s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_sym_next : forall s v, ds_bi_buf (set_sym_next s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_sym_next : forall s v, ds_bi_valid (set_sym_next s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_sym_next : forall s v, ds_high_water (set_sym_next s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_sym_next : forall s v, ds_self_blk (set_sym_next s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_sym_next : forall s v, ds_window_blk (set_sym_next s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_sym_next : forall s v, ds_prev_blk (set_sym_next s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_sym_next : forall s v, ds_head_blk (set_sym_next s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_sym_next : forall s v, ds_pending_buf_blk (set_sym_next s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_sym_next : forall s v, ds_strm (set_sym_next s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_sym_next pending_buf_set_sym_next pending_buf_size_set_sym_next pending_out_set_sym_next pending_set_sym_next wrap_set_sym_next gzhead_set_sym_next gzindex_set_sym_next method_set_sym_next last_flush_set_sym_next w_size_set_sym_next w_bits_set_sym_next w_mask_set_sym_next window_set_sym_next window_size_set_sym_next prev_set_sym_next head_set_sym_next ins_h_set_sym_next hash_size_set_sym_next hash_bits_set_sym_next hash_mask_set_sym_next hash_shift_set_sym_next block_start_set_sym_next match_length_set_sym_next prev_match_set_sym_next match_available_set_sym_next strstart_set_sym_next match_start_set_sym_next lookahead_set_sym_next prev_length_set_sym_next max_chain_length_set_sym_next max_lazy_match_set_sym_next level_set_sym_next strategy_set_sym_next good_match_set_sym_next nice_match_set_sym_next dyn_ltree_fc_set_sym_next dyn_ltree_dl_set_sym_next dyn_dtree_fc_set_sym_next dyn_dtree_dl_set_sym_next bl_tree_fc_set_sym_next bl_tree_dl_set_sym_next l_max_code_set_sym_next d_max_code_set_sym_next bl_max_code_set_sym_next bl_count_set_sym_next heap_set_sym_next heap_len_set_sym_next heap_max_set_sym_next depth_set_sym_next lit_bufsize_set_sym_next sym_next_set_sym_next sym_end_set_sym_next opt_len_set_sym_next static_len_set_sym_next matches_set_sym_next insert_set_sym_next bi_buf_set_sym_next bi_valid_set_sym_next high_water_set_sym_next self_blk_set_sym_next window_blk_set_sym_next prev_blk_set_sym_next head_blk_set_sym_next pending_buf_blk_set_sym_next strm_set_sym_next : dsf.
Lemma status_set_opt_len : forall s v, ds_status (set_opt_len s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_opt_len : forall s v, ds_pending_buf (set_opt_len s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_opt_len : forall s v, ds_pending_buf_size (set_opt_len s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_opt_len : forall s v, ds_pending_out (set_opt_len s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_opt_len : forall s v, ds_pending (set_opt_len s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_opt_len : forall s v, ds_wrap (set_opt_len s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_opt_len : forall s v, ds_gzhead (set_opt_len s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_opt_len : forall s v, ds_gzindex (set_opt_len s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_opt_len : forall s v, ds_method (set_opt_len s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_opt_len : forall s v, ds_last_flush (set_opt_len s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_opt_len : forall s v, ds_w_size (set_opt_len s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_opt_len : forall s v, ds_w_bits (set_opt_len s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_opt_len : forall s v, ds_w_mask (set_opt_len s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_opt_len : forall s v, ds_window (set_opt_len s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_opt_len : forall s v, ds_window_size (set_opt_len s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_opt_len : forall s v, ds_prev (set_opt_len s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_opt_len : forall s v, ds_head (set_opt_len s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_opt_len : forall s v, ds_ins_h (set_opt_len s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_opt_len : forall s v, ds_hash_size (set_opt_len s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_opt_len : forall s v, ds_hash_bits (set_opt_len s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_opt_len : forall s v, ds_hash_mask (set_opt_len s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_opt_len : forall s v, ds_hash_shift (set_opt_len s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_opt_len : forall s v, ds_block_start (set_opt_len s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_opt_len : forall s v, ds_match_length (set_opt_len s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_opt_len : forall s v, ds_prev_match (set_opt_len s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_opt_len : forall s v, ds_match_available (set_opt_len s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_opt_len : forall s v, ds_strstart (set_opt_len s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_opt_len : forall s v, ds_match_start (set_opt_len s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_opt_len : forall s v, ds_lookahead (set_opt_len s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_opt_len : forall s v, ds_prev_length (set_opt_len s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_opt_len : forall s v, ds_max_chain_length (set_opt_len s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_opt_len : forall s v, ds_max_lazy_match (set_opt_len s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_opt_len : forall s v, ds_level (set_opt_len s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_opt_len : forall s v, ds_strategy (set_opt_len s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_opt_len : forall s v, ds_good_match (set_opt_len s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_opt_len : forall s v, ds_nice_match (set_opt_len s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_opt_len : forall s v, ds_dyn_ltree_fc (set_opt_len s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_opt_len : forall s v, ds_dyn_ltree_dl (set_opt_len s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_opt_len : forall s v, ds_dyn_dtree_fc (set_opt_len s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_opt_len : forall s v, ds_dyn_dtree_dl (set_opt_len s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_opt_len : forall s v, ds_bl_tree_fc (set_opt_len s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_opt_len : forall s v, ds_bl_tree_dl (set_opt_len s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_opt_len : forall s v, ds_l_max_code (set_opt_len s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_opt_len : forall s v, ds_d_max_code (set_opt_len s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_opt_len : forall s v, ds_bl_max_code (set_opt_len s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_opt_len : forall s v, ds_bl_count (set_opt_len s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_opt_len : forall s v, ds_heap (set_opt_len s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_opt_len : forall s v, ds_heap_len (set_opt_len s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_opt_len : forall s v, ds_heap_max (set_opt_len s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_opt_len : forall s v, ds_depth (set_opt_len s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_opt_len : forall s v, ds_lit_bufsize (set_opt_len s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_opt_len : forall s v, ds_sym_next (set_opt_len s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_opt_len : forall s v, ds_sym_end (set_opt_len s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_opt_len : forall s v, ds_opt_len (set_opt_len s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_opt_len : forall s v, ds_static_len (set_opt_len s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_opt_len : forall s v, ds_matches (set_opt_len s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_opt_len : forall s v, ds_insert (set_opt_len s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_opt_len : forall s v, ds_bi_buf (set_opt_len s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_opt_len : forall s v, ds_bi_valid (set_opt_len s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_opt_len : forall s v, ds_high_water (set_opt_len s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_opt_len : forall s v, ds_self_blk (set_opt_len s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_opt_len : forall s v, ds_window_blk (set_opt_len s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_opt_len : forall s v, ds_prev_blk (set_opt_len s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_opt_len : forall s v, ds_head_blk (set_opt_len s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_opt_len : forall s v, ds_pending_buf_blk (set_opt_len s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_opt_len : forall s v, ds_strm (set_opt_len s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_opt_len pending_buf_set_opt_len pending_buf_size_set_opt_len pending_out_set_opt_len pending_set_opt_len wrap_set_opt_len gzhead_set_opt_len gzindex_set_opt_len method_set_opt_len last_flush_set_opt_len w_size_set_opt_len w_bits_set_opt_len w_mask_set_opt_len window_set_opt_len window_size_set_opt_len prev_set_opt_len head_set_opt_len ins_h_set_opt_len hash_size_set_opt_len hash_bits_set_opt_len hash_mask_set_opt_len hash_shift_set_opt_len block_start_set_opt_len match_length_set_opt_len prev_match_set_opt_len match_available_set_opt_len strstart_set_opt_len match_start_set_opt_len lookahead_set_opt_len prev_length_set_opt_len max_chain_length_set_opt_len max_lazy_match_set_opt_len level_set_opt_len strategy_set_opt_len good_match_set_opt_len nice_match_set_opt_len dyn_ltree_fc_set_opt_len dyn_ltree_dl_set_opt_len dyn_dtree_fc_set_opt_len dyn_dtree_dl_set_opt_len bl_tree_fc_set_opt_len bl_tree_dl_set_opt_len l_max_code_set_opt_len d_max_code_set_opt_len bl_max_code_set_opt_len bl_count_set_opt_len heap_set_opt_len heap_len_set_opt_len heap_max_set_opt_len depth_set_opt_len lit_bufsize_set_opt_len sym_next_set_opt_len sym_end_set_opt_len opt_len_set_opt_len static_len_set_opt_len matches_set_opt_len insert_set_opt_len bi_buf_set_opt_len bi_valid_set_opt_len high_water_set_opt_len self_blk_set_opt_len window_blk_set_opt_len prev_blk_set_opt_len head_blk_set_opt_len pending_buf_blk_set_opt_len strm_set_opt_len : dsf.
Lemma status_set_static_len : forall s v, ds_status (set_static_len s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_static_len : forall s v, ds_pending_buf (set_static_len s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_static_len : forall s v, ds_pending_buf_size (set_static_len s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_static_len : forall s v, ds_pending_out (set_static_len s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_static_len : forall s v, ds_pending (set_static_len s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_static_len : forall s v, ds_wrap (set_static_len s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_static_len : forall s v, ds_gzhead (set_static_len s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_static_len : forall s v, ds_gzindex (set_static_len s v) = ds_gzindex s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_static_len : forall s v, ds_method (set_static_len s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_static_len : forall s v, ds_last_flush (set_static_len s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_static_len : forall s v, ds_w_size (set_static_len s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_static_len : forall s v, ds_w_bits (set_static_len s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_static_len : forall s v, ds_w_mask (set_static_len s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_static_len : forall s v, ds_window (set_static_len s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_static_len : forall s v, ds_window_size (set_static_len s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_static_len : forall s v, ds_prev (set_static_len s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_static_len : forall s v, ds_head (set_static_len s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_static_len : forall s v, ds_ins_h (set_static_len s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_static_len : forall s v, ds_hash_size (set_static_len s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_static_len : forall s v, ds_hash_bits (set_static_len s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_static_len : forall s v, ds_hash_mask (set_static_len s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_static_len : forall s v, ds_hash_shift (set_static_len s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_static_len : forall s v, ds_block_start (set_static_len s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_static_len : forall s v, ds_match_length (set_static_len s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_static_len : forall s v, ds_prev_match (set_static_len s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_static_len : forall s v, ds_match_available (set_static_len s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_static_len : forall s v, ds_strstart (set_static_len s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_static_len : forall s v, ds_match_start (set_static_len s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_static_len : forall s v, ds_lookahead (set_static_len s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_static_len : forall s v, ds_prev_length (set_static_len s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_static_len : forall s v, ds_max_chain_length (set_static_len s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_static_len : forall s v, ds_max_lazy_match (set_static_len s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_static_len : forall s v, ds_level (set_static_len s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_static_len : forall s v, ds_strategy (set_static_len s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_static_len : forall s v, ds_good_match (set_static_len s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_static_len : forall s v, ds_nice_match (set_static_len s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_static_len : forall s v, ds_dyn_ltree_fc (set_static_len s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_static_len : forall s v, ds_dyn_ltree_dl (set_static_len s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_static_len : forall s v, ds_dyn_dtree_fc (set_static_len s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_static_len : forall s v, ds_dyn_dtree_dl (set_static_len s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_static_len : forall s v, ds_bl_tree_fc (set_static_len s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_static_len : forall s v, ds_bl_tree_dl (set_static_len s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_static_len : forall s v, ds_l_max_code (set_static_len s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_static_len : forall s v, ds_d_max_code (set_static_len s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_static_len : forall s v, ds_bl_max_code (set_static_len s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_static_len : forall s v, ds_bl_count (set_static_len s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_static_len : forall s v, ds_heap (set_static_len s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_static_len : forall s v, ds_heap_len (set_static_len s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_static_len : forall s v, ds_heap_max (set_static_len s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_static_len : forall s v, ds_depth (set_static_len s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_static_len : forall s v, ds_lit_bufsize (set_static_len s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_static_len : forall s v, ds_sym_next (set_static_len s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_static_len : forall s v, ds_sym_end (set_static_len s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_static_len : forall s v, ds_opt_len (set_static_len s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_static_len : forall s v, ds_static_len (set_static_len s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_static_len : forall s v, ds_matches (set_static_len s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_static_len : forall s v, ds_insert (set_static_len s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_static_len : forall s v, ds_bi_buf (set_static_len s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_static_len : forall s v, ds_bi_valid (set_static_len s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_static_len : forall s v, ds_high_water (set_static_len s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_static_len : forall s v, ds_self_blk (set_static_len s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_static_len : forall s v, ds_window_blk (set_static_len s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_static_len : forall s v, ds_prev_blk (set_static_len s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_static_len : forall s v, ds_head_blk (set_static_len s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_static_len : forall s v, ds_pending_buf_blk (set_static_len s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_static_len : forall s v, ds_strm (set_static_len s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_static_len pending_buf_set_static_len pending_buf_size_set_static_len pending_out_set_static_len pending_set_static_len wrap_set_static_len gzhead_set_static_len gzindex_set_static_len method_set_static_len last_flush_set_static_len w_size_set_static_len w_bits_set_static_len w_mask_set_static_len window_set_static_len window_size_set_static_len prev_set_static_len head_set_static_len ins_h_set_static_len hash_size_set_static_len hash_bits_set_static_len hash_mask_set_static_len hash_shift_set_static_len block_start_set_static_len match_length_set_static_len prev_match_set_static_len match_available_set_static_len strstart_set_static_len match_start_set_static_len lookahead_set_static_len prev_length_set_static_len max_chain_length_set_static_len max_lazy_match_set_static_len level_set_static_len strategy_set_static_len good_match_set_static_len nice_match_set_static_len dyn_ltree_fc_set_static_len dyn_ltree_dl_set_static_len dyn_dtree_fc_set_static_len dyn_dtree_dl_set_static_len bl_tree_fc_set_static_len bl_tree_dl_set_static_len l_max_code_set_static_len d_max_code_set_static_len bl_max_code_set_static_len bl_count_set_static_len heap_set_static_len heap_len_set_static_len heap_max_set_static_len depth_set_static_len lit_bufsize_set_static_len sym_next_set_static_len sym_end_set_static_len opt_len_set_static_len static_len_set_static_len matches_set_static_len insert_set_static_len bi_buf_set_static_len bi_valid_set_static_len high_water_set_static_len self_blk_set_static_len window_blk_set_static_len prev_blk_set_static_len head_blk_set_static_len pending_buf_blk_set_static_len strm_set_static_len : dsf.
Lemma status_set_gzindex : forall s v, ds_status (set_gzindex s v) = ds_status s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_set_gzindex : forall s v, ds_pending_buf (set_gzindex s v) = ds_pending_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_size_set_gzindex : forall s v, ds_pending_buf_size (set_gzindex s v) = ds_pending_buf_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_out_set_gzindex : forall s v, ds_pending_out (set_gzindex s v) = ds_pending_out s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_set_gzindex : forall s v, ds_pending (set_gzindex s v) = ds_pending s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma wrap_set_gzindex : forall s v, ds_wrap (set_gzindex s v) = ds_wrap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzhead_set_gzindex : forall s v, ds_gzhead (set_gzindex s v) = ds_gzhead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma gzindex_set_gzindex : forall s v, ds_gzindex (set_gzindex s v) = v.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma method_set_gzindex : forall s v, ds_method (set_gzindex s v) = ds_method s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma last_flush_set_gzindex : forall s v, ds_last_flush (set_gzindex s v) = ds_last_flush s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_size_set_gzindex : forall s v, ds_w_size (set_gzindex s v) = ds_w_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_bits_set_gzindex : forall s v, ds_w_bits (set_gzindex s v) = ds_w_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma w_mask_set_gzindex : forall s v, ds_w_mask (set_gzindex s v) = ds_w_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_set_gzindex : forall s v, ds_window (set_gzindex s v) = ds_window s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_size_set_gzindex : forall s v, ds_window_size (set_gzindex s v) = ds_window_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_set_gzindex : forall s v, ds_prev (set_gzindex s v) = ds_prev s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_set_gzindex : forall s v, ds_head (set_gzindex s v) = ds_head s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ins_h_set_gzindex : forall s v, ds_ins_h (set_gzindex s v) = ds_ins_h s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_size_set_gzindex : forall s v, ds_hash_size (set_gzindex s v) = ds_hash_size s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_bits_set_gzindex : forall s v, ds_hash_bits (set_gzindex s v) = ds_hash_bits s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_mask_set_gzindex : forall s v, ds_hash_mask (set_gzindex s v) = ds_hash_mask s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma hash_shift_set_gzindex : forall s v, ds_hash_shift (set_gzindex s v) = ds_hash_shift s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma block_start_set_gzindex : forall s v, ds_block_start (set_gzindex s v) = ds_block_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_length_set_gzindex : forall s v, ds_match_length (set_gzindex s v) = ds_match_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_match_set_gzindex : forall s v, ds_prev_match (set_gzindex s v) = ds_prev_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_available_set_gzindex : forall s v, ds_match_available (set_gzindex s v) = ds_match_available s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strstart_set_gzindex : forall s v, ds_strstart (set_gzindex s v) = ds_strstart s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma match_start_set_gzindex : forall s v, ds_match_start (set_gzindex s v) = ds_match_start s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lookahead_set_gzindex : forall s v, ds_lookahead (set_gzindex s v) = ds_lookahead s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_length_set_gzindex : forall s v, ds_prev_length (set_gzindex s v) = ds_prev_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_chain_length_set_gzindex : forall s v, ds_max_chain_length (set_gzindex s v) = ds_max_chain_length s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma max_lazy_match_set_gzindex : forall s v, ds_max_lazy_match (set_gzindex s v) = ds_max_lazy_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma level_set_gzindex : forall s v, ds_level (set_gzindex s v) = ds_level s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strategy_set_gzindex : forall s v, ds_strategy (set_gzindex s v) = ds_strategy s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma good_match_set_gzindex : forall s v, ds_good_match (set_gzindex s v) = ds_good_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma nice_match_set_gzindex : forall s v, ds_nice_match (set_gzindex s v) = ds_nice_match s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_set_gzindex : forall s v, ds_dyn_ltree_fc (set_gzindex s v) = ds_dyn_ltree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_set_gzindex : forall s v, ds_dyn_ltree_dl (set_gzindex s v) = ds_dyn_ltree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_set_gzindex : forall s v, ds_dyn_dtree_fc (set_gzindex s v) = ds_dyn_dtree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_set_gzindex : forall s v, ds_dyn_dtree_dl (set_gzindex s v) = ds_dyn_dtree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_set_gzindex : forall s v, ds_bl_tree_fc (set_gzindex s v) = ds_bl_tree_fc s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_set_gzindex : forall s v, ds_bl_tree_dl (set_gzindex s v) = ds_bl_tree_dl s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma l_max_code_set_gzindex : forall s v, ds_l_max_code (set_gzindex s v) = ds_l_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma d_max_code_set_gzindex : forall s v, ds_d_max_code (set_gzindex s v) = ds_d_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_max_code_set_gzindex : forall s v, ds_bl_max_code (set_gzindex s v) = ds_bl_max_code s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bl_count_set_gzindex : forall s v, ds_bl_count (set_gzindex s v) = ds_bl_count s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_set_gzindex : forall s v, ds_heap (set_gzindex s v) = ds_heap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_len_set_gzindex : forall s v, ds_heap_len (set_gzindex s v) = ds_heap_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma heap_max_set_gzindex : forall s v, ds_heap_max (set_gzindex s v) = ds_heap_max s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma depth_set_gzindex : forall s v, ds_depth (set_gzindex s v) = ds_depth s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma lit_bufsize_set_gzindex : forall s v, ds_lit_bufsize (set_gzindex s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_next_set_gzindex : forall s v, ds_sym_next (set_gzindex s v) = ds_sym_next s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma sym_end_set_gzindex : forall s v, ds_sym_end (set_gzindex s v) = ds_sym_end s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma opt_len_set_gzindex : forall s v, ds_opt_len (set_gzindex s v) = ds_opt_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma static_len_set_gzindex : forall s v, ds_static_len (set_gzindex s v) = ds_static_len s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma matches_set_gzindex : forall s v, ds_matches (set_gzindex s v) = ds_matches s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma insert_set_gzindex : forall s v, ds_insert (set_gzindex s v) = ds_insert s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_buf_set_gzindex : forall s v, ds_bi_buf (set_gzindex s v) = ds_bi_buf s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma bi_valid_set_gzindex : forall s v, ds_bi_valid (set_gzindex s v) = ds_bi_valid s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma high_water_set_gzindex : forall s v, ds_high_water (set_gzindex s v) = ds_high_water s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma self_blk_set_gzindex : forall s v, ds_self_blk (set_gzindex s v) = ds_self_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma window_blk_set_gzindex : forall s v, ds_window_blk (set_gzindex s v) = ds_window_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma prev_blk_set_gzindex : forall s v, ds_prev_blk (set_gzindex s v) = ds_prev_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma head_blk_set_gzindex : forall s v, ds_head_blk (set_gzindex s v) = ds_head_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_set_gzindex : forall s v, ds_pending_buf_blk (set_gzindex s v) = ds_pending_buf_blk s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma strm_set_gzindex : forall s v, ds_strm (set_gzindex s v) = ds_strm s.
Proof. intros s v. destruct s. reflexivity. Qed.
#[export] Hint Rewrite status_set_gzindex pending_buf_set_gzindex pending_buf_size_set_gzindex pending_out_set_gzindex pending_set_gzindex wrap_set_gzindex gzhead_set_gzindex gzindex_set_gzindex method_set_gzindex last_flush_set_gzindex w_size_set_gzindex w_bits_set_gzindex w_mask_set_gzindex window_set_gzindex window_size_set_gzindex prev_set_gzindex head_set_gzindex ins_h_set_gzindex hash_size_set_gzindex hash_bits_set_gzindex hash_mask_set_gzindex hash_shift_set_gzindex block_start_set_gzindex match_length_set_gzindex prev_match_set_gzindex match_available_set_gzindex strstart_set_gzindex match_start_set_gzindex lookahead_set_gzindex prev_length_set_gzindex max_chain_length_set_gzindex max_lazy_match_set_gzindex level_set_gzindex strategy_set_gzindex good_match_set_gzindex nice_match_set_gzindex dyn_ltree_fc_set_gzindex dyn_ltree_dl_set_gzindex dyn_dtree_fc_set_gzindex dyn_dtree_dl_set_gzindex bl_tree_fc_set_gzindex bl_tree_dl_set_gzindex l_max_code_set_gzindex d_max_code_set_gzindex bl_max_code_set_gzindex bl_count_set_gzindex heap_set_gzindex heap_len_set_gzindex heap_max_set_gzindex depth_set_gzindex lit_bufsize_set_gzindex sym_next_set_gzindex sym_end_set_gzindex opt_len_set_gzindex static_len_set_gzindex matches_set_gzindex insert_set_gzindex bi_buf_set_gzindex bi_valid_set_gzindex high_water_set_gzindex self_blk_set_gzindex window_blk_set_gzindex prev_blk_set_gzindex head_blk_set_gzindex pending_buf_blk_set_gzindex strm_set_gzindex : dsf.
Lemma cs_input_cset_input : forall st v, cs_input (cset_input st v) = v.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_next_in_cset_input : forall st v, cs_next_in (cset_input st v) = cs_next_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_in_cset_input : forall st v, cs_avail_in (cset_input st v) = cs_avail_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_out_rev_cset_input : forall st v, cs_out_rev (cset_input st v) = cs_out_rev st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_out_cset_input : forall st v, cs_avail_out (cset_input st v) = cs_avail_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_in_cset_input : forall st v, cs_total_in (cset_input st v) = cs_total_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_out_cset_input : forall st v, cs_total_out (cset_input st v) = cs_total_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_msg_cset_input : forall st v, cs_msg (cset_input st v) = cs_msg st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_data_type_cset_input : forall st v, cs_data_type (cset_input st v) = cs_data_type st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_adler_cset_input : forall st v, cs_adler (cset_input st v) = cs_adler st.
Proof. intros st v. destruct st. reflexivity. Qed.
#[export] Hint Rewrite cs_input_cset_input cs_next_in_cset_input cs_avail_in_cset_input cs_out_rev_cset_input cs_avail_out_cset_input cs_total_in_cset_input cs_total_out_cset_input cs_msg_cset_input cs_data_type_cset_input cs_adler_cset_input : dsf.
Lemma cs_input_cset_next_in : forall st v, cs_input (cset_next_in st v) = cs_input st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_next_in_cset_next_in : forall st v, cs_next_in (cset_next_in st v) = v.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_in_cset_next_in : forall st v, cs_avail_in (cset_next_in st v) = cs_avail_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_out_rev_cset_next_in : forall st v, cs_out_rev (cset_next_in st v) = cs_out_rev st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_out_cset_next_in : forall st v, cs_avail_out (cset_next_in st v) = cs_avail_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_in_cset_next_in : forall st v, cs_total_in (cset_next_in st v) = cs_total_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_out_cset_next_in : forall st v, cs_total_out (cset_next_in st v) = cs_total_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_msg_cset_next_in : forall st v, cs_msg (cset_next_in st v) = cs_msg st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_data_type_cset_next_in : forall st v, cs_data_type (cset_next_in st v) = cs_data_type st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_adler_cset_next_in : forall st v, cs_adler (cset_next_in st v) = cs_adler st.
Proof. intros st v. destruct st. reflexivity. Qed.
#[export] Hint Rewrite cs_input_cset_next_in cs_next_in_cset_next_in cs_avail_in_cset_next_in cs_out_rev_cset_next_in cs_avail_out_cset_next_in cs_total_in_cset_next_in cs_total_out_cset_next_in cs_msg_cset_next_in cs_data_type_cset_next_in cs_adler_cset_next_in : dsf.
Lemma cs_input_cset_avail_in : forall st v, cs_input (cset_avail_in st v) = cs_input st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_next_in_cset_avail_in : forall st v, cs_next_in (cset_avail_in st v) = cs_next_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_in_cset_avail_in : forall st v, cs_avail_in (cset_avail_in st v) = v.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_out_rev_cset_avail_in : forall st v, cs_out_rev (cset_avail_in st v) = cs_out_rev st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_out_cset_avail_in : forall st v, cs_avail_out (cset_avail_in st v) = cs_avail_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_in_cset_avail_in : forall st v, cs_total_in (cset_avail_in st v) = cs_total_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_out_cset_avail_in : forall st v, cs_total_out (cset_avail_in st v) = cs_total_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_msg_cset_avail_in : forall st v, cs_msg (cset_avail_in st v) = cs_msg st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_data_type_cset_avail_in : forall st v, cs_data_type (cset_avail_in st v) = cs_data_type st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_adler_cset_avail_in : forall st v, cs_adler (cset_avail_in st v) = cs_adler st.
Proof. intros st v. destruct st. reflexivity. Qed.
#[export] Hint Rewrite cs_input_cset_avail_in cs_next_in_cset_avail_in cs_avail_in_cset_avail_in cs_out_rev_cset_avail_in cs_avail_out_cset_avail_in cs_total_in_cset_avail_in cs_total_out_cset_avail_in cs_msg_cset_avail_in cs_data_type_cset_avail_in cs_adler_cset_avail_in : dsf.
Lemma cs_input_cset_out_rev : forall st v, cs_input (cset_out_rev st v) = cs_input st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_next_in_cset_out_rev : forall st v, cs_next_in (cset_out_rev st v) = cs_next_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_in_cset_out_rev : forall st v, cs_avail_in (cset_out_rev st v) = cs_avail_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_out_rev_cset_out_rev : forall st v, cs_out_rev (cset_out_rev st v) = v.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_out_cset_out_rev : forall st v, cs_avail_out (cset_out_rev st v) = cs_avail_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_in_cset_out_rev : forall st v, cs_total_in (cset_out_rev st v) = cs_total_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_out_cset_out_rev : forall st v, cs_total_out (cset_out_rev st v) = cs_total_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_msg_cset_out_rev : forall st v, cs_msg (cset_out_rev st v) = cs_msg st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_data_type_cset_out_rev : forall st v, cs_data_type (cset_out_rev st v) = cs_data_type st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_adler_cset_out_rev : forall st v, cs_adler (cset_out_rev st v) = cs_adler st.
Proof. intros st v. destruct st. reflexivity. Qed.
#[export] Hint Rewrite cs_input_cset_out_rev cs_next_in_cset_out_rev cs_avail_in_cset_out_rev cs_out_rev_cset_out_rev cs_avail_out_cset_out_rev cs_total_in_cset_out_rev cs_total_out_cset_out_rev cs_msg_cset_out_rev cs_data_type_cset_out_rev cs_adler_cset_out_rev : dsf.
Lemma cs_input_cset_avail_out : forall st v, cs_input (cset_avail_out st v) = cs_input st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_next_in_cset_avail_out : forall st v, cs_next_in (cset_avail_out st v) = cs_next_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_in_cset_avail_out : forall st v, cs_avail_in (cset_avail_out st v) = cs_avail_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_out_rev_cset_avail_out : forall st v, cs_out_rev (cset_avail_out st v) = cs_out_rev st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_out_cset_avail_out : forall st v, cs_avail_out (cset_avail_out st v) = v.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_in_cset_avail_out : forall st v, cs_total_in (cset_avail_out st v) = cs_total_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_out_cset_avail_out : forall st v, cs_total_out (cset_avail_out st v) = cs_total_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_msg_cset_avail_out : forall st v, cs_msg (cset_avail_out st v) = cs_msg st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_data_type_cset_avail_out : forall st v, cs_data_type (cset_avail_out st v) = cs_data_type st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_adler_cset_avail_out : forall st v, cs_adler (cset_avail_out st v) = cs_adler st.
Proof. intros st v. destruct st. reflexivity. Qed.
#[export] Hint Rewrite cs_input_cset_avail_out cs_next_in_cset_avail_out cs_avail_in_cset_avail_out cs_out_rev_cset_avail_out cs_avail_out_cset_avail_out cs_total_in_cset_avail_out cs_total_out_cset_avail_out cs_msg_cset_avail_out cs_data_type_cset_avail_out cs_adler_cset_avail_out : dsf.
Lemma cs_input_cset_total_in : forall st v, cs_input (cset_total_in st v) = cs_input st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_next_in_cset_total_in : forall st v, cs_next_in (cset_total_in st v) = cs_next_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_in_cset_total_in : forall st v, cs_avail_in (cset_total_in st v) = cs_avail_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_out_rev_cset_total_in : forall st v, cs_out_rev (cset_total_in st v) = cs_out_rev st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_out_cset_total_in : forall st v, cs_avail_out (cset_total_in st v) = cs_avail_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_in_cset_total_in : forall st v, cs_total_in (cset_total_in st v) = v.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_out_cset_total_in : forall st v, cs_total_out (cset_total_in st v) = cs_total_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_msg_cset_total_in : forall st v, cs_msg (cset_total_in st v) = cs_msg st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_data_type_cset_total_in : forall st v, cs_data_type (cset_total_in st v) = cs_data_type st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_adler_cset_total_in : forall st v, cs_adler (cset_total_in st v) = cs_adler st.
Proof. intros st v. destruct st. reflexivity. Qed.
#[export] Hint Rewrite cs_input_cset_total_in cs_next_in_cset_total_in cs_avail_in_cset_total_in cs_out_rev_cset_total_in cs_avail_out_cset_total_in cs_total_in_cset_total_in cs_total_out_cset_total_in cs_msg_cset_total_in cs_data_type_cset_total_in cs_adler_cset_total_in : dsf.
Lemma cs_input_cset_total_out : forall st v, cs_input (cset_total_out st v) = cs_input st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_next_in_cset_total_out : forall st v, cs_next_in (cset_total_out st v) = cs_next_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_in_cset_total_out : forall st v, cs_avail_in (cset_total_out st v) = cs_avail_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_out_rev_cset_total_out : forall st v, cs_out_rev (cset_total_out st v) = cs_out_rev st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_out_cset_total_out : forall st v, cs_avail_out (cset_total_out st v) = cs_avail_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_in_cset_total_out : forall st v, cs_total_in (cset_total_out st v) = cs_total_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_out_cset_total_out : forall st v, cs_total_out (cset_total_out st v) = v.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_msg_cset_total_out : forall st v, cs_msg (cset_total_out st v) = cs_msg st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_data_type_cset_total_out : forall st v, cs_data_type (cset_total_out st v) = cs_data_type st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_adler_cset_total_out : forall st v, cs_adler (cset_total_out st v) = cs_adler st.
Proof. intros st v. destruct st. reflexivity. Qed.
#[export] Hint Rewrite cs_input_cset_total_out cs_next_in_cset_total_out cs_avail_in_cset_total_out cs_out_rev_cset_total_out cs_avail_out_cset_total_out cs_total_in_cset_total_out cs_total_out_cset_total_out cs_msg_cset_total_out cs_data_type_cset_total_out cs_adler_cset_total_out : dsf.
Lemma cs_input_cset_msg : forall st v, cs_input (cset_msg st v) = cs_input st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_next_in_cset_msg : forall st v, cs_next_in (cset_msg st v) = cs_next_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_in_cset_msg : forall st v, cs_avail_in (cset_msg st v) = cs_avail_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_out_rev_cset_msg : forall st v, cs_out_rev (cset_msg st v) = cs_out_rev st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_out_cset_msg : forall st v, cs_avail_out (cset_msg st v) = cs_avail_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_in_cset_msg : forall st v, cs_total_in (cset_msg st v) = cs_total_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_out_cset_msg : forall st v, cs_total_out (cset_msg st v) = cs_total_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_msg_cset_msg : forall st v, cs_msg (cset_msg st v) = v.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_data_type_cset_msg : forall st v, cs_data_type (cset_msg st v) = cs_data_type st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_adler_cset_msg : forall st v, cs_adler (cset_msg st v) = cs_adler st.
Proof. intros st v. destruct st. reflexivity. Qed.
#[export] Hint Rewrite cs_input_cset_msg cs_next_in_cset_msg cs_avail_in_cset_msg cs_out_rev_cset_msg cs_avail_out_cset_msg cs_total_in_cset_msg cs_total_out_cset_msg cs_msg_cset_msg cs_data_type_cset_msg cs_adler_cset_msg : dsf.
Lemma cs_input_cset_data_type : forall st v, cs_input (cset_data_type st v) = cs_input st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_next_in_cset_data_type : forall st v, cs_next_in (cset_data_type st v) = cs_next_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_in_cset_data_type : forall st v, cs_avail_in (cset_data_type st v) = cs_avail_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_out_rev_cset_data_type : forall st v, cs_out_rev (cset_data_type st v) = cs_out_rev st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_out_cset_data_type : forall st v, cs_avail_out (cset_data_type st v) = cs_avail_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_in_cset_data_type : forall st v, cs_total_in (cset_data_type st v) = cs_total_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_out_cset_data_type : forall st v, cs_total_out (cset_data_type st v) = cs_total_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_msg_cset_data_type : forall st v, cs_msg (cset_data_type st v) = cs_msg st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_data_type_cset_data_type : forall st v, cs_data_type (cset_data_type st v) = v.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_adler_cset_data_type : forall st v, cs_adler (cset_data_type st v) = cs_adler st.
Proof. intros st v. destruct st. reflexivity. Qed.
#[export] Hint Rewrite cs_input_cset_data_type cs_next_in_cset_data_type cs_avail_in_cset_data_type cs_out_rev_cset_data_type cs_avail_out_cset_data_type cs_total_in_cset_data_type cs_total_out_cset_data_type cs_msg_cset_data_type cs_data_type_cset_data_type cs_adler_cset_data_type : dsf.
Lemma cs_input_cset_adler : forall st v, cs_input (cset_adler st v) = cs_input st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_next_in_cset_adler : forall st v, cs_next_in (cset_adler st v) = cs_next_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_in_cset_adler : forall st v, cs_avail_in (cset_adler st v) = cs_avail_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_out_rev_cset_adler : forall st v, cs_out_rev (cset_adler st v) = cs_out_rev st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_avail_out_cset_adler : forall st v, cs_avail_out (cset_adler st v) = cs_avail_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_in_cset_adler : forall st v, cs_total_in (cset_adler st v) = cs_total_in st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_total_out_cset_adler : forall st v, cs_total_out (cset_adler st v) = cs_total_out st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_msg_cset_adler : forall st v, cs_msg (cset_adler st v) = cs_msg st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_data_type_cset_adler : forall st v, cs_data_type (cset_adler st v) = cs_data_type st.
Proof. intros st v. destruct st. reflexivity. Qed.
Lemma cs_adler_cset_adler : forall st v, cs_adler (cset_adler st v) = v.
Proof. intros st v. destruct st. reflexivity. Qed.
#[export] Hint Rewrite cs_input_cset_adler cs_next_in_cset_adler cs_avail_in_cset_adler cs_out_rev_cset_adler cs_avail_out_cset_adler cs_total_in_cset_adler cs_total_out_cset_adler cs_msg_cset_adler cs_data_type_cset_adler cs_adler_cset_adler : dsf.
Lemma cs_input_cs_emit : forall st l, cs_input (cs_emit st l) = cs_input st.
Proof. intros st l. destruct st. reflexivity. Qed.
Lemma cs_next_in_cs_emit : forall st l, cs_next_in (cs_emit st l) = cs_next_in st.
Proof. intros st l. destruct st. reflexivity. Qed.
Lemma cs_avail_in_cs_emit : forall st l, cs_avail_in (cs_emit st l) = cs_avail_in st.
Proof. intros st l. destruct st. reflexivity. Qed.
Lemma cs_out_rev_cs_emit : forall st l, cs_out_rev (cs_emit st l) = List.rev_append l (cs_out_rev st).
Proof. intros st l. destruct st. reflexivity. Qed.
Lemma cs_avail_out_cs_emit : forall st l, cs_avail_out (cs_emit st l) = cs_avail_out st.
Proof. intros st l. destruct st. reflexivity. Qed.
Lemma cs_total_in_cs_emit : forall st l, cs_total_in (cs_emit st l) = cs_total_in st.
Proof. intros st l. destruct st. reflexivity. Qed.
Lemma cs_total_out_cs_emit : forall st l, cs_total_out (cs_emit st l) = cs_total_out st.
Proof. intros st l. destruct st. reflexivity. Qed.
Lemma cs_msg_cs_emit : forall st l, cs_msg (cs_emit st l) = cs_msg st.
Proof. intros st l. destruct st. reflexivity. Qed.
Lemma cs_data_type_cs_emit : forall st l, cs_data_type (cs_emit st l) = cs_data_type st.
Proof. intros st l. destruct st. reflexivity. Qed.
Lemma cs_adler_cs_emit : forall st l, cs_adler (cs_emit st l) = cs_adler st.
Proof. intros st l. destruct st. reflexivity. Qed.
#[export] Hint Rewrite cs_input_cs_emit cs_next_in_cs_emit cs_avail_in_cs_emit cs_out_rev_cs_emit cs_avail_out_cs_emit cs_total_in_cs_emit cs_total_out_cs_emit cs_msg_cs_emit cs_data_type_cs_emit cs_adler_cs_emit : dsf.
Lemma pending_put_byte : forall s c, ds_pending (put_byte s c) = (ds_pending s + 1)%Z.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma pending_buf_put_byte : forall s c, ds_pending_buf (put_byte s c) = arr_set (ds_pending_buf s) (ds_pending s) (wrap8 c).
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma status_put_byte : forall s c, ds_status (put_byte s c) = ds_status s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma pending_buf_size_put_byte : forall s c, ds_pending_buf_size (put_byte s c) = ds_pending_buf_size s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma pending_out_put_byte : forall s c, ds_pending_out (put_byte s c) = ds_pending_out s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma wrap_put_byte : forall s c, ds_wrap (put_byte s c) = ds_wrap s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma gzhead_put_byte : forall s c, ds_gzhead (put_byte s c) = ds_gzhead s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma gzindex_put_byte : forall s c, ds_gzindex (put_byte s c) = ds_gzindex s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma method_put_byte : forall s c, ds_method (put_byte s c) = ds_method s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma last_flush_put_byte : forall s c, ds_last_flush (put_byte s c) = ds_last_flush s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma w_size_put_byte : forall s c, ds_w_size (put_byte s c) = ds_w_size s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma w_bits_put_byte : forall s c, ds_w_bits (put_byte s c) = ds_w_bits s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma w_mask_put_byte : forall s c, ds_w_mask (put_byte s c) = ds_w_mask s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma window_put_byte : forall s c, ds_window (put_byte s c) = ds_window s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma window_size_put_byte : forall s c, ds_window_size (put_byte s c) = ds_window_size s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma prev_put_byte : forall s c, ds_prev (put_byte s c) = ds_prev s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma head_put_byte : forall s c, ds_head (put_byte s c) = ds_head s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma ins_h_put_byte : forall s c, ds_ins_h (put_byte s c) = ds_ins_h s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma hash_size_put_byte : forall s c, ds_hash_size (put_byte s c) = ds_hash_size s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma hash_bits_put_byte : forall s c, ds_hash_bits (put_byte s c) = ds_hash_bits s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma hash_mask_put_byte : forall s c, ds_hash_mask (put_byte s c) = ds_hash_mask s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma hash_shift_put_byte : forall s c, ds_hash_shift (put_byte s c) = ds_hash_shift s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma block_start_put_byte : forall s c, ds_block_start (put_byte s c) = ds_block_start s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma match_length_put_byte : forall s c, ds_match_length (put_byte s c) = ds_match_length s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma prev_match_put_byte : forall s c, ds_prev_match (put_byte s c) = ds_prev_match s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma match_available_put_byte : forall s c, ds_match_available (put_byte s c) = ds_match_available s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma strstart_put_byte : forall s c, ds_strstart (put_byte s c) = ds_strstart s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma match_start_put_byte : forall s c, ds_match_start (put_byte s c) = ds_match_start s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma lookahead_put_byte : forall s c, ds_lookahead (put_byte s c) = ds_lookahead s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma prev_length_put_byte : forall s c, ds_prev_length (put_byte s c) = ds_prev_length s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma max_chain_length_put_byte : forall s c, ds_max_chain_length (put_byte s c) = ds_max_chain_length s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma max_lazy_match_put_byte : forall s c, ds_max_lazy_match (put_byte s c) = ds_max_lazy_match s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma level_put_byte : forall s c, ds_level (put_byte s c) = ds_level s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma strategy_put_byte : forall s c, ds_strategy (put_byte s c) = ds_strategy s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma good_match_put_byte : forall s c, ds_good_match (put_byte s c) = ds_good_match s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma nice_match_put_byte : forall s c, ds_nice_match (put_byte s c) = ds_nice_match s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma dyn_ltree_fc_put_byte : forall s c, ds_dyn_ltree_fc (put_byte s c) = ds_dyn_ltree_fc s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma dyn_ltree_dl_put_byte : forall s c, ds_dyn_ltree_dl (put_byte s c) = ds_dyn_ltree_dl s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma dyn_dtree_fc_put_byte : forall s c, ds_dyn_dtree_fc (put_byte s c) = ds_dyn_dtree_fc s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma dyn_dtree_dl_put_byte : forall s c, ds_dyn_dtree_dl (put_byte s c) = ds_dyn_dtree_dl s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma bl_tree_fc_put_byte : forall s c, ds_bl_tree_fc (put_byte s c) = ds_bl_tree_fc s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma bl_tree_dl_put_byte : forall s c, ds_bl_tree_dl (put_byte s c) = ds_bl_tree_dl s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma l_max_code_put_byte : forall s c, ds_l_max_code (put_byte s c) = ds_l_max_code s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma d_max_code_put_byte : forall s c, ds_d_max_code (put_byte s c) = ds_d_max_code s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma bl_max_code_put_byte : forall s c, ds_bl_max_code (put_byte s c) = ds_bl_max_code s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma bl_count_put_byte : forall s c, ds_bl_count (put_byte s c) = ds_bl_count s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma heap_put_byte : forall s c, ds_heap (put_byte s c) = ds_heap s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma heap_len_put_byte : forall s c, ds_heap_len (put_byte s c) = ds_heap_len s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma heap_max_put_byte : forall s c, ds_heap_max (put_byte s c) = ds_heap_max s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma depth_put_byte : forall s c, ds_depth (put_byte s c) = ds_depth s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma lit_bufsize_put_byte : forall s c, ds_lit_bufsize (put_byte s c) = ds_lit_bufsize s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma sym_next_put_byte : forall s c, ds_sym_next (put_byte s c) = ds_sym_next s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma sym_end_put_byte : forall s c, ds_sym_end (put_byte s c) = ds_sym_end s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma opt_len_put_byte : forall s c, ds_opt_len (put_byte s c) = ds_opt_len s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma static_len_put_byte : forall s c, ds_static_len (put_byte s c) = ds_static_len s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma matches_put_byte : forall s c, ds_matches (put_byte s c) = ds_matches s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma insert_put_byte : forall s c, ds_insert (put_byte s c) = ds_insert s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma bi_buf_put_byte : forall s c, ds_bi_buf (put_byte s c) = ds_bi_buf s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma bi_valid_put_byte : forall s c, ds_bi_valid (put_byte s c) = ds_bi_valid s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma high_water_put_byte : forall s c, ds_high_water (put_byte s c) = ds_high_water s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma self_blk_put_byte : forall s c, ds_self_blk (put_byte s c) = ds_self_blk s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma window_blk_put_byte : forall s c, ds_window_blk (put_byte s c) = ds_window_blk s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma prev_blk_put_byte : forall s c, ds_prev_blk (put_byte s c) = ds_prev_blk s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma head_blk_put_byte : forall s c, ds_head_blk (put_byte s c) = ds_head_blk s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma pending_buf_blk_put_byte : forall s c, ds_pending_buf_blk (put_byte s c) = ds_pending_buf_blk s.
Proof. intros s c. destruct s. reflexivity. Qed.
Lemma strm_put_byte : forall s c, ds_strm (put_byte s c) = ds_strm s.
Proof. intros s c. destruct s. reflexivity. Qed.
#[export] Hint Rewrite pending_put_byte pending_buf_put_byte status_put_byte pending_buf_size_put_byte pending_out_put_byte wrap_put_byte gzhead_put_byte gzindex_put_byte method_put_byte last_flush_put_byte w_size_put_byte w_bits_put_byte w_mask_put_byte window_put_byte window_size_put_byte prev_put_byte head_put_byte ins_h_put_byte hash_size_put_byte hash_bits_put_byte hash_mask_put_byte hash_shift_put_byte block_start_put_byte match_length_put_byte prev_match_put_byte match_available_put_byte strstart_put_byte match_start_put_byte lookahead_put_byte prev_length_put_byte max_chain_length_put_byte max_lazy_match_put_byte level_put_byte strategy_put_byte good_match_put_byte nice_match_put_byte dyn_ltree_fc_put_byte dyn_ltree_dl_put_byte dyn_dtree_fc_put_byte dyn_dtree_dl_put_byte bl_tree_fc_put_byte bl_tree_dl_put_byte l_max_code_put_byte d_max_code_put_byte bl_max_code_put_byte bl_count_put_byte heap_put_byte heap_len_put_byte heap_max_put_byte depth_put_byte lit_bufsize_put_byte sym_next_put_byte sym_end_put_byte opt_len_put_byte static_len_put_byte matches_put_byte insert_put_byte bi_buf_put_byte bi_valid_put_byte high_water_put_byte self_blk_put_byte window_blk_put_byte prev_blk_put_byte head_blk_put_byte pending_buf_blk_put_byte strm_put_byte : dsf.
