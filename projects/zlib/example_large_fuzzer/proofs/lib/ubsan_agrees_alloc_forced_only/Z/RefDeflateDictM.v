(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
Definition zc_ao (zc : ZCall) (ao : Z) : ZCall := mkZCall (zc_input zc) ao (zc_strm zc).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sd_bad (s0 : deflate_state) : bool :=
  (ds_wrap s0 =? 2) || ((ds_wrap s0 =? 1) && negb (ds_status s0 =? INIT_STATE)) || negb (ds_lookahead s0 =? 0).
(* [comment removed for export] *)
Definition sd_s2 (s0 : deflate_state) (dict : list Z) : deflate_state :=
  set_wrap (if ds_wrap s0 =? 1
            then set_strm s0 (cset_adler (ds_strm s0) (adler32_upd (cs_adler (ds_strm s0)) dict))
            else s0) 0.
(* [comment removed for export] *)
Definition sd_clear (s2 : deflate_state) : deflate_state :=
  set_insert (set_block_start (set_strstart (clear_hash s2) 0) 0) 0.
(* [comment removed for export] *)
Definition sd_split (wrap : Z) (s2 : deflate_state) (dict : list Z) : deflate_state * list Z :=
  if ds_w_size s2 <=? zlength dict
  then (let s := if wrap =? 0 then sd_clear s2 else s2 in (s, zskipn (zlength dict - ds_w_size s) dict))
  else (s2, dict).
(* [comment removed for export] *)
Definition sd_s4 (s3 : deflate_state) (dict' : list Z) : deflate_state :=
  set_strm s3 (cset_avail_in (cset_next_in (cset_input (ds_strm s3) (arr_of_list dict')) 0) (zlength dict')).
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition csput0 (c d : cstrm) : cstrm :=
  mkCS (cs_input c) (cs_next_in d) (cs_avail_in d) (cs_out_rev c) (cs_avail_out c) (cs_total_in d)
       (cs_total_out c) (cs_msg c) (cs_data_type c) (cs_adler c).

(* [comment removed for export] *)
Definition CSK0 (s t : deflate_state) : Prop := ds_strm t = csput0 (ds_strm s) (ds_strm t) /\ ds_wrap t = 0.

(* [comment removed for export] *)

