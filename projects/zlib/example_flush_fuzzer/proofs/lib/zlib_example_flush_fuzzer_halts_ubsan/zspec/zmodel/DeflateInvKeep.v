(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition arr0 : arr := arr_make 0 0.

Definition kzap (s : deflate_state) : deflate_state :=
  (set_bi_valid (set_bi_buf (set_static_len (set_opt_len (set_heap_max (set_heap_len (set_bl_max_code (set_d_max_code (set_l_max_code (set_pending (set_depth (set_heap (set_bl_count (set_bl_tree_dl (set_bl_tree_fc (set_dyn_dtree_dl (set_dyn_dtree_fc (set_dyn_ltree_dl (set_dyn_ltree_fc (set_pending_buf s arr0) arr0) arr0) arr0) arr0) arr0) arr0) arr0) arr0) arr0) 0) 0) 0) 0) 0) 0) 0) 0) 0) 0).
Definition klens (s : deflate_state) : list Z :=
  [arr_len (ds_pending_buf s); arr_len (ds_dyn_ltree_fc s); arr_len (ds_dyn_ltree_dl s); arr_len (ds_dyn_dtree_fc s); arr_len (ds_dyn_dtree_dl s); arr_len (ds_bl_tree_fc s); arr_len (ds_bl_tree_dl s); arr_len (ds_bl_count s); arr_len (ds_heap s); arr_len (ds_depth s)].
Definition kproj (s : deflate_state) : deflate_state * list Z := (kzap s, klens s).

Lemma kp_status : forall s s', kproj s' = kproj s -> ds_status s' = ds_status s.
Proof. intros s s' H. apply (f_equal (fun q => ds_status (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_pending_buf_size : forall s s', kproj s' = kproj s -> ds_pending_buf_size s' = ds_pending_buf_size s.
Proof. intros s s' H. apply (f_equal (fun q => ds_pending_buf_size (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_pending_out : forall s s', kproj s' = kproj s -> ds_pending_out s' = ds_pending_out s.
Proof. intros s s' H. apply (f_equal (fun q => ds_pending_out (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_wrap : forall s s', kproj s' = kproj s -> ds_wrap s' = ds_wrap s.
Proof. intros s s' H. apply (f_equal (fun q => ds_wrap (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_gzhead : forall s s', kproj s' = kproj s -> ds_gzhead s' = ds_gzhead s.
Proof. intros s s' H. apply (f_equal (fun q => ds_gzhead (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_gzindex : forall s s', kproj s' = kproj s -> ds_gzindex s' = ds_gzindex s.
Proof. intros s s' H. apply (f_equal (fun q => ds_gzindex (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_method : forall s s', kproj s' = kproj s -> ds_method s' = ds_method s.
Proof. intros s s' H. apply (f_equal (fun q => ds_method (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_last_flush : forall s s', kproj s' = kproj s -> ds_last_flush s' = ds_last_flush s.
Proof. intros s s' H. apply (f_equal (fun q => ds_last_flush (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_w_size : forall s s', kproj s' = kproj s -> ds_w_size s' = ds_w_size s.
Proof. intros s s' H. apply (f_equal (fun q => ds_w_size (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_w_bits : forall s s', kproj s' = kproj s -> ds_w_bits s' = ds_w_bits s.
Proof. intros s s' H. apply (f_equal (fun q => ds_w_bits (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_w_mask : forall s s', kproj s' = kproj s -> ds_w_mask s' = ds_w_mask s.
Proof. intros s s' H. apply (f_equal (fun q => ds_w_mask (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_window : forall s s', kproj s' = kproj s -> ds_window s' = ds_window s.
Proof. intros s s' H. apply (f_equal (fun q => ds_window (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_window_size : forall s s', kproj s' = kproj s -> ds_window_size s' = ds_window_size s.
Proof. intros s s' H. apply (f_equal (fun q => ds_window_size (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_prev : forall s s', kproj s' = kproj s -> ds_prev s' = ds_prev s.
Proof. intros s s' H. apply (f_equal (fun q => ds_prev (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_head : forall s s', kproj s' = kproj s -> ds_head s' = ds_head s.
Proof. intros s s' H. apply (f_equal (fun q => ds_head (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_ins_h : forall s s', kproj s' = kproj s -> ds_ins_h s' = ds_ins_h s.
Proof. intros s s' H. apply (f_equal (fun q => ds_ins_h (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_hash_size : forall s s', kproj s' = kproj s -> ds_hash_size s' = ds_hash_size s.
Proof. intros s s' H. apply (f_equal (fun q => ds_hash_size (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_hash_bits : forall s s', kproj s' = kproj s -> ds_hash_bits s' = ds_hash_bits s.
Proof. intros s s' H. apply (f_equal (fun q => ds_hash_bits (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_hash_mask : forall s s', kproj s' = kproj s -> ds_hash_mask s' = ds_hash_mask s.
Proof. intros s s' H. apply (f_equal (fun q => ds_hash_mask (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_hash_shift : forall s s', kproj s' = kproj s -> ds_hash_shift s' = ds_hash_shift s.
Proof. intros s s' H. apply (f_equal (fun q => ds_hash_shift (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_block_start : forall s s', kproj s' = kproj s -> ds_block_start s' = ds_block_start s.
Proof. intros s s' H. apply (f_equal (fun q => ds_block_start (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_match_length : forall s s', kproj s' = kproj s -> ds_match_length s' = ds_match_length s.
Proof. intros s s' H. apply (f_equal (fun q => ds_match_length (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_prev_match : forall s s', kproj s' = kproj s -> ds_prev_match s' = ds_prev_match s.
Proof. intros s s' H. apply (f_equal (fun q => ds_prev_match (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_match_available : forall s s', kproj s' = kproj s -> ds_match_available s' = ds_match_available s.
Proof. intros s s' H. apply (f_equal (fun q => ds_match_available (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_strstart : forall s s', kproj s' = kproj s -> ds_strstart s' = ds_strstart s.
Proof. intros s s' H. apply (f_equal (fun q => ds_strstart (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_match_start : forall s s', kproj s' = kproj s -> ds_match_start s' = ds_match_start s.
Proof. intros s s' H. apply (f_equal (fun q => ds_match_start (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_lookahead : forall s s', kproj s' = kproj s -> ds_lookahead s' = ds_lookahead s.
Proof. intros s s' H. apply (f_equal (fun q => ds_lookahead (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_prev_length : forall s s', kproj s' = kproj s -> ds_prev_length s' = ds_prev_length s.
Proof. intros s s' H. apply (f_equal (fun q => ds_prev_length (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_max_chain_length : forall s s', kproj s' = kproj s -> ds_max_chain_length s' = ds_max_chain_length s.
Proof. intros s s' H. apply (f_equal (fun q => ds_max_chain_length (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_max_lazy_match : forall s s', kproj s' = kproj s -> ds_max_lazy_match s' = ds_max_lazy_match s.
Proof. intros s s' H. apply (f_equal (fun q => ds_max_lazy_match (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_level : forall s s', kproj s' = kproj s -> ds_level s' = ds_level s.
Proof. intros s s' H. apply (f_equal (fun q => ds_level (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_strategy : forall s s', kproj s' = kproj s -> ds_strategy s' = ds_strategy s.
Proof. intros s s' H. apply (f_equal (fun q => ds_strategy (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_good_match : forall s s', kproj s' = kproj s -> ds_good_match s' = ds_good_match s.
Proof. intros s s' H. apply (f_equal (fun q => ds_good_match (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_nice_match : forall s s', kproj s' = kproj s -> ds_nice_match s' = ds_nice_match s.
Proof. intros s s' H. apply (f_equal (fun q => ds_nice_match (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_lit_bufsize : forall s s', kproj s' = kproj s -> ds_lit_bufsize s' = ds_lit_bufsize s.
Proof. intros s s' H. apply (f_equal (fun q => ds_lit_bufsize (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_sym_next : forall s s', kproj s' = kproj s -> ds_sym_next s' = ds_sym_next s.
Proof. intros s s' H. apply (f_equal (fun q => ds_sym_next (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_sym_end : forall s s', kproj s' = kproj s -> ds_sym_end s' = ds_sym_end s.
Proof. intros s s' H. apply (f_equal (fun q => ds_sym_end (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_matches : forall s s', kproj s' = kproj s -> ds_matches s' = ds_matches s.
Proof. intros s s' H. apply (f_equal (fun q => ds_matches (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_insert : forall s s', kproj s' = kproj s -> ds_insert s' = ds_insert s.
Proof. intros s s' H. apply (f_equal (fun q => ds_insert (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_high_water : forall s s', kproj s' = kproj s -> ds_high_water s' = ds_high_water s.
Proof. intros s s' H. apply (f_equal (fun q => ds_high_water (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_self_blk : forall s s', kproj s' = kproj s -> ds_self_blk s' = ds_self_blk s.
Proof. intros s s' H. apply (f_equal (fun q => ds_self_blk (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_window_blk : forall s s', kproj s' = kproj s -> ds_window_blk s' = ds_window_blk s.
Proof. intros s s' H. apply (f_equal (fun q => ds_window_blk (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_prev_blk : forall s s', kproj s' = kproj s -> ds_prev_blk s' = ds_prev_blk s.
Proof. intros s s' H. apply (f_equal (fun q => ds_prev_blk (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_head_blk : forall s s', kproj s' = kproj s -> ds_head_blk s' = ds_head_blk s.
Proof. intros s s' H. apply (f_equal (fun q => ds_head_blk (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_pending_buf_blk : forall s s', kproj s' = kproj s -> ds_pending_buf_blk s' = ds_pending_buf_blk s.
Proof. intros s s' H. apply (f_equal (fun q => ds_pending_buf_blk (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_strm : forall s s', kproj s' = kproj s -> ds_strm s' = ds_strm s.
Proof. intros s s' H. apply (f_equal (fun q => ds_strm (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma kp_len_pending_buf : forall s s', kproj s' = kproj s -> arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s).
Proof. intros s s' H. apply (f_equal (fun q => nth 0%nat (snd q) 0)) in H. exact H. Qed.
Lemma kp_len_dyn_ltree_fc : forall s s', kproj s' = kproj s -> arr_len (ds_dyn_ltree_fc s') = arr_len (ds_dyn_ltree_fc s).
Proof. intros s s' H. apply (f_equal (fun q => nth 1%nat (snd q) 0)) in H. exact H. Qed.
Lemma kp_len_dyn_ltree_dl : forall s s', kproj s' = kproj s -> arr_len (ds_dyn_ltree_dl s') = arr_len (ds_dyn_ltree_dl s).
Proof. intros s s' H. apply (f_equal (fun q => nth 2%nat (snd q) 0)) in H. exact H. Qed.
Lemma kp_len_dyn_dtree_fc : forall s s', kproj s' = kproj s -> arr_len (ds_dyn_dtree_fc s') = arr_len (ds_dyn_dtree_fc s).
Proof. intros s s' H. apply (f_equal (fun q => nth 3%nat (snd q) 0)) in H. exact H. Qed.
Lemma kp_len_dyn_dtree_dl : forall s s', kproj s' = kproj s -> arr_len (ds_dyn_dtree_dl s') = arr_len (ds_dyn_dtree_dl s).
Proof. intros s s' H. apply (f_equal (fun q => nth 4%nat (snd q) 0)) in H. exact H. Qed.
Lemma kp_len_bl_tree_fc : forall s s', kproj s' = kproj s -> arr_len (ds_bl_tree_fc s') = arr_len (ds_bl_tree_fc s).
Proof. intros s s' H. apply (f_equal (fun q => nth 5%nat (snd q) 0)) in H. exact H. Qed.
Lemma kp_len_bl_tree_dl : forall s s', kproj s' = kproj s -> arr_len (ds_bl_tree_dl s') = arr_len (ds_bl_tree_dl s).
Proof. intros s s' H. apply (f_equal (fun q => nth 6%nat (snd q) 0)) in H. exact H. Qed.
Lemma kp_len_bl_count : forall s s', kproj s' = kproj s -> arr_len (ds_bl_count s') = arr_len (ds_bl_count s).
Proof. intros s s' H. apply (f_equal (fun q => nth 7%nat (snd q) 0)) in H. exact H. Qed.
Lemma kp_len_heap : forall s s', kproj s' = kproj s -> arr_len (ds_heap s') = arr_len (ds_heap s).
Proof. intros s s' H. apply (f_equal (fun q => nth 8%nat (snd q) 0)) in H. exact H. Qed.
Lemma kp_len_depth : forall s s', kproj s' = kproj s -> arr_len (ds_depth s') = arr_len (ds_depth s).
Proof. intros s s' H. apply (f_equal (fun q => nth 9%nat (snd q) 0)) in H. exact H. Qed.

Lemma kp_set_pending : forall s v, kproj (set_pending s v) = kproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma kp_set_l_max_code : forall s v, kproj (set_l_max_code s v) = kproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma kp_set_d_max_code : forall s v, kproj (set_d_max_code s v) = kproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma kp_set_bl_max_code : forall s v, kproj (set_bl_max_code s v) = kproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma kp_set_heap_len : forall s v, kproj (set_heap_len s v) = kproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma kp_set_heap_max : forall s v, kproj (set_heap_max s v) = kproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma kp_set_opt_len : forall s v, kproj (set_opt_len s v) = kproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma kp_set_static_len : forall s v, kproj (set_static_len s v) = kproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma kp_set_bi_buf : forall s v, kproj (set_bi_buf s v) = kproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma kp_set_bi_valid : forall s v, kproj (set_bi_valid s v) = kproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma kp_set_pending_buf : forall s a, arr_len a = arr_len (ds_pending_buf s) -> kproj (set_pending_buf s a) = kproj s.
Proof. intros s a H. destruct s. unfold kproj, klens. cbn -[arr_len]. cbn -[arr_len] in H. rewrite H. reflexivity. Qed.
Lemma kp_set_dyn_ltree_fc : forall s a, arr_len a = arr_len (ds_dyn_ltree_fc s) -> kproj (set_dyn_ltree_fc s a) = kproj s.
Proof. intros s a H. destruct s. unfold kproj, klens. cbn -[arr_len]. cbn -[arr_len] in H. rewrite H. reflexivity. Qed.
Lemma kp_set_dyn_ltree_dl : forall s a, arr_len a = arr_len (ds_dyn_ltree_dl s) -> kproj (set_dyn_ltree_dl s a) = kproj s.
Proof. intros s a H. destruct s. unfold kproj, klens. cbn -[arr_len]. cbn -[arr_len] in H. rewrite H. reflexivity. Qed.
Lemma kp_set_dyn_dtree_fc : forall s a, arr_len a = arr_len (ds_dyn_dtree_fc s) -> kproj (set_dyn_dtree_fc s a) = kproj s.
Proof. intros s a H. destruct s. unfold kproj, klens. cbn -[arr_len]. cbn -[arr_len] in H. rewrite H. reflexivity. Qed.
Lemma kp_set_dyn_dtree_dl : forall s a, arr_len a = arr_len (ds_dyn_dtree_dl s) -> kproj (set_dyn_dtree_dl s a) = kproj s.
Proof. intros s a H. destruct s. unfold kproj, klens. cbn -[arr_len]. cbn -[arr_len] in H. rewrite H. reflexivity. Qed.
Lemma kp_set_bl_tree_fc : forall s a, arr_len a = arr_len (ds_bl_tree_fc s) -> kproj (set_bl_tree_fc s a) = kproj s.
Proof. intros s a H. destruct s. unfold kproj, klens. cbn -[arr_len]. cbn -[arr_len] in H. rewrite H. reflexivity. Qed.
Lemma kp_set_bl_tree_dl : forall s a, arr_len a = arr_len (ds_bl_tree_dl s) -> kproj (set_bl_tree_dl s a) = kproj s.
Proof. intros s a H. destruct s. unfold kproj, klens. cbn -[arr_len]. cbn -[arr_len] in H. rewrite H. reflexivity. Qed.
Lemma kp_set_bl_count : forall s a, arr_len a = arr_len (ds_bl_count s) -> kproj (set_bl_count s a) = kproj s.
Proof. intros s a H. destruct s. unfold kproj, klens. cbn -[arr_len]. cbn -[arr_len] in H. rewrite H. reflexivity. Qed.
Lemma kp_set_heap : forall s a, arr_len a = arr_len (ds_heap s) -> kproj (set_heap s a) = kproj s.
Proof. intros s a H. destruct s. unfold kproj, klens. cbn -[arr_len]. cbn -[arr_len] in H. rewrite H. reflexivity. Qed.
Lemma kp_set_depth : forall s a, arr_len a = arr_len (ds_depth s) -> kproj (set_depth s a) = kproj s.
Proof. intros s a H. destruct s. unfold kproj, klens. cbn -[arr_len]. cbn -[arr_len] in H. rewrite H. reflexivity. Qed.


Create HintDb kp.
Hint Rewrite kp_set_pending kp_set_l_max_code kp_set_d_max_code kp_set_bl_max_code kp_set_heap_len kp_set_heap_max
  kp_set_opt_len kp_set_static_len kp_set_bi_buf kp_set_bi_valid : kp.
Ltac kp := autorewrite with kp; try reflexivity.


Lemma kp_set_tree_fc : forall s t a, arr_len a = arr_len (tree_fc s t) -> kproj (set_tree_fc s t a) = kproj s.
Proof. intros s [| |] a H; cbn [set_tree_fc tree_fc] in *; [apply kp_set_dyn_ltree_fc | apply kp_set_dyn_dtree_fc | apply kp_set_bl_tree_fc]; exact H. Qed.
Lemma kp_set_tree_dl : forall s t a, arr_len a = arr_len (tree_dl s t) -> kproj (set_tree_dl s t a) = kproj s.
Proof. intros s [| |] a H; cbn [set_tree_dl tree_dl] in *; [apply kp_set_dyn_ltree_dl | apply kp_set_dyn_dtree_dl | apply kp_set_bl_tree_dl]; exact H. Qed.
Lemma kp_set_Freq : forall s t n v, kproj (set_Freq s t n v) = kproj s.
Proof. intros. unfold set_Freq. apply kp_set_tree_fc. apply arr_len_set. Qed.
Lemma kp_set_Code : forall s t n v, kproj (set_Code s t n v) = kproj s.
Proof. exact kp_set_Freq. Qed.
Lemma kp_set_Dad : forall s t n v, kproj (set_Dad s t n v) = kproj s.
Proof. intros. unfold set_Dad. apply kp_set_tree_dl. apply arr_len_set. Qed.
Lemma kp_set_Len : forall s t n v, kproj (set_Len s t n v) = kproj s.
Proof. exact kp_set_Dad. Qed.
Lemma kp_set_max_code : forall s t v, kproj (set_max_code s t v) = kproj s.
Proof. intros s [| |] v; cbn [set_max_code]; [apply kp_set_l_max_code | apply kp_set_d_max_code | apply kp_set_bl_max_code]. Qed.
Lemma kp_heap_set : forall s i v, kproj (heap_set s i v) = kproj s.
Proof. intros. unfold heap_set. apply kp_set_heap. apply arr_len_set. Qed.
Lemma kp_depth_set : forall s i v, kproj (depth_set s i v) = kproj s.
Proof. intros. unfold depth_set. apply kp_set_depth. apply arr_len_set. Qed.
Lemma kp_bl_count_set : forall s i v, kproj (bl_count_set s i v) = kproj s.
Proof. intros. unfold bl_count_set. apply kp_set_bl_count. apply arr_len_set. Qed.
Lemma kp_put_byte : forall s c, kproj (put_byte s c) = kproj s.
Proof. intros. unfold put_byte. rewrite kp_set_pending. apply kp_set_pending_buf. apply arr_len_set. Qed.
Lemma kp_sym_buf_set : forall s i v, kproj (sym_buf_set s i v) = kproj s.
Proof. intros. unfold sym_buf_set. apply kp_set_pending_buf. apply arr_len_set. Qed.
Lemma kp_put_short : forall s w, kproj (put_short s w) = kproj s.
Proof. intros. unfold put_short. rewrite !kp_put_byte. reflexivity. Qed.
Lemma kp_bi_flush : forall s, kproj (bi_flush s) = kproj s.
Proof.
  intros s. unfold bi_flush. destruct (ds_bi_valid s =? 16); [| destruct (8 <=? ds_bi_valid s)];
    rewrite ?kp_set_bi_valid, ?kp_set_bi_buf, ?kp_put_short, ?kp_put_byte; reflexivity.
Qed.
Lemma kp_bi_windup : forall s, kproj (bi_windup s) = kproj s.
Proof.
  intros s. unfold bi_windup. rewrite kp_set_bi_valid, kp_set_bi_buf.
  destruct (8 <? ds_bi_valid s); [apply kp_put_short|]. destruct (0 <? ds_bi_valid s); [apply kp_put_byte | reflexivity].
Qed.
Lemma kp_send_bits : forall s v l, kproj (send_bits s v l) = kproj s.
Proof.
  intros s v l. unfold send_bits. destruct (Buf_size - l <? ds_bi_valid s);
    rewrite ?kp_set_bi_valid, ?kp_set_bi_buf, ?kp_put_short, ?kp_set_bi_buf; reflexivity.
Qed.
Lemma kp_send_code : forall s c tfc tdl, kproj (send_code s c tfc tdl) = kproj s.
Proof. intros. unfold send_code. apply kp_send_bits. Qed.
Lemma kp_send_dcode : forall s c t, kproj (send_dcode s c t) = kproj s.
Proof. intros. unfold send_dcode. apply kp_send_bits. Qed.
Lemma kp_tr_flush_bits : forall s, kproj (tr_flush_bits s) = kproj s.
Proof. exact kp_bi_flush. Qed.
Lemma kp_tr_align : forall s, kproj (tr_align s) = kproj s.
Proof. intros s. unfold tr_align. rewrite kp_bi_flush, kp_send_code. apply kp_send_bits. Qed.
Lemma kp_putShortMSB : forall s b, kproj (putShortMSB s b) = kproj s.
Proof. intros. unfold putShortMSB. rewrite !kp_put_byte. reflexivity. Qed.

Hint Rewrite kp_set_Freq kp_set_Code kp_set_Dad kp_set_Len kp_set_max_code kp_heap_set kp_depth_set kp_bl_count_set
  kp_put_byte kp_sym_buf_set kp_put_short kp_bi_flush kp_bi_windup kp_send_bits kp_send_code kp_send_dcode kp_tr_flush_bits
  kp_tr_align kp_putShortMSB : kp.


Lemma kp_pqdownheap_loop : forall f s t v k j, kproj (fst (pqdownheap_loop f s t v k j)) = kproj s.
Proof.
  induction f as [|f IH]; intros s t v k j; cbn [pqdownheap_loop fst]; [reflexivity|].
  destruct (j <=? ds_heap_len s); [| reflexivity].
  destruct (smaller s t v _); [reflexivity|]. rewrite IH. apply kp_heap_set.
Qed.
Lemma kp_pqdownheap : forall s t k, kproj (pqdownheap s t k) = kproj s.
Proof.
  intros s t k. unfold pqdownheap.
  destruct (pqdownheap_loop 32 s t (heap_get s k) k (Z.shiftl k 1)) as [s1 k1] eqn:E.
  rewrite kp_heap_set. apply (f_equal fst) in E. cbn [fst] in E. rewrite <- E. apply kp_pqdownheap_loop.
Qed.
Hint Rewrite kp_pqdownheap : kp.
Lemma kp_gen_bitlen_loop1 : forall f s t mc base ml h ov, kproj (fst (gen_bitlen_loop1 f s t mc base ml h ov)) = kproj s.
Proof.
  induction f as [|f IH]; intros s t mc base ml h ov; cbn [gen_bitlen_loop1 fst]; [reflexivity|].
  destruct (h <? HEAP_SIZE); [| reflexivity].
  destruct (ml <? Len s t (Dad s t (heap_get s h)) + 1); (destruct (mc <? heap_get s h); [rewrite IH; apply kp_set_Len|]);
    rewrite IH; (destruct (stree_has t); [rewrite kp_set_static_len|]); rewrite kp_set_opt_len, kp_bl_count_set; apply kp_set_Len.
Qed.
Lemma kp_gen_bitlen_loop2 : forall f s ml ov, kproj (gen_bitlen_loop2 f s ml ov) = kproj s.
Proof.
  induction f as [|f IH]; intros s ml ov; cbn [gen_bitlen_loop2]; [reflexivity|].
  destruct (0 <? ov - 2); rewrite ?IH, !kp_bl_count_set; reflexivity.
Qed.
Hint Rewrite kp_gen_bitlen_loop2 : kp.
Lemma kp_gen_bitlen_loop3i : forall f s t mc bits n h, kproj (fst (gen_bitlen_loop3i f s t mc bits n h)) = kproj s.
Proof.
  induction f as [|f IH]; intros s t mc bits n h; cbn [gen_bitlen_loop3i fst]; [reflexivity|].
  destruct (negb (n =? 0)); [| reflexivity].
  destruct (mc <? heap_get s (h - 1)); [apply IH|].
  rewrite IH. destruct (negb (Len s t (heap_get s (h - 1)) =? bits)); [| reflexivity].
  rewrite kp_set_Len. apply kp_set_opt_len.
Qed.
Lemma kp_gen_bitlen_loop3 : forall f s t mc bits h, kproj (gen_bitlen_loop3 f s t mc bits h) = kproj s.
Proof.
  induction f as [|f IH]; intros s t mc bits h; cbn [gen_bitlen_loop3]; [reflexivity|].
  destruct (negb (bits =? 0)); [| reflexivity].
  destruct (gen_bitlen_loop3i 574 s t mc bits (bl_count_get s bits) h) as [s1 h1] eqn:E.
  rewrite IH. apply (f_equal fst) in E. cbn [fst] in E. rewrite <- E. apply kp_gen_bitlen_loop3i.
Qed.
Hint Rewrite kp_gen_bitlen_loop3 : kp.
Lemma kp_gen_bitlen : forall s t, kproj (gen_bitlen s t) = kproj s.
Proof.
  intros s t. unfold gen_bitlen.
  match goal with |- context [gen_bitlen_loop1 ?f ?s1 ?t1 ?a ?b ?c ?d ?e] =>
    destruct (gen_bitlen_loop1 f s1 t1 a b c d e) as [s2 ov] eqn:E;
    pose proof (kp_gen_bitlen_loop1 f s1 t1 a b c d e) as K; rewrite E in K; cbn [fst] in K end.
  rewrite kp_set_Len, kp_set_bl_count in K by (rewrite arr_len_fill; reflexivity).
  destruct (ov =? 0); [exact K|]. rewrite kp_gen_bitlen_loop3, kp_gen_bitlen_loop2. exact K.
Qed.
Hint Rewrite kp_gen_bitlen : kp.
Lemma kp_gen_codes_loop2 : forall f s t nc mc n, kproj (gen_codes_loop2 f s t nc mc n) = kproj s.
Proof.
  induction f as [|f IH]; intros s t nc mc n; cbn [gen_codes_loop2]; [reflexivity|].
  destruct (n <=? mc); [| reflexivity]. destruct (Len s t n =? 0); [apply IH|]. rewrite IH. apply kp_set_Code.
Qed.
Lemma kp_gen_codes : forall s t mc, kproj (gen_codes s t mc) = kproj s.
Proof. intros. unfold gen_codes. apply kp_gen_codes_loop2. Qed.
Hint Rewrite kp_gen_codes : kp.

Lemma kp_build_tree_loop1 : forall f s t el n mc, kproj (fst (build_tree_loop1 f s t el n mc)) = kproj s.
Proof.
  induction f as [|f IH]; intros s t el n mc; cbn [build_tree_loop1 fst]; [reflexivity|].
  destruct (n <? el); [| reflexivity].
  destruct (negb (Freq s t n =? 0)); rewrite IH; [rewrite kp_depth_set, kp_heap_set; apply kp_set_heap_len | apply kp_set_Len].
Qed.
Lemma kp_build_tree_loop2 : forall f s t mc, kproj (fst (build_tree_loop2 f s t mc)) = kproj s.
Proof.
  induction f as [|f IH]; intros s t mc; cbn [build_tree_loop2 fst]; [reflexivity|].
  destruct (ds_heap_len s <? 2); [| reflexivity].
  destruct (mc <? 2); rewrite IH; (destruct (stree_has t); [rewrite kp_set_static_len|]);
    rewrite kp_set_opt_len, kp_depth_set, kp_set_Freq, kp_heap_set; apply kp_set_heap_len.
Qed.
Lemma kp_build_tree_loop3 : forall f s t n, kproj (build_tree_loop3 f s t n) = kproj s.
Proof.
  induction f as [|f IH]; intros s t n; cbn [build_tree_loop3]; [reflexivity|].
  destruct (1 <=? n); [| reflexivity]. rewrite IH. apply kp_pqdownheap.
Qed.
Hint Rewrite kp_build_tree_loop3 : kp.
Lemma kp_build_tree_loop4 : forall f s t node, kproj (build_tree_loop4 f s t node) = kproj s.
Proof.
  induction f as [|f IH]; intros s t node; cbn [build_tree_loop4]; [reflexivity|].
  match goal with |- context [if ?c then _ else _] => destruct c end; rewrite ?IH; kp.
Qed.
Hint Rewrite kp_build_tree_loop4 : kp.
Lemma kp_build_tree : forall s t, kproj (build_tree s t) = kproj s.
Proof.
  intros s t. unfold build_tree.
  match goal with |- context [build_tree_loop1 ?f ?s1 ?t1 ?a ?b ?c] =>
    destruct (build_tree_loop1 f s1 t1 a b c) as [s2 mc2] eqn:E1;
    pose proof (kp_build_tree_loop1 f s1 t1 a b c) as K1; rewrite E1 in K1; cbn [fst] in K1 end.
  rewrite kp_set_heap_max, kp_set_heap_len in K1.
  destruct (build_tree_loop2 2 s2 t mc2) as [s3 mc3] eqn:E2.
  pose proof (kp_build_tree_loop2 2 s2 t mc2) as K2. rewrite E2 in K2. cbn [fst] in K2.
  rewrite kp_gen_codes, kp_gen_bitlen, kp_heap_set, kp_set_heap_max, kp_build_tree_loop4, kp_build_tree_loop3, kp_set_max_code, K2. exact K1.
Qed.
Hint Rewrite kp_build_tree : kp.


Lemma kp_scan_tree_loop : forall f s t mc n pl nl c mx mn, kproj (scan_tree_loop f s t mc n pl nl c mx mn) = kproj s.
Proof.
  induction f as [|f IH]; intros s t mc n pl nl c mx mn; cbn [scan_tree_loop]; [reflexivity|].
  destruct (n <=? mc); [| reflexivity].
  destruct ((c + 1 <? mx) && (nl =? Len s t (n + 1))); [apply IH|].
  destruct (tree_counts nl (Len s t (n + 1))) as [mx' mn']. rewrite IH.
  destruct (c + 1 <? mn); [apply kp_set_Freq|]. destruct (negb (nl =? 0)); [| destruct (c + 1 <=? 10); apply kp_set_Freq].
  rewrite kp_set_Freq. destruct (negb (nl =? pl)); [apply kp_set_Freq | reflexivity].
Qed.
Hint Rewrite kp_scan_tree_loop : kp.
Lemma kp_scan_tree : forall s t mc, kproj (scan_tree s t mc) = kproj s.
Proof.
  intros s t mc. unfold scan_tree. destruct (Len s t 0 =? 0); rewrite kp_scan_tree_loop; apply kp_set_Len.
Qed.
Hint Rewrite kp_scan_tree : kp.
Lemma kp_send_tree_rep : forall f s cl c, kproj (send_tree_rep f s cl c) = kproj s.
Proof.
  induction f as [|f IH]; intros s cl c; cbn [send_tree_rep]; [reflexivity|].
  destruct (negb (c - 1 =? 0)); rewrite ?IH; apply kp_send_dcode.
Qed.
Hint Rewrite kp_send_tree_rep : kp.
Lemma kp_send_tree_loop : forall f s t mc n pl nl c mx mn, kproj (send_tree_loop f s t mc n pl nl c mx mn) = kproj s.
Proof.
  induction f as [|f IH]; intros s t mc n pl nl c mx mn; cbn [send_tree_loop]; [reflexivity|].
  destruct (n <=? mc); [| reflexivity].
  destruct ((c + 1 <? mx) && (nl =? Len s t (n + 1))); [apply IH|].
  destruct (tree_counts nl (Len s t (n + 1))) as [mx' mn']. rewrite IH.
  destruct (c + 1 <? mn); [apply kp_send_tree_rep|].
  destruct (negb (nl =? 0)).
  - destruct (negb (nl =? pl)); rewrite kp_send_bits, kp_send_dcode; [apply kp_send_dcode | reflexivity].
  - destruct (c + 1 <=? 10); rewrite kp_send_bits; apply kp_send_dcode.
Qed.
Hint Rewrite kp_send_tree_loop : kp.
Lemma kp_send_tree : forall s t mc, kproj (send_tree s t mc) = kproj s.
Proof. intros s t mc. unfold send_tree. destruct (Len s t 0 =? 0); apply kp_send_tree_loop. Qed.
Hint Rewrite kp_send_tree : kp.
Lemma kp_build_bl_tree : forall s, kproj (fst (build_bl_tree s)) = kproj s.
Proof.
  intros s. unfold build_bl_tree. cbn [fst]. rewrite kp_set_opt_len, kp_build_tree, !kp_scan_tree. reflexivity.
Qed.
Lemma kp_send_all_trees_loop : forall f s bl r, kproj (send_all_trees_loop f s bl r) = kproj s.
Proof.
  induction f as [|f IH]; intros s bl r; cbn [send_all_trees_loop]; [reflexivity|].
  destruct (r <? bl); [| reflexivity]. rewrite IH. apply kp_send_bits.
Qed.
Hint Rewrite kp_send_all_trees_loop : kp.
Lemma kp_send_all_trees : forall s lc dc bc, kproj (send_all_trees s lc dc bc) = kproj s.
Proof. intros. unfold send_all_trees. rewrite !kp_send_tree, kp_send_all_trees_loop, !kp_send_bits. reflexivity. Qed.
Hint Rewrite kp_send_all_trees : kp.
Lemma kp_tr_stored_block : forall s buf len last, kproj (tr_stored_block s buf len last) = kproj s.
Proof.
  intros s buf len last. unfold tr_stored_block. rewrite kp_set_pending.
  assert (X : forall s1, kproj (if negb (len =? 0) then match buf with Some off => set_pending_buf s1 (arr_blit (ds_pending_buf s1) (ds_pending s1) (ds_window s1) off len) | None => s1 end else s1) = kproj s1).
  { intros s1. destruct (negb (len =? 0)); [| reflexivity]. destruct buf; [| reflexivity]. apply kp_set_pending_buf. apply arr_len_blit. }
  rewrite X, !kp_put_short, kp_bi_windup. apply kp_send_bits.
Qed.
Hint Rewrite kp_tr_stored_block : kp.
Lemma kp_compress_block_sym : forall s lfc ldl dfc ddl sx, kproj (fst (compress_block_sym s lfc ldl dfc ddl sx)) = kproj s.
Proof.
  intros. unfold compress_block_sym.
  destruct (_ =? 0); cbn [fst]; [apply kp_send_code|].
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; rewrite ?kp_send_bits, ?kp_send_code, ?kp_send_bits, ?kp_send_code; reflexivity.
Qed.
Lemma kp_compress_block_loop : forall f s lfc ldl dfc ddl sx, kproj (compress_block_loop f s lfc ldl dfc ddl sx) = kproj s.
Proof.
  induction f as [|f IH]; intros; cbn [compress_block_loop]; [reflexivity|].
  destruct (compress_block_sym s lfc ldl dfc ddl sx) as [s1 sx1] eqn:E.
  pose proof (kp_compress_block_sym s lfc ldl dfc ddl sx) as K. rewrite E in K. cbn [fst] in K.
  destruct (sx1 <? ds_sym_next s1); [rewrite IH|]; exact K.
Qed.
Hint Rewrite kp_compress_block_loop : kp.
Lemma kp_compress_block : forall s lfc ldl dfc ddl, kproj (compress_block s lfc ldl dfc ddl) = kproj s.
Proof.
  intros. unfold compress_block. rewrite kp_send_code. destruct (negb (ds_sym_next s =? 0)); [apply kp_compress_block_loop | reflexivity].
Qed.
Hint Rewrite kp_compress_block : kp.


Lemma kp_init_block : forall s, kproj (init_block s) = kproj (set_sym_next (set_matches s 0) 0).
Proof.
  intros s. unfold kproj, klens, init_block, set_Freq. destruct s; cbn -[arr_len arr_fill arr_set Z.add].
  rewrite ?arr_len_set, ?arr_len_fill. reflexivity.
Qed.


Lemma kp_tr_flush_block : forall s buf len last,
  kproj (tr_flush_block s buf len last)
  = kproj (set_strm (set_sym_next (set_matches s 0) 0) (cset_data_type (ds_strm s) (cs_data_type (ds_strm (tr_flush_block s buf len last))))).
Proof.
  intros s buf len last. unfold tr_flush_block.
  set (s1 := if cs_data_type (ds_strm s) =? Z_UNKNOWN then set_strm s (cset_data_type (ds_strm s) (detect_data_type s)) else s).
  assert (K1 : kproj s1 = kproj (set_strm s (cset_data_type (ds_strm s) (cs_data_type (ds_strm s1))))).
  { subst s1. destruct (cs_data_type (ds_strm s) =? Z_UNKNOWN); destruct s; cbn; [reflexivity|]. destruct ds_strm; reflexivity. }
  assert (KG : forall x, kproj (set_sym_next (set_matches x 0) 0) = (set_sym_next (set_matches (fst (kproj x)) 0) 0, snd (kproj x))).
  { intros x. destruct x; reflexivity. }
  assert (GEN : forall (a b : deflate_state),
            kproj a = kproj (set_strm b (cset_data_type (ds_strm b) (cs_data_type (ds_strm a)))) ->
            kproj (if negb (last =? 0) then bi_windup (init_block a) else init_block a)
            = kproj (set_strm (set_sym_next (set_matches b 0) 0)
                       (cset_data_type (ds_strm b) (cs_data_type (ds_strm (if negb (last =? 0) then bi_windup (init_block a) else init_block a)))))).
  { intros a b H.
    assert (SW : ds_strm (if negb (last =? 0) then bi_windup (init_block a) else init_block a) = ds_strm a).
    { destruct (negb (last =? 0)); [rewrite (kp_strm _ _ (kp_bi_windup _))|]; destruct a; reflexivity. }
    rewrite SW.
    transitivity (kproj (init_block a)); [destruct (negb (last =? 0)); [apply kp_bi_windup | reflexivity]|].
    rewrite kp_init_block.
    replace (set_strm (set_sym_next (set_matches b 0) 0) (cset_data_type (ds_strm b) (cs_data_type (ds_strm a))))
       with (set_sym_next (set_matches (set_strm b (cset_data_type (ds_strm b) (cs_data_type (ds_strm a)))) 0) 0) by (destruct b; reflexivity).
    rewrite !KG, H. reflexivity. }
  destruct (0 <? ds_level s) eqn:EL.
  - destruct (build_bl_tree (build_tree (build_tree s1 TL) TD)) as [s4 mb] eqn:E4.
    pose proof (kp_build_bl_tree (build_tree (build_tree s1 TL) TD)) as K4. rewrite E4 in K4. cbn [fst] in K4. rewrite !kp_build_tree in K4.
    cbv beta iota zeta. apply GEN.
    match goal with |- kproj ?a = _ => set (X7 := a) in * end.
    assert (KA : kproj X7 = kproj s1).
    { subst X7. repeat match goal with |- context [if ?c then _ else _] => destruct c end;
        rewrite ?kp_tr_stored_block, ?kp_compress_block, ?kp_send_all_trees, ?kp_send_bits; exact K4. }
    rewrite (kp_strm _ _ KA), KA, K1. destruct s, s1; reflexivity.
  - cbv beta iota zeta. apply GEN.
    match goal with |- kproj ?a = _ => set (X7 := a) in * end.
    assert (KA : kproj X7 = kproj s).
    { subst X7. repeat match goal with |- context [if ?c then _ else _] => destruct c end;
        rewrite ?kp_tr_stored_block, ?kp_compress_block, ?kp_send_all_trees, ?kp_send_bits; reflexivity. }
    rewrite (kp_strm _ _ KA), KA. destruct s; cbn; destruct ds_strm; reflexivity.
Qed.

Definition ksn (p : deflate_state * list Z) (v : Z) : deflate_state * list Z := (set_sym_next (fst p) v, snd p).
Lemma kp_set_sym_next : forall a v, kproj (set_sym_next a v) = ksn (kproj a) v.
Proof. intros a v. destruct a; reflexivity. Qed.
Lemma ksn_ksn : forall p v w, ksn (ksn p v) w = ksn p w.
Proof. intros [d l] v w. destruct d; reflexivity. Qed.
Lemma sym_next_sym_buf_set : forall s i v, ds_sym_next (sym_buf_set s i v) = ds_sym_next s.
Proof. intros. destruct s; reflexivity. Qed.
Lemma sym_next_set_sym_next : forall s v, ds_sym_next (set_sym_next s v) = v.
Proof. intros. destruct s; reflexivity. Qed.
Lemma kp_tr_tally_lit : forall s c, kproj (fst (tr_tally_lit s c)) = kproj (set_sym_next s (ds_sym_next s + 3)).
Proof.
  intros s c. unfold tr_tally_lit. cbn [fst].
  rewrite kp_set_Freq, kp_set_sym_next, kp_sym_buf_set, kp_set_sym_next, kp_sym_buf_set, kp_set_sym_next, kp_sym_buf_set, !ksn_ksn.
  repeat first [rewrite sym_next_sym_buf_set | rewrite sym_next_set_sym_next]. rewrite kp_set_sym_next. f_equal. lia.
Qed.
Lemma kp_tr_tally_dist : forall s d l, kproj (fst (tr_tally_dist s d l)) = kproj (set_sym_next s (ds_sym_next s + 3)).
Proof.
  intros s d l. unfold tr_tally_dist. cbn [fst].
  rewrite !kp_set_Freq, kp_set_sym_next, kp_sym_buf_set, kp_set_sym_next, kp_sym_buf_set, kp_set_sym_next, kp_sym_buf_set, !ksn_ksn.
  repeat first [rewrite sym_next_sym_buf_set | rewrite sym_next_set_sym_next]. rewrite kp_set_sym_next. f_equal. lia.
Qed.


Definition u16a (a : arr) : Prop := forall i, 0 <= i < arr_len a -> 0 <= arr_get a i < 65536.
Definition u8a (a : arr) : Prop := forall i, 0 <= i < arr_len a -> 0 <= arr_get a i < 256.

Record cty (s : deflate_state) : Prop := CTY {
  ct_lfc : u16a (ds_dyn_ltree_fc s); ct_ldl : u16a (ds_dyn_ltree_dl s);
  ct_dfc : u16a (ds_dyn_dtree_fc s); ct_ddl : u16a (ds_dyn_dtree_dl s);
  ct_bfc : u16a (ds_bl_tree_fc s); ct_bdl : u16a (ds_bl_tree_dl s);
  ct_blc : u16a (ds_bl_count s); ct_dep : u8a (ds_depth s); ct_pb : u8a (ds_pending_buf s);
  ct_win : u8a (ds_window s); ct_prev : u16a (ds_prev s); ct_head : u16a (ds_head s);
  ct_in : u8a (cs_input (ds_strm s)) }.

Lemma wrap16_range : forall z, 0 <= wrap16 z < 65536.
Proof. intros z. unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma wrap8_range : forall z, 0 <= wrap8 z < 256.
Proof. intros z. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma u16a_set : forall a i v, u16a a -> 0 <= v < 65536 -> u16a (arr_set a i v).
Proof.
  intros a i v H Hv j Hj. rewrite arr_len_set in Hj.
  destruct (Z.eq_dec i j) as [<-|Hne]; [rewrite arr_get_set_same by exact Hj; exact Hv | rewrite arr_get_set_other by exact Hne; exact (H j Hj)].
Qed.
Lemma u8a_set : forall a i v, u8a a -> 0 <= v < 256 -> u8a (arr_set a i v).
Proof.
  intros a i v H Hv j Hj. rewrite arr_len_set in Hj.
  destruct (Z.eq_dec i j) as [<-|Hne]; [rewrite arr_get_set_same by exact Hj; exact Hv | rewrite arr_get_set_other by exact Hne; exact (H j Hj)].
Qed.
Lemma u16a_setw : forall a i v, u16a a -> u16a (arr_set a i (wrap16 v)).
Proof. intros. apply u16a_set; [assumption | apply wrap16_range]. Qed.
Lemma u8a_setw : forall a i v, u8a a -> u8a (arr_set a i (wrap8 v)).
Proof. intros. apply u8a_set; [assumption | apply wrap8_range]. Qed.
Lemma u16a_fill : forall a o n v, u16a a -> 0 <= v < 65536 -> u16a (arr_fill a o n v).
Proof.
  intros a o n v H Hv j Hj. rewrite arr_len_fill in Hj. rewrite arr_get_fill.
  destruct (_ && _); [exact Hv | exact (H j Hj)].
Qed.
Lemma u8a_blit : forall d dofs a sofs n, u8a d -> (0 < n -> 0 <= sofs /\ sofs + n <= arr_len a) -> u8a a -> u8a (arr_blit d dofs a sofs n).
Proof.
  intros d dofs a sofs n Hd Hr Ha j Hj. rewrite arr_len_blit in Hj. rewrite arr_get_blit.
  destruct ((dofs <=? j) && (j <? dofs + Z.max 0 n) && arr_inb d j) eqn:E; [| exact (Hd j Hj)].
  rewrite !Bool.andb_true_iff, Z.leb_le, Z.ltb_lt in E. destruct E as [[E1 E2] _].
  apply Ha. specialize (Hr ltac:(lia)). lia.
Qed.
Lemma u8a_upd : forall a o l, u8a a -> Forall (fun b => 0 <= b < 256) l -> u8a (arr_upd a o l).
Proof.
  intros a o l Ha Hl j Hj. rewrite arr_len_upd in Hj. rewrite (arr_get_upd l a o j 0).
  destruct ((o <=? j) && (j <? o + zlength l) && arr_inb a j) eqn:E; [| exact (Ha j Hj)].
  rewrite !Bool.andb_true_iff, Z.leb_le, Z.ltb_lt in E. destruct E as [[E1 E2] _].
  apply (proj1 (Forall_nth _ _) Hl). unfold zlength in E2. lia.
Qed.
Lemma u8a_slice : forall a o n, u8a a -> (0 < n -> 0 <= o /\ o + n <= arr_len a) -> Forall (fun b => 0 <= b < 256) (arr_slice a o n).
Proof.
  intros a o n Ha Hr. apply Forall_nth. intros i d Hi.
  unfold arr_slice in *. rewrite arr_slice_nat_length in Hi. rewrite arr_slice_nat_nth by exact Hi.
  apply Ha. specialize (Hr ltac:(lia)). lia.
Qed.

Local Ltac ctyset H := destruct H; constructor; cbn; try assumption.

Lemma cty_K : forall s s', cty s ->
  ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s -> ds_dyn_ltree_dl s' = ds_dyn_ltree_dl s ->
  ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s -> ds_dyn_dtree_dl s' = ds_dyn_dtree_dl s ->
  ds_bl_tree_fc s' = ds_bl_tree_fc s -> ds_bl_tree_dl s' = ds_bl_tree_dl s ->
  ds_bl_count s' = ds_bl_count s -> ds_depth s' = ds_depth s -> ds_pending_buf s' = ds_pending_buf s ->
  ds_window s' = ds_window s -> ds_prev s' = ds_prev s -> ds_head s' = ds_head s -> cs_input (ds_strm s') = cs_input (ds_strm s) ->
  cty s'.
Proof. intros s s' H E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13. destruct H; constructor; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9, ?E10, ?E11, ?E12, ?E13; assumption. Qed.

Local Ltac cty_triv := let s := fresh "s" in intro s; intros; eapply cty_K; [eassumption | destruct s; reflexivity ..].
Lemma cty_set_pending : forall s v, cty s -> cty (set_pending s v). Proof. cty_triv. Qed.
Lemma cty_set_heap_len : forall s v, cty s -> cty (set_heap_len s v). Proof. cty_triv. Qed.
Lemma cty_set_heap_max : forall s v, cty s -> cty (set_heap_max s v). Proof. cty_triv. Qed.
Lemma cty_set_opt_len : forall s v, cty s -> cty (set_opt_len s v). Proof. cty_triv. Qed.
Lemma cty_set_static_len : forall s v, cty s -> cty (set_static_len s v). Proof. cty_triv. Qed.
Lemma cty_set_bi_buf : forall s v, cty s -> cty (set_bi_buf s v). Proof. cty_triv. Qed.
Lemma cty_set_bi_valid : forall s v, cty s -> cty (set_bi_valid s v). Proof. cty_triv. Qed.
Lemma cty_set_max_code : forall s t v, cty s -> cty (set_max_code s t v). Proof. intros s [| |] v H; cbn [set_max_code]; (eapply cty_K; [exact H | destruct s; reflexivity ..]). Qed.
Lemma cty_set_heap : forall s a, cty s -> cty (set_heap s a). Proof. cty_triv. Qed.
Lemma cty_set_sym_next : forall s v, cty s -> cty (set_sym_next s v). Proof. cty_triv. Qed.
Lemma cty_set_matches : forall s v, cty s -> cty (set_matches s v). Proof. cty_triv. Qed.
Lemma cty_set_strm_dt : forall s v, cty s -> cty (set_strm s (cset_data_type (ds_strm s) v)).
Proof. intros s v H; eapply cty_K; [exact H | destruct s; cbn; try reflexivity ..]. all: destruct ds_strm; reflexivity. Qed.
Lemma cty_set_ins_h : forall s v, cty s -> cty (set_ins_h s v). Proof. cty_triv. Qed.
Lemma cty_set_strstart : forall s v, cty s -> cty (set_strstart s v). Proof. cty_triv. Qed.
Lemma cty_set_lookahead : forall s v, cty s -> cty (set_lookahead s v). Proof. cty_triv. Qed.
Lemma cty_set_match_length : forall s v, cty s -> cty (set_match_length s v). Proof. cty_triv. Qed.
Lemma cty_set_match_start : forall s v, cty s -> cty (set_match_start s v). Proof. cty_triv. Qed.
Lemma cty_set_prev_length : forall s v, cty s -> cty (set_prev_length s v). Proof. cty_triv. Qed.
Lemma cty_set_prev_match : forall s v, cty s -> cty (set_prev_match s v). Proof. cty_triv. Qed.
Lemma cty_set_match_available : forall s v, cty s -> cty (set_match_available s v). Proof. cty_triv. Qed.
Lemma cty_set_insert : forall s v, cty s -> cty (set_insert s v). Proof. cty_triv. Qed.
Lemma cty_set_block_start : forall s v, cty s -> cty (set_block_start s v). Proof. cty_triv. Qed.
Lemma cty_set_high_water : forall s v, cty s -> cty (set_high_water s v). Proof. cty_triv. Qed.
Lemma cty_set_pending_out : forall s v, cty s -> cty (set_pending_out s v). Proof. cty_triv. Qed.
Lemma cty_set_last_flush : forall s v, cty s -> cty (set_last_flush s v). Proof. cty_triv. Qed.
Lemma cty_set_status : forall s v, cty s -> cty (set_status s v). Proof. cty_triv. Qed.
Lemma cty_set_wrap : forall s v, cty s -> cty (set_wrap s v). Proof. cty_triv. Qed.
Lemma cty_set_gzindex : forall s v, cty s -> cty (set_gzindex s v). Proof. cty_triv. Qed.

Lemma cty_set_pending_buf : forall s a, cty s -> u8a a -> cty (set_pending_buf s a).
Proof. intros s a H Ha; ctyset H. Qed.
Lemma cty_set_window : forall s a, cty s -> u8a a -> cty (set_window s a).
Proof. intros s a H Ha; ctyset H. Qed.
Lemma cty_set_prev : forall s a, cty s -> u16a a -> cty (set_prev s a).
Proof. intros s a H Ha; ctyset H. Qed.
Lemma cty_set_head : forall s a, cty s -> u16a a -> cty (set_head s a).
Proof. intros s a H Ha; ctyset H. Qed.
Lemma cty_set_tree_fc : forall s t a, cty s -> u16a a -> cty (set_tree_fc s t a).
Proof. intros s [| |] a H Ha; cbn [set_tree_fc]; ctyset H. Qed.
Lemma cty_set_tree_dl : forall s t a, cty s -> u16a a -> cty (set_tree_dl s t a).
Proof. intros s [| |] a H Ha; cbn [set_tree_dl]; ctyset H. Qed.
Lemma cty_tree_fc : forall s t, cty s -> u16a (tree_fc s t).
Proof. intros s [| |] H; cbn; destruct H; assumption. Qed.
Lemma cty_tree_dl : forall s t, cty s -> u16a (tree_dl s t).
Proof. intros s [| |] H; cbn; destruct H; assumption. Qed.
Lemma cty_set_Freq : forall s t n v, cty s -> cty (set_Freq s t n v).
Proof. intros. unfold set_Freq. apply cty_set_tree_fc; [assumption|]. apply u16a_setw. apply cty_tree_fc. assumption. Qed.
Lemma cty_set_Code : forall s t n v, cty s -> cty (set_Code s t n v).
Proof. exact cty_set_Freq. Qed.
Lemma cty_set_Dad : forall s t n v, cty s -> cty (set_Dad s t n v).
Proof. intros. unfold set_Dad. apply cty_set_tree_dl; [assumption|]. apply u16a_setw. apply cty_tree_dl. assumption. Qed.
Lemma cty_set_Len : forall s t n v, cty s -> cty (set_Len s t n v).
Proof. exact cty_set_Dad. Qed.
Lemma cty_heap_set : forall s i v, cty s -> cty (heap_set s i v).
Proof. intros. unfold heap_set. apply cty_set_heap. assumption. Qed.
Lemma cty_depth_set : forall s i v, cty s -> cty (depth_set s i v).
Proof. intros s i v H. unfold depth_set. ctyset H. apply u8a_setw. assumption. Qed.
Lemma cty_bl_count_set : forall s i v, cty s -> cty (bl_count_set s i v).
Proof. intros s i v H. unfold bl_count_set. ctyset H. apply u16a_setw. assumption. Qed.
Lemma cty_put_byte : forall s c, cty s -> cty (put_byte s c).
Proof. intros s c H. unfold put_byte. apply cty_set_pending. ctyset H. apply u8a_setw. assumption. Qed.
Lemma cty_sym_buf_set : forall s i v, cty s -> cty (sym_buf_set s i v).
Proof. intros s i v H. unfold sym_buf_set. ctyset H. apply u8a_setw. assumption. Qed.

Create HintDb cty.
Hint Resolve cty_set_pending cty_set_heap_len cty_set_heap_max cty_set_opt_len cty_set_static_len cty_set_bi_buf cty_set_bi_valid
  cty_set_max_code cty_set_heap cty_set_sym_next cty_set_matches cty_set_strm_dt
  cty_set_ins_h cty_set_strstart cty_set_lookahead cty_set_match_length cty_set_match_start cty_set_prev_length cty_set_prev_match
  cty_set_match_available cty_set_insert cty_set_block_start cty_set_high_water cty_set_pending_out cty_set_last_flush cty_set_status
  cty_set_wrap cty_set_gzindex
  cty_set_Freq cty_set_Code cty_set_Dad cty_set_Len cty_heap_set cty_depth_set cty_bl_count_set cty_put_byte cty_sym_buf_set : cty.
Local Ltac ct := auto 30 with cty.

Lemma cty_put_short : forall s w, cty s -> cty (put_short s w). Proof. intros. unfold put_short. ct. Qed.
Hint Resolve cty_put_short : cty.
Lemma cty_bi_flush : forall s, cty s -> cty (bi_flush s).
Proof. intros s H. unfold bi_flush. destruct (ds_bi_valid s =? 16); [ct|]. destruct (8 <=? ds_bi_valid s); ct. Qed.
Lemma cty_bi_windup : forall s, cty s -> cty (bi_windup s).
Proof. intros s H. unfold bi_windup. destruct (8 <? ds_bi_valid s); [ct|]. destruct (0 <? ds_bi_valid s); ct. Qed.
Lemma cty_send_bits : forall s v l, cty s -> cty (send_bits s v l).
Proof. intros s v l H. unfold send_bits. destruct (Buf_size - l <? ds_bi_valid s); ct. Qed.
Hint Resolve cty_bi_flush cty_bi_windup cty_send_bits : cty.
Lemma cty_send_code : forall s c tfc tdl, cty s -> cty (send_code s c tfc tdl). Proof. intros. unfold send_code. ct. Qed.
Lemma cty_send_dcode : forall s c t, cty s -> cty (send_dcode s c t). Proof. intros. unfold send_dcode. ct. Qed.
Lemma cty_tr_flush_bits : forall s, cty s -> cty (tr_flush_bits s). Proof. exact cty_bi_flush. Qed.
Hint Resolve cty_send_code cty_send_dcode cty_tr_flush_bits : cty.
Lemma cty_tr_align : forall s, cty s -> cty (tr_align s). Proof. intros. unfold tr_align. ct. Qed.
Lemma cty_putShortMSB : forall s b, cty s -> cty (putShortMSB s b). Proof. intros. unfold putShortMSB. ct. Qed.
Hint Resolve cty_tr_align cty_putShortMSB : cty.

Lemma cty_pqdownheap_loop : forall f s t v k j, cty s -> cty (fst (pqdownheap_loop f s t v k j)).
Proof.
  induction f as [|f IH]; intros s t v k j H; cbn [pqdownheap_loop fst]; [exact H|].
  destruct (j <=? ds_heap_len s); [| exact H]. destruct (smaller s t v _); [exact H|]. apply IH. ct.
Qed.
Lemma cty_pqdownheap : forall s t k, cty s -> cty (pqdownheap s t k).
Proof.
  intros s t k H. unfold pqdownheap.
  destruct (pqdownheap_loop 32 s t (heap_get s k) k (Z.shiftl k 1)) as [s1 k1] eqn:E.
  pose proof (cty_pqdownheap_loop 32 s t (heap_get s k) k (Z.shiftl k 1) H) as C. rewrite E in C. cbn [fst] in C. ct.
Qed.
Hint Resolve cty_pqdownheap : cty.
Lemma cty_gen_bitlen_loop1 : forall f s t mc base ml h ov, cty s -> cty (fst (gen_bitlen_loop1 f s t mc base ml h ov)).
Proof.
  induction f as [|f IH]; intros s t mc base ml h ov H; cbn [gen_bitlen_loop1 fst]; [exact H|].
  destruct (h <? HEAP_SIZE); [| exact H].
  destruct (ml <? Len s t (Dad s t (heap_get s h)) + 1); (destruct (mc <? heap_get s h); [apply IH; ct|]); apply IH; destruct (stree_has t); ct.
Qed.
Lemma cty_gen_bitlen_loop2 : forall f s ml ov, cty s -> cty (gen_bitlen_loop2 f s ml ov).
Proof.
  induction f as [|f IH]; intros s ml ov H; cbn [gen_bitlen_loop2]; [exact H|].
  destruct (0 <? ov - 2); [apply IH|]; ct.
Qed.
Lemma cty_gen_bitlen_loop3i : forall f s t mc bits n h, cty s -> cty (fst (gen_bitlen_loop3i f s t mc bits n h)).
Proof.
  induction f as [|f IH]; intros s t mc bits n h H; cbn [gen_bitlen_loop3i fst]; [exact H|].
  destruct (negb (n =? 0)); [| exact H].
  destruct (mc <? heap_get s (h - 1)); [apply IH; exact H|].
  apply IH. destruct (negb (Len s t (heap_get s (h - 1)) =? bits)); ct.
Qed.
Lemma cty_gen_bitlen_loop3 : forall f s t mc bits h, cty s -> cty (gen_bitlen_loop3 f s t mc bits h).
Proof.
  induction f as [|f IH]; intros s t mc bits h H; cbn [gen_bitlen_loop3]; [exact H|].
  destruct (negb (bits =? 0)); [| exact H].
  destruct (gen_bitlen_loop3i 574 s t mc bits (bl_count_get s bits) h) as [s1 h1] eqn:E.
  apply IH. pose proof (cty_gen_bitlen_loop3i 574 s t mc bits (bl_count_get s bits) h H) as C. rewrite E in C. exact C.
Qed.
Lemma cty_gen_bitlen : forall s t, cty s -> cty (gen_bitlen s t).
Proof.
  intros s t H. unfold gen_bitlen.
  match goal with |- context [gen_bitlen_loop1 ?f ?s1 ?t1 ?a ?b ?c ?d ?e] =>
    destruct (gen_bitlen_loop1 f s1 t1 a b c d e) as [s2 ov] eqn:E;
    pose proof (cty_gen_bitlen_loop1 f s1 t1 a b c d e) as C; rewrite E in C; cbn [fst] in C end.
  assert (C2 : cty s2).
  { apply C. apply cty_set_Len. destruct H; constructor; cbn; try assumption. apply u16a_fill; [assumption | lia]. }
  destruct (ov =? 0); [exact C2|]. apply cty_gen_bitlen_loop3, cty_gen_bitlen_loop2. exact C2.
Qed.
Lemma cty_gen_codes_loop2 : forall f s t nc mc n, cty s -> cty (gen_codes_loop2 f s t nc mc n).
Proof.
  induction f as [|f IH]; intros s t nc mc n H; cbn [gen_codes_loop2]; [exact H|].
  destruct (n <=? mc); [| exact H]. destruct (Len s t n =? 0); apply IH; ct.
Qed.
Lemma cty_gen_codes : forall s t mc, cty s -> cty (gen_codes s t mc).
Proof. intros. unfold gen_codes. apply cty_gen_codes_loop2. assumption. Qed.
Hint Resolve cty_gen_bitlen cty_gen_codes : cty.

Lemma cty_build_tree_loop1 : forall f s t el n mc, cty s -> cty (fst (build_tree_loop1 f s t el n mc)).
Proof.
  induction f as [|f IH]; intros s t el n mc H; cbn [build_tree_loop1 fst]; [exact H|].
  destruct (n <? el); [| exact H]. destruct (negb (Freq s t n =? 0)); apply IH; ct.
Qed.
Lemma cty_build_tree_loop2 : forall f s t mc, cty s -> cty (fst (build_tree_loop2 f s t mc)).
Proof.
  induction f as [|f IH]; intros s t mc H; cbn [build_tree_loop2 fst]; [exact H|].
  destruct (ds_heap_len s <? 2); [| exact H]. destruct (mc <? 2); apply IH; destruct (stree_has t); ct.
Qed.
Lemma cty_build_tree_loop3 : forall f s t n, cty s -> cty (build_tree_loop3 f s t n).
Proof.
  induction f as [|f IH]; intros s t n H; cbn [build_tree_loop3]; [exact H|].
  destruct (1 <=? n); [apply IH; ct | exact H].
Qed.
Lemma cty_build_tree_loop4 : forall f s t node, cty s -> cty (build_tree_loop4 f s t node).
Proof.
  induction f as [|f IH]; intros s t node H; cbn [build_tree_loop4]; [exact H|].
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply IH|]; ct.
Qed.
Lemma cty_build_tree : forall s t, cty s -> cty (build_tree s t).
Proof.
  intros s t H. unfold build_tree.
  match goal with |- context [build_tree_loop1 ?f ?s1 ?t1 ?a ?b ?c] =>
    destruct (build_tree_loop1 f s1 t1 a b c) as [s2 mc2] eqn:E1;
    pose proof (cty_build_tree_loop1 f s1 t1 a b c) as C1; rewrite E1 in C1; cbn [fst] in C1 end.
  specialize (C1 ltac:(ct)).
  destruct (build_tree_loop2 2 s2 t mc2) as [s3 mc3] eqn:E2.
  pose proof (cty_build_tree_loop2 2 s2 t mc2 C1) as C2. rewrite E2 in C2. cbn [fst] in C2.
  apply cty_gen_codes, cty_gen_bitlen, cty_heap_set, cty_set_heap_max, cty_build_tree_loop4, cty_build_tree_loop3, cty_set_max_code. exact C2.
Qed.
Hint Resolve cty_build_tree : cty.

Lemma cty_scan_tree_loop : forall f s t mc n pl nl c mx mn, cty s -> cty (scan_tree_loop f s t mc n pl nl c mx mn).
Proof.
  induction f as [|f IH]; intros s t mc n pl nl c mx mn H; cbn [scan_tree_loop]; [exact H|].
  destruct (n <=? mc); [| exact H].
  destruct ((c + 1 <? mx) && (nl =? Len s t (n + 1))); [apply IH; exact H|].
  destruct (tree_counts nl (Len s t (n + 1))) as [mx' mn']. apply IH.
  destruct (c + 1 <? mn); [ct|]. destruct (negb (nl =? 0)); [| destruct (c + 1 <=? 10); ct].
  destruct (negb (nl =? pl)); ct.
Qed.
Lemma cty_scan_tree : forall s t mc, cty s -> cty (scan_tree s t mc).
Proof. intros s t mc H. unfold scan_tree. destruct (Len s t 0 =? 0); apply cty_scan_tree_loop; ct. Qed.
Lemma cty_send_tree_rep : forall f s cl c, cty s -> cty (send_tree_rep f s cl c).
Proof.
  induction f as [|f IH]; intros s cl c H; cbn [send_tree_rep]; [exact H|].
  destruct (negb (c - 1 =? 0)); [apply IH|]; ct.
Qed.
Lemma cty_send_tree_loop : forall f s t mc n pl nl c mx mn, cty s -> cty (send_tree_loop f s t mc n pl nl c mx mn).
Proof.
  induction f as [|f IH]; intros s t mc n pl nl c mx mn H; cbn [send_tree_loop]; [exact H|].
  destruct (n <=? mc); [| exact H].
  destruct ((c + 1 <? mx) && (nl =? Len s t (n + 1))); [apply IH; exact H|].
  destruct (tree_counts nl (Len s t (n + 1))) as [mx' mn']. apply IH.
  destruct (c + 1 <? mn); [apply cty_send_tree_rep; exact H|].
  destruct (negb (nl =? 0)); [destruct (negb (nl =? pl)); ct | destruct (c + 1 <=? 10); ct].
Qed.
Lemma cty_send_tree : forall s t mc, cty s -> cty (send_tree s t mc).
Proof. intros s t mc H. unfold send_tree. destruct (Len s t 0 =? 0); apply cty_send_tree_loop; exact H. Qed.
Hint Resolve cty_scan_tree cty_send_tree : cty.
Lemma cty_build_bl_tree : forall s, cty s -> cty (fst (build_bl_tree s)).
Proof. intros s H. unfold build_bl_tree. cbn [fst]. ct. Qed.
Lemma cty_send_all_trees_loop : forall f s bl r, cty s -> cty (send_all_trees_loop f s bl r).
Proof.
  induction f as [|f IH]; intros s bl r H; cbn [send_all_trees_loop]; [exact H|].
  destruct (r <? bl); [apply IH; ct | exact H].
Qed.
Lemma cty_send_all_trees : forall s lc dc bc, cty s -> cty (send_all_trees s lc dc bc).
Proof. intros. unfold send_all_trees. apply cty_send_tree, cty_send_tree, cty_send_all_trees_loop. ct. Qed.
Hint Resolve cty_send_all_trees : cty.

Definition buf_ok (s : deflate_state) (buf : option Z) (len : Z) : Prop :=
  forall off, buf = Some off -> 0 < len -> 0 <= off /\ off + len <= arr_len (ds_window s).

Lemma cty_tr_stored_block : forall s buf len last, cty s -> buf_ok s buf len -> cty (tr_stored_block s buf len last).
Proof.
  intros s buf len last H Hb. unfold tr_stored_block. apply cty_set_pending.
  set (s1 := put_short (put_short (bi_windup (send_bits s (Z.shiftl STORED_BLOCK 1 + last) 3)) (wrap16 len)) (wrap16 (Z.lnot len))).
  assert (C1 : cty s1) by (subst s1; ct).
  assert (W1 : ds_window s1 = ds_window s) by (apply (kp_window s s1); subst s1; kp).
  destruct (negb (len =? 0)); [| exact C1]. destruct buf as [off|]; [| exact C1].
  apply cty_set_pending_buf; [exact C1|]. apply u8a_blit; [exact (ct_pb _ C1) | | rewrite W1; exact (ct_win _ H)].
  intros Hn. rewrite W1. exact (Hb off eq_refl Hn).
Qed.

Lemma cty_compress_block_sym : forall s lfc ldl dfc ddl sx, cty s -> cty (fst (compress_block_sym s lfc ldl dfc ddl sx)).
Proof.
  intros s lfc ldl dfc ddl sx H. unfold compress_block_sym.
  destruct (_ =? 0); cbn [fst]; [ct|].
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst]; ct.
Qed.
Lemma cty_compress_block_loop : forall f s lfc ldl dfc ddl sx, cty s -> cty (compress_block_loop f s lfc ldl dfc ddl sx).
Proof.
  induction f as [|f IH]; intros s lfc ldl dfc ddl sx H; cbn [compress_block_loop]; [exact H|].
  destruct (compress_block_sym s lfc ldl dfc ddl sx) as [s1 sx1] eqn:E.
  pose proof (cty_compress_block_sym s lfc ldl dfc ddl sx H) as C. rewrite E in C. cbn [fst] in C.
  destruct (sx1 <? ds_sym_next s1); [apply IH|]; exact C.
Qed.
Lemma cty_compress_block : forall s lfc ldl dfc ddl, cty s -> cty (compress_block s lfc ldl dfc ddl).
Proof.
  intros s lfc ldl dfc ddl H. unfold compress_block. apply cty_send_code.
  destruct (negb (ds_sym_next s =? 0)); [apply cty_compress_block_loop|]; exact H.
Qed.
Hint Resolve cty_compress_block : cty.

Lemma cty_init_block : forall s, cty s -> cty (init_block s).
Proof.
  intros s H. unfold init_block. apply cty_set_matches, cty_set_sym_next, cty_set_static_len, cty_set_opt_len, cty_set_Freq.
  destruct H; constructor; cbn; try assumption; apply u16a_fill; try assumption; lia.
Qed.
Lemma cty_tr_init : forall s, cty s -> cty (tr_init s).
Proof. intros s H. unfold tr_init. apply cty_init_block. ct. Qed.
Hint Resolve cty_init_block cty_tr_init : cty.

Lemma cty_tr_flush_block : forall s buf len last, cty s -> buf_ok s buf len -> cty (tr_flush_block s buf len last).
Proof.
  intros s buf len last H Hb. unfold tr_flush_block.
  set (s1 := if cs_data_type (ds_strm s) =? Z_UNKNOWN then set_strm s (cset_data_type (ds_strm s) (detect_data_type s)) else s).
  assert (C1 : cty s1) by (subst s1; destruct (cs_data_type (ds_strm s) =? Z_UNKNOWN); ct).
  assert (W1 : ds_window s1 = ds_window s) by (subst s1; destruct (cs_data_type (ds_strm s) =? Z_UNKNOWN); destruct s; reflexivity).
  assert (TAIL : forall a, cty a -> cty (if negb (last =? 0) then bi_windup (init_block a) else init_block a)).
  { intros a Ha. destruct (negb (last =? 0)); ct. }
  destruct (0 <? ds_level s).
  - destruct (build_bl_tree (build_tree (build_tree s1 TL) TD)) as [s4 mb] eqn:E4.
    pose proof (cty_build_bl_tree (build_tree (build_tree s1 TL) TD) ltac:(ct)) as C4. rewrite E4 in C4. cbn [fst] in C4.
    pose proof (kp_build_bl_tree (build_tree (build_tree s1 TL) TD)) as K4. rewrite E4 in K4. cbn [fst] in K4. rewrite !kp_build_tree in K4.
    assert (W4 : ds_window s4 = ds_window s) by (rewrite <- W1; exact (kp_window _ _ K4)).
    cbv beta iota zeta. apply TAIL.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; try solve [ct].
    apply cty_tr_stored_block; [exact C4|]. intros off Ho Hn. rewrite W4. exact (Hb off Ho Hn).
  - cbv beta iota zeta. apply TAIL.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; try solve [ct].
    apply cty_tr_stored_block; [exact H | exact Hb].
Qed.

Lemma cty_tr_tally_lit : forall s c, cty s -> cty (fst (tr_tally_lit s c)).
Proof. intros s c H. unfold tr_tally_lit. cbn [fst]. ct. Qed.
Lemma cty_tr_tally_dist : forall s d l, cty s -> cty (fst (tr_tally_dist s d l)).
Proof. intros s d l H. unfold tr_tally_dist. cbn [fst]. ct. Qed.


Lemma land_mask_range : forall y m, 0 <= m -> 0 <= Z.land y m <= m.
Proof.
  intros y m Hm. split; [apply Z.land_nonneg; right; exact Hm|].
  destruct (Z.eq_dec m 0) as [->|Hm0]; [rewrite Z.land_0_r; lia|].
  pose proof (Z.add_nocarry_lxor (Z.land y m) (Z.ldiff m y)) as E.
  assert (D : Z.land (Z.land y m) (Z.ldiff m y) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.land_spec, Z.ldiff_spec, Z.bits_0.
    destruct (Z.testbit y n), (Z.testbit m n); reflexivity. }
  specialize (E D).
  assert (X : Z.lxor (Z.land y m) (Z.ldiff m y) = m).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.land_spec, Z.ldiff_spec.
    destruct (Z.testbit y n), (Z.testbit m n); reflexivity. }
  rewrite X in E. pose proof (Z.ldiff_nonneg m y) as Hl. lia.
Qed.

Lemma update_hash_lt : forall s h c, 0 <= ds_hash_mask s < arr_len (ds_head s) -> 0 <= update_hash s h c < arr_len (ds_head s).
Proof. intros s h c Hm. unfold update_hash. pose proof (land_mask_range (Z.lxor (wrap32 (Z.shiftl h (ds_hash_shift s))) c) _ (proj1 Hm)). lia. Qed.

Lemma cty_insert_string : forall s str, cty s -> 0 <= ds_hash_mask s < arr_len (ds_head s) -> cty (fst (insert_string s str)).
Proof.
  intros s str H Hm. unfold insert_string. cbn [fst].
  apply cty_set_head; [apply cty_set_prev; [ct|]|].
  - cbn. apply u16a_set; [exact (ct_prev _ H)|]. apply (ct_head _ H). cbn. apply update_hash_lt. exact Hm.
  - cbn. apply u16a_setw. exact (ct_head _ H).
Qed.

Lemma u16a_slide_hash_loop : forall f a n ws, u16a a -> u16a (slide_hash_loop f a n ws).
Proof.
  induction f as [|f IH]; intros a n ws H; cbn [slide_hash_loop]; [exact H|].
  destruct (negb (n - 1 =? 0)); [apply IH|]; apply u16a_setw; exact H.
Qed.
Lemma cty_slide_hash : forall s, cty s -> cty (slide_hash s).
Proof.
  intros s H. unfold slide_hash. apply cty_set_prev; [apply cty_set_head; [exact H|]|]; cbn; apply u16a_slide_hash_loop; [exact (ct_head _ H) | exact (ct_prev _ H)].
Qed.
Lemma cty_clear_hash : forall s, cty s -> cty (clear_hash s).
Proof.
  intros s H. unfold clear_hash. apply cty_set_head; [apply cty_set_head; [exact H|]|]; cbn.
  - apply u16a_set; [exact (ct_head _ H) | unfold NIL; lia].
  - apply u16a_fill; [| lia]. apply u16a_set; [exact (ct_head _ H) | unfold NIL; lia].
Qed.

Lemma cty_set_strm_in : forall s st, cty s -> cs_input st = cs_input (ds_strm s) -> cty (set_strm s st).
Proof. intros s st H E. eapply cty_K; [exact H | destruct s; try reflexivity ..]. exact E. Qed.



Lemma cty_flush_pending : forall s, cty s -> cty (flush_pending s).
Proof.
  intros s H. unfold flush_pending.
  assert (C1 : cty (tr_flush_bits s)) by ct.
  destruct (_ =? 0); [exact C1|].
  match goal with |- cty (if ?c then set_pending_out ?x 0 else ?x') => assert (C : cty x) end.
  { apply cty_set_pending, cty_set_strm_in; [apply cty_set_pending_out; exact C1|]. cbn. destruct (tr_flush_bits s); cbn; destruct ds_strm; reflexivity. }
  destruct (_ =? 0); [apply cty_set_pending_out|]; exact C.
Qed.
Hint Resolve cty_slide_hash cty_clear_hash cty_flush_pending : cty.

Definition ezap (s : deflate_state) : deflate_state := set_bi_valid (set_bi_buf (set_pending (set_pending_buf s arr0) 0) 0) 0.
Definition eproj (s : deflate_state) : deflate_state * Z := (ezap s, arr_len (ds_pending_buf s)).

Definition ep_to_kp (q : deflate_state * Z) : deflate_state * list Z :=
  (kzap (fst q), [snd q; arr_len (ds_dyn_ltree_fc (fst q)); arr_len (ds_dyn_ltree_dl (fst q)); arr_len (ds_dyn_dtree_fc (fst q));
                 arr_len (ds_dyn_dtree_dl (fst q)); arr_len (ds_bl_tree_fc (fst q)); arr_len (ds_bl_tree_dl (fst q));
                 arr_len (ds_bl_count (fst q)); arr_len (ds_heap (fst q)); arr_len (ds_depth (fst q))]).
Lemma kproj_eproj : forall s, kproj s = ep_to_kp (eproj s).
Proof. intros s. destruct s. reflexivity. Qed.
Lemma ep_kp : forall s s', eproj s' = eproj s -> kproj s' = kproj s.
Proof. intros s s' H. rewrite !kproj_eproj, H. reflexivity. Qed.
Lemma ep_status : forall s s', eproj s' = eproj s -> ds_status s' = ds_status s.
Proof. intros s s' H. apply (f_equal (fun q => ds_status (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_pending_out : forall s s', eproj s' = eproj s -> ds_pending_out s' = ds_pending_out s.
Proof. intros s s' H. apply (f_equal (fun q => ds_pending_out (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_wrap : forall s s', eproj s' = eproj s -> ds_wrap s' = ds_wrap s.
Proof. intros s s' H. apply (f_equal (fun q => ds_wrap (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_last_flush : forall s s', eproj s' = eproj s -> ds_last_flush s' = ds_last_flush s.
Proof. intros s s' H. apply (f_equal (fun q => ds_last_flush (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_w_size : forall s s', eproj s' = eproj s -> ds_w_size s' = ds_w_size s.
Proof. intros s s' H. apply (f_equal (fun q => ds_w_size (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_window : forall s s', eproj s' = eproj s -> ds_window s' = ds_window s.
Proof. intros s s' H. apply (f_equal (fun q => ds_window (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_prev : forall s s', eproj s' = eproj s -> ds_prev s' = ds_prev s.
Proof. intros s s' H. apply (f_equal (fun q => ds_prev (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_head : forall s s', eproj s' = eproj s -> ds_head s' = ds_head s.
Proof. intros s s' H. apply (f_equal (fun q => ds_head (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_ins_h : forall s s', eproj s' = eproj s -> ds_ins_h s' = ds_ins_h s.
Proof. intros s s' H. apply (f_equal (fun q => ds_ins_h (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_hash_size : forall s s', eproj s' = eproj s -> ds_hash_size s' = ds_hash_size s.
Proof. intros s s' H. apply (f_equal (fun q => ds_hash_size (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_block_start : forall s s', eproj s' = eproj s -> ds_block_start s' = ds_block_start s.
Proof. intros s s' H. apply (f_equal (fun q => ds_block_start (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_match_length : forall s s', eproj s' = eproj s -> ds_match_length s' = ds_match_length s.
Proof. intros s s' H. apply (f_equal (fun q => ds_match_length (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_prev_match : forall s s', eproj s' = eproj s -> ds_prev_match s' = ds_prev_match s.
Proof. intros s s' H. apply (f_equal (fun q => ds_prev_match (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_match_available : forall s s', eproj s' = eproj s -> ds_match_available s' = ds_match_available s.
Proof. intros s s' H. apply (f_equal (fun q => ds_match_available (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_strstart : forall s s', eproj s' = eproj s -> ds_strstart s' = ds_strstart s.
Proof. intros s s' H. apply (f_equal (fun q => ds_strstart (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_match_start : forall s s', eproj s' = eproj s -> ds_match_start s' = ds_match_start s.
Proof. intros s s' H. apply (f_equal (fun q => ds_match_start (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_lookahead : forall s s', eproj s' = eproj s -> ds_lookahead s' = ds_lookahead s.
Proof. intros s s' H. apply (f_equal (fun q => ds_lookahead (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_prev_length : forall s s', eproj s' = eproj s -> ds_prev_length s' = ds_prev_length s.
Proof. intros s s' H. apply (f_equal (fun q => ds_prev_length (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_level : forall s s', eproj s' = eproj s -> ds_level s' = ds_level s.
Proof. intros s s' H. apply (f_equal (fun q => ds_level (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_strategy : forall s s', eproj s' = eproj s -> ds_strategy s' = ds_strategy s.
Proof. intros s s' H. apply (f_equal (fun q => ds_strategy (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_dyn_ltree_fc : forall s s', eproj s' = eproj s -> ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s.
Proof. intros s s' H. apply (f_equal (fun q => ds_dyn_ltree_fc (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_dyn_ltree_dl : forall s s', eproj s' = eproj s -> ds_dyn_ltree_dl s' = ds_dyn_ltree_dl s.
Proof. intros s s' H. apply (f_equal (fun q => ds_dyn_ltree_dl (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_dyn_dtree_fc : forall s s', eproj s' = eproj s -> ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s.
Proof. intros s s' H. apply (f_equal (fun q => ds_dyn_dtree_fc (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_dyn_dtree_dl : forall s s', eproj s' = eproj s -> ds_dyn_dtree_dl s' = ds_dyn_dtree_dl s.
Proof. intros s s' H. apply (f_equal (fun q => ds_dyn_dtree_dl (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_bl_tree_fc : forall s s', eproj s' = eproj s -> ds_bl_tree_fc s' = ds_bl_tree_fc s.
Proof. intros s s' H. apply (f_equal (fun q => ds_bl_tree_fc (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_bl_tree_dl : forall s s', eproj s' = eproj s -> ds_bl_tree_dl s' = ds_bl_tree_dl s.
Proof. intros s s' H. apply (f_equal (fun q => ds_bl_tree_dl (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_bl_count : forall s s', eproj s' = eproj s -> ds_bl_count s' = ds_bl_count s.
Proof. intros s s' H. apply (f_equal (fun q => ds_bl_count (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_depth : forall s s', eproj s' = eproj s -> ds_depth s' = ds_depth s.
Proof. intros s s' H. apply (f_equal (fun q => ds_depth (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_lit_bufsize : forall s s', eproj s' = eproj s -> ds_lit_bufsize s' = ds_lit_bufsize s.
Proof. intros s s' H. apply (f_equal (fun q => ds_lit_bufsize (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_sym_next : forall s s', eproj s' = eproj s -> ds_sym_next s' = ds_sym_next s.
Proof. intros s s' H. apply (f_equal (fun q => ds_sym_next (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_sym_end : forall s s', eproj s' = eproj s -> ds_sym_end s' = ds_sym_end s.
Proof. intros s s' H. apply (f_equal (fun q => ds_sym_end (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_opt_len : forall s s', eproj s' = eproj s -> ds_opt_len s' = ds_opt_len s.
Proof. intros s s' H. apply (f_equal (fun q => ds_opt_len (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_static_len : forall s s', eproj s' = eproj s -> ds_static_len s' = ds_static_len s.
Proof. intros s s' H. apply (f_equal (fun q => ds_static_len (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_matches : forall s s', eproj s' = eproj s -> ds_matches s' = ds_matches s.
Proof. intros s s' H. apply (f_equal (fun q => ds_matches (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_insert : forall s s', eproj s' = eproj s -> ds_insert s' = ds_insert s.
Proof. intros s s' H. apply (f_equal (fun q => ds_insert (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_high_water : forall s s', eproj s' = eproj s -> ds_high_water s' = ds_high_water s.
Proof. intros s s' H. apply (f_equal (fun q => ds_high_water (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_strm : forall s s', eproj s' = eproj s -> ds_strm s' = ds_strm s.
Proof. intros s s' H. apply (f_equal (fun q => ds_strm (fst q))) in H. destruct s, s'. exact H. Qed.
Lemma ep_len_pending_buf : forall s s', eproj s' = eproj s -> arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s).
Proof. intros s s' H. apply (f_equal snd) in H. exact H. Qed.
Lemma ep_Freq : forall s s' t c, eproj s' = eproj s -> Freq s' t c = Freq s t c.
Proof. intros s s' [| |] c H; unfold Freq; cbn [tree_fc]; [rewrite (ep_dyn_ltree_fc _ _ H) | rewrite (ep_dyn_dtree_fc _ _ H) | rewrite (ep_bl_tree_fc _ _ H)]; reflexivity. Qed.

Lemma ep_set_pending : forall s v, eproj (set_pending s v) = eproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ep_set_bi_buf : forall s v, eproj (set_bi_buf s v) = eproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ep_set_bi_valid : forall s v, eproj (set_bi_valid s v) = eproj s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma ep_set_pending_buf : forall s a, arr_len a = arr_len (ds_pending_buf s) -> eproj (set_pending_buf s a) = eproj s.
Proof. intros s a H. destruct s. unfold eproj. cbn -[arr_len]. cbn -[arr_len] in H. rewrite H. reflexivity. Qed.

Create HintDb ep.
Hint Rewrite ep_set_pending ep_set_bi_buf ep_set_bi_valid : ep.
Local Ltac ep := autorewrite with ep; try reflexivity.

Lemma ep_put_byte : forall s c, eproj (put_byte s c) = eproj s.
Proof. intros. unfold put_byte. rewrite ep_set_pending. apply ep_set_pending_buf. apply arr_len_set. Qed.
Lemma ep_put_short : forall s w, eproj (put_short s w) = eproj s.
Proof. intros. unfold put_short. rewrite !ep_put_byte. reflexivity. Qed.
Hint Rewrite ep_put_byte ep_put_short : ep.
Lemma ep_bi_flush : forall s, eproj (bi_flush s) = eproj s.
Proof. intros s. unfold bi_flush. destruct (ds_bi_valid s =? 16); [| destruct (8 <=? ds_bi_valid s)]; ep. Qed.
Lemma ep_bi_windup : forall s, eproj (bi_windup s) = eproj s.
Proof. intros s. unfold bi_windup. destruct (8 <? ds_bi_valid s); [| destruct (0 <? ds_bi_valid s)]; ep. Qed.
Lemma ep_send_bits : forall s v l, eproj (send_bits s v l) = eproj s.
Proof. intros s v l. unfold send_bits. destruct (Buf_size - l <? ds_bi_valid s); ep. Qed.
Hint Rewrite ep_bi_flush ep_bi_windup ep_send_bits : ep.
Lemma ep_send_code : forall s c tfc tdl, eproj (send_code s c tfc tdl) = eproj s.
Proof. intros. unfold send_code. apply ep_send_bits. Qed.
Lemma ep_send_dcode : forall s c t, eproj (send_dcode s c t) = eproj s.
Proof. intros. unfold send_dcode. apply ep_send_bits. Qed.
Lemma ep_tr_flush_bits : forall s, eproj (tr_flush_bits s) = eproj s.
Proof. exact ep_bi_flush. Qed.
Hint Rewrite ep_send_code ep_send_dcode ep_tr_flush_bits : ep.
Lemma ep_tr_align : forall s, eproj (tr_align s) = eproj s.
Proof. intros s. unfold tr_align. ep. Qed.
Lemma ep_putShortMSB : forall s b, eproj (putShortMSB s b) = eproj s.
Proof. intros. unfold putShortMSB. ep. Qed.
Hint Rewrite ep_tr_align ep_putShortMSB : ep.
Lemma ep_tr_stored_block : forall s buf len last, eproj (tr_stored_block s buf len last) = eproj s.
Proof.
  intros s buf len last. unfold tr_stored_block. rewrite ep_set_pending.
  assert (X : forall s1, eproj (if negb (len =? 0) then match buf with Some off => set_pending_buf s1 (arr_blit (ds_pending_buf s1) (ds_pending s1) (ds_window s1) off len) | None => s1 end else s1) = eproj s1).
  { intros s1. destruct (negb (len =? 0)); [| reflexivity]. destruct buf; [| reflexivity]. apply ep_set_pending_buf. apply arr_len_blit. }
  rewrite X. ep.
Qed.
Hint Rewrite ep_tr_stored_block : ep.
Lemma ep_send_tree_rep : forall f s cl c, eproj (send_tree_rep f s cl c) = eproj s.
Proof.
  induction f as [|f IH]; intros s cl c; cbn [send_tree_rep]; [reflexivity|].
  destruct (negb (c - 1 =? 0)); rewrite ?IH; apply ep_send_dcode.
Qed.
Hint Rewrite ep_send_tree_rep : ep.
Lemma ep_send_tree_loop : forall f s t mc n pl nl c mx mn, eproj (send_tree_loop f s t mc n pl nl c mx mn) = eproj s.
Proof.
  induction f as [|f IH]; intros s t mc n pl nl c mx mn; cbn [send_tree_loop]; [reflexivity|].
  destruct (n <=? mc); [| reflexivity].
  destruct ((c + 1 <? mx) && (nl =? Len s t (n + 1))); [apply IH|].
  destruct (tree_counts nl (Len s t (n + 1))) as [mx' mn']. rewrite IH.
  destruct (c + 1 <? mn); [apply ep_send_tree_rep|].
  destruct (negb (nl =? 0)); [destruct (negb (nl =? pl)); ep | destruct (c + 1 <=? 10); ep].
Qed.
Lemma ep_send_tree : forall s t mc, eproj (send_tree s t mc) = eproj s.
Proof. intros s t mc. unfold send_tree. destruct (Len s t 0 =? 0); apply ep_send_tree_loop. Qed.
Hint Rewrite ep_send_tree : ep.
Lemma ep_send_all_trees_loop : forall f s bl r, eproj (send_all_trees_loop f s bl r) = eproj s.
Proof.
  induction f as [|f IH]; intros s bl r; cbn [send_all_trees_loop]; [reflexivity|].
  destruct (r <? bl); [| reflexivity]. rewrite IH. apply ep_send_bits.
Qed.
Hint Rewrite ep_send_all_trees_loop : ep.
Lemma ep_send_all_trees : forall s lc dc bc, eproj (send_all_trees s lc dc bc) = eproj s.
Proof. intros. unfold send_all_trees. ep. Qed.
Hint Rewrite ep_send_all_trees : ep.
Lemma ep_compress_block_sym : forall s lfc ldl dfc ddl sx, eproj (fst (compress_block_sym s lfc ldl dfc ddl sx)) = eproj s.
Proof.
  intros. unfold compress_block_sym.
  destruct (_ =? 0); cbn [fst]; [apply ep_send_code|].
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst]; ep.
Qed.
Lemma ep_compress_block_loop : forall f s lfc ldl dfc ddl sx, eproj (compress_block_loop f s lfc ldl dfc ddl sx) = eproj s.
Proof.
  induction f as [|f IH]; intros; cbn [compress_block_loop]; [reflexivity|].
  destruct (compress_block_sym s lfc ldl dfc ddl sx) as [s1 sx1] eqn:E.
  pose proof (ep_compress_block_sym s lfc ldl dfc ddl sx) as K. rewrite E in K. cbn [fst] in K.
  destruct (sx1 <? ds_sym_next s1); [rewrite IH|]; exact K.
Qed.
Lemma ep_compress_block : forall s lfc ldl dfc ddl, eproj (compress_block s lfc ldl dfc ddl) = eproj s.
Proof.
  intros. unfold compress_block. rewrite ep_send_code. destruct (negb (ds_sym_next s =? 0)); [apply ep_compress_block_loop | reflexivity].
Qed.
Hint Rewrite ep_compress_block : ep.
