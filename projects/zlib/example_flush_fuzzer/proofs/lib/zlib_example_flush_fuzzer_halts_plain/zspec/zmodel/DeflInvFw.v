(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz Deflate DeflateInvHash DeflateInvKeep OverlayFBS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import AdlerModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import DeflInvTally.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.


Definition zapin (st : cstrm) : cstrm := cset_next_in (cset_avail_in (cset_adler (cset_total_in st 0) 0) 0) 0.
Definition fwzap (s : deflate_state) : deflate_state := (set_strm (set_high_water (set_lookahead (set_ins_h (set_prev (set_head (set_insert (set_block_start (set_strstart (set_match_start (set_window s arr0) 0) 0) 0) 0) arr0) arr0) 0) 0) 0) (zapin (ds_strm s))).

Lemma fw_status : forall s s', fwzap s' = fwzap s -> ds_status s' = ds_status s.
Proof. intros s s' H. apply (f_equal ds_status) in H. destruct s, s'. exact H. Qed.
Lemma fw_pending_buf : forall s s', fwzap s' = fwzap s -> ds_pending_buf s' = ds_pending_buf s.
Proof. intros s s' H. apply (f_equal ds_pending_buf) in H. destruct s, s'. exact H. Qed.
Lemma fw_pending_buf_size : forall s s', fwzap s' = fwzap s -> ds_pending_buf_size s' = ds_pending_buf_size s.
Proof. intros s s' H. apply (f_equal ds_pending_buf_size) in H. destruct s, s'. exact H. Qed.
Lemma fw_pending_out : forall s s', fwzap s' = fwzap s -> ds_pending_out s' = ds_pending_out s.
Proof. intros s s' H. apply (f_equal ds_pending_out) in H. destruct s, s'. exact H. Qed.
Lemma fw_pending : forall s s', fwzap s' = fwzap s -> ds_pending s' = ds_pending s.
Proof. intros s s' H. apply (f_equal ds_pending) in H. destruct s, s'. exact H. Qed.
Lemma fw_wrap : forall s s', fwzap s' = fwzap s -> ds_wrap s' = ds_wrap s.
Proof. intros s s' H. apply (f_equal ds_wrap) in H. destruct s, s'. exact H. Qed.
Lemma fw_gzhead : forall s s', fwzap s' = fwzap s -> ds_gzhead s' = ds_gzhead s.
Proof. intros s s' H. apply (f_equal ds_gzhead) in H. destruct s, s'. exact H. Qed.
Lemma fw_method : forall s s', fwzap s' = fwzap s -> ds_method s' = ds_method s.
Proof. intros s s' H. apply (f_equal ds_method) in H. destruct s, s'. exact H. Qed.
Lemma fw_last_flush : forall s s', fwzap s' = fwzap s -> ds_last_flush s' = ds_last_flush s.
Proof. intros s s' H. apply (f_equal ds_last_flush) in H. destruct s, s'. exact H. Qed.
Lemma fw_w_size : forall s s', fwzap s' = fwzap s -> ds_w_size s' = ds_w_size s.
Proof. intros s s' H. apply (f_equal ds_w_size) in H. destruct s, s'. exact H. Qed.
Lemma fw_w_bits : forall s s', fwzap s' = fwzap s -> ds_w_bits s' = ds_w_bits s.
Proof. intros s s' H. apply (f_equal ds_w_bits) in H. destruct s, s'. exact H. Qed.
Lemma fw_w_mask : forall s s', fwzap s' = fwzap s -> ds_w_mask s' = ds_w_mask s.
Proof. intros s s' H. apply (f_equal ds_w_mask) in H. destruct s, s'. exact H. Qed.
Lemma fw_window_size : forall s s', fwzap s' = fwzap s -> ds_window_size s' = ds_window_size s.
Proof. intros s s' H. apply (f_equal ds_window_size) in H. destruct s, s'. exact H. Qed.
Lemma fw_hash_size : forall s s', fwzap s' = fwzap s -> ds_hash_size s' = ds_hash_size s.
Proof. intros s s' H. apply (f_equal ds_hash_size) in H. destruct s, s'. exact H. Qed.
Lemma fw_hash_bits : forall s s', fwzap s' = fwzap s -> ds_hash_bits s' = ds_hash_bits s.
Proof. intros s s' H. apply (f_equal ds_hash_bits) in H. destruct s, s'. exact H. Qed.
Lemma fw_hash_mask : forall s s', fwzap s' = fwzap s -> ds_hash_mask s' = ds_hash_mask s.
Proof. intros s s' H. apply (f_equal ds_hash_mask) in H. destruct s, s'. exact H. Qed.
Lemma fw_hash_shift : forall s s', fwzap s' = fwzap s -> ds_hash_shift s' = ds_hash_shift s.
Proof. intros s s' H. apply (f_equal ds_hash_shift) in H. destruct s, s'. exact H. Qed.
Lemma fw_match_length : forall s s', fwzap s' = fwzap s -> ds_match_length s' = ds_match_length s.
Proof. intros s s' H. apply (f_equal ds_match_length) in H. destruct s, s'. exact H. Qed.
Lemma fw_prev_match : forall s s', fwzap s' = fwzap s -> ds_prev_match s' = ds_prev_match s.
Proof. intros s s' H. apply (f_equal ds_prev_match) in H. destruct s, s'. exact H. Qed.
Lemma fw_match_available : forall s s', fwzap s' = fwzap s -> ds_match_available s' = ds_match_available s.
Proof. intros s s' H. apply (f_equal ds_match_available) in H. destruct s, s'. exact H. Qed.
Lemma fw_prev_length : forall s s', fwzap s' = fwzap s -> ds_prev_length s' = ds_prev_length s.
Proof. intros s s' H. apply (f_equal ds_prev_length) in H. destruct s, s'. exact H. Qed.
Lemma fw_max_chain_length : forall s s', fwzap s' = fwzap s -> ds_max_chain_length s' = ds_max_chain_length s.
Proof. intros s s' H. apply (f_equal ds_max_chain_length) in H. destruct s, s'. exact H. Qed.
Lemma fw_max_lazy_match : forall s s', fwzap s' = fwzap s -> ds_max_lazy_match s' = ds_max_lazy_match s.
Proof. intros s s' H. apply (f_equal ds_max_lazy_match) in H. destruct s, s'. exact H. Qed.
Lemma fw_level : forall s s', fwzap s' = fwzap s -> ds_level s' = ds_level s.
Proof. intros s s' H. apply (f_equal ds_level) in H. destruct s, s'. exact H. Qed.
Lemma fw_strategy : forall s s', fwzap s' = fwzap s -> ds_strategy s' = ds_strategy s.
Proof. intros s s' H. apply (f_equal ds_strategy) in H. destruct s, s'. exact H. Qed.
Lemma fw_good_match : forall s s', fwzap s' = fwzap s -> ds_good_match s' = ds_good_match s.
Proof. intros s s' H. apply (f_equal ds_good_match) in H. destruct s, s'. exact H. Qed.
Lemma fw_nice_match : forall s s', fwzap s' = fwzap s -> ds_nice_match s' = ds_nice_match s.
Proof. intros s s' H. apply (f_equal ds_nice_match) in H. destruct s, s'. exact H. Qed.
Lemma fw_dyn_ltree_fc : forall s s', fwzap s' = fwzap s -> ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s.
Proof. intros s s' H. apply (f_equal ds_dyn_ltree_fc) in H. destruct s, s'. exact H. Qed.
Lemma fw_dyn_ltree_dl : forall s s', fwzap s' = fwzap s -> ds_dyn_ltree_dl s' = ds_dyn_ltree_dl s.
Proof. intros s s' H. apply (f_equal ds_dyn_ltree_dl) in H. destruct s, s'. exact H. Qed.
Lemma fw_dyn_dtree_fc : forall s s', fwzap s' = fwzap s -> ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s.
Proof. intros s s' H. apply (f_equal ds_dyn_dtree_fc) in H. destruct s, s'. exact H. Qed.
Lemma fw_dyn_dtree_dl : forall s s', fwzap s' = fwzap s -> ds_dyn_dtree_dl s' = ds_dyn_dtree_dl s.
Proof. intros s s' H. apply (f_equal ds_dyn_dtree_dl) in H. destruct s, s'. exact H. Qed.
Lemma fw_bl_tree_fc : forall s s', fwzap s' = fwzap s -> ds_bl_tree_fc s' = ds_bl_tree_fc s.
Proof. intros s s' H. apply (f_equal ds_bl_tree_fc) in H. destruct s, s'. exact H. Qed.
Lemma fw_bl_tree_dl : forall s s', fwzap s' = fwzap s -> ds_bl_tree_dl s' = ds_bl_tree_dl s.
Proof. intros s s' H. apply (f_equal ds_bl_tree_dl) in H. destruct s, s'. exact H. Qed.
Lemma fw_bl_count : forall s s', fwzap s' = fwzap s -> ds_bl_count s' = ds_bl_count s.
Proof. intros s s' H. apply (f_equal ds_bl_count) in H. destruct s, s'. exact H. Qed.
Lemma fw_heap : forall s s', fwzap s' = fwzap s -> ds_heap s' = ds_heap s.
Proof. intros s s' H. apply (f_equal ds_heap) in H. destruct s, s'. exact H. Qed.
Lemma fw_depth : forall s s', fwzap s' = fwzap s -> ds_depth s' = ds_depth s.
Proof. intros s s' H. apply (f_equal ds_depth) in H. destruct s, s'. exact H. Qed.
Lemma fw_lit_bufsize : forall s s', fwzap s' = fwzap s -> ds_lit_bufsize s' = ds_lit_bufsize s.
Proof. intros s s' H. apply (f_equal ds_lit_bufsize) in H. destruct s, s'. exact H. Qed.
Lemma fw_sym_next : forall s s', fwzap s' = fwzap s -> ds_sym_next s' = ds_sym_next s.
Proof. intros s s' H. apply (f_equal ds_sym_next) in H. destruct s, s'. exact H. Qed.
Lemma fw_sym_end : forall s s', fwzap s' = fwzap s -> ds_sym_end s' = ds_sym_end s.
Proof. intros s s' H. apply (f_equal ds_sym_end) in H. destruct s, s'. exact H. Qed.
Lemma fw_opt_len : forall s s', fwzap s' = fwzap s -> ds_opt_len s' = ds_opt_len s.
Proof. intros s s' H. apply (f_equal ds_opt_len) in H. destruct s, s'. exact H. Qed.
Lemma fw_static_len : forall s s', fwzap s' = fwzap s -> ds_static_len s' = ds_static_len s.
Proof. intros s s' H. apply (f_equal ds_static_len) in H. destruct s, s'. exact H. Qed.
Lemma fw_matches : forall s s', fwzap s' = fwzap s -> ds_matches s' = ds_matches s.
Proof. intros s s' H. apply (f_equal ds_matches) in H. destruct s, s'. exact H. Qed.
Lemma fw_bi_buf : forall s s', fwzap s' = fwzap s -> ds_bi_buf s' = ds_bi_buf s.
Proof. intros s s' H. apply (f_equal ds_bi_buf) in H. destruct s, s'. exact H. Qed.
Lemma fw_bi_valid : forall s s', fwzap s' = fwzap s -> ds_bi_valid s' = ds_bi_valid s.
Proof. intros s s' H. apply (f_equal ds_bi_valid) in H. destruct s, s'. exact H. Qed.
Lemma fw_window_blk : forall s s', fwzap s' = fwzap s -> ds_window_blk s' = ds_window_blk s.
Proof. intros s s' H. apply (f_equal ds_window_blk) in H. destruct s, s'. exact H. Qed.
Lemma fw_prev_blk : forall s s', fwzap s' = fwzap s -> ds_prev_blk s' = ds_prev_blk s.
Proof. intros s s' H. apply (f_equal ds_prev_blk) in H. destruct s, s'. exact H. Qed.
Lemma fw_head_blk : forall s s', fwzap s' = fwzap s -> ds_head_blk s' = ds_head_blk s.
Proof. intros s s' H. apply (f_equal ds_head_blk) in H. destruct s, s'. exact H. Qed.
Lemma fw_pending_buf_blk : forall s s', fwzap s' = fwzap s -> ds_pending_buf_blk s' = ds_pending_buf_blk s.
Proof. intros s s' H. apply (f_equal ds_pending_buf_blk) in H. destruct s, s'. exact H. Qed.
Lemma fw_cs_input : forall s s', fwzap s' = fwzap s -> cs_input (ds_strm s') = cs_input (ds_strm s).
Proof. intros s s' H. apply (f_equal (fun q => cs_input (ds_strm q))) in H. destruct s, s'. cbn in H. destruct ds_strm, ds_strm0. exact H. Qed.
Lemma fw_cs_out_rev : forall s s', fwzap s' = fwzap s -> cs_out_rev (ds_strm s') = cs_out_rev (ds_strm s).
Proof. intros s s' H. apply (f_equal (fun q => cs_out_rev (ds_strm q))) in H. destruct s, s'. cbn in H. destruct ds_strm, ds_strm0. exact H. Qed.
Lemma fw_cs_avail_out : forall s s', fwzap s' = fwzap s -> cs_avail_out (ds_strm s') = cs_avail_out (ds_strm s).
Proof. intros s s' H. apply (f_equal (fun q => cs_avail_out (ds_strm q))) in H. destruct s, s'. cbn in H. destruct ds_strm, ds_strm0. exact H. Qed.
Lemma fw_cs_total_out : forall s s', fwzap s' = fwzap s -> cs_total_out (ds_strm s') = cs_total_out (ds_strm s).
Proof. intros s s' H. apply (f_equal (fun q => cs_total_out (ds_strm q))) in H. destruct s, s'. cbn in H. destruct ds_strm, ds_strm0. exact H. Qed.
Lemma fw_cs_data_type : forall s s', fwzap s' = fwzap s -> cs_data_type (ds_strm s') = cs_data_type (ds_strm s).
Proof. intros s s' H. apply (f_equal (fun q => cs_data_type (ds_strm q))) in H. destruct s, s'. cbn in H. destruct ds_strm, ds_strm0. exact H. Qed.

Lemma fwz_set_window : forall s v, fwzap (set_window s v) = fwzap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma fwz_set_match_start : forall s v, fwzap (set_match_start s v) = fwzap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma fwz_set_strstart : forall s v, fwzap (set_strstart s v) = fwzap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma fwz_set_block_start : forall s v, fwzap (set_block_start s v) = fwzap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma fwz_set_insert : forall s v, fwzap (set_insert s v) = fwzap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma fwz_set_head : forall s v, fwzap (set_head s v) = fwzap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma fwz_set_prev : forall s v, fwzap (set_prev s v) = fwzap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma fwz_set_ins_h : forall s v, fwzap (set_ins_h s v) = fwzap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma fwz_set_lookahead : forall s v, fwzap (set_lookahead s v) = fwzap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma fwz_set_high_water : forall s v, fwzap (set_high_water s v) = fwzap s.
Proof. intros s v. destruct s. reflexivity. Qed.
Lemma fwz_cset_next_in : forall s v, fwzap (set_strm s (cset_next_in (ds_strm s) v)) = fwzap s.
Proof. intros s v. destruct s. cbn. destruct ds_strm. reflexivity. Qed.
Lemma fwz_cset_avail_in : forall s v, fwzap (set_strm s (cset_avail_in (ds_strm s) v)) = fwzap s.
Proof. intros s v. destruct s. cbn. destruct ds_strm. reflexivity. Qed.
Lemma fwz_cset_adler : forall s v, fwzap (set_strm s (cset_adler (ds_strm s) v)) = fwzap s.
Proof. intros s v. destruct s. cbn. destruct ds_strm. reflexivity. Qed.
Lemma fwz_cset_total_in : forall s v, fwzap (set_strm s (cset_total_in (ds_strm s) v)) = fwzap s.
Proof. intros s v. destruct s. cbn. destruct ds_strm. reflexivity. Qed.
#[export] Hint Rewrite fwz_set_window fwz_set_match_start fwz_set_strstart fwz_set_block_start fwz_set_insert fwz_set_head fwz_set_prev fwz_set_ins_h fwz_set_lookahead fwz_set_high_water fwz_cset_next_in fwz_cset_avail_in fwz_cset_adler fwz_cset_total_in : fwz.

Local Ltac fwz := autorewrite with fwz; try reflexivity.

Lemma fwz_slide_hash : forall s, fwzap (slide_hash s) = fwzap s.
Proof. intros s. unfold slide_hash. fwz. Qed.
Lemma fwz_fw_slide : forall s ws more, fwzap (fw_slide s ws more) = fwzap s.
Proof. intros s ws more. unfold fw_slide. rewrite fwz_slide_hash. destruct (_ <? _); fwz. Qed.
Lemma fwz_read_buf : forall s off size, fwzap (fst (read_buf s (RB_window off) size)) = fwzap s.
Proof.
  intros s off size. unfold read_buf.
  destruct (_ =? 0); cbn [fst]; [reflexivity|].
  destruct s; cbn. destruct ds_strm; cbn. destruct (ds_wrap =? 1); [| destruct (ds_wrap =? 2)]; reflexivity.
Qed.
Lemma fwz_fill_window_insert : forall f s str, fwzap (fill_window_insert f s str) = fwzap s.
Proof.
  induction f as [|f IH]; intros s str; cbn [fill_window_insert]; [reflexivity|].
  destruct (negb (ds_insert s =? 0)); [| reflexivity].
  match goal with |- fwzap (if ?c then ?x else _) = _ => assert (E : fwzap x = fwzap s) by fwz; destruct c; [exact E | rewrite IH; exact E] end.
Qed.
Lemma fwz_fw_insert : forall s, fwzap (fw_insert s) = fwzap s.
Proof. intros s. unfold fw_insert. destruct (_ <=? _); [rewrite fwz_fill_window_insert|]; fwz. Qed.
Lemma fwz_fill_window_body : forall s ws, fwzap (fst (fill_window_body s ws)) = fwzap s.
Proof.
  intros s ws. rewrite fill_window_body_eq.
  destruct (ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s).
  - destruct (cs_avail_in (ds_strm (fw_slide s ws (fw_more s))) =? 0); cbn [fst]; [apply fwz_fw_slide|].
    destruct (read_buf (fw_slide s ws (fw_more s)) _ _) as [s2 n] eqn:E. cbn [fst].
    rewrite fwz_fw_insert, fwz_set_lookahead. apply (f_equal fst) in E. cbn [fst] in E. rewrite <- E, fwz_read_buf. apply fwz_fw_slide.
  - destruct (cs_avail_in (ds_strm s) =? 0); cbn [fst]; [reflexivity|].
    destruct (read_buf s _ _) as [s2 n] eqn:E. cbn [fst].
    rewrite fwz_fw_insert, fwz_set_lookahead. apply (f_equal fst) in E. cbn [fst] in E. rewrite <- E. apply fwz_read_buf.
Qed.
Lemma fwz_fill_window_loop : forall f s ws, fwzap (fill_window_loop f s ws) = fwzap s.
Proof.
  induction f as [|f IH]; intros s ws; cbn [fill_window_loop]; [reflexivity|].
  destruct (fill_window_body s ws) as [s1 brk] eqn:E. pose proof (fwz_fill_window_body s ws) as B. rewrite E in B. cbn [fst] in B.
  destruct brk; [exact B|]. destruct (_ && _); [rewrite IH|]; exact B.
Qed.
Lemma fwz_fill_window_high : forall s, fwzap (fill_window_high s) = fwzap s.
Proof.
  intros s. unfold fill_window_high.
  destruct (_ <? _); [| reflexivity]. destruct (_ <? _); [fwz|]. destruct (_ <? _); fwz.
Qed.
Lemma fwz_fill_window : forall s, fwzap (fill_window s) = fwzap s.
Proof. intros s. unfold fill_window. rewrite fwz_fill_window_high. apply fwz_fill_window_loop. Qed.


Lemma fw_slide_fields : forall s ws more,
  let s' := fw_slide s ws more in
  ds_strstart s' = ds_strstart s - ws /\ ds_block_start s' = ds_block_start s - ws
  /\ ds_match_start s' = wrap32 (ds_match_start s - ws) /\ ds_lookahead s' = ds_lookahead s
  /\ ds_high_water s' = ds_high_water s /\ ds_ins_h s' = ds_ins_h s
  /\ ds_insert s' = (if ds_strstart s - ws <? ds_insert s then ds_strstart s - ws else ds_insert s)
  /\ ds_head s' = slide_hash_loop (Z.to_nat (ds_hash_size s)) (ds_head s) (ds_hash_size s) (ds_w_size s)
  /\ ds_prev s' = slide_hash_loop (Z.to_nat (ds_w_size s)) (ds_prev s) (ds_w_size s) (ds_w_size s)
  /\ ds_strm s' = ds_strm s /\ ds_w_size s' = ds_w_size s /\ ds_hash_size s' = ds_hash_size s
  /\ ds_window s' = arr_blit (ds_window s) 0 (ds_window s) ws (wrap32 (ws - more)).
Proof.
  intros s ws more. unfold fw_slide, slide_hash. cbv zeta.
  destruct s; dsr. destruct (_ <? _); dsr; repeat split; reflexivity.
Qed.

Lemma read_buf_fields : forall s off size,
  let '(s', n) := read_buf s (RB_window off) size in
  let st := ds_strm s in let st' := ds_strm s' in
  n = (if (if size <? cs_avail_in st then size else cs_avail_in st) =? 0 then 0 else (if size <? cs_avail_in st then size else cs_avail_in st))
  /\ cs_avail_in st' = cs_avail_in st - n /\ cs_next_in st' = cs_next_in st + n
  /\ cs_total_in st' = (if n =? 0 then cs_total_in st else wrap64 (cs_total_in st + n))
  /\ cs_input st' = cs_input st /\ cs_out_rev st' = cs_out_rev st /\ cs_avail_out st' = cs_avail_out st
  /\ cs_total_out st' = cs_total_out st /\ cs_data_type st' = cs_data_type st /\ cs_msg st' = cs_msg st
  /\ (ds_wrap s = 0 -> cs_adler st' = cs_adler st)
  /\ (ds_wrap s = 1 -> n <> 0 -> cs_adler st' = adler32_upd (cs_adler st) (arr_slice (cs_input st) (cs_next_in st) n))
  /\ (ds_wrap s = 2 -> n <> 0 -> cs_adler st' = crc32_upd (cs_adler st) (arr_slice (cs_input st) (cs_next_in st) n))
  /\ ds_window s' = (if n =? 0 then ds_window s else arr_upd (ds_window s) off (arr_slice (cs_input st) (cs_next_in st) n))
  /\ fwzap s' = fwzap s
  /\ ds_strstart s' = ds_strstart s /\ ds_block_start s' = ds_block_start s /\ ds_match_start s' = ds_match_start s
  /\ ds_lookahead s' = ds_lookahead s /\ ds_high_water s' = ds_high_water s /\ ds_ins_h s' = ds_ins_h s
  /\ ds_insert s' = ds_insert s /\ ds_head s' = ds_head s /\ ds_prev s' = ds_prev s /\ ds_wrap s' = ds_wrap s.
Proof.
  intros s off size. unfold read_buf.
  set (len := if size <? cs_avail_in (ds_strm s) then size else cs_avail_in (ds_strm s)).
  destruct (Z.eqb_spec len 0) as [Z0|Z0].
  - cbn [fst snd]. rewrite Z.eqb_refl. repeat split; try reflexivity; intros; try reflexivity; try lia.
    all: match goal with H : ?x <> ?x |- _ => destruct (H eq_refl) end.
  - replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; exact Z0).
    destruct s; dsr. destruct ds_strm; dsr.
    destruct (Z.eqb_spec ds_wrap 1) as [W1|W1]; [| destruct (Z.eqb_spec ds_wrap 2) as [W2|W2]]; dsr;
      repeat split; try reflexivity; intros; try reflexivity; try lia.
Qed.


Definition fwi_step (s : deflate_state) (str : Z) : deflate_state :=
  let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) in
  let s := set_ins_h s h in
  let s := set_prev s (arr_set (ds_prev s) (Z.land str (ds_w_mask s)) (arr_get (ds_head s) h)) in
  let s := set_head s (arr_set (ds_head s) h (wrap16 str)) in
  set_insert s (ds_insert s - 1).

Lemma fill_window_insert_step' : forall f s str,
  fill_window_insert (S f) s str
  = if negb (ds_insert s =? 0)
    then (let s1 := fwi_step s str in
          if ds_lookahead s1 + ds_insert s1 <? MIN_MATCH then s1 else fill_window_insert f s1 (str + 1))
    else s.
Proof. intros f s str. reflexivity. Qed.

Lemma fwi_step_fields : forall s str,
  let s' := fwi_step s str in
  let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) in
  ds_ins_h s' = h /\ ds_insert s' = ds_insert s - 1
  /\ ds_prev s' = arr_set (ds_prev s) (Z.land str (ds_w_mask s)) (arr_get (ds_head s) h)
  /\ ds_head s' = arr_set (ds_head s) h (wrap16 str)
  /\ ds_strstart s' = ds_strstart s /\ ds_lookahead s' = ds_lookahead s /\ ds_block_start s' = ds_block_start s
  /\ ds_match_start s' = ds_match_start s /\ ds_high_water s' = ds_high_water s /\ ds_window s' = ds_window s
  /\ ds_strm s' = ds_strm s /\ ds_w_size s' = ds_w_size s /\ ds_hash_size s' = ds_hash_size s
  /\ ds_w_mask s' = ds_w_mask s /\ ds_hash_mask s' = ds_hash_mask s /\ ds_hash_shift s' = ds_hash_shift s
  /\ fwzap s' = fwzap s.
Proof. intros s str. unfold fwi_step. destruct s; dsr. repeat split; reflexivity. Qed.

Record fwi_rel (s s' : deflate_state) : Prop := MkFWI {
  fi_z : fwzap s' = fwzap s;
  fi_str : ds_strstart s' = ds_strstart s; fi_look : ds_lookahead s' = ds_lookahead s;
  fi_bs : ds_block_start s' = ds_block_start s; fi_ms : ds_match_start s' = ds_match_start s;
  fi_hw : ds_high_water s' = ds_high_water s; fi_win : ds_window s' = ds_window s; fi_strm : ds_strm s' = ds_strm s;
  fi_ws : ds_w_size s' = ds_w_size s; fi_hs : ds_hash_size s' = ds_hash_size s;
  fi_wm : ds_w_mask s' = ds_w_mask s; fi_hm : ds_hash_mask s' = ds_hash_mask s; fi_hsh : ds_hash_shift s' = ds_hash_shift s;
  fi_hl : arr_len (ds_head s') = arr_len (ds_head s); fi_pl : arr_len (ds_prev s') = arr_len (ds_prev s);
  fi_ins : 0 <= ds_insert s -> 0 <= ds_insert s' <= ds_insert s }.

Lemma fwi_rel_refl : forall s, fwi_rel s s.
Proof. intros s. constructor; try reflexivity. lia. Qed.
Lemma fwi_rel_trans : forall a b c, fwi_rel a b -> fwi_rel b c -> fwi_rel a c.
Proof. intros a b c [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16]; constructor; try congruence. intros H. specialize (A16 H). specialize (B16 ltac:(lia)). lia. Qed.
Lemma fwi_rel_step : forall s str, 0 < ds_insert s -> fwi_rel s (fwi_step s str).
Proof.
  intros s str Hi. destruct (fwi_step_fields s str) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17).
  constructor; try assumption. - rewrite E4. apply arr_len_set. - rewrite E3. apply arr_len_set. - rewrite E2. lia.
Qed.

Lemma fill_window_insert_rel : forall f s str, 0 <= ds_insert s -> fwi_rel s (fill_window_insert f s str).
Proof.
  induction f as [|f IH]; intros s str Hi; [apply fwi_rel_refl|].
  rewrite fill_window_insert_step'. destruct (Z.eqb_spec (ds_insert s) 0) as [Z0|Z0]; cbn [negb]; [apply fwi_rel_refl|].
  pose proof (fwi_rel_step s str ltac:(lia)) as R1. cbv zeta.
  destruct (_ <? MIN_MATCH); [exact R1|].
  eapply fwi_rel_trans; [exact R1|]. apply IH. pose proof (fi_ins _ _ R1 Hi). lia.
Qed.

Lemma update_hash_range16 : forall s h c, 0 <= ds_hash_mask s < 2 ^ 16 -> 0 <= update_hash s h c < 2 ^ 16.
Proof. intros s h c Hm. unfold update_hash. pose proof (land_mask_range (Z.lxor (wrap32 (Z.shiftl h (ds_hash_shift s))) c) _ (proj1 Hm)). lia. Qed.

Lemma fill_window_insert_ih : forall f s str, 0 <= ds_hash_mask s < 2 ^ 16 -> 0 <= ds_ins_h s < 2 ^ 16 ->
  0 <= ds_ins_h (fill_window_insert f s str) < 2 ^ 16.
Proof.
  induction f as [|f IH]; intros s str Hm Hi; [exact Hi|].
  rewrite fill_window_insert_step'. destruct (negb (ds_insert s =? 0)); [| exact Hi]. cbv zeta.
  destruct (fwi_step_fields s str) as (E1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E15 & _).
  assert (R : 0 <= ds_ins_h (fwi_step s str) < 2 ^ 16) by (rewrite E1; apply update_hash_range16; exact Hm).
  destruct (_ <? MIN_MATCH); [exact R|]. apply IH; [rewrite E15; exact Hm | exact R].
Qed.

Lemma fill_window_insert_hash : forall f s str Ins,
  hc_inv Ins (ds_strstart s) (ds_w_size s) (ds_head s) (ds_prev s) (ds_hash_size s) ->
  str = ds_strstart s - ds_insert s -> 0 <= str -> 0 <= ds_insert s -> ds_strstart s <= 65536 ->
  arr_len (ds_prev s) = ds_w_size s -> arr_len (ds_head s) = ds_hash_size s -> 0 < ds_w_size s -> 0 < ds_hash_size s ->
  ds_hash_mask s = ds_hash_size s - 1 -> ds_w_mask s = ds_w_size s - 1 -> (exists k, 0 <= k /\ ds_w_size s = 2 ^ k) ->
  exists Ins', hc_inv Ins' (ds_strstart s) (ds_w_size s) (ds_head (fill_window_insert f s str)) (ds_prev (fill_window_insert f s str)) (ds_hash_size s).
Proof.
  induction f as [|f IH]; intros s str Ins HC Estr Hstr Hins Hss Lp Lh Hws Hhs Hhm Hwm Hpow.
  - exists Ins. exact HC.
  - rewrite fill_window_insert_step'. destruct (Z.eqb_spec (ds_insert s) 0) as [Z0|Z0]; cbn [negb]; [exists Ins; exact HC|]. cbv zeta.
    destruct (fwi_step_fields s str) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17).
    set (h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1)))) in *.
    assert (Hh : 0 <= h < ds_hash_size s).
    { subst h. pose proof (update_hash_lt s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) ltac:(rewrite Hhm, Lh; lia)). rewrite Lh in H. exact H. }
    assert (Hland : Z.land str (ds_w_mask s) = str mod ds_w_size s).
    { destruct Hpow as (k & Hk & Ek). rewrite Hwm, Ek. replace (2 ^ k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia). apply Z.land_ones. exact Hk. }
    assert (HC1 : hc_inv (fun q => Ins q \/ q = str) (ds_strstart s) (ds_w_size s) (ds_head (fwi_step s str)) (ds_prev (fwi_step s str)) (ds_hash_size s)).
    { rewrite E3, E4, Hland. apply (hc_inv_insert Ins (ds_strstart s)); try assumption; try lia;
        try (rewrite wrap16_id by lia; reflexivity); try (rewrite Lp; apply Z.mod_pos_bound; exact Hws); rewrite ?Lh; lia. }
    destruct (_ <? MIN_MATCH); [eexists; exact HC1|].
    rewrite <- E5, <- E12, <- E13 in HC1.
    destruct (IH (fwi_step s str) (str + 1) _ HC1) as [Ins' HC']; rewrite ?E2, ?E3, ?E4, ?E5, ?E12, ?E13, ?E14, ?E15, ?arr_len_set; try assumption; try lia.
    exists Ins'. rewrite E5, E12, E13 in HC'. exact HC'.
Qed.

Lemma fw_insert_facts : forall s,
  0 <= ds_insert s <= ds_strstart s -> 0 <= ds_hash_mask s < 2 ^ 16 -> 0 <= ds_ins_h s < 2 ^ 16 ->
  (forall i, 0 <= i < arr_len (ds_window s) -> 0 <= arr_get (ds_window s) i < 256) ->
  let s' := fw_insert s in
  fwi_rel s s' /\ 0 <= ds_ins_h s' < 2 ^ 16.
Proof.
  intros s Hins Hm Hih Hwb. unfold fw_insert.
  destruct (MIN_MATCH <=? ds_lookahead s + ds_insert s); [| split; [apply fwi_rel_refl | exact Hih]].
  set (s2 := set_ins_h (set_ins_h s _) _).
  assert (R2 : fwi_rel s s2) by (subst s2; constructor; dsr; try reflexivity; lia).
  assert (I2 : 0 <= ds_ins_h s2 < 2 ^ 16).
  { subst s2. dsr. apply update_hash_range16. dsr. exact Hm. }
  replace (Z.to_nat (ds_insert s2)) with (Z.to_nat (ds_insert s)) by (subst s2; dsr; reflexivity).
  split.
  - eapply fwi_rel_trans; [exact R2|]. apply fill_window_insert_rel. subst s2; dsr; lia.
  - apply fill_window_insert_ih; [subst s2; dsr; exact Hm | exact I2].
Qed.

Lemma fw_insert_hash : forall s Ins,
  hc_inv Ins (ds_strstart s) (ds_w_size s) (ds_head s) (ds_prev s) (ds_hash_size s) ->
  0 <= ds_insert s <= ds_strstart s -> ds_strstart s <= 65536 ->
  arr_len (ds_prev s) = ds_w_size s -> arr_len (ds_head s) = ds_hash_size s -> 0 < ds_w_size s -> 0 < ds_hash_size s ->
  ds_hash_mask s = ds_hash_size s - 1 -> ds_w_mask s = ds_w_size s - 1 -> (exists k, 0 <= k /\ ds_w_size s = 2 ^ k) ->
  exists Ins', hc_inv Ins' (ds_strstart s) (ds_w_size s) (ds_head (fw_insert s)) (ds_prev (fw_insert s)) (ds_hash_size s).
Proof.
  intros s Ins HC Hins Hss Lp Lh Hws Hhs Hhm Hwm Hpow. unfold fw_insert.
  destruct (MIN_MATCH <=? ds_lookahead s + ds_insert s); [| exists Ins; exact HC].
  set (s2 := set_ins_h (set_ins_h s _) _).
  replace (Z.to_nat (ds_insert s2)) with (Z.to_nat (ds_insert s)) by (subst s2; dsr; reflexivity).
  destruct (fill_window_insert_hash (Z.to_nat (ds_insert s)) s2 (ds_strstart s - ds_insert s) Ins) as [Ins' HC'];
    try (subst s2; dsr; first [exact HC | assumption | lia]).
  exists Ins'. subst s2. dsr in HC'. exact HC'.
Qed.


Record fwt (s0 s : deflate_state) : Prop := MkFWT {
  t_z : fwzap s = fwzap s0;
  t_bs : ds_strstart s - ds_block_start s = ds_strstart s0 - ds_block_start s0;
  t_ms : wrap32 (ds_strstart s - 1 - ds_match_start s) = wrap32 (ds_strstart s0 - 1 - ds_match_start s0);
  t_hw : ds_high_water s = ds_high_water s0;
  t_ih : 0 <= ds_ins_h s0 < 2 ^ 16 -> 0 <= ds_ins_h s < 2 ^ 16;
  t_str1 : 1 <= ds_strstart s0 -> 1 <= ds_strstart s;
  t_cons : ds_lookahead s + cs_avail_in (ds_strm s) = ds_lookahead s0 + cs_avail_in (ds_strm s0);
  t_look : ds_lookahead s0 <= ds_lookahead s;
  t_in : cs_next_in (ds_strm s) + cs_avail_in (ds_strm s) = cs_next_in (ds_strm s0) + cs_avail_in (ds_strm s0);
  t_ad0 : ds_wrap s0 = 0 -> cs_adler (ds_strm s) = cs_adler (ds_strm s0);
  t_ad2 : ds_wrap s0 = 2 -> 0 <= cs_adler (ds_strm s0) < 2 ^ 32 -> 0 <= cs_adler (ds_strm s) < 2 ^ 32;
  t_hash : (exists Ins, hc_inv Ins (ds_strstart s0) (ds_w_size s0) (ds_head s0) (ds_prev s0) (ds_hash_size s0)) ->
           exists Ins, hc_inv Ins (ds_strstart s) (ds_w_size s) (ds_head s) (ds_prev s) (ds_hash_size s);
  t_strle : ds_strstart s <= ds_strstart s0;
  t_nb : (ds_block_start s0 < 0 -> ds_w_size s0 - MIN_LOOKAHEAD <= ds_strstart s0) ->
         (ds_block_start s < 0 -> ds_w_size s - MIN_LOOKAHEAD <= ds_strstart s) }.

Lemma fwt_refl : forall s, fwt s s.
Proof. intros s. constructor; auto; try reflexivity; lia. Qed.

Lemma fwt_trans : forall a b c, ds_wrap b = ds_wrap a -> fwt a b -> fwt b c -> fwt a c.
Proof.
  intros a b c W [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A10b A11 A12 A13] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B10b B11 B12 B13]; constructor.
  - congruence. - clear - A2 B2; lia. - congruence. - congruence.
  - intros H. exact (B5 (A5 H)).
  - intros H. exact (B6 (A6 H)).
  - clear - A7 B7; lia. - clear - A8 B8; lia. - clear - A9 B9; lia.
  - intros H. rewrite (B10 ltac:(congruence)). exact (A10 H).
  - intros H R. apply B10b; [congruence | exact (A10b H R)].
  - intros H. exact (B11 (A11 H)).
  - clear - A12 B12; lia.
  - intros H. exact (B13 (A13 H)).
Qed.

Lemma wrap32_sub_wrap32 : forall a b, wrap32 (a - wrap32 b) = wrap32 (a - b).
Proof. intros a b. rewrite !wrap32_mod. rewrite <- (Zminus_mod_idemp_r a b). reflexivity. Qed.

Lemma fw_tail_facts : forall ws hs s1 more,
  fw_wf ws hs s1 -> more = 2 * ws - ds_lookahead s1 - ds_strstart s1 -> 0 < more ->
  cs_avail_in (ds_strm s1) <> 0 -> 0 <= ds_hash_mask s1 < 2 ^ 16 -> 0 <= ds_ins_h s1 < 2 ^ 16 ->
  (exists k, 0 <= k /\ ws = 2 ^ k) ->
  let '(s2, n) := read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) more in
  let s4 := fw_insert (set_lookahead s2 (ds_lookahead s2 + n)) in
  fw_wf ws hs s4 /\ fwt s1 s4 /\ ds_wrap s4 = ds_wrap s1 /\ 0 <= ds_hash_mask s4 < 2 ^ 16 /\ 0 <= ds_ins_h s4 < 2 ^ 16
  /\ ds_lookahead s1 < ds_lookahead s4 /\ ds_strstart s4 = ds_strstart s1.
Proof.
  intros ws hs s1 more HW1 Hmore Hpos Hai Hhm Hih POW.
  pose proof (wf_wsr _ _ _ HW1) as Lws. pose proof (wf_sl _ _ _ HW1) as Vsl. pose proof (wf_look _ _ _ HW1) as Vlook.
  pose proof (wf_ws _ _ _ HW1) as Vws. pose proof (wf_ins _ _ _ HW1) as Vins. pose proof (wf_hs _ _ _ HW1) as Vhs. pose proof (wf_hsr _ _ _ HW1) as Lhs.
  pose proof (wf_hl _ _ _ HW1) as Vhl. pose proof (wf_pl _ _ _ HW1) as Vpl. pose proof (wf_hmask _ _ _ HW1) as Vhm. pose proof (wf_wmask _ _ _ HW1) as Vwm.
  destruct (read_buf_wf ws hs s1 (ds_strstart s1 + ds_lookahead s1) more HW1 eq_refl ltac:(lia) ltac:(lia))
    as (HW2 & HC2 & HL2 & HS2 & HI2 & _ & Hhm2 & Hwm2 & Hih2 & Hn & Hpos2 & HA2).
  pose proof (read_buf_fields s1 (ds_strstart s1 + ds_lookahead s1) more) as RF.
  destruct (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) more) as [s2 n]. cbn [fst snd] in *.
  destruct RF as (_ & RA & RN & RT & RI & _ & _ & _ & _ & _ & RAD0 & _ & RAD2 & _ & RZ & RS & RB & RM & RL & RH & RIH & RINS & RHD & RPV & RW).
  specialize (Hpos2 Hai Hpos).
  set (s3 := set_lookahead s2 (ds_lookahead s2 + n)).
  assert (HW3 : fw_wf ws hs s3) by (subst s3; destruct HW2; constructor; dsr; try assumption; lia).
  destruct (fw_insert_facts s3 ltac:(subst s3; dsr; lia) ltac:(subst s3; dsr; lia) ltac:(subst s3; dsr; lia)
              ltac:(subst s3; dsr; intros i Hi; apply (wf_wb _ _ _ HW2); rewrite <- (wf_wl _ _ _ HW2); exact Hi)) as [R4 I4].
  destruct (fw_insert_wf ws hs s3 HW3) as (HW4 & HC4 & HL4 & HS4 & HA4).
  remember (fw_insert s3) as s4 eqn:Es4.
  pose proof R4 as [Z4 S4 L4 B4 M4 W4 WI4 ST4 WS4 HS4' WM4 HM4 HSH4 HL4' PL4 IN4].
  split; [exact HW4|].
  split.
  { constructor.
    - rewrite Z4. subst s3. rewrite fwz_set_lookahead. exact RZ.
    - rewrite S4, B4. subst s3. dsr. rewrite RS, RB. reflexivity.
    - rewrite S4, M4. subst s3. dsr. rewrite RS, RM. reflexivity.
    - rewrite W4. subst s3. dsr. exact RH.
    - intros _. exact I4.
    - rewrite S4. subst s3. dsr. rewrite RS. intros H; exact H.
    - rewrite L4, ST4. subst s3. dsr. rewrite RA, RL. lia.
    - rewrite L4. subst s3. dsr. rewrite RL. lia.
    - rewrite ST4. subst s3. dsr. rewrite RN, RA. lia.
    - intros W0. rewrite ST4. subst s3. dsr. exact (RAD0 W0).
    - intros W0 A0. rewrite ST4. subst s3. dsr. rewrite (RAD2 W0 ltac:(lia)). apply crc32_upd_range.
      intros b Hb. pose proof (u8a_slice (cs_input (ds_strm s1)) (cs_next_in (ds_strm s1)) n (wf_ib _ _ _ HW1)
                    ltac:(intros _; pose proof (wf_ni _ _ _ HW1); pose proof (wf_inlen _ _ _ HW1); pose proof (wf_ai _ _ _ HW2); lia)) as BY.
      exact (proj1 (List.Forall_forall _ _) BY b Hb).
    - intros [Ins HC]. rewrite S4, WS4, HS4'.
      pose proof (wf_ws _ _ _ HW3) as Y1. pose proof (wf_hs _ _ _ HW3) as Y2. pose proof (wf_pl _ _ _ HW3) as Y3. pose proof (wf_hl _ _ _ HW3) as Y4.
      pose proof (wf_hmask _ _ _ HW3) as Y5. pose proof (wf_wmask _ _ _ HW3) as Y6. pose proof (wf_ins _ _ _ HW3) as Y7.
      pose proof (wf_sl _ _ _ HW3) as Y8. pose proof (wf_look _ _ _ HW3) as Y9.
      assert (ES3 : ds_strstart s3 = ds_strstart s1) by (subst s3; dsr; exact RS).
      assert (X1 : hc_inv Ins (ds_strstart s3) (ds_w_size s3) (ds_head s3) (ds_prev s3) (ds_hash_size s3)).
      { rewrite Y1, Y2, ES3. replace (ds_head s3) with (ds_head s1) by (subst s3; dsr; symmetry; exact RHD).
        replace (ds_prev s3) with (ds_prev s1) by (subst s3; dsr; symmetry; exact RPV). rewrite <- Vws, <- Vhs. exact HC. }
      destruct (fw_insert_hash s3 Ins X1 Y7) as [Ins' HC']; try (rewrite ?Y1, ?Y2, ?Y3, ?Y4, ?Y5, ?Y6; first [reflexivity | exact POW | lia]).
      exists Ins'. rewrite Es4. exact HC'.
    - rewrite S4. subst s3. dsr. rewrite RS. lia.
    - rewrite S4, B4, WS4. subst s3. dsr. rewrite RS, RB, (fw_w_size _ _ RZ). intros H; exact H. }
  split; [rewrite (proj1 (proj2 HC4)); subst s3; dsr; exact RW|].
  split; [rewrite HM4; subst s3; dsr; rewrite Hhm2; exact Hhm|].
  split; [exact I4|].
  split; [rewrite L4; subst s3; dsr; rewrite RL; lia|].
  rewrite S4. subst s3. dsr. exact RS.
Qed.

Lemma fw_body_facts : forall ws hs s,
  fw_wf ws hs s -> ds_lookahead s < MIN_LOOKAHEAD -> 0 <= ds_hash_mask s < 2 ^ 16 -> 0 <= ds_ins_h s < 2 ^ 16 ->
  (exists k, 0 <= k /\ ws = 2 ^ k) ->
  let '(s', brk) := fill_window_body s ws in
  fw_wf ws hs s' /\ fwt s s' /\ ds_wrap s' = ds_wrap s /\ 0 <= ds_hash_mask s' < 2 ^ 16 /\ 0 <= ds_ins_h s' < 2 ^ 16
  /\ ds_strstart s' + MIN_LOOKAHEAD < 2 * ws
  /\ (brk = true -> cs_avail_in (ds_strm s') = 0)
  /\ (brk = false -> ds_lookahead s < ds_lookahead s').
Proof.
  intros ws hs s HW Hlook Hhm Hih POW.
  rewrite fill_window_body_eq.
  pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_look _ _ _ HW) as Vlook.
  pose proof (wf_ws _ _ _ HW) as Vws. pose proof (wf_wsz _ _ _ HW) as Vwsz. pose proof (wf_ins _ _ _ HW) as Vins.
  pose proof (wf_hs _ _ _ HW) as Vhs. pose proof (wf_hsr _ _ _ HW) as Lhs. pose proof (wf_hl _ _ _ HW) as Vhl. pose proof (wf_pl _ _ _ HW) as Vpl.
  unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *.
  assert (Hmore : fw_more s = 2 * ws - ds_lookahead s - ds_strstart s).
  { unfold fw_more. rewrite Vwsz. rewrite wrap32_id by lia. lia. }
  destruct (Z.leb_spec (ws + (ds_w_size s - (258 + 3 + 1))) (ds_strstart s)) as [Sl|Ns].
  -
    destruct (fw_slide_wf ws hs s (fw_more s) HW ltac:(lia) Hmore) as (HW1 & HC1 & HL1 & HS1).
    pose proof (fw_slide_fields s ws (fw_more s)) as SF. cbv zeta in SF.
    destruct SF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
    remember (fw_slide s ws (fw_more s)) as s1 eqn:Es1.
    assert (T1 : fwt s s1).
    { constructor.
      - rewrite Es1. apply fwz_fw_slide.
      - rewrite F1, F2. lia.
      - rewrite F1, F3, wrap32_sub_wrap32. f_equal. lia.
      - exact F5.
      - rewrite F6. intros H; exact H.
      - rewrite F1. lia.
      - rewrite F4, F10. reflexivity.
      - rewrite F4. lia.
      - rewrite F10. reflexivity.
      - rewrite F10. reflexivity.
      - rewrite F10. intros _ H; exact H.
      - intros [Ins HC]. rewrite F1, F8, F9, F11, F12, Vws, Vhs. rewrite Vws, Vhs in HC.
        eexists. apply (hc_inv_slide Ins (ds_strstart s) ws (ds_head s) (ds_prev s) hs HC); try lia.
        + intros j Hj. apply (wf_hb _ _ _ HW). exact Hj.
        + intros j Hj. apply (wf_pb _ _ _ HW). exact Hj.
      - rewrite F1. lia.
      - rewrite F1, F2, F11. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH. intros _ _. clear -Sl. lia. }
    assert (W1 : ds_wrap s1 = ds_wrap s) by exact (proj1 (proj2 HC1)).
    assert (HM1 : 0 <= ds_hash_mask s1 < 2 ^ 16) by (rewrite (fw_hash_mask _ _ (t_z _ _ T1)); exact Hhm).
    assert (IH1 : 0 <= ds_ins_h s1 < 2 ^ 16) by (rewrite F6; exact Hih).
    assert (Hm1 : wrap32 (fw_more s + ws) = 2 * ws - ds_lookahead s1 - ds_strstart s1).
    { rewrite Hmore, HL1, HS1. rewrite wrap32_id by lia. lia. }
    rewrite Hm1.
    destruct (Z.eqb_spec (cs_avail_in (ds_strm s1)) 0) as [A0|A0].
    + split; [exact HW1|]. split; [exact T1|]. split; [exact W1|]. split; [exact HM1|]. split; [exact IH1|].
      split; [rewrite HS1; lia|]. split; [intros _; exact A0 | intros X; discriminate X].
    + pose proof (fw_tail_facts ws hs s1 (2 * ws - ds_lookahead s1 - ds_strstart s1) HW1 eq_refl ltac:(rewrite HL1, HS1; lia) A0 HM1 IH1 POW) as TF.
      destruct (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) (2 * ws - ds_lookahead s1 - ds_strstart s1)) as [s2 n].
      cbv zeta in TF. destruct TF as (HW4 & T4 & W4 & HM4 & IH4 & L4 & S4). cbn [fst snd].
      split; [exact HW4|]. split; [exact (fwt_trans _ _ _ W1 T1 T4)|]. split; [congruence|]. split; [exact HM4|]. split; [exact IH4|].
      split; [rewrite S4, HS1; lia|]. split; [intros X; discriminate X | intros _; rewrite <- HL1; exact L4].
  - destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [A0|A0].
    + split; [exact HW|]. split; [apply fwt_refl|]. split; [reflexivity|]. split; [exact Hhm|]. split; [exact Hih|].
      split; [lia|]. split; [intros _; exact A0 | intros X; discriminate X].
    + pose proof (fw_tail_facts ws hs s (fw_more s) HW Hmore ltac:(lia) A0 Hhm Hih POW) as TF.
      destruct (read_buf s (RB_window (ds_strstart s + ds_lookahead s)) (fw_more s)) as [s2 n].
      cbv zeta in TF. destruct TF as (HW4 & T4 & W4 & HM4 & IH4 & L4 & S4). cbn [fst snd].
      split; [exact HW4|]. split; [exact T4|]. split; [exact W4|]. split; [exact HM4|]. split; [exact IH4|].
      split; [rewrite S4; lia|]. split; [intros X; discriminate X | intros _; exact L4].
Qed.


Lemma fw_loop_facts : forall ws hs f s,
  fw_wf ws hs s -> ds_lookahead s < MIN_LOOKAHEAD -> 0 <= ds_hash_mask s < 2 ^ 16 -> 0 <= ds_ins_h s < 2 ^ 16 ->
  (exists k, 0 <= k /\ ws = 2 ^ k) ->
  MIN_LOOKAHEAD - ds_lookahead s < Z.of_nat f ->
  let s' := fill_window_loop f s ws in
  fw_wf ws hs s' /\ fwt s s' /\ ds_wrap s' = ds_wrap s /\ 0 <= ds_ins_h s' < 2 ^ 16
  /\ ds_strstart s' + MIN_LOOKAHEAD < 2 * ws
  /\ (cs_avail_in (ds_strm s') = 0 \/ MIN_LOOKAHEAD <= ds_lookahead s').
Proof.
  intros ws hs f. induction f as [|f IH]; intros s HW Hlook Hhm Hih POW Hfuel.
  { exfalso. pose proof (wf_look _ _ _ HW). unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. cbn in Hfuel. lia. }
  cbn [fill_window_loop].
  pose proof (fw_body_facts ws hs s HW Hlook Hhm Hih POW) as BF.
  destruct (fill_window_body s ws) as [s1 brk]. destruct BF as (HW1 & T1 & W1 & HM1 & IH1 & ST1 & Bt & Bf).
  destruct brk.
  - split; [exact HW1|]. split; [exact T1|]. split; [exact W1|]. split; [exact IH1|]. split; [exact ST1|]. left. exact (Bt eq_refl).
  - specialize (Bf eq_refl).
    destruct (Z.ltb_spec (ds_lookahead s1) MIN_LOOKAHEAD) as [L|L]; [| cbn [andb]].
    + destruct (Z.eqb_spec (cs_avail_in (ds_strm s1)) 0) as [A|A]; cbn [andb negb].
      * split; [exact HW1|]. split; [exact T1|]. split; [exact W1|]. split; [exact IH1|]. split; [exact ST1|]. left. exact A.
      * destruct (IH s1 HW1 L HM1 IH1 POW ltac:(rewrite Nat2Z.inj_succ in Hfuel; lia)) as (HW2 & T2 & W2 & IH2 & ST2 & EX2).
        split; [exact HW2|]. split; [exact (fwt_trans _ _ _ W1 T1 T2)|]. split; [congruence|]. split; [exact IH2|]. split; [exact ST2|]. exact EX2.
    + split; [exact HW1|]. split; [exact T1|]. split; [exact W1|]. split; [exact IH1|]. split; [exact ST1|]. right. exact L.
Qed.

Lemma fw_high_facts : forall ws hs s, fw_wf ws hs s ->
  let s' := fill_window_high s in
  fw_wf ws hs s' /\ fwzap s' = fwzap s /\ 0 <= ds_high_water s' <= Z.max (ds_high_water s) (2 * ws)
  /\ ds_strstart s' = ds_strstart s /\ ds_lookahead s' = ds_lookahead s /\ ds_block_start s' = ds_block_start s
  /\ ds_match_start s' = ds_match_start s /\ ds_ins_h s' = ds_ins_h s /\ ds_insert s' = ds_insert s
  /\ ds_head s' = ds_head s /\ ds_prev s' = ds_prev s /\ ds_strm s' = ds_strm s /\ ds_wrap s' = ds_wrap s
  /\ ds_w_size s' = ds_w_size s /\ ds_hash_size s' = ds_hash_size s.
Proof.
  intros ws hs s HW. pose proof (wf_wsz _ _ _ HW) as Vwsz. pose proof (wf_sl _ _ _ HW) as Vsl.
  pose proof (wf_look _ _ _ HW) as Vlook. pose proof (wf_hw _ _ _ HW) as Vhw. pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_ins _ _ _ HW) as Vins.
  cbv zeta. pose proof (fwz_fill_window_high s) as FZ. revert FZ.
  unfold fill_window_high, WIN_INIT, MAX_MATCH. rewrite Vwsz.
  assert (GEN : forall a n, 0 <= n -> 0 <= a -> a + n <= 2 * ws -> fw_wf ws hs (set_high_water (set_window s (arr_fill (ds_window s) a n 0)) (a + n))).
  { intros a n Hn Ha Han. pose proof (wf_wb _ _ _ HW) as WB. destruct HW; constructor; dsr; try assumption; try lia; try (rewrite arr_len_fill; assumption).
    intros i Hi. rewrite arr_get_fill. destruct (_ && _); [lia | apply WB; exact Hi]. }
  destruct (Z.ltb_spec (ds_high_water s) (2 * ws)) as [C1|C1].
  - destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s)) as [C2|C2].
    + set (init := if 258 <? 2 * ws - (ds_strstart s + ds_lookahead s) then 258 else 2 * ws - (ds_strstart s + ds_lookahead s)).
      assert (Hinit : 0 <= init <= 258 /\ ds_strstart s + ds_lookahead s + init <= 2 * ws) by (subst init; destruct (Z.ltb_spec 258 (2 * ws - (ds_strstart s + ds_lookahead s))); lia).
      rewrite (wrap32_id init) by lia. intros FZ.
      split. { apply GEN. all: lia. } split; [exact FZ|]. dsr. repeat split; try reflexivity. all: lia.
    + destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s + 258)) as [C3|C3].
      * set (init := if 2 * ws - ds_high_water s <? ds_strstart s + ds_lookahead s + 258 - ds_high_water s then 2 * ws - ds_high_water s else ds_strstart s + ds_lookahead s + 258 - ds_high_water s).
        assert (Hinit : 0 <= init <= 258 /\ ds_high_water s + init <= 2 * ws) by (subst init; destruct (Z.ltb_spec (2 * ws - ds_high_water s) (ds_strstart s + ds_lookahead s + 258 - ds_high_water s)); lia).
        rewrite (wrap32_id init) by lia. intros FZ.
        split. { apply GEN; dsr; lia. } split; [exact FZ|]. dsr. repeat split; try reflexivity. all: lia.
      * intros FZ. split; [exact HW|]. split; [exact FZ|]. repeat split; try reflexivity. all: lia.
  - intros FZ. split; [exact HW|]. split; [exact FZ|]. repeat split; try reflexivity. all: lia.
Qed.

Record dwin (rm : Z) (fz : bool) (ws hs ILEN : Z) (s : deflate_state) : Prop := MkDWIN {
  dw_cfg : dcfg s;
  dw_inv : dinvR rm 0 fz s;
  dw_ws : ds_w_size s = ws;
  dw_hs : ds_hash_size s = hs;
  dw_wrap : 0 <= ds_wrap s;
  dw_lz : ds_level s <> 0;
  dw_busy : ds_status s = BUSY_STATE;
  dw_ilen : arr_len (cs_input (ds_strm s)) = ILEN;
  dw_ilen32 : 0 <= ILEN < 2 ^ 32;
  dw_ni : 0 <= cs_next_in (ds_strm s);
  dw_ai : 0 <= cs_avail_in (ds_strm s);
  dw_in : cs_next_in (ds_strm s) + cs_avail_in (ds_strm s) = ILEN;
  dw_ti : 0 <= cs_total_in (ds_strm s) < 2 ^ 64;
  dw_ad : 0 <= cs_adler (ds_strm s) < 2 ^ 32;
  dw_ad1 : ds_wrap s = 1 -> adler_ok (cs_adler (ds_strm s));
  dw_ad2 : ds_wrap s = 2 -> 0 <= cs_adler (ds_strm s) < 2 ^ 32 }.

Lemma adler_ok_canon : forall a, adler_ok a <-> adler_canon a.
Proof. intros a. unfold adler_ok, adler_canon, lo16, hi16, ZChecksum.ABASE. tauto. Qed.

Lemma dwin_fw_wf : forall rm fz ws hs ILEN s, dwin rm fz ws hs ILEN s -> fw_wf ws hs s.
Proof.
  intros rm fz ws hs ILEN s D. destruct D as [C I Ews Ehs Wr Lz Sbusy Il Il32 Ni Ai In Ti Ad Ad1 Ad2].
  pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl). pose proof (cf_wrap _ C) as Wr2.
  pose proof (di_ins _ _ _ _ I). pose proof (di_look _ _ _ _ I). pose proof (di_sl _ _ _ _ I). pose proof (di_ms _ _ _ _ I). pose proof (di_ih _ _ _ _ I). pose proof (di_hw _ _ _ _ I).
  pose proof (cf_hbits _ C) as HB.
  assert (HSH : 0 <= ds_hash_shift s < 32).
  { rewrite (cf_hshift _ C). unfold MIN_MATCH. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  pose proof (ct_win _ (di_cty _ _ _ _ I)) as TW. pose proof (ct_prev _ (di_cty _ _ _ _ I)) as TP. pose proof (ct_head _ (di_cty _ _ _ _ I)) as TH. pose proof (ct_in _ (di_cty _ _ _ _ I)) as TI.
  unfold u8a, u16a in TW, TP, TH, TI. rewrite (cf_wl _ C) in TW. rewrite (cf_pl _ C) in TP. rewrite (cf_hl _ C) in TH.
  subst ws hs. constructor; try assumption; try lia;
    first [ exact (cf_wl _ C) | exact (cf_wsz _ C) | exact (cf_pl _ C) | exact (cf_wmask _ C) | exact (cf_hl _ C) | exact (cf_hmask _ C)
          | (intros W; apply adler_ok_canon; exact (Ad1 W)) | (intros W; pose proof (Ad2 W); lia) | (intros _; exact Ad) ].
Qed.
Lemma dcfg_fw : forall a b, fwzap a = fwzap b -> arr_len (ds_window a) = arr_len (ds_window b) -> arr_len (ds_prev a) = arr_len (ds_prev b) -> arr_len (ds_head a) = arr_len (ds_head b) -> dcfg b -> dcfg a.
Proof.
  intros a b K EW EP EH C.
  pose proof (fw_status _ _ K) as E1.
  pose proof (fw_window_blk _ _ K) as E2.
  pose proof (fw_prev_blk _ _ K) as E3.
  pose proof (fw_head_blk _ _ K) as E4.
  pose proof (fw_pending_buf_blk _ _ K) as E5.
  pose proof (fw_w_bits _ _ K) as E6.
  pose proof (fw_w_size _ _ K) as E7.
  pose proof (fw_w_mask _ _ K) as E8.
  pose proof (fw_window_size _ _ K) as E9.
  pose proof (fw_hash_bits _ _ K) as E10.
  pose proof (fw_hash_size _ _ K) as E11.
  pose proof (fw_hash_mask _ _ K) as E12.
  pose proof (fw_hash_shift _ _ K) as E13.
  pose proof (fw_lit_bufsize _ _ K) as E14.
  pose proof (fw_pending_buf_size _ _ K) as E15.
  pose proof (fw_sym_end _ _ K) as E16.
  pose proof (fw_gzhead _ _ K) as E17.
  pose proof (fw_method _ _ K) as E18.
  pose proof (fw_level _ _ K) as E19.
  pose proof (fw_strategy _ _ K) as E20.
  pose proof (fw_wrap _ _ K) as E21.
  pose proof (fw_good_match _ _ K) as E22.
  pose proof (fw_max_lazy_match _ _ K) as E23.
  pose proof (fw_nice_match _ _ K) as E24.
  pose proof (fw_max_chain_length _ _ K) as E25.
  pose proof (fw_pending_buf _ _ K) as E26.
  pose proof (fw_dyn_ltree_fc _ _ K) as E27.
  pose proof (fw_dyn_ltree_dl _ _ K) as E28.
  pose proof (fw_dyn_dtree_fc _ _ K) as E29.
  pose proof (fw_dyn_dtree_dl _ _ K) as E30.
  pose proof (fw_bl_tree_fc _ _ K) as E31.
  pose proof (fw_bl_tree_dl _ _ K) as E32.
  pose proof (fw_bl_count _ _ K) as E33.
  pose proof (fw_heap _ _ K) as E34.
  pose proof (fw_depth _ _ K) as E35.
  destruct C; constructor; unfold deflateStateCheck, fbs_tree_lens in *; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9, ?E10, ?E11, ?E12, ?E13, ?E14, ?E15, ?E16, ?E17, ?E18, ?E19, ?E20, ?E21, ?E22, ?E23, ?E24, ?E25, ?E26, ?E27, ?E28, ?E29, ?E30, ?E31, ?E32, ?E33, ?E34, ?E35, ?EW, ?EP, ?EH; assumption.
Qed.

Lemma cty_fw : forall a b, fwzap a = fwzap b -> u8a (ds_window a) -> u16a (ds_prev a) -> u16a (ds_head a) -> cty b -> cty a.
Proof.
  intros a b K TW TP TH C.
  pose proof (fw_dyn_ltree_fc _ _ K) as Q_dyn_ltree_fc.
  pose proof (fw_dyn_ltree_dl _ _ K) as Q_dyn_ltree_dl.
  pose proof (fw_dyn_dtree_fc _ _ K) as Q_dyn_dtree_fc.
  pose proof (fw_dyn_dtree_dl _ _ K) as Q_dyn_dtree_dl.
  pose proof (fw_bl_tree_fc _ _ K) as Q_bl_tree_fc.
  pose proof (fw_bl_tree_dl _ _ K) as Q_bl_tree_dl.
  pose proof (fw_bl_count _ _ K) as Q_bl_count.
  pose proof (fw_depth _ _ K) as Q_depth.
  pose proof (fw_pending_buf _ _ K) as Q_pending_buf.
  pose proof (fw_cs_input _ _ K) as Q_in.
  destruct C; constructor; rewrite ?Q_dyn_ltree_fc, ?Q_dyn_ltree_dl, ?Q_dyn_dtree_fc, ?Q_dyn_dtree_dl, ?Q_bl_tree_fc, ?Q_bl_tree_dl, ?Q_bl_count, ?Q_depth, ?Q_pending_buf, ?Q_in; assumption.
Qed.

Theorem fw_run : forall rm fz ws hs ILEN s, dwin rm fz ws hs ILEN s -> ds_lookahead s < MIN_LOOKAHEAD ->
  let s' := fill_window s in
  dwin rm fz ws hs ILEN s' /\ fwzap s' = fwzap s
  /\ ds_lookahead s <= ds_lookahead s'
  /\ ds_lookahead s' + cs_avail_in (ds_strm s') = ds_lookahead s + cs_avail_in (ds_strm s)
  /\ (cs_avail_in (ds_strm s') = 0 \/ MIN_LOOKAHEAD <= ds_lookahead s')
  /\ ds_strstart s' + MIN_LOOKAHEAD < 2 * ws
  /\ ds_strstart s' - ds_block_start s' = ds_strstart s - ds_block_start s
  /\ wrap32 (ds_strstart s' - 1 - ds_match_start s') = wrap32 (ds_strstart s - 1 - ds_match_start s)
  /\ cs_next_in (ds_strm s') + cs_avail_in (ds_strm s') = cs_next_in (ds_strm s) + cs_avail_in (ds_strm s)
  /\ ((ds_block_start s < 0 -> ds_w_size s - MIN_LOOKAHEAD <= ds_strstart s) ->
      (ds_block_start s' < 0 -> ds_w_size s' - MIN_LOOKAHEAD <= ds_strstart s')).
Proof.
  intros rm fz ws hs ILEN s D Hlook.
  pose proof (dwin_fw_wf _ _ _ _ _ _ D) as HW.
  pose proof D as [C I Ews Ehs Wr Lz Sbusy Il Il32 Ni Ai In Ti Ad Ad1 Ad2].
  pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
  assert (POW : exists k, 0 <= k /\ ws = 2 ^ k).
  { exists (ds_w_bits s). pose proof (cf_wbits _ C) as X. split; [clear -X; lia|]. rewrite <- Ews. exact (cf_wsize _ C). }
  assert (Hhm : 0 <= ds_hash_mask s < 2 ^ 16) by (rewrite (cf_hmask _ C); clear -Sh; lia).
  pose proof (di_ih _ _ _ _ I) as Hih. pose proof (di_look _ _ _ _ I) as Vlook.
  pose proof (fw_loop_facts ws hs 263 s HW Hlook Hhm Hih POW ltac:(unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; change (Z.of_nat 263) with 263; lia)) as LF.
  unfold fill_window. rewrite Ews. cbv zeta in LF.
  remember (fill_window_loop 263 s ws) as s1 eqn:Es1.
  destruct LF as (HW1 & T1 & W1 & IH1 & ST1 & EX1).
  pose proof (fw_high_facts ws hs s1 HW1) as HF. cbv zeta in HF.
  remember (fill_window_high s1) as s2 eqn:Es2.
  destruct HF as (HW2 & Z2 & HWM2 & S2 & L2 & B2 & M2 & IH2 & IN2 & HD2 & PV2 & SM2 & W2 & WS2 & HS2).
  destruct T1 as [Z1 Tbs Tms Thw Tih Tstr1 Tcons Tlook Tin Tad0 Tad2 Thash Tstrle Tnb].
  assert (Z20 : fwzap s2 = fwzap s) by congruence.
  assert (C2 : dcfg s2).
  { apply (dcfg_fw s2 s Z20); [rewrite (wf_wl _ _ _ HW2), (cf_wl _ C), Ews | rewrite (wf_pl _ _ _ HW2), (cf_pl _ C), Ews | rewrite (wf_hl _ _ _ HW2), (cf_hl _ C), Ehs |]; try reflexivity. exact C. }
  assert (T2 : cty s2).
  { apply (cty_fw s2 s Z20); [ | | | exact (di_cty _ _ _ _ I)]; unfold u8a, u16a.
    - rewrite (wf_wl _ _ _ HW2). exact (wf_wb _ _ _ HW2).
    - rewrite (wf_pl _ _ _ HW2). exact (wf_pb _ _ _ HW2).
    - rewrite (wf_hl _ _ _ HW2). exact (wf_hb _ _ _ HW2). }
  pose proof I as [_ Istr Ilook Isl Iins Ibs Ibs0 Ihw Iih Ims Ipm Iml Ipl Ima Ima1 Imt Ifast Ifastpl Islow Islow1 Ihash Isyms Iroom Ibv Ibb Ipend Ipout Ipop Ipo0 Ipobv Ilf Ilive Iinit Igz Ineg Ilk0 Isn0 Iinw Ifl Imas Ips].
  assert (I2 : dinvR rm 0 fz s2).
  { pose proof (fw_level _ _ Z20) as QL. pose proof (fw_strategy _ _ Z20) as QS. pose proof (fw_match_length _ _ Z20) as QML.
    pose proof (fw_prev_length _ _ Z20) as QPL. pose proof (fw_prev_match _ _ Z20) as QPM. pose proof (fw_match_available _ _ Z20) as QMA.
    pose proof (fw_matches _ _ Z20) as QMT. pose proof (fw_sym_next _ _ Z20) as QSN. pose proof (fw_sym_end _ _ Z20) as QSE.
    pose proof (fw_bi_valid _ _ Z20) as QBV. pose proof (fw_bi_buf _ _ Z20) as QBB. pose proof (fw_pending _ _ Z20) as QPD.
    pose proof (fw_pending_out _ _ Z20) as QPO. pose proof (fw_lit_bufsize _ _ Z20) as QLB. pose proof (fw_last_flush _ _ Z20) as QLF.
    pose proof (fw_status _ _ Z20) as QST. pose proof (fw_wrap _ _ Z20) as QW.
    constructor.
    - exact T2.
    - pose proof (wf_ins _ _ _ HW2) as X. clear -X. lia.
    - exact (wf_look _ _ _ HW2).
    - rewrite WS2, (wf_ws _ _ _ HW1). exact (wf_sl _ _ _ HW2).
    - exact (wf_ins _ _ _ HW2).
    - rewrite S2, B2. clear -Tbs Ibs. lia.
    - rewrite QL. intros Hz. exfalso. exact (Lz Hz).
    - rewrite WS2, (wf_ws _ _ _ HW1). rewrite Thw in HWM2. rewrite Ews in Ihw. clear -HWM2 Ihw. lia.
    - rewrite IH2. exact IH1.
    - exact (wf_ms _ _ _ HW2).
    - rewrite QPM. exact Ipm.
    - rewrite QML. exact Iml.
    - rewrite QPL. exact Ipl.
    - rewrite QMA. exact Ima.
    - rewrite QMA, S2, QL. intros Hm HL. apply Tstr1. exact (Ima1 Hm HL).
    - rewrite QMT. exact Imt.
    - unfold lz_strat. rewrite QL, QS, QML. exact Ifast.
    - unfold lz_strat. rewrite QL, QS, QPL. exact Ifastpl.
    - unfold lz_strat in *. rewrite QL, QS, QML, S2, M2, L2, WS2, (wf_ws _ _ _ HW1), Tms.
      intros Fz A B Cm. destruct (Islow Fz A B Cm) as (X1 & X2 & X3). rewrite Ews in X2. split; [apply Tstr1; exact X1|]. split; [exact X2|]. clear -X3 Tlook. lia.
    - unfold lz_strat. rewrite QL, QS, QML. exact Islow1.
    - rewrite QL. intros Hl. apply dhashb0. unfold dhash. rewrite S2, WS2, HD2, PV2, HS2. apply Thash. exact (dhashb0' _ (Ihash Hl)).
    - destruct Isyms as (syms & DS & COV). exists syms. split.
      + eapply dsyms_keep; [exact DS | ..];
          [exact QSN | exact (fw_pending_buf _ _ Z20) | exact QLB | | exact (fw_dyn_ltree_fc _ _ Z20)
          | exact (fw_dyn_dtree_fc _ _ Z20) | exact (fw_bl_tree_fc _ _ Z20) | exact (fw_opt_len _ _ Z20) | exact (fw_static_len _ _ Z20)].
        rewrite WS2, (wf_ws _ _ _ HW1), Ews. reflexivity.
      + rewrite QL, QMA, S2, B2, Tbs. exact COV.
    - rewrite QSN, QSE. exact Iroom.
    - rewrite QBV. exact Ibv.
    - rewrite QBB. exact Ibb.
    - rewrite QPD. exact Ipend.
    - rewrite QPO. exact Ipout.
    - rewrite QPO, QPD, QBV, QLB. exact Ipop.
    - rewrite QPD, QPO. exact Ipo0.
    - rewrite QPO, QBV. exact Ipobv.
    - rewrite QLF. exact Ilf.
    - rewrite QST. exact Ilive.
    - rewrite QST, QPD, QW, QSN. exact Iinit.
    - rewrite QST, QW. exact Igz.
    - rewrite QW. intros Hn. exfalso. clear -Hn Wr. lia.
    - rewrite QL. intros L0. exfalso. exact (Lz L0).
    - rewrite QL. intros L0. exfalso. exact (Lz L0).
    - rewrite QST, QW. intros E. pose proof (Iinw E). clear -H. lia.
    - rewrite QST, Sbusy. unfold BUSY_STATE, FINISH_STATE. intros E; discriminate E.
    - unfold lz_strat. rewrite QMA, QL, QS. exact Imas.
    - rewrite QPD, QSN. exact Ips. }
  split.
  { constructor; try assumption.
    - rewrite WS2, (wf_ws _ _ _ HW1). reflexivity.
    - rewrite HS2, (wf_hs _ _ _ HW1). reflexivity.
    - rewrite W2, W1. exact Wr.
    - rewrite (fw_level _ _ Z20). exact Lz.
    - rewrite (fw_status _ _ Z20). exact Sbusy.
    - rewrite (fw_cs_input _ _ Z20). exact Il.
    - exact (wf_ni _ _ _ HW2).
    - pose proof (wf_ai _ _ _ HW2) as X. clear -X. lia.
    - rewrite SM2, Tin. exact In.
    - exact (wf_ti _ _ _ HW2).
    - pose proof (wf_wrap _ _ _ HW2) as WW. pose proof (wf_ad1 _ _ _ HW2) as A1. pose proof (wf_ad2 _ _ _ HW2) as A2.
      assert (W3 : ds_wrap s2 = 0 \/ ds_wrap s2 = 1 \/ ds_wrap s2 = 2) by (clear -WW; lia).
      destruct W3 as [W0 | [W0 | W0]].
      + rewrite SM2, Tad0 by (rewrite <- W1, <- W2; exact W0). exact Ad.
      + pose proof (A1 W0) as CA. unfold adler_canon in CA. clear -CA. lia.
      + rewrite SM2. apply Tad2; [congruence | apply Ad2; congruence].
    - intros W0. apply adler_ok_canon. exact (wf_ad1 _ _ _ HW2 W0).
    - intros W0. rewrite SM2. apply Tad2; [congruence | apply Ad2; congruence]. }
  split; [exact Z20|]. rewrite L2, S2, B2, SM2, M2, WS2. split; [exact Tlook|]. split; [exact Tcons|]. split; [exact EX1|]. split; [exact ST1|].
  split; [exact Tbs|]. split; [exact Tms|]. split; [exact Tin|]. rewrite (fw_w_size _ _ Z1) in Tnb |- *. rewrite ?Ews in Tnb |- *. exact Tnb.
Qed.
