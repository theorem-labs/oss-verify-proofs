(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma arr_set_range16 : forall (a : arr) i v nn,
  (forall j, 0 <= j < nn -> 0 <= arr_get a j < 65536) ->
  forall j, 0 <= j < nn -> 0 <= arr_get (arr_set a i (wrap16 v)) j < 65536.
Proof.
  intros a i v nn H j Hj. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply H; exact Hj].
Qed.

Lemma arr_set_range8 : forall (a : arr) i v nn,
  (forall j, 0 <= j < nn -> 0 <= arr_get a j < 256) ->
  forall j, 0 <= j < nn -> 0 <= arr_get (arr_set a i (wrap8 v)) j < 256.
Proof.
  intros a i v nn H j Hj. rewrite arr_get_set. destruct (_ && _); [apply wrap8_range | apply H; exact Hj].
Qed.

Definition tally_keep (a b : deflate_state) : Prop :=
  ds_strm b = ds_strm a /\ ds_window b = ds_window a /\ ds_prev b = ds_prev a /\ ds_head b = ds_head a
  /\ ds_lookahead b = ds_lookahead a /\ ds_strstart b = ds_strstart a /\ ds_block_start b = ds_block_start a
  /\ ds_match_length b = ds_match_length a /\ ds_match_start b = ds_match_start a /\ ds_prev_length b = ds_prev_length a
  /\ ds_prev_match b = ds_prev_match a /\ ds_match_available b = ds_match_available a
  /\ ds_pending b = ds_pending a /\ ds_pending_out b = ds_pending_out a /\ ds_bi_valid b = ds_bi_valid a /\ ds_bi_buf b = ds_bi_buf a
  /\ ds_lit_bufsize b = ds_lit_bufsize a /\ ds_pending_buf_size b = ds_pending_buf_size a /\ ds_sym_end b = ds_sym_end a
  /\ ds_w_size b = ds_w_size a /\ ds_hash_size b = ds_hash_size a /\ ds_w_mask b = ds_w_mask a /\ ds_hash_mask b = ds_hash_mask a
  /\ ds_hash_shift b = ds_hash_shift a /\ ds_ins_h b = ds_ins_h a /\ ds_insert b = ds_insert a /\ ds_window_size b = ds_window_size a
  /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a /\ ds_max_lazy_match b = ds_max_lazy_match a
  /\ ds_good_match b = ds_good_match a /\ ds_nice_match b = ds_nice_match a /\ ds_max_chain_length b = ds_max_chain_length a
  /\ ds_status b = ds_status a /\ ds_wrap b = ds_wrap a /\ ds_high_water b = ds_high_water a /\ ds_matches b = ds_matches a
  /\ arr_len (ds_pending_buf b) = arr_len (ds_pending_buf a).

Lemma tally_lit_facts : forall s c,
  let r := tr_tally_lit s c in
  tally_keep s (fst r)
  /\ ds_sym_next (fst r) = ds_sym_next s + 3
  /\ snd r = (ds_sym_next s + 3 =? ds_sym_end s)
  /\ ds_dyn_dtree_fc (fst r) = ds_dyn_dtree_fc s /\ ds_bl_tree_fc (fst r) = ds_bl_tree_fc s
  /\ ds_dyn_ltree_fc (fst r) = arr_set (ds_dyn_ltree_fc s) (wrap8 c) (wrap16 (arr_get (ds_dyn_ltree_fc s) (wrap8 c) + 1))
  /\ (forall nn, (forall j, 0 <= j < nn -> 0 <= arr_get (ds_dyn_ltree_fc s) j < 65536) ->
               forall j, 0 <= j < nn -> 0 <= arr_get (ds_dyn_ltree_fc (fst r)) j < 65536)
  /\ (forall nn, (forall j, 0 <= j < nn -> 0 <= arr_get (ds_pending_buf s) j < 256) ->
               forall j, 0 <= j < nn -> 0 <= arr_get (ds_pending_buf (fst r)) j < 256).
Proof.
  intros s c r. subst r. unfold tr_tally_lit, sym_buf_set, set_Freq, Freq, tree_fc, set_tree_fc. dsred.
  split. { unfold tally_keep. dsred. rewrite !arr_len_set. repeat split; reflexivity. }
  split; [lia|]. split; [f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split. { intros nn H. apply arr_set_range16. exact H. }
  intros nn H. apply arr_set_range8. apply arr_set_range8. apply arr_set_range8. exact H.
Qed.

Lemma tally_dist_facts : forall s distance length,
  let r := tr_tally_dist s distance length in
  tally_keep s (fst r)
  /\ ds_sym_next (fst r) = ds_sym_next s + 3
  /\ snd r = (ds_sym_next s + 3 =? ds_sym_end s)
  /\ ds_bl_tree_fc (fst r) = ds_bl_tree_fc s
  /\ (forall nn, (forall j, 0 <= j < nn -> 0 <= arr_get (ds_dyn_ltree_fc s) j < 65536) ->
               forall j, 0 <= j < nn -> 0 <= arr_get (ds_dyn_ltree_fc (fst r)) j < 65536)
  /\ (forall nn, (forall j, 0 <= j < nn -> 0 <= arr_get (ds_dyn_dtree_fc s) j < 65536) ->
               forall j, 0 <= j < nn -> 0 <= arr_get (ds_dyn_dtree_fc (fst r)) j < 65536)
  /\ (forall nn, (forall j, 0 <= j < nn -> 0 <= arr_get (ds_pending_buf s) j < 256) ->
               forall j, 0 <= j < nn -> 0 <= arr_get (ds_pending_buf (fst r)) j < 256).
Proof.
  intros s distance length r. subst r. unfold tr_tally_dist, sym_buf_set, set_Freq, Freq, tree_fc, set_tree_fc. dsred.
  split. { unfold tally_keep. dsred. rewrite !arr_len_set. repeat split; reflexivity. }
  split; [lia|]. split; [f_equal; lia|]. split; [reflexivity|].
  split. { intros nn H. apply arr_set_range16. exact H. }
  split. { intros nn H. apply arr_set_range16. exact H. }
  intros nn H. apply arr_set_range8. apply arr_set_range8. apply arr_set_range8. exact H.
Qed.

Lemma insert_string_facts : forall s str,
  let r := insert_string s str in
  let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) in
  snd r = arr_get (ds_head s) h
  /\ ds_ins_h (fst r) = h
  /\ ds_head (fst r) = arr_set (ds_head s) h (wrap16 str)
  /\ ds_prev (fst r) = arr_set (ds_prev s) (Z.land str (ds_w_mask s)) (arr_get (ds_head s) h)
  /\ ds_strm (fst r) = ds_strm s /\ ds_window (fst r) = ds_window s /\ ds_lookahead (fst r) = ds_lookahead s
  /\ ds_strstart (fst r) = ds_strstart s /\ ds_block_start (fst r) = ds_block_start s
  /\ ds_match_length (fst r) = ds_match_length s /\ ds_sym_next (fst r) = ds_sym_next s
  /\ ds_dyn_ltree_fc (fst r) = ds_dyn_ltree_fc s /\ ds_dyn_dtree_fc (fst r) = ds_dyn_dtree_fc s
  /\ ds_pending (fst r) = ds_pending s /\ ds_pending_buf (fst r) = ds_pending_buf s
  /\ ds_bi_valid (fst r) = ds_bi_valid s /\ ds_bi_buf (fst r) = ds_bi_buf s
  /\ ds_insert (fst r) = ds_insert s /\ ds_prev_length (fst r) = ds_prev_length s /\ ds_match_start (fst r) = ds_match_start s
  /\ (0 <= ds_hash_mask s -> 0 <= h <= ds_hash_mask s).
Proof.
  intros s str r h. subst r h. unfold insert_string. dsred.
  repeat (split; [reflexivity|]).
  intros Hm. exact (update_hash_range s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) Hm).
Qed.
