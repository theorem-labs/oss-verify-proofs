(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record INVG (s : deflate_state) : Prop := {
  ig_wsize : ds_w_size s = 32768;
  ig_wmask : ds_w_mask s = 32767;
  ig_wbits : ds_w_bits s = 15;
  ig_wsz : ds_window_size s = 65536;
  ig_hsize : ds_hash_size s = 32768;
  ig_hmask : ds_hash_mask s = 32767;
  ig_hbits : ds_hash_bits s = 15;
  ig_hshift : ds_hash_shift s = 5;
  ig_lbs : ds_lit_bufsize s = 16384;
  ig_pbs : ds_pending_buf_size s = 65536;
  ig_symend : ds_sym_end s = 49149;
  ig_wl : arr_len (ds_window s) = 65536;
  ig_pl : arr_len (ds_prev s) = 32768;
  ig_hl : arr_len (ds_head s) = 32768;
  ig_bl : arr_len (ds_pending_buf s) = 65536;
  ig_tl : arr_len (ds_dyn_ltree_fc s) = 573 /\ arr_len (ds_dyn_ltree_dl s) = 573
          /\ arr_len (ds_dyn_dtree_fc s) = 61 /\ arr_len (ds_dyn_dtree_dl s) = 61
          /\ arr_len (ds_bl_tree_fc s) = 39 /\ arr_len (ds_bl_tree_dl s) = 39
          /\ arr_len (ds_bl_count s) = 16 /\ arr_len (ds_heap s) = 573 /\ arr_len (ds_depth s) = 573;
  ig_ss : 0 <= ds_strstart s;
  ig_look : 0 <= ds_lookahead s;
  ig_ins : 0 <= ds_insert s <= ds_strstart s;
  ig_sl : ds_strstart s + ds_lookahead s <= 65536;
  ig_hw : 0 <= ds_high_water s <= 65536;
  ig_ain : 0 <= cs_avail_in (ds_strm s);
  ig_ol : 0 <= ds_opt_len s < 2 ^ 64;
  ig_stl : 0 <= ds_static_len s < 2 ^ 64;
  ig_ml : 0 <= ds_match_length s <= 258;
  ig_pvl : 0 <= ds_prev_length s <= 258;
  ig_strat : ds_strategy s <> 2 /\ ds_strategy s <> 3;
  ig_pend : 0 <= ds_pending s;
  ig_po : ds_pending s = 0 -> ds_pending_out s = 0;
  ig_aout : 0 <= cs_avail_out (ds_strm s)
}.

Lemma INVG_set_status s v : INVG s -> INVG (set_status s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_wrap s v : INVG s -> INVG (set_wrap s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.

Lemma INVG_set_last_flush s v : INVG s -> INVG (set_last_flush s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_ins_h s v : INVG s -> INVG (set_ins_h s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_block_start s v : INVG s -> INVG (set_block_start s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_match_length s v : 0 <= v <= 258 -> INVG s -> INVG (set_match_length s v).
Proof. intros; match goal with I : INVG s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.
Lemma INVG_set_match_available s v : INVG s -> INVG (set_match_available s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_prev_length s v : 0 <= v <= 258 -> INVG s -> INVG (set_prev_length s v).
Proof. intros; match goal with I : INVG s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.
Lemma INVG_set_max_chain_length s v : INVG s -> INVG (set_max_chain_length s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_max_lazy_match s v : INVG s -> INVG (set_max_lazy_match s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_level s v : INVG s -> INVG (set_level s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_strategy s v : v <> 2 /\ v <> 3 -> INVG s -> INVG (set_strategy s v).
Proof. intros; match goal with I : INVG s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.
Lemma INVG_set_good_match s v : INVG s -> INVG (set_good_match s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_nice_match s v : INVG s -> INVG (set_nice_match s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_matches s v : INVG s -> INVG (set_matches s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_bi_buf s v : INVG s -> INVG (set_bi_buf s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_bi_valid s v : INVG s -> INVG (set_bi_valid s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.

Lemma INVG_set_pending s v : 0 <= v -> (v = 0 -> ds_pending_out s = 0) -> INVG s -> INVG (set_pending s v).
Proof. intros; match goal with I : INVG s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.

Lemma INVG_set_match_start s v : INVG s -> INVG (set_match_start s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_prev_match s v : INVG s -> INVG (set_prev_match s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INVG_set_strstart s v : 0 <= v -> ds_insert s <= v -> v + ds_lookahead s <= 65536 -> INVG s -> INVG (set_strstart s v).
Proof. intros; match goal with I : INVG s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.
Lemma INVG_set_lookahead s v : 0 <= v -> ds_strstart s + v <= 65536 -> INVG s -> INVG (set_lookahead s v).
Proof. intros; match goal with I : INVG s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.
Lemma INVG_set_insert s v : 0 <= v <= ds_strstart s -> INVG s -> INVG (set_insert s v).
Proof. intros; match goal with I : INVG s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.
Lemma INVG_set_high_water s v : 0 <= v <= 65536 -> INVG s -> INVG (set_high_water s v).
Proof. intros; match goal with I : INVG s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.

Lemma INVG_set_strm s v : 0 <= cs_avail_in v -> 0 <= cs_avail_out v -> INVG s -> INVG (set_strm s v).
Proof. intros; match goal with I : INVG s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.

Lemma INVG_of_INV s : INV s -> INVG s.
Proof. intros I. destruct I; constructor; try assumption. rewrite iv_strat. split; discriminate. Qed.
