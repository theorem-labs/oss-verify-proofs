(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Export DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition olist (ob : option blk) (sz : Z) : list (blk * Z) :=
  match ob with Some b => [(b, sz)] | None => [] end.

Definition dblocks (ds : deflate_state) : list (blk * Z) :=
  olist (ds_pending_buf_blk ds) (ds_lit_bufsize ds * 4)
  ++ olist (ds_head_blk ds) (ds_hash_size ds * 2)
  ++ olist (ds_prev_blk ds) (ds_w_size ds * 2)
  ++ olist (ds_window_blk ds) (ds_w_size ds * 2)
  ++ [(ds_self_blk ds, SIZEOF_deflate_state)].

Record dwf (s : deflate_state) : Prop := DWF {
  df_status : deflateStateCheck s = false;
  df_blkw : ds_window_blk s <> None;
  df_blkp : ds_prev_blk s <> None;
  df_blkh : ds_head_blk s <> None;
  df_blkb : ds_pending_buf_blk s <> None;
  df_wbits : 9 <= ds_w_bits s <= 15;
  df_wsize : ds_w_size s = 2 ^ ds_w_bits s;
  df_wmask : ds_w_mask s = ds_w_size s - 1;
  df_wsz : ds_window_size s = 2 * ds_w_size s;
  df_hbits : 12 <= ds_hash_bits s <= 16;
  df_hsize : ds_hash_size s = 2 ^ ds_hash_bits s;
  df_hmask : ds_hash_mask s = ds_hash_size s - 1;
  df_hshift : ds_hash_shift s = (ds_hash_bits s + MIN_MATCH - 1) / MIN_MATCH;
  df_lbs : ds_lit_bufsize s = 2 ^ (ds_hash_bits s - 1);
  df_pbs : ds_pending_buf_size s = ds_lit_bufsize s * 4;
  df_symend : ds_sym_end s = (ds_lit_bufsize s - 1) * 3;
  df_wl : arr_len (ds_window s) = 2 * ds_w_size s;
  df_pl : arr_len (ds_prev s) = ds_w_size s;
  df_hl : arr_len (ds_head s) = ds_hash_size s;
  df_bl : arr_len (ds_pending_buf s) = ds_lit_bufsize s * 4;
  df_tl : tree_lens s;
  df_gzhead : ds_gzhead s = 0;
  df_method : ds_method s = Z_DEFLATED;
  df_level : 0 <= ds_level s <= 9;
  df_strategy : 0 <= ds_strategy s <= Z_FIXED;
  df_wrap : - 2 <= ds_wrap s <= 2;
  df_strstart : 0 <= ds_strstart s < 2 ^ 32;
  df_ins : 0 <= ds_insert s <= ds_strstart s;
  df_look : 0 <= ds_lookahead s;
  df_sl : ds_strstart s + ds_lookahead s <= 2 * ds_w_size s;
  df_ms : 0 <= ds_match_start s < 2 ^ 32;
  df_ih : 0 <= ds_ins_h s < 2 ^ 32;
  df_hw : 0 <= ds_high_water s < 2 ^ 64;
  df_wb : forall i, 0 <= i < 2 * ds_w_size s -> 0 <= arr_get (ds_window s) i < 256;
  df_pb : forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev s) i < 65536;
  df_hb : forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get (ds_head s) i < 65536;
  df_bb : forall i, 0 <= i < ds_lit_bufsize s * 4 -> 0 <= arr_get (ds_pending_buf s) i < 256;
  df_st4 : ds_status s = 42 \/ ds_status s = 57 \/ ds_status s = 113 \/ ds_status s = 666;
  df_lf : - 2 <= ds_last_flush s <= 5;
  df_pend : 0 <= ds_pending_out s /\ 0 <= ds_pending s /\ ds_pending_out s + ds_pending s <= ds_lit_bufsize s * 4;
  df_bi : 0 <= ds_bi_valid s <= 16 /\ 0 <= ds_bi_buf s < 2 ^ 16
}.

