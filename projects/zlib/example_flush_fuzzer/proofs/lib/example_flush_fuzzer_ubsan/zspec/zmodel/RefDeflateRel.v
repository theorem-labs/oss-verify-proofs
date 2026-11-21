(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate TreeModel AdlerModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require DeflateInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

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
  df_hbits : 8 <= ds_hash_bits s <= 16;
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
  df_wrap : -2 <= ds_wrap s <= 2;
  df_strstart : 0 <= ds_strstart s < 2 ^ 32;
  df_ins : 0 <= ds_insert s <= ds_strstart s;
  df_look : 0 <= ds_lookahead s;
  df_sl : ds_strstart s + ds_lookahead s <= 2 * ds_w_size s;
  df_ms : 0 <= ds_match_start s < 2 ^ 32;
  df_ih : 0 <= ds_ins_h s < 2 ^ 32;
  df_hw : 0 <= ds_high_water s < 2 ^ 64;
  df_bs : - 2 ^ 63 <= ds_block_start s < 2 ^ 63;
  df_wbv : forall i, 0 <= i < 2 * ds_w_size s -> 0 <= arr_get (ds_window s) i < 256;
  df_pbv : forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev s) i < 65536;
  df_hbv : forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get (ds_head s) i < 65536
}.

Definition DADLER (ds : deflate_state) (a : Z) : Prop :=
  (0 <= a < 2 ^ 32 /\ (ds_wrap ds = 1 -> adler_canon a)) /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.DeflateInv.DI ds.




Definition zcall_ok (zc : ZCall) : Prop :=
  (0 <= zs_total_in (zc_strm zc) < 2 ^ 64 /\ 0 <= zs_total_out (zc_strm zc) < 2 ^ 64
   /\ 0 <= zs_adler (zc_strm zc) < 2 ^ 64 /\ - 2 ^ 31 <= zs_data_type (zc_strm zc) < 2 ^ 31)
  /\ 0 <= zc_avail_out zc < 2 ^ 32 /\ zlength (zc_input zc) < 2 ^ 32
  /\ Forall (fun b => 0 <= b < 256) (zc_input zc).

Definition DOK (s0 : deflate_state) (zc : ZCall) (flush : Z) : Prop :=
  dwf s0 /\ zcall_ok zc /\ 0 <= flush < 16 /\ DADLER s0 (zs_adler (zc_strm zc)).
