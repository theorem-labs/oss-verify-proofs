(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Export RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Export DeflateOverlay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Record fb_entry (s : deflate_state) (last : Z) : Prop := {
  fe_last : 0 <= last <= 1;
  (* [comment removed for export] *)
  fe_diff : 0 <= ds_strstart s - ds_block_start s < 2 ^ 32;
  fe_bs : - 2 ^ 63 <= ds_block_start s;
  (* [comment removed for export] *)
  fe_str : 0 <= ds_strstart s <= 2 * ds_w_size s;
  fe_look : 0 <= ds_lookahead s <= 2 * ds_w_size s;
  fe_ws : 256 <= ds_w_size s <= 32768;
  fe_wl : arr_len (ds_window s) = 2 * ds_w_size s;
  fe_wb : forall j, 0 <= j < 2 * ds_w_size s -> 0 <= arr_get (ds_window s) j < 256;
  (* [comment removed for export] *)
  fe_level : 1 <= ds_level s <= 9;
  fe_strategy : 0 <= ds_strategy s <= 4;
  fe_dt : - 2 ^ 31 <= cs_data_type (ds_strm s) < 2 ^ 31;
  fe_lbs : 2048 <= ds_lit_bufsize s <= 32768;
  fe_pbl : arr_len (ds_pending_buf s) = ds_lit_bufsize s * 4;
  fe_symend : ds_sym_end s = (ds_lit_bufsize s - 1) * 3;
  (* [comment removed for export] *)
  fe_pending : ds_pending s = 0;
  fe_pout : ds_pending_out s = 0;
  fe_biv : 0 <= ds_bi_valid s <= 7;
  fe_bib : 0 <= ds_bi_buf s < 2 ^ 16;
  fe_pbb : forall i, 0 <= i < arr_len (ds_pending_buf s) -> 0 <= arr_get (ds_pending_buf s) i < 256;
  fe_tout : 0 <= cs_total_out (ds_strm s) < 2 ^ 64;
  fe_aout : 0 <= cs_avail_out (ds_strm s) < 2 ^ 32;
  (* [comment removed for export] *)
  fe_sn : ds_sym_next s = 3 * nsym s;
  fe_nsym : 0 <= nsym s <= ds_lit_bufsize s - 1;
  fe_syms : forall j, 0 <= j < nsym s -> sym_okb s j;
  fe_hist : freq_hist s;
  fe_optlen : ds_opt_len s = 0;
  fe_statlen : ds_static_len s = 0;
  (* [comment removed for export] *)
  fe_tl : tree_lens s;
  fe_fc : forall t i, 0 <= arr_get (tree_fc s t) i < 65536;
  fe_dl : forall t i, 0 <= arr_get (tree_dl s t) i < 65536;
  fe_depth : forall i, 0 <= arr_get (ds_depth s) i < 256;
  fe_blc : forall i, 0 <= i < 16 -> 0 <= arr_get (ds_bl_count s) i < 65536;
  (* [comment removed for export] *)
  fe_lbs2 : exists k, ds_lit_bufsize s = 2 ^ k }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record fb_post (s : deflate_state) (last : Z) (s8 : deflate_state) : Prop := {
  (* [comment removed for export] *)
  fp_lz : lz_view s8 = lz_view s;
  fp_keep : forall (A : Type) (g : deflate_state -> A), keeps g true true -> g s8 = g (tfb_X0 s);
  fp_strm : exists dt, ds_strm s8 = cset_data_type (ds_strm s) dt /\ - 2 ^ 31 <= dt < 2 ^ 31;
  (* [comment removed for export] *)
  fp_sn : ds_sym_next s8 = 0;
  fp_matches : ds_matches s8 = 0;
  fp_optlen : ds_opt_len s8 = 0;
  fp_statlen : ds_static_len s8 = 0;
  fp_ltree : forall c, 0 <= c < L_CODES -> arr_get (ds_dyn_ltree_fc s8) c = zind (c =? END_BLOCK);
  fp_dtree : forall d, 0 <= d < D_CODES -> arr_get (ds_dyn_dtree_fc s8) d = 0;
  fp_bltree : forall b, 0 <= b < BL_CODES -> arr_get (ds_bl_tree_fc s8) b = 0;
  fp_tl : tree_lens s8;
  fp_fc : forall t i, 0 <= arr_get (tree_fc s8 t) i < 65536;
  fp_dl : forall t i, 0 <= arr_get (tree_dl s8 t) i < 65536;
  fp_depth : forall i, 0 <= arr_get (ds_depth s8) i < 256;
  fp_blc : forall i, 0 <= i < 16 -> 0 <= arr_get (ds_bl_count s8) i < 65536;
  (* [comment removed for export] *)
  fp_pending : 0 <= ds_pending s8 /\ ds_pending s8 + 2 <= ds_lit_bufsize s * 4;
  fp_pout : ds_pending_out s8 = 0;
  fp_biv : 0 <= ds_bi_valid s8 <= 16;
  fp_biv_last : last <> 0 -> ds_bi_valid s8 <= 7;
  fp_bib : 0 <= ds_bi_buf s8 < 2 ^ 16;
  fp_pbl : arr_len (ds_pending_buf s8) = ds_lit_bufsize s * 4;
  fp_pbb : forall i, 0 <= i < arr_len (ds_pending_buf s8) -> 0 <= arr_get (ds_pending_buf s8) i < 256 }.

(* [comment removed for export] *)
Definition FB_CALL : Prop :=
  forall s last, fb_entry s last ->
    flush_ok s last /\ fb_post s last (tr_flush_block s (fb_buf s) (fb_len s) last).
