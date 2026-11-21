(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Record ds_ptrs : Type := DSP { p_strm : Z; p_window : Z; p_prev : Z; p_head : Z; p_pending_buf : Z }.

Definition dsl_SIZE : Z := 5952.

Definition dsl_layout : list (Z * nat) := [
  (0, 8%nat) (* [comment removed for export] *);
  (8, 4%nat) (* [comment removed for export] *);
  (16, 8%nat) (* [comment removed for export] *);
  (24, 8%nat) (* [comment removed for export] *);
  (32, 8%nat) (* [comment removed for export] *);
  (40, 8%nat) (* [comment removed for export] *);
  (48, 4%nat) (* [comment removed for export] *);
  (56, 8%nat) (* [comment removed for export] *);
  (64, 8%nat) (* [comment removed for export] *);
  (72, 1%nat) (* [comment removed for export] *);
  (76, 4%nat) (* [comment removed for export] *);
  (80, 4%nat) (* [comment removed for export] *);
  (84, 4%nat) (* [comment removed for export] *);
  (88, 4%nat) (* [comment removed for export] *);
  (96, 8%nat) (* [comment removed for export] *);
  (104, 8%nat) (* [comment removed for export] *);
  (112, 8%nat) (* [comment removed for export] *);
  (120, 8%nat) (* [comment removed for export] *);
  (128, 4%nat) (* [comment removed for export] *);
  (132, 4%nat) (* [comment removed for export] *);
  (136, 4%nat) (* [comment removed for export] *);
  (140, 4%nat) (* [comment removed for export] *);
  (144, 4%nat) (* [comment removed for export] *);
  (152, 8%nat) (* [comment removed for export] *);
  (160, 4%nat) (* [comment removed for export] *);
  (164, 4%nat) (* [comment removed for export] *);
  (168, 4%nat) (* [comment removed for export] *);
  (172, 4%nat) (* [comment removed for export] *);
  (176, 4%nat) (* [comment removed for export] *);
  (180, 4%nat) (* [comment removed for export] *);
  (184, 4%nat) (* [comment removed for export] *);
  (188, 4%nat) (* [comment removed for export] *);
  (192, 4%nat) (* [comment removed for export] *);
  (196, 4%nat) (* [comment removed for export] *);
  (200, 4%nat) (* [comment removed for export] *);
  (204, 4%nat) (* [comment removed for export] *);
  (208, 4%nat) (* [comment removed for export] *);
  (2904, 8%nat) (* [comment removed for export] *);
  (2912, 4%nat) (* [comment removed for export] *);
  (2920, 8%nat) (* [comment removed for export] *);
  (2928, 8%nat) (* [comment removed for export] *);
  (2936, 4%nat) (* [comment removed for export] *);
  (2944, 8%nat) (* [comment removed for export] *);
  (2952, 8%nat) (* [comment removed for export] *);
  (2960, 4%nat) (* [comment removed for export] *);
  (2968, 8%nat) (* [comment removed for export] *);
  (5300, 4%nat) (* [comment removed for export] *);
  (5304, 4%nat) (* [comment removed for export] *);
  (5888, 8%nat) (* [comment removed for export] *);
  (5896, 4%nat) (* [comment removed for export] *);
  (5900, 4%nat) (* [comment removed for export] *);
  (5904, 4%nat) (* [comment removed for export] *);
  (5912, 8%nat) (* [comment removed for export] *);
  (5920, 8%nat) (* [comment removed for export] *);
  (5928, 4%nat) (* [comment removed for export] *);
  (5932, 4%nat) (* [comment removed for export] *);
  (5936, 2%nat) (* [comment removed for export] *);
  (5940, 4%nat) (* [comment removed for export] *);
  (5944, 8%nat) (* [comment removed for export] *)].

Definition dsl_vals (SL SD SB : Z) (ds : deflate_state) (p : ds_ptrs) (S : Z) : list Z := [
  p_strm p (* [comment removed for export] *);
  ds_status ds (* [comment removed for export] *);
  p_pending_buf p (* [comment removed for export] *);
  ds_pending_buf_size ds (* [comment removed for export] *);
  p_pending_buf p + ds_pending_out ds (* [comment removed for export] *);
  ds_pending ds (* [comment removed for export] *);
  ds_wrap ds (* [comment removed for export] *);
  ds_gzhead ds (* [comment removed for export] *);
  ds_gzindex ds (* [comment removed for export] *);
  ds_method ds (* [comment removed for export] *);
  ds_last_flush ds (* [comment removed for export] *);
  ds_w_size ds (* [comment removed for export] *);
  ds_w_bits ds (* [comment removed for export] *);
  ds_w_mask ds (* [comment removed for export] *);
  p_window p (* [comment removed for export] *);
  ds_window_size ds (* [comment removed for export] *);
  p_prev p (* [comment removed for export] *);
  p_head p (* [comment removed for export] *);
  ds_ins_h ds (* [comment removed for export] *);
  ds_hash_size ds (* [comment removed for export] *);
  ds_hash_bits ds (* [comment removed for export] *);
  ds_hash_mask ds (* [comment removed for export] *);
  ds_hash_shift ds (* [comment removed for export] *);
  ds_block_start ds (* [comment removed for export] *);
  ds_match_length ds (* [comment removed for export] *);
  ds_prev_match ds (* [comment removed for export] *);
  ds_match_available ds (* [comment removed for export] *);
  ds_strstart ds (* [comment removed for export] *);
  ds_match_start ds (* [comment removed for export] *);
  ds_lookahead ds (* [comment removed for export] *);
  ds_prev_length ds (* [comment removed for export] *);
  ds_max_chain_length ds (* [comment removed for export] *);
  ds_max_lazy_match ds (* [comment removed for export] *);
  ds_level ds (* [comment removed for export] *);
  ds_strategy ds (* [comment removed for export] *);
  ds_good_match ds (* [comment removed for export] *);
  ds_nice_match ds (* [comment removed for export] *);
  S + 212 (* [comment removed for export] *);
  ds_l_max_code ds (* [comment removed for export] *);
  SL (* [comment removed for export] *);
  S + 2504 (* [comment removed for export] *);
  ds_d_max_code ds (* [comment removed for export] *);
  SD (* [comment removed for export] *);
  S + 2748 (* [comment removed for export] *);
  ds_bl_max_code ds (* [comment removed for export] *);
  SB (* [comment removed for export] *);
  ds_heap_len ds (* [comment removed for export] *);
  ds_heap_max ds (* [comment removed for export] *);
  p_pending_buf p + ds_lit_bufsize ds (* [comment removed for export] *);
  ds_lit_bufsize ds (* [comment removed for export] *);
  ds_sym_next ds (* [comment removed for export] *);
  ds_sym_end ds (* [comment removed for export] *);
  ds_opt_len ds (* [comment removed for export] *);
  ds_static_len ds (* [comment removed for export] *);
  ds_matches ds (* [comment removed for export] *);
  ds_insert ds (* [comment removed for export] *);
  ds_bi_buf ds (* [comment removed for export] *);
  ds_bi_valid ds (* [comment removed for export] *);
  ds_high_water ds (* [comment removed for export] *)].

Section WithImage.
Variables SL SD SB : Z.
End WithImage.
