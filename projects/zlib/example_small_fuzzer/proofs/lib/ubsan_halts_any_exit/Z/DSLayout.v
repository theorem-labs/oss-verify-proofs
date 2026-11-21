(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.

Module ItableRod.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition tab_u16 (a : arr) (n : nat) : bool :=
  forallb (fun j => (0 <=? arr_get a (Z.of_nat j)) && (arr_get a (Z.of_nat j) <? 65536)) (seq 0 n).

Lemma tab_u16_sound : forall a n i, tab_u16 a n = true -> 0 <= i < Z.of_nat n -> 0 <= arr_get a i < 65536.
Proof.
  intros a n i H Hi. unfold tab_u16 in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Section Rod.

End Rod.
End ItableRod.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record ds_ptrs : Type := DSP { p_strm : Z; p_window : Z; p_prev : Z; p_head : Z; p_pending_buf : Z }.

Definition dsl_SIZE : Z := 5952.

Definition dsl_layout : list (Z * nat) := [
  (0, 8%nat) ;
  (8, 4%nat) ;
  (16, 8%nat) ;
  (24, 8%nat) ;
  (32, 8%nat) ;
  (40, 8%nat) ;
  (48, 4%nat) ;
  (56, 8%nat) ;
  (64, 8%nat) ;
  (72, 1%nat) ;
  (76, 4%nat) ;
  (80, 4%nat) ;
  (84, 4%nat) ;
  (88, 4%nat) ;
  (96, 8%nat) ;
  (104, 8%nat) ;
  (112, 8%nat) ;
  (120, 8%nat) ;
  (128, 4%nat) ;
  (132, 4%nat) ;
  (136, 4%nat) ;
  (140, 4%nat) ;
  (144, 4%nat) ;
  (152, 8%nat) ;
  (160, 4%nat) ;
  (164, 4%nat) ;
  (168, 4%nat) ;
  (172, 4%nat) ;
  (176, 4%nat) ;
  (180, 4%nat) ;
  (184, 4%nat) ;
  (188, 4%nat) ;
  (192, 4%nat) ;
  (196, 4%nat) ;
  (200, 4%nat) ;
  (204, 4%nat) ;
  (208, 4%nat) ;
  (2904, 8%nat) ;
  (2912, 4%nat) ;
  (2920, 8%nat) ;
  (2928, 8%nat) ;
  (2936, 4%nat) ;
  (2944, 8%nat) ;
  (2952, 8%nat) ;
  (2960, 4%nat) ;
  (2968, 8%nat) ;
  (5300, 4%nat) ;
  (5304, 4%nat) ;
  (5888, 8%nat) ;
  (5896, 4%nat) ;
  (5900, 4%nat) ;
  (5904, 4%nat) ;
  (5912, 8%nat) ;
  (5920, 8%nat) ;
  (5928, 4%nat) ;
  (5932, 4%nat) ;
  (5936, 2%nat) ;
  (5940, 4%nat) ;
  (5944, 8%nat) ].

Definition dsl_vals (SL SD SB : Z) (ds : deflate_state) (p : ds_ptrs) (S : Z) : list Z := [
  p_strm p ;
  ds_status ds ;
  p_pending_buf p ;
  ds_pending_buf_size ds ;
  p_pending_buf p + ds_pending_out ds ;
  ds_pending ds ;
  ds_wrap ds ;
  ds_gzhead ds ;
  ds_gzindex ds ;
  ds_method ds ;
  ds_last_flush ds ;
  ds_w_size ds ;
  ds_w_bits ds ;
  ds_w_mask ds ;
  p_window p ;
  ds_window_size ds ;
  p_prev p ;
  p_head p ;
  ds_ins_h ds ;
  ds_hash_size ds ;
  ds_hash_bits ds ;
  ds_hash_mask ds ;
  ds_hash_shift ds ;
  ds_block_start ds ;
  ds_match_length ds ;
  ds_prev_match ds ;
  ds_match_available ds ;
  ds_strstart ds ;
  ds_match_start ds ;
  ds_lookahead ds ;
  ds_prev_length ds ;
  ds_max_chain_length ds ;
  ds_max_lazy_match ds ;
  ds_level ds ;
  ds_strategy ds ;
  ds_good_match ds ;
  ds_nice_match ds ;
  S + 212 ;
  ds_l_max_code ds ;
  SL ;
  S + 2504 ;
  ds_d_max_code ds ;
  SD ;
  S + 2748 ;
  ds_bl_max_code ds ;
  SB ;
  ds_heap_len ds ;
  ds_heap_max ds ;
  p_pending_buf p + ds_lit_bufsize ds ;
  ds_lit_bufsize ds ;
  ds_sym_next ds ;
  ds_sym_end ds ;
  ds_opt_len ds ;
  ds_static_len ds ;
  ds_matches ds ;
  ds_insert ds ;
  ds_bi_buf ds ;
  ds_bi_valid ds ;
  ds_high_water ds ].

Lemma dsl_layout_within : layout_within dsl_layout dsl_SIZE = true.
Proof. vm_compute. reflexivity. Qed.

Section WithImage.
Variables SL SD SB : Z.
End WithImage.
