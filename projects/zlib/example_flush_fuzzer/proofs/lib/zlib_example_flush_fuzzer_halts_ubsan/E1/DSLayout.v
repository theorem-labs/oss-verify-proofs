(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Record ds_ptrs : Type := DSP { p_strm : Z; p_window : Z; p_prev : Z; p_head : Z; p_pending_buf : Z }.

Definition dsl_SIZE : Z := 5968.

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
  (5952, 8%nat) (* 1.4: high_water moves 5944 -> 5952; bi_used (5944, 4) and slid (5960, 4)
                   are junk bytes no field names, as in w5's P/Z_drep (only deflateUsed / deflateCopy read them) *)].

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
Variable segs : list Segment.
Variables SL SD SB : Z.

Definition dsl_scalars (mem : word -> option byte) (S : Z) (p : ds_ptrs) (ds : deflate_state) : Prop :=
  fields segs mem S dsl_layout (dsl_vals SL SD SB ds p S).

Definition dsl_arrays (mem : word -> option byte) (S : Z) (ds : deflate_state) : Prop :=
  cells segs mem (S + 212) 4 2 573 (arr_get (ds_dyn_ltree_fc ds))
  /\ cells segs mem (S + 214) 4 2 573 (arr_get (ds_dyn_ltree_dl ds))
  /\ cells segs mem (S + 2504) 4 2 61 (arr_get (ds_dyn_dtree_fc ds))
  /\ cells segs mem (S + 2506) 4 2 61 (arr_get (ds_dyn_dtree_dl ds))
  /\ cells segs mem (S + 2748) 4 2 39 (arr_get (ds_bl_tree_fc ds))
  /\ cells segs mem (S + 2750) 4 2 39 (arr_get (ds_bl_tree_dl ds))
  /\ cells segs mem (S + 2976) 2 2 16 (arr_get (ds_bl_count ds))
  /\ cells segs mem (S + 3008) 4 4 573 (arr_get (ds_heap ds))
  /\ cells segs mem (S + 5308) 1 1 573 (arr_get (ds_depth ds)).

Definition dsl_windowA (mem : word -> option byte) (p : ds_ptrs) (ds : deflate_state) : Prop :=
  cells segs mem (p_window p) 1 1 (arr_len (ds_window ds)) (arr_get (ds_window ds)).
Definition dsl_prevA (mem : word -> option byte) (p : ds_ptrs) (ds : deflate_state) : Prop :=
  cells segs mem (p_prev p) 2 2 (arr_len (ds_prev ds)) (arr_get (ds_prev ds)).
Definition dsl_headA (mem : word -> option byte) (p : ds_ptrs) (ds : deflate_state) : Prop :=
  cells segs mem (p_head p) 2 2 (arr_len (ds_head ds)) (arr_get (ds_head ds)).
Definition dsl_pendA (mem : word -> option byte) (p : ds_ptrs) (ds : deflate_state) : Prop :=
  cells segs mem (p_pending_buf p) 1 1 (arr_len (ds_pending_buf ds)) (arr_get (ds_pending_buf ds)).


Lemma dsl_strm : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 0) 8 (p_strm p).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 0 0 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_status : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 8) 4 (ds_status ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 1 8 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_pending_buf : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 16) 8 (p_pending_buf p).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 2 16 8%nat _ H eq_refl eq_refl). Qed.


Lemma dsl_pending_out : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 32) 8 (p_pending_buf p + ds_pending_out ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 4 32 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_pending : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 40) 8 (ds_pending ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 5 40 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_wrap : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 48) 4 (ds_wrap ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 6 48 4%nat _ H eq_refl eq_refl). Qed.




Lemma dsl_last_flush : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 76) 4 (ds_last_flush ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 10 76 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_w_size : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 80) 4 (ds_w_size ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 11 80 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_w_bits : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 84) 4 (ds_w_bits ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 12 84 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_w_mask : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 88) 4 (ds_w_mask ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 13 88 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_window : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 96) 8 (p_window p).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 14 96 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_window_size : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 104) 8 (ds_window_size ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 15 104 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_prev : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 112) 8 (p_prev p).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 16 112 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_head : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 120) 8 (p_head p).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 17 120 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_ins_h : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 128) 4 (ds_ins_h ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 18 128 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_hash_size : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 132) 4 (ds_hash_size ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 19 132 4%nat _ H eq_refl eq_refl). Qed.


Lemma dsl_hash_mask : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 140) 4 (ds_hash_mask ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 21 140 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_hash_shift : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 144) 4 (ds_hash_shift ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 22 144 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_block_start : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 152) 8 (ds_block_start ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 23 152 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_match_length : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 160) 4 (ds_match_length ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 24 160 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_prev_match : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 164) 4 (ds_prev_match ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 25 164 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_match_available : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 168) 4 (ds_match_available ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 26 168 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_strstart : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 172) 4 (ds_strstart ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 27 172 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_match_start : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 176) 4 (ds_match_start ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 28 176 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_lookahead : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 180) 4 (ds_lookahead ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 29 180 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_prev_length : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 184) 4 (ds_prev_length ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 30 184 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_max_chain_length : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 188) 4 (ds_max_chain_length ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 31 188 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_max_lazy_match : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 192) 4 (ds_max_lazy_match ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 32 192 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_level : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 196) 4 (ds_level ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 33 196 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_strategy : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 200) 4 (ds_strategy ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 34 200 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_good_match : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 204) 4 (ds_good_match ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 35 204 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_nice_match : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 208) 4 (ds_nice_match ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 36 208 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_l_desc_dyn_tree : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 2904) 8 (S + 212).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 37 2904 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_l_desc_max_code : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 2912) 4 (ds_l_max_code ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 38 2912 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_l_desc_stat_desc : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 2920) 8 (SL).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 39 2920 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_d_desc_dyn_tree : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 2928) 8 (S + 2504).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 40 2928 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_d_desc_max_code : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 2936) 4 (ds_d_max_code ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 41 2936 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_d_desc_stat_desc : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 2944) 8 (SD).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 42 2944 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_bl_desc_dyn_tree : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 2952) 8 (S + 2748).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 43 2952 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_bl_desc_max_code : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 2960) 4 (ds_bl_max_code ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 44 2960 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_bl_desc_stat_desc : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 2968) 8 (SB).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 45 2968 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_heap_len : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 5300) 4 (ds_heap_len ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 46 5300 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_heap_max : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 5304) 4 (ds_heap_max ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 47 5304 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_sym_buf : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 5888) 8 (p_pending_buf p + ds_lit_bufsize ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 48 5888 8%nat _ H eq_refl eq_refl). Qed.


Lemma dsl_sym_next : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 5900) 4 (ds_sym_next ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 50 5900 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_sym_end : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 5904) 4 (ds_sym_end ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 51 5904 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_opt_len : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 5912) 8 (ds_opt_len ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 52 5912 8%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_static_len : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 5920) 8 (ds_static_len ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 53 5920 8%nat _ H eq_refl eq_refl). Qed.


Lemma dsl_insert : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 5932) 4 (ds_insert ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 55 5932 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_bi_buf : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 5936) 2 (ds_bi_buf ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 56 5936 2%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_bi_valid : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 5940) 4 (ds_bi_valid ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 57 5940 4%nat _ H eq_refl eq_refl). Qed.

Lemma dsl_high_water : forall mem S p ds, dsl_scalars mem S p ds -> cell segs mem (S + 5952) 8 (ds_high_water ds).
Proof. intros mem S p ds H. exact (fields_nth segs mem S _ _ 58 5952 8%nat _ H eq_refl eq_refl). Qed.


Lemma dsl_upd_status : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 8)) (Z_to_le_bytes 4 v)) S p (set_status ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 1 8 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.


Lemma dsl_upd_pending : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 40)) (Z_to_le_bytes 8 v)) S p (set_pending ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 5 40 8%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_wrap : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 48)) (Z_to_le_bytes 4 v)) S p (set_wrap ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 6 48 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.




Lemma dsl_upd_last_flush : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 76)) (Z_to_le_bytes 4 v)) S p (set_last_flush ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 10 76 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.





Lemma dsl_upd_ins_h : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 128)) (Z_to_le_bytes 4 v)) S p (set_ins_h ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 18 128 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.





Lemma dsl_upd_block_start : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 152)) (Z_to_le_bytes 8 v)) S p (set_block_start ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 23 152 8%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_match_length : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 160)) (Z_to_le_bytes 4 v)) S p (set_match_length ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 24 160 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_prev_match : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 164)) (Z_to_le_bytes 4 v)) S p (set_prev_match ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 25 164 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_match_available : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 168)) (Z_to_le_bytes 4 v)) S p (set_match_available ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 26 168 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_strstart : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 172)) (Z_to_le_bytes 4 v)) S p (set_strstart ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 27 172 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_match_start : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 176)) (Z_to_le_bytes 4 v)) S p (set_match_start ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 28 176 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_lookahead : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 180)) (Z_to_le_bytes 4 v)) S p (set_lookahead ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 29 180 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_prev_length : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 184)) (Z_to_le_bytes 4 v)) S p (set_prev_length ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 30 184 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.







Lemma dsl_upd_heap_len : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 5300)) (Z_to_le_bytes 4 v)) S p (set_heap_len ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 46 5300 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_heap_max : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 5304)) (Z_to_le_bytes 4 v)) S p (set_heap_max ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 47 5304 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_sym_next : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 5900)) (Z_to_le_bytes 4 v)) S p (set_sym_next ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 50 5900 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.


Lemma dsl_upd_opt_len : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 5912)) (Z_to_le_bytes 8 v)) S p (set_opt_len ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 52 5912 8%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_static_len : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 5920)) (Z_to_le_bytes 8 v)) S p (set_static_len ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 53 5920 8%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_matches : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 5928)) (Z_to_le_bytes 4 v)) S p (set_matches ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 54 5928 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_insert : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 5932)) (Z_to_le_bytes 4 v)) S p (set_insert ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 55 5932 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_bi_buf : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 5936)) (Z_to_le_bytes 2 v)) S p (set_bi_buf ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 56 5936 2%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_bi_valid : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 5940)) (Z_to_le_bytes 4 v)) S p (set_bi_valid ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 57 5940 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_high_water : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 5952)) (Z_to_le_bytes 8 v)) S p (set_high_water ds v).
Proof.
  intros mem S p ds v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 58 5952 8%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

(* 1.4: a write to bytes that no field of a layout names keeps the fields.
   layout_avoids L o n: the range [o, o + n) meets no (o', w') of L. *)
Fixpoint layout_avoids (L : list (Z * nat)) (o n : Z) : bool :=
  match L with
  | [] => true
  | (o', w') :: L' => ((o + n <=? o') || (o' + Z.of_nat w' <=? o)) && layout_avoids L' o n
  end.

Lemma fields_write_gap : forall mem S L vs size (o : Z) bs,
  fields segs mem S L vs -> layout_within L size = true -> layout_avoids L o (Z.of_nat (length bs)) = true ->
  0 <= S -> S + size <= 2 ^ 64 -> 0 <= o -> o + Z.of_nat (length bs) <= size ->
  fields segs (wbytes mem (zw (S + o)) bs) S L vs.
Proof.
  intros mem S L. induction L as [|[o' w'] L' IH]; intros vs size o bs Hf HL HA HS HSz Ho Hon.
  - destruct vs; [exact I | destruct Hf].
  - destruct vs as [|v vs']; [destruct Hf|]. destruct Hf as [Hc Hf'].
    cbn [layout_within] in HL. apply andb_prop in HL as [HL HL']. apply andb_prop in HL as [H0 H1].
    apply Z.leb_le in H0. apply Z.leb_le in H1.
    cbn [layout_avoids] in HA. apply andb_prop in HA as [HA HA'].
    split; [| exact (IH vs' size o bs Hf' HL' HA' HS HSz Ho Hon)].
    apply orb_prop in HA as [HA|HA]; apply Z.leb_le in HA; (apply cell_write_other; [exact Hc | lia ..]).
Qed.

(* bi_used (int, 5944) and slid (int, 5960): any 4-byte store there keeps dsl_scalars *)
Lemma dsl_upd_bi_used : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 5944)) (Z_to_le_bytes 4 v)) S p ds.
Proof.
  intros mem S p ds v H HS0 HS1.
  apply (fields_write_gap mem S _ _ dsl_SIZE 5944 _ H dsl_layout_within); rewrite ?length_Z_to_le_bytes;
    [vm_compute; reflexivity | lia | lia | lia | unfold dsl_SIZE; lia].
Qed.

Lemma dsl_upd_slid : forall mem S p ds v,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars (wbytes mem (zw (S + 5960)) (Z_to_le_bytes 4 v)) S p ds.
Proof.
  intros mem S p ds v H HS0 HS1.
  apply (fields_write_gap mem S _ _ dsl_SIZE 5960 _ H dsl_layout_within); rewrite ?length_Z_to_le_bytes;
    [vm_compute; reflexivity | lia | lia | lia | unfold dsl_SIZE; lia].
Qed.

Lemma dsl_scalars_frame : forall mem S p ds (b : Z) bs,
  dsl_scalars mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (S + dsl_SIZE <= b \/ b + Z.of_nat (length bs) <= S) ->
  dsl_scalars (wbytes mem (zw b) bs) S p ds.
Proof.
  intros mem S p ds b bs H HS0 HS1 Hb0 Hb1 Hd.
  exact (fields_write_other segs mem S _ _ dsl_SIZE b bs H dsl_layout_within HS0 HS1 Hb0 Hb1 Hd).
Qed.

Lemma dsl_scalars_agree : forall F mem mem' S p ds,
  dsl_scalars mem S p ds -> agree_out F mem mem' -> disj_franges F S dsl_SIZE ->
  0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_scalars mem' S p ds.
Proof.
  intros F mem mem' S p ds H Hag Hd HS0 HS1.
  exact (fields_agree_out segs F mem mem' S _ _ dsl_SIZE H dsl_layout_within Hag Hd HS0 HS1).
Qed.

End WithImage.
End FXG.
