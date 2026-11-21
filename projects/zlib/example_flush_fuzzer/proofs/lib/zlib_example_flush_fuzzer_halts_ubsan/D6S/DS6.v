(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Export DSLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Definition ds6_SIZE : Z := 5968.
  Definition ds6_layout : list (Z * nat) := dsl_layout.
Definition ds6_vals (ds : deflate_state) (p : ds_ptrs) (S : Z) : list Z := dsl_vals 168672 168704 168736 ds p S.
Definition ds6_scalars (mem : word -> option byte) (S : Z) (p : ds_ptrs) (ds : deflate_state) : Prop :=
  fields s6_segs mem S ds6_layout (ds6_vals ds p S).
Lemma ds6_layout_within : layout_within ds6_layout ds6_SIZE = true.
Proof. exact dsl_layout_within. Qed.
Definition ds6_arrays (mem : word -> option byte) (S : Z) (ds : deflate_state) : Prop := dsl_arrays s6_segs mem S ds.
Definition ds6_windowA (mem : word -> option byte) (p : ds_ptrs) (ds : deflate_state) : Prop :=
  cells s6_segs mem (p_window p) 1 1 (arr_len (ds_window ds)) (arr_get (ds_window ds)).
Definition ds6_prevA (mem : word -> option byte) (p : ds_ptrs) (ds : deflate_state) : Prop :=
  cells s6_segs mem (p_prev p) 2 2 (arr_len (ds_prev ds)) (arr_get (ds_prev ds)).
Definition ds6_headA (mem : word -> option byte) (p : ds_ptrs) (ds : deflate_state) : Prop :=
  cells s6_segs mem (p_head p) 2 2 (arr_len (ds_head ds)) (arr_get (ds_head ds)).
Definition ds6_pendA (mem : word -> option byte) (p : ds_ptrs) (ds : deflate_state) : Prop :=
  cells s6_segs mem (p_pending_buf p) 1 1 (arr_len (ds_pending_buf ds)) (arr_get (ds_pending_buf ds)).


Lemma ds6_strm : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 0) 8 (p_strm p).
Proof. exact (dsl_strm s6_segs 168672 168704 168736). Qed.

Lemma ds6_status : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 8) 4 (ds_status ds).
Proof. exact (dsl_status s6_segs 168672 168704 168736). Qed.

Lemma ds6_pending_buf : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 16) 8 (p_pending_buf p).
Proof. exact (dsl_pending_buf s6_segs 168672 168704 168736). Qed.


Lemma ds6_pending_out : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 32) 8 (p_pending_buf p + ds_pending_out ds).
Proof. exact (dsl_pending_out s6_segs 168672 168704 168736). Qed.

Lemma ds6_pending : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 40) 8 (ds_pending ds).
Proof. exact (dsl_pending s6_segs 168672 168704 168736). Qed.

Lemma ds6_wrap : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 48) 4 (ds_wrap ds).
Proof. exact (dsl_wrap s6_segs 168672 168704 168736). Qed.




Lemma ds6_last_flush : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 76) 4 (ds_last_flush ds).
Proof. exact (dsl_last_flush s6_segs 168672 168704 168736). Qed.

Lemma ds6_w_size : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 80) 4 (ds_w_size ds).
Proof. exact (dsl_w_size s6_segs 168672 168704 168736). Qed.

Lemma ds6_w_bits : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 84) 4 (ds_w_bits ds).
Proof. exact (dsl_w_bits s6_segs 168672 168704 168736). Qed.

Lemma ds6_w_mask : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 88) 4 (ds_w_mask ds).
Proof. exact (dsl_w_mask s6_segs 168672 168704 168736). Qed.

Lemma ds6_window : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 96) 8 (p_window p).
Proof. exact (dsl_window s6_segs 168672 168704 168736). Qed.


Lemma ds6_prev : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 112) 8 (p_prev p).
Proof. exact (dsl_prev s6_segs 168672 168704 168736). Qed.

Lemma ds6_head : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 120) 8 (p_head p).
Proof. exact (dsl_head s6_segs 168672 168704 168736). Qed.

Lemma ds6_ins_h : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 128) 4 (ds_ins_h ds).
Proof. exact (dsl_ins_h s6_segs 168672 168704 168736). Qed.

Lemma ds6_hash_size : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 132) 4 (ds_hash_size ds).
Proof. exact (dsl_hash_size s6_segs 168672 168704 168736). Qed.


Lemma ds6_hash_mask : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 140) 4 (ds_hash_mask ds).
Proof. exact (dsl_hash_mask s6_segs 168672 168704 168736). Qed.

Lemma ds6_hash_shift : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 144) 4 (ds_hash_shift ds).
Proof. exact (dsl_hash_shift s6_segs 168672 168704 168736). Qed.

Lemma ds6_block_start : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 152) 8 (ds_block_start ds).
Proof. exact (dsl_block_start s6_segs 168672 168704 168736). Qed.

Lemma ds6_match_length : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 160) 4 (ds_match_length ds).
Proof. exact (dsl_match_length s6_segs 168672 168704 168736). Qed.

Lemma ds6_prev_match : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 164) 4 (ds_prev_match ds).
Proof. exact (dsl_prev_match s6_segs 168672 168704 168736). Qed.

Lemma ds6_match_available : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 168) 4 (ds_match_available ds).
Proof. exact (dsl_match_available s6_segs 168672 168704 168736). Qed.

Lemma ds6_strstart : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 172) 4 (ds_strstart ds).
Proof. exact (dsl_strstart s6_segs 168672 168704 168736). Qed.

Lemma ds6_match_start : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 176) 4 (ds_match_start ds).
Proof. exact (dsl_match_start s6_segs 168672 168704 168736). Qed.

Lemma ds6_lookahead : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 180) 4 (ds_lookahead ds).
Proof. exact (dsl_lookahead s6_segs 168672 168704 168736). Qed.

Lemma ds6_prev_length : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 184) 4 (ds_prev_length ds).
Proof. exact (dsl_prev_length s6_segs 168672 168704 168736). Qed.

Lemma ds6_max_chain_length : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 188) 4 (ds_max_chain_length ds).
Proof. exact (dsl_max_chain_length s6_segs 168672 168704 168736). Qed.

Lemma ds6_max_lazy_match : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 192) 4 (ds_max_lazy_match ds).
Proof. exact (dsl_max_lazy_match s6_segs 168672 168704 168736). Qed.

Lemma ds6_level : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 196) 4 (ds_level ds).
Proof. exact (dsl_level s6_segs 168672 168704 168736). Qed.

Lemma ds6_strategy : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 200) 4 (ds_strategy ds).
Proof. exact (dsl_strategy s6_segs 168672 168704 168736). Qed.

Lemma ds6_good_match : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 204) 4 (ds_good_match ds).
Proof. exact (dsl_good_match s6_segs 168672 168704 168736). Qed.

Lemma ds6_nice_match : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 208) 4 (ds_nice_match ds).
Proof. exact (dsl_nice_match s6_segs 168672 168704 168736). Qed.












Lemma ds6_sym_buf : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 5888) 8 (p_pending_buf p + ds_lit_bufsize ds).
Proof. exact (dsl_sym_buf s6_segs 168672 168704 168736). Qed.


Lemma ds6_sym_next : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 5900) 4 (ds_sym_next ds).
Proof. exact (dsl_sym_next s6_segs 168672 168704 168736). Qed.

Lemma ds6_sym_end : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 5904) 4 (ds_sym_end ds).
Proof. exact (dsl_sym_end s6_segs 168672 168704 168736). Qed.




Lemma ds6_insert : forall mem S p ds, ds6_scalars mem S p ds -> cell s6_segs mem (S + 5932) 4 (ds_insert ds).
Proof. exact (dsl_insert s6_segs 168672 168704 168736). Qed.
















































Lemma ds6_scalars_agree : forall F mem mem' S p ds,
  ds6_scalars mem S p ds -> agree_out F mem mem' -> disj_franges F S ds6_SIZE ->
  0 <= S -> S + ds6_SIZE <= 2 ^ 64 ->
  ds6_scalars mem' S p ds.
Proof. exact (dsl_scalars_agree s6_segs 168672 168704 168736). Qed.
End FXG.
