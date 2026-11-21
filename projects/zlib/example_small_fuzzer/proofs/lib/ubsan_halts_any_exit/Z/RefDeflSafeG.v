(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pow2_bounds : forall a b k, 0 <= a <= k /\ k <= b -> 2 ^ a <= 2 ^ k <= 2 ^ b.
Proof. intros a b k H. split; apply Z.pow_le_mono_r; lia. Qed.

Lemma dwf_sizes : forall s, dwf s ->
  512 <= ds_w_size s <= 32768 /\ 256 <= ds_hash_size s <= 65536 /\ 2048 <= ds_lit_bufsize s <= 32768
  /\ ds_pending_buf_size s = ds_lit_bufsize s * 4 /\ 0 <= ds_hash_shift s < 32.
Proof.
  intros s D. pose proof (df_wbits _ D) as Hwb. pose proof (df_hbits _ D) as Hhb.
  rewrite (df_wsize _ D), (df_hsize _ D), (df_lbs _ D), (df_pbs _ D), (df_hshift _ D), (df_lbs _ D). unfold MIN_MATCH.
  pose proof (pow2_bounds 9 15 (ds_w_bits s) ltac:(lia)) as A. change (2 ^ 9) with 512 in A. change (2 ^ 15) with 32768 in A.
  pose proof (pow2_bounds 8 16 (ds_hash_bits s) ltac:(lia)) as B. change (2 ^ 8) with 256 in B. change (2 ^ 16) with 65536 in B.
  pose proof (pow2_bounds 11 15 (ds_hash_bits s - 1) ltac:(lia)) as C. change (2 ^ 11) with 2048 in C. change (2 ^ 15) with 32768 in C.
  assert (0 <= (ds_hash_bits s + 3 - 1) / 3 < 32) by (Z.to_euclidean_division_equations; lia).
  repeat split; lia.
Qed.

Lemma dwf_set_strm : forall s c, dwf s -> dwf (set_strm s c).
Proof. intros s c D. destruct D; constructor; dsred; assumption. Qed.

Lemma dwf_DWF : forall s, dwf s -> 0 <= cs_avail_out (ds_strm s) < 2 ^ 32 -> RefDeflFast1.DWF s.
Proof.
  intros s D Hao. pose proof (dwf_sizes s D) as (A & B & C & _).
  constructor; [exact (df_wl _ D) | exact (df_pl _ D) | exact (df_hl _ D) | exact (df_bl _ D) | lia | lia | lia | exact Hao].
Qed.

Lemma dwf_fw_wf : forall s, dwf s ->
  0 <= ds_wrap s ->
  0 <= cs_next_in (ds_strm s) -> 0 <= cs_avail_in (ds_strm s) < 2 ^ 32 ->
  cs_next_in (ds_strm s) + cs_avail_in (ds_strm s) <= arr_len (cs_input (ds_strm s)) ->
  0 <= cs_total_in (ds_strm s) < 2 ^ 64 -> 0 <= cs_adler (ds_strm s) < 2 ^ 64 ->
  (forall i, 0 <= i < arr_len (cs_input (ds_strm s)) -> 0 <= arr_get (cs_input (ds_strm s)) i < 256) ->
  fw_wf (ds_w_size s) (ds_hash_size s) s.
Proof.
  intros s D Hwr Hni Hai Hil Hti Had Hib. pose proof (dwf_sizes s D) as (A & B & C & _ & E).
  constructor; try reflexivity; try assumption; try lia.
  - exact (df_wl _ D).
  - exact (df_wsz _ D).
  - exact (df_pl _ D).
  - exact (df_wmask _ D).
  - exact (df_hl _ D).
  - exact (df_hmask _ D).
  - exact (df_ins _ D).
  - exact (df_look _ D).
  - exact (df_sl _ D).
  - exact (df_ms _ D).
  - exact (df_ih _ D).
  - exact (df_hw _ D).
  - pose proof (df_wrap _ D). lia.
  - exact (df_wb _ D).
  - exact (df_pb _ D).
  - exact (df_hb _ D).
Qed.
