(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition dkeep (s0 s1 : deflate_state) : Prop :=
  ds_self_blk s1 = ds_self_blk s0 /\ ds_window_blk s1 = ds_window_blk s0 /\ ds_prev_blk s1 = ds_prev_blk s0
  /\ ds_head_blk s1 = ds_head_blk s0 /\ ds_pending_buf_blk s1 = ds_pending_buf_blk s0
  /\ ds_w_size s1 = ds_w_size s0 /\ ds_hash_size s1 = ds_hash_size s0 /\ ds_lit_bufsize s1 = ds_lit_bufsize s0.

Definition zpost_ok (zc : ZCall) (st : cstrm) (rc : Z) : Prop :=
  (0 <= cs_next_in st /\ 0 <= cs_avail_in st /\ cs_next_in st + cs_avail_in st = zlength (zc_input zc))
  /\ (0 <= cs_avail_out st /\ cs_avail_out st + zlength (cs_out_rev st) = zc_avail_out zc)
  /\ cs_total_out st = wrap64 (zs_total_out (zc_strm zc) + zlength (cs_out_rev st))
  /\ (0 <= cs_total_in st < 2 ^ 64 /\ 0 <= cs_total_out st < 2 ^ 64 /\ 0 <= cs_adler st < 2 ^ 64
      /\ - 2 ^ 31 <= cs_data_type st < 2 ^ 31)
  /\ Forall (fun b => 0 <= b < 256) (cs_out_rev st)
  /\ - 2 ^ 31 <= rc < 2 ^ 31.



Lemma cs_output_rev : forall st, cs_output st = rev (cs_out_rev st).
Proof. intros st. unfold cs_output. rewrite rev_append_rev, app_nil_r. reflexivity. Qed.
Lemma zlength_cs_output : forall st, zlength (cs_output st) = zlength (cs_out_rev st).
Proof. intros st. rewrite cs_output_rev. unfold zlength. rewrite length_rev. reflexivity. Qed.
Lemma zlength_of_nat : forall {X} (l : list X), zlength l = Z.of_nat (length l).
Proof. reflexivity. Qed.
