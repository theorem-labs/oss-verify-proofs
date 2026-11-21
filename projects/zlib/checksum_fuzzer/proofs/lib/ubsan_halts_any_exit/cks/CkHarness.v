(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.cks Require Import
  CkTables CkModel CkXt CkMultmodp CkMathCrc CkMathAdler.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma harness_crc_init : crc32_spec 0 [] = 0.
Proof. apply crc32_spec_nil. lia. Qed.

Lemma harness_adler_init : adler_spec 1 [] = 1.
Proof. apply adler_spec_nil. apply adler_ok_1. Qed.


Theorem harness_crc_stream : forall a A B, bytes A -> bytes B ->
  crc32_z_model a (crc32_spec 0 A) B = crc32_spec 0 (A ++ B).
Proof.
  intros a A B HA HB. rewrite crc32_z_model_spec by exact HB.
  apply crc32_spec_app. exact HA.
Qed.

Theorem harness_assert1 : forall a0 a1 c B, bytes B -> 0 <= c < 2 ^ 32 -> 1 <= Zlen B < 2 ^ 29 ->
  crc32_z_model a1 c B = crc32_combine_op c (crc32_z_model a0 0 B) (crc32_combine_gen (Zlen B)).
Proof.
  intros a0 a1 c B HB Hc HL. rewrite !crc32_z_model_spec by exact HB.
  symmetry. apply crc32_combine_op_spec; [exact HB | exact Hc | lia].
Qed.





Theorem harness_assert5 : forall crc1 crc2 len, crc1 = crc2 ->
  crc32_combine crc1 crc2 len = crc32_combine_op crc2 crc1 (crc32_combine_gen len).
Proof. intros crc1 crc2 len ->. apply crc32_combine_gen_op. Qed.


Theorem crc32_combine_op_range : forall crc1 crc2 op, 0 <= crc1 < 2 ^ 32 ->
  0 <= crc32_combine_op crc1 crc2 op < 2 ^ 32.
Proof.
  (* 1.4: the op = 0 branch is 0; crc1 is masked before multmodp *)
  intros crc1 crc2 op Hc. unfold crc32_combine_op.
  destruct (op =? 0); [lia|].
  apply lxor_bound32.
  - apply multmodp_range. rewrite land_M32. apply Z.mod_pos_bound. lia.
  - rewrite land_M32. apply Z.mod_pos_bound. lia.
Qed.

Theorem crc32_combine_range : forall crc1 crc2 len, 0 <= crc1 < 2 ^ 32 ->
  0 <= crc32_combine crc1 crc2 len < 2 ^ 32.
Proof. intros. rewrite crc32_combine_gen_op. apply crc32_combine_op_range. assumption. Qed.

Theorem crc32_combine_gen_range : forall len, 0 <= crc32_combine_gen len < 2 ^ 32.
Proof.
  (* 1.4: a negative length gives 0 *)
  intros. unfold crc32_combine_gen, crc32_combine_gen64. destruct (len <? 0); [lia|]. apply x2nmodp_range_any.
Qed.

Theorem crc32_combine_gen_nz : forall len, 0 <= len < 2 ^ 29 ->
  crc32_combine_gen len mod 2 ^ 32 <> 0.
Proof.
  intros len Hl. unfold crc32_combine_gen, crc32_combine_gen64.
  (* 1.4: the length is not negative here *)
  rewrite (proj2 (Z.ltb_ge len 0)) by lia.
  apply x2nmodp_nz_mod; lia.
Qed.



Theorem harness_adler_stream : forall A B, bytes A -> bytes B ->
  adler32_z_model (adler_spec 1 A) B = adler_spec 1 (A ++ B).
Proof.
  intros A B HA HB.
  rewrite adler32_z_model_spec by (try apply adler_spec_ok; try apply adler_ok_1; exact HB).
  apply adler_spec_app. apply adler_ok_1.
Qed.

Theorem harness_adler_whole : forall D, bytes D -> adler32_model 1 D = adler_spec 1 D.
Proof. intros D HD. unfold adler32_model. apply adler32_z_model_spec; [apply adler_ok_1 | exact HD]. Qed.



Theorem adler_spec_1_range : forall D, 0 <= adler_spec 1 D < 2 ^ 32.
Proof. intros. apply adler_spec_range. apply adler_ok_1. Qed.




















