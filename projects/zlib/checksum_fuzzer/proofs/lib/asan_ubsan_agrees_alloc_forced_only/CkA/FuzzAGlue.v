(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkWalk CkHarness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition fz_chunk (bs : list Z) (off k : Z) : list Z := firstn (Z.to_nat k) (skipn (Z.to_nat off) bs).
Definition fz_pre (bs : list Z) (off : Z) : list Z := firstn (Z.to_nat off) bs.

Lemma fz_chunk_length : forall bs off k, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length bs) ->
  Z.of_nat (length (fz_chunk bs off k)) = k.
Proof. intros bs off k H0 Hk H. unfold fz_chunk. rewrite length_firstn, length_skipn. lia. Qed.

Lemma fz_chunk_bytes : forall bs off k, bytes bs -> bytes (fz_chunk bs off k).
Proof. intros. unfold fz_chunk. apply bytes_firstn, bytes_skipn. assumption. Qed.

Lemma fz_pre_bytes : forall bs off, bytes bs -> bytes (fz_pre bs off).
Proof. intros. unfold fz_pre. apply bytes_firstn. assumption. Qed.

Lemma fz_pre_chunk : forall bs off k, 0 <= off -> 0 <= k -> fz_pre bs off ++ fz_chunk bs off k = fz_pre bs (off + k).
Proof.
  intros bs off k H0 Hk. unfold fz_pre, fz_chunk. rewrite chunk_app. f_equal. lia.
Qed.

Lemma fz_pre_all : forall bs off, Z.of_nat (length bs) <= off -> fz_pre bs off = bs.
Proof. intros bs off H. unfold fz_pre. apply firstn_all2. lia. Qed.

Lemma fz_pre_0 : forall bs, fz_pre bs 0 = [].
Proof. reflexivity. Qed.

Lemma fz_crc_step : forall a bs off k, bytes bs -> 0 <= off -> 0 <= k ->
  crc32_z_model a (crc32_spec 0 (fz_pre bs off)) (fz_chunk bs off k) = crc32_spec 0 (fz_pre bs (off + k)).
Proof.
  intros a bs off k HB H0 Hk.
  rewrite (harness_crc_stream a _ _ (fz_pre_bytes bs off HB) (fz_chunk_bytes bs off k HB)).
  rewrite fz_pre_chunk by lia. reflexivity.
Qed.

Lemma fz_assert1 : forall a0 a1 bs off k, bytes bs -> 0 <= off -> 1 <= k < 2^29 -> off + k <= Z.of_nat (length bs) ->
  crc32_z_model a1 (crc32_spec 0 (fz_pre bs off)) (fz_chunk bs off k)
  = crc32_combine_op (crc32_spec 0 (fz_pre bs off)) (crc32_z_model a0 0 (fz_chunk bs off k)) (crc32_combine_gen k).
Proof.
  intros a0 a1 bs off k HB H0 Hk HL.
  rewrite <- (fz_chunk_length bs off k) at 3 by lia.
  apply harness_assert1; [apply fz_chunk_bytes; exact HB | apply crc32_spec_range, fz_pre_bytes; exact HB |].
  unfold Zlen. rewrite fz_chunk_length by lia. lia.
Qed.

Lemma fz_crc_whole : forall a bs, bytes bs -> crc32_z_model a 0 bs = crc32_spec 0 bs.
Proof. intros a bs HB. apply (harness_crc_whole a bs HB). Qed.

Lemma fz_adler_step : forall bs off k, bytes bs -> 0 <= off -> 0 <= k ->
  adler32_z_model (adler_spec 1 (fz_pre bs off)) (fz_chunk bs off k) = adler_spec 1 (fz_pre bs (off + k)).
Proof.
  intros bs off k HB H0 Hk.
  rewrite (harness_adler_stream _ _ (fz_pre_bytes bs off HB) (fz_chunk_bytes bs off k HB)).
  rewrite fz_pre_chunk by lia. reflexivity.
Qed.

Lemma fz_adler_whole : forall bs, bytes bs -> adler32_z_model 1 bs = adler_spec 1 bs.
Proof. intros bs HB. apply (harness_adler_whole bs HB). Qed.

Lemma fz_crc_range : forall bs off, bytes bs -> 0 <= crc32_spec 0 (fz_pre bs off) < 2^32.
Proof. intros. apply crc32_spec_range, fz_pre_bytes. assumption. Qed.

Lemma fz_adler_range : forall bs off, 0 <= adler_spec 1 (fz_pre bs off) < 2^32.
Proof. intros. apply adler_spec_1_range. Qed.

Lemma fz_tail_len : forall n b q off, 1 <= b -> off = b * q -> 0 <= q -> off <= n -> n < off + b -> n mod b = n - off.
Proof.
  intros n b q off Hb -> Hq Hle Hlt. symmetry. apply (Z.mod_unique n b q (n - b * q)); lia.
Qed.

Lemma land_M32_small : forall x, 0 <= x < 2^32 -> Z.land x 4294967295 = x.
Proof.
  intros x Hx. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma swrap32_small : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.
