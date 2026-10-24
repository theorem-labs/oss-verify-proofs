(** Exact four- and twenty-byte suffix laws for the five-chain loop. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcLib CrcModel CrcWordModel CrcBraidModel CrcChunks CrcLinearBasis.
Import ListNotations.
Open Scope Z_scope.
Opaque csteps.
Lemma raw_four_at : forall inp i q,
  0 <= i -> i+4 <= Z.of_nat (length inp) ->
  raw_crc (firstn 4 (skipn (Z.to_nat i) inp)) q = word_update q (bv_unsigned (bword4 inp i)).
Proof.
  intros inp i q Hi HL. unfold word_update,bword4.
  assert (LEN : length (firstn 4 (skipn (Z.to_nat i) inp)) = 4%nat).
  { rewrite length_firstn,length_skipn. lia. }
  rewrite raw_four_bytes_value by exact LEN.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_nonneg (firstn 4 (skipn (Z.to_nat i) inp))) as H0.
  pose proof (bytes_le_to_Z_bound (firstn 4 (skipn (Z.to_nat i) inp))) as H1.
  rewrite LEN in H1. rewrite bv_wrap_small;[reflexivity|].
  change (bv_modulus 64) with (2^64). lia.
Qed.
Lemma raw_suffix_four : forall inp i q,
  0 <= i -> i+4 <= Z.of_nat (length inp) ->
  raw_crc (skipn (Z.to_nat i) inp) q =
  raw_crc (skipn (Z.to_nat (i+4)) inp) (word_update q (bv_unsigned (bword4 inp i))).
Proof.
  intros inp i q Hi HL. rewrite (raw_suffix_chunk inp i 4 q Hi),raw_four_at by assumption. reflexivity.
Qed.
Theorem raw_suffix_twenty : forall inp i q,
  0 <= i -> i+20 <= Z.of_nat (length inp) ->
  raw_crc (skipn (Z.to_nat i) inp) q =
  raw_crc (skipn (Z.to_nat (i+20)) inp)
    (block5 q (bv_unsigned (bword4 inp i)) (bv_unsigned (bword4 inp (i+4)))
      (bv_unsigned (bword4 inp (i+8))) (bv_unsigned (bword4 inp (i+12))) (bv_unsigned (bword4 inp (i+16)))).
Proof.
  intros inp i q Hi HL.
  rewrite (raw_suffix_four inp i q ltac:(lia) ltac:(lia)).
  replace (i+4) with (i+4) by lia.
  rewrite (raw_suffix_four inp (i+4) (word_update q (bv_unsigned (bword4 inp i))) ltac:(lia) ltac:(lia)).
  replace ((i+4)+4) with (i+8) by lia.
  rewrite (raw_suffix_four inp (i+8) (word_update (word_update q (bv_unsigned (bword4 inp i))) (bv_unsigned (bword4 inp (i+4)))) ltac:(lia) ltac:(lia)).
  replace ((i+8)+4) with (i+12) by lia.
  rewrite (raw_suffix_four inp (i+12) (word_update (word_update (word_update q (bv_unsigned (bword4 inp i))) (bv_unsigned (bword4 inp (i+4)))) (bv_unsigned (bword4 inp (i+8)))) ltac:(lia) ltac:(lia)).
  replace ((i+12)+4) with (i+16) by lia.
  rewrite (raw_suffix_four inp (i+16) (word_update (word_update (word_update (word_update q (bv_unsigned (bword4 inp i))) (bv_unsigned (bword4 inp (i+4)))) (bv_unsigned (bword4 inp (i+8)))) (bv_unsigned (bword4 inp (i+12)))) ltac:(lia) ltac:(lia)).
  replace ((i+16)+4) with (i+20) by lia.
  reflexivity.
Qed.
Lemma word_update_range : forall q w, 0 <= q < 2^32 -> 0 <= w < 2^32 -> 0 <= word_update q w < 2^32.
Proof. intros. apply csteps_range,lxor_bound;lia. Qed.
Lemma block5_range : forall q w0 w1 w2 w3 w4,
  0 <= q < 2^32 -> 0 <= w0 < 2^32 -> 0 <= w1 < 2^32 -> 0 <= w2 < 2^32 ->
  0 <= w3 < 2^32 -> 0 <= w4 < 2^32 -> 0 <= block5 q w0 w1 w2 w3 w4 < 2^32.
Proof. intros. unfold block5. repeat apply word_update_range;assumption. Qed.
