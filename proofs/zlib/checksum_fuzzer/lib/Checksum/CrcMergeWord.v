(** Signed and unsigned zero-byte updates used by the final CRC braid merge. *)
From Stdlib Require Import ZArith NArith List Lia Bool Btauto.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcLib CrcWord CrcLinearBasis CrcByteStep CrcBraidModel.
Open Scope Z_scope.
Opaque csteps.
Lemma low32_mod64 : forall a, (a mod 2^64) mod 2^32 = a mod 2^32.
Proof.
  intros a. apply Z.bits_inj'. intros k Hk. destruct (Z_lt_ge_dec k 32).
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma srliw8_raw : forall a,
  bv_swrap 32 (Z.shiftr (bv_wrap 32 a) 8) = Z.shiftr (a mod 2^32) 8.
Proof.
  intros a. unfold bv_wrap. change (bv_modulus 32) with (2^32).
  pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)) as Hq.
  assert (HQ : 0 <= Z.shiftr (a mod 2^32) 8 < 2^24).
  { rewrite Z.shiftr_div_pow2 by lia. change (0 <= (a mod 2^32)/256 < 16777216).
    split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]. }
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
Qed.
Lemma shiftr8_u32_range : forall q, 0 <= q < 2^32 -> 0 <= Z.shiftr q 8 < 2^24.
Proof.
  intros q Hq. rewrite Z.shiftr_div_pow2 by lia.
  change (0 <= q/256 < 16777216). split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia].
Qed.
Lemma zero_byte_unsigned : forall a,
  Z.lxor (Z.shiftr (a mod 2^32) 8) (csteps 8 (Z.land a 255)) = csteps 8 (a mod 2^32).
Proof.
  intros a. pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)) as Hq.
  rewrite (land_right_u32 a 255 ltac:(lia)),land255_mod.
  rewrite (byte_split_value (a mod 2^32) Hq). unfold byte_split_rhs. apply Z.lxor_comm.
Qed.
Lemma zero_byte_signed : forall a,
  Z.lxor (Z.shiftr (a mod 2^32) 8) (SX (csteps 8 (Z.land a 255))) = SX (csteps 8 (a mod 2^32)).
Proof.
  intros a. pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)) as Hq.
  pose proof (shiftr8_u32_range (a mod 2^32) Hq) as HS.
  assert (HT : 0 <= csteps 8 (Z.land a 255) < 2^32).
  { apply csteps_range. pose proof (land255_range a). lia. }
  rewrite lxor_small_SX by lia. f_equal. apply zero_byte_unsigned.
Qed.
Lemma zero_byte_insert_signed : forall a rest,
  Z.lxor (SX (csteps 8 (Z.land a 255))) (Z.lxor rest (Z.shiftr (a mod 2^32) 8)) =
  Z.lxor rest (SX (csteps 8 (a mod 2^32))).
Proof.
  intros a rest. rewrite <- (zero_byte_signed a).
  apply Z.bits_inj'. intros k Hk. rewrite !Z.lxor_spec. btauto.
Qed.
Lemma zero_byte_unsigned_low : forall a q, a mod 2^32 = q ->
  Z.lxor (Z.shiftr q 8) (csteps 8 (Z.land a 255)) = csteps 8 q.
Proof. intros a q <-. apply zero_byte_unsigned. Qed.
Lemma zero_byte_signed_low : forall a q, a mod 2^32 = q ->
  Z.lxor (Z.shiftr q 8) (SX (csteps 8 (Z.land a 255))) = SX (csteps 8 q).
Proof. intros a q <-. apply zero_byte_signed. Qed.
Lemma zero_byte_insert_signed_low : forall a q rest, a mod 2^32 = q ->
  Z.lxor (SX (csteps 8 (Z.land a 255))) (Z.lxor rest (Z.shiftr q 8)) =
  Z.lxor rest (SX (csteps 8 q)).
Proof. intros a q rest <-. apply zero_byte_insert_signed. Qed.
