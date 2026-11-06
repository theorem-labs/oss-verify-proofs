From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

Lemma firstn1_skipn : forall {A} (bs : list A) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof. intros A bs. induction bs as [|x bs IH]; intros [|k] d Hk; cbn in *; try lia; auto. apply IH. lia. Qed.

Lemma read1 : forall m a bs k, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [nth k bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk. rewrite (bytes_at_ov_read rsegs m a bs k 1 H) by lia.
  rewrite (firstn1_skipn bs k (Z_to_bv 8 0) Hk). reflexivity.
Qed.

Lemma byte_signed : forall b : byte, bv_signed b = if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b - 256.
Proof.
  intros b. pose proof (byte_range b) as Hr. unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  destruct (Z.ltb_spec (bv_unsigned b) 128).
  - rewrite Z.mod_small by lia. lia.
  - replace (bv_unsigned b + 128) with ((bv_unsigned b - 128) + 1 * 256) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sxb_unsigned : forall b : byte,
  bv_unsigned (sxb b) = if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b - 256 + 2 ^ 64.
Proof.
  intros b. pose proof (byte_range b) as Hr. unfold sxb. rewrite unsigned_lit_wrap, byte_signed.
  destruct (Z.ltb_spec (bv_unsigned b) 128).
  - apply Z.mod_small. lia.
  - rewrite <- (Z.mod_add (bv_unsigned b - 256) 1 (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma sxb_lts0 : forall b : byte, bv_lts (sxb b) (Z_to_bv 64 0) = (128 <=? bv_unsigned b).
Proof.
  intros b. rewrite bv_lts_zero_r, sxb_unsigned. pose proof (byte_range b) as Hr.
  apply Bool.eq_iff_eq_true. rewrite !Z.leb_le.
  destruct (Z.ltb_spec (bv_unsigned b) 128); lia.
Qed.

Lemma sxb_land : forall (b : byte) k, 0 <= k <= 8 ->
  Z.land (bv_unsigned (sxb b)) (Z.ones k) = bv_unsigned b mod 2 ^ k.
Proof.
  intros b k Hk. rewrite Z.land_ones by lia. rewrite sxb_unsigned. pose proof (byte_range b) as Hr.
  assert (H256 : 2 ^ 8 = 2 ^ k * 2 ^ (8 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (H64 : 2 ^ 64 = 2 ^ k * 2 ^ (64 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  destruct (Z.ltb_spec (bv_unsigned b) 128); [reflexivity|].
  replace (bv_unsigned b - 256 + 2 ^ 64) with (bv_unsigned b + (2 ^ (64 - k) - 2 ^ (8 - k)) * 2 ^ k)
    by (change 256 with (2 ^ 8) in *; nia).
  apply Z.mod_add. apply Z.pow_nonzero; lia.
Qed.

Lemma sxb_swrap : forall b : byte, sxb b = Z_to_bv 64 (bv_swrap 8 (bv_unsigned b)).
Proof. intros b. reflexivity. Qed.

Lemma eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.
Lemma sltu_sub : forall a d, 0 <= a < 2 ^ 64 -> 0 <= d < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 (a - d)) = Z_to_bv 64 (if a <? d then 1 else 0).
Proof.
  intros a d Ha Hd. rewrite v_sltu_b2z. rewrite (unsigned_lit a) by lia. rewrite unsigned_lit_wrap.
  destruct (Z.ltb_spec a d).
  - rewrite <- (Z.mod_add (a - d) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  - rewrite Z.mod_small by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Lemma lor_byte_shift : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> Z.lor (Z.shiftl hi 8) lo = lo + 256 * hi.
Proof.
  intros lo hi Hlo Hhi. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  assert (H0 : Z.land (hi * 256) lo = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8).
    - change 256 with (2 ^ 8). rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. reflexivity.
    - rewrite <- (Z.mod_small lo (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
      rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- (Z.lxor_lor _ _ H0), <- (Z.add_nocarry_lxor _ _ H0). lia.
Qed.

Lemma nth_past : forall (bs : list byte) k, (length bs <= k)%nat -> bv_unsigned (nth k bs (Z_to_bv 8 0)) = 0.
Proof. intros bs k H. rewrite nth_overflow by exact H. reflexivity. Qed.

Lemma ltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma swrap32_id : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. Qed.
