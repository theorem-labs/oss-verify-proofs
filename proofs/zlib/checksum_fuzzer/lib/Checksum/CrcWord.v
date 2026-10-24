(** Low-word algebra for the actual unsigned CRC API arguments. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcLib.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Tac Bytes.
Open Scope Z_scope.
Lemma low32_xor : forall a b,
  Z.lxor a b mod 2^32 = Z.lxor (a mod 2^32) (b mod 2^32).
Proof.
  intros a b. apply Z.bits_inj'. intros k Hk. rewrite Z.lxor_spec.
  destruct (Z_lt_ge_dec k 32).
  - rewrite !Z.mod_pow2_bits_low by lia. apply Z.lxor_spec.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma low32_odd : forall a b, a mod 2^32 = b -> Z.odd a = Z.odd b.
Proof.
  intros a b <-. rewrite <- !Z.bit0_odd. symmetry. apply Z.mod_pow2_bits_low. lia.
Qed.
Lemma srliw1_low32 : forall a b, a mod 2^32 = b -> 0 <= b < 2^32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 a) 1) = Z.shiftr b 1.
Proof.
  intros a b E Hb. unfold bv_wrap. change (bv_modulus 32) with (2^32). rewrite E.
  pose proof (shiftr1_bound 31 b ltac:(change (31+1) with 32; lia) ltac:(lia)).
  unfold_swrap32. change (2^31) with 2147483648 in H. rewrite Z.mod_small; lia.
Qed.
Lemma signmask_low32 : forall a b, 0 <= a < 2^64 -> a mod 2^32 = b ->
  Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl a 63))) 63 mod 2^64) 18446744073402876704
  = if Z.odd b then 18446744073402876704 else 0.
Proof.
  intros a b Ha E. rewrite zb_signed, Z.shiftl_mul_pow2 by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- (low32_odd a b E). pose proof (Zmod_odd a) as Hm2.
  destruct (Z.odd a).
  - replace (a * 2^63) with (2^63 + (a / 2) * 2^64) by (Z.div_mod_to_equations; lia).
    rewrite Z.mod_add by lia. vm_compute. reflexivity.
  - replace (a * 2^63) with (0 + (a / 2) * 2^64) by (Z.div_mod_to_equations; lia).
    rewrite Z.mod_add by lia. vm_compute. reflexivity.
Qed.
Lemma land_right_u32 : forall x y, 0 <= y < 2^32 ->
  Z.land x y = Z.land (x mod 2^32) y.
Proof.
  intros x y Hy. apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
  destruct (Z_lt_ge_dec k 32).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite (testbit_small y 32 k Hy ltac:(lia)). rewrite !andb_false_r. reflexivity.
Qed.
Lemma land_SX_left : forall m a, 0 <= m < 2^32 -> 0 <= a < 2^32 ->
  Z.land (SX m) a = Z.land m a.
Proof. intros m a Hm Ha. rewrite land_right_u32 by exact Ha. rewrite SX_mod32 by exact Hm. reflexivity. Qed.
Lemma SX_minus_one_low32 : forall m, 1 <= m <= 2^31 ->
  (SX m + -1) mod 2^32 = m - 1.
Proof.
  intros m Hm. unfold SX, HI32. destruct (Z.ltb_spec m (2^31)); Z.div_mod_to_equations; lia.
Qed.
Lemma land_SX_minus_one_left : forall m a, 1 <= m <= 2^31 -> 0 <= a < 2^32 ->
  Z.land (SX m + -1) a = Z.land (m-1) a.
Proof. intros m a Hm Ha. rewrite land_right_u32 by exact Ha. rewrite SX_minus_one_low32 by exact Hm. reflexivity. Qed.
