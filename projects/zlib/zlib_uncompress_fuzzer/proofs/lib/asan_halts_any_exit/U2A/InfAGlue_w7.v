(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import MState Mem ZBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma mask_sllw : forall k, 0 <= k <= 30 ->
  Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (k mod 32)) mod 18446744073709551616) 18446744073709551615 = 2 ^ k - 1.
Proof.
  intros k Hk. replace k with (Z.of_nat (Z.to_nat k)) by lia.
  assert (H : (Z.to_nat k <= 30)%nat) by lia. revert H. generalize (Z.to_nat k). clear. intros j H.
  do 31 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma land_mask_mod : forall h k, 0 <= k -> Z.land h (2 ^ k - 1) = h mod 2 ^ k.
Proof. intros h k Hk. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). apply Z.land_ones. exact Hk. Qed.
Lemma land_mask_mod' : forall h k, 0 <= k -> Z.land (2 ^ k - 1) h = h mod 2 ^ k.
Proof. intros h k Hk. rewrite Z.land_comm. apply land_mask_mod. exact Hk. Qed.
Lemma srl_div : forall h k, 0 <= k < 64 -> Z.shiftr h (k mod 64) = h / 2 ^ k.
Proof. intros h k Hk. rewrite Z.mod_small by lia. apply Z.shiftr_div_pow2. lia. Qed.
Lemma drop_bound : forall h b k, 0 <= k <= b -> 0 <= h < 2 ^ b -> 0 <= h / 2 ^ k < 2 ^ (b - k).
Proof.
  intros h b k Hk Hh. assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (b - k)) with b by lia. lia.
Qed.
Lemma mod_pow2_bound : forall h k, 0 <= k -> 0 <= h mod 2 ^ k < 2 ^ k.
Proof. intros h k Hk. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow2_le_15 : forall k, 0 <= k <= 15 -> 1 <= 2 ^ k <= 32768.
Proof. intros k Hk. split; [assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia); lia | change 32768 with (2 ^ 15); apply Z.pow_le_mono_r; lia]. Qed.
Lemma bits_mask_sllw : forall h k, 0 <= k <= 30 ->
  Z.land h (Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (k mod 32)) mod 18446744073709551616) 18446744073709551615) = h mod 2 ^ k.
Proof. intros h k Hk. rewrite mask_sllw by lia. apply land_mask_mod. lia. Qed.
Lemma pull_bound : forall h b c, 0 <= b -> 0 <= h < 2 ^ b -> 0 <= c < 256 -> 0 <= h + c * 2 ^ b < 2 ^ (b + 8).
Proof.
  intros h b c Hb Hh Hc. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  assert (0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.
Lemma zx32_small : forall e, 0 <= e < 4294967296 -> zx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof. intros e H. unfold zx32. rewrite unsigned_lit by lia. change (2^32) with 4294967296. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma shl2 : forall x, Z.shiftl x 2 = 4 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.
Lemma root_idx : forall h k, 0 <= k -> Z.land (2 ^ k - 1) h = h mod 2 ^ k.
Proof. intros. apply land_mask_mod'. assumption. Qed.
Lemma u8_lit : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. intros x H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.
Lemma zx16_small : forall e, 0 <= e < 65536 -> zx16 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof. intros e H. unfold zx16. rewrite unsigned_lit by lia. change (2^16) with 65536. rewrite Z.mod_small by lia. reflexivity. Qed.
