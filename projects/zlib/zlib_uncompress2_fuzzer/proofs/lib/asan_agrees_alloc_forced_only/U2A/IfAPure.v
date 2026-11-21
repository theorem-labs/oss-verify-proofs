(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import MState Mem ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import InflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma pow2_pos : forall k, 0 <= k -> 0 < 2 ^ k.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow2_le : forall a b, 0 <= a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.
Lemma pow2_15 : forall k, 0 <= k <= 15 -> 1 <= 2 ^ k <= 32768.
Proof. intros k Hk. split; [pose proof (pow2_pos k ltac:(lia)); lia | change 32768 with (2 ^ 15); apply pow2_le; lia]. Qed.
Lemma pow2_40 : forall b, 0 <= b <= 40 -> 1 <= 2 ^ b <= 1099511627776.
Proof. intros b Hb. split; [pose proof (pow2_pos b ltac:(lia)); lia | change 1099511627776 with (2 ^ 40); apply pow2_le; lia]. Qed.

Lemma mask_sllw : forall k, 0 <= k <= 30 ->
  Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (k mod 32)) mod 18446744073709551616) 18446744073709551615 = 2 ^ k - 1.
Proof.
  intros k Hk. replace k with (Z.of_nat (Z.to_nat k)) by lia.
  assert (H : (Z.to_nat k <= 30)%nat) by lia. revert H. generalize (Z.to_nat k). clear. intros j H.
  do 31 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma land_mask_mod : forall h k, 0 <= k -> Z.land h (2 ^ k - 1) = h mod 2 ^ k.
Proof. intros h k Hk. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). apply Z.land_ones. exact Hk. Qed.
Lemma mod_pow2_bound : forall h k, 0 <= k -> 0 <= h mod 2 ^ k < 2 ^ k.
Proof. intros h k Hk. apply Z.mod_pos_bound. apply pow2_pos; lia. Qed.
Lemma srl_div : forall h k, 0 <= k < 64 -> Z.shiftr h (k mod 64) = h / 2 ^ k.
Proof. intros h k Hk. rewrite Z.mod_small by lia. apply Z.shiftr_div_pow2. lia. Qed.
Lemma drop_bound : forall h b k, 0 <= k <= b -> 0 <= h < 2 ^ b -> 0 <= h / 2 ^ k < 2 ^ (b - k).
Proof.
  intros h b k Hk Hh. pose proof (pow2_pos k ltac:(lia)).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (b - k)) with b by lia. lia.
Qed.
Lemma shl_byte : forall c b, 0 <= b < 64 -> Z.shiftl c (b mod 64) = c * 2 ^ b.
Proof. intros c b Hb. rewrite Z.mod_small by lia. apply Z.shiftl_mul_pow2. lia. Qed.
Lemma pull_bound : forall h b c, 0 <= b -> 0 <= h < 2 ^ b -> 0 <= c < 256 -> 0 <= h + c * 2 ^ b < 2 ^ (b + 8).
Proof.
  intros h b c Hb Hh Hc. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. pose proof (pow2_pos b Hb). nia.
Qed.
Lemma pull2_bound : forall h b c0 c1, 0 <= b -> 0 <= h < 2 ^ b -> 0 <= c0 < 256 -> 0 <= c1 < 256 ->
  0 <= h + c0 * 2 ^ b + c1 * 2 ^ (b + 8) < 2 ^ (b + 16).
Proof.
  intros h b c0 c1 Hb Hh H0 H1. pose proof (pull_bound h b c0 Hb Hh H0) as A.
  pose proof (pull_bound (h + c0 * 2 ^ b) (b + 8) c1 ltac:(lia) A H1) as B. replace (b + 8 + 8) with (b + 16) in B by lia. lia.
Qed.
Lemma lor_16 : forall b, 0 <= b < 16 -> Z.lor b 16 = b + 16.
Proof.
  intros b Hb. replace b with (Z.of_nat (Z.to_nat b)) by lia.
  assert (H : (Z.to_nat b <= 15)%nat) by lia. revert H. generalize (Z.to_nat b). clear. intros j H.
  do 16 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma land_255_id : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land_7_mod : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma shl2 : forall x, Z.shiftl x 2 = 4 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.

Lemma zext32_small : forall e, 0 <= e < 4294967296 -> (e mod 18446744073709551616) mod 4294967296 = e.
Proof. intros e H. rewrite Z.mod_small by lia. apply Z.mod_small. lia. Qed.
Lemma zx16_small : forall e, 0 <= e < 65536 -> zx16 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof. intros e H. unfold zx16. rewrite unsigned_lit by lia. change (2 ^ 16) with 65536. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma zx32_small : forall e, 0 <= e < 4294967296 -> zx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof. intros e H. unfold zx32. rewrite unsigned_lit by lia. change (2^32) with 4294967296. rewrite Z.mod_small by lia. reflexivity. Qed.

Definition fupd8 (f : Z -> Z) (i v : Z) : Z -> Z := fun j => if Z.eqb j i then v else f j.
Lemma fupd8_range : forall (f : Z -> Z) i v N, (forall j, 0 <= j < N -> 0 <= f j < 256) -> 0 <= v < 256 ->
  forall j, 0 <= j < N -> 0 <= fupd8 f i v j < 256.
Proof. intros f i v N Hf Hv j Hj. unfold fupd8. destruct (Z.eqb_spec j i); [lia| apply Hf; lia]. Qed.

Lemma code_op_range : forall c, 0 <= code_op c < 256.
Proof. intros c. unfold code_op. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma code_bits_range : forall c, 0 <= code_bits c < 256.
Proof. intros c. unfold code_bits. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma code_val_range : forall c, 0 <= code_val c < 65536.
Proof. intros c. unfold code_val. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma u8_val : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. intros x H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.
