(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import InflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma land_shift_mask : forall c k M, 0 <= k -> Z.land c (Z.shiftl M k) = Z.shiftl (Z.land (Z.shiftr c k) M) k.
Proof.
  intros c k M Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.ltb_spec i k) as [LT|GE].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec by lia. rewrite Z.land_spec, Z.shiftr_spec by lia. replace (i - k + k) with i by lia. reflexivity.
Qed.

Lemma cw_land_sub : forall c M, Z.land 255 M = M -> Z.land (Z.shiftr c 8) M = Z.land (code_bits c) M.
Proof. intros c M HM. unfold code_bits. rewrite <- Z.land_assoc, HM. reflexivity. Qed.

Lemma small_land_hi : forall b M, 0 <= b <= 15 -> Z.land 15 M = 0 -> Z.land b M = 0.
Proof.
  intros b M Hb HM. replace b with (Z.land b 15).
  - rewrite <- Z.land_assoc, HM. apply Z.land_0_r.
  - change 15 with (Z.ones 4). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 4) with 16. lia.
Qed.
Lemma small_land_lo : forall b k, 0 <= b <= 15 -> 4 <= k -> Z.land b (Z.ones k) = b.
Proof. intros b k Hb Hk. rewrite Z.land_ones by lia. apply Z.mod_small. assert (2 ^ 4 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 4) with 16 in *. lia. Qed.

Lemma cw_land192 : forall c, 0 <= code_bits c <= 15 -> Z.land (Z.shiftr c 8) 192 = 0.
Proof. intros c Hb. rewrite (cw_land_sub c 192) by reflexivity. apply small_land_hi; [exact Hb| reflexivity]. Qed.
Lemma cw_land224 : forall c, 0 <= code_bits c <= 15 -> Z.land (Z.shiftr c 8) 224 = 0.
Proof. intros c Hb. rewrite (cw_land_sub c 224) by reflexivity. apply small_land_hi; [exact Hb| reflexivity]. Qed.
Lemma cw_land63 : forall c, 0 <= code_bits c <= 15 -> Z.land (Z.shiftr c 8) 63 = code_bits c.
Proof. intros c Hb. rewrite (cw_land_sub c 63) by reflexivity. change 63 with (Z.ones 6). apply small_land_lo; [exact Hb| lia]. Qed.
Lemma cw_land31 : forall c, 0 <= code_bits c <= 15 -> Z.land (Z.shiftr c 8) 31 = code_bits c.
Proof. intros c Hb. rewrite (cw_land_sub c 31) by reflexivity. change 31 with (Z.ones 5). apply small_land_lo; [exact Hb| lia]. Qed.
Lemma cw_mod64 : forall c, 0 <= code_bits c <= 15 -> Z.shiftr c 8 mod 64 = code_bits c.
Proof. intros c Hb. rewrite <- (cw_land63 c Hb). change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma cw_landE000 : forall c, 0 <= code_bits c <= 15 -> Z.land c 57344 = 0.
Proof. intros c Hb. change 57344 with (Z.shiftl 224 8). rewrite land_shift_mask by lia. rewrite (cw_land224 c Hb). reflexivity. Qed.
Lemma cw_shr8_range : forall c, 0 <= c < 4294967296 -> 0 <= Z.shiftr c 8 < 16777216.
Proof. intros c Hc. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. Z.div_mod_to_equations. lia. Qed.
Lemma shl32_shr32 : forall x, Z.shiftr (Z.shiftl x 32) 32 = x.
Proof. intros x. rewrite Z.shiftr_shiftl_l by lia. change (32 - 32) with 0. apply Z.shiftl_0_r. Qed.
Lemma shl32_shr29 : forall x, Z.shiftr (Z.shiftl x 32) 29 = 8 * x.
Proof. intros x. rewrite Z.shiftr_shiftl_l by lia. change (32 - 29) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.
