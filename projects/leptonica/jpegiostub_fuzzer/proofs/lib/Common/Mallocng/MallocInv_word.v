(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML}.


Notation M64 := (2^64) (only parsing).

Lemma uZ : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. Qed.

Lemma uZ_mod : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2^64.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma ZZ_mod : forall z, Z_to_bv 64 (z mod 2^64) = Z_to_bv 64 z.
Proof. intros z. apply bv_eq. rewrite !uZ_mod. apply Zmod_mod. Qed.

Lemma sZ : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite bv_signed_small by (rewrite uZ by lia; lia). apply uZ. lia. Qed.

Lemma swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. reflexivity. Qed.

(* [comment removed for export] *)
Lemma c_ltu_Z : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> c_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold c_ltu, bv_ltu. rewrite !uZ by lia. reflexivity. Qed.

Lemma c_lts_Z : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> c_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold c_lts, bv_lts. rewrite !sZ by lia. reflexivity. Qed.

Lemma c_eq_Z : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> c_eq (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold c_eq, bv_eqb. rewrite !uZ by lia. reflexivity. Qed.

Lemma is0_Z : forall x, 0 <= x < 2^64 -> is0 (Z_to_bv 64 x) = (x =? 0).
Proof. intros x Hx. unfold is0, w0. apply c_eq_Z; lia. Qed.

(* [comment removed for export] *)
Lemma v_add_Z : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. unfold v_add. apply bv_eq. rewrite !uZ_mod.
  rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma v_sub_Z : forall a b, v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. unfold v_sub. apply bv_eq. rewrite !uZ_mod.
  rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma v_addi_Z : forall a i, v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i. unfold v_addi. apply bv_eq. rewrite !uZ_mod. rewrite Zplus_mod_idemp_l. reflexivity. Qed.

Lemma at_Z : forall a d, at_ (Z_to_bv 64 a) d = Z_to_bv 64 (a + d).
Proof. intros a d. unfold at_. apply bv_eq. rewrite !uZ_mod. rewrite Zplus_mod_idemp_l. reflexivity. Qed.

Lemma v_mul_Z : forall a b, v_mul (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof. intros a b. unfold v_mul. apply bv_eq. rewrite !uZ_mod. rewrite <- Zmult_mod. reflexivity. Qed.

(* [comment removed for export] *)
Lemma v_and_Z : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  v_and (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.land a b).
Proof. intros a b Ha Hb. unfold v_and. rewrite !uZ by lia. reflexivity. Qed.

Lemma v_or_Z : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  v_or (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lor a b).
Proof. intros a b Ha Hb. unfold v_or. rewrite !uZ by lia. reflexivity. Qed.

Lemma v_xor_Z : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lxor a b).
Proof. intros a b Ha Hb. unfold v_xor. rewrite !uZ by lia. reflexivity. Qed.

Lemma v_andi_Z : forall a i, 0 <= a < 2^64 -> 0 <= i < 2^64 ->
  v_andi (Z_to_bv 64 a) i = Z_to_bv 64 (Z.land a i).
Proof.
  intros a i Ha Hi. unfold v_andi. rewrite uZ by lia.
  rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). reflexivity.
Qed.

Lemma v_andi_negZ : forall a i, 0 <= a < 2^64 -> - 2^64 <= i < 0 ->
  v_andi (Z_to_bv 64 a) i = Z_to_bv 64 (Z.land a (2^64 + i)).
Proof.
  intros a i Ha Hi. unfold v_andi. rewrite uZ by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  replace (i mod 2^64) with (2^64 + i); [reflexivity|].
  symmetry. rewrite <- (Z.mod_add i 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma v_ori_Z : forall a i, 0 <= a < 2^64 -> 0 <= i < 2^64 ->
  v_ori (Z_to_bv 64 a) i = Z_to_bv 64 (Z.lor a i).
Proof.
  intros a i Ha Hi. unfold v_ori. rewrite uZ by lia.
  rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). reflexivity.
Qed.

Lemma v_xori_Z : forall a i, 0 <= a < 2^64 -> 0 <= i < 2^64 ->
  v_xori (Z_to_bv 64 a) i = Z_to_bv 64 (Z.lxor a i).
Proof.
  intros a i Ha Hi. unfold v_xori. rewrite uZ by lia.
  rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). reflexivity.
Qed.

Lemma v_xori_negZ : forall a i, 0 <= a < 2^64 -> - 2^64 <= i < 0 ->
  v_xori (Z_to_bv 64 a) i = Z_to_bv 64 (Z.lxor a (2^64 + i)).
Proof.
  intros a i Ha Hi. unfold v_xori. rewrite uZ by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  replace (i mod 2^64) with (2^64 + i); [reflexivity|].
  symmetry. rewrite <- (Z.mod_add i 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma v_slli_Z : forall a k, 0 <= a < 2^64 -> 0 <= k -> v_slli (Z_to_bv 64 a) k = Z_to_bv 64 (a * 2^k).
Proof. intros a k Ha Hk. unfold v_slli. rewrite uZ by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma v_srli_Z : forall a k, 0 <= a < 2^64 -> 0 <= k -> v_srli (Z_to_bv 64 a) k = Z_to_bv 64 (a / 2^k).
Proof. intros a k Ha Hk. unfold v_srli. rewrite uZ by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma v_sll_Z : forall a s, 0 <= a < 2^64 -> 0 <= s < 64 ->
  v_sll (Z_to_bv 64 a) (Z_to_bv 64 s) = Z_to_bv 64 (a * 2^s).
Proof.
  intros a s Ha Hs. unfold v_sll. rewrite !uZ by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_addiw_Z : forall a i, 0 <= a < 2^64 -> v_addiw (Z_to_bv 64 a) i = Z_to_bv 64 (bv_swrap 32 (a + i)).
Proof. intros a i Ha. unfold v_addiw. rewrite uZ by lia. reflexivity. Qed.

Lemma v_addw_Z : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (bv_swrap 32 (a + b)).
Proof. intros a b Ha Hb. unfold v_addw. rewrite !uZ by lia. reflexivity. Qed.

Lemma v_subw_Z : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (bv_swrap 32 (a - b)).
Proof. intros a b Ha Hb. unfold v_subw. rewrite !uZ by lia. reflexivity. Qed.

Lemma v_slliw_Z : forall a k, 0 <= a < 2^64 -> 0 <= k ->
  v_slliw (Z_to_bv 64 a) k = Z_to_bv 64 (bv_swrap 32 (a * 2^k)).
Proof. intros a k Ha Hk. unfold v_slliw. rewrite uZ by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma v_srliw_Z : forall a k, 0 <= a < 2^64 -> 0 <= k ->
  v_srliw (Z_to_bv 64 a) k = Z_to_bv 64 (bv_swrap 32 ((a mod 2^32) / 2^k)).
Proof.
  intros a k Ha Hk. unfold v_srliw. rewrite uZ by lia. rewrite Z.shiftr_div_pow2 by lia.
  unfold bv_wrap. change (bv_modulus 32) with (2^32). reflexivity.
Qed.

Lemma v_sllw_Z : forall a s, 0 <= a < 2^64 -> 0 <= s < 2^64 ->
  v_sllw (Z_to_bv 64 a) (Z_to_bv 64 s) = Z_to_bv 64 (bv_swrap 32 (a * 2^(s mod 32))).
Proof.
  intros a s Ha Hs. unfold v_sllw. rewrite !uZ by lia.
  rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.

Lemma v_lw_Z : forall a, 0 <= a < 2^64 -> v_lw (Z_to_bv 64 a) = Z_to_bv 64 (bv_swrap 32 a).
Proof. intros a Ha. unfold v_lw. rewrite uZ by lia. reflexivity. Qed.

Lemma v_sltu_Z : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (if x <? y then 1 else 0).
Proof. intros x y Hx Hy. unfold v_sltu. rewrite c_ltu_Z by lia. destruct (x <? y); reflexivity. Qed.

Lemma v_divu_Z : forall x y, 0 <= x < 2^64 -> 0 < y < 2^64 ->
  v_divu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold v_divu. rewrite !uZ by lia.
  replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wlit_eq : forall z, wlit z = Z_to_bv 64 z. Proof. reflexivity. Qed.
Lemma w0_eq : w0 = Z_to_bv 64 0. Proof. reflexivity. Qed.
Lemma wm1_eq : wm1 = Z_to_bv 64 (2^64 - 1). Proof. reflexivity. Qed.
Lemma PAGEMASK_eq : PAGEMASK = Z_to_bv 64 (2^64 - 4096). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma le_val_Z : forall bs v, bytes_le_to_Z bs = v -> le_val bs = Z_to_bv 64 v.
Proof. intros bs v <-. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_ones_low : forall a n, 0 <= a -> 0 <= n -> Z.land a (2^n - 1) = a mod 2^n.
Proof.
  intros a n Ha Hn. rewrite <- Z.land_ones by lia. f_equal. unfold Z.ones. rewrite Z.shiftl_1_l. lia.
Qed.

Lemma testbit_high_mask : forall n i, 0 <= n <= 64 -> 0 <= i ->
  Z.testbit (2^64 - 2^n) i = ((n <=? i) && (i <? 64))%bool.
Proof.
  intros n i Hn Hi.
  assert (D : 2^64 - 2^n = Z.ones (64 - n) * 2^n).
  { unfold Z.ones. rewrite Z.shiftl_1_l.
    assert (E : 2 ^ (64 - n) * 2 ^ n = 2 ^ 64) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). lia. }
  rewrite D. destruct (Z.lt_ge_cases i n) as [Hlt | Hge].
  - rewrite Z.mul_pow2_bits_low by lia. symmetry. apply andb_false_intro1. apply Z.leb_gt. lia.
  - rewrite Z.mul_pow2_bits by lia. rewrite Z.testbit_ones by lia.
    replace (n <=? i) with true by (symmetry; apply Z.leb_le; lia).
    replace (0 <=? i - n) with true by (symmetry; apply Z.leb_le; lia).
    cbn [andb]. destruct (Z.lt_ge_cases i 64).
    + rewrite (proj2 (Z.ltb_lt (i - n) (64 - n))) by lia. rewrite (proj2 (Z.ltb_lt i 64)) by lia. reflexivity.
    + rewrite (proj2 (Z.ltb_ge (i - n) (64 - n))) by lia. rewrite (proj2 (Z.ltb_ge i 64)) by lia. reflexivity.
Qed.

Lemma testbit_above64 : forall a i, 0 <= a < 2^64 -> 64 <= i -> Z.testbit a i = false.
Proof.
  intros a i Ha Hi. destruct (Z.eq_dec a 0) as [->|Hnz]; [apply Z.testbit_0_l|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia].
Qed.

Lemma land_high_mask : forall a n, 0 <= a < 2^64 -> 0 <= n <= 64 ->
  Z.land a (2^64 - 2^n) = a - a mod 2^n.
Proof.
  intros a n Ha Hn.
  assert (Hm : a - a mod 2^n = (a / 2^n) * 2^n) by (pose proof (Z.div_mod a (2^n) ltac:(lia)); lia).
  rewrite Hm. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, testbit_high_mask by lia.
  destruct (Z.lt_ge_cases i n) as [Hlt | Hge].
  - rewrite Z.mul_pow2_bits_low by lia. replace (n <=? i) with false by (symmetry; apply Z.leb_gt; lia). apply andb_false_r.
  - rewrite Z.mul_pow2_bits, Z.div_pow2_bits by lia. replace (i - n + n) with i by lia.
    replace (n <=? i) with true by (symmetry; apply Z.leb_le; lia).
    destruct (Z.lt_ge_cases i 64).
    + rewrite (proj2 (Z.ltb_lt i 64)) by lia. apply andb_true_r.
    + rewrite (proj2 (Z.ltb_ge i 64)) by lia. rewrite testbit_above64 by lia. reflexivity.
Qed.

End WithLayout.
