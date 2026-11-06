(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import AxSymExec3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma testbit_pow2 : forall n k, 0 <= n -> 0 <= k -> Z.testbit (2^n) k = (n =? k).
Proof.
  intros n k Hn Hk. rewrite <- (Z.shiftl_1_l n), Z.shiftl_spec by lia.
  destruct (Z.eqb_spec n k) as [->|Hne].
  - rewrite Z.sub_diag. reflexivity.
  - destruct (Z.lt_ge_cases (k - n) 0) as [Hl|Hg].
    + apply Z.testbit_neg_r. lia.
    + rewrite Z.bits_above_log2; [reflexivity | lia |]. apply Z.log2_lt_pow2; [lia|].
      apply Z.lt_le_trans with (2^1)%Z; [simpl; lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma testbit_high : forall n a k, 0 <= n -> 0 <= a < 2^n -> n <= k -> Z.testbit a k = false.
Proof.
  intros n a k Hn Ha Hk. destruct (Z.eq_dec a 0) as [->|Hnz]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
  apply Z.lt_le_trans with (2^n); [lia | apply Z.pow_le_mono_r; lia].
Qed.

Lemma testbit_add_shifted : forall a m k n, 0 <= n -> 0 <= a < 2^n -> 0 <= m -> 0 <= k ->
  Z.testbit (a + 2^n * m) k = if k <? n then Z.testbit a k else Z.testbit m (k - n).
Proof.
  intros a m k n Hn Ha Hm Hk.
  assert (Hd : Z.land a (2^n * m) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [Hl|Hg].
    - replace (2^n * m) with (Z.shiftl m n) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite (testbit_high n a i) by lia. reflexivity. }
  rewrite (Z.add_nocarry_lxor a (2^n * m) Hd). rewrite Z.lxor_spec.
  replace (2^n * m) with (Z.shiftl m n) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  destruct (Z.ltb_spec k n) as [Hl|Hg].
  - rewrite Z.shiftl_spec_low by lia. apply xorb_false_r.
  - rewrite Z.shiftl_spec by lia. rewrite (testbit_high n a k) by lia. reflexivity.
Qed.

Lemma testbit31_iff : forall u, 0 <= u < 2^32 -> Z.testbit u 31 = (2^31 <=? u).
Proof.
  intros u Hu. destruct (Z.leb_spec (2^31) u) as [Hg|Hl].
  - apply Z.testbit_true; [lia|].
    assert (E : u / 2^31 = 1) by (symmetry; apply Z.div_unique with (r := u - 2^31); lia). rewrite E. reflexivity.
  - apply (testbit_high 31); lia.
Qed.

Lemma swrap32_eq_mod : forall x, bv_swrap 32 x = bv_swrap 32 (x mod 2^32).
Proof. intros. apply swrap32_eqm. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma swrap32_mod : forall x, bv_swrap 32 x mod 2^32 = x mod 2^32.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Zminus_mod. rewrite Z.mod_mod by lia. rewrite <- Zminus_mod. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma sx32_val : forall x, bv_swrap 32 x mod 2^64 =
  if Z.testbit x 31 then x mod 2^32 + 2^32 * (2^32 - 1) else x mod 2^32.
Proof.
  intros x. rewrite swrap32_eq_mod.
  assert (Hu : 0 <= x mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  replace (Z.testbit x 31) with (Z.testbit (x mod 2^32) 31) by (apply Z.mod_pow2_bits_low; lia).
  rewrite testbit31_iff by exact Hu. set (u := x mod 2^32) in *.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.leb_spec (2^31) u) as [Hg|Hl].
  - rewrite <- (Z.mod_unique (u + 2^31) (2^32) 1 (u + 2^31 - 2^32)) by lia.
    rewrite <- (Z.mod_unique (u + 2^31 - 2^32 - 2^31) (2^64) (-1) (u + 2^32 * (2^32 - 1))) by lia. reflexivity.
  - rewrite (Z.mod_small (u + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma testbit_sx32 : forall x k, 0 <= k ->
  Z.testbit (bv_swrap 32 x mod 2^64) k = (k <? 64) && Z.testbit x (Z.min k 31).
Proof.
  intros x k Hk. rewrite sx32_val.
  assert (Hu : 0 <= x mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  destruct (Z.ltb_spec k 32) as [Hl|Hg].
  - replace (Z.min k 31) with k by lia. replace (k <? 64) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [andb]. destruct (Z.testbit x 31).
    + rewrite testbit_add_shifted by lia. replace (k <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
      apply Z.mod_pow2_bits_low; lia.
    + apply Z.mod_pow2_bits_low; lia.
  - replace (Z.min k 31) with 31 by lia. destruct (Z.testbit x 31) eqn:Hb.
    + rewrite testbit_add_shifted by lia. replace (k <? 32) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (2^32 - 1) with (Z.ones 32) by reflexivity. rewrite Z.testbit_ones by lia. rewrite andb_true_r.
      destruct (Z.leb_spec 0 (k - 32)); [|lia]. cbn [andb].
      destruct (Z.ltb_spec (k - 32) 32), (Z.ltb_spec k 64); try reflexivity; lia.
    + rewrite (testbit_high 32 (x mod 2^32) k) by lia. rewrite andb_false_r. reflexivity.
Qed.

Lemma sx32_lor : forall a b, Z.lor (bv_swrap 32 a mod 2^64) (bv_swrap 32 b mod 2^64) = bv_swrap 32 (Z.lor a b) mod 2^64.
Proof.
  intros a b. apply Z.bits_inj'. intros k Hk. rewrite Z.lor_spec, !testbit_sx32 by lia.
  rewrite Z.lor_spec. destruct (k <? 64); reflexivity.
Qed.

Lemma sx32_land : forall a b, Z.land (bv_swrap 32 a mod 2^64) (bv_swrap 32 b mod 2^64) = bv_swrap 32 (Z.land a b) mod 2^64.
Proof.
  intros a b. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, !testbit_sx32 by lia.
  rewrite Z.land_spec. destruct (k <? 64); reflexivity.
Qed.

Lemma sx32_eqb : forall a b, (bv_swrap 32 a mod 2^64 =? bv_swrap 32 b mod 2^64) = (a mod 2^32 =? b mod 2^32).
Proof.
  intros a b. rewrite !sx32_val.
  assert (Ha : 0 <= a mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  assert (Hb : 0 <= b mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  replace (Z.testbit a 31) with (Z.testbit (a mod 2^32) 31) by (apply Z.mod_pow2_bits_low; lia).
  replace (Z.testbit b 31) with (Z.testbit (b mod 2^32) 31) by (apply Z.mod_pow2_bits_low; lia).
  rewrite !testbit31_iff by assumption.
  set (u := a mod 2^32) in *. set (v := b mod 2^32) in *.
  destruct (Z.leb_spec (2^31) u), (Z.leb_spec (2^31) v);
    destruct (Z.eqb_spec u v); first [reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia].
Qed.

Lemma ext4_swrap : forall x, ext_Z true 0 4 x = bv_swrap 32 x.
Proof.
  intros x. unfold ext_Z. cbn [Z.of_nat N.of_nat]. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r.
  change (8 * N.pos 4)%N with 32%N. change (2 ^ (8 * 4)) with (2^32). symmetry. apply swrap32_eq_mod.
Qed.

(* [comment removed for export] *)

Lemma sllw1_val : forall idx, 0 <= idx <= 31 -> bv_swrap 32 (Z.shiftl 1 idx) mod 2^64 = bv_swrap 32 (2^idx) mod 2^64.
Proof. intros idx H. rewrite Z.shiftl_1_l. reflexivity. Qed.

Lemma mask_bit_clear : forall f idx, 0 <= f < 2^32 -> 0 <= idx <= 31 -> Z.testbit f idx = false ->
  Z.land (bv_swrap 32 f mod 2^64) (bv_swrap 32 (Z.shiftl 1 idx) mod 2^64) = 0.
Proof.
  intros f idx Hf Hi Hb. rewrite sllw1_val by lia. rewrite sx32_land.
  replace (Z.land f (2^idx)) with 0.
  - reflexivity.
  - apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0, testbit_pow2 by lia.
    destruct (Z.eqb_spec idx k) as [<-|]; [rewrite Hb; reflexivity | rewrite andb_false_r; reflexivity].
Qed.

Lemma mask2_bit_clear : forall a f idx, 0 <= a < 2^32 -> 0 <= f < 2^32 -> 0 <= idx <= 31 ->
  Z.testbit a idx = false -> Z.testbit f idx = false ->
  Z.land (Z.lor (bv_swrap 32 a mod 2^64) (bv_swrap 32 f mod 2^64) mod 2^64) (bv_swrap 32 (Z.shiftl 1 idx) mod 2^64) = 0.
Proof.
  intros a f idx Ha Hf Hi Hba Hbf. rewrite sx32_lor. rewrite Z.mod_mod by lia.
  apply mask_bit_clear; [split; [apply Z.lor_nonneg; lia | ] | lia | ].
  - apply (Z.le_lt_trans _ (Z.lor a f)); [lia|]. 
    destruct (Z.eq_dec (Z.lor a f) 0) as [->|Hnz]; [lia|].
    apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia. rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt; [destruct (Z.eq_dec a 0) as [->|]; [simpl; lia | apply Z.log2_lt_pow2; lia]
                         | destruct (Z.eq_dec f 0) as [->|]; [simpl; lia | apply Z.log2_lt_pow2; lia]].
  - rewrite Z.lor_spec, Hba, Hbf. reflexivity.
Qed.

Lemma land31_bound : forall x, 0 <= x -> 0 <= Z.land x 31 < 32.
Proof.
  intros x Hx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2^5) ltac:(lia)). change (2^5) with 32 in *. lia.
Qed.

Lemma shiftr5_bound : forall h, 0 <= h <= 159 -> 0 <= Z.shiftr h 5 <= 4.
Proof.
  intros h H. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32.
  split; [apply Z.div_pos; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia].
Qed.

Lemma lor_lt32 : forall a f, 0 <= a < 2^32 -> 0 <= f < 2^32 -> 0 <= Z.lor a f < 2^32.
Proof.
  intros a f Ha Hf. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a f) 0) as [->|Hnz]; [lia|].
  apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; [destruct (Z.eq_dec a 0) as [->|]; [simpl; lia | apply Z.log2_lt_pow2; lia]
                       | destruct (Z.eq_dec f 0) as [->|]; [simpl; lia | apply Z.log2_lt_pow2; lia]].
Qed.

Lemma add_bit_clear_lt : forall a k, 0 <= a < 2^32 -> 0 <= k <= 31 -> Z.testbit a k = false -> a + 2^k < 2^32.
Proof.
  intros a k Ha Hk Hb.
  assert (Hd : Z.land a (2^k) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, testbit_pow2 by lia.
    destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity | apply andb_false_r]. }
  rewrite (Z.add_nocarry_lxor a (2^k) Hd), (Z.lxor_lor a (2^k) Hd).
  apply lor_lt32; [lia|]. split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
Qed.

(* [comment removed for export] *)
Lemma all_cond_z : forall a f idx W, 0 <= a < 2^32 -> 0 <= f < 2^32 -> 0 <= idx <= 31 -> 0 <= W ->
  Z.testbit a idx = false -> Z.testbit f idx = false ->
  (bv_swrap 32 (Z.lor (ext_Z true 0 4 a mod 2^64) (ext_Z true 0 4 f mod 2^64) + bv_swrap 32 (Z.shiftl 1 idx)) mod 2^64
     =? bv_swrap 32 (bv_swrap 32 (Z.shiftl 2 (W mod 32)) + -1) mod 2^64)
  = (Z.lor a f + 2^idx =? 2^(Z.land W 31 + 1) - 1).
Proof.
  intros a f idx W Ha Hf Hi HW Hba Hbf.
  rewrite !ext4_swrap, sx32_lor, sx32_eqb.
  assert (HL : 0 <= Z.lor a f < 2^32) by (apply lor_lt32; lia).
  assert (HLb : Z.testbit (Z.lor a f) idx = false) by (rewrite Z.lor_spec, Hba, Hbf; reflexivity).
  assert (HLt : Z.lor a f + 2^idx < 2^32) by (apply add_bit_clear_lt; [exact HL | lia | exact HLb]).
  assert (Hp : 0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.shiftl_1_l.
  assert (E1 : (bv_swrap 32 (Z.lor a f) mod 2^64 + bv_swrap 32 (2^idx)) mod 2^32 = Z.lor a f + 2^idx).
  { rewrite Zplus_mod, mod64_32, !swrap32_mod, <- Zplus_mod. apply Z.mod_small. lia. }
  assert (Hl : 0 <= Z.land W 31 < 32) by (apply land31_bound; lia).
  assert (Hw : W mod 32 = Z.land W 31) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity).
  assert (E2 : (bv_swrap 32 (Z.shiftl 2 (W mod 32)) + -1) mod 2^32 = 2^(Z.land W 31 + 1) - 1).
  { rewrite Zplus_mod, swrap32_mod, <- Zplus_mod. rewrite Hw. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.pow_add_r by lia. change (2^1) with 2.
    assert (0 < 2^(Z.land W 31) <= 2^31) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    rewrite Z.mod_small; lia. }
  rewrite E1, E2. reflexivity.
Qed.

Lemma sx32_zero : forall f, (bv_swrap 32 f mod 2^64 =? 0) = (f mod 2^32 =? 0).
Proof. intros f. change 0 with (bv_swrap 32 0 mod 2^64) at 1. rewrite sx32_eqb. reflexivity. Qed.
