(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface InflateState RefInflateArmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma wz_wrap64 : forall x, Z_to_bv 64 (wrap64 x) = Z_to_bv 64 x.
Proof. intros x. apply Z_to_bv_eqm. rewrite wrap64_mod. apply Z.mod_mod. lia. Qed.

Lemma land_u32_small : forall x, 0 <= x < 2 ^ 32 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. exact Hx. Qed.

Lemma lor_hi_lo : forall k a b, 0 <= k -> 0 <= a < 2 ^ k -> Z.lor (b * 2 ^ k) a = b * 2 ^ k + a.
Proof.
  intros k a b Hk Ha.
  assert (Hz : Z.land (b * 2 ^ k) a = 0).
  { apply Z.bits_inj_0. intros n. destruct (Z.leb_spec 0 n) as [Hn|Hn]; [| rewrite Z.testbit_neg_r by lia; reflexivity].
    rewrite Z.land_spec. destruct (Z.ltb_spec n k).
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit a n) with false; [apply andb_false_r|]. symmetry.
      destruct (Z.eq_dec a 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [exact (proj2 Ha)|]. apply Z.pow_le_mono_r; lia. }
  rewrite <- Z.lxor_lor by exact Hz. symmetry. apply Z.add_nocarry_lxor. exact Hz.
Qed.

Lemma land_65280 : forall x, 0 <= x -> Z.land x 65280 = (x / 2 ^ 8) mod 2 ^ 8 * 2 ^ 8.
Proof.
  intros x Hx. rewrite <- Z.shiftr_div_pow2, <- Z.land_ones, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, testbit_65280 by lia.
  destruct (Z.ltb_spec n 8).
  - rewrite Z.shiftl_spec_low by lia. destruct (Z.leb_spec 8 n); [lia|]. cbn [andb]. apply andb_false_r.
  - rewrite Z.shiftl_spec by lia. rewrite Z.land_spec, Z.shiftr_spec by lia. replace (n - 8 + 8) with n by lia.
    destruct (Z.leb_spec 8 n); [|lia]. cbn [andb]. destruct (Z.ltb_spec n 16).
    + rewrite Z.ones_spec_low by lia. reflexivity.
    + rewrite Z.ones_spec_high by lia. reflexivity.
Qed.

Definition byte_of (h k : Z) : Z := (h / 2 ^ (8 * k)) mod 2 ^ 8.

Lemma ZSWAP32_bytes : forall h, 0 <= h ->
  ZSWAP32 h = byte_of h 0 * 2 ^ 24 + byte_of h 1 * 2 ^ 16 + byte_of h 2 * 2 ^ 8 + byte_of h 3.
Proof.
  intros h Hh. unfold ZSWAP32, byte_of.
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. rewrite !Z.shiftr_div_pow2, !Z.shiftl_mul_pow2 by lia.
  rewrite !land_65280 by (first [lia | apply Z.div_pos; [lia| reflexivity]]).
  change (8 * 0) with 0. change (8 * 1) with 8. change (8 * 2) with 16. change (8 * 3) with 24. rewrite Z.pow_0_r, Z.div_1_r.
  rewrite (Z.div_div h (2 ^ 8) (2 ^ 8)) by lia. change (2 ^ 8 * 2 ^ 8) with (2 ^ 16).
  pose proof (Z.mod_pos_bound h (2 ^ 8) ltac:(lia)). pose proof (Z.mod_pos_bound (h / 2 ^ 8) (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound (h / 2 ^ 16) (2 ^ 8) ltac:(lia)). pose proof (Z.mod_pos_bound (h / 2 ^ 24) (2 ^ 8) ltac:(lia)).
  rewrite wrap64_mod. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ZSWAP32_range : forall h, 0 <= ZSWAP32 h < 2 ^ 64.
Proof. intros h. unfold ZSWAP32. apply wrap64_range. Qed.

Lemma zswap_clang : forall h, 0 <= h < 2 ^ 64 ->
  Z.land (Z.lor (Z.lor (Z.land (Z.shiftl h 24) 18446744073709551615) (Z.land (Z.shiftl (Z.land h 65280) 8) 18446744073709551615))
                (Z.lor (Z.land (Z.shiftr h 8) 65280) (Z.land (bv_swrap 32 (Z.shiftr (bv_wrap 32 h) 24)) 18446744073709551615))) 4294967295
  = ZSWAP32 h.
Proof.
  intros h Hh. rewrite ZSWAP32_bytes by lia. unfold byte_of.
  change (8 * 0) with 0. change (8 * 1) with 8. change (8 * 2) with 16. change (8 * 3) with 24. rewrite Z.pow_0_r, Z.div_1_r.
  set (b0 := h mod 2 ^ 8). set (b1 := (h / 2 ^ 8) mod 2 ^ 8). set (b2 := (h / 2 ^ 16) mod 2 ^ 8). set (b3 := (h / 2 ^ 24) mod 2 ^ 8).
  assert (R0 : 0 <= b0 < 2 ^ 8) by (apply Z.mod_pos_bound; lia). assert (R1 : 0 <= b1 < 2 ^ 8) by (apply Z.mod_pos_bound; lia).
  assert (R2 : 0 <= b2 < 2 ^ 8) by (apply Z.mod_pos_bound; lia). assert (R3 : 0 <= b3 < 2 ^ 8) by (apply Z.mod_pos_bound; lia).

  assert (E4 : bv_swrap 32 (Z.shiftr (bv_wrap 32 h) 24) = b3).
  { unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite Z.shiftr_div_pow2 by lia.
    assert (EE : h mod 2 ^ 32 / 2 ^ 24 = b3).
    { subst b3. change (2 ^ 32) with (2 ^ 24 * 2 ^ 8). rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.div_add by lia.
      rewrite (Z.div_small (h mod 2 ^ 24)) by (apply Z.mod_pos_bound; lia). lia. }
    rewrite EE. unfold bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_small by lia. lia. }
  assert (E3 : Z.land (Z.shiftr h 8) 65280 = b2 * 2 ^ 8).
  { rewrite land_65280 by (apply Z.shiftr_nonneg; lia). rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia. reflexivity. }
  assert (E2 : Z.shiftl (Z.land h 65280) 8 = b1 * 2 ^ 16).
  { rewrite land_65280 by lia. rewrite Z.shiftl_mul_pow2 by lia. fold b1. lia. }
  change 18446744073709551615 with (Z.ones 64). change 4294967295 with (Z.ones 32).
  rewrite E4, E3, E2. rewrite (Z.land_ones b3), (Z.land_ones (b1 * 2 ^ 16)) by lia.
  rewrite (Z.mod_small b3), (Z.mod_small (b1 * 2 ^ 16)) by lia.
  rewrite (lor_hi_lo 8 b3 b2) by lia.

  rewrite !Z.land_lor_distr_l.
  assert (E1 : Z.land (Z.land (Z.shiftl h 24) (Z.ones 64)) (Z.ones 32) = b0 * 2 ^ 24).
  { rewrite !Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia.
    change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). rewrite Z.rem_mul_r by lia.
    rewrite (Z.mul_comm (2 ^ 32) (_ mod 2 ^ 32)), Z.mod_add by lia. rewrite Z.mod_mod by lia.
    subst b0. rewrite (Z.div_mod h (2 ^ 8)) at 1 by lia.
    replace ((2 ^ 8 * (h / 2 ^ 8) + h mod 2 ^ 8) * 2 ^ 24) with (h mod 2 ^ 8 * 2 ^ 24 + (h / 2 ^ 8) * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. pose proof (Z.mod_pos_bound h (2 ^ 8) ltac:(lia)). lia. }
  rewrite E1. rewrite (Z.land_ones (b1 * 2 ^ 16)), (Z.land_ones (b2 * 2 ^ 8 + b3)) by lia.
  rewrite (Z.mod_small (b1 * 2 ^ 16)), (Z.mod_small (b2 * 2 ^ 8 + b3)) by lia.
  assert (EA : Z.lor (b0 * 2 ^ 24) (b1 * 2 ^ 16) = (b0 * 2 ^ 8 + b1) * 2 ^ 16).
  { replace (b0 * 2 ^ 24) with ((b0 * 2 ^ 8) * 2 ^ 16) by lia.
    rewrite <- (Z.shiftl_mul_pow2 (b0 * 2 ^ 8) 16), <- (Z.shiftl_mul_pow2 b1 16) by lia. rewrite <- Z.shiftl_lor.
    rewrite (lor_hi_lo 8 b1 b0) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  rewrite EA. rewrite (lor_hi_lo 16 (b2 * 2 ^ 8 + b3) (b0 * 2 ^ 8 + b1)) by lia. lia.
Qed.

Lemma lor_lxor_lt1 : forall i h o l, 0 <= i -> 0 <= h -> 0 <= o -> 0 <= l ->
  (Z.lor (Z.lxor i h) (Z.lxor o l) <? 1) = ((i =? h) && (o =? l))%bool.
Proof.
  intros i h o l Hi Hh Ho Hl.
  assert (N1 : 0 <= Z.lxor i h) by (apply Z.lxor_nonneg; lia). assert (N2 : 0 <= Z.lxor o l) by (apply Z.lxor_nonneg; lia).
  assert (N3 : 0 <= Z.lor (Z.lxor i h) (Z.lxor o l)) by (apply Z.lor_nonneg; lia).
  destruct (Z.eqb_spec i h) as [E1|E1]; destruct (Z.eqb_spec o l) as [E2|E2]; cbn [andb].
  - subst. rewrite !Z.lxor_nilpotent. reflexivity.
  - apply Z.ltb_ge. destruct (Z.eq_dec (Z.lor (Z.lxor i h) (Z.lxor o l)) 0) as [E|E]; [|lia].
    apply Z.lor_eq_0_iff in E. destruct E as [_ E]. apply Z.lxor_eq in E. contradiction.
  - apply Z.ltb_ge. destruct (Z.eq_dec (Z.lor (Z.lxor i h) (Z.lxor o l)) 0) as [E|E]; [|lia].
    apply Z.lor_eq_0_iff in E. destruct E as [E _]. apply Z.lxor_eq in E. contradiction.
  - apply Z.ltb_ge. destruct (Z.eq_dec (Z.lor (Z.lxor i h) (Z.lxor o l)) 0) as [E|E]; [|lia].
    apply Z.lor_eq_0_iff in E. destruct E as [E _]. apply Z.lxor_eq in E. contradiction.
Qed.

Lemma bufrule_clang : forall f i h o l rt,
  0 <= f <= 4 -> 0 <= i < 2 ^ 32 -> 0 <= h < 2 ^ 32 -> 0 <= o < 2 ^ 32 -> 0 <= l < 2 ^ 32 -> - 2 ^ 31 <= rt < 2 ^ 31 ->
  Z.land (Z.lor (Z.b2z (Z.land (f + -4) 18446744073709551615 <? 1)) (Z.b2z (Z.lor (Z.lxor i h) (Z.lxor o l) <? 1)))
         (Z.b2z (Z.land rt 18446744073709551615 <? 1))
  = Z.b2z ((((wrap32 (i - h) =? 0) && (wrap32 (o - l) =? 0)) || (f =? 4)) && (rt =? 0))%bool.
Proof.
  intros f i h o l rt Hf Hi Hh Ho Hl Hr.
  rewrite lor_lxor_lt1 by lia.
  change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia.
  assert (E1 : ((f + -4) mod 2 ^ 64 <? 1) = (f =? 4)).
  { destruct (Z.eqb_spec f 4) as [->|NE]; [reflexivity|]. apply Z.ltb_ge.
    replace ((f + -4) mod 2 ^ 64) with (f + -4 + 2 ^ 64); [lia|]. symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia. }
  assert (E2 : (rt mod 2 ^ 64 <? 1) = (rt =? 0)).
  { destruct (Z.eqb_spec rt 0) as [->|NE]; [reflexivity|]. apply Z.ltb_ge.
    destruct (Z_lt_le_dec rt 0) as [L|L].
    - replace (rt mod 2 ^ 64) with (rt + 2 ^ 64); [lia|]. symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia.
    - rewrite Z.mod_small by lia. lia. }
  assert (E3 : (wrap32 (i - h) =? 0) = (i =? h)).
  { rewrite wrap32_mod. destruct (Z.eqb_spec i h) as [->|NE]; [rewrite Z.sub_diag; reflexivity|]. apply Z.eqb_neq.
    destruct (Z_lt_le_dec i h) as [L|L].
    - replace ((i - h) mod 2 ^ 32) with (i - h + 2 ^ 32); [lia|]. symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia.
    - rewrite Z.mod_small by lia. lia. }
  assert (E4 : (wrap32 (o - l) =? 0) = (o =? l)).
  { rewrite wrap32_mod. destruct (Z.eqb_spec o l) as [->|NE]; [rewrite Z.sub_diag; reflexivity|]. apply Z.eqb_neq.
    destruct (Z_lt_le_dec o l) as [L|L].
    - replace ((o - l) mod 2 ^ 32) with (o - l + 2 ^ 32); [lia|]. symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia.
    - rewrite Z.mod_small by lia. lia. }
  rewrite E1, E2, E3, E4.
  destruct (f =? 4); destruct ((i =? h) && (o =? l))%bool; destruct (rt =? 0); reflexivity.
Qed.

Lemma mask_eq_clang : forall wn ws, 0 <= wn < 2 ^ 32 -> 0 <= ws < 2 ^ 32 ->
  Z.land (Z.land (Z.b2z (Z.lxor wn ws <? 1) + -1) 18446744073709551615) wn = if wn =? ws then 0 else wn.
Proof.
  intros wn ws Hn Hs. destruct (Z.eqb_spec wn ws) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - assert (N : 0 <= Z.lxor wn ws) by (apply Z.lxor_nonneg; lia).
    assert (NZ : Z.lxor wn ws <> 0) by (intros E; apply Z.lxor_eq in E; contradiction).
    replace (Z.lxor wn ws <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
    change (Z.land (0 + -1) 18446744073709551615) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
