(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec StepTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptArith LeptArith2.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma bv_signed_Z : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma slt0_Z : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> v_slt (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 (if 0 <? x then 1 else 0).
Proof.
  intros x Hx. unfold v_slt, c_lts, bv_lts. rewrite (bv_signed_Z x Hx), (bv_signed_Z 0) by lia.
  unfold Z.ltb at 1. destruct (0 ?= x) eqn:E; unfold Z.ltb; rewrite E; reflexivity.
Qed.
Lemma slt0_pos : forall x, 1 <= x < 2 ^ 63 -> v_slt (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 1.
Proof. intros x Hx. rewrite slt0_Z by lia. replace (0 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma slt0_nonpos : forall x, - 2 ^ 63 <= x <= 0 -> v_slt (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 0.
Proof. intros x Hx. rewrite slt0_Z by lia. replace (0 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

(* [comment removed for export] *)
Lemma srai63_nn : forall x, 0 <= x < 2 ^ 63 -> v_srai (Z_to_bv 64 x) 63 = Z_to_bv 64 0.
Proof. intros x Hx. rewrite zbv_srai_small by lia. rewrite Z.div_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition msk0 (x : Z) : Z := if 0 <? x then -1 else 0.
Lemma negw_bit : forall x, v_subw (Z_to_bv 64 0) (Z_to_bv 64 (if 0 <? x then 1 else 0)) = Z_to_bv 64 (msk0 x).
Proof. intros x. rewrite v_subw_Z. unfold msk0. destruct (0 <? x); reflexivity. Qed.
Lemma neg_bit : forall x, v_sub (Z_to_bv 64 0) (Z_to_bv 64 (if 0 <? x then 1 else 0)) = Z_to_bv 64 (msk0 x).
Proof. intros x. rewrite zbv_sub. unfold msk0. destruct (0 <? x); reflexivity. Qed.

Lemma and_0_l : forall y : word, v_and (Z_to_bv 64 0) y = Z_to_bv 64 0.
Proof. intros y. unfold v_and. rewrite u_Z2bv by lia. rewrite Z.land_0_l. reflexivity. Qed.
Lemma and_m1_l : forall y : word, v_and (Z_to_bv 64 (-1)) y = y.
Proof.
  intros y. unfold v_and. pose proof (u64_range y) as Hy.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64) by (rewrite u_Z2bv_mod; reflexivity).
  rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. apply zbv_self.
Qed.
(* [comment removed for export] *)
Lemma and_msk0 : forall x, v_and (Z_to_bv 64 (msk0 x)) (Z_to_bv 64 x) = Z_to_bv 64 (Z.max 0 x).
Proof.
  intros x. unfold msk0. destruct (Z.ltb_spec 0 x).
  - rewrite and_m1_l. f_equal. lia.
  - rewrite and_0_l. f_equal. lia.
Qed.
Lemma and_msk0_nn : forall x, 0 <= x -> v_and (Z_to_bv 64 (msk0 x)) (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. rewrite and_msk0. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma subw_fit : forall a b, - 2 ^ 31 <= a - b < 2 ^ 31 -> v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H. rewrite v_subw_Z, sw32_small by lia. reflexivity. Qed.
Lemma addw_fit : forall a b, - 2 ^ 31 <= a + b < 2 ^ 31 -> v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b H. rewrite v_addw_Z, sw32_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma andi_31 : forall x : word, v_andi x 31 = Z_to_bv 64 (bv_unsigned x mod 32).
Proof. intros x. change 31 with (2 ^ 5 - 1). change 32 with (2 ^ 5). apply andi_ones. lia. Qed.
Lemma andi_31_Z : forall a, 0 <= a < 2 ^ 64 -> v_andi (Z_to_bv 64 a) 31 = Z_to_bv 64 (a mod 32).
Proof. intros a Ha. rewrite andi_31, u_Z2bv by lia. reflexivity. Qed.
Lemma or_andi31_0 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a mod 32 = 0 -> b mod 32 = 0 ->
  v_andi (v_or (Z_to_bv 64 a) (Z_to_bv 64 b)) 31 = Z_to_bv 64 0.
Proof.
  intros a b Ha Hb Ea Eb. rewrite andi_31. unfold v_or. rewrite (u_Z2bv a), (u_Z2bv b) by lia. rewrite u_Z2bv_mod.
  assert (D : (32 | 2 ^ 64)) by (exists (2 ^ 59); reflexivity).
  rewrite <- (Znumtheory.Zmod_div_mod 32 (2 ^ 64) (Z.lor a b) ltac:(lia) ltac:(lia) D).
  change 32 with (2 ^ 5). rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
  change (2 ^ 5) with 32. rewrite Ea, Eb. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zext_len4 : forall n, 1 <= n < 2 ^ 32 ->
  v_addi (v_srli (v_slli (Z_to_bv 64 (n - 1)) 32) 30) 4 = Z_to_bv 64 (4 * n).
Proof.
  intros n Hn. rewrite zbv_slli by lia. rewrite zbv_srli by lia. rewrite zbv_addi. f_equal.
  replace ((n - 1) * 2 ^ 32) with ((n - 1) * 4 * 2 ^ 30) by lia. rewrite Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma wpl_bits : forall w d, 0 <= w -> 1 <= d -> w * d <= 32 * wpl_of w d.
Proof. intros w d Hw Hd. unfold wpl_of. pose proof (Z.div_mod (w * d + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (w * d + 31) 32 ltac:(lia)). nia. Qed.

(* [comment removed for export] *)
Lemma col_hi : forall x n W, 0 <= x -> 1 <= n -> x + n <= 32 * W -> x / 32 + (n + 31) / 32 <= W \/ x mod 32 <> 0.
Proof.
  intros x n W Hx Hn H. destruct (Z.eq_dec (x mod 32) 0) as [E|NE]; [left | right; exact NE].
  pose proof (Z.div_mod x 32 ltac:(lia)). pose proof (Z.div_mod (n + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 31) 32 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma rop_rows_in : forall data wpl h y rh c nw i, 0 <= y -> 0 <= c -> 0 <= nw -> c + nw <= wpl -> y + rh <= h -> 0 <= i < rh ->
  data <= data + 4 * (y * wpl) + 4 * c + 4 * wpl * i /\ data + 4 * (y * wpl) + 4 * c + 4 * wpl * i + 4 * nw <= data + 4 * (wpl * h).
Proof. intros data wpl h y rh c nw i Hy Hc Hn Hcw Hyh Hi. split; nia. Qed.

(* [comment removed for export] *)
Lemma col_bound : forall X N W c nf k, X = 32 * c -> N = 32 * nf + k -> 0 <= k < 32 -> X + N <= 32 * W ->
  c + (nf + (if Z.eq_dec k 0 then 0 else 1)) <= W.
Proof. intros X N W c nf k EX EN Hk H. destruct (Z.eq_dec k 0); lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zext32_id : forall n, 0 <= n < 2 ^ 32 -> v_srli (v_slli (Z_to_bv 64 n) 32) 32 = Z_to_bv 64 n.
Proof. intros n Hn. rewrite zbv_slli by lia. rewrite zbv_srli by lia. f_equal. rewrite Z.div_mul by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition len4 (nfw : Z) : word := v_addi (v_srli (v_slli (Z_to_bv 64 (nfw - 1)) 32) 30) 4.

(* [comment removed for export] *)
Lemma c_eq_Z0s : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> c_eq (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. rewrite c_eq_Zm. rewrite (Z.mod_small 0) by lia.
  destruct (Z.eqb_spec x 0) as [->|NE]; [reflexivity|]. apply Z.eqb_neq. intros E.
  destruct (Z_lt_ge_dec x 0).
  - replace x with (x + 2 ^ 64 + (-1) * 2 ^ 64) in E by lia. rewrite Z_mod_plus_full in E. rewrite Z.mod_small in E by lia. lia.
  - rewrite Z.mod_small in E by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma c_lts_Zs : forall a b : Z, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 -> c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold c_lts, bv_lts. rewrite !bv_signed_Z by lia. reflexivity. Qed.

Lemma and_m1u_l : forall y : word, v_and (Z_to_bv 64 18446744073709551615) y = y.
Proof. intros y. replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply bv_eq; reflexivity). apply and_m1_l. Qed.

Lemma addiw_fit : forall a i, - 2 ^ 31 <= a + i < 2 ^ 31 -> v_addiw (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i H. rewrite LeptArith2.v_addiw_Z, sw32_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma andi3_Z0 : forall a, 0 <= a < 2 ^ 64 -> a mod 4 = 0 -> v_andi (Z_to_bv 64 a) 3 = Z_to_bv 64 0.
Proof. intros a Ha E. rewrite W2Lib.andi_3, u_Z2bv by lia. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall a, 0 <= a < 2 ^ 64 -> Z.lxor a (2 ^ 64 - 1) = 2 ^ 64 - 1 - a.
Proof.
  intros a Ha. replace (2 ^ 64 - 1 - a) with ((Z.lnot a) mod 2 ^ 64).
  2:{ unfold Z.lnot. replace (Z.pred (- a)) with ((2 ^ 64 - 1 - a) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  change (2 ^ 64 - 1) with (Z.ones 64). apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec.
  destruct (Z_lt_ge_dec n 64).
  - rewrite Z.ones_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia. destruct (Z.testbit a n); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite Z.mod_pow2_bits_high by lia. rewrite xorb_false_r.
    replace a with (a mod 2 ^ 64) by (apply Z.mod_small; lia). apply Z.mod_pow2_bits_high. lia.
Qed.
Lemma zbv_not : forall a, 0 <= a < 2 ^ 64 -> v_xori (Z_to_bv 64 a) (-1) = Z_to_bv 64 (2 ^ 64 - 1 - a).
Proof. intros a Ha. unfold v_xori. rewrite u_Z2bv by lia. change (bv_wrap 64 (-1)) with (2 ^ 64 - 1). rewrite lxor_ones64 by lia. reflexivity. Qed.
