(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma testbit_high64 : forall x n, 0 <= x < 18446744073709551616 -> 64 <= n -> Z.testbit x n = false.
Proof.
  intros x n Hx Hn. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [| exact Hn].
  apply Z.log2_lt_pow2; [lia|]. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

Lemma lnot64 : forall x, 0 <= x < 18446744073709551616 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  assert (L : Z.land x (Z.lxor x (Z.ones 64)) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z.ltb_spec n 64).
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
    - rewrite (testbit_high64 x n Hx) by lia. reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ L) as E.
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in E. lia.
Qed.

Lemma land1_even : forall x, x mod 2 = 0 -> Z.land x 1 = 0.
Proof. intros x H. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. exact H. Qed.

Lemma zext32_shift31 : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 31 = 2 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Lemma srliw30_small : forall x, 0 <= x < 1073741824 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 30) = 0.
Proof.
  intros x Hx. replace (bv_wrap 32 x) with x by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; rewrite Z.mod_small by lia; reflexivity).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 30) with 1073741824. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma fub_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma fub_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma fub_land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
