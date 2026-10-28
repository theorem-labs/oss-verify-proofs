(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Export Ubs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ubs_sw32 : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32 `div` 2)%Z with (2 ^ 31)%Z. lia.
Qed.
(* [comment removed for export] *)
Lemma ubs_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  assert (L : x = 0 \/ Z.log2 x < 64). { destruct (Z.eq_dec x 0) as [->|]; [left; reflexivity| right; apply Z.log2_lt_pow2; lia]. }
  assert (LG : x = 0 -> Z.log2 x < 64) by (intros ->; cbn; lia).
  assert (LL : Z.log2 x < 64) by (destruct L as [E|L']; [apply LG; exact E | exact L']).
  rewrite <- Z.ldiff_ones_l_low; [| lia | exact LL].
  symmetry. apply Z.sub_nocarry_ldiff. apply Z.ldiff_ones_r_low; [lia | exact LL].
Qed.
(* [comment removed for export] *)
Lemma ubs_land7_mod : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma ubs_land3_mod : forall x, 0 <= x -> Z.land x 3 = x mod 4.
Proof. intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma ubs_land15_mod : forall x, 0 <= x -> Z.land x 15 = x mod 16.
Proof. intros x Hx. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma ubs_sltu0_pos : forall x, 0 < x < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 1.
Proof. intros x Hx. rewrite v_sltu_b2z. rewrite !unsigned_lit by lia. replace (0 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma ubs_sltiu1_nz : forall x, 0 < x < 2 ^ 64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof. intros x Hx. rewrite v_sltiu_b2z. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1. replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma ubs_sltiu1_w_nz : forall x : word, bv_unsigned x <> 0 -> v_sltiu x 1 = Z_to_bv 64 0.
Proof. intros x Hx. rewrite v_sltiu_b2z. change (bv_wrap 64 1) with 1. pose proof (bv_unsigned_in_range 64 x). replace (bv_unsigned x <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma ubs_sltu0_w_nz : forall x : word, bv_unsigned x <> 0 -> v_sltu (Z_to_bv 64 0) x = Z_to_bv 64 1.
Proof. intros x Hx. rewrite v_sltu_b2z. rewrite unsigned_lit by lia. pose proof (bv_unsigned_in_range 64 x). replace (0 <? bv_unsigned x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma ubs_sltiu1_0 : v_sltiu (Z_to_bv 64 0) 1 = Z_to_bv 64 1. Proof. reflexivity. Qed.
Lemma ubs_sltu0_0 : v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0) = Z_to_bv 64 0. Proof. reflexivity. Qed.
