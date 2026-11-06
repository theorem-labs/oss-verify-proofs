(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import MState Mem ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import PC_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma land_low_of_mod : forall A k, 0 <= k -> A mod 2 ^ k = 0 -> Z.land A (Z.ones k) = 0.
Proof. intros A k Hk H. rewrite Z.land_ones by exact Hk. exact H. Qed.
Lemma mod_of_mod_mul : forall A a b, 0 < a -> 0 < b -> A mod (a * b) = 0 -> A mod a = 0.
Proof.
  intros A a b Ha Hb H. apply Z.mod_divide in H; [|lia]. destruct H as [q Hq]. subst A.
  replace (q * (a * b)) with ((q * b) * a) by ring. apply Z.mod_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma land7_of_mod8 : forall A, A mod 8 = 0 -> Z.land A 7 = 0.
Proof. intros A H. change 7 with (Z.ones 3). apply land_low_of_mod; [lia| exact H]. Qed.
Lemma land7_of_mod16 : forall A, A mod 16 = 0 -> Z.land A 7 = 0.
Proof. intros A H. apply land7_of_mod8. apply (mod_of_mod_mul A 8 2); [lia| lia| exact H]. Qed.
Lemma land15_of_mod16 : forall A, A mod 16 = 0 -> Z.land A 15 = 0.
Proof. intros A H. change 15 with (Z.ones 4). apply land_low_of_mod; [lia| exact H]. Qed.
Lemma land3_of_mod4 : forall A, A mod 4 = 0 -> Z.land A 3 = 0.
Proof. intros A H. change 3 with (Z.ones 2). apply land_low_of_mod; [lia| exact H]. Qed.
Lemma land3_of_mod8 : forall A, A mod 8 = 0 -> Z.land A 3 = 0.
Proof. intros A H. apply land3_of_mod4. apply (mod_of_mod_mul A 4 2); [lia| lia| exact H]. Qed.
Lemma land3_of_mod16 : forall A, A mod 16 = 0 -> Z.land A 3 = 0.
Proof. intros A H. apply land3_of_mod4. apply (mod_of_mod_mul A 4 4); [lia| lia| exact H]. Qed.
Lemma mod8_add : forall A k, A mod 8 = 0 -> k mod 8 = 0 -> (A + k) mod 8 = 0.
Proof. intros A k H1 H2. rewrite Z.add_mod by lia. rewrite H1, H2. reflexivity. Qed.
Lemma mod8_of_mod16 : forall A, A mod 16 = 0 -> A mod 8 = 0.
Proof. intros A H. apply (mod_of_mod_mul A 8 2); [lia| lia| exact H]. Qed.

(* [comment removed for export] *)
Ltac land_m64_in K := rewrite ?land_ones64 in K by lia.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  assert (E : Z.lxor x (Z.ones 64) = Z.ldiff (Z.ones 64) x).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec.
    destruct (Z.ltb_spec n 64) as [L|L].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
    - rewrite Z.ones_spec_high by lia.
      assert (T : Z.testbit x n = false).
      { destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.testbit_0_l|].
        apply Z.bits_above_log2; [lia|]. pose proof (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia)) ltac:(lia)); lia. }
      rewrite T. reflexivity. }
  rewrite E. rewrite Z.sub_nocarry_ldiff; [reflexivity|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.bits_0.
  destruct (Z.ltb_spec n 64) as [L|L].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
  - assert (T : Z.testbit x n = false).
    { destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.testbit_0_l|].
      apply Z.bits_above_log2; [lia|]. pose proof (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia)) ltac:(lia)); lia. }
    rewrite T. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sx32_small : forall e, 0 <= e < 2 ^ 31 -> bv_unsigned (sx32 (Z_to_bv 64 e)) = e.
Proof.
  intros e He. unfold sx32. rewrite (unsigned_lit e) by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow].
  change (2 ^ 32 / 2) with (2 ^ 31).
  replace ((e + 2 ^ 31) mod 2 ^ 32) with (e + 2 ^ 31) by (symmetry; apply Z.mod_small; lia).
  replace (e + 2 ^ 31 - 2 ^ 31) with e by lia. apply unsigned_lit. lia.
Qed.
