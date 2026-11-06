(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Fixpoint le_val (bs : list Z) : Z :=
  match bs with [] => 0 | b :: bs' => b + 256 * le_val bs' end.
Fixpoint ones (n : nat) : Z := match n with O => 0 | S n' => 1 + 256 * ones n' end.
Definition highs (n : nat) : Z := 128 * ones n.
Definition bytes_ok (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.

Lemma le_val_range : forall bs, bytes_ok bs -> 0 <= le_val bs < 256 ^ Z.of_nat (length bs).
Proof.
  induction bs as [|b bs IH]; intros H; cbn [le_val length]; [lia|].
  inversion H; subst. specialize (IH ltac:(assumption)).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma testbit_split : forall x y i, 0 <= x < 256 -> 0 <= i ->
  Z.testbit (x + 256 * y) i = if i <? 8 then Z.testbit x i else Z.testbit y (i - 8).
Proof.
  intros x y i Hx Hi. destruct (Z.ltb_spec0 i 8).
  - rewrite <- (Z.mod_pow2_bits_low _ 8) by lia. change (2^8) with 256.
    rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia. reflexivity.
  - replace i with ((i - 8) + 8) at 1 by lia. rewrite <- Z.div_pow2_bits by lia. change (2^8) with 256.
    rewrite (Z.mul_comm 256 y), Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.

Lemma lor_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros a b n Ha Hb.
  assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  pose proof (Z.lor_nonneg a b) as Hnn. split; [lia|].
  destruct (Z.eq_dec a 0) as [->|]. { rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0) as [->|]. { rewrite Z.lor_0_r. lia. }
  assert (Hp : 0 < Z.lor a b). { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n Hp)). rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Definition ONES64b  : Z := 0x0101010101010101.
Definition HIGHS64b : Z := 0x8080808080808080.

Lemma testbit_high_false : forall x n i, 0 <= x < 2^n -> 0 <= n <= i -> Z.testbit x i = false.
Proof.
  intros x n i Hx Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with n; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma land_mod_pow2_r : forall a b n, 0 <= a < 2^n -> 0 <= n -> Z.land a (b mod 2^n) = Z.land a b.
Proof.
  intros a b n Ha Hn. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i n).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite (testbit_high_false a n i) by lia. reflexivity.
Qed.

Lemma lor_shiftl8_add : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (Z.shiftl y 8) = x + 256 * y.
Proof.
  intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
  rewrite <- Z.lxor_lor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
       replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
       destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
       rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
       destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia]. }
  symmetry. replace (256 * y) with (y * 256) by lia. apply Z.add_nocarry_lxor.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
  destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
  rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
  destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma bytes_ok_map : forall bs : list byte, bytes_ok (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
Qed.

Lemma bytes_le_to_Z_le_val : forall bs : list byte, bytes_le_to_Z bs = le_val (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z le_val map]; [reflexivity|].
  rewrite IH. apply lor_shiftl8_add.
  - pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
  - pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)). lia.
Qed.

End AC_1.
