(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec SymExec3 SymExec3Sound.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HCommon.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma w_sltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
    alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
  Proof.
    intros a b Ha Hb. apply bv_eq. rewrite u_sltu64, !u64_of_Z by lia.
    destruct (a <? b); rewrite u64_of_Z by lia; reflexivity.
  Qed.

Lemma w_or : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  alu64 ALU_OR (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lor a b).
Proof.
  intros a b Ha Hb. apply bv_eq. cbn [alu64 alu].
  rewrite bv_or_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small a), (Z.mod_small b) by lia.
  assert (0 <= Z.lor a b < 2 ^ 64).
  { split; [apply Z.lor_nonneg; lia|].
    destruct (Z.eq_dec (Z.lor a b) 0) as [->|Hnz]; [lia|].
    apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg a b); lia|].
    rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt.
    - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
    - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma lor_2b : forall a b, (a = 0 \/ a = 1) -> 0 <= b -> Z.lor a (2 * b) = 2 * b + a.
Proof.
  intros a b [-> | ->] Hb; [rewrite Z.lor_0_l; lia|].
  pose proof (Z.add_lor_land 1 (2 * b)) as H. rewrite (Z.land_comm 1), land_1 in H.
  replace ((2 * b) mod 2) with 0 in H by (symmetry; rewrite Z.mul_comm; apply Z_mod_mult). lia.
Qed.

Lemma w_srl : forall a k, 0 <= a < 2 ^ 64 -> 0 <= k < 64 ->
  alu64 ALU_SRL (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a / 2 ^ k).
Proof.
  intros a k Ha Hk. apply bv_eq. cbn [alu64 alu].
  rewrite bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small a), (Z.mod_small k), (Z.mod_small 63) by lia.
  replace (Z.land k 63) with k.
  2:{ change 63 with (Z.ones 6). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
  rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= a / 2 ^ k <= a) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; try lia; nia]).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma w_xor : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  alu64 ALU_XOR (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lxor a b).
Proof.
  intros a b Ha Hb. apply bv_eq. cbn [alu64 alu].
  rewrite bv_xor_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small a), (Z.mod_small b) by lia.
  assert (0 <= Z.lxor a b < 2 ^ 64).
  { split; [apply Z.lxor_nonneg; lia|].
    destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
    apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); lia|].
    eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
    apply Z.max_lub_lt.
    - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
    - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma land_7 : forall a, Z.land a 7 = a mod 8.
Proof. intros a. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma w_notexpr : forall p, 0 <= p < 2 ^ 64 ->
  alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 p)) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - p).
Proof.
  intros p Hp. apply bv_eq. cbn [alu64 alu mul_div].
  rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small p) by lia.
  rewrite Z.mul_mod_idemp_l, Zplus_mod_idemp_l, Zplus_mod_idemp_r by lia.
  replace (-1 * p + -1) with ((2 ^ 64 - 1 - p) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
