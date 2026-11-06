(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Lemmas shared by the walks of the check_ functions of fuzz/fuzz_decode.c in fuzz_decode.plain:
   the value of an lw of a cell holding a C int, of an lbu of a cell holding a byte, the results of
   seqz / snez, and the beq / bne tests on such values, each stated over Z.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec.
Import ListNotations.
Open Scope Z_scope.

(* lw of a cell C4 (Z_to_bv 64 z) whose z is a C int *)
Lemma sx32_int : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  replace (2^64) with 18446744073709551616 by reflexivity.
  replace (2^32) with 4294967296 by reflexivity. replace (2^31) with 2147483648 by reflexivity.
  replace (2^31) with 2147483648 in Hz by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* beq / bne of two 64-bit values that are signed 64-bit integers *)
Lemma eqb_int64 : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  replace (2^64) with 18446744073709551616 in E by reflexivity.
  replace (2^63) with 9223372036854775808 in Hx, Hy by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* seqz (sltiu x, 1) of a signed 64-bit integer *)
Lemma sltiu1_int : forall z, -2^63 <= z < 2^63 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 (Z.b2z (z =? 0)).
Proof.
  intros z Hz. rewrite v_sltiu_b2z. f_equal. f_equal.
  rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
  replace (2^64) with 18446744073709551616 by reflexivity.
  replace (2^63) with 9223372036854775808 in Hz by reflexivity.
  destruct (Z.eqb_spec z 0) as [->|N]; [reflexivity|].
  apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

(* snez (sltu zero, x) of a signed 64-bit integer *)
Lemma sltu0_int : forall z, -2^63 <= z < 2^63 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 (Z.b2z (negb (z =? 0))).
Proof.
  intros z Hz. rewrite v_sltu_b2z. f_equal. f_equal.
  rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  replace (2^64) with 18446744073709551616 by reflexivity.
  replace (2^63) with 9223372036854775808 in Hz by reflexivity.
  destruct (Z.eqb_spec z 0) as [->|N]; [reflexivity|].
  apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

(* lbu of a cell C1 (b8 z) whose z is a byte *)
Lemma zxb_b8 : forall z, 0 <= z < 256 -> zxb (b8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zxb, b8. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. exact Hz.
Qed.

(* a test of a value against itself *)
Lemma eqb_same : forall (x : word), bv_eqb x x = true.
Proof. intros x. apply bv_eqb_refl. Qed.
