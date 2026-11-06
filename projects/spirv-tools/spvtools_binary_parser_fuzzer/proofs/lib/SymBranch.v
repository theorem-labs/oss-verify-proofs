(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import StepTac.
From stdpp Require Import bitvector.bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma bv_signed_small : forall (x : word),
  bv_unsigned x < 2 ^ 63 -> bv_signed x = bv_unsigned x.
Proof.
  intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Hr.
  unfold bv_signed. apply bv_swrap_small.
  assert (Hh : bv_half_modulus 64 = 9223372036854775808) by (vm_compute; reflexivity).
  rewrite Hh. change (2 ^ 63) with 9223372036854775808 in Hx. lia.
Qed.

Lemma bv_signed_lit : forall z : Z,
  - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small.
  assert (Hh : bv_half_modulus 64 = 9223372036854775808) by (vm_compute; reflexivity).
  rewrite Hh. change (2 ^ 63) with 9223372036854775808 in Hz. lia.
Qed.

Lemma v_addiw_range : forall (x : word) imm,
  0 <= bv_unsigned x + imm -> bv_unsigned x + imm < 2 ^ 31 ->
  bv_unsigned (v_addiw x imm) = bv_unsigned x + imm.
Proof.
  intros x imm Hlo Hhi. unfold v_addiw.
  rewrite Z_to_bv_unsigned.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Ltac sym_br :=
  rewrite ?negb_true_iff, ?negb_false_iff;
  unfold bv_lts, bv_ltu, bv_eqb;
  rewrite ?bv_signed_lit by lia;
  rewrite ?bv_signed_small by (rewrite ?v_addiw_range by lia; u_norm; lia);
  rewrite ?v_addiw_range by lia;
  u_norm;
  rewrite ?Z.ltb_ge, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.eqb_neq;
  lia.
