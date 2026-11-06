(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Class AllocCeiling : Type := mkAllocCeiling {
  alloc_ceiling : Z;
  ac_bounds : sp_window_lo - stack_max_size <= alloc_ceiling <= sp_window_hi - stack_max_size;
  ac_align : alloc_ceiling mod 16 = 0
}.

Section WithAC.
Context {AC : AllocCeiling}.

Lemma ac_bounds_lit : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof.
  pose proof ac_bounds as H. unfold sp_window_lo, sp_window_hi, stack_max_size in H. lia.
Qed.

Lemma alloc_ceiling_lt_task_size : alloc_ceiling < TASK_SIZE.
Proof. pose proof ac_bounds_lit. unfold TASK_SIZE. lia. Qed.

End WithAC.

Lemma ac_of_sp_bounds : forall sp : word, valid_sp sp ->
  sp_window_lo - stack_max_size <= bv_unsigned sp - stack_max_size <= sp_window_hi - stack_max_size.
Proof. intros sp (H1 & H2 & _). lia. Qed.

Lemma ac_of_sp_align : forall sp : word, valid_sp sp ->
  (bv_unsigned sp - stack_max_size) mod 16 = 0.
Proof.
  intros sp (_ & _ & H3). unfold stack_max_size.
  replace (bv_unsigned sp - 8 * 1024 * 1024) with (bv_unsigned sp + (-524288) * 16) by lia.
  rewrite Z_mod_plus_full. exact H3.
Qed.

Definition ac_of_sp (sp : word) (Hsp : valid_sp sp) : AllocCeiling :=
  mkAllocCeiling (bv_unsigned sp - stack_max_size) (ac_of_sp_bounds sp Hsp) (ac_of_sp_align sp Hsp).

