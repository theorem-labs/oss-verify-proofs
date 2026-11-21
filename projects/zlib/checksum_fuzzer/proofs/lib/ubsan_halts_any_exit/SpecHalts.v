(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import ShapeAlg Spec ShapeHalts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma no_terminal_W : forall ch s, no_terminal (W ch s).
Proof.
  intros ch s e Hin. unfold W in Hin. apply in_map_iff in Hin.
  destruct Hin as (b & <- & _). exact I.
Qed.

Lemma ends_in_exit_code : forall z fs, 0 <= z < 256 -> ends_in AnyExit.codes (t_exit (exit_code z) fs).
Proof. intros z fs Hz. apply ends_in_exit. unfold exit_code, AnyExit.codes. apply in_byte_codes. exact Hz. Qed.

Lemma ends_in_die : forall msg fs, ends_in AnyExit.codes (t_die msg fs).
Proof.
  intros msg fs. unfold t_die. apply ends_in_emit; [apply no_terminal_W|]. apply ends_in_exit_code. lia.
Qed.

Lemma ends_in_body : forall data fs, ends_in AnyExit.codes (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data)); [apply ends_in_die|].
  destruct (length data <? 6)%nat; [apply ends_in_die|].
  destruct (length data <? 6 + Z.to_nat ((bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) mod 32768))%nat; [apply ends_in_die|].
  assert (HS : forall calls, ends_in AnyExit.codes (t_emit (W 1 (zero_lines calls)) (t_exit (exit_code 0) fs))).
  { intros calls. apply ends_in_emit; [apply no_terminal_W|]. apply ends_in_exit_code. lia. }
  destruct (length data - 6 - Z.to_nat ((bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) mod 32768))%nat.
  - apply HS.
  - apply ends_in_alt2; [| apply HS]. apply ends_in_exit_code.
    destruct (32768 <=? bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))); lia.
Qed.

Theorem spec_ends_in : forall argv fs0, ends_in AnyExit.codes (spec argv fs0).
Proof.
  intros argv fs0. unfold spec.
  destruct argv as [|a0 [|path [|x l]]]; try apply ends_in_die.
  destruct (4096 <=? length path)%nat; [apply ends_in_die|].
  destruct (list_byte_eqb path []); [apply ends_in_die|].
  destruct (list_byte_eqb path dot_path).
  - apply ends_in_alt2; [apply ends_in_die|]. unfold t_opened_dir. apply ends_in_alt2; apply ends_in_die.
  - destruct (fs_lookup fs0 path) as [data|]; [| apply ends_in_die].
    apply ends_in_alt2; [apply ends_in_die|]. unfold t_opened. apply ends_in_alt2; [apply ends_in_die | apply ends_in_body].
Qed.
