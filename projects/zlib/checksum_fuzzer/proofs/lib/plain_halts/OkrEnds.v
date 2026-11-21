(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(** * plain_halts.OkrEnds: the specification ends only with status 0 or 2

    [Spec.spec] (the specification that the halting walk of [plain_halts_any_exit] realizes) ends only by
    [t_exit] with [exit_code 0] or [exit_code 2], so every end is in [Exits.ok_or_refused].  The case split is
    the one of [SpecHalts.spec_ends_in]; only the exit leaves differ. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Core Require Shapes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import ShapeAlg Spec ShapeHalts SpecHalts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation OKR := OSSVerify.Core.Shapes.Exits.ok_or_refused.

Local Ltac okr_in :=
  unfold OSSVerify.Core.Shapes.Exits.ok_or_refused, exit_code; cbn [In];
  first [ left; reflexivity | right; left; reflexivity ].

Lemma okr_exit0 : forall fs, ends_in OKR (t_exit (exit_code 0) fs).
Proof. intros fs. apply ends_in_exit. okr_in. Qed.

Lemma okr_exit2 : forall fs, ends_in OKR (t_exit (exit_code 2) fs).
Proof. intros fs. apply ends_in_exit. okr_in. Qed.

Lemma okr_die : forall msg fs, ends_in OKR (t_die msg fs).
Proof.
  intros msg fs. unfold t_die. apply ends_in_emit; [apply no_terminal_W|]. apply okr_exit2.
Qed.

Lemma okr_body : forall data fs, ends_in OKR (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data)); [apply okr_die|].
  destruct (length data <? 6)%nat; [apply okr_die|].
  destruct (length data <? 6 + Z.to_nat ((bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) mod 32768))%nat; [apply okr_die|].
  assert (HS : forall calls, ends_in OKR (t_emit (W 1 (zero_lines calls)) (t_exit (exit_code 0) fs))).
  { intros calls. apply ends_in_emit; [apply no_terminal_W|]. apply okr_exit0. }
  destruct (length data - 6 - Z.to_nat ((bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) mod 32768))%nat.
  - apply HS.
  - apply ends_in_alt2; [| apply HS]. apply ends_in_exit.
    destruct (32768 <=? bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))); okr_in.
Qed.

Theorem okr_spec_ends_in : forall argv fs0, ends_in OKR (spec argv fs0).
Proof.
  intros argv fs0. unfold spec.
  destruct argv as [|a0 [|path [|x l]]]; try apply okr_die.
  destruct (4096 <=? length path)%nat; [apply okr_die|].
  destruct (list_byte_eqb path []); [apply okr_die|].
  destruct (list_byte_eqb path dot_path).
  - apply ends_in_alt2; [apply okr_die|]. unfold t_opened_dir. apply ends_in_alt2; apply okr_die.
  - destruct (fs_lookup fs0 path) as [data|]; [| apply okr_die].
    apply ends_in_alt2; [apply okr_die|]. unfold t_opened. apply ends_in_alt2; [apply okr_die | apply okr_body].
Qed.
