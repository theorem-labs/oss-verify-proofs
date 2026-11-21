(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CrcRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition CRCTAB : Z := 0x2f550.
Definition BRAIDTAB : Z := 0x2f9d0.
Definition braid_entry (e : Z) : Z := braid_tab (Z.to_nat (e / 256)) (e mod 256).

Lemma crc_tab_range : forall i, 0 <= i < 256 -> 0 <= crc_tab i < 2 ^ 32.
Proof. intros i Hi. unfold crc_tab. apply (xtn_range 8 i). lia. Qed.

Lemma braid_tab_range : forall k i, 0 <= i < 256 -> 0 <= braid_tab k i < 2 ^ 32.
Proof.
  intros k i Hi. unfold braid_tab. apply xtn_range.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 24) with 16777216. lia.
Qed.

Lemma braid_entry_eq : forall k i, 0 <= i < 256 ->
  braid_entry (256 * Z.of_nat k + i) = braid_tab k i.
Proof.
  intros k i Hi. unfold braid_entry.
  replace ((256 * Z.of_nat k + i) / 256) with (Z.of_nat k)
    by (rewrite Z.add_comm, Z.mul_comm, Z.div_add, Z.div_small; lia).
  replace ((256 * Z.of_nat k + i) mod 256) with i
    by (rewrite Z.add_comm, Z.mul_comm, Z.mod_add, Z.mod_small; lia).
  rewrite Nat2Z.id. reflexivity.
Qed.
