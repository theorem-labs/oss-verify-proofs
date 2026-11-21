(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkCrc.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ListFacts.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import CrcBraid.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import CrcRod.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCrcRod.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".

Definition FT : nat -> Z -> Z := fun f x =>
  match f with 0%nat => crc_tab (x mod 256) | S k => braid_tab k (x mod 256) end.

Lemma In_skipn_w {A} (x : A) : forall i (l : list A), In x (skipn i l) -> In x l.
Proof.
  induction i as [|i IH]; intros [|y l] H; cbn in H; try exact H.
  right. apply IH. exact H.
Qed.

Lemma mod64_mod32 : forall a, (a mod 2 ^ 64) mod 2 ^ 32 = a mod 2 ^ 32.
Proof.
  intros a. rewrite <- Znumtheory.Zmod_div_mod; try lia.
  exists (2 ^ 32). reflexivity.
Qed.

Definition c0_of (crc : Z) : Z := (Z.lxor crc (-1)) mod 2 ^ 32.

Definition MASK : Z := 4294967295.

Definition hide (Q : Prop) : Prop := Q.
