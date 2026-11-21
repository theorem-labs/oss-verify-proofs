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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition bs_code (b : block_state) : Z :=
  match b with need_more => 0 | block_done => 1 | finish_started => 2 | finish_done => 3 end.

Definition DFAST_FRAME : Z := 368.
Definition DSLOW_FRAME : Z := 384.
Definition DSTORED_FRAME : Z := 208.


