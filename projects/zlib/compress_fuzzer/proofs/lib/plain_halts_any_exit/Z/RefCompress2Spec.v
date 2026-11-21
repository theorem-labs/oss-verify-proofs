(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition DEFLATE_PROGRESS : Prop :=
  forall (s : deflate_state) (zc : ZCall) (flush : Z),
    INV s -> dreach s -> dcall_wf zc ->
    (flush = Z_FINISH \/ (flush = Z_NO_FLUSH /\ 0 < zlength (zc_input zc))) ->
    zr_rc (snd (deflate_m s zc flush)) = Z_OK ->
    0 < zr_consumed (snd (deflate_m s zc flush)) + zlength (zr_output (snd (deflate_m s zc flush))).
