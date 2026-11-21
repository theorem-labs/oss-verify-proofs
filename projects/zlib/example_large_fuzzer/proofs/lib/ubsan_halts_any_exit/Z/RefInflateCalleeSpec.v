(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition offblk (a n : Z) : Prop := a + n <= 0x10000 \/ 0x36000 <= a.

Set Implicit Arguments.
Unset Implicit Arguments.

Definition ff_msg_addr (a : Z) : Z :=
  if a =? MSG_invalid_literal_length_code then 0x2dc30
  else if a =? MSG_invalid_distance_code then 0x2dc50 else 0x2dc68.

Definition inflate_fast_congr_stmt : Prop :=
  forall (s : inflate_state) (c : icall) (r : iregs) (ob : arr),
    arr_len ob = arr_len (ic_outbuf c) ->
    (forall i, 0 <= i < ic_next_out c -> arr_get ob i = arr_get (ic_outbuf c) i) ->
    (forall i, 0 <= i < arr_len ob -> 0 <= arr_get ob i < 256) ->
    ff_ok s c r = true ->
    wrap32 (ir_out r - ic_avail_out c) <= ic_next_out c ->
    arr_len (ic_outbuf c) < 2 ^ 32 ->
    0 <= is_wnext s ->
    let w1 := inflate_fast (mkW s c r) in
    let w2 := inflate_fast (mkW s (icset_outbuf c ob) r) in
    ff_ok s (icset_outbuf c ob) r = true
    /\ w_s w2 = w_s w1 /\ w_r w2 = w_r w1
    /\ w_c w2 = icset_outbuf (w_c w1) (ic_outbuf (w_c w2))
    /\ arr_len (ic_outbuf (w_c w2)) = arr_len (ic_outbuf (w_c w1))
    /\ (forall i, 0 <= i < ic_next_out (w_c w1) -> arr_get (ic_outbuf (w_c w2)) i = arr_get (ic_outbuf (w_c w1)) i).

Set Implicit Arguments.
Unset Implicit Arguments.
