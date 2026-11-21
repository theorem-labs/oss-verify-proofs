(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItTable.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition IT_SAFE_INTRO : Prop :=
  forall (ty : codetype) (lens : arr) (lens_ofs codes : Z) (tbl : arr) (table bits : Z) (work : arr),
    0 <= codes <= 288 -> codes <= arr_len work -> arr_len work <= 65536 ->
    0 <= lens_ofs -> lens_ofs + codes <= arr_len lens ->
    (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15) ->
    ty_ok ty (lens_list lens lens_ofs codes) bits ->
    1 <= bits <= 15 -> 0 <= table -> table + it_room ty <= arr_len tbl ->
    it_safe ty lens lens_ofs codes tbl table bits work = true.
