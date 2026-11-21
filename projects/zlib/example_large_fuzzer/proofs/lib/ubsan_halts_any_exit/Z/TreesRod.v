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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BvAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition A_length_code : Z := 0x2ea60.
Definition A_extra_lbits : Z := 0x2eb60.
Definition A_base_length : Z := 0x2ebd8.
Definition A_dist_code : Z := 0x2ec50.
Definition A_extra_dbits : Z := 0x2ee50.
Definition A_base_dist : Z := 0x2eec8.
Definition A_static_l_desc : Z := 0x2ef40.
Definition A_static_d_desc : Z := 0x2ef60.
Definition A_static_bl_desc : Z := 0x2ef80.
Definition A_static_dtree : Z := 0x2efa0.
Definition A_static_ltree : Z := 0x2f018.
Definition A_bl_order : Z := 0x2f498.
Definition A_extra_blbits : Z := 0x2f4b0.
Definition TREES_ROD_LO : Z := 0x2ea60.
Definition TREES_ROD_HI : Z := 0x2f4fc.

Section Rod.

End Rod.

Section RefReads.

Local Ltac ua := unfold TREES_ROD_LO, TREES_ROD_HI,
    A_length_code, A_extra_lbits, A_base_length, A_dist_code, A_extra_dbits, A_base_dist,
    A_static_dtree, A_static_ltree, A_bl_order, A_extra_blbits in *.

End RefReads.
