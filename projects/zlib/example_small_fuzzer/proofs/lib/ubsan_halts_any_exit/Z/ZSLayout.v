(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record zs_ptrs : Type := ZSP {
  zp_in : Z; zp_out : Z; zp_zalloc : Z; zp_zfree : Z; zp_opaque : Z; zp_reserved : Z;
  zp_msg : Z -> Z }.

Definition zsl_SIZE : Z := 112.

Definition zsl_layout : list (Z * nat) := [
  (0, 8%nat) ;
  (8, 4%nat) ;
  (16, 8%nat) ;
  (24, 8%nat) ;
  (32, 4%nat) ;
  (40, 8%nat) ;
  (48, 8%nat) ;
  (56, 8%nat) ;
  (64, 8%nat) ;
  (72, 8%nat) ;
  (80, 8%nat) ;
  (88, 4%nat) ;
  (96, 8%nat) ;
  (104, 8%nat) ].

Definition zsl_vals (p : zs_ptrs) (S : Z) (st : cstrm) : list Z := [
  zp_in p + cs_next_in st ;
  cs_avail_in st ;
  cs_total_in st ;
  zp_out p + Z.of_nat (length (cs_out_rev st)) ;
  cs_avail_out st ;
  cs_total_out st ;
  zp_msg p (cs_msg st) ;
  S ;
  zp_zalloc p ;
  zp_zfree p ;
  zp_opaque p ;
  cs_data_type st ;
  cs_adler st ;
  zp_reserved p ].

Lemma zsl_layout_within : layout_within zsl_layout zsl_SIZE = true.
Proof. vm_compute. reflexivity. Qed.

Section WithImage.
End WithImage.
