(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocRep MallocTree MallocFacts_A MallocKit_A Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require InitMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocFacts_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.Malloc_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A2.MallocKit_AB OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.InitMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import Malloc_fp F_malloc_top F_malloc_big.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_inv2.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling}.
Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.
End WithCeiling0.
