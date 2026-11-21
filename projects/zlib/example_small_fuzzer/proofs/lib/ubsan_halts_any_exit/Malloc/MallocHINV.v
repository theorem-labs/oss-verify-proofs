(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocRep MallocTree.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Export MallocBlocks.
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
Definition HINV_from (resv : list (Z * Z)) (st : mstate) (pbrk : Z) (LB : list block) : Prop :=
  brk_link st pbrk /\ AREACH_from resv st LB.

Lemma HINV_from_init : forall resv pbrk, HINV_from resv (minit 0 resv) pbrk [].
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros. split; [exact I | apply areach_init]. Qed.

Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros st s. unfold brk_link_ps, brk_link. destruct (c_brk (ctx st)); tauto. Qed.
End WithCeiling0.
