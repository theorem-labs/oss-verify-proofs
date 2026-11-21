(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Malloc Require Import MallocRep F_malloc_free.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Malloc Require Import MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Malloc Require Import MallocKit_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition fm_facts (st : mstate) (g : aptr) : Prop :=
  forall head, c_free_meta_head (ctx st) = Some head ->
    head <> g /\ meta_slot st head /\
    exists pv, m_prev (get_meta_rec st head) = Some pv /\ pv <> g /\ meta_slot st pv.

Lemma meta_word_meta0 : meta_word meta0 = 0. Proof. reflexivity. Qed.

End CANSEC1.
