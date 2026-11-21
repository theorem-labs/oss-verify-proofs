(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition AS_STACK (fuel : nat) : Z := 128 + 96 * Z.of_nat fuel.

Lemma AS_STACK_S f : AS_STACK (S f) = AS_STACK f + 96.
Proof. unfold AS_STACK. rewrite Nat2Z.inj_succ. lia. Qed.
Lemma AS_STACK_ge f : 128 <= AS_STACK f.
Proof. unfold AS_STACK. lia. Qed.

End CANSEC1.
