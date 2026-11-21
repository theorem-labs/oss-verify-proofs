(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Malloc Require Import MallocRep MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Malloc Require Export MallocBlocks.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition HINV_from (resv : list (Z * Z)) (st : mstate) (pbrk : Z) (LB : list block) : Prop :=
  brk_link st pbrk /\ AREACH_from resv st LB.
End CANSEC1.
Notation HINV := (HINV_from agent_reserved).

Section CANSEC2. Context {rc : runConstT}.
Lemma HINV_from_init : forall resv pbrk, HINV_from resv (minit 0 resv ATOP) pbrk [].
Proof. intros. split; [exact I | apply areach_init]. Qed.

Lemma HINV_init : forall pbrk, HINV (minit 0 agent_reserved ATOP) pbrk [].
Proof. intros. apply HINV_from_init. Qed.

Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof. intros st s. unfold brk_link_ps, brk_link. destruct (c_brk (ctx st)); tauto. Qed.


End CANSEC2.
