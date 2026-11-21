(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Malloc Require Import MallocKit_B F_ntf_A F_ntf_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition qa_facts (st : mstate) (sc : Z) (g : aptr) : Prop :=
  forall head, active st sc = Some head -> head <> g ->
    meta_slot st head /\
    exists pv, m_prev (get_meta_rec st head) = Some pv /\ pv <> g /\ meta_slot st pv.

Definition qpath_st (st : mstate) (sc : Z) (g : aptr) : mstate :=
  if optr_eqb (active st sc) (Some g) then st else queue_st (LActive sc) g st.

End CANSEC1.
