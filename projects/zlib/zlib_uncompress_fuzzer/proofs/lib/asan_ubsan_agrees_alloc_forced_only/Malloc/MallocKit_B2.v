(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Malloc Require Import MallocRep F_malloc_free F_malloc_enframe MallocTree MallocKit_B.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma peek_ok_pans o p c h : peek_answer_ok (pans_mem o p c h) = true.
Proof.
  pose proof (pans_mem_range o p c h). unfold peek_answer_ok.
  apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.



Definition grp_region_addr (st : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

End CANSEC1.
