(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: written for simdjson/fuzz_utf8's ubsan binary from simdjson/fuzz_minifyimpl's proofs/lib/Ubsan/UM_client.v: the client statement is closed from this harness's parts (validate_utf8, the join, the first and later calls) instead of minify's lambda, vector, string and assign proofs. *)
(* fuzz_utf8's UBSan client statement, closed from its parts. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Malloc PState HarnessU ProgP.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import RunDraw PU_iface PM_iface UM_vutf8 UM_fuzz UM_fuzzF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

  (* The later calls (vector built) by the join from validate_utf8; the first call by fuzz_first_proof. *)
  Theorem fuzz_oneM_proof : opnew_stmt -> opdelete_stmt -> fuzz_oneU_stmt ProgP.fuzz_one.
  Proof.
    intros ON OD. pose proof (fuzz_join_proof vutf8_proof) as JN.
    pose proof (fuzz_first_proof ON JN) as FF. unfold fuzz_first_stmt in FF.
    unfold fuzz_oneU_stmt. intros.
    destruct (ps_fa s) as [p|] eqn:FA.
    - eapply (fuzz_later vutf8_proof); eassumption.
    - eapply FF; eassumption.
  Qed.
End CANSEC1.

(* The statement UbsanClosed.ubsan_client_stmt asks. *)
Theorem ubsan_client_proof : forall rc : runConstT, @opnew_stmt rc -> @opdelete_stmt rc -> @fuzz_oneU_stmt rc ProgP.fuzz_one.
Proof. intros rc ON OD. exact (@fuzz_oneM_proof rc ON OD). Qed.
