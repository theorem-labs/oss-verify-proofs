(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Malloc PState HarnessM ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RunDraw PU_iface PM_iface UM_vctor UM_strctor UM_assign UM_lam UM_fuzz UM_fuzzF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

  (* [comment removed for export] *)
  Lemma lam_closed : opnew_stmt -> opdelete_stmt -> lam_stmt.
  Proof. intros ON OD. exact (lam_proof (vctor_proof ON) (strctor_proof ON) (assign_proof ON OD) OD). Qed.

  (* [comment removed for export] *)
  Theorem fuzz_oneM_proof : opnew_stmt -> opdelete_stmt -> fuzz_oneU_stmt ProgP.fuzz_one.
  Proof.
    intros ON OD. pose proof (lam_closed ON OD) as LAM.
    unfold fuzz_oneU_stmt. intros.
    destruct (ps_fa s) as [p|] eqn:FA.
    - eapply (fuzz_later LAM OD); eassumption.
    - eapply (fuzz_first ON LAM OD); eassumption.
  Qed.
End CANSEC1.

(* [comment removed for export] *)
Theorem ubsan_client_proof : forall rc : runConstT, @opnew_stmt rc -> @opdelete_stmt rc -> @fuzz_oneU_stmt rc ProgP.fuzz_one.
Proof. intros rc ON OD. exact (@fuzz_oneM_proof rc ON OD). Qed.
