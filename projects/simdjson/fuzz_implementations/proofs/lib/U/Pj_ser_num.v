(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Sj_iface Sj_kit Pj_defs Pj_ser_defs Pj_ser_true Pj_ser_atom Pj_ser_i64 Pj_ser_dbl.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem num_arms : rmalloc_stmt -> rfree_stmt -> i64_stmt /\ u64_stmt /\ dbl_stmt /\ null_stmt /\ false_stmt.
Proof.
  intros HM HF.
  split; [exact (i64_proof HM HF)|]. split; [exact (u64_proof HM HF)|]. split; [exact (dbl_closed HM HF)|].
  split; [exact (null_proof HM HF)| exact (false_proof HM HF)].
Qed.

Theorem atom_true : rmalloc_stmt -> rfree_stmt -> true_stmt.
Proof. intros HM HF. exact (true_proof HM HF). Qed.

End WithCeiling0.
