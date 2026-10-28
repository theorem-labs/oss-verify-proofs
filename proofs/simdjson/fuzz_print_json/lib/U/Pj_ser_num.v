(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Sj_iface Sj_kit Pj_defs Pj_ser_defs Pj_ser_true Pj_ser_atom Pj_ser_i64 Pj_ser_dbl.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
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
