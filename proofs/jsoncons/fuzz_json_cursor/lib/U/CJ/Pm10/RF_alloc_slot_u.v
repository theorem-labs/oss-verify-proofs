(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import MallocTree_u MallocFacts_A_u MallocHINV_u Malloc_fp_u MallocFacts_AS_u ASlot_I_u ASlot_M0_u MallocFacts_AM_u MallocFacts_AMP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Pm10 Require Import RMallocRep_u RMallocTree_u RMalloc_fp_u RAllocSlot_iface_u RASlot_I_u RF_am_P_u RF_alloc_meta_u RASlot_M6_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require MallocFacts_inv4_u.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Lemma ras_pre2_intro : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> ras_pre2 st (set_tick t st) sc n FUEL.
Proof.
  intros st LB t sc n AR MF TT SC N FIT. split; [| split; [| split; [| repeat split; lia]]].
  - exists LB. split; [exact AR| apply ist_top; exact TT].
  - apply ER_refl_tick.
  - apply ALLC_tick; [| exact TT]. exact (mf_cell_ticks _ _ MF).
Qed.

Theorem ralloc_slot_spec : ralloc_slot_stmt ras_pre2 as_inv2.
Proof.
  unfold ralloc_slot_stmt. intros fuel.
  exact (ralloc_slot_ok ram_pre ralloc_meta_spec MallocFacts_inv4_u.ist_ampre_proof fuel).
Qed.
End CEIL_WRAP_1.

