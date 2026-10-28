(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qn X0py X0qc X0qo X0q1 X0ns X0nt X0pz X0q0.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m4 X1k8 X1jk X1kq X1ke X1ju.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0qa.
Import ListNotations.
Open Scope Z_scope.

Lemma ras_pre2_intro {RCEIL : RunCeiling} : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> ras_pre2 st (set_tick t st) sc n FUEL.
Proof.
intros st LB t sc n AR MF TT SC N FIT. split; [| split; [| split; [| repeat split; lia]]].
- exists LB. split; [exact AR| apply ist_top; exact TT].
- apply ER_refl_tick.
- apply ALLC_tick; [| exact TT]. exact (mf_cell_ticks _ _ MF).
Qed.

Theorem ralloc_slot_spec {RCEIL : RunCeiling} : ralloc_slot_stmt ras_pre2 as_inv2.
Proof.
unfold ralloc_slot_stmt. intros fuel.
exact (ralloc_slot_ok ram_pre ralloc_meta_spec X0qa.ist_ampre_proof fuel).
Qed.
