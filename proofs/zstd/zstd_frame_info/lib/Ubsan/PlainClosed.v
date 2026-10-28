(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv Image.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg Harness_iface RF_fi_final PlainMain_asm.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import PState Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Lemma plain_fuzz_closed : fuzz_one_stmt.
Proof. exact fuzz_one_final. Qed.
End CANSEC1.

(* [comment removed for export] *)
Theorem plain_impl_closed : forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage usegs u_init_pc u_phdrs) en inp ->
    valid_input_either inp ->
    impl usegs (at_node usegs) (Prog.prog usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 usegs u_init_pc u_phdrs en inp).
Proof. exact (plain_impl (fun rc => @plain_fuzz_closed rc)). Qed.
