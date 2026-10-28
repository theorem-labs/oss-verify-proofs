(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv Image.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX StdioFiles Startup Exit F_printf_iface Stdio_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_fprintf F_fwritex_stderr F_stdio_flush F_fwrite F_vfprintf F_vfprintf_stdout F_fwritex_stdout F_stdio_exit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMalloc_iface RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import Harness_iface RDriver_iface RF_target_run RF_main PlainImpl.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import PState Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib Require Import TopLevel.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma plain_target_run_closed : fuzz_one_stmt -> ptarget_run_stmt.
Proof.
intros FUZZ.
exact (ptarget_run_proof rmalloc_spec rfree_spec_proof FUZZ
(emit_printf_proof PState ps_so set_so_ps) fwritex_stdout_proof).
Qed.
#[using="Type"] Lemma plain_main_closed : fuzz_one_stmt -> pmain_stmt.
Proof.
intros FUZZ.
exact (plain_main_proof rmalloc_spec rfree_spec_proof (fprintf_diag_proof PState) fwritex_stderr_proof
stdio_write_flush_proof fwrite_diag_proof towrite_proof (plain_target_run_closed FUZZ)).
Qed.
End CANSEC1.
Theorem plain_impl : (forall rc : runConstT, @fuzz_one_stmt rc) ->
forall (en : ExecEntry) (inp : ProcInput),
valid_entry (mkImage usegs u_init_pc u_phdrs) en inp ->
valid_input_either inp ->
impl usegs (at_node usegs) (Prog.prog usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
(ms0 usegs u_init_pc u_phdrs en inp).
Proof.
intros FUZZ. exact (plain_impl_from_main stdio_exit_proof_ps (fun rc => @plain_main_closed rc (FUZZ rc))).
Qed.
