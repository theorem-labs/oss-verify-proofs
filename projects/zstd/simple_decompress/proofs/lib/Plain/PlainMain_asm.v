(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv Image.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg StdioFiles Startup Exit F_printf_iface Stdio_iface.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import F_fprintf F_fwritex_stderr F_stdio_flush F_fwrite F_vfprintf F_vfprintf_stdout F_fwritex_stdout F_stdio_exit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import RMalloc_iface RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import Harness_iface RDriver_iface RF_target_run RF_main PlainImpl.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import PState Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.simple_decompress.lib Require Import TopLevel.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import RunDraw.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma plain_target_run_closed : fuzz_one_stmt -> ptarget_run_stmt.
Proof.
  intros FUZZ.
  exact (ptarget_run_proof rmalloc_spec rfree_spec_proof FUZZ
           (emit_printf_proof PState ps_so set_so_ps) fwritex_stdout_proof).
Qed.

(* [comment removed for export] *)
Lemma plain_main_closed : fuzz_one_stmt -> pmain_stmt.
Proof.
  intros FUZZ.
  exact (plain_main_proof rmalloc_spec rfree_spec_proof (fprintf_diag_proof PState) fwritex_stderr_proof
           stdio_write_flush_proof fwrite_diag_proof towrite_proof (plain_target_run_closed FUZZ)).
Qed.
End CANSEC1.

(* [comment removed for export] *)
Theorem plain_impl : (forall rc : runConstT, @fuzz_one_stmt rc) ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs p_init_pc p_phdrs) en inp ->
    valid_input_either inp ->
    impl psegs (at_node psegs) (Prog.prog psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 psegs p_init_pc p_phdrs en inp).
Proof.
  intros FUZZ. exact (plain_impl_from_main stdio_exit_proof_ps (fun rc => @plain_main_closed rc (FUZZ rc))).
Qed.
