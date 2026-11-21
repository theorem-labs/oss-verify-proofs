(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv Image.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import PImg StdioFiles Startup Exit F_printf_iface Stdio_iface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import F_fprintf F_fwritex_stderr F_stdio_flush F_fwrite F_vfprintf F_vfprintf_stdout F_fwritex_stdout F_stdio_exit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import RMalloc_iface RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import Harness_iface RDriver_iface RF_target_run RF_main PlainImpl.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import PState Monad Stdio Driver Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import CMonad CMonadX ProgC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require AdapterC DriverC HarnessC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require ExFlushIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import TopLevel.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {rl : runLaunchT}.
Variable FM : ExFlushIface.flush_model.
Lemma plain_target_run_closed : fuzz_one_stmt FM -> ptarget_run_stmt FM.
Proof.
  intros FUZZ.
  exact (ptarget_run_proof FM rmalloc_spec rfree_spec_proof FUZZ
           (emit_printf_proof PState ps_so set_so_ps) fwritex_stdout_proof).
Qed.

Lemma plain_main_closed : fuzz_one_stmt FM -> pmain_stmt FM.
Proof.
  intros FUZZ.
  exact (plain_main_proof FM rmalloc_spec rfree_spec_proof (fprintf_diag_proof PState) fwritex_stderr_proof
           stdio_write_flush_proof fwrite_diag_proof towrite_proof (plain_target_run_closed FUZZ)).
Qed.
End CANSEC1.

Theorem plain_impl : forall FM : ExFlushIface.flush_model, (forall rc : runConstT, @fuzz_one_stmt rc FM) ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs p_init_pc p_phdrs) en inp ->
    valid_input_either inp ->
    implC psegs (at_node psegs) (progC_tree FM psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
          (ms0 psegs p_init_pc p_phdrs en inp).
Proof.
  intros FM FUZZ. exact (plain_impl_from_main FM stdio_exit_proof_ps (fun rc rl => @plain_main_closed rc rl FM (FUZZ rc))).
Qed.
