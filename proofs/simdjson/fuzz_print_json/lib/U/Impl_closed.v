(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Stdio_iface Printf_stdio_iface Printf_closed F_towrite F_fwrite F_fprintf F_vfprintf_stdout Sj_iface Driver_iface Drv_kit Drv_target Drv_main Impl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
From OssFuzzTheorems.simdjson.fuzz_print_json.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma rtarget_run_closed : rfuzz_one_stmt -> rtarget_run_stmt.
Proof.
  intros FUZZ.
  exact (rtarget_run_proof rmalloc_spec rfree_spec_proof rfree_null_spec FUZZ
           (emit_printf_proof PState ps_so set_so_ps) fwritex_stdout_ok
           RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof).
Qed.

Lemma rmain_closed : rfuzz_one_stmt -> rmain_stmt.
Proof.
  intros FUZZ.
  exact (main_proof rmalloc_spec rfree_spec_proof (fprintf_diag_proof PState) fwritex_stderr_ok stdio_write_flush_ok
           (fwrite_diag_proof towrite_proof) (rtarget_run_closed FUZZ)).
Qed.
End WithCeiling0.

Theorem impl_U_closed : (forall (CE__ : Ceiling) (RN__ : RunRnd), @rfuzz_one_stmt CE__ RN__) ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp ->
    valid_input_either inp ->
    impl usegs (at_node usegs) (@prog (ceiling_of_sp (bv_unsigned (en_sp en))) usegs ustage (in_argv inp))
         (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 usegs Ubsan.M.init_pc Ubsan.M.phdrs en inp).
Proof. intros FUZZ. exact (impl_U_from_main (fun CE__ RN__ => @rmain_closed CE__ RN__ (FUZZ CE__ RN__))). Qed.

