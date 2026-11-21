(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.MState.PropExec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.MState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Mem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Cells OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Exec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Frame OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.RegsEquiv OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Image.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Monad Stdio Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Stdio_iface Printf_stdio_iface Printf_closed.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwrite F_fprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Zlib_iface Driver_iface Drv_kit Drv_target Drv_main Impl Zh_closed F_calloc.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_closed OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.F_towrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fprintf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fprintf.F_vfprintf_stdout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Drv_target OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Drv_main OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Impl OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_closed OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_calloc.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RCalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit Require Import TopLevel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
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

Theorem impl_P_closed : (forall (CE__ : Ceiling) (RN__ : RunRnd), @rfuzz_one_stmt CE__ RN__) ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs Src_zlib_example_small_fuzzer_repro.M.init_pc Src_zlib_example_small_fuzzer_repro.M.phdrs) en inp ->
    valid_input inp ->
    impl psegs (at_node psegs) (@prog (ceiling_of_sp (bv_unsigned (en_sp en))) psegs pstage (in_argv inp))
         (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 psegs Src_zlib_example_small_fuzzer_repro.M.init_pc Src_zlib_example_small_fuzzer_repro.M.phdrs en inp).
Proof. intros FUZZ. exact (impl_P_from_main (fun CE__ RN__ => @rmain_closed CE__ RN__ (FUZZ CE__ RN__))). Qed.

Theorem impl_P_of_zlib : forall R : Ceiling -> zreps,
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @zlib_ok CE__ RN__ (R CE__)) ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs Src_zlib_example_small_fuzzer_repro.M.init_pc Src_zlib_example_small_fuzzer_repro.M.phdrs) en inp ->
    valid_input inp ->
    impl psegs (at_node psegs) (@prog (ceiling_of_sp (bv_unsigned (en_sp en))) psegs pstage (in_argv inp))
         (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 psegs Src_zlib_example_small_fuzzer_repro.M.init_pc Src_zlib_example_small_fuzzer_repro.M.phdrs en inp).
Proof.
  intros R ZOK. exact (impl_P_closed (fun CE__ RN__ => @rfuzz_one_of_zlib CE__ RN__ (R CE__) (ZOK CE__ RN__) (@rcalloc_proof CE__ RN__))).
Qed.
