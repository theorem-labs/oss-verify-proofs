(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Stdio_iface Printf_stdio_iface Printf_closed F_towrite F_fwrite F_fprintf F_vfprintf_stdout
  Fz_iface Driver_iface Drv_kit Drv_target Drv_main Impl.
From OssFuzzTheorems.Proofs.openssl.pem.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma rtarget_run_closed : forall C : cli_sig, rfuzz_init_stmt C -> rfuzz_one_stmt C -> rtarget_run_stmt C.
Proof.
  intros C INIT FUZZ.
  exact (rtarget_run_proof C rmalloc_spec rfree_spec_proof rfree_null_spec INIT FUZZ
           (emit_printf_proof PState ps_so set_so_ps) fwritex_stdout_ok
           RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof).
Qed.

(* [comment removed for export] *)
Lemma rmain_closed : forall C : cli_sig, cli0_at_main C -> rfuzz_init_stmt C -> rfuzz_one_stmt C -> rmain_stmt.
Proof.
  intros C CLI0AT INIT FUZZ.
  exact (main_proof C CLI0AT rmalloc_spec rfree_spec_proof (fprintf_diag_proof PState) fwritex_stderr_ok stdio_write_flush_ok
           (fwrite_diag_proof towrite_proof) (rtarget_run_closed C INIT FUZZ)).
Qed.
End WithCeiling0.

(* [comment removed for export] *)
Theorem impl_U_closed :
  (forall (CE__ : Ceiling) (RN__ : RunRnd), exists C : cli_sig, cli0_at_main C /\ rfuzz_init_stmt C /\ rfuzz_one_stmt C) ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp ->
    valid_input_w inp ->
    impl usegs (at_node usegs) (@prog (ceiling_of_sp (bv_unsigned (en_sp en))) usegs ustage (in_argv inp))
         (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 usegs Ubsan.M.init_pc Ubsan.M.phdrs en inp).
Proof.
  intros CLIENT. apply impl_U_from_main. intros CE__ RN__. destruct (CLIENT CE__ RN__) as (C & C0 & CI & CF). exact (@rmain_closed CE__ RN__ C C0 CI CF).
Qed.

