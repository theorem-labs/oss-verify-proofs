(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Monad Stdio Driver Prog LibProg ProgG ProgGDet.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Stdio_iface Printf_stdio_iface Printf_closed F_towrite F_fwrite F_fprintf F_vfprintf_stdout Lib_iface Exit Exit_defs Exit_walk F_stdio_exit Driver_iface Drv_kit Drv_target Drv_main Impl.
From OssFuzzTheorems.Proofs.openssl.bignum.lib Require Import TopLevel Obligations ProofBaseG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} {LL : LibLaws}.

Lemma rtarget_run_closed : rinit_stmt -> rfuzz_one_stmt -> rtarget_run_stmt.
Proof.
  intros INIT FUZZ.
  exact (rtarget_run_proof rmalloc_spec rfree_spec_proof rfree_null_spec INIT FUZZ
           (emit_printf_proof PState ps_so set_so_ps) fwritex_stdout_ok
           RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof).
Qed.

Lemma rmain_closed : rinit_stmt -> rfuzz_one_stmt -> rmain_stmt.
Proof.
  intros INIT FUZZ.
  exact (main_proof rmalloc_spec rfree_spec_proof (fprintf_diag_proof PState) fwritex_stderr_ok stdio_write_flush_ok
           (fwrite_diag_proof towrite_proof) (rtarget_run_closed INIT FUZZ)).
Qed.
End WithCeiling0.

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem exit_from_at_exit_proof : exit_from_at_exit_stmt.
Proof.
  exact (exit_from_at_exit_core (stdio_exit_proof ps_so set_so_ps ps_get_set ps_set_set ps_set_get)).
Qed.
End WithCeiling1.

Theorem implG_U_closed : forall (LM : LibModel)
    (LSP : forall (CE__ : Ceiling) (RN__ : RunRnd), @LibSpec LM)
    (LL : forall (CE__ : Ceiling) (RN__ : RunRnd), @LibLaws LM (LSP CE__ RN__)),
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @rinit_stmt CE__ RN__ LM (LSP CE__ RN__)) ->
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @rfuzz_one_stmt CE__ RN__ LM (LSP CE__ RN__)) ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage bgusegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp ->
    valid_input_either inp ->
    impl bgusegs (at_node bgusegs) (@progG (ceiling_of_sp (bv_unsigned (en_sp en))) LM bgusegs bgustage (in_argv inp))
         (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 bgusegs Ubsan.M.init_pc Ubsan.M.phdrs en inp).
Proof.
  intros LM LSP LL INIT FUZZ.
  exact (impl_U_from_main (fun CE__ RN__ => @exit_from_at_exit_proof CE__ RN__)
           (fun CE__ RN__ => @rmain_closed CE__ RN__ LM (LSP CE__ RN__) (LL CE__ RN__) (INIT CE__ RN__) (FUZZ CE__ RN__))).
Qed.

Theorem implG_U_stmt_closed : forall (LM : LibModel)
    (LSP : forall (CE__ : Ceiling) (RN__ : RunRnd), @LibSpec LM)
    (LL : forall (CE__ : Ceiling) (RN__ : RunRnd), @LibLaws LM (LSP CE__ RN__)),
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @rinit_stmt CE__ RN__ LM (LSP CE__ RN__)) ->
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @rfuzz_one_stmt CE__ RN__ LM (LSP CE__ RN__)) ->
  @implG_stmt LM bgusegs Ubsan.M.init_pc Ubsan.M.phdrs bgustage.
Proof.
  intros LM LSP LL INIT FUZZ en inp VE VI. exact (implG_U_closed LM LSP LL INIT FUZZ en inp VE VI).
Qed.

