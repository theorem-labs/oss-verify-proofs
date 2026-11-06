(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Monad Stdio Driver Prog LibProg ProgG ProgGDet.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocP Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Stdio_iface Printf_stdio_iface Printf_closed F_towrite F_fwrite F_fprintf F_vfprintf_stdout
  Lib_iface Exit Exit_defs Exit_walk F_stdio_exit Driver_iface Drv_kit Drv_target Drv_main Impl.
From OSSVerify.Proofs.openssl.bndiv.lib Require Import TopLevel Obligations ProofBaseG.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
From OSSVerify.openssl.bndiv.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} {LL : LibLaws}.

(* [comment removed for export] *)
Lemma rtarget_run_closed : rinit_stmt -> rfuzz_one_stmt -> rtarget_run_stmt.
Proof.
  intros INIT FUZZ.
  exact (rtarget_run_proof rmalloc_spec rfree_spec_proof rfree_null_spec INIT FUZZ
           (emit_printf_proof PState ps_so set_so_ps) fwritex_stdout_ok
           RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof).
Qed.

(* [comment removed for export] *)
Lemma rmain_closed : rinit_stmt -> rfuzz_one_stmt -> rmain_stmt.
Proof.
  intros INIT FUZZ.
  exact (main_proof rmalloc_spec rfree_spec_proof (fprintf_diag_proof PState) fwritex_stderr_ok stdio_write_flush_ok
           (fwrite_diag_proof towrite_proof) (rtarget_run_closed INIT FUZZ)).
Qed.
End WithCeiling0.

(* [comment removed for export] *)
Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem exit_from_at_exit_proof : exit_from_at_exit_stmt.
Proof.
  exact (exit_from_at_exit_core (stdio_exit_proof ps_so set_so_ps ps_get_set ps_set_set ps_set_get)).
Qed.
End WithCeiling1.

(* [comment removed for export] *)
Theorem implG_P_closed : forall (LM : LibModel)
    (LSP : forall (CE__ : Ceiling) (RN__ : RunRnd), @LibSpec LM)
    (LL : forall (CE__ : Ceiling) (RN__ : RunRnd), @LibLaws LM (LSP CE__ RN__)),
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @rinit_stmt CE__ RN__ LM (LSP CE__ RN__)) ->
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @rfuzz_one_stmt CE__ RN__ LM (LSP CE__ RN__)) ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp ->
    valid_input_either inp ->
    impl psegs (at_node psegs) (@progG (ceiling_of_sp (bv_unsigned (en_sp en))) LM psegs pstage (in_argv inp))
         (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 psegs Plain.M.init_pc Plain.M.phdrs en inp).
Proof.
  intros LM LSP LL INIT FUZZ.
  exact (impl_P_from_main (fun CE__ RN__ => @exit_from_at_exit_proof CE__ RN__)
           (fun CE__ RN__ => @rmain_closed CE__ RN__ LM (LSP CE__ RN__) (LL CE__ RN__) (INIT CE__ RN__) (FUZZ CE__ RN__))).
Qed.

(* [comment removed for export] *)
Theorem implG_P_stmt_closed : forall (LM : LibModel)
    (LSP : forall (CE__ : Ceiling) (RN__ : RunRnd), @LibSpec LM)
    (LL : forall (CE__ : Ceiling) (RN__ : RunRnd), @LibLaws LM (LSP CE__ RN__)),
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @rinit_stmt CE__ RN__ LM (LSP CE__ RN__)) ->
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @rfuzz_one_stmt CE__ RN__ LM (LSP CE__ RN__)) ->
  @implG_stmt LM psegs Plain.M.init_pc Plain.M.phdrs pstage.
Proof.
  intros LM LSP LL INIT FUZZ en inp VE VI. exact (implG_P_closed LM LSP LL INIT FUZZ en inp VE VI).
Qed.

(* [comment removed for export] *)
