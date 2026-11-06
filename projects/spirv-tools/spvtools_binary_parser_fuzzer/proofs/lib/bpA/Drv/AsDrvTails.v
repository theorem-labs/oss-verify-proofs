(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HCatExec HCatSim HSeqExec HStoreOk HShapeAlg HNodes HAgentLib SpecConsts HFrame HStreamSim HFileSim HSymExec HSymExec2 HSymExec2Sound HSymRun HSymDrive HSymDriveX HLibKnowFrame HSymAux HHoare HRefPrintfLib HLibTail HSpec HShapeLaws LazyRestrict LazySR LazyFdNodes LazySym.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HRefExitBase HRefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib AsPrintfFirst AsSxKit AsExitDefs AsTailExit AsRefused.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Abbreviation RSEGS := Asan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Tails.
  Variables (L S Zr : list (word * word)).

  Theorem as_refused : forall regs mem msF mo (sp : word) (can tid TB : Z),
    rfH regs mem sp can -> exitA mem sp tid can TB ->
    getr regs 4 = Z_to_bv 64 0x6c3f18 ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0xe89f4) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    realizes RSEGS (mkCfg msF mo) (t_die msg_refused (m_fs mo)).
  Proof.
    intros regs mem msF mo sp can tid TB PH XA R4 OK RS Hfd2. unfold t_die.
    apply (as_refused_k L S Zr regs mem msF mo sp can); try assumption; [apply t_exit_has_nil|].
    intros regs' mem' msF' mo' PO OK' SB' HS' RS'.
    rewrite <- (same_but_materialized_fs _ _ SB').
    destruct PH as [R2 Rsp16 RspLo RspHi Rstk Rimg Rgot Rcells Rcan Rcan64 Rsh0].
    destruct PO as [Psp Pra Pa0 Pcs Pframe Pflags Prpos Prend Pwend Pwpos Pwbase Pbuf Pbsz Plock Pmode Plbf Pcan Pstk].
    apply (tail_exitA L S Zr regs' mem mem' msF' mo' sp RF_FR tid can TB XA); try assumption; try (unfold RF_FR; lia).
    - intros a n Ha Hn. apply Pstk; unfold RF_FR in *; lia.
    - unfold xk_stderr, cells_ok. repeat apply Forall_cons; try apply Forall_nil; unfold cell_ok; assumption.
    - rewrite (Pcs 4%bv); [exact R4 | cbn; tauto].
  Qed.
End Tails.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
