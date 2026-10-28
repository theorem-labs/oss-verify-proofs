(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail Spec ShapeLaws
  LazyRestrict LazySR LazyFdNodes LazySym.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib
  AsPrintfFirst AsSxKit AsExitCas AsExitDefs AsExit AsTailExit AsRefused.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Tails.
  Variables (L S Zr : list (word * word)).

  (* [comment removed for export] *)
  Theorem as_refused : forall regs mem msF mo (sp : word) (can tid : Z) (ro wpw : word),
    rfH regs mem sp can -> exitH mem sp tid ro wpw ->
    getr regs 4 = Z_to_bv 64 0xbe1c90 ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0x1eef6c) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    realizes RSEGS (mkCfg msF mo) (t_die msg_refused (m_fs mo)).
  Proof.
    intros regs mem msF mo sp can tid ro wpw PH XH R4 OK RS Hfd2. unfold t_die.
    apply (as_refused_k L S Zr regs mem msF mo sp can); try assumption; [apply t_exit_has_nil|].
    intros regs' mem' msF' mo' PO OK' SB' HS' RS'.
    rewrite <- (same_but_materialized_fs _ _ SB').
    destruct PH as [R2 Rsp16 RspLo RspHi Rstk Rimg Rgot Rcells Rcan Rcan64 Rsh0].
    destruct PO as [Psp Pra Pa0 Pcs Pframe Pflags Prpos Prend Pwend Pwpos Pwbase Pbuf Pbsz Plock Pcan Pstk].
    apply (tail_exit2 L S Zr regs' mem mem' msF' mo' sp RF_FR tid can ro wpw (Z_to_bv 64 0) (Z_to_bv 64 0));
      try assumption; try (unfold RF_FR; lia).
    - (* [comment removed for export] *) intros a n Ha Hn. apply Pstk; unfold RF_FR in *; lia.
    - rewrite (Pcs 4%bv); [exact R4 | cbn; tauto].
  Qed.
End Tails.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
