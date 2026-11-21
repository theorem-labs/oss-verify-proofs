(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail Spec ShapeLaws
  LazyRestrict LazySR LazyFdNodes LazySym.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib
  AsPrintfFirst AsSxKit AsExitCas AsExitDefs AsExit AsTailExit AsRefused.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RSEGS := Asan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Tails.
  Variables (L S Zr : list (word * word)).
Scheme kc__1 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.AsRefused.rfH Sort Prop.
Scheme kc__2 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.AsRefused.rfPost Sort Prop.

  (* [comment removed for export] *)
  Theorem as_refused : forall regs mem msF mo (sp : word) (can tid : Z) (ro wpw : word),
    rfH regs mem sp can -> exitH mem sp tid ro wpw ->
    getr regs 4 = Z_to_bv 64 0x65d4b0 ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0x0a2f18) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    (* LPS 75d69e00: the reader premise, after fd_lookup, passed to as_refused_k. *)
    m_channel_reader mo = true ->
    realizes RSEGS (mkCfg msF mo) (t_die msg_refused (m_fs mo)).
  Proof.
    (* LPS 75d69e00: the recorded proof applied as_refused_k one argument short of the reader
       premise; written out.  Text from boost-json/fuzz_parse As/AsDrvTails.v
       (an earlier repair's copy), whose proof names no address: the getr regs 4 fact and the entry
       come from this file's own statement (R4, RS). *)
    intros regs mem msF mo sp can tid ro wpw PH XH R4 OK RS Hfd2 Hrd2. unfold t_die.
    apply (as_refused_k L S Zr regs mem msF mo sp can); try assumption; [apply t_exit_has_nil|].
    intros regs' mem' msF' mo' PO OK' SB' HS' RS'.
    rewrite <- (same_but_materialized_fs _ _ SB').
    destruct PH as [R2 Rsp16 RspLo RspHi Rstk Rimg Rgot Rcells Rcan Rcan64 Rsh0].
    destruct PO as [Psp Pra Pa0 Pcs Pframe Pflags Prpos Prend Pwend Pwpos Pwbase Pbuf Pbsz Plock Pcan Pstk].
    apply (tail_exit2 L S Zr regs' mem mem' msF' mo' sp RF_FR tid can ro wpw (Z_to_bv 64 0) (Z_to_bv 64 0));
      try assumption; try (unfold RF_FR; lia).
    - intros a n Ha Hn. apply Pstk; unfold RF_FR in *; lia.
    - rewrite (Pcs 4%bv); [exact R4 | cbn; tauto].
  Qed.
End Tails.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
