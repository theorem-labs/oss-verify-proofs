(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Ub/RefPrintfFirst.v: rz_run_lf restated over BudgetWit.Rzb.rzb *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefNodes LibTail.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RefExitBase RefStdioDefs RefStdioWrite LibStdioCall RefPrintfBufBase LibDiagKn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RefPrintfFirst.
From OSSVerify.Proofs.boost_beast.http_request.lib.BudgetWit Require Import Rzb AgentNodesB NodesB LibWritevB RefNodesB SymDriveB.
Open Scope bv_scope.

Theorem rzb_run_lf : forall segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R model T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
     rzb segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  rzb segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
         Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply (Hcont R' _ HR'); [| reflexivity | exact Hlf].
  eapply carry_after; eassumption.
Qed.
