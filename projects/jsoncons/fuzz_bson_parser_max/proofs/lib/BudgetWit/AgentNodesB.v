(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from AgentNodes.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes StoreOk.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AgentLib.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AgentNodes.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.BudgetWit Require Import SpinAlgB.

Open Scope bv_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Section FPX_1.
Context {fx : PropExec.FPState}.
Context {bmK : BMode}.
Lemma rz_sys_b : forall segs scfg regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  SpinAlgB.rzb segs scfg (mkCfg (AgentNodes.epend regs pc mem rom (getr regs 17)) model) T ->
  SpinAlgB.rzb segs scfg (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros segs scfg regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply SpinAlgB.rzb_step; [exact Hh | exact Hlazy | reflexivity | eapply AgentNodes.step_ecall_epend; eassumption | exact Hc].
Qed.
End FPX_1.
