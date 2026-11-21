(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Common/AgentNodes.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import AgentLib.
Import ListNotations.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import AgentNodes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.BudgetWit Require Import Rzb.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope bv_scope.
Lemma rzb_sys : forall segs regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  Rzb.rzb segs (mkCfg (AgentNodes.epend regs pc mem rom (getr regs 17)) model) T ->
  Rzb.rzb segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply Rzb.rzb_step; [exact Hh | exact Hlazy | reflexivity | eapply AgentNodes.step_ecall_epend; eassumption | exact Hc].
Qed.
