(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Info/AgentNodes.v: rz_sys restated over BudgetWit.Rzb.rzb *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import AgentLib.
Unset Nia Cache.  
Unset Lia Cache.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import AgentNodes.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.BudgetWit Require Import Rzb.

Section WithFP1. Context {FP : PropExec.FPState}.
Lemma rzb_sys : forall segs regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  rzb segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  rzb segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply rzb_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.
End WithFP1.
