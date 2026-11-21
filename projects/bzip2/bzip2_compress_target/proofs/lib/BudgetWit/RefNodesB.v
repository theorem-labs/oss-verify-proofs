(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from RefNodes.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
From Stdlib Require Lia.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.MiniExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SimInv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require StreamSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require FileSim ShapeAlg Nodes StoreOk AgentLib AgentNodes ModelAmb.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SimInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StreamSim.StreamExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim.AllocSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.FileSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.AgentNodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.
Import ListNotations.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common Require Import CfgStep AllocRefusal.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import RefNodes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.BudgetWit Require Import AgentNodesB Rzb.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope bv_scope.
Section ACeilS1.
Context {ACEIL__ : ACeil}.
Section WithSegs.
Variable segs : list Segment.
Lemma rzb_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  Rzb.rzb segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply AgentNodesB.rzb_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply Rzb.rzb_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.
End WithSegs.
End ACeilS1.
Local Open Scope Z_scope.
