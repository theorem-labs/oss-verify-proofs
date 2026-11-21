(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Sys/AgentNodes.v's rz_sys, over BudgetWit.Rzb.realizes; the proof is unchanged. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim ShapeX StoreOk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import AgentLib.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import AgentNodes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BudgetWit Require Import Rzb.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Lemma rz_sys : forall segs regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply rz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.
