(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Common/CliDriver/AgentNodesG.v: rz_sys and rz_exit_at restated over the budget carrier rzb. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import AgentLib.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require Import AgentNodesG.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.BudgetWit Require Import Rzb.

Section G.
Context {fx : FPState}.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma rzb_exit_at : forall segs regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  rzb segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros segs regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rzb_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rzb_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

End G.
