(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from RefNodes.v: the set_tid_address (96) and exit nodes restated over BudgetWit.Rzb.rzb, with the no-allocation check at the set_tid_address node *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg Amb RelSpec
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes Gap04.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import RefNodes.
From OSSVerify.Proofs.boost_beast.http_request.lib.BudgetWit Require Import Rzb AgentNodesB NodesB.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.
Lemma rzb_set_tid : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     rzb segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  rzb segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
  eapply rzb_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (rzb_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply rzb_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid]
                   | rob_mf H17
                   | apply nonalloc_no with (x8 := getr regs 17); [reflexivity | rewrite H17; vm_compute; reflexivity] |].
  intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.
Lemma rzb_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  rzb segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rzb_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rzb_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.
End WithSegs.
