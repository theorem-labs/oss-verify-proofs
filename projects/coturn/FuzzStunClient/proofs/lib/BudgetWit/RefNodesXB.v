(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from RefNodesX.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: node 96's read-only-backing side goal is discharged by RefNodesX.rob_mf. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import CheckLite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes AsanCeil RefNodes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Import ListNotations.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefNodesX.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.BudgetWit Require Import Common_AgentNodesB Common_NodesB Rzb.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.
Section WithSegsMM.
Variable segs : list Segment.
Lemma rzb_set_tid : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     Rzb.rzb segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  Rzb.rzb segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hc.
  eapply Common_AgentNodesB.rzb_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  assert (Hno : bv_unsigned (getr regs 17) = 96%Z) by (rewrite H17; apply u64_lit; lia).
  set (t1 := exist (fun t : word => (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z) (Z_to_bv 64 1) one_tid_ok : tid_I).
  apply (Rzb.rzb_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists t1; exact Ht]].
  apply (Common_NodesB.rzb_cases segs _ tid_I
           (fun i => mkCfg (advance_past_svc (set_gpr0 (epend regs pc mem rom (getr regs 17)) (proj1_sig i)))
                           (with_tid (proj1_sig i) model)) (fun _ => K) t1).
  - apply (node_set_tid segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17) Hh Hlazy eq_refl Hno Htid).
  - (* 96 does not read [in_mem]: [RefNodesX.rob_mf], as [RefNodesX.rz_set_tid] discharges it *)
    rob_mf H17.
  - exact (Rzb.budget_ok_num segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17) 96 eq_refl Hno eq_refl).
  - intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hc. exact Ht.
Qed.
End WithSegsMM.
