(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from RefNodes.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (RomBase.sys_rob at the set_tid_address node, as RefNodes.v proves it). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Export AsanCeil.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes ModelAmb.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Import ListNotations.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefNodes.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.BudgetWit Require Import AgentNodesB NodesB Rzb.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require RomBase.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.
Open Scope bv_scope.
Section FPW_1.
Context {fx : PropExec.FPState}.
Section WithSegs.
Variable segs : list Segment.
#[using="Type"] Lemma check_syscall_96 : forall ms x8 eff m,
  bv_unsigned x8 = 96%Z ->
  check_syscall (sys_input segs ms x8) eff m = check_set_tid_address eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.
#[using="Type"] Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.
#[using="Type"] Lemma node_set_tid : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) RefNodes.tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Htid.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
     match eff with
     | mkEffectU ret [] [] [] [] [] =>
         if (0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z
         then CheckOk (with_tid ret model) [] else CheckReject
     | _ => CheckReject end).
  { intros eff. rewrite (check_syscall_96 ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
  pose (effs := fun i : RefNodes.tid_I => mkEffectU (proj1_sig i) [] [] [] [] []).
  assert (Enx : forall i : RefNodes.tid_I,
    mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
  { intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
  split.
  - intros i. rewrite Enx. apply (sstep_of_check segs ms model x8); [exact Hh | exact Hsvc | | rewrite RefNodes.with_tid_halted; exact Hh | rewrite RefNodes.with_tid_lazy; exact Hlazy].
    destruct i as [t [Ht1 Ht2]]. subst effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
  - assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
              exists i : RefNodes.tid_I, eff = effs i /\ m' = with_tid (proj1_sig i) model /\ ev = []).
    { intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z) eqn:Eb; [|discriminate].
      apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
      injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity. }
    intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans (RefNodes.with_tid_lazy _ model) Hlazy)) in Hmat.
      injection Hmat as <-. exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans (RefNodes.with_tid_lazy _ model) Hlazy)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite RefNodes.with_tid_halted in Hh2. congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z); discriminate.
Qed.
#[using="Type"] Lemma rzb_set_tid : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     Rzb.rzb segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  Rzb.rzb segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
  eapply AgentNodesB.rzb_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (Rzb.rzb_conseq segs _ (t_alt (fun _ : RefNodes.tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply NodesB.rzb_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid]
                   | (* set_tid_address (96) does not read the process's memory. *)
                     eapply (RomBase.sys_rob_memfree segs _ _ (getr regs 17));
                       [ reflexivity
                       | replace (bv_unsigned (getr regs 17)) with 96%Z
                           by (rewrite H17; rewrite u64_lit by lia; reflexivity);
                         exact RomBase.memfree_96 ]
                   | (* set_tid_address (96) is not an allocation call. *)
                     eapply (Rzb.grant_ok_num segs _ _ (getr regs 17) 96);
                       [reflexivity | rewrite H17; apply u64_lit; lia | reflexivity] |].
  intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.
#[using="Type"] Lemma rzb_exit_at : forall regs (pc : word) mem rom model w code,
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
End FPW_1.
Local Open Scope Z_scope.
