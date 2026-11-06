(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec ExitSim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import DivergeSim AgentLib AgentNodes Nodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance cfglift_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AnyCfg.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma node_ok_unit_silent_cfg : forall c c',
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  node_ok_cfg cfg segs c unit (fun _ => []) (fun _ => c').
Proof.
  intros [ms model] c' [Hcomp Hexact]. split; [|intros e st Hss; apply Hexact; eapply sstep_cfg_sub; exact Hss].
  intros []. pose proof (Hcomp tt) as Hs.
  apply sstep_cfg_of_sstep; [exact Hs|].
  intros x8 eff m' evs' Hsvc Hspec Hh' [Hoff [Hr (eff2 & m2 & evs2 & Hspec2 & Hr2)]].
  assert (Hh0 : m_halted model = None) by (inversion Hs; assumption).
  destruct (materialize_model_accesses m' (syscall_effect_accesses eff)) as [m''|] eqn:Hm.
  2:{ destruct (Hexact _ _ (sstep_syscall_materialization_fault segs ms model x8 eff m' evs' Hh0 Hsvc Hspec Hh' Hm)) as (u & _ & X). discriminate X. }
  destruct (Hexact _ _ (sstep_syscall segs ms model x8 eff m' m'' evs' Hh0 Hsvc Hspec Hh' Hm)) as (u1 & _ & X1).
  destruct (m_halted m2) as [code|] eqn:Hh2.
  - destruct (m_killed m2) as [sig|] eqn:Hk2.
    + destruct (Hexact _ _ (sstep_killed segs ms model x8 eff2 m2 evs2 sig Hh0 Hsvc Hspec2 Hk2)) as (u2 & X & _). destruct evs2; discriminate X.
    + destruct (Hexact _ _ (sstep_exit segs ms model x8 eff2 m2 evs2 code Hh0 Hsvc Hspec2 Hh2 Hk2)) as (u2 & X & _). destruct evs2; discriminate X.
  - destruct (materialize_model_accesses m2 (syscall_effect_accesses eff2)) as [m3|] eqn:Hm2.
    + destruct (Hexact _ _ (sstep_syscall segs ms model x8 eff2 m2 m3 evs2 Hh0 Hsvc Hspec2 Hh2 Hm2)) as (u2 & _ & X2).
      assert (Hms : advance_past_svc (apply_effect ms eff2) = advance_past_svc (apply_effect ms eff)) by (rewrite <- X1 in X2; congruence).
      rewrite (advance_apply_effect_ret _ _ _ Hms) in Hr2. congruence.
    + destruct (Hexact _ _ (sstep_syscall_materialization_fault segs ms model x8 eff2 m2 evs2 Hh0 Hsvc Hspec2 Hh2 Hm2)) as (u2 & _ & X). discriminate X.
Qed.

Lemma rz_silent1_unit_cfg : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  realizes_cfg cfg segs c' T -> realizes_cfg cfg segs c T.
Proof. intros c c' T Hn Hc. eapply rz_silent1_cfg; [apply node_ok_unit_silent_cfg; exact Hn | exact Hc]. Qed.

(* [comment removed for export] *)
Lemma stepacc_ecall_epend' : forall regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
  = MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

Lemma node_instr_noacc' : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  ShapeAlg.node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  split.
  - intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

(* [comment removed for export] *)
Lemma rz_sys_lazy_cfg : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes_cfg cfg segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes_cfg cfg segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply rz_silent1_unit_cfg; [| exact Hc].
  exact (node_instr_noacc' (mkst regs pc mem rom) model _ Hh eq_refl (stepacc_ecall_epend' regs pc mem rom w HF HE)).
Qed.

End AnyCfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CfgNodes.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
(* [comment removed for export] *)
Hypothesis ALLOC_OFF : family_may_fail cfg FamAlloc = false.

Lemma injected_arm_222 : injected_arm 222 = Some (mkInjectedArm 222 FamAlloc mmap_errnos).
Proof. reflexivity. Qed.

Lemma injected_family_off_mmap : forall i,
  bv_unsigned (in_sysno i) = 222 -> injected_family_off cfg i = true.
Proof. intros i H. unfold injected_family_off. rewrite H, injected_arm_222. cbn [ia_family negb]. rewrite ALLOC_OFF. reflexivity. Qed.

(* [comment removed for export] *)
Lemma refusal_b_mmap : forall i m r,
  bv_unsigned (in_sysno i) = 222 -> refusal_b i m r = errno_ret_in mmap_errnos r.
Proof. intros i m r H. unfold refusal_b. rewrite H, injected_arm_222. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_chk_grant_cfg : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event) (i0 : I),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  injected_family_off cfg (sys_input segs ms x8) = true ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     refusal_b (sys_input segs ms x8) model (eff_ret eff) = true -> m_halted m' = None) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok_cfg cfg segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs i0 Hh Hsvc Hoff Hok Hnr Hinv Href Hnu Hh' Hacc.
  assert (NSP : forall i, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model (effs i)).
  { intros i [_ [Hr _]]. rewrite Hnr in Hr. discriminate Hr. }
  assert (WIT : exists eff' m' evs', syscall_spec (sys_input segs ms x8) model (Ok eff' m' evs')
                                    /\ refusal_b (sys_input segs ms x8) model (eff_ret eff') = false).
  { exists (effs i0), (ms' i0), (evs i0). split; [apply check_syscall_ok_iff; apply Hok | apply Hnr]. }
  assert (LISTED : forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
            ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff ->
            exists i, eff = effs i /\ m' = ms' i /\ ev = evs i).
  { intros eff m' ev Hs Hns. apply check_syscall_ok_iff in Hs.
    destruct (refusal_b (sys_input segs ms x8) model (eff_ret eff)) eqn:Hr.
    - exfalso. apply Hns. split; [exact Hoff | split; [exact Hr | exact WIT]].
    - exact (Hinv eff m' ev Hs Hr). }
  assert (NOHALT : forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) -> m_halted m' = None).
  { intros eff m' ev Hs. apply check_syscall_ok_iff in Hs.
    destruct (refusal_b (sys_input segs ms x8) model (eff_ret eff)) eqn:Hr.
    - exact (Href eff m' ev Hs Hr).
    - destruct (Hinv eff m' ev Hs Hr) as (i & -> & -> & ->). apply Hh'. }
  split.
  - intros i. apply (sstep_cfg_syscall segs cfg ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc).
    + apply check_syscall_ok_iff. exact (Hok i).
    + exact (NSP i).
    + exact (Hh' i).
    + rewrite (Hacc i). apply materialize_model_accesses_nil.
  - intros e st Hss.
    inversion Hss; subst;
      match goal with
      | H : ms_svc_pending ms = None |- _ => rewrite Hsvc in H; discriminate H
      | H : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in H; injection H as <-
      end.
    all: first
      [ (* [comment removed for export] *)
        match goal with Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hc : m_halted ?m1 = Some _ |- _ =>
          exfalso; rewrite (NOHALT _ _ _ Hs) in Hc; discriminate Hc end
      | (* [comment removed for export] *)
        match goal with Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hk : m_killed ?m1 = Some _ |- _ =>
          exfalso; rewrite (m_killed_of_m_halted_none _ (NOHALT _ _ _ Hs)) in Hk; discriminate Hk end
      | (* [comment removed for export] *)
        match goal with Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hns : ~ spurious_refusal_cfg _ _ _ _ |- _ =>
          destruct (LISTED _ _ _ Hs Hns) as (i & E1 & E2 & E3) end; subst;
        match goal with Hm : materialize_model_accesses _ _ = _ |- _ =>
          rewrite (Hacc i), materialize_model_accesses_nil in Hm;
          first [ discriminate Hm | injection Hm as <-; exists i; split; reflexivity ] end
      | (* [comment removed for export] *)
        match goal with Hs : syscall_spec _ _ Unmodeled |- _ =>
          exfalso; apply (Hnu (mkEffect (Z_to_bv 64 0) [] [])); apply check_syscall_err_iff; exact Hs end ].
Qed.

End CfgNodes.
