(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BRelSpec BSimInv BExitSim BCatSim BFileSim BShapeAlg.

Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.

Lemma sstep_cfg_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs the_scfg (mkCfg ms model) e st ->
  (exists eff model' evs,
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
      /\ ((exists model'', m_halted model' = None /\ e = evs
             /\ ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (m_halted model' = None /\ e = []
              /\ ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code /\ m_killed model' = None
              /\ e = evs ++ [ExitEv code (m_fs model')]
              /\ st = SNext (mkCfg ms model'))
          \/ (exists sig, m_killed model' = Some sig
              /\ e = evs ++ [KillEv sig (m_fs model')]
              /\ st = SNext (mkCfg ms model'))))
  \/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    left. eexists. repeat split; eauto.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. left. repeat split; auto.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. right. left. eexists. repeat split; eauto.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. right. right. eexists. repeat split; eauto.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. repeat split; auto.
Qed.

Lemma not_spurious_det : forall ms model x8 eff0 m0 evs0,
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 evs0) ->
  ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff0.
Proof.
  intros ms model x8 eff0 m0 evs0 Hchk (_ & Hr & (eff' & m' & evs' & Hspec & Hnr)).
  apply Hchk in Hspec. apply Ok_inj in Hspec as (-> & -> & ->).
  rewrite Hr in Hnr. discriminate Hnr.
Qed.

Definition open_I (model : Model) : Type := {e : Z | In e openat_errnos} + unit.

Definition open_nx (ms : machine_state) (model : Model) (mk : word -> Model)
  (i : open_I model) : config :=
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr _ => mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                   (mk (alloc_fd (m_fds model)))
  end.

End WithSegs.
