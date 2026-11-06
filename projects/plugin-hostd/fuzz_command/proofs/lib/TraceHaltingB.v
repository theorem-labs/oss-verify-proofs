From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit Equivalence HaltsAllowed.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK15.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import TraceHalting.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable.R Require Import Cfg.
Import ListNotations.

Lemma not_budget_refused_step : forall segs cfg c evs c',
  ~ reaches_budget_refused_cfg segs cfg c ->
  sstep_cfg segs cfg c evs (SNext c') ->
  ~ reaches_budget_refused_cfg segs cfg c'.
Proof.
  intros segs cfg c evs c' NR Hs (tr & c'' & Hstar & Hb).
  apply NR. exists (evs ++ tr), c''.
  split; [eapply star_cfg_step; [exact Hs | exact Hstar] | exact Hb].
Qed.

Lemma forced_step_acfg : forall segs c evs st,
  sstep_cfg segs forced_only_cfg c evs st -> sstep_cfg segs ACFG c evs st.
Proof.
  intros segs c evs st Hs.
  exact (sstep_cfg_mono segs forced_only_cfg ACFG c evs st (forced_only_cfg_least ACFG) Hs).
Qed.

Lemma forced_progress : forall segs c evs st,
  sstep_cfg segs ACFG c evs st -> exists evs' st', sstep_cfg segs forced_only_cfg c evs' st'.
Proof.
  intros segs [ms model] evs st Hs.
  apply (sstep_cfg_progress segs forced_only_cfg ms model evs st).
  - intros x8 _. apply refusal_decided_classical.
  - exact (sstep_cfg_sub segs ACFG _ evs st Hs).
Qed.

Lemma permitted_halt_next : forall allowed segs c evs c',
  sstep_cfg segs ACFG c evs (SNext c') ->
  Forall (permitted_event allowed) evs ->
  permitted_halt allowed c'.
Proof.
  intros allowed segs c evs c' Hstep HE.
  destruct (sstep_cfg_next_halts_by_exit segs ACFG c evs c' Hstep)
    as [Hnone | [(es0 & code & E & Hh & Hk) | (es0 & sig & E & Hk)]].
  - unfold permitted_halt. rewrite Hnone. constructor.
  - unfold permitted_halt. rewrite Hh. split; [|exact Hk].
    apply (proj1 (Forall_forall _ _) HE (ExitEv code (m_fs (cfg_model c')))).
    rewrite E. apply in_or_app. right. simpl. auto.
  - exfalso.
    apply (proj1 (Forall_forall _ _) HE (KillEv sig (m_fs (cfg_model c')))).
    rewrite E. apply in_or_app. right. simpl. auto.
Qed.

Theorem realizes_must_exit_forced_cut : forall segs c T,
  realizes segs c T -> forall allowed,
  permitted_halt allowed c -> permitted_traces allowed T ->
  ~ reaches_budget_refused_cfg segs forced_only_cfg c ->
  must_exit_in_at_cfg forced_only_cfg segs allowed c.
Proof.
  intros segs c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hhalt | c T T' H IH Heq
                 | c I nx T i0 Hnode Hcont IH | c T Hb];
    intros allowed HH HT NR.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact (sstep_cfg_not_halted _ _ _ _ _ (Hcomp i0)).
    + exact (forced_progress segs c (evs i0) (SNext (nx i0)) (Hcomp i0)).
    + intros es Herror.
      destruct (Hsound es SError (forced_step_acfg _ _ _ _ Herror)) as [i [_ E]]. discriminate E.
    + intros es c' Hstep.
      pose proof (forced_step_acfg _ _ _ _ Hstep) as HstepA.
      destruct (Hsound es (SNext c') HstepA) as [i [Ees Enext]].
      inversion Enext; subst c'. subst es.
      assert (HE : Forall (permitted_event allowed) (evs i)).
      { apply HT. exists i. left. apply is_prefix_refl. }
      apply (IH i allowed).
      * exact (permitted_halt_next allowed segs c (evs i) (nx i) HstepA HE).
      * intros tr Htr.
        assert (HF : Forall (permitted_event allowed) (evs i ++ tr)).
        { apply HT. exists i. right. exists tr. split; [reflexivity | exact Htr]. }
        apply Forall_app in HF. exact (proj2 HF).
      * exact (not_budget_refused_step _ _ _ _ _ NR Hstep).
  - unfold permitted_halt in HH.
    destruct (m_halted (cfg_model c)) as [code|] eqn:Hh; [|contradiction].
    destruct HH as [Hin Hk].
    eapply must_exit_in_at_cfg_halted; eassumption.
  - apply (IH allowed); [exact HH | | exact NR].
    intros tr Htr. apply HT. apply Heq. exact Htr.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact (sstep_cfg_not_halted _ _ _ _ _ (Hcomp i0)).
    + exact (forced_progress segs c [] (SNext (nx i0)) (Hcomp i0)).
    + intros es Herror.
      destruct (Hsound es SError (forced_step_acfg _ _ _ _ Herror)) as [i [_ E]]. discriminate E.
    + intros es c' Hstep.
      pose proof (forced_step_acfg _ _ _ _ Hstep) as HstepA.
      destruct (Hsound es (SNext c') HstepA) as [i [Ees Enext]].
      inversion Enext; subst c'. subst es.
      apply (IH i allowed).
      * exact (permitted_halt_next allowed segs c [] (nx i) HstepA (Forall_nil _)).
      * intros tr Htr. apply HT. exists i. exact Htr.
      * exact (not_budget_refused_step _ _ _ _ _ NR Hstep).
  - exfalso. apply NR. exists [], c. split; [apply star_cfg_refl | exact Hb].
Qed.

Theorem realizes_must_exit_forced_budget : forall segs c0 T allowed,
  realizes segs c0 T ->
  permitted_traces allowed T ->
  m_halted (cfg_model c0) = None ->
  ~ reaches_budget_refused_cfg segs forced_only_cfg c0 ->
  must_exit_in_at_cfg forced_only_cfg segs allowed c0.
Proof.
  intros segs c0 T allowed HR HT Hh NR.
  apply (realizes_must_exit_forced_cut segs c0 T HR allowed); [| exact HT | exact NR].
  unfold permitted_halt. rewrite Hh. exact I.
Qed.

Corollary halts_budgets_of_realizes : forall (lim : Z) (allowed : list word) segs pc ph,
  (forall sp brk0 mbase rnd inp,
    valid_entry (mkImage segs pc ph) (mkEntry sp brk0 mbase rnd) inp ->
    valid_input inp ->
    exists T, realizes segs (init_config segs pc ph sp brk0 mbase rnd lim inp) T
              /\ permitted_traces allowed T) ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim allowed (mkImage segs pc ph).
Proof.
  intros lim allowed segs pc ph HR. unfold halts_allowed_T_scfg_budgets.
  intros [sp brk0 mbase rnd] inp Hen Hinp Hbud.
  destruct (HR sp brk0 mbase rnd inp Hen Hinp) as (T & HRz & HT).
  change (must_exit_in_at_cfg forced_only_cfg segs allowed
    (init_config segs pc ph sp brk0 mbase rnd lim inp)).
  apply (realizes_must_exit_forced_budget segs _ T allowed HRz HT).
  - reflexivity.
  - exact Hbud.
Qed.

Corollary halts_within_budget_of_realizes : forall (lim : Z) (allowed : list word) segs pc ph,
  (forall sp brk0 mbase rnd inp,
    valid_entry (mkImage segs pc ph) (mkEntry sp brk0 mbase rnd) inp ->
    valid_input inp ->
    exists T, realizes segs (init_config segs pc ph sp brk0 mbase rnd lim inp) T
              /\ permitted_traces allowed T) ->
  halts_within_budget lim allowed (mkImage segs pc ph).
Proof.
  intros lim allowed segs pc ph HR.
  rewrite halts_within_budget_is_lps.
  exact (halts_budgets_of_realizes lim allowed segs pc ph HR).
Qed.
