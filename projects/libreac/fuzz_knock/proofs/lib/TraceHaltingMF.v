From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit Equivalence.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK15.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import TraceHalting.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R Require Import Cfg.
Import ListNotations.

Lemma permitted_traces_sub : forall allowed (T T' : TSet),
  permitted_traces allowed T' -> (forall tr, T tr -> T' tr) -> permitted_traces allowed T.
Proof. intros allowed T T' H Hs tr Htr. exact (H tr (Hs tr Htr)). Qed.

Lemma permitted_halt_next_cfg : forall allowed segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  Forall (permitted_event allowed) evs ->
  permitted_halt allowed c'.
Proof.
  intros allowed segs cfg c evs c' Hstep HE.
  destruct (sstep_cfg_next_halts_by_exit segs cfg c evs c' Hstep)
    as [Hnone | [(es0 & code & E & Hh & Hk) | (es0 & sig & E & Hk)]].
  - unfold permitted_halt. rewrite Hnone. constructor.
  - unfold permitted_halt. rewrite Hh. split; [|exact Hk].
    apply (proj1 (Forall_forall _ _) HE (ExitEv code (m_fs (cfg_model c')))).
    rewrite E. apply in_or_app. right. simpl. auto.
  - exfalso.
    apply (proj1 (Forall_forall _ _) HE (KillEv sig (m_fs (cfg_model c')))).
    rewrite E. apply in_or_app. right. simpl. auto.
Qed.

Theorem realizes_must_exit_mf_halt : forall segs c T,
  @realizes segs MayFail c T -> forall allowed,
  permitted_halt allowed c -> permitted_traces allowed T ->
  must_exit_in_at_cfg may_fail_cfg segs allowed c.
Proof.
  intros segs c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hhalt | c T T' H IH Heq
                 | c I nx T i0 Hnode Hcont IH | c T Hb];
    intros allowed HH HT.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact (sstep_cfg_not_halted _ _ _ _ _ (Hcomp i0)).
    + exists (evs i0), (SNext (nx i0)). exact (Hcomp i0).
    + intros es Herror.
      destruct (Hsound es SError Herror) as [i [_ E]]. discriminate E.
    + intros es c' Hstep.
      destruct (Hsound es (SNext c') Hstep) as [i [Ees Enext]].
      inversion Enext; subst c'. subst es.
      assert (HE : Forall (permitted_event allowed) (evs i)).
      { apply HT. exists i. left. apply is_prefix_refl. }
      apply (IH i allowed).
      * exact (permitted_halt_next_cfg allowed segs may_fail_cfg c (evs i) (nx i) Hstep HE).
      * intros tr Htr.
        assert (HF : Forall (permitted_event allowed) (evs i ++ tr)).
        { apply HT. exists i. right. exists tr. split; [reflexivity | exact Htr]. }
        apply Forall_app in HF. exact (proj2 HF).
  - unfold permitted_halt in HH.
    destruct (m_halted (cfg_model c)) as [code|] eqn:Hh; [|contradiction].
    destruct HH as [Hin Hk].
    eapply must_exit_in_at_cfg_halted; eassumption.
  - exact (IH allowed HH (permitted_traces_sub allowed T T' HT Heq)).
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact (sstep_cfg_not_halted _ _ _ _ _ (Hcomp i0)).
    + exists [], (SNext (nx i0)). exact (Hcomp i0).
    + intros es Herror.
      destruct (Hsound es SError Herror) as [i [_ E]]. discriminate E.
    + intros es c' Hstep.
      destruct (Hsound es (SNext c') Hstep) as [i [Ees Enext]].
      inversion Enext; subst c'. subst es.
      apply (IH i allowed).
      * exact (permitted_halt_next_cfg allowed segs may_fail_cfg c [] (nx i) Hstep (Forall_nil _)).
      * intros tr Htr. apply HT. exists i. exact Htr.
  - exact (False_ind _ Hb).
Qed.

Theorem realizes_must_exit_mf : forall segs c T allowed,
  @realizes segs MayFail c T ->
  permitted_traces allowed T ->
  m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg may_fail_cfg segs allowed c.
Proof.
  intros segs c T allowed HR HT Hh.
  apply (realizes_must_exit_mf_halt segs c T HR allowed); [| exact HT].
  unfold permitted_halt. rewrite Hh. exact I.
Qed.
