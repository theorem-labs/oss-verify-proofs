(** Derive termination from the published inductive trace certificates.
    A trace certificate alone does not restrict exit statuses or exclude kills;
    those obligations are explicit below. Restricting environment failures
    additionally requires LPS's original progress/decision premise. *)
From Stdlib Require Import ZArith List Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit Equivalence.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable.R Require Import Cfg.
Import ListNotations.

Definition permitted_event (allowed : list word) (e : event) : Prop :=
  match e with
  | ExitEv code _ => In code allowed
  | KillEv _ _ => False
  | _ => True
  end.
Definition permitted_traces (allowed : list word) (T : TSet) : Prop :=
  forall tr, T tr -> Forall (permitted_event allowed) tr.
Definition permitted_halt (allowed : list word) (c : config) : Prop :=
  match m_halted (cfg_model c) with
  | None => True
  | Some code => In code allowed /\ m_killed (cfg_model c) = None
  end.

Theorem realizes_must_exit_allowed : forall segs c T,
  realizes segs c T -> forall allowed,
  permitted_halt allowed c -> permitted_traces allowed T ->
  must_exit_in_at_cfg ACFG segs allowed c.
Proof.
  intros segs c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hhalt | c T T' H IH Heq];
    intros allowed HH HT.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact (sstep_cfg_not_halted _ _ _ _ _ (Hcomp i0)).
    + exists (evs i0), (SNext (nx i0)). apply Hcomp.
    + intros es Herror.
      destruct (Hsound es SError Herror) as [i [_ E]]. discriminate E.
    + intros es c' Hstep.
      destruct (Hsound es (SNext c') Hstep) as [i [Ees Enext]].
      inversion Enext; subst c'. subst es.
      assert (HE : Forall (permitted_event allowed) (evs i)).
      { apply HT. exists i. left. apply is_prefix_refl. }
      apply (IH i allowed).
      * destruct (sstep_cfg_next_halts_by_exit segs ACFG c (evs i) (nx i) Hstep)
          as [Hnone | [(es0 & code & E & Hh & Hk) | (es0 & sig & E & Hk)]].
        -- unfold permitted_halt. rewrite Hnone. constructor.
        -- unfold permitted_halt. rewrite Hh. split; [|exact Hk].
           apply (proj1 (Forall_forall _ _) HE (ExitEv code (m_fs (cfg_model (nx i))))).
           rewrite E. apply in_or_app. right. simpl. auto.
        -- exfalso.
           apply (proj1 (Forall_forall _ _) HE (KillEv sig (m_fs (cfg_model (nx i))))).
           rewrite E. apply in_or_app. right. simpl. auto.
      * intros tr Htr.
        assert (HF : Forall (permitted_event allowed) (evs i ++ tr)).
        { apply HT. exists i. right. exists tr. split; [reflexivity | exact Htr]. }
        apply Forall_app in HF. exact (proj2 HF).
  - unfold permitted_halt in HH.
    destruct (m_halted (cfg_model c)) as [code|] eqn:Hh; [|contradiction].
    destruct HH as [Hin Hk].
    eapply must_exit_in_at_cfg_halted; eassumption.
  - apply (IH allowed); [exact HH |].
    intros tr Htr. apply HT. apply Heq. exact Htr.
Qed.

Lemma refusal_decided_classical : forall cfg i model,
  refusal_decided cfg i model.
Proof.
  intros cfg i model Hfamily.
  destruct (classic (exists eff next events,
    syscall_spec i model (Ok eff next events) /\ refusal_b i model (eff_ret eff) = false))
    as [Hsuccess | Hnone].
  - left. exact Hsuccess.
  - right. intros eff next events Hspec.
    destruct (refusal_b i model (eff_ret eff)) eqn:Hrefusal; [reflexivity |].
    exfalso. apply Hnone. exists eff, next, events. auto.
Qed.

Lemma decided_from_classical : forall cfg segs c, decided_from cfg segs c.
Proof.
  intros cfg segs c tr c' x8 Hstar Hpending.
  apply refusal_decided_classical.
Qed.

Corollary realizes_must_exit_forced : forall segs c T allowed,
  realizes segs c T -> permitted_halt allowed c -> permitted_traces allowed T ->
  decided_from forced_only_cfg segs c ->
  must_exit_in_at_cfg forced_only_cfg segs allowed c.
Proof.
  intros segs c T allowed HR HH HT HD.
  eapply must_exit_in_at_cfg_mono.
  - apply forced_only_cfg_least.
  - exact HD.
  - eapply realizes_must_exit_allowed; eassumption.
Qed.

Corollary realizes_must_exit_forced_closed : forall segs c T allowed,
  realizes segs c T -> permitted_halt allowed c -> permitted_traces allowed T ->
  must_exit_in_at_cfg forced_only_cfg segs allowed c.
Proof.
  intros segs c T allowed HR HH HT.
  eapply realizes_must_exit_forced; [exact HR | exact HH | exact HT |].
  apply decided_from_classical.
Qed.

Set Printing Fully Qualified.
Print Assumptions realizes_must_exit_forced.
Print Assumptions realizes_must_exit_forced_closed.
