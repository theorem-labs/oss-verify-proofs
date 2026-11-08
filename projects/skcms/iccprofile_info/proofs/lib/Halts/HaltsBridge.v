(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/fast_float/from_chars/proofs/lib/Common/RealizesHalts.v at commit c395a1e0dfa (its whole content bar the abort section: refusal_decided_classic, decided_from_classic, the two cfg-monotonicity lemmas, exits_in, kill_free and their closure lemmas, realizes_cfg_must_exit_in and the three corollaries), with [realizes_cfg segs cfg] replaced throughout by skcms/iccprofile_info's Info.ShapeAlg.realizes, whose node relation is pinned to Info.ShapeAlg.CFG, and with the image premise taken as Info.ProofInfoPlan.realizes_spec_stmt rather than from_chars's image_realizes_cfg_e. *)
(** From a [realizes] fact about an image to [HaltsAllowed.halts_allowed_T_scfg_budgets].

    [Info.ShapeAlg.realizes] has no spinning leaf: its three constructors are a
    node that covers every step the configured relation admits, a halted
    configuration, and a rewriting of the realized set.  So a derivation of it
    is a well-founded tree of steps ending in halted configurations, and when
    every exit the set admits carries an allowed status and the set admits no
    death by a signal, the configuration must exit with an allowed status. *)

From Stdlib Require Import ZArith NArith List Bool.
From Stdlib Require Import Logic.Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec ShapeAlg Spec ProofInfoPlan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts Require Import SpecHalts.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Existing Instance PropExec.fp0.

(** ** The refusal question, answered classically *)

Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m _.
  destruct (classic (exists eff' m' evs',
              syscall_spec i m (Ok eff' m' evs')
              /\ refusal_b i m (eff_ret eff') = false)) as [H | H];
    [left; exact H | right].
  intros eff' m' evs' Hs.
  destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity | exfalso].
  apply H. exists eff', m', evs'. split; [exact Hs | exact E].
Qed.

Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.

Lemma must_exit_in_at_cfg_mono_classic : forall cfg1 cfg2 segs S c,
  cfg_le cfg1 cfg2 ->
  must_exit_in_at_cfg cfg2 segs S c ->
  must_exit_in_at_cfg cfg1 segs S c.
Proof.
  intros cfg1 cfg2 segs S c Hle H.
  exact (must_exit_in_at_cfg_mono cfg1 cfg2 segs S c Hle (decided_from_classic cfg1 segs c) H).
Qed.

(** ** What the realized set must say *)

Definition exits_in (S : list word) (T : TSet) : Prop :=
  forall tr code fs, T (tr ++ [ExitEv code fs]) -> In code S.

Definition kill_free (T : TSet) : Prop :=
  forall tr sig fs, ~ T (tr ++ [KillEv sig fs]).

Lemma exits_in_eq : forall S T T', t_eq T T' -> exits_in S T' -> exits_in S T.
Proof. intros S T T' Heq H tr code fs Htr. apply (H tr code fs). apply Heq. exact Htr. Qed.

Lemma kill_free_eq : forall T T', t_eq T T' -> kill_free T' -> kill_free T.
Proof. intros T T' Heq H tr sig fs Htr. apply (H tr sig fs). apply Heq. exact Htr. Qed.

Lemma node_shape_cont : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i tr,
  T i tr -> t_alt (fun j => t_emit (evs j) (T j)) (evs i ++ tr).
Proof. intros I evs T i tr Htr. exists i. right. exists tr. split; [reflexivity | exact Htr]. Qed.

Lemma exits_in_cont : forall S (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  exits_in S (t_alt (fun j => t_emit (evs j) (T j))) -> exits_in S (T i).
Proof.
  intros S I evs T i H tr code fs Htr.
  apply (H (evs i ++ tr) code fs). rewrite <- app_assoc. apply node_shape_cont. exact Htr.
Qed.

Lemma kill_free_cont : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  kill_free (t_alt (fun j => t_emit (evs j) (T j))) -> kill_free (T i).
Proof.
  intros I evs T i H tr sig fs Htr.
  apply (H (evs i ++ tr) sig fs). rewrite <- app_assoc. apply node_shape_cont. exact Htr.
Qed.

Lemma node_shape_self : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  t_alt (fun j => t_emit (evs j) (T j)) (evs i).
Proof. intros I evs T i. exists i. left. apply is_prefix_refl. Qed.

(** ** The walk *)

Section WithSegs.
Variable segs : list Segment.
Variable S : list word.

Theorem realizes_must_exit_in : forall c T,
  realizes segs c T ->
  m_halted (cfg_model c) = None ->
  exits_in S T ->
  kill_free T ->
  must_exit_in_at_cfg CFG segs S c.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros Hnone HE HK.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + exists (evs i0), (SNext (nx i0)). apply Hcomp.
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Hbad). discriminate Hbad.
    + intros e c' Hss.
      destruct (Hsound e (SNext c') Hss) as (i & He & Hc'). injection Hc' as Hc'. subst e c'.
      destruct (m_halted (cfg_model (nx i))) as [code |] eqn:Hh.
      * destruct (sstep_cfg_next_halts_by_exit _ _ _ _ _ Hss)
          as [Hn | [(evs0 & code0 & Hevs & Hcode0 & Hk0) | (evs0 & sig & Hevs & Hsig)]].
        -- exfalso. rewrite Hn in Hh. discriminate Hh.
        -- apply (must_exit_in_at_cfg_halted CFG segs S (nx i) code0 Hcode0); [| exact Hk0].
           apply (HE evs0 code0 (m_fs (cfg_model (nx i)))). rewrite <- Hevs. apply node_shape_self.
        -- exfalso. apply (HK evs0 sig (m_fs (cfg_model (nx i)))). rewrite <- Hevs. apply node_shape_self.
      * apply (IH i Hh).
        -- exact (exits_in_cont S I evs T i HE).
        -- exact (kill_free_cont I evs T i HK).
  - exfalso. exact (Hh Hnone).
  - apply IH; [exact Hnone | exact (exits_in_eq S T T' Heq HE) | exact (kill_free_eq T T' Heq HK)].
Qed.

End WithSegs.

(** ** The two facts of [SpecHalts], in the form the walk consumes *)

Lemma exits_in_spec : forall argv fs0, exits_in HALT_CODES (spec argv fs0).
Proof.
  intros argv fs0 tr code fs Htr.
  apply (exs_spec argv fs0 _ code fs Htr). apply in_app_iff. right. left. reflexivity.
Qed.

Lemma kill_free_spec : forall argv fs0, kill_free (spec argv fs0).
Proof.
  intros argv fs0 tr sig fs Htr.
  apply (nk_spec argv fs0 _ sig fs Htr). apply in_app_iff. right. left. reflexivity.
Qed.

(** ** From [realizes_spec_stmt] to the halting statement *)

Theorem must_exit_of_realizes_spec : forall segs pc ph lim,
  realizes_spec_stmt segs pc ph lim ->
  forall en inp,
    valid_entry (mkImage segs pc ph) en inp ->
    valid_input inp ->
    must_exit_in_scfg forced_only_cfg HALT_CODES (mkImage segs pc ph) lim en inp.
Proof.
  intros segs pc ph lim HR [sp brk0 mbase rnd] inp Hen Hinp.
  cbn [must_exit_in_scfg].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfit).
  destruct Hinp as (Hargv & Henvp & Hfs & _).
  apply (must_exit_in_at_cfg_mono_classic forced_only_cfg CFG segs HALT_CODES _
           (forced_only_cfg_least CFG)).
  apply (realizes_must_exit_in segs HALT_CODES _ (spec (in_argv inp) (in_fs inp))
           (HR sp brk0 mbase rnd inp Hsp Hbrk Hfit Hargv Henvp Hfs)).
  - cbn [init_config cfg_model]. reflexivity.
  - exact (exits_in_spec (in_argv inp) (in_fs inp)).
  - exact (kill_free_spec (in_argv inp) (in_fs inp)).
Qed.

(** The statement's own form: the budget premise is not needed at the budget
    the realization is proved at, so it is dropped. *)
Theorem halts_of_realizes_spec : forall segs pc ph lim,
  realizes_spec_stmt segs pc ph lim ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim HALT_CODES (mkImage segs pc ph).
Proof.
  intros segs pc ph lim HR en inp Hen Hinp _.
  exact (must_exit_of_realizes_spec segs pc ph lim HR en inp Hen Hinp).
Qed.
