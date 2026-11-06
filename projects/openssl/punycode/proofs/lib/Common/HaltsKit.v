(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import CfgStep ShapeAlg.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition exits_in (S : list word) (T : TSet) : Prop :=
  forall tr code fs, T (tr ++ [ExitEv code fs]) -> In code S.

(* [comment removed for export] *)
Definition kill_free (T : TSet) : Prop :=
  forall tr sig fs, ~ T (tr ++ [KillEv sig fs]).

Lemma exits_in_eq : forall S T T', t_eq T T' -> exits_in S T -> exits_in S T'.
Proof. intros S T T' Heq H tr code fs HT. apply (H tr code fs). apply Heq. exact HT. Qed.

Lemma kill_free_eq : forall T T', t_eq T T' -> kill_free T -> kill_free T'.
Proof. intros T T' Heq H tr sig fs HT. apply (H tr sig fs). apply Heq. exact HT. Qed.

Lemma exits_in_mono : forall S1 S2 T,
  (forall code, In code S1 -> In code S2) -> exits_in S1 T -> exits_in S2 T.
Proof. intros S1 S2 T Hsub H tr code fs HT. apply Hsub. exact (H tr code fs HT). Qed.

Section NodeShape.
  Context {I : Type} (evs : I -> list event) (T : I -> TSet).

  (* [comment removed for export] *)
  Lemma node_shape_own : forall i, t_alt (fun i => t_emit (evs i) (T i)) (evs i).
  Proof. intros i. exists i. left. apply is_prefix_refl. Qed.

  (* [comment removed for export] *)
  Lemma node_shape_child : forall i tr, T i tr -> t_alt (fun i => t_emit (evs i) (T i)) (evs i ++ tr).
  Proof. intros i tr H. exists i. right. exists tr. split; [reflexivity | exact H]. Qed.

  Lemma exits_in_child : forall S,
    exits_in S (t_alt (fun i => t_emit (evs i) (T i))) -> forall i, exits_in S (T i).
  Proof.
    intros S H i tr code fs HT. apply (H (evs i ++ tr) code fs).
    rewrite <- app_assoc. apply node_shape_child. exact HT.
  Qed.

  Lemma kill_free_child :
    kill_free (t_alt (fun i => t_emit (evs i) (T i))) -> forall i, kill_free (T i).
  Proof.
    intros H i tr sig fs HT. apply (H (evs i ++ tr) sig fs).
    rewrite <- app_assoc. apply node_shape_child. exact HT.
  Qed.
End NodeShape.

(* [comment removed for export] *)

Section HaltsKit.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma cfg_step_of_kit_step : forall cfg c e c',
  cfg_le cfg kit_cfg ->
  (forall e', ~ sstep_cfg segs kit_cfg c e' SError) ->
  sstep_cfg segs kit_cfg c e (SNext c') ->
  exists e'' st, sstep_cfg segs cfg c e'' st.
Proof.
  intros cfg c e c' Hle Hnoerr H.
  inversion H; subst.
  - (* [comment removed for export] *)
    eexists _, _. eapply sstep_cfg_instr; eassumption.
  - (* [comment removed for export] *)
    match goal with
    | [ Hspec : syscall_spec (sys_input segs ?ms ?x8) ?model (Ok ?eff ?model' ?evs) |- _ ] =>
        destruct (classic (spurious_refusal_cfg cfg (sys_input segs ms x8) model eff)) as [Hsp | Hnsp];
        [ | eexists _, _; eapply sstep_cfg_syscall; eassumption ]
    end.
    (* [comment removed for export] *)
    destruct Hsp as (_ & _ & (eff' & m' & evs' & Hspec' & Hnr)).
    pose proof (spurious_refusal_not_refusal cfg _ _ _ Hnr) as Hns.
    destruct (m_killed m') as [sig |] eqn:Hk'.
    + eexists _, _. eapply sstep_cfg_killed; eassumption.
    + destruct (m_halted m') as [code |] eqn:Hh'.
      * eexists _, _. eapply sstep_cfg_exit; eassumption.
      * destruct (materialize_model_accesses m' (syscall_effect_accesses eff')) as [m'' |] eqn:Hmat.
        { eexists _, _. eapply sstep_cfg_syscall; eassumption. }
        { exfalso. eapply (Hnoerr []).
          eapply sstep_cfg_syscall_materialization_fault; try eassumption.
          exact (spurious_refusal_not_refusal kit_cfg _ _ _ Hnr). }
  - (* [comment removed for export] *)
    eexists _, _. eapply sstep_cfg_exit; eassumption.
  - (* [comment removed for export] *)
    eexists _, _. eapply sstep_cfg_killed; eassumption.
Qed.

(* [comment removed for export] *)
Theorem realizes_must_exit : forall c T,
  realizes segs c T ->
  forall S cfg, cfg_le cfg kit_cfg ->
  exits_in S T ->
  kill_free T ->
  m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg cfg segs S c.
Proof.
  intros c T H S cfg Hle.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros HS HK Hnone.
  - destruct Hnode as [Hcomp Hsound].
    assert (Hnoerr : forall e, ~ sstep_cfg segs kit_cfg c e SError).
    { intros e He. destruct (Hsound e SError He) as (i & _ & Hst). discriminate Hst. }
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + exact (cfg_step_of_kit_step cfg c (evs i0) (nx i0) Hle Hnoerr (Hcomp i0)).
    + intros e He. exact (Hnoerr e (sstep_cfg_mono segs cfg kit_cfg c e SError Hle He)).
    + intros e c' He.
      destruct (Hsound e (SNext c') (sstep_cfg_mono segs cfg kit_cfg c e (SNext c') Hle He))
        as (i & He_i & Hst).
      injection Hst as Hc'. subst e c'.
      destruct (sstep_cfg_next_halts_by_exit segs cfg c (evs i) (nx i) He)
        as [Hn | [(evs0 & code & Hevs & Hcode & Hkill) | (evs0 & sig & Hevs & Hsig)]].
      * apply (IH i).
        -- exact (exits_in_child evs T S HS i).
        -- exact (kill_free_child evs T HK i).
        -- exact Hn.
      * apply (must_exit_in_at_cfg_halted cfg segs S (nx i) code Hcode); [| exact Hkill].
        apply (HS evs0 code (m_fs (cfg_model (nx i)))). rewrite <- Hevs. apply node_shape_own.
      * exfalso. apply (HK evs0 sig (m_fs (cfg_model (nx i)))). rewrite <- Hevs. apply node_shape_own.
  - exfalso. exact (Hh Hnone).
  - apply IH.
    + exact (exits_in_eq S T' T (t_eq_sym T T' Heq) HS).
    + exact (kill_free_eq T' T (t_eq_sym T T' Heq) HK).
    + exact Hnone.
Qed.

(* [comment removed for export] *)
Corollary realizes_must_exit_forced_only : forall c T S,
  realizes segs c T ->
  exits_in S T -> kill_free T -> m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros c T S H HS HK Hnone.
  exact (realizes_must_exit c T H S forced_only_cfg (forced_only_cfg_least kit_cfg) HS HK Hnone).
Qed.

End HaltsKit.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lane_halts (cfg : SpuriousCfg) (segs : list Segment) (pc : N) (ph : PhdrInfo)
    (lim : Z) (S : list word) : Prop :=
  forall en inp,
    valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
    must_exit_in_at_cfg cfg segs S
      (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp).

Lemma halts_allowed_of_lane : forall cfg segs pc ph lim S,
  lane_halts cfg segs pc ph lim S ->
  halts_allowed_T_scfg_budgets cfg lim S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lim S H en inp Hen Hv _.
  destruct en as [sp brk0 mbase rnd]. exact (H _ inp Hen Hv).
Qed.

(* [comment removed for export] *)
Lemma halts_allowed_scfg_of_lane : forall cfg segs pc ph S,
  lane_halts cfg segs pc ph source_alloc_limit S ->
  halts_allowed_T_scfg cfg S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph S H en inp Hen Hv.
  destruct en as [sp brk0 mbase rnd]. exact (H _ inp Hen Hv).
Qed.
