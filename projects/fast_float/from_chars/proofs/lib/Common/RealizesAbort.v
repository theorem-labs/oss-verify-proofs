(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition image_realizes_cfg_e (cfg : SpuriousCfg) (segs : list Segment) (pc : N)
    (ph : PhdrInfo) (lim : Z) (Spec : ProcInput -> TSet) : Prop :=
  forall sp brk0 mb rnd inp,
    valid_entry (mkImage segs pc ph) (mkEntry sp brk0 mb rnd) inp ->
    valid_input_either inp ->
    realizes_cfg segs cfg (init_config segs pc ph sp brk0 mb rnd lim inp) (Spec inp).

(* [comment removed for export] *)
Lemma image_realizes_cfg_of_e : forall cfg segs pc ph lim Spec,
  image_realizes_cfg_e cfg segs pc ph lim Spec ->
  image_realizes_cfg cfg segs pc ph lim Spec.
Proof.
  intros cfg segs pc ph lim Spec H sp brk0 mb rnd inp Hv Hinp.
  apply H; [exact Hv | exact (valid_input_either_of_valid_input _ Hinp)].
Qed.

(* [comment removed for export] *)
Lemma image_realizes_cfg_abort_of_e : forall cfg segs pc ph lim Spec sp brk0 mb rnd inp,
  image_realizes_cfg_e cfg segs pc ph lim Spec ->
  valid_entry (mkImage segs pc ph) (mkEntry sp brk0 mb rnd) inp ->
  valid_input_abort inp ->
  realizes_cfg segs cfg (init_config segs pc ph sp brk0 mb rnd lim inp) (Spec inp).
Proof.
  intros cfg segs pc ph lim Spec sp brk0 mb rnd inp H Hv Hinp.
  apply H; [exact Hv | exact (valid_input_either_of_valid_input_abort _ Hinp)].
Qed.

(* [comment removed for export] *)
Definition no_kill (Spec : ProcInput -> TSet) : Prop :=
  forall inp tr sig fs, Spec inp tr -> ~ List.In (KillEv sig fs) tr.

(* [comment removed for export] *)
Lemma realizes_cfg_error_free_unkilled : forall cfg segs pc ph sp brk0 mb rnd lim inp T,
  realizes_cfg segs cfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  (forall tr sig fs, T tr -> ~ List.In (KillEv sig fs) tr) ->
  error_free_unkilled (run_scfg cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros cfg segs pc ph sp brk0 mb rnd lim inp T HR HK. split.
  - exact (realizes_cfg_error_free cfg segs pc ph sp brk0 mb rnd lim inp T HR).
  - intros (tr & sig & fs & Htr & Hin).
    apply (HK tr sig fs); [| exact Hin].
    exact (proj1 (realizes_cfg_traces_iff cfg segs pc ph sp brk0 mb rnd lim inp T tr HR) Htr).
Qed.

(* [comment removed for export] *)
Theorem shape_strong_equiv_ef_scfg_abort :
  forall (cfg : SpuriousCfg)
         source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes_cfg source_segs cfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes_cfg target_segs cfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  (forall tr sig fs, T tr -> ~ List.In (KillEv sig fs) tr) ->
  error_free_unkilled (run_scfg cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free_unkilled (run_scfg cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv
       (bh_traces (run_scfg cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
       (bh_traces (run_scfg cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros cfg source_segs rpc rph rsp rbrk rmb rrnd rlim
    target_segs apc aph asp abrk amb arnd alim T inp Hsource Htarget HK.
  split; [| split].
  - eapply realizes_cfg_error_free_unkilled; eassumption.
  - eapply realizes_cfg_error_free_unkilled; eassumption.
  - intro tr.
    rewrite (realizes_cfg_traces_iff cfg source_segs rpc rph rsp rbrk rmb rrnd rlim inp T tr Hsource).
    rewrite (realizes_cfg_traces_iff cfg target_segs apc aph asp abrk amb arnd alim inp T tr Htarget).
    reflexivity.
Qed.

(* [comment removed for export] *)
Theorem strong_universal_error_free_T_scfg_budgets_abort_of_realizes :
  forall (cfg : SpuriousCfg) (lim_s lim_t : Z) source_segs rpc rph target_segs apc aph
         (Spec : ProcInput -> TSet),
  image_realizes_cfg_e cfg source_segs rpc rph lim_s Spec ->
  image_realizes_cfg_e cfg target_segs apc aph lim_t Spec ->
  no_kill Spec ->
  strong_universal_error_free_T_scfg_budgets_abort cfg lim_s lim_t
    (mkImage source_segs rpc rph) (mkImage target_segs apc aph).
Proof.
  intros cfg lim_s lim_t source_segs rpc rph target_segs apc aph Spec HS HT HK
    [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hvs Hvt Hinp _.
  unfold strong_equiv_error_free_budgets_scfg_abort.
  apply shape_strong_equiv_ef_scfg_abort with (T := Spec inp).
  - exact (image_realizes_cfg_abort_of_e cfg _ _ _ _ Spec _ _ _ _ inp HS Hvs Hinp).
  - exact (image_realizes_cfg_abort_of_e cfg _ _ _ _ Spec _ _ _ _ inp HT Hvt Hinp).
  - intros tr sig fs. exact (HK inp tr sig fs).
Qed.

(* [comment removed for export] *)
Corollary strong_universal_error_free_T_scfg_budgets_abort_shipped :
  forall (cfg : SpuriousCfg) source_segs rpc rph target_segs apc aph
         (Spec : ProcInput -> TSet),
  image_realizes_cfg_e cfg source_segs rpc rph source_alloc_limit Spec ->
  image_realizes_cfg_e cfg target_segs apc aph target_alloc_limit Spec ->
  no_kill Spec ->
  strong_universal_error_free_T_scfg_budgets_abort cfg
    ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage source_segs rpc rph) (mkImage target_segs apc aph).
Proof.
  intros. apply strong_universal_error_free_T_scfg_budgets_abort_of_realizes with (Spec := Spec);
    assumption.
Qed.

(* [comment removed for export] *)
Corollary strong_universal_error_free_T_scfg_budgets_abort_sanitizer :
  forall (cfg : SpuriousCfg) source_segs rpc rph target_segs apc aph
         (Spec : ProcInput -> TSet),
  image_realizes_cfg_e cfg source_segs rpc rph SanitizerBudgets.lim_source Spec ->
  image_realizes_cfg_e cfg target_segs apc aph SanitizerBudgets.lim_target Spec ->
  no_kill Spec ->
  strong_universal_error_free_T_scfg_budgets_abort cfg
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage source_segs rpc rph) (mkImage target_segs apc aph).
Proof.
  intros. apply strong_universal_error_free_T_scfg_budgets_abort_of_realizes with (Spec := Spec);
    assumption.
Qed.
