(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section Glue.
  Variable T : ProcInput -> list event -> Prop.

  Definition side_canon (img : Image) (lim : Z) : Prop :=
    forall en inp, valid_entry img en inp -> valid_input_either inp ->
      trace_equiv (bh_traces (run_scfg ACFG img lim en inp)) (T inp) /\ ~ bh_errors (run_scfg ACFG img lim en inp).

  Definition T_nokill : Prop := forall inp tr sig fs, T inp tr -> ~ In (KillEv sig fs) tr.

  Lemma side_unkilled : forall img lim, side_canon img lim -> T_nokill ->
    forall en inp, valid_entry img en inp -> valid_input_either inp -> error_free_unkilled (run_scfg ACFG img lim en inp).
  Proof.
    intros img lim H NK en inp He Hi. destruct (H en inp He Hi) as [Htr Herr]. split; [exact Herr|].
    intros (tr & sig & fs & Hb & Hin). exact (NK inp tr sig fs (proj1 (Htr tr) Hb) Hin).
  Qed.

  Variables (imgS imgT : Image).
  Hypothesis HS : side_canon imgS source_alloc_limit.
  Hypothesis HT : side_canon imgT target_alloc_limit.

  Lemma glue_traces : forall enS enT inp,
    valid_entry imgS enS inp -> valid_entry imgT enT inp -> valid_input_either inp ->
    trace_equiv (bh_traces (run_scfg ACFG imgS source_alloc_limit enS inp)) (bh_traces (run_scfg ACFG imgT target_alloc_limit enT inp)).
  Proof.
    intros enS enT inp HeS HeT Hi tr.
    rewrite (proj1 (HS enS inp HeS Hi) tr). symmetry. exact (proj1 (HT enT inp HeT Hi) tr).
  Qed.

  Theorem glue_off : strong_universal_error_free_T_scfg ACFG imgS imgT.
  Proof.
    intros enS enT inp HeS HeT Hv. pose proof (valid_input_either_of_valid_input _ Hv) as Hi.
    split; [exact (proj2 (HS enS inp HeS Hi))|]. split; [exact (proj2 (HT enT inp HeT Hi))|].
    exact (glue_traces enS enT inp HeS HeT Hi).
  Qed.

  Theorem glue_abort : T_nokill -> strong_universal_error_free_T_scfg_abort ACFG imgS imgT.
  Proof.
    intros NK enS enT inp HeS HeT Hv. pose proof (valid_input_either_of_valid_input_abort _ Hv) as Hi.
    split; [exact (side_unkilled _ _ HS NK enS inp HeS Hi)|]. split; [exact (side_unkilled _ _ HT NK enT inp HeT Hi)|].
    exact (glue_traces enS enT inp HeS HeT Hi).
  Qed.

  Theorem glue_budgets_abort : T_nokill ->
    strong_universal_error_free_T_scfg_budgets_abort ACFG ShippedBudgets.lim_source ShippedBudgets.lim_target imgS imgT.
  Proof. intros NK. exact (strong_universal_error_free_T_scfg_budgets_abort_of_scfg ACFG imgS imgT (glue_abort NK)). Qed.
End Glue.

Section GlueLim.
  Variable T : ProcInput -> list event -> Prop.
  Variables (limS : Z) (imgS imgT : Image).
  Hypothesis HS : side_canon T imgS limS.
  Hypothesis HT : side_canon T imgT target_alloc_limit.

  Lemma glue_traces_lim : forall enS enT inp,
    valid_entry imgS enS inp -> valid_entry imgT enT inp -> valid_input_either inp ->
    trace_equiv (bh_traces (run_scfg ACFG imgS limS enS inp)) (bh_traces (run_scfg ACFG imgT target_alloc_limit enT inp)).
  Proof.
    intros enS enT inp HeS HeT Hi tr.
    rewrite (proj1 (HS enS inp HeS Hi) tr). symmetry. exact (proj1 (HT enT inp HeT Hi) tr).
  Qed.

  Theorem glue_budgets_abort_lim : T_nokill T ->
    strong_universal_error_free_T_scfg_budgets_abort ACFG limS target_alloc_limit imgS imgT.
  Proof.
    intros NK enS enT inp HeS HeT Hv _. pose proof (valid_input_either_of_valid_input_abort _ Hv) as Hi.
    split; [exact (side_unkilled T _ _ HS NK enS inp HeS Hi)|]. split; [exact (side_unkilled T _ _ HT NK enT inp HeT Hi)|].
    exact (glue_traces_lim enS enT inp HeS HeT Hi).
  Qed.
End GlueLim.

Theorem glue_budgets_abort_san : forall T imgS imgT,
  side_canon T imgS SanitizerBudgets.lim_source -> side_canon T imgT target_alloc_limit -> T_nokill T ->
  strong_universal_error_free_T_scfg_budgets_abort ACFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target imgS imgT.
Proof. intros T imgS imgT HS HT NK. exact (glue_budgets_abort_lim T _ imgS imgT HS HT NK). Qed.
