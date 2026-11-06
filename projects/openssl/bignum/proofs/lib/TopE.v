(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section Glue.
  Variable cfg : SpuriousCfg.
  Variable T : ProcInput -> list event -> Prop.

  Definition side_canon (img : Image) (lim : Z) : Prop :=
    forall en inp, valid_entry img en inp -> valid_input_either inp ->
      trace_equiv (bh_traces (run_scfg cfg img lim en inp)) (T inp) /\ ~ bh_errors (run_scfg cfg img lim en inp).

  Definition side_canon_off (img : Image) (lim : Z) : Prop :=
    forall en inp, valid_entry img en inp -> valid_input inp ->
      trace_equiv (bh_traces (run_scfg cfg img lim en inp)) (T inp) /\ ~ bh_errors (run_scfg cfg img lim en inp).

  Lemma side_canon_off_of_either : forall img lim, side_canon img lim -> side_canon_off img lim.
  Proof. intros img lim H en inp He Hv. exact (H en inp He (valid_input_either_of_valid_input _ Hv)). Qed.

  Definition T_nokill : Prop := forall inp tr sig fs, T inp tr -> ~ In (KillEv sig fs) tr.

  Variables (imgS imgT : Image).

  Section Off.
  Hypothesis HS : side_canon_off imgS source_alloc_limit.
  Hypothesis HT : side_canon_off imgT target_alloc_limit.

  Lemma glue_traces : forall enS enT inp,
    valid_entry imgS enS inp -> valid_entry imgT enT inp -> valid_input inp ->
    trace_equiv (bh_traces (run_scfg cfg imgS source_alloc_limit enS inp))
                (bh_traces (run_scfg cfg imgT target_alloc_limit enT inp)).
  Proof.
    intros enS enT inp HeS HeT Hi tr.
    rewrite (proj1 (HS enS inp HeS Hi) tr). symmetry. exact (proj1 (HT enT inp HeT Hi) tr).
  Qed.

  Theorem glue_scfg : strong_universal_error_free_T_scfg cfg imgS imgT.
  Proof.
    intros enS enT inp HeS HeT Hv.
    split; [exact (proj2 (HS enS inp HeS Hv))|]. split; [exact (proj2 (HT enT inp HeT Hv))|].
    exact (glue_traces enS enT inp HeS HeT Hv).
  Qed.

  Theorem glue_scfg_budgets :
    strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target imgS imgT.
  Proof. apply (strong_universal_error_free_T_scfg_budgets_of_scfg cfg). exact glue_scfg. Qed.

  Theorem glue_scfg_baseline : strong_universal_T_scfg cfg imgS imgT.
  Proof. apply strong_universal_error_free_T_scfg_implies. exact glue_scfg. Qed.
  End Off.

  Section OffLim.
  Variables (limS limT : Z).
  Hypothesis HS : side_canon_off imgS limS.
  Hypothesis HT : side_canon_off imgT limT.
  Theorem glue_scfg_budgets_lim : strong_universal_error_free_T_scfg_budgets cfg limS limT imgS imgT.
  Proof.
    intros enS enT inp HeS HeT Hv _.
    split; [exact (proj2 (HS enS inp HeS Hv))|]. split; [exact (proj2 (HT enT inp HeT Hv))|].
    intros tr. rewrite (proj1 (HS enS inp HeS Hv) tr). symmetry. exact (proj1 (HT enT inp HeT Hv) tr).
  Qed.
  End OffLim.

  Section Either.
  Hypothesis HS : side_canon imgS source_alloc_limit.
  Hypothesis HT : side_canon imgT target_alloc_limit.

  Theorem glue_scfg_e : strong_universal_error_free_T_scfg cfg imgS imgT.
  Proof. exact (glue_scfg (side_canon_off_of_either _ _ HS) (side_canon_off_of_either _ _ HT)). Qed.

  Theorem glue_scfg_budgets_e :
    strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target imgS imgT.
  Proof. exact (glue_scfg_budgets (side_canon_off_of_either _ _ HS) (side_canon_off_of_either _ _ HT)). Qed.
  End Either.
End Glue.
