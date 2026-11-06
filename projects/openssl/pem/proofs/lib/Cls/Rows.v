(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition always_accepts (C : Image) : Prop :=
  forall f en, valid_fin_input f -> valid_entry C en (to_proc_input f) ->
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f).

(* [comment removed for export] *)
Lemma always_accepts_accepts_fo : forall C,
  always_accepts C <-> (forall f, valid_fin_input f -> accepts_fo C f).
Proof.
  intros C. unfold always_accepts, accepts_fo. split.
  - intros H f Hf en Hen. exact (H f en Hf Hen).
  - intros H f en Hf Hen. exact (H f Hf en Hen).
Qed.

(* [comment removed for export] *)
Lemma always_accepts_of_must_exit : forall C,
  (forall inp en, valid_input inp -> valid_entry C en inp ->
     must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp) ->
  always_accepts C.
Proof. intros C H f en Hf Hen. exact (H (to_proc_input f) en Hf Hen). Qed.

(* [comment removed for export] *)
Lemma always_accepts_eq : forall C C', C' = C -> always_accepts C -> always_accepts C'.
Proof. intros C C' -> H. exact H. Qed.

(* [comment removed for export] *)
Theorem total_of_always_accepts : forall C, always_accepts C -> classifier_total_T_fo C.
Proof. intros C H f Hf en Hen. left. exact (H f en Hf Hen). Qed.

(* [comment removed for export] *)
Theorem decides_fo_of_always_accepts : forall C (spec : ProcInput -> Prop),
  always_accepts C ->
  (forall f, valid_fin_input f -> spec (to_proc_input f)) ->
  decides_fo C spec.
Proof.
  intros C spec Hacc Hspec f Hf en Hen. split.
  - split; [intros _; exact (Hspec f Hf) | intros _; exact (Hacc f en Hf Hen)].
  - left. exact (Hacc f en Hf Hen).
Qed.

(* [comment removed for export] *)
Theorem decides_fo_always_accepts_necessary : forall C (spec : ProcInput -> Prop),
  image_brk_satisfiable (img_segments C) = true ->
  always_accepts C ->
  decides_fo C spec ->
  forall f, valid_fin_input f -> spec (to_proc_input f).
Proof.
  intros C spec Hwf Hacc Hdec f Hf.
  destruct (image_brk_satisfiable_entry C (to_proc_input f) Hf Hwf) as [en Hen].
  destruct (Hdec f Hf en Hen) as [Hiff _].
  apply Hiff. exact (Hacc f en Hf Hen).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fin_good (cfg : SpuriousCfg) (SRC TGT : Image) : Prop :=
  forall f, valid_fin_input f -> good_input_s cfg SRC TGT (to_proc_input f).

(* [comment removed for export] *)
Definition entry_independent_s (cfg : SpuriousCfg) (X : Image) (lim : Z) (inp : ProcInput) : Prop :=
  forall en1 en2, valid_entry X en1 inp -> valid_entry X en2 inp ->
    trace_equiv (bh_traces (run_scfg cfg X lim en1 inp)) (bh_traces (run_scfg cfg X lim en2 inp)).

Definition fin_entry_independent (cfg : SpuriousCfg) (X : Image) (lim : Z) : Prop :=
  forall f, valid_fin_input f -> entry_independent_s cfg X lim (to_proc_input f).

(* [comment removed for export] *)
Definition fin_never_refused (cfg : SpuriousCfg) (SRC : Image) : Prop :=
  forall f en, valid_fin_input f -> valid_entry SRC en (to_proc_input f) ->
    source_within_budget_scfg cfg source_alloc_limit SRC en (to_proc_input f).

(* [comment removed for export] *)
Lemma fin_good_of_pinned : forall cfg SRC TGT,
  strong_universal_error_free_T_scfg cfg SRC TGT -> fin_good cfg SRC TGT.
Proof. intros cfg SRC TGT H f Hf en1 en2 H1 H2. exact (H en1 en2 (to_proc_input f) H1 H2 Hf). Qed.

(* [comment removed for export] *)
Lemma fin_good_of_budgets : forall cfg SRC TGT,
  strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target SRC TGT ->
  fin_never_refused cfg SRC ->
  fin_good cfg SRC TGT.
Proof.
  intros cfg SRC TGT H Hn f Hf en1 en2 H1 H2.
  exact (H en1 en2 (to_proc_input f) H1 H2 Hf (Hn f en1 Hf H1)).
Qed.

(* [comment removed for export] *)
Lemma fin_never_refused_of_unfiltered : forall cfg SRC,
  (forall f en, valid_fin_input f -> valid_entry SRC en (to_proc_input f) ->
     source_within_budget source_alloc_limit SRC en (to_proc_input f)) ->
  fin_never_refused cfg SRC.
Proof.
  intros cfg SRC H f en Hf Hen.
  apply source_within_budget_scfg_of_source_within_budget. exact (H f en Hf Hen).
Qed.

(* [comment removed for export] *)
Lemma fin_entry_independent_src_of_fin_good : forall cfg SRC TGT,
  image_brk_satisfiable (img_segments TGT) = true ->
  fin_good cfg SRC TGT ->
  fin_entry_independent cfg SRC source_alloc_limit.
Proof.
  intros cfg SRC TGT Hwf Hg f Hf en1 en2 H1 H2 tr.
  destruct (image_brk_satisfiable_entry TGT (to_proc_input f) Hf Hwf) as [ent Hent].
  destruct (Hg f Hf en1 ent H1 Hent) as (_ & _ & Htr1).
  destruct (Hg f Hf en2 ent H2 Hent) as (_ & _ & Htr2).
  split; intros Hin.
  - apply (proj2 (Htr2 tr)). apply (proj1 (Htr1 tr)). exact Hin.
  - apply (proj2 (Htr1 tr)). apply (proj1 (Htr2 tr)). exact Hin.
Qed.

Lemma fin_entry_independent_tgt_of_fin_good : forall cfg SRC TGT,
  image_brk_satisfiable (img_segments SRC) = true ->
  fin_good cfg SRC TGT ->
  fin_entry_independent cfg TGT target_alloc_limit.
Proof.
  intros cfg SRC TGT Hwf Hg f Hf en1 en2 H1 H2 tr.
  destruct (image_brk_satisfiable_entry SRC (to_proc_input f) Hf Hwf) as [ens Hens].
  destruct (Hg f Hf ens en1 Hens H1) as (_ & _ & Htr1).
  destruct (Hg f Hf ens en2 Hens H2) as (_ & _ & Htr2).
  split; intros Hin.
  - apply (proj1 (Htr2 tr)). apply (proj2 (Htr1 tr)). exact Hin.
  - apply (proj1 (Htr1 tr)). apply (proj2 (Htr2 tr)). exact Hin.
Qed.

(* [comment removed for export] *)
Lemma fin_entry_independent_of_traces_eq : forall cfg X lim (T : ProcInput -> list event -> Prop),
  (forall f en, valid_fin_input f -> valid_entry X en (to_proc_input f) ->
     trace_equiv (bh_traces (run_scfg cfg X lim en (to_proc_input f))) (T (to_proc_input f))) ->
  fin_entry_independent cfg X lim.
Proof.
  intros cfg X lim T H f Hf en1 en2 H1 H2 tr.
  pose proof (H f en1 Hf H1 tr) as E1. pose proof (H f en2 Hf H2 tr) as E2.
  split; intros Hin.
  - apply (proj2 E2). apply (proj1 E1). exact Hin.
  - apply (proj2 E1). apply (proj1 E2). exact Hin.
Qed.

(* [comment removed for export] *)
Lemma fin_good_of_traces_eq : forall cfg SRC TGT (T : ProcInput -> list event -> Prop),
  (forall f en, valid_fin_input f -> valid_entry SRC en (to_proc_input f) ->
     error_free (run_scfg cfg SRC source_alloc_limit en (to_proc_input f))
     /\ trace_equiv (bh_traces (run_scfg cfg SRC source_alloc_limit en (to_proc_input f))) (T (to_proc_input f))) ->
  (forall f en, valid_fin_input f -> valid_entry TGT en (to_proc_input f) ->
     error_free (run_scfg cfg TGT target_alloc_limit en (to_proc_input f))
     /\ trace_equiv (bh_traces (run_scfg cfg TGT target_alloc_limit en (to_proc_input f))) (T (to_proc_input f))) ->
  fin_good cfg SRC TGT.
Proof.
  intros cfg SRC TGT T HS HT f Hf en1 en2 H1 H2.
  destruct (HS f en1 Hf H1) as [Hes Hts]. destruct (HT f en2 Hf H2) as [Het Htt].
  split; [exact Hes | split; [exact Het |]].
  intros tr. split; intros Hin.
  - apply (proj2 (Htt tr)). apply (proj1 (Hts tr)). exact Hin.
  - apply (proj2 (Hts tr)). apply (proj1 (Htt tr)). exact Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma agree_s_self_iff : forall cfg X lim inp,
  agree_s cfg X X lim inp <-> entry_independent_s cfg X lim inp.
Proof.
  intros cfg X lim inp. unfold agree_s, entry_independent_s. split.
  - intros (H & _). exact H.
  - intros H. split; [exact H |]. split; [| split]; split; intros Hx; exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ca_iff_of_fin_good : forall cfg SRC TGT C,
  always_accepts C -> fin_good cfg SRC TGT ->
  classifies_good_inputs_T_s cfg SRC TGT C.
Proof.
  intros cfg SRC TGT C Hacc Hg. unfold classifies_good_inputs_T_s.
  exact (decides_fo_of_always_accepts C _ Hacc Hg).
Qed.

Theorem ca_iff_of_pinned : forall cfg SRC TGT C,
  always_accepts C -> strong_universal_error_free_T_scfg cfg SRC TGT ->
  classifies_good_inputs_T_s cfg SRC TGT C.
Proof. intros cfg SRC TGT C Hacc Hb. exact (ca_iff_of_fin_good _ _ _ _ Hacc (fin_good_of_pinned _ _ _ Hb)). Qed.

Theorem ca_iff_of_budgets : forall cfg SRC TGT C,
  always_accepts C ->
  strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target SRC TGT ->
  fin_never_refused cfg SRC ->
  classifies_good_inputs_T_s cfg SRC TGT C.
Proof.
  intros cfg SRC TGT C Hacc Hb Hn. exact (ca_iff_of_fin_good _ _ _ _ Hacc (fin_good_of_budgets _ _ _ Hb Hn)).
Qed.

(* [comment removed for export] *)
Theorem ca_iff_necessary : forall cfg SRC TGT C,
  image_brk_satisfiable (img_segments C) = true ->
  always_accepts C ->
  classifies_good_inputs_T_s cfg SRC TGT C ->
  fin_good cfg SRC TGT.
Proof.
  intros cfg SRC TGT C Hwf Hacc Hrow.
  exact (decides_fo_always_accepts_necessary C _ Hwf Hacc Hrow).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem cb_iff_of_entry_independent : forall cfg SRC TGT C,
  always_accepts C ->
  fin_entry_independent cfg SRC source_alloc_limit ->
  fin_entry_independent cfg TGT target_alloc_limit ->
  classifies_patch_diff_T_s cfg SRC SRC TGT TGT C.
Proof.
  intros cfg SRC TGT C Hacc HS HT. unfold classifies_patch_diff_T_s.
  apply (decides_fo_of_always_accepts C _ Hacc).
  intros f Hf. split; apply agree_s_self_iff; [exact (HS f Hf) | exact (HT f Hf)].
Qed.

Theorem cb_iff_of_fin_good : forall cfg SRC TGT C,
  image_brk_satisfiable (img_segments SRC) = true ->
  image_brk_satisfiable (img_segments TGT) = true ->
  always_accepts C -> fin_good cfg SRC TGT ->
  classifies_patch_diff_T_s cfg SRC SRC TGT TGT C.
Proof.
  intros cfg SRC TGT C HwS HwT Hacc Hg.
  apply (cb_iff_of_entry_independent _ _ _ _ Hacc).
  - exact (fin_entry_independent_src_of_fin_good _ _ _ HwT Hg).
  - exact (fin_entry_independent_tgt_of_fin_good _ _ _ HwS Hg).
Qed.

Theorem cb_iff_of_pinned : forall cfg SRC TGT C,
  image_brk_satisfiable (img_segments SRC) = true ->
  image_brk_satisfiable (img_segments TGT) = true ->
  always_accepts C -> strong_universal_error_free_T_scfg cfg SRC TGT ->
  classifies_patch_diff_T_s cfg SRC SRC TGT TGT C.
Proof.
  intros cfg SRC TGT C HwS HwT Hacc Hb.
  exact (cb_iff_of_fin_good _ _ _ _ HwS HwT Hacc (fin_good_of_pinned _ _ _ Hb)).
Qed.

Theorem cb_iff_of_budgets : forall cfg SRC TGT C,
  image_brk_satisfiable (img_segments SRC) = true ->
  image_brk_satisfiable (img_segments TGT) = true ->
  always_accepts C ->
  strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target SRC TGT ->
  fin_never_refused cfg SRC ->
  classifies_patch_diff_T_s cfg SRC SRC TGT TGT C.
Proof.
  intros cfg SRC TGT C HwS HwT Hacc Hb Hn.
  exact (cb_iff_of_fin_good _ _ _ _ HwS HwT Hacc (fin_good_of_budgets _ _ _ Hb Hn)).
Qed.

(* [comment removed for export] *)
Theorem cb_iff_necessary : forall cfg SRC TGT C,
  image_brk_satisfiable (img_segments C) = true ->
  always_accepts C ->
  classifies_patch_diff_T_s cfg SRC SRC TGT TGT C ->
  fin_entry_independent cfg SRC source_alloc_limit /\ fin_entry_independent cfg TGT target_alloc_limit.
Proof.
  intros cfg SRC TGT C Hwf Hacc Hrow.
  pose proof (decides_fo_always_accepts_necessary C _ Hwf Hacc Hrow) as H.
  split; intros f Hf; apply agree_s_self_iff; [exact (proj1 (H f Hf)) | exact (proj2 (H f Hf))].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition realizes_T (cfg : SpuriousCfg) (X : Image) (lim : Z) (T : ProcInput -> list event -> Prop) : Prop :=
  forall inp en, valid_input inp -> valid_entry X en inp ->
    error_free (run_scfg cfg X lim en inp)
    /\ trace_equiv (bh_traces (run_scfg cfg X lim en inp)) (T inp).

(* [comment removed for export] *)
Theorem pinned_of_realizes_T : forall cfg SRC TGT T,
  realizes_T cfg SRC source_alloc_limit T ->
  realizes_T cfg TGT target_alloc_limit T ->
  strong_universal_error_free_T_scfg cfg SRC TGT.
Proof.
  intros cfg SRC TGT T HS HT en1 en2 inp H1 H2 Hv.
  destruct (HS inp en1 Hv H1) as [Hes Hts]. destruct (HT inp en2 Hv H2) as [Het Htt].
  split; [exact Hes | split; [exact Het |]].
  intros tr. split; intros Hin.
  - apply (proj2 (Htt tr)). apply (proj1 (Hts tr)). exact Hin.
  - apply (proj2 (Hts tr)). apply (proj1 (Htt tr)). exact Hin.
Qed.

Lemma fin_entry_independent_of_realizes_T : forall cfg X lim T,
  realizes_T cfg X lim T -> fin_entry_independent cfg X lim.
Proof.
  intros cfg X lim T H. apply (fin_entry_independent_of_traces_eq cfg X lim T).
  intros f en Hf Hen. exact (proj2 (H (to_proc_input f) en Hf Hen)).
Qed.

(* [comment removed for export] *)
Theorem pair_of_realizes_T : forall cfg SRC TGT CA CB T,
  always_accepts CA -> always_accepts CB ->
  realizes_T cfg SRC source_alloc_limit T ->
  realizes_T cfg TGT target_alloc_limit T ->
  strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target SRC TGT
  /\ classifier_total_T_fo CA
  /\ classifies_good_inputs_T_s cfg SRC TGT CA
  /\ classifier_total_T_fo CB
  /\ classifies_patch_diff_T_s cfg SRC SRC TGT TGT CB.
Proof.
  intros cfg SRC TGT CA CB T HA HB HS HT.
  pose proof (pinned_of_realizes_T cfg SRC TGT T HS HT) as Hp.
  split; [exact (strong_universal_error_free_T_scfg_budgets_of_scfg cfg SRC TGT Hp) |].
  split; [exact (total_of_always_accepts CA HA) |].
  split; [exact (ca_iff_of_pinned cfg SRC TGT CA HA Hp) |].
  split; [exact (total_of_always_accepts CB HB) |].
  exact (cb_iff_of_entry_independent cfg SRC TGT CB HB
           (fin_entry_independent_of_realizes_T cfg SRC _ T HS)
           (fin_entry_independent_of_realizes_T cfg TGT _ T HT)).
Qed.

(* [comment removed for export] *)
Theorem issued_base_of_pinned : forall cfg SRC TGT,
  strong_universal_error_free_T_scfg cfg SRC TGT ->
  strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target SRC TGT.
Proof. intros cfg SRC TGT H. exact (strong_universal_error_free_T_scfg_budgets_of_scfg cfg SRC TGT H). Qed.
