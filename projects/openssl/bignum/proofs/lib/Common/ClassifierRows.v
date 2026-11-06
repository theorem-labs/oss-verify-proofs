(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition accepts_all (C : Image) : Prop :=
  forall f, valid_fin_input f -> forall en,
    valid_entry C en (to_proc_input f) ->
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f).

Definition rejects_all (C : Image) : Prop :=
  forall f, valid_fin_input f -> forall en,
    valid_entry C en (to_proc_input f) ->
    must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f).

Lemma total_of_accepts_all : forall C, accepts_all C -> classifier_total_T_fo C.
Proof. intros C H f Hf en Hve. left. exact (H f Hf en Hve). Qed.

Lemma decides_true_of_accepts_all : forall C (spec : ProcInput -> Prop),
  accepts_all C ->
  (forall f, valid_fin_input f -> spec (to_proc_input f)) ->
  decides_fo C spec.
Proof.
  intros C spec H Hspec f Hf en Hve. split.
  - split; [intros _; exact (Hspec f Hf) | intros _; exact (H f Hf en Hve)].
  - left. exact (H f Hf en Hve).
Qed.

Lemma good_input_s_of_base : forall cfg O1 O2,
  strong_universal_error_free_T_scfg cfg O1 O2 ->
  forall inp, valid_input inp -> good_input_s cfg O1 O2 inp.
Proof.
  intros cfg O1 O2 T inp Hinp en1 en2 H1 H2. exact (T en1 en2 inp H1 H2 Hinp).
Qed.

Lemma ca_iff_of_base : forall cfg O1 O2 C,
  strong_universal_error_free_T_scfg cfg O1 O2 ->
  accepts_all C ->
  classifies_good_inputs_T_s cfg O1 O2 C.
Proof.
  intros cfg O1 O2 C T HC. unfold classifies_good_inputs_T_s.
  apply decides_true_of_accepts_all; [exact HC|].
  intros f Hf. exact (good_input_s_of_base cfg O1 O2 T _ Hf).
Qed.

Lemma trace_equiv_sym : forall T1 T2, trace_equiv T1 T2 -> trace_equiv T2 T1.
Proof. intros T1 T2 H t. specialize (H t). tauto. Qed.

Lemma trace_equiv_trans : forall T1 T2 T3,
  trace_equiv T1 T2 -> trace_equiv T2 T3 -> trace_equiv T1 T3.
Proof. intros T1 T2 T3 H12 H23 t. specialize (H12 t). specialize (H23 t). tauto. Qed.

Lemma agree_s_self : forall cfg X lim inp,
  (forall en en', valid_entry X en inp -> valid_entry X en' inp ->
     trace_equiv (bh_traces (run_scfg cfg X lim en inp)) (bh_traces (run_scfg cfg X lim en' inp))) ->
  agree_s cfg X X lim inp.
Proof.
  intros cfg X lim inp H. split; [exact H|]. split; [tauto|]. split; tauto.
Qed.

Lemma cb_spec_of_base : forall cfg O1 O2,
  strong_universal_error_free_T_scfg cfg O1 O2 ->
  image_brk_satisfiable (img_segments O1) = true ->
  image_brk_satisfiable (img_segments O2) = true ->
  forall inp, valid_input inp ->
    agree_s cfg O1 O1 source_alloc_limit inp /\ agree_s cfg O2 O2 target_alloc_limit inp.
Proof.
  intros cfg O1 O2 T Hb1 Hb2 inp Hinp.
  destruct (image_brk_satisfiable_entry O1 inp Hinp Hb1) as [e1 He1].
  destruct (image_brk_satisfiable_entry O2 inp Hinp Hb2) as [e2 He2]. split.
  - apply agree_s_self. intros en en' Hen Hen'.
    destruct (T en e2 inp Hen He2 Hinp) as (_ & _ & A).
    destruct (T en' e2 inp Hen' He2 Hinp) as (_ & _ & B).
    exact (trace_equiv_trans _ _ _ A (trace_equiv_sym _ _ B)).
  - apply agree_s_self. intros en en' Hen Hen'.
    destruct (T e1 en inp He1 Hen Hinp) as (_ & _ & A).
    destruct (T e1 en' inp He1 Hen' Hinp) as (_ & _ & B).
    exact (trace_equiv_trans _ _ _ (trace_equiv_sym _ _ A) B).
Qed.

Lemma cb_iff_of_base : forall cfg O1 O2 C,
  strong_universal_error_free_T_scfg cfg O1 O2 ->
  image_brk_satisfiable (img_segments O1) = true ->
  image_brk_satisfiable (img_segments O2) = true ->
  accepts_all C ->
  classifies_patch_diff_T_s cfg O1 O1 O2 O2 C.
Proof.
  intros cfg O1 O2 C T H1 H2 HC. unfold classifies_patch_diff_T_s.
  apply decides_true_of_accepts_all; [exact HC|].
  intros f Hf. exact (cb_spec_of_base cfg O1 O2 T H1 H2 _ Hf).
Qed.

Lemma cb_iff_of_base_eq : forall cfg O1 O2 O1' O2' C,
  O1' = O1 -> O2' = O2 ->
  strong_universal_error_free_T_scfg cfg O1 O2 ->
  image_brk_satisfiable (img_segments O1) = true ->
  image_brk_satisfiable (img_segments O2) = true ->
  accepts_all C ->
  classifies_patch_diff_T_s cfg O1' O1 O2' O2 C.
Proof.
  intros cfg O1 O2 O1' O2' C -> -> T H1 H2 HC. exact (cb_iff_of_base cfg O1 O2 C T H1 H2 HC).
Qed.

Lemma ca_iff_of_base_eq : forall cfg O1 O2 O1' O2' C,
  O1' = O1 -> O2' = O2 ->
  strong_universal_error_free_T_scfg cfg O1 O2 ->
  accepts_all C ->
  classifies_good_inputs_T_s cfg O1' O2' C.
Proof.
  intros cfg O1 O2 O1' O2' C -> -> T HC. exact (ca_iff_of_base cfg O1 O2 C T HC).
Qed.

