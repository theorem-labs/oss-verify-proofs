(** it answers yes on every
    input.  For such an image the classifier rows follow from one fact about
    the image, [accepts_all C], and, for the rows that name builds, from the
    agreement of those builds:

    - totality, with two answers ([classifier_total]) and with three
      ([classifier_total3]);
    - every bound is 0: the rejects bound ([classifier_rejects_at_most]) and
      the maybe bound ([maybe_at_most]), and the maybe set is empty
      ([maybe_empty]);
    - classifier A decides, and is sound for, agreement of its two builds
      ([classifies], [classifies_good_inputs_sound]), from that agreement;
    - classifier B decides, and is sound for, agreement of each published
      build with its original ([classifies_patch_diff],
      [classifies_patch_diff_sound]), in two forms: with no patch (each
      original IS its published build), from the agreement of the pair; and
      with unpatched originals, from the hypothesis that each published build
      agrees with its original on every valid input.

    Every shape is the one of theories/Shapes.v or theories/ClassifierShapes.v
    (the frozen A1 shapes), applied to any image [C].  The fact
    [accepts_all C] for a given image is NOT proved here: it is a walk of
    that image's start-up to its [_Exit(0)], or an equality with an image
    whose walk is done.  No axiom, no parameter, no unfinished proof. *)
From Stdlib Require Import ZArith QArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit FinInput Classifier Measure.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.OSSV Require Import Images Shapes ClassifierShapes.
Import ListNotations.

(** [accepts_all C]: on every valid finite input, from every valid entry,
    every run of [C] exits 0. *)
Definition accepts_all (C : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en : ExecEntry,
      valid_entry C en (to_proc_input f) ->
      must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f).

(** ** 1. The classifier is total *)

Lemma total_of_accepts_all : forall C, accepts_all C -> classifier_total C.
Proof. intros C H f Hf en Hen. left. exact (H f Hf en Hen). Qed.

Lemma total3_of_accepts_all : forall C, accepts_all C -> classifier_total3 C.
Proof. intros C H. exact (classifier_total3_of_total C (total_of_accepts_all C H)). Qed.

(** ** 2. Every bound is 0 *)

Lemma accepts_all_accepts_fo : forall C f, accepts_all C -> valid_fin_input f -> accepts_fo C f.
Proof. intros C f H Hf en Hen. exact (H f Hf en Hen). Qed.

Lemma accepts_all_not_rejects : forall C f, accepts_all C -> ~ rejects_fo C f.
Proof. intros C f H [Hf Hna]. exact (Hna (accepts_all_accepts_fo C f H Hf)). Qed.

Lemma rejects_at_most_zero_of_accepts_all : forall C w M,
  accepts_all C -> classifier_rejects_at_most C w M 0.
Proof.
  intros C w M H l _ Hall.
  destruct l as [| f l].
  - rewrite sum_weights_nil. rewrite Qmult_0_l. apply Qle_refl.
  - exfalso. exact (accepts_all_not_rejects C f H (Hall f (or_introl eq_refl))).
Qed.

Lemma maybe_empty_of_accepts_all : forall C, accepts_all C -> maybe_empty C.
Proof.
  intros C H f (Hf & Hna & _). exact (Hna (accepts_all_accepts_fo C f H Hf)).
Qed.

Lemma maybe_at_most_zero_of_accepts_all : forall C w M,
  accepts_all C -> maybe_at_most C w M 0.
Proof. intros C w M H. exact (maybe_at_most_zero_of_empty C w M (maybe_empty_of_accepts_all C H)). Qed.

(** ** 3. The iff and sound rows *)

(** An accept-all classifier decides any property that holds on every valid
    input. *)
Lemma decides_of_accepts_all : forall C (spec : ProcInput -> Prop),
  accepts_all C ->
  (forall f, valid_fin_input f -> spec (to_proc_input f)) ->
  decides_fo C spec.
Proof.
  intros C spec H Hspec f Hf en Hen. split.
  - split; [intros _; exact (Hspec f Hf) | intros _; exact (H f Hf en Hen)].
  - left. exact (H f Hf en Hen).
Qed.

(** *** Classifier A: its two builds agree *)

Lemma good_input_of_base : forall env O1 O2,
  strong_universal_error_free_T_scfg env O1 O2 ->
  forall f, valid_fin_input f -> good_input_s env O1 O2 (to_proc_input f).
Proof. intros env O1 O2 T f Hf en1 en2 H1 H2. exact (T en1 en2 (to_proc_input f) H1 H2 Hf). Qed.

Lemma classifies_of_accepts_all : forall env O1 O2 C,
  strong_universal_error_free_T_scfg env O1 O2 ->
  accepts_all C ->
  classifies env O1 O2 C.
Proof.
  intros env O1 O2 C T H. rewrite classifies_is_lps. unfold classifies_good_inputs_T_s.
  exact (decides_of_accepts_all C _ H (good_input_of_base env O1 O2 T)).
Qed.

Lemma classifies_good_inputs_sound_of_accepts_all : forall env O1 O2 C,
  strong_universal_error_free_T_scfg env O1 O2 ->
  accepts_all C ->
  classifies_good_inputs_sound env O1 O2 C.
Proof.
  intros env O1 O2 C T H.
  exact (classifies_good_inputs_sound_of_classifies env O1 O2 C (classifies_of_accepts_all env O1 O2 C T H)).
Qed.

(** *** Classifier B, with unpatched originals: from the agreement of each
    published build with its original on every valid input *)

Lemma classifies_patch_diff_of_accepts_all : forall env O1 P1 O2 P2 C,
  (forall f, valid_fin_input f ->
     agree_s env O1 P1 source_alloc_limit (to_proc_input f)
     /\ agree_s env O2 P2 target_alloc_limit (to_proc_input f)) ->
  accepts_all C ->
  classifies_patch_diff env O1 P1 O2 P2 C.
Proof.
  intros env O1 P1 O2 P2 C Hag H. rewrite classifies_patch_diff_is_lps.
  unfold classifies_patch_diff_T_s.
  exact (decides_of_accepts_all C _ H Hag).
Qed.

Lemma classifies_patch_diff_sound_of_accepts_all : forall env O1 P1 O2 P2 C,
  (forall f, valid_fin_input f ->
     agree_s env O1 P1 source_alloc_limit (to_proc_input f)
     /\ agree_s env O2 P2 target_alloc_limit (to_proc_input f)) ->
  accepts_all C ->
  classifies_patch_diff_sound env O1 P1 O2 P2 C.
Proof.
  intros env O1 P1 O2 P2 C Hag H.
  exact (classifies_patch_diff_sound_of_exact env O1 P1 O2 P2 C
           (classifies_patch_diff_of_accepts_all env O1 P1 O2 P2 C Hag H)).
Qed.

(** *** Classifier B, with no patch: each original IS its published build,
    and each build agrees with itself, from the agreement of the pair *)

Lemma trace_equiv_trans_sym : forall T1 T2 T3,
  trace_equiv T1 T2 -> trace_equiv T3 T2 -> trace_equiv T1 T3.
Proof. intros T1 T2 T3 H12 H32 t. specialize (H12 t). specialize (H32 t). tauto. Qed.

Lemma trace_equiv_sym_trans : forall T1 T2 T3,
  trace_equiv T2 T1 -> trace_equiv T2 T3 -> trace_equiv T1 T3.
Proof. intros T1 T2 T3 H21 H23 t. specialize (H21 t). specialize (H23 t). tauto. Qed.

Lemma agree_s_self_of : forall env X lim inp,
  (forall en en', valid_entry X en inp -> valid_entry X en' inp ->
     trace_equiv (bh_traces (run_scfg env X lim en inp)) (bh_traces (run_scfg env X lim en' inp))) ->
  agree_s env X X lim inp.
Proof. intros env X lim inp H. split; [exact H |]. split; [tauto |]. split; tauto. Qed.

Lemma self_agreement_of_base : forall env P1 P2,
  strong_universal_error_free_T_scfg env P1 P2 ->
  image_brk_satisfiable (img_segments P1) = true ->
  image_brk_satisfiable (img_segments P2) = true ->
  forall f, valid_fin_input f ->
    agree_s env P1 P1 source_alloc_limit (to_proc_input f)
    /\ agree_s env P2 P2 target_alloc_limit (to_proc_input f).
Proof.
  intros env P1 P2 T Hb1 Hb2 f Hf.
  destruct (image_brk_satisfiable_entry P1 (to_proc_input f) Hf Hb1) as [e1 He1].
  destruct (image_brk_satisfiable_entry P2 (to_proc_input f) Hf Hb2) as [e2 He2]. split.
  - apply agree_s_self_of. intros en en' Hen Hen'.
    destruct (T en e2 (to_proc_input f) Hen He2 Hf) as (_ & _ & A).
    destruct (T en' e2 (to_proc_input f) Hen' He2 Hf) as (_ & _ & B).
    exact (trace_equiv_trans_sym _ _ _ A B).
  - apply agree_s_self_of. intros en en' Hen Hen'.
    destruct (T e1 en (to_proc_input f) He1 Hen Hf) as (_ & _ & A).
    destruct (T e1 en' (to_proc_input f) He1 Hen' Hf) as (_ & _ & B).
    exact (trace_equiv_sym_trans _ _ _ A B).
Qed.

Lemma classifies_patch_diff_of_accepts_all_nopatch : forall env P1 P2 C,
  strong_universal_error_free_T_scfg env P1 P2 ->
  image_brk_satisfiable (img_segments P1) = true ->
  image_brk_satisfiable (img_segments P2) = true ->
  accepts_all C ->
  classifies_patch_diff env P1 P1 P2 P2 C.
Proof.
  intros env P1 P2 C T Hb1 Hb2 H.
  exact (classifies_patch_diff_of_accepts_all env P1 P1 P2 P2 C (self_agreement_of_base env P1 P2 T Hb1 Hb2) H).
Qed.

Lemma classifies_patch_diff_sound_of_accepts_all_nopatch : forall env P1 P2 C,
  strong_universal_error_free_T_scfg env P1 P2 ->
  image_brk_satisfiable (img_segments P1) = true ->
  image_brk_satisfiable (img_segments P2) = true ->
  accepts_all C ->
  classifies_patch_diff_sound env P1 P1 P2 P2 C.
Proof.
  intros env P1 P2 C T Hb1 Hb2 H.
  exact (classifies_patch_diff_sound_of_accepts_all env P1 P1 P2 P2 C
           (self_agreement_of_base env P1 P2 T Hb1 Hb2) H).
Qed.

(** ** Planted negatives: the conclusions need [accepts_all]; a reject-all
    hypothesis, or a swapped argument, does not type-check *)

Definition rejects_all (C : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en : ExecEntry,
      valid_entry C en (to_proc_input f) ->
      must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f).

Section Negatives.
  Variables (C O1 P1 O2 P2 : Image) (env : SpuriousCfg) (w : FinProcInput -> Q) (M : Q).
  Hypothesis Hrej : rejects_all C.
  Fail Check (rejects_at_most_zero_of_accepts_all C w M Hrej).
  Fail Check (maybe_empty_of_accepts_all C Hrej).
  Hypothesis Hacc : accepts_all C.
  Hypothesis Hag : forall f, valid_fin_input f ->
     agree_s env O1 P1 source_alloc_limit (to_proc_input f)
     /\ agree_s env O2 P2 target_alloc_limit (to_proc_input f).
  (* the argument order is O1 P1 O2 P2: the original first, then its published build *)
  Check (classifies_patch_diff_of_accepts_all env O1 P1 O2 P2 C Hag Hacc : classifies_patch_diff env O1 P1 O2 P2 C).
  Fail Check (classifies_patch_diff_of_accepts_all env O1 P1 O2 P2 C Hag Hacc : classifies_patch_diff env P1 O1 O2 P2 C).
  Fail Check (classifies_patch_diff_of_accepts_all env O1 P1 O2 P2 C Hag Hacc : classifies_patch_diff env O2 P2 O1 P1 C).
End Negatives.

(** ** The conclusions are the frozen shapes, and no axiom is used *)
Print Assumptions total3_of_accepts_all.
Print Assumptions rejects_at_most_zero_of_accepts_all.
Print Assumptions maybe_at_most_zero_of_accepts_all.
Print Assumptions classifies_of_accepts_all.
Print Assumptions classifies_good_inputs_sound_of_accepts_all.
Print Assumptions classifies_patch_diff_sound_of_accepts_all.
Print Assumptions classifies_patch_diff_sound_of_accepts_all_nopatch.
