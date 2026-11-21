(** * OSSVerify.Core.ClassifierShapes: the statements about a named classifier

    theories/Shapes.v leaves the classifier open: [agreement_decidable] says
    that SOME program decides the agreeing inputs, and a harness's
    Characterise.v states [classifies] and [classifier_rejects_at_most] for
    any program [C] as definitions, not claims.  A classifier statement
    names ONE program, a published riscv64 binary of the harness, and makes
    a claim about it (docs/statements.md, "Classifier statements").

    A classifier answers yes, no or maybe: it exits 0 for yes, 1 for no and
    2 for maybe.  A crash, a hang or another exit code is not an answer.
    At one valid entry, an answer is an exit code that every run there
    gives.  This is the form the project owner decided on 2026-11-03 (the tracker, approved
    spec version 23).  Each pair of builds has two classifiers, A and B, and
    these statements about them:
    - each always answers ([classifier_total3]);
    - each is sound: a yes means the property holds, and where the property
      holds the answer is never no ([classifies_good_inputs_sound] for A,
      [classifies_patch_diff_sound] for B);
    - the inputs on which it gives no firm answer weigh at most [b]
      ([maybe_at_most]), or, with no input distribution, there are none
      ([maybe_empty]);
    - the inputs it does not accept weigh at most [b]
      ([Shapes.classifier_rejects_at_most], which counts no and maybe).
    A's property is that the two ORIGINALS agree, the builds of the pair
    without the patches ([Shapes.good_input]); B's is that each published
    build agrees with its original ([Classifier.agree_s]).

    THESE SHAPES ARE COPIES.  the tracker added these definitions to
    linux-process-semantics (lps) at commit
    (theories/EquivalenceDefinition/
    Classifier.v and Measure.v).  The lps that this release pins
    (release.yaml semantics) does not have those names yet.  So this file
    carries their text VERBATIM, in module [LpsBet618] at the end, and
    proves each shape equal to its copy by [reflexivity] ([_is_copy]).
    [oft lint] checks that the copy is still byte for byte the text of
    (rules.py, LPS_BET618_COPY), so a change to either cannot pass
    unseen.

    FOLLOW-UP, named so it is not lost: when release.yaml pins an lps that
    has these names, give each shape an [_is_lps] lemma proved by
    [reflexivity] against the lps name, as the shapes of Shapes.v have;
    then remove [LpsBet618], the [_is_copy] lemmas and the lint pin.

    The exact forms come first ([classifier_total] and
    [classifies_patch_diff], with Shapes.v's [classifies]): a proof of an
    exact statement proves each new statement, with a maybe bound of 0, by
    the lemmas at the end of this file, which use no axiom.

    Shapes.v holds the shapes of the other statements, and its code enters
    their fingerprints; this file's code enters the fingerprints of the
    classifier statements alone.  It declares no axiom or parameter and
    leaves no proof unfinished. *)
From Stdlib Require Import ZArith QArith List.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit FinInput Classifier Measure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.OSSV Require Import Images Shapes.
Import ListNotations.

(** ** The exact forms

    Two answers, decided exactly.  No statement of this release is stated
    in these forms; they are here for the bridges at the end. *)

(** [classifier_total C]: on every valid finite input, from every valid
    entry, every execution of [C] exits 0, or every execution exits 1. *)
Definition classifier_total (C : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en : ExecEntry,
      valid_entry C en (to_proc_input f) ->
      must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
      \/ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f).

Lemma classifier_total_is_lps : forall C,
  classifier_total C = LinuxProcessSemantics.EquivalenceDefinition.Classifier.classifier_total_T_fo C.
Proof. reflexivity. Qed.

(** [classifies_patch_diff env plain_o plain san_o san C]: [C] decides
    exactly the inputs on which both published builds agree with their
    originals: it exits 0 if they do and 1 if they do not. *)
Definition classifies_patch_diff (env : SpuriousCfg) (plain_o plain san_o san C : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en : ExecEntry,
      valid_entry C en (to_proc_input f) ->
      (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en
         (to_proc_input f)
       <-> agree_s env plain_o plain source_alloc_limit (to_proc_input f)
           /\ agree_s env san_o san target_alloc_limit (to_proc_input f))
      /\ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en
            (to_proc_input f)
          \/ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en
               (to_proc_input f)).

Lemma classifies_patch_diff_is_lps : forall env plain_o plain san_o san C,
  classifies_patch_diff env plain_o plain san_o san C
  = LinuxProcessSemantics.EquivalenceDefinition.Classifier.classifies_patch_diff_T_s
      env plain_o plain san_o san C.
Proof. reflexivity. Qed.

(** ** Yes, no or maybe *)

(** The maybe exit code, exit(2), written plain, as [verdict_accept] is.
    lps: [Classifier.verdict_maybe]. *)
Definition verdict_maybe : word := Z_to_bv 64 2.

(** Totality with three answers: on every valid finite input, at every
    valid entry, every run of [C] exits 0, every run exits 1, or every run
    exits 2.  lps: [Classifier.classifier_total3_T_fo]. *)
Definition classifier_total3 (C : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry C en (to_proc_input f) ->
      must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
      \/ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f)
      \/ must_exit_with_scfg forced_only_cfg verdict_maybe C classifier_alloc_limit en (to_proc_input f).

(** No at every valid entry.  lps: [Classifier.says_no_fo]. *)
Definition says_no (C : Image) (f : FinProcInput) : Prop :=
  forall en,
    valid_entry C en (to_proc_input f) ->
    must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f).

(** The maybe set: the valid finite inputs that get neither yes at every
    valid entry ([Classifier.accepts_fo]) nor no at every valid entry.  A
    crash, a hang and mixed answers put an input here too.  lps:
    [Classifier.maybe_fo]. *)
Definition maybe_input (C : Image) (f : FinProcInput) : Prop :=
  valid_fin_input f /\ ~ accepts_fo C f /\ ~ says_no C f.

(** Soundness: on every valid finite input, at every valid entry, a yes
    means that the input has the property, and an input that has the
    property never gets a no.  lps: [Classifier.sound_fo]. *)
Definition sound (C : Image) (spec : ProcInput -> Prop) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry C en (to_proc_input f) ->
      (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
       -> spec (to_proc_input f))
      /\ (spec (to_proc_input f)
          -> ~ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f)).

(** Classifier A is sound for agreement of the two originals.  lps:
    [Classifier.classifies_good_inputs_sound_T_s]. *)
Definition classifies_good_inputs_sound (env : SpuriousCfg) (plain_o san_o C : Image) : Prop :=
  sound C (good_input_s env plain_o san_o).

(** Classifier B is sound for agreement of each published build with its
    original.  lps: [Classifier.classifies_patch_diff_sound_T_s]. *)
Definition classifies_patch_diff_sound (env : SpuriousCfg) (plain_o plain san_o san C : Image) : Prop :=
  sound C (fun inp => agree_s env plain_o plain source_alloc_limit inp
                      /\ agree_s env san_o san target_alloc_limit inp).

(** With no input distribution: no valid input is a maybe input.  lps:
    [Classifier.maybe_empty_T_fo]. *)
Definition maybe_empty (C : Image) : Prop := forall f, ~ maybe_input C f.

(** With an input distribution [w] of total [M]: the maybe inputs weigh at
    most [b] of [M], counted over every list of them whose cores are
    distinct.  lps: [Measure.maybe_bound_T_fo]. *)
Definition maybe_at_most (C : Image) (w : FinProcInput -> Q) (M b : Q) : Prop :=
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (forall f, In f l -> maybe_input C f) ->
    (sum_weights w l <= b * M)%Q.

(** ** From the exact forms to yes, no or maybe

    A proof of an exact statement proves the new ones, with a maybe bound
    of 0.  None of these lemmas uses an axiom. *)

Lemma classifier_total3_of_total : forall C, classifier_total C -> classifier_total3 C.
Proof.
  intros C H f Hf en Hen.
  destruct (H f Hf en Hen) as [H0 | H1]; [left; exact H0 | right; left; exact H1].
Qed.

(** A decider is sound.  lps: [Classifier.sound_fo_of_decides_fo]. *)
Lemma sound_of_decides : forall C spec, decides_fo C spec -> sound C spec.
Proof.
  intros C spec H f Hf en Hen.
  destruct (H f Hf en Hen) as [Hiff _].
  split.
  - exact (proj1 Hiff).
  - intros Hs Hno.
    exact (verdict_accept_neq_reject
             (must_exit_with_scfg_exclusive _ _ _ _ _ _ _ (proj2 Hiff Hs) Hno)).
Qed.

(** A decider has no maybe input.  lps:
    [Classifier.maybe_empty_T_fo_of_decides_fo]. *)
Lemma maybe_empty_of_decides : forall C spec, decides_fo C spec -> maybe_empty C.
Proof.
  intros C spec H f (Hf & Hna & Hnn).
  assert (Hns : ~ spec (to_proc_input f)).
  { intros Hs. apply Hna. intros en Hen. exact (proj2 (proj1 (H f Hf en Hen)) Hs). }
  apply Hnn. intros en Hen.
  destruct (H f Hf en Hen) as [Hiff [H0 | H1]].
  - exfalso. exact (Hns (proj1 Hiff H0)).
  - exact H1.
Qed.

(** An empty maybe set gives a maybe bound of 0.  lps:
    [Measure.maybe_bound_T_fo_zero_of_maybe_empty]. *)
Lemma maybe_at_most_zero_of_empty : forall C w M, maybe_empty C -> maybe_at_most C w M 0.
Proof.
  intros C w M Hempty l _ Hall.
  destruct l as [| f l].
  - rewrite sum_weights_nil. rewrite Qmult_0_l. apply Qle_refl.
  - exfalso. exact (Hempty f (Hall f (or_introl eq_refl))).
Qed.

(** The four bridges a grader applies to an exact proof of a pair. *)
Lemma classifies_good_inputs_sound_of_classifies : forall env plain_o san_o C,
  classifies env plain_o san_o C -> classifies_good_inputs_sound env plain_o san_o C.
Proof.
  intros env plain_o san_o C H. rewrite classifies_is_lps in H.
  exact (sound_of_decides C (good_input_s env plain_o san_o) H).
Qed.

Lemma maybe_empty_of_classifies : forall env plain_o san_o C,
  classifies env plain_o san_o C -> maybe_empty C.
Proof.
  intros env plain_o san_o C H. rewrite classifies_is_lps in H.
  exact (maybe_empty_of_decides C (good_input_s env plain_o san_o) H).
Qed.

Lemma classifies_patch_diff_sound_of_exact : forall env plain_o plain san_o san C,
  classifies_patch_diff env plain_o plain san_o san C
  -> classifies_patch_diff_sound env plain_o plain san_o san C.
Proof.
  intros env plain_o plain san_o san C H.
  exact (sound_of_decides C (fun inp => agree_s env plain_o plain source_alloc_limit inp
                                        /\ agree_s env san_o san target_alloc_limit inp) H).
Qed.

Lemma maybe_empty_of_classifies_patch_diff : forall env plain_o plain san_o san C,
  classifies_patch_diff env plain_o plain san_o san C -> maybe_empty C.
Proof.
  intros env plain_o plain san_o san C H.
  exact (maybe_empty_of_decides C (fun inp => agree_s env plain_o plain source_alloc_limit inp
                                              /\ agree_s env san_o san target_alloc_limit inp) H).
Qed.

(** A proof of a sound statement or of totality is about the classifier
    alone; a proof of [classifies] or [classifies_patch_diff] also proves
    [classifier_total], so it proves [classifier_total3] too. *)
Lemma classifier_total_of_classifies : forall env plain san C,
  classifies env plain san C -> classifier_total C.
Proof. intros env plain san C H f Hf en Hen. exact (proj2 (H f Hf en Hen)). Qed.

Lemma classifier_total_of_classifies_patch_diff : forall env plain_o plain san_o san C,
  classifies_patch_diff env plain_o plain san_o san C -> classifier_total C.
Proof. intros env plain_o plain san_o san C H f Hf en Hen. exact (proj2 (H f Hf en Hen)). Qed.

(** ** The lps text these shapes copy

    The definitions the tracker added to lps at commit
    , VERBATIM, out of
    theories/EquivalenceDefinition/Classifier.v and Measure.v.  Nothing in
    this repository states anything with them; they are here so that each
    shape above is proved equal to the lps text ([_is_copy]).  oft lint
    pins these bytes (rules.py, LPS_BET618_COPY).  This section goes when
    the follow-up in this file's header is done. *)
Module LpsBet618.
Definition verdict_maybe : word := Z_to_bv 64 2.

Definition classifier_total3_T_fo (Cl : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry Cl en (to_proc_input f) ->
      must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en (to_proc_input f)
      \/ must_exit_with_scfg forced_only_cfg verdict_reject Cl classifier_alloc_limit en (to_proc_input f)
      \/ must_exit_with_scfg forced_only_cfg verdict_maybe Cl classifier_alloc_limit en (to_proc_input f).

Definition says_no_fo (C : Image) (f : FinProcInput) : Prop :=
  forall en,
    valid_entry C en (to_proc_input f) ->
    must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f).

Definition maybe_fo (C : Image) (f : FinProcInput) : Prop :=
  valid_fin_input f /\ ~ accepts_fo C f /\ ~ says_no_fo C f.

Definition sound_fo (C : Image) (spec : ProcInput -> Prop) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry C en (to_proc_input f) ->
      (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
       -> spec (to_proc_input f))
      /\ (spec (to_proc_input f)
          -> ~ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f)).

Definition maybe_empty_T_fo (C : Image) : Prop := forall f, ~ maybe_fo C f.

Definition classifies_good_inputs_sound_T_s (cfg : SpuriousCfg) (O1 O2 C : Image) : Prop :=
  sound_fo C (good_input_s cfg O1 O2).

Definition classifies_patch_diff_sound_T_s (cfg : SpuriousCfg) (O1 P1 O2 P2 C : Image) : Prop :=
  sound_fo C (fun inp => agree_s cfg O1 P1 source_alloc_limit inp
                         /\ agree_s cfg O2 P2 target_alloc_limit inp).

Definition maybe_bound_T_fo (C : Image) (w : FinProcInput -> Q) (M b : Q) : Prop :=
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (forall f, In f l -> maybe_fo C f) ->
    (sum_weights w l <= b * M)%Q.
End LpsBet618.

Lemma verdict_maybe_is_copy : verdict_maybe = LpsBet618.verdict_maybe.
Proof. reflexivity. Qed.
Lemma classifier_total3_is_copy : forall C, classifier_total3 C = LpsBet618.classifier_total3_T_fo C.
Proof. reflexivity. Qed.
Lemma says_no_is_copy : forall C f, says_no C f = LpsBet618.says_no_fo C f.
Proof. reflexivity. Qed.
Lemma maybe_input_is_copy : forall C f, maybe_input C f = LpsBet618.maybe_fo C f.
Proof. reflexivity. Qed.
Lemma sound_is_copy : forall C spec, sound C spec = LpsBet618.sound_fo C spec.
Proof. reflexivity. Qed.
Lemma maybe_empty_is_copy : forall C, maybe_empty C = LpsBet618.maybe_empty_T_fo C.
Proof. reflexivity. Qed.
Lemma classifies_good_inputs_sound_is_copy : forall env O1 O2 C,
  classifies_good_inputs_sound env O1 O2 C = LpsBet618.classifies_good_inputs_sound_T_s env O1 O2 C.
Proof. reflexivity. Qed.
Lemma classifies_patch_diff_sound_is_copy : forall env O1 P1 O2 P2 C,
  classifies_patch_diff_sound env O1 P1 O2 P2 C = LpsBet618.classifies_patch_diff_sound_T_s env O1 P1 O2 P2 C.
Proof. reflexivity. Qed.
Lemma maybe_at_most_is_copy : forall C w M b, maybe_at_most C w M b = LpsBet618.maybe_bound_T_fo C w M b.
Proof. reflexivity. Qed.
