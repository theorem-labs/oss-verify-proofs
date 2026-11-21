(** * toy / ebreak: theorem statements, and the falsifiability controls on them

    SUBJECT.  [Images.plain] faults on its first instruction; [Images.asan]
    calls exit_group(0) (Images.v).  Below is one statement of each kind of
    OSSVerify.Core.Shapes, at each budget, environment, abort reading,
    machine and exit set the generator writes, and of each kind of classifier
    statement (OSSVerify.Core.ClassifierShapes), for each classifier, reading
    and originals and with and without an input distribution, in the
    generator's own words (tools/oft/shapes.py, [term], [classifier_term] and
    [templates]; the test tools/oft/tests/test_toy_controls.py requires each
    statement here to be exactly the generator's rendering, and every one of
    its choices to have one).

    Each statement without a parameter, other than the decidability ones, is
    a control: it is false for this pair, and
    tests/proofs/toy/ebreak/<statement>/Refutation.v proves so.  On one valid
    input and valid entries the plain run is never refused memory (so the
    budget premise holds) and it reaches an error.  A statement with a
    parameter (a bound [b], a classifier [C]) is controlled through the
    statement after it: the bound statements hold at no [b] below 1
    ([_below_1]), the classifier problem fails for a classifier that accepts
    every input ([_accept_all]), and the soundness of a classifier fails for
    one that always answers yes ([_accept_all]) or always no
    ([_reject_all]).  The decidability statements are true for this pair and
    are not controls (see their section). *)

From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Core Require Import Shapes ClassifierShapes.
From OSSVerify.Tests.toy.ebreak Require Images Distribution.

(** ** Halting: [halts_within_budget] at the one budget the generator uses (16 GiB, for plain, UBSan
    and ASan builds alike), at each exit set. *)
Definition plain_halts_any : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.any Images.plain.
Definition plain_halts_ok_or_refused : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.plain.
Definition plain_halts_rejected : Prop :=
  halts_within_budget Budgets.Standard.lim_source (cons (stdpp.bitvector.definitions.Z_to_bv _ 78%Z) Exits.ok_or_refused) Images.plain.

(** ** Halting: [halts_may_fail], at each exit set. *)
Definition plain_halts_may_fail_any : Prop :=
  halts_may_fail Exits.any Images.plain.
Definition plain_halts_may_fail_ok_or_refused : Prop :=
  halts_may_fail Exits.ok_or_refused Images.plain.
Definition plain_halts_may_fail_rejected : Prop :=
  halts_may_fail (cons (stdpp.bitvector.definitions.Z_to_bv _ 78%Z) Exits.ok_or_refused) Images.plain.

(** ** Agreement: each of the seven shapes, at both budget pairs ([Budgets.Standard]: 16 GiB plain;
    [Budgets.Asan]: 2 GiB plain). *)
Definition asan_agrees_standard : Prop :=
  agrees Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.asan.
Definition asan_agrees_asan : Prop :=
  agrees Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.
Definition asan_agrees_abort_modelled_standard : Prop :=
  agrees_abort_modelled Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.asan.
Definition asan_agrees_abort_modelled_asan : Prop :=
  agrees_abort_modelled Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.
Definition asan_agrees_in_standard : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.asan.
Definition asan_agrees_in_asan : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.
Definition asan_agrees_in_abort_modelled_standard : Prop :=
  agrees_in_abort_modelled Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.asan.
Definition asan_agrees_in_abort_modelled_asan : Prop :=
  agrees_in_abort_modelled Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.
Definition asan_agrees_rv64gc_standard : Prop :=
  agrees_rv64gc Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.asan.
Definition asan_agrees_rv64gc_asan : Prop :=
  agrees_rv64gc Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.
Definition asan_agrees_abort_modelled_rv64gc_standard : Prop :=
  agrees_abort_modelled_rv64gc Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.asan.
Definition asan_agrees_abort_modelled_rv64gc_asan : Prop :=
  agrees_abort_modelled_rv64gc Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.
Definition asan_agrees_in_rv64gc_standard : Prop :=
  agrees_in_rv64gc Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.asan.
Definition asan_agrees_in_rv64gc_asan : Prop :=
  agrees_in_rv64gc Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.

(** ** How often the builds disagree, in both readings and on both machines.  Each statement is
    written as the generator writes it, with its bound [b] a parameter; the control is that it holds
    at NO [b] below 1 ([_below_1], refuted). *)
Definition asan_disagrees_at_most_may_fail (b : Q) : Prop :=
  disagrees_at_most Env.may_fail Distribution.w Distribution.M Images.plain Images.asan b.
Definition asan_disagrees_at_most_may_fail_below_1 : Prop :=
  exists b : Q, (b < 1)%Q /\ asan_disagrees_at_most_may_fail b.
Definition asan_disagrees_at_most_alloc_forced_only (b : Q) : Prop :=
  disagrees_at_most Env.alloc_forced_only Distribution.w Distribution.M Images.plain Images.asan b.
Definition asan_disagrees_at_most_alloc_forced_only_below_1 : Prop :=
  exists b : Q, (b < 1)%Q /\ asan_disagrees_at_most_alloc_forced_only b.
Definition asan_disagrees_at_most_rv64gc_may_fail (b : Q) : Prop :=
  disagrees_at_most_rv64gc Env.may_fail Distribution.w Distribution.M Images.plain Images.asan b.
Definition asan_disagrees_at_most_rv64gc_may_fail_below_1 : Prop :=
  exists b : Q, (b < 1)%Q /\ asan_disagrees_at_most_rv64gc_may_fail b.
Definition asan_disagrees_at_most_rv64gc_alloc_forced_only (b : Q) : Prop :=
  disagrees_at_most_rv64gc Env.alloc_forced_only Distribution.w Distribution.M Images.plain Images.asan b.
Definition asan_disagrees_at_most_rv64gc_alloc_forced_only_below_1 : Prop :=
  exists b : Q, (b < 1)%Q /\ asan_disagrees_at_most_rv64gc_alloc_forced_only b.

(** ** The classifier problem a decidability proof solves (a harness's Characterise.v), as the
    generator writes it, for the classifier [Images.asan], which exits 0, "the builds agree", on every
    input ([_accept_all], refuted). *)
Definition asan_classifies_may_fail (C : Image) : Prop :=
  classifies Env.may_fail Images.plain Images.asan C.
Definition asan_classifies_may_fail_accept_all : Prop :=
  asan_classifies_may_fail Images.asan.
Definition asan_classifies_alloc_forced_only (C : Image) : Prop :=
  classifies Env.alloc_forced_only Images.plain Images.asan C.
Definition asan_classifies_alloc_forced_only_accept_all : Prop :=
  asan_classifies_alloc_forced_only Images.asan.
Definition asan_classifies_rv64gc_may_fail (C : Image) : Prop :=
  classifies_rv64gc Env.may_fail Images.plain Images.asan C.
Definition asan_classifies_rv64gc_may_fail_accept_all : Prop :=
  asan_classifies_rv64gc_may_fail Images.asan.
Definition asan_classifies_rv64gc_alloc_forced_only (C : Image) : Prop :=
  classifies_rv64gc Env.alloc_forced_only Images.plain Images.asan C.
Definition asan_classifies_rv64gc_alloc_forced_only_accept_all : Prop :=
  asan_classifies_rv64gc_alloc_forced_only Images.asan.

(** ** Deciding where the builds agree, as the generator writes it.  Not refuted.  The code proves
    only that the pair disagrees on one input ([ebreak_exit0_disagree_fin]); that no input agrees,
    so the program that always exits 1 decides the agreeing inputs, is believed true, not proved here.
    tests/toy/Controls.v pins the body of [agreement_decidable] to its [image_wf] and [classifies]
    conjuncts, and the [_accept_all] controls above refute [classifies] for a wrong classifier. *)
Definition asan_agreement_decidable_may_fail : Prop :=
  agreement_decidable Env.may_fail Images.plain Images.asan.
Definition asan_agreement_decidable_alloc_forced_only : Prop :=
  agreement_decidable Env.alloc_forced_only Images.plain Images.asan.
Definition asan_agreement_decidable_rv64gc_may_fail : Prop :=
  agreement_decidable_rv64gc Env.may_fail Images.plain Images.asan.
Definition asan_agreement_decidable_rv64gc_alloc_forced_only : Prop :=
  agreement_decidable_rv64gc Env.alloc_forced_only Images.plain Images.asan.

(** ** Each classifier answers yes, no or maybe, as the generator writes it, for the pair's
    classifiers [Images.classifier_a_asan] and [Images.classifier_b_asan], which give no answer: each
    is lps's ebreak image, whose one run faults (refuted). *)
Definition asan_ca_total : Prop :=
  classifier_total3 Images.classifier_a_asan.
Definition asan_cb_total : Prop :=
  classifier_total3 Images.classifier_b_asan.

(** ** Each classifier is sound, as the generator writes it, in each reading and with each
    originals ([Images.plain_original] and [Images.asan_original] are the builds' own images), with
    the classifier a parameter [C]: a classifier that gives no answer is sound for every property.
    Classifier A's property fails for [Images.always_yes], which answers yes on an input where the
    builds disagree ([_accept_all], refuted); classifier B's for [Images.always_no], which answers no
    on an input where each build agrees with its original ([_reject_all], refuted). *)
Definition asan_ca_sound_may_fail_published (C : Image) : Prop :=
  classifies_good_inputs_sound Env.may_fail Images.plain Images.asan C.
Definition asan_ca_sound_may_fail_published_accept_all : Prop :=
  asan_ca_sound_may_fail_published Images.always_yes.
Definition asan_ca_sound_may_fail_unpatched (C : Image) : Prop :=
  classifies_good_inputs_sound Env.may_fail Images.plain_original Images.asan_original C.
Definition asan_ca_sound_may_fail_unpatched_accept_all : Prop :=
  asan_ca_sound_may_fail_unpatched Images.always_yes.
Definition asan_ca_sound_alloc_forced_only_published (C : Image) : Prop :=
  classifies_good_inputs_sound Env.alloc_forced_only Images.plain Images.asan C.
Definition asan_ca_sound_alloc_forced_only_published_accept_all : Prop :=
  asan_ca_sound_alloc_forced_only_published Images.always_yes.
Definition asan_ca_sound_alloc_forced_only_unpatched (C : Image) : Prop :=
  classifies_good_inputs_sound Env.alloc_forced_only Images.plain_original Images.asan_original C.
Definition asan_ca_sound_alloc_forced_only_unpatched_accept_all : Prop :=
  asan_ca_sound_alloc_forced_only_unpatched Images.always_yes.
Definition asan_cb_sound_may_fail_published (C : Image) : Prop :=
  classifies_patch_diff_sound Env.may_fail Images.plain Images.plain Images.asan Images.asan C.
Definition asan_cb_sound_may_fail_published_reject_all : Prop :=
  asan_cb_sound_may_fail_published Images.always_no.
Definition asan_cb_sound_may_fail_unpatched (C : Image) : Prop :=
  classifies_patch_diff_sound Env.may_fail Images.plain_original Images.plain Images.asan_original Images.asan C.
Definition asan_cb_sound_may_fail_unpatched_reject_all : Prop :=
  asan_cb_sound_may_fail_unpatched Images.always_no.
Definition asan_cb_sound_alloc_forced_only_published (C : Image) : Prop :=
  classifies_patch_diff_sound Env.alloc_forced_only Images.plain Images.plain Images.asan Images.asan C.
Definition asan_cb_sound_alloc_forced_only_published_reject_all : Prop :=
  asan_cb_sound_alloc_forced_only_published Images.always_no.
Definition asan_cb_sound_alloc_forced_only_unpatched (C : Image) : Prop :=
  classifies_patch_diff_sound Env.alloc_forced_only Images.plain_original Images.plain Images.asan_original Images.asan C.
Definition asan_cb_sound_alloc_forced_only_unpatched_reject_all : Prop :=
  asan_cb_sound_alloc_forced_only_unpatched Images.always_no.

(** ** How often each classifier answers maybe, as the generator writes it with the toy distribution
    (a bound [b]; the control is that it holds at NO [b] below 1, [_below_1], refuted) and, for a
    harness with no distribution, as the empty maybe set ([_no_distribution], refuted): lps's finite
    input gets no firm answer, and it weighs the whole mass. *)
Definition asan_maybe_good (b : Q) : Prop :=
  maybe_at_most Images.classifier_a_asan Distribution.w Distribution.M b.
Definition asan_maybe_good_below_1 : Prop :=
  exists b : Q, (b < 1)%Q /\ asan_maybe_good b.
Definition asan_maybe_diff (b : Q) : Prop :=
  maybe_at_most Images.classifier_b_asan Distribution.w Distribution.M b.
Definition asan_maybe_diff_below_1 : Prop :=
  exists b : Q, (b < 1)%Q /\ asan_maybe_diff b.
Definition asan_maybe_good_no_distribution : Prop :=
  maybe_empty Images.classifier_a_asan.
Definition asan_maybe_diff_no_distribution : Prop :=
  maybe_empty Images.classifier_b_asan.

(** ** How much each classifier does not accept, as the generator writes it (a bound [b]; the
    control is that it holds at NO [b] below 1, [_below_1], refuted): the classifier does not accept
    lps's finite input, which weighs the whole mass. *)
Definition asan_bound_good (b : Q) : Prop :=
  classifier_rejects_at_most Images.classifier_a_asan Distribution.w Distribution.M b.
Definition asan_bound_good_below_1 : Prop :=
  exists b : Q, (b < 1)%Q /\ asan_bound_good b.
Definition asan_bound_diff (b : Q) : Prop :=
  classifier_rejects_at_most Images.classifier_b_asan Distribution.w Distribution.M b.
Definition asan_bound_diff_below_1 : Prop :=
  exists b : Q, (b < 1)%Q /\ asan_bound_diff b.
