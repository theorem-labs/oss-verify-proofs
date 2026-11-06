(** Controls that live inside Rocq: this file compiles only if every [Fail]
    below fails and every lemma below holds.

    - [check_image_wf] refuses images that are not well formed, so the [_wf]
      lemma every harness's Images.v proves is a real check.
    - Each [_is_lps] lemma of OSSVerify.Core.Shapes is an equality
      between two different constants; the second group shows that such an
      equality is not free: a shape stated with a DIFFERENT budget, reading or
      exit set is not equal to lps's by [reflexivity].
    - Each per-shape lemma of OSSVerify.Core.Premises applies to the
      toy images through their [_wf] lemmas, as it applies to every
      harness's images: their entry and input premises hold together. *)
From Stdlib Require Import ZArith QArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence HaltsAllowed.
From OSSVerify.Core Require Import Images Shapes Premises.
From OSSVerify.Tests.toy.exit0.images Require Plain.
From OSSVerify.Tests.toy.exit0 Require Images.
Import ListNotations.

(** The toy image with its entry point moved past the end of its only
    segment: nothing is fetchable there. *)
Definition entry_outside : Image :=
  mkImage Plain.M.loaded_segments 0x20000%N Plain.M.phdrs.

Lemma entry_outside_not_wf : ~ image_wf entry_outside.
Proof. intros H. apply image_wf_b_complete in H. vm_compute in H. discriminate H. Qed.

Fail Definition entry_outside_wf : image_wf entry_outside := ltac:(check_image_wf).

(** The same image claiming a program-header table in unmapped memory. *)
Definition phdrs_outside : Image :=
  mkImage Plain.M.loaded_segments Plain.M.init_pc (mkPhdrInfo 0x30000%N 56%N 1%N).

Lemma phdrs_outside_not_wf : ~ image_wf phdrs_outside.
Proof. intros H. apply image_wf_b_complete in H. vm_compute in H. discriminate H. Qed.

Fail Definition phdrs_outside_wf : image_wf phdrs_outside := ltac:(check_image_wf).

(** No segments at all. *)
Fail Definition empty_wf : image_wf (mkImage [] 0x10078%N Plain.M.phdrs) := ltac:(check_image_wf).

(** The shapes' equalities with lps are not satisfied by a neighbouring
    definition: the reading, the budget and the exit set all matter. *)
Fail Definition halts_reading_matters : forall lim S img,
  halts_within_budget lim S img = halts_allowed_T_scfg_budgets may_fail_cfg lim S img
  := fun _ _ _ => eq_refl.
Fail Definition agrees_reading_matters : forall lp ls p s,
  agrees lp ls p s = strong_universal_error_free_T_budgets_abort lp ls p s
  := fun _ _ _ _ => eq_refl.
Fail Definition exits_matter :
  Exits.ok_or_refused = [Z_to_bv 64 0; Z_to_bv 64 1]
  := eq_refl.
Fail Definition budgets_matter :
  Budgets.Asan.lim_source = Budgets.Standard.lim_source
  := eq_refl.

(** Each of the 14 [_not_vacuous] lemmas of Premises.v, instantiated on the
    exit0 toy's images ([plain] alone for the two halting shapes, [plain] and
    [padded] for the others), at one value of each budget or environment
    parameter the lemma has; each typechecks.  The nine halting and agreement
    definitions and
    [of_good_input_s] use the images' [_wf] lemmas, so for these the entry and
    input premises hold together on the toy images.  The nine halting and
    agreement definitions still take the shape as a hypothesis, and for
    [halts_within_budget] and the agreement shapes the budget premise stays a
    hypothesis.  The two bound definitions use no [_wf] lemma: under the shape
    and [~ good_input_s] they give only the weight bound at lps's finite-input
    witness.  The two decidability definitions use no [_wf] lemma either: the
    entry they give is one of the classifier, not of a toy image. *)
Module ToyPremises.
  Module I := OSSVerify.Tests.toy.exit0.Images.
  Definition of_halts_within_budget :=
    halts_within_budget_not_vacuous Budgets.Standard.lim_source Exits.ok_or_refused _ I.plain_wf.
  Definition of_halts_may_fail := halts_may_fail_not_vacuous Exits.any _ I.plain_wf.
  Definition of_agrees :=
    agrees_not_vacuous Budgets.Standard.lim_source Budgets.Standard.lim_target _ _
      I.plain_wf I.padded_wf.
  Definition of_agrees_in :=
    agrees_in_not_vacuous Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target
      _ _ I.plain_wf I.padded_wf.
  Definition of_agrees_abort_modelled :=
    agrees_abort_modelled_not_vacuous Budgets.Standard.lim_source Budgets.Standard.lim_target
      _ _ I.plain_wf I.padded_wf.
  Definition of_agrees_in_abort_modelled :=
    agrees_in_abort_modelled_not_vacuous Env.alloc_forced_only Budgets.Asan.lim_source
      Budgets.Asan.lim_target _ _ I.plain_wf I.padded_wf.
  Definition of_agrees_rv64gc :=
    agrees_rv64gc_not_vacuous Budgets.Standard.lim_source Budgets.Standard.lim_target _ _
      I.plain_wf I.padded_wf.
  Definition of_agrees_in_rv64gc :=
    agrees_in_rv64gc_not_vacuous Env.alloc_forced_only Budgets.Asan.lim_source
      Budgets.Asan.lim_target _ _ I.plain_wf I.padded_wf.
  Definition of_agrees_abort_modelled_rv64gc :=
    agrees_abort_modelled_rv64gc_not_vacuous Budgets.Asan.lim_source Budgets.Asan.lim_target
      _ _ I.plain_wf I.padded_wf.
  Definition of_good_input_s := good_input_s_not_vacuous Env.may_fail _ _ I.plain_wf I.padded_wf.
  Definition of_disagrees_at_most :=
    disagrees_at_most_not_vacuous Env.may_fail (fun _ => 1%Q) 1%Q I.plain I.padded 0%Q.
  Definition of_disagrees_at_most_rv64gc :=
    disagrees_at_most_rv64gc_not_vacuous Env.may_fail (fun _ => 1%Q) 1%Q I.plain I.padded 0%Q.
  Definition of_agreement_decidable :=
    agreement_decidable_not_vacuous Env.may_fail I.plain I.padded.
  Definition of_agreement_decidable_rv64gc :=
    agreement_decidable_rv64gc_not_vacuous Env.may_fail I.plain I.padded.
End ToyPremises.

(** [agreement_decidable] has no lps twin to be proved equal to, so its body
    is pinned here: a well-formed classifier ([image_wf C]) that solves the
    classifier problem.  Without the [image_wf] conjunct a classifier with no
    valid entry would "decide" everything vacuously (Shapes.v), and dropping
    it makes these equalities fail. *)
Lemma agreement_decidable_is : forall env plain san,
  agreement_decidable env plain san = (exists C : Image, image_wf C /\ classifies env plain san C).
Proof. reflexivity. Qed.

Lemma agreement_decidable_rv64gc_is : forall env plain san,
  agreement_decidable_rv64gc env plain san
  = (exists C : Image, image_wf C /\ classifies_rv64gc env plain san C).
Proof. reflexivity. Qed.
