(* NEGATIVE CONTROL: a lemma about an image that the proof library's own
   Images.v names plain.  Control.shadowed_images.Images.plain is the plain
   image of the exit1 toy, and this lemma proves the premises of
   halts_within_budget for it on the instance's input: exit1 calls
   exit_group(1) at its third instruction and never asks for memory.  The
   wrapper defines the type before it loads this library, so there
   Images.plain is the plain image of OSSVerify.Tests.toy.exit0.Images.  The
   budget premise is about the run of that image, so the wrapper does not
   type-check. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import BudgetPremise.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence Classifier.
From OSSVerify.Core Require Import Shapes Premises.
From OSSVerify.Tests.proofs.lib Require Exit0Run.
From OSSVerify.Tests.proofs.lib Require Import Exit0Instance.
From OSSVerify.Tests.toy.exit1 Require Images.
From Control.shadowed_images Require Images.

Lemma exit1_never_budget_refused : forall lim en inp,
  ~ run_budget_refused Control.shadowed_images.Images.plain lim en inp.
Proof.
  intros lim [sp brk0 mbase rnd] inp.
  unfold run_budget_refused, Control.shadowed_images.Images.plain, OSSVerify.Tests.toy.exit1.Images.plain,
    init_config.
  apply exits_c_no_budget_refused with (code := verdict_reject) (fuel := 8%nat);
    [reflexivity | reflexivity | apply Exit0Run.exit1_exits_c].
Qed.

Lemma exit1_never_refused_cfg : forall cfg lim en inp,
  ~ run_scfg_budget_refused cfg Control.shadowed_images.Images.plain lim en inp.
Proof.
  intros cfg lim en inp.
  change (source_within_budget_scfg cfg lim Control.shadowed_images.Images.plain en inp).
  apply source_within_budget_scfg_of_source_within_budget.
  exact (exit1_never_budget_refused lim en inp).
Qed.

Lemma plain_halts_instance :
  exists en, valid_entry Control.shadowed_images.Images.plain en (input reaches_harness seven)
    /\ valid_input (input reaches_harness seven)
    /\ ~ run_scfg_budget_refused forced_only_cfg Control.shadowed_images.Images.plain
           Budgets.Standard.lim_source en (input reaches_harness seven).
Proof.
  pose proof (input_valid reaches_harness seven launch_argv_reaches_harness) as Hv.
  destruct (valid_input_entry Control.shadowed_images.Images.plain _
              Control.shadowed_images.Images.plain_wf Hv) as [en Hen].
  exists en. exact (conj Hen (conj Hv (exit1_never_refused_cfg _ _ en _))).
Qed.
