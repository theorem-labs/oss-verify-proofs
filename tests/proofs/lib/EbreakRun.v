(** What the refutations of tests/toy/ebreak/Statements.v share: each shape
    of OSSVerify.Core.Shapes is false of lps's ebreak image (and, for
    the pair shapes, lps's exit0 image beside it), at EVERY budget,
    environment and exit set, so in particular at the ones the statements
    use.

    The pieces are lps's own ([Checks.BudgetPremise]): the ebreak image's
    one instruction faults, so its run is never refused memory
    ([ebreak_source_within_budget]) and reaches an error
    ([ebreak_errors_cfg]); lps fires them on [agrees], [agrees_in] and
    [agrees_in_abort_modelled] ([ebreak_refutes_error_free_budgets] and its
    siblings).  What lps does not have is built here: the two halting
    shapes, [agrees_abort_modelled] (through lps's equivalence with the
    configured form at [may_fail_cfg]), the three [_rv64gc] shapes (on lps's
    demo and abort inputs, whose AT_HWCAP word is already RV64GC), the bound
    shapes and the classifier problem.  Each refutation applies the
    statement to one valid input and valid entries, so it really reaches
    inside the statement's quantifier, and it discharges the budget premise
    where the shape has one. *)
From Stdlib Require Import ZArith QArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType StackLayout State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs Examples Omni AbortWitness BudgetPremise.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit HaltsAllowed FinInput Classifier Measure.
From OSSVerify.Core Require Import Shapes Premises.
From OSSVerify.Tests.toy.ebreak Require Distribution.
Import ListNotations.

(** ** Inputs and runs *)

(** lps's demo and abort inputs carry the RV64GC word ([demo_hwcap] is
    [hwcap_rv64gc]), so they satisfy the declared predicates too. *)
Lemma demo_input_rv64gc : valid_input_hwcap_rv64gc demo_proc_input.
Proof.
  destruct demo_input_valid as (a & b & c & k & d & e & f & _ & h & v & u).
  exact (conj a (conj b (conj c (conj k (conj d (conj e (conj f
    (conj eq_refl (conj h (conj v u)))))))))).
Qed.

Lemma abrt_input_rv64gc : valid_input_abort_hwcap_rv64gc abrt_input.
Proof.
  destruct abrt_input_valid as (a & b & c & k & d & e & f & _ & h & v & u).
  exact (conj a (conj b (conj c (conj k (conj d (conj e (conj f
    (conj eq_refl (conj h (conj v u)))))))))).
Qed.

Lemma ebreak_never_refused_cfg : forall cfg lim,
  ~ run_scfg_budget_refused cfg ebreak_image lim demo_entry demo_proc_input.
Proof.
  intros cfg lim.
  change (source_within_budget_scfg cfg lim ebreak_image demo_entry demo_proc_input).
  apply source_within_budget_scfg_of_source_within_budget.
  apply ebreak_source_within_budget.
Qed.

(** The unconfigured run under the abort declaration errors too:
    [ebreak_errors] at lps's abort input. *)
Lemma ebreak_errors_abort : forall lim,
  bh_errors (run ebreak_image lim demo_entry abrt_input).
Proof.
  intros lim. cbn [run ebreak_image demo_entry bh_errors]. rewrite ebreak_config_abort.
  exists [], (mkCfg ebreak_ms (ebreak_model_abort lim)), []. split; [apply star_refl |].
  apply sstep_instr_fault; [reflexivity | reflexivity |].
  no_lazy. rewrite ebreak_faults. reflexivity.
Qed.

(** ... and so does every configured run at lps's finite-input witness
    ([Premises.inhabited_fin_input_valid]), which the bound and classifier
    shapes quantify over. *)
Lemma ebreak_errors_fin : forall cfg lim,
  bh_errors (run_scfg cfg ebreak_image lim demo_entry (to_proc_input inhabited_fin_input)).
Proof.
  intros cfg lim. cbn [run_scfg ebreak_image demo_entry bh_errors].
  match goal with |- reaches_error_cfg _ _ ?c => exists [], c, [] end.
  split; [apply star_cfg_refl |]. unfold init_config.
  apply sstep_cfg_instr_fault; [reflexivity | reflexivity |].
  no_lazy. vm_compute. reflexivity.
Qed.

(** The two builds disagree on that input, under any environment. *)
Lemma ebreak_exit0_disagree_fin : forall env,
  ~ good_input_s env ebreak_image exit0_image (to_proc_input inhabited_fin_input).
Proof.
  intros env Hg. pose proof inhabited_fin_input_valid as Hf.
  destruct (Hg demo_entry demo_entry (demo_entry_valid_ebreak _ Hf) (demo_entry_valid_exit0 _ Hf))
    as (Hef & _).
  exact (Hef (ebreak_errors_fin env source_alloc_limit)).
Qed.

(** ** Halting *)

Theorem ebreak_refutes_halts_within_budget : forall lim allowed,
  ~ halts_within_budget lim allowed ebreak_image.
Proof.
  intros lim S H.
  apply (must_exit_in_scfg_refuted_by_error forced_only_cfg S ebreak_image lim
           demo_entry demo_proc_input (ebreak_errors_cfg forced_only_cfg lim)).
  exact (H demo_entry demo_proc_input (demo_entry_valid_ebreak _ demo_input_valid)
           demo_input_valid (ebreak_never_refused_cfg forced_only_cfg lim)).
Qed.

Theorem ebreak_refutes_halts_may_fail : forall allowed,
  ~ halts_may_fail allowed ebreak_image.
Proof.
  intros S H.
  apply (must_exit_in_scfg_refuted_by_error may_fail_cfg S ebreak_image source_alloc_limit
           demo_entry demo_proc_input (ebreak_errors_cfg may_fail_cfg source_alloc_limit)).
  exact (H demo_entry demo_proc_input (demo_entry_valid_ebreak _ demo_input_valid)
           demo_input_valid).
Qed.

(** ** Agreement *)

Theorem ebreak_refutes_agrees : forall lp ls,
  ~ agrees lp ls ebreak_image exit0_image.
Proof. exact ebreak_refutes_error_free_budgets. Qed.

Theorem ebreak_refutes_agrees_in : forall env lp ls,
  ~ agrees_in env lp ls ebreak_image exit0_image.
Proof. exact ebreak_refutes_error_free_scfg_budgets. Qed.

Theorem ebreak_refutes_agrees_in_abort_modelled : forall env lp ls,
  ~ agrees_in_abort_modelled env lp ls ebreak_image exit0_image.
Proof. exact ebreak_refutes_error_free_scfg_budgets_abort. Qed.

Theorem ebreak_refutes_agrees_abort_modelled : forall lp ls,
  ~ agrees_abort_modelled lp ls ebreak_image exit0_image.
Proof.
  intros lp ls H. apply (ebreak_refutes_error_free_scfg_budgets_abort may_fail_cfg lp ls).
  apply strong_universal_error_free_T_scfg_budgets_abort_may_fail. exact H.
Qed.

Theorem ebreak_refutes_agrees_rv64gc : forall lp ls,
  ~ agrees_rv64gc lp ls ebreak_image exit0_image.
Proof.
  intros lp ls H.
  destruct (H demo_entry demo_entry demo_proc_input
              (demo_entry_valid_ebreak _ demo_input_valid)
              (demo_entry_valid_exit0 _ demo_input_valid)
              demo_input_rv64gc (ebreak_source_within_budget lp)) as (Hef & _).
  exact (Hef (ebreak_errors lp)).
Qed.

Theorem ebreak_refutes_agrees_in_rv64gc : forall env lp ls,
  ~ agrees_in_rv64gc env lp ls ebreak_image exit0_image.
Proof.
  intros env lp ls H.
  destruct (H demo_entry demo_entry demo_proc_input
              (demo_entry_valid_ebreak _ demo_input_valid)
              (demo_entry_valid_exit0 _ demo_input_valid)
              demo_input_rv64gc (ebreak_never_refused_cfg env lp)) as (Hef & _).
  exact (Hef (ebreak_errors_cfg env lp)).
Qed.

Theorem ebreak_refutes_agrees_abort_modelled_rv64gc : forall lp ls,
  ~ agrees_abort_modelled_rv64gc lp ls ebreak_image exit0_image.
Proof.
  intros lp ls H.
  destruct (H demo_entry demo_entry abrt_input
              (demo_entry_valid_ebreak_abort _ abrt_input_valid)
              (demo_entry_valid_exit0_abort _ abrt_input_valid)
              abrt_input_rv64gc (ebreak_source_within_budget_abort lp)) as ((Hef & _) & _).
  exact (Hef (ebreak_errors_abort lp)).
Qed.

(** ** How often the builds disagree: the one input above weighs 1, the
    whole mass [Distribution.M], so no bound below 1 holds.  (A proof claims
    some bound [b] > 0, so refuting only [b = 0] would leave every claimed
    bound uncontrolled.) *)
Lemma one_weight_exceeds : forall b,
  (b < 1)%Q ->
  ~ (sum_weights Distribution.w [inhabited_fin_input] <= b * Distribution.M)%Q.
Proof.
  intros b Hb Hle. apply (Qlt_not_le b 1 Hb).
  apply (Qle_trans _ (sum_weights Distribution.w [inhabited_fin_input])).
  - vm_compute. intro Hc. discriminate Hc.
  - apply (Qle_trans _ _ _ Hle). unfold Distribution.M.
    apply Qle_lteq. right. apply Qmult_1_r.
Qed.

Theorem ebreak_refutes_disagrees_at_most_below_1 : forall env,
  ~ exists b : Q, (b < 1)%Q
      /\ disagrees_at_most env Distribution.w Distribution.M ebreak_image exit0_image b.
Proof.
  intros env (b & Hb & H). apply (one_weight_exceeds b Hb).
  apply H.
  - cbn. constructor; [intros [] | constructor].
  - intros f [<- | []].
    exact (conj inhabited_fin_input_valid (ebreak_exit0_disagree_fin env)).
Qed.

Theorem ebreak_refutes_disagrees_at_most_rv64gc_below_1 : forall env,
  ~ exists b : Q, (b < 1)%Q
      /\ disagrees_at_most_rv64gc env Distribution.w Distribution.M ebreak_image exit0_image b.
Proof.
  intros env (b & Hb & H). apply (one_weight_exceeds b Hb).
  apply H.
  - cbn. constructor; [intros [] | constructor].
  - intros f [<- | []].
    exact (conj inhabited_fin_input_valid
             (conj inhabited_fin_input_rv64gc (ebreak_exit0_disagree_fin env))).
Qed.

(** ** The classifier problem: [exit0_image] (the toy's [Images.asan]) exits
    0, "the builds agree", on [inhabited_fin_input] ([exit0_accepts_fin]),
    where the builds disagree ([ebreak_exit0_disagree_fin]).  That they agree
    on no input is believed true, not proved here. *)
Lemma exit0_accepts_fin :
  must_exit_with_scfg forced_only_cfg verdict_accept exit0_image classifier_alloc_limit
    demo_entry (to_proc_input inhabited_fin_input).
Proof. exact (exit0_must_exit_at_cfg _ _ _ _ _ _ _). Qed.

Theorem asan_refutes_classifies : forall env,
  ~ classifies env ebreak_image exit0_image exit0_image.
Proof.
  intros env H. pose proof inhabited_fin_input_valid as Hf.
  destruct (H inhabited_fin_input Hf demo_entry (demo_entry_valid_exit0 _ Hf))
    as ((Hacc & _) & _).
  exact (ebreak_exit0_disagree_fin env (Hacc exit0_accepts_fin)).
Qed.

Theorem asan_refutes_classifies_rv64gc : forall env,
  ~ classifies_rv64gc env ebreak_image exit0_image exit0_image.
Proof.
  intros env H. pose proof inhabited_fin_input_valid as Hf.
  destruct (H inhabited_fin_input Hf inhabited_fin_input_rv64gc demo_entry
              (demo_entry_valid_exit0 _ Hf)) as ((Hacc & _) & _).
  exact (ebreak_exit0_disagree_fin env (Hacc exit0_accepts_fin)).
Qed.
