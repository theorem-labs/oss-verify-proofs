(** What the refutations of the classifier statements of
    tests/toy/ebreak/Statements.v share: each shape of
    OSSVerify.Core.ClassifierShapes, and [Shapes.classifier_rejects_at_most],
    is false of one of three of lps's own test images, on the toy's pair (lps's
    ebreak image as the plain build, its exit0 image as the asan build) and in
    EVERY environment, so in particular in the ones the statements use.

    - lps's ebreak image ([Checks.Omni.ebreak_image]) gives no answer: its one
      instruction faults, so no run of it exits.  On lps's finite-input witness
      ([Premises.inhabited_fin_input_valid]) it answers neither yes nor no, so
      it is not total, its maybe set is not empty, and, since the toy
      distribution gives that one input the whole mass, neither its maybe
      inputs nor the inputs it does not accept weigh at most [b * M] for any
      [b] below 1.
    - lps's exit0 image ([Checks.Examples.exit0_image]) always answers yes, and
      on that input the builds disagree ([EbreakRun.ebreak_exit0_disagree_fin]):
      it is not sound for classifier A's property.
    - lps's exit1 image ([Checks.GatedSize.exit1_image]) always answers no, and
      on that input each build agrees with itself, at every pair of valid
      entries: it is not sound for classifier B's property with the builds as
      their own originals.  That the exit0 image agrees with itself is lps's
      trace set of it ([Checks.BudgetPremise.exit0_obs_cfg]); that the ebreak
      image does is proved here, from its fault at every entry, computed with
      the stack memory abstracted as lps computes the exit0 image's run
      ([Checks.Omni.exit0_exits_c]).

    Stated at lps c0dd863a, the model release.yaml pins from the update
    (OSSV-509): a launch places the stack by the input, so each run here is
    entered at [fin_entry], the entry [Checks.Examples.demo_entry_of] gives
    the finite-input witness, as in [EbreakRun]; and a run reads the segment
    list [Run.run_segments] builds, the image's own segment and then the vDSO
    pair, which no fetch of these images reaches. *)
From Stdlib Require Import ZArith QArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  Examples Omni SpuriousCfg BudgetPremise GatedSize.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit FinInput Classifier Measure.
From OSSVerify.Core Require Import Shapes ClassifierShapes Premises.
From OSSVerify.Tests.toy.ebreak Require Distribution.
From OSSVerify.Tests.proofs.lib Require EbreakRun.
Import ListNotations.

(** The witness's own entry ([EbreakRun.fin_entry]). *)
Abbreviation fin_entry := (demo_entry_of (to_proc_input inhabited_fin_input)).

(** ** The classifier that gives no answer: lps's ebreak image *)

Lemma ebreak_entry_fin :
  valid_entry ebreak_image fin_entry (to_proc_input inhabited_fin_input).
Proof. exact (demo_entry_valid_ebreak _ inhabited_fin_input_valid). Qed.

(** At that entry its run errors, so it exits with no code at all. *)
Lemma ebreak_no_answer : forall code,
  ~ must_exit_with_scfg forced_only_cfg code ebreak_image classifier_alloc_limit fin_entry
      (to_proc_input inhabited_fin_input).
Proof.
  intros code Hm.
  exact (must_exit_with_scfg_refuted_by_error _ _ _ _ _ _ (EbreakRun.ebreak_errors_fin _ _) Hm).
Qed.

(** So the input is a maybe input: neither yes nor no from every valid entry. *)
Lemma ebreak_maybe_fin : maybe_input ebreak_image inhabited_fin_input.
Proof.
  split; [exact inhabited_fin_input_valid |]. split.
  - intros H. exact (ebreak_no_answer _ (H fin_entry ebreak_entry_fin)).
  - intros H. exact (ebreak_no_answer _ (H fin_entry ebreak_entry_fin)).
Qed.

Theorem ebreak_refutes_classifier_total3 : ~ classifier_total3 ebreak_image.
Proof.
  intros H.
  destruct (H inhabited_fin_input inhabited_fin_input_valid fin_entry ebreak_entry_fin)
    as [Hv | [Hv | Hv]]; exact (ebreak_no_answer _ Hv).
Qed.

Theorem ebreak_refutes_maybe_empty : ~ maybe_empty ebreak_image.
Proof. intros H. exact (H inhabited_fin_input ebreak_maybe_fin). Qed.

(** The one input weighs 1, the whole mass [Distribution.M] (as in
    [EbreakRun.ebreak_refutes_disagrees_at_most_below_1]). *)
Theorem ebreak_refutes_maybe_at_most_below_1 :
  ~ exists b : Q, (b < 1)%Q
      /\ maybe_at_most ebreak_image Distribution.w Distribution.M b.
Proof.
  intros (b & Hb & H). apply (EbreakRun.one_weight_exceeds b Hb).
  apply H.
  - cbn. constructor; [intros [] | constructor].
  - intros f [<- | []]. exact ebreak_maybe_fin.
Qed.

Theorem ebreak_refutes_classifier_rejects_at_most_below_1 :
  ~ exists b : Q, (b < 1)%Q
      /\ classifier_rejects_at_most ebreak_image Distribution.w Distribution.M b.
Proof.
  intros (b & Hb & H). apply (EbreakRun.one_weight_exceeds b Hb).
  apply H.
  - cbn. constructor; [intros [] | constructor].
  - intros f [<- | []].
    exact (conj inhabited_fin_input_valid (proj1 (proj2 ebreak_maybe_fin))).
Qed.

(** ** The classifier that always answers yes: lps's exit0 image

    It exits 0 on lps's finite-input witness ([EbreakRun.exit0_accepts_fin]),
    on which the builds disagree. *)
Theorem exit0_refutes_classifies_good_inputs_sound : forall env,
  ~ classifies_good_inputs_sound env ebreak_image exit0_image exit0_image.
Proof.
  intros env H. pose proof inhabited_fin_input_valid as Hf.
  destruct (H inhabited_fin_input Hf fin_entry (demo_entry_valid_exit0 _ Hf)) as (Hacc & _).
  exact (EbreakRun.ebreak_exit0_disagree_fin env (Hacc EbreakRun.exit0_accepts_fin)).
Qed.

(** ** The classifier that always answers no: lps's exit1 image *)

(** It exits 1 from every placement and on every input: the exit0 image's
    three instructions with one immediate changed, computed with the stack
    memory abstracted, as [Checks.Omni.exit0_exits_c] computes the exit0
    image's, at the segment list the run reads ([Run.run_segments]). *)
Lemma exit1_exits_c : forall sp mbase draw inp,
  exits_c (run_segments exit1_segments inp sp mbase) verdict_reject 8
    (init_machine_state (run_segments exit1_segments inp sp mbase) 0x100 demo_phdrs sp
       mbase draw inp)
  = true.
Proof.
  intros. rewrite (with_mem_eta (init_machine_state _ _ _ _ _ _ _)).
  generalize (ms_mem (init_machine_state (run_segments exit1_segments inp sp mbase) 0x100
                        demo_phdrs sp mbase draw inp)).
  intros mem. unfold run_segments. vm_compute. reflexivity.
Qed.

Lemma exit1_rejects_fin :
  must_exit_with_scfg forced_only_cfg verdict_reject exit1_image classifier_alloc_limit
    fin_entry (to_proc_input inhabited_fin_input).
Proof.
  unfold must_exit_with_scfg, exit1_image. rewrite (entry_eta fin_entry).
  cbn beta iota zeta. unfold init_config.
  apply (exits_c_must_exit_at_cfg _ _ _ 8); [reflexivity | reflexivity | apply exit1_exits_c].
Qed.

(** The ebreak image's first step faults from EVERY placement and on EVERY
    input: the fetch reads the image's segment, which no placement touches,
    and which [Run.run_segments] puts before the vDSO pair. *)
Lemma ebreak_faults_at : forall sp mbase draw inp,
  RiscvSemantics.step (run_segments ebreak_segments inp sp mbase)
    (init_machine_state (run_segments ebreak_segments inp sp mbase) 0x100 demo_phdrs sp
       mbase draw inp)
  = MachineFault.
Proof.
  intros. rewrite (with_mem_eta (init_machine_state _ _ _ _ _ _ _)).
  generalize (ms_mem (init_machine_state (run_segments ebreak_segments inp sp mbase) 0x100
                        demo_phdrs sp mbase draw inp)).
  intros mem. unfold run_segments. vm_compute. reflexivity.
Qed.

Lemma ebreak_only_at : forall sp brk0 mbase rnd lim inp evs st,
  sstep (run_segments ebreak_segments inp sp mbase)
    (init_config (run_segments ebreak_segments inp sp mbase) 0x100 demo_phdrs sp brk0 mbase
       rnd lim inp)
    evs st ->
  evs = [] /\ st = SError.
Proof.
  intros sp brk0 mbase rnd lim inp. unfold init_config.
  apply sstep_fault_only; [reflexivity | reflexivity | apply ebreak_faults_at].
Qed.

(** So under any configuration its one trace is the empty one. *)
Lemma ebreak_obs_cfg : forall cfg sp brk0 mbase rnd lim inp tr,
  obs_trace_cfg (run_segments ebreak_segments inp sp mbase) cfg
    (init_config (run_segments ebreak_segments inp sp mbase) 0x100 demo_phdrs sp brk0 mbase
       rnd lim inp) tr
  <-> tr = [].
Proof.
  intros cfg sp brk0 mbase rnd lim inp tr. split.
  - intros H.
    destruct (obs_trace_cfg_sub (run_segments ebreak_segments inp sp mbase) cfg _ _ H)
      as (tr' & c & Hstar & Hp).
    inversion Hstar; subst.
    + destruct tr; [reflexivity | destruct Hp].
    + match goal with
      | Hss : sstep _ _ _ (SNext _) |- _ =>
          destruct (ebreak_only_at _ _ _ _ _ _ _ _ Hss) as (_ & Habs); discriminate Habs
      end.
  - intros ->.
    exists [], (init_config (run_segments ebreak_segments inp sp mbase) 0x100 demo_phdrs sp
                  brk0 mbase rnd lim inp).
    split; [apply star_cfg_refl | exact I].
Qed.

(** Each build agrees with itself, at every budget and in every
    environment: its trace set is the same from every entry, and the other
    three conjuncts compare a run with itself. *)
Lemma ebreak_agrees_with_itself : forall cfg lim inp,
  agree_s cfg ebreak_image ebreak_image lim inp.
Proof.
  intros cfg lim inp. unfold agree_s.
  refine (conj _ (conj (iff_refl _) (conj (iff_refl _) (iff_refl _)))).
  intros [sp1 brk1 mb1 rnd1] [sp2 brk2 mb2 rnd2] _ _ tr.
  cbn [run_scfg ebreak_image bh_traces]. rewrite !ebreak_obs_cfg. reflexivity.
Qed.

Lemma exit0_agrees_with_itself : forall cfg lim inp,
  agree_s cfg exit0_image exit0_image lim inp.
Proof.
  intros cfg lim inp. unfold agree_s.
  refine (conj _ (conj (iff_refl _) (conj (iff_refl _) (iff_refl _)))).
  intros [sp1 brk1 mb1 rnd1] [sp2 brk2 mb2 rnd2] _ _ tr.
  cbn [run_scfg exit0_image bh_traces]. rewrite !exit0_obs_cfg. reflexivity.
Qed.

Theorem exit1_refutes_classifies_patch_diff_sound : forall env,
  ~ classifies_patch_diff_sound env ebreak_image ebreak_image exit0_image exit0_image exit1_image.
Proof.
  intros env H. pose proof inhabited_fin_input_valid as Hf.
  destruct (H inhabited_fin_input Hf fin_entry (demo_entry_valid_exit1 _ Hf)) as (_ & Hno).
  exact (Hno (conj (ebreak_agrees_with_itself _ _ _) (exit0_agrees_with_itself _ _ _))
             exit1_rejects_fin).
Qed.
