(** * OSSVerify.Core.Shapes: what every statement in this collection says

    Every statement in oss-fuzz-theorems is one of the definitions below,
    applied to the memory images of specific binaries.  Each is written out
    in full.  Each agreement and halting shape, and the two classifier
    shapes, is proved EQUAL, by [reflexivity], to the definition in
    linux-process-semantics (lps) it corresponds to, so what you read here is
    exactly what lps means and lps's documentation applies unchanged.  The
    other input-set shapes are built from lps definitions only.

    Vocabulary (all from lps):
    - IMAGE ([MemImageType.Image]): what the Linux loader maps from a static
      riscv64 ELF file: its loadable segments, entry point and program-header
      location.
    - ENTRY ([Run.ExecEntry]): what the kernel chooses at execve and the
      program does not control: stack top, program break, mmap base, the
      AT_RANDOM bytes.  Statements quantify over every valid entry,
      independently for each build.
    - INPUT ([State.ProcInput]): everything the environment supplies: argv,
      envp, the starting file system (so the input file, its contents or its
      absence), stdin, user and group ids, network peers, limits, the
      advertised machine capabilities.  [Run.valid_input] is lps's set of
      realistic inputs for a riscv64 Linux process with a 48-bit address
      space.  docs/semantics.md lists where it is narrower than Linux.
    - RUN ([Run.run img lim en inp]): the process's behaviour with [lim]
      bytes of memory it may allocate: its finite event traces (bytes written
      to each file descriptor, in order, and the exit status) and whether
      some execution reaches an ERROR.
    - ERROR: a step lps does not model, or a fault it treats as one: an
      unmodelled system call or instruction, an invalid memory access, an
      illegal instruction (how a UBSan check fails in these builds), and
      abort() (how a failed assert(), an AddressSanitizer report and an
      uncaught C++ exception end the process).
    - ENVIRONMENT FAILURES ([Run.SpuriousCfg]): which system calls may fail
      even though the process's state does not force them to.  See [Env].

    Nothing in this file is assumed: it declares no axiom or parameter and
    leaves no proof unfinished.  [Print Assumptions] of any lemma below
    lists only axioms in toolchain/allowed-axioms.txt; for the [_is_lps]
    lemmas, only Rocq's primitive integer and string types, which lps's
    definitions use. *)

From Stdlib Require Import ZArith QArith List.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit HaltsAllowed FinInput Classifier Measure.
From OSSVerify.Core Require Import Images.
Import ListNotations.

(** ** Parameters *)

(** Memory budgets in bytes, for the plain build and the sanitizer build. *)
Module Budgets.
  (** 16 GiB for the plain build, 512 GiB for the sanitizer build. *)
  Module Standard := Equivalence.ShippedBudgets.
  (** 2 GiB for the plain build, 512 GiB for the sanitizer build: used when
      the sanitizer build includes AddressSanitizer, whose allocator caps
      each size class well below 16 GiB. *)
  Module Asan := Equivalence.SanitizerBudgets.
End Budgets.

Lemma standard_budgets : Budgets.Standard.lim_source = 0x400000000%Z
                         /\ Budgets.Standard.lim_target = 0x8000000000%Z.
Proof. split; reflexivity. Qed.

Lemma asan_budgets : Budgets.Asan.lim_source = 0x80000000%Z
                     /\ Budgets.Asan.lim_target = 0x8000000000%Z.
Proof. split; reflexivity. Qed.

(** How much the environment may refuse. *)
Module Env.
  (** Any system call lps lets fail may fail, at any time: memory, file
      system, descriptors, network, credentials, interruption. *)
  Definition may_fail : SpuriousCfg := Run.may_fail_cfg.
  (** As [may_fail], except that a memory request fails only when the budget
      is spent or no address range is free. *)
  Definition alloc_forced_only : SpuriousCfg := Run.alloc_only_cfg false.
  (** A call fails only where the process's own state forces it to. *)
  Definition forced_only : SpuriousCfg := Run.forced_only_cfg.
End Env.

(** The three readings, spelled as lps's six per-family switches (memory
    first; [true] means "may fail without cause"). *)
Lemma may_fail_is : Env.may_fail = mkSpuriousCfg true true true true true true.
Proof. reflexivity. Qed.
Lemma alloc_forced_only_is :
  Env.alloc_forced_only = mkSpuriousCfg false true true true true true.
Proof. reflexivity. Qed.
Lemma forced_only_is :
  Env.forced_only = mkSpuriousCfg false false false false false false.
Proof. reflexivity. Qed.

(** Sets of allowed exit statuses. *)
Module Exits.
  (** 0..255: the statement says only that the process exits. *)
  Definition any : list word := HaltsAllowed.AnyExit.codes.
  (** 0 (every harness call returned 0 or -1) or 2 (the driver refused the
      input file, or ran out of memory, before or instead of calling the
      harness; in a Rust fuzz target, also an allocation that failed at any
      point, which the OSS Verify port's allocation-error hook ends with one
      line on standard error).
      docs/running.md lists the others: 77 (the harness called exit()),
      78 (a harness call returned a value other than 0 or -1), 79 (a Rust
      fuzz target panicked: a failed assertion, an unwrap, an overflow check
      or a failed rustc UB check, which the port's panic hook ends with one
      line on standard error); an abort, including a failed assert() and a
      sanitizer report, is not an exit at all.  In the driver's counting mode
      (bit 15 of the config-length word) a harness binary exits 0 whatever
      the harness returned. *)
  Definition ok_or_refused : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
End Exits.

(** ** Shape 1: agreement of a sanitizer build with the plain build

    [agrees lim_plain lim_san plain san]: for every valid input and every
    valid pair of entries, IF the plain build's run is never refused memory
    for exceeding [lim_plain], THEN
    - no execution of the plain build reaches an error;
    - no execution of the sanitizer build reaches an error (so the sanitizer
      never reports: a report aborts);
    - the two builds have exactly the same finite traces: the same bytes on
      every descriptor and the same exit status.
    The environment may refuse any call, in either build ([Env.may_fail]).
    The budget premise is on the plain build only: the sanitizer build, with
    [lim_san], gets no exemption. *)
Definition agrees (lim_plain lim_san : Z) (plain san : Image) : Prop :=
  forall (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp ->
    valid_entry san en_san inp ->
    valid_input inp ->
    ~ run_budget_refused plain lim_plain en_plain inp ->
    error_free (run plain lim_plain en_plain inp)
    /\ error_free (run san lim_san en_san inp)
    /\ trace_equiv (bh_traces (run plain lim_plain en_plain inp))
                   (bh_traces (run san lim_san en_san inp)).

Lemma agrees_is_lps : forall lp ls p s,
  agrees lp ls p s = strong_universal_error_free_T_budgets lp ls p s.
Proof. reflexivity. Qed.

(** [agrees_in env ...]: the same claim when the environment refuses only
    what [env] allows.  Used, with [Env.alloc_forced_only], where under
    [Env.may_fail] the statement would be false for a reason unrelated to
    the sanitizer: for harnesses whose own error path aborts on an
    allocation failure, and for a Rust fuzz target's AddressSanitizer pairs,
    whose allocation-failure hook writes the failed allocation's size while
    the ASan allocator asks the kernel for memory at other allocations than
    musl's, so the two builds refused at will could write different lines. *)
Definition agrees_in (env : SpuriousCfg) (lim_plain lim_san : Z) (plain san : Image) : Prop :=
  forall (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp ->
    valid_entry san en_san inp ->
    valid_input inp ->
    ~ run_scfg_budget_refused env plain lim_plain en_plain inp ->
    error_free (run_scfg env plain lim_plain en_plain inp)
    /\ error_free (run_scfg env san lim_san en_san inp)
    /\ trace_equiv (bh_traces (run_scfg env plain lim_plain en_plain inp))
                   (bh_traces (run_scfg env san lim_san en_san inp)).

Lemma agrees_in_is_lps : forall env lp ls p s,
  agrees_in env lp ls p s = strong_universal_error_free_T_scfg_budgets env lp ls p s.
Proof. reflexivity. Qed.

(** [agrees] is [agrees_in Env.may_fail].  They are different terms (one is
    stated over [Run.run], the other over [Run.run_scfg]), so this is an
    equivalence, from lps's [strong_universal_error_free_T_scfg_budgets_may_fail]. *)
Lemma agrees_iff_agrees_in_may_fail : forall lp ls p s,
  agrees lp ls p s <-> agrees_in Env.may_fail lp ls p s.
Proof.
  intros lp ls p s. rewrite agrees_is_lps, agrees_in_is_lps.
  symmetry. apply strong_universal_error_free_T_scfg_budgets_may_fail.
Qed.

(** [agrees_abort_modelled] and [agrees_in_abort_modelled]: the same two
    claims under lps's other reading of abort(), in which abort is death by
    SIGABRT ([Run.valid_input_abort]) rather than an unmodelled step.  The
    claims still forbid it: both runs must be error-free AND never killed by
    a signal.  Some C++ harnesses are stated this way because an uncaught
    exception reaches abort() through the C++ runtime. *)
Definition agrees_abort_modelled (lim_plain lim_san : Z) (plain san : Image) : Prop :=
  forall (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp ->
    valid_entry san en_san inp ->
    valid_input_abort inp ->
    ~ run_budget_refused plain lim_plain en_plain inp ->
    error_free_unkilled (run plain lim_plain en_plain inp)
    /\ error_free_unkilled (run san lim_san en_san inp)
    /\ trace_equiv (bh_traces (run plain lim_plain en_plain inp))
                   (bh_traces (run san lim_san en_san inp)).

Lemma agrees_abort_modelled_is_lps : forall lp ls p s,
  agrees_abort_modelled lp ls p s = strong_universal_error_free_T_budgets_abort lp ls p s.
Proof. reflexivity. Qed.

Definition agrees_in_abort_modelled (env : SpuriousCfg) (lim_plain lim_san : Z)
    (plain san : Image) : Prop :=
  forall (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp ->
    valid_entry san en_san inp ->
    valid_input_abort inp ->
    ~ run_scfg_budget_refused env plain lim_plain en_plain inp ->
    error_free_unkilled (run_scfg env plain lim_plain en_plain inp)
    /\ error_free_unkilled (run_scfg env san lim_san en_san inp)
    /\ trace_equiv (bh_traces (run_scfg env plain lim_plain en_plain inp))
                   (bh_traces (run_scfg env san lim_san en_san inp)).

Lemma agrees_in_abort_modelled_is_lps : forall env lp ls p s,
  agrees_in_abort_modelled env lp ls p s
  = strong_universal_error_free_T_scfg_budgets_abort env lp ls p s.
Proof. reflexivity. Qed.

(** The [_rv64gc] variants: [agrees], [agrees_abort_modelled] and
    [agrees_in] on the inputs whose advertised machine (AT_HWCAP) is RV64GC,
    with no vector unit ([Run.valid_input_hwcap_rv64gc] and
    [Run.valid_input_abort_hwcap_rv64gc]).  They are used for harnesses whose
    libraries probe for the vector extension at start-up: lps does not model
    the vector instructions such a probe runs when a vector unit is
    advertised, so the unrestricted statement would be false for a reason
    unrelated to the sanitizer.  Everything else is unchanged. *)
Definition agrees_rv64gc (lim_plain lim_san : Z) (plain san : Image) : Prop :=
  forall (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp ->
    valid_entry san en_san inp ->
    valid_input_hwcap_rv64gc inp ->
    ~ run_budget_refused plain lim_plain en_plain inp ->
    error_free (run plain lim_plain en_plain inp)
    /\ error_free (run san lim_san en_san inp)
    /\ trace_equiv (bh_traces (run plain lim_plain en_plain inp))
                   (bh_traces (run san lim_san en_san inp)).

Lemma agrees_rv64gc_is_lps : forall lp ls p s,
  agrees_rv64gc lp ls p s = strong_universal_error_free_T_budgets_hwcap_rv64gc lp ls p s.
Proof. reflexivity. Qed.

Definition agrees_abort_modelled_rv64gc (lim_plain lim_san : Z) (plain san : Image) : Prop :=
  forall (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp ->
    valid_entry san en_san inp ->
    valid_input_abort_hwcap_rv64gc inp ->
    ~ run_budget_refused plain lim_plain en_plain inp ->
    error_free_unkilled (run plain lim_plain en_plain inp)
    /\ error_free_unkilled (run san lim_san en_san inp)
    /\ trace_equiv (bh_traces (run plain lim_plain en_plain inp))
                   (bh_traces (run san lim_san en_san inp)).

Lemma agrees_abort_modelled_rv64gc_is_lps : forall lp ls p s,
  agrees_abort_modelled_rv64gc lp ls p s
  = strong_universal_error_free_T_budgets_abort_hwcap_rv64gc lp ls p s.
Proof. reflexivity. Qed.

Definition agrees_in_rv64gc (env : SpuriousCfg) (lim_plain lim_san : Z)
    (plain san : Image) : Prop :=
  forall (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp ->
    valid_entry san en_san inp ->
    valid_input_hwcap_rv64gc inp ->
    ~ run_scfg_budget_refused env plain lim_plain en_plain inp ->
    error_free (run_scfg env plain lim_plain en_plain inp)
    /\ error_free (run_scfg env san lim_san en_san inp)
    /\ trace_equiv (bh_traces (run_scfg env plain lim_plain en_plain inp))
                   (bh_traces (run_scfg env san lim_san en_san inp)).

Lemma agrees_in_rv64gc_is_lps : forall env lp ls p s,
  agrees_in_rv64gc env lp ls p s
  = strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc env lp ls p s.
Proof. reflexivity. Qed.

(** ** Shape 2: halting

    [halts_within_budget lim allowed img]: on every valid input and entry on
    which the run is never refused memory for exceeding [lim], and when the
    environment refuses nothing it is not forced to ([Env.forced_only]),
    EVERY execution of [img] ends by calling exit_group with a status in
    [allowed].  So no execution runs forever (the predicate is inductive),
    gets stuck, reaches an error, or dies by a signal.  Nothing is said about
    output.  Under [Env.forced_only] a memory request is refused only when
    the budget is spent or no address range is free, and address-space
    reservations that are never touched (PROT_NONE, MAP_NORESERVE) are not
    charged to the budget (lps Mmap.v). *)
Definition halts_within_budget (lim : Z) (allowed : list word) (img : Image) : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry img en inp ->
    valid_input inp ->
    ~ run_scfg_budget_refused forced_only_cfg img lim en inp ->
    must_exit_in_scfg forced_only_cfg allowed img lim en inp.

Lemma halts_within_budget_is_lps : forall lim allowed img,
  halts_within_budget lim allowed img
  = halts_allowed_T_scfg_budgets forced_only_cfg lim allowed img.
Proof. reflexivity. Qed.

(** [halts_may_fail allowed img]: as above, with no budget premise, whatever
    the environment refuses ([Env.may_fail]), at lps's single-binary budget
    (16 GiB).  Stronger, and false for any build whose start-up waits
    forever when a reservation is refused, which is why no AddressSanitizer
    build has a statement of this shape. *)
Definition halts_may_fail (allowed : list word) (img : Image) : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry img en inp ->
    valid_input inp ->
    must_exit_in_scfg may_fail_cfg allowed img source_alloc_limit en inp.

Lemma halts_may_fail_is_lps : forall allowed img,
  halts_may_fail allowed img = halts_allowed_T_scfg may_fail_cfg allowed img.
Proof. reflexivity. Qed.

(** Widening the allowed set weakens both readings. *)
Lemma halts_within_budget_mono : forall lim S1 S2 img,
  (forall code, In code S1 -> In code S2) ->
  halts_within_budget lim S1 img -> halts_within_budget lim S2 img.
Proof.
  intros lim S1 S2 img Hsub H en inp Hen Hinp Hlim.
  exact (must_exit_in_scfg_mono_set _ _ _ _ _ _ _ Hsub (H en inp Hen Hinp Hlim)).
Qed.

Lemma halts_may_fail_mono : forall S1 S2 img,
  (forall code, In code S1 -> In code S2) ->
  halts_may_fail S1 img -> halts_may_fail S2 img.
Proof.
  intros S1 S2 img Hsub H. rewrite halts_may_fail_is_lps in *.
  exact (halts_allowed_T_scfg_mono_set _ _ _ _ Hsub H).
Qed.

(** ** Shapes 3 and 4: on which inputs the builds agree

    An input AGREES ([Classifier.good_input_s env plain san]) when, at every
    pair of valid entries, both builds are error-free on it and have equal
    traces.  Unlike shape 1, agreement is judged at lps's fixed budgets
    (16 GiB plain, 512 GiB sanitizer) and with no budget premise.  Only
    FINITE inputs are considered ([FinInput.FinProcInput]: finite stdin,
    finite files).

    [disagrees_at_most env w M plain san b]: under the input distribution
    [w] (total mass [M]; 1 for every distribution here), the inputs on which
    the builds do not agree weigh at most [b * M].  Each input CORE (argv,
    envp, files, stdin) is counted once, and counts as a disagreement if the
    builds disagree under SOME launch environment for it.  Every [b] is a
    statement; a proof at [b] implies every larger [b].

    ([List.NoDup] is written qualified here and below because stdpp, which
    lps uses, defines a second [NoDup]; lps's definitions use the standard
    library's, and so must these for the equalities with lps to hold.) *)
Definition disagrees_at_most (env : SpuriousCfg) (w : FinProcInput -> Q) (M : Q)
    (plain san : Image) (b : Q) : Prop :=
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (forall f, In f l -> valid_fin_input f /\ ~ good_input_s env plain san (to_proc_input f)) ->
    (sum_weights w l <= b * M)%Q.

(** [classifies env plain san C]: the riscv64 program [C] decides exactly the
    agreeing inputs: on every valid finite input, from every valid entry, it
    exits 0 if the input agrees and 1 if it does not.  [C]'s own runs are
    judged with [Env.forced_only], because under [Env.may_fail] no program
    that reads its input could be both total and correct.  Totality is
    implied ([Classifier.decides_fo_implies_total]). *)
Definition classifies (env : SpuriousCfg) (plain san C : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en : ExecEntry,
      valid_entry C en (to_proc_input f) ->
      (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en
         (to_proc_input f)
       <-> good_input_s env plain san (to_proc_input f))
      /\ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en
            (to_proc_input f)
          \/ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en
               (to_proc_input f)).

Lemma classifies_is_lps : forall env plain san C,
  classifies env plain san C = classifies_good_inputs_T_s env plain san C.
Proof. reflexivity. Qed.

(** [classifier_rejects_at_most C w M b]: the inputs [C] rejects weigh at
    most [b * M], each core counted once.  An input is rejected when it is a
    valid finite input and [C] does not exit 0 on it from every valid entry
    ([Classifier.rejects_fo]). *)
Definition classifier_rejects_at_most (C : Image) (w : FinProcInput -> Q) (M b : Q) : Prop :=
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (forall f, In f l -> rejects_fo C f) ->
    (sum_weights w l <= b * M)%Q.

Lemma classifier_rejects_at_most_is_lps : forall C w M b,
  classifier_rejects_at_most C w M b = weight_bound_T_fo C w M b.
Proof. reflexivity. Qed.

(** [agreement_decidable env plain san]: some well-formed riscv64 program
    decides the agreeing inputs.  [image_wf] is required: an image with no
    valid entry would "decide" everything vacuously. *)
Definition agreement_decidable (env : SpuriousCfg) (plain san : Image) : Prop :=
  exists C : Image, image_wf C /\ classifies env plain san C.

(** The [_rv64gc] variants of the input-set shapes, for the harnesses whose
    agreement statements are [_rv64gc]: only inputs whose advertised machine
    is RV64GC are considered, for the classifier and for the claim alike. *)
Definition disagrees_at_most_rv64gc (env : SpuriousCfg) (w : FinProcInput -> Q) (M : Q)
    (plain san : Image) (b : Q) : Prop :=
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (forall f, In f l ->
       valid_fin_input f
       /\ in_hwcap (to_proc_input f) = hwcap_rv64gc
       /\ ~ good_input_s env plain san (to_proc_input f)) ->
    (sum_weights w l <= b * M)%Q.

Definition classifies_rv64gc (env : SpuriousCfg) (plain san C : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    in_hwcap (to_proc_input f) = hwcap_rv64gc ->
    forall en : ExecEntry,
      valid_entry C en (to_proc_input f) ->
      (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en
         (to_proc_input f)
       <-> good_input_s env plain san (to_proc_input f))
      /\ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en
            (to_proc_input f)
          \/ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en
               (to_proc_input f)).

Lemma classifies_rv64gc_is_lps : forall env plain san C,
  classifies_rv64gc env plain san C = classifies_good_inputs_T_s_hwcap_rv64gc env plain san C.
Proof. reflexivity. Qed.

Definition agreement_decidable_rv64gc (env : SpuriousCfg) (plain san : Image) : Prop :=
  exists C : Image, image_wf C /\ classifies_rv64gc env plain san C.

(** A classifier for all inputs is one for the RV64GC inputs. *)
Lemma classifies_rv64gc_of_classifies : forall env plain san C,
  classifies env plain san C -> classifies_rv64gc env plain san C.
Proof. intros env plain san C H f Hf _ en Hen. exact (H f Hf en Hen). Qed.

(** Smaller [b] is stronger. *)
Lemma disagrees_at_most_mono : forall env w M plain san b b',
  (0 <= M)%Q -> (b <= b')%Q ->
  disagrees_at_most env w M plain san b -> disagrees_at_most env w M plain san b'.
Proof.
  intros env w M plain san b b' HM Hb H l Hnd Hin.
  eapply Qle_trans; [exact (H l Hnd Hin) |].
  apply Qmult_le_compat_r; assumption.
Qed.

Lemma classifier_rejects_at_most_mono : forall C w M b b',
  (0 <= M)%Q -> (b <= b')%Q ->
  classifier_rejects_at_most C w M b -> classifier_rejects_at_most C w M b'.
Proof.
  intros C w M b b' HM Hb H l Hnd Hin.
  eapply Qle_trans; [exact (H l Hnd Hin) |].
  apply Qmult_le_compat_r; assumption.
Qed.

(** ** How the classifier results give the claims

    A classifier proved exact ([classifies]) and well formed, whose rejected
    inputs weigh at most [b], proves [disagrees_at_most ... b]: an input on
    which the builds disagree is one the classifier cannot accept, because a
    well-formed image has a valid entry on every valid input
    ([Equivalence.image_brk_satisfiable_entry]) and from that entry it would
    have to exit 0.  So proving the two templates of a harness's
    Characterise.v for one [C] proves its [_disagrees_at_most] and
    [_agreement_decidable] statements. *)
Lemma disagrees_at_most_of_classifier : forall env w M plain san C b,
  image_wf C ->
  classifies env plain san C ->
  classifier_rejects_at_most C w M b ->
  disagrees_at_most env w M plain san b.
Proof.
  intros env w M plain san C b Hwf Hcls Hrej l Hnd Hin.
  apply Hrej; [exact Hnd |].
  intros f Hf. destruct (Hin f Hf) as [Hv Hbad].
  split; [exact Hv |]. intros Hacc. apply Hbad.
  assert (Hbrk : image_brk_satisfiable (img_segments C) = true)
    by (destruct C as [segs pc ph]; exact (proj2 (proj2 Hwf))).
  destruct (image_brk_satisfiable_entry C (to_proc_input f) Hv Hbrk) as [en Hen].
  exact (proj1 (proj1 (Hcls f Hv en Hen)) (Hacc en Hen)).
Qed.

Lemma agreement_decidable_of_classifier : forall env plain san C,
  image_wf C -> classifies env plain san C -> agreement_decidable env plain san.
Proof. intros env plain san C Hwf Hcls. exists C. split; assumption. Qed.

Lemma disagrees_at_most_rv64gc_of_classifier : forall env w M plain san C b,
  image_wf C ->
  classifies_rv64gc env plain san C ->
  classifier_rejects_at_most C w M b ->
  disagrees_at_most_rv64gc env w M plain san b.
Proof.
  intros env w M plain san C b Hwf Hcls Hrej l Hnd Hin.
  apply Hrej; [exact Hnd |].
  intros f Hf. destruct (Hin f Hf) as (Hv & Hhw & Hbad).
  split; [exact Hv |]. intros Hacc. apply Hbad.
  assert (Hbrk : image_brk_satisfiable (img_segments C) = true)
    by (destruct C as [segs pc ph]; exact (proj2 (proj2 Hwf))).
  destruct (image_brk_satisfiable_entry C (to_proc_input f) Hv Hbrk) as [en Hen].
  exact (proj1 (proj1 (Hcls f Hv Hhw en Hen)) (Hacc en Hen)).
Qed.

Lemma agreement_decidable_rv64gc_of_classifier : forall env plain san C,
  image_wf C -> classifies_rv64gc env plain san C -> agreement_decidable_rv64gc env plain san.
Proof. intros env plain san C Hwf Hcls. exists C. split; assumption. Qed.
