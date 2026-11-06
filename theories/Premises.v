(** * OSSVerify.Core.Premises: the entry and input premises can hold

    A statement whose hypotheses can never hold together is proved by
    anything.  The checker cannot see that: it compares a proof's type with
    the statement, nothing more.  This file shows, for every shape of
    [OSSVerify.Core.Shapes], that the entry and input premises hold
    together for every well-formed image ([Images.image_wf], which every
    harness's Images.v proves of each of its images by computation):
    - a valid input of the kind the shape quantifies over exists
      ([valid_input], [valid_input_abort], [valid_input_hwcap_rv64gc] or
      [valid_input_abort_hwcap_rv64gc]);
    - for every such input, every well-formed image has a valid entry, so
      the two images of an agreement shape have valid entries on the SAME
      input.

    The last section ties this to the shapes themselves: for each shape,
    a lemma whose hypothesis is the shape as Shapes.v defines it, and which
    applies it at these entries and this input ([<shape>_not_vacuous]).  So a
    change to Shapes.v that added a premise the witnesses do not meet makes
    this file fail to compile.

    So [halts_may_fail], whose only premises are these, is not vacuous for
    any well-formed image: [halts_may_fail_not_vacuous] gives its
    conclusion at one entry and input.  The other halting shape and the
    agreement shapes have one premise more, the budget premise
    ([~ run_scfg_budget_refused] or [~ run_budget_refused]).  It reads the
    run, so no lemma over all images can discharge it, and their
    [_not_vacuous] lemmas leave it as a hypothesis; the falsifiability
    controls (tests/README.md) show, for each of those shapes at the budgets
    and environments the statements use, that it holds together with these
    premises on a toy image.  The bound shape's other premise,
    [~ good_input_s], also reads the runs; this file shows only that both
    images have valid entries on a valid finite input, so [good_input_s] is
    not vacuously true ([good_input_s_not_vacuous]).  It does not show that
    a disagreeing input exists, nor that a harness's weights are not zero
    everywhere.  The decidability shape's classifier is applied at a valid
    finite input and an entry of its own ([agreement_decidable_not_vacuous]).

    This file is not hashed into any statement's fingerprint (only Shapes.v
    and Images.v are).  It declares no axiom or parameter and leaves no
    proof unfinished; [Print Assumptions] of its lemmas lists only Rocq's
    primitive integer, string and array types, which lps's definitions use. *)

From Stdlib Require Import ZArith QArith List Lia.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs MemImageType StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit HaltsAllowed FinInput Classifier Measure.
From OSSVerify.Core Require Import Images Shapes.
Import ListNotations.

(** ** Entries

    [Run.valid_entry] reads the input only through argv, envp and the
    address-space size, and the image only through its segments.  This is
    lps's [Equivalence.image_brk_satisfiable_entry] with its [valid_input]
    hypothesis cut down to those three clauses, so that it serves every
    input predicate the shapes use: the witness stack pointer is the
    bottom of the stack window, and the third conjunct of [image_wf]
    gives the break. *)
Lemma entry_exists : forall img inp,
  image_wf img ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> in_va_size inp = Sv48 ->
  exists en, valid_entry img en inp.
Proof.
  intros [segs pc ph] inp Hwf Hargv Henvp Hsize.
  destruct Hwf as (_ & _ & H).
  destruct (image_brk_satisfiable_sound segs H) as [brk Hbrk].
  pose proof (entry_stack_span_bound _ _ Hargv Henvp) as Hspan.
  exists (mkEntry (Z_to_bv 64 sp_window_lo) brk
            (Z_to_bv 64 mmap_base_max)
            (mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0))).
  rewrite (valid_entry_sv48 _ _ _ Hsize).
  cbn. split; [| split; [exact Hbrk | split]].
  - unfold valid_sp, sp_window_lo, sp_window_hi.
    rewrite Z_to_bv_unsigned, bv_wrap_small
      by (unfold bv_modulus; cbn; lia).
    lia.
  - unfold valid_mmap_base, mmap_base_min, mmap_base_max, sp_window_hi,
      page_size.
    rewrite Z_to_bv_unsigned, bv_wrap_small
      by (unfold bv_modulus; cbn; lia).
    lia.
  - unfold entry_stack_fits.
    rewrite Z_to_bv_unsigned, bv_wrap_small
      by (unfold bv_modulus, sp_window_lo; cbn; lia).
    unfold entry_stack_span_max in Hspan.
    unfold sp_window_lo, sp_window_hi. lia.
Qed.

(** Each input predicate the shapes use carries the three clauses. *)
Lemma valid_input_entry : forall img inp,
  image_wf img -> valid_input inp -> exists en, valid_entry img en inp.
Proof.
  intros img inp Hwf Hv. pose proof (valid_input_va_size _ Hv) as Hs.
  destruct Hv as (Ha & He & _). exact (entry_exists img inp Hwf Ha He Hs).
Qed.

Lemma valid_input_abort_entry : forall img inp,
  image_wf img -> valid_input_abort inp -> exists en, valid_entry img en inp.
Proof.
  intros img inp Hwf Hv. pose proof (valid_input_abort_va_size _ Hv) as Hs.
  destruct Hv as (Ha & He & _). exact (entry_exists img inp Hwf Ha He Hs).
Qed.

Lemma valid_input_hwcap_rv64gc_entry : forall img inp,
  image_wf img -> valid_input_hwcap_rv64gc inp -> exists en, valid_entry img en inp.
Proof.
  intros img inp Hwf Hv.
  apply valid_input_entry; [exact Hwf |].
  exact (valid_input_of_valid_input_hwcap_rv64gc _ Hv).
Qed.

Lemma valid_input_abort_hwcap_rv64gc_entry : forall img inp,
  image_wf img -> valid_input_abort_hwcap_rv64gc inp -> exists en, valid_entry img en inp.
Proof.
  intros img inp Hwf Hv.
  apply valid_input_abort_entry; [exact Hwf |].
  exact (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _ Hv).
Qed.

(** The bound and decidability shapes quantify over valid finite inputs. *)
Lemma fin_input_entry : forall img f,
  image_wf img -> valid_fin_input f -> exists en, valid_entry img en (to_proc_input f).
Proof. intros img f Hwf Hv. exact (valid_input_entry img _ Hwf Hv). Qed.

(** ** Inputs

    One input for all four predicates: one empty argument, no environment,
    an empty file system, end of input, ids 0, a quiet network, the
    default descriptor limit, an empty signal mask, the AT_HWCAP word
    without V (RV64GC), Sv48, and [abort] for the abort declaration.  The
    proofs are lps's for its fixtures ([Checks.AbortWitness.abrt_input_valid],
    [Checks.Cases.Hwcap.hwcap_abort_input_gc_declared]); this file states
    its own input rather than importing lps's test files. *)
Definition witness_input (abort : bool) : ProcInput :=
  mkProcInput [[]] [] [] IEof (Z_to_bv 64 0) (Z_to_bv 64 0) [] net_silent
    default_nofile (Z_to_bv 64 0) hwcap_rv64gc abort Sv48.

Local Ltac witness_valid :=
  cbn [mkProcInput in_argv in_envp in_fs];
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ];
    try valid_urandom_default.

Lemma witness_valid_input_hwcap_rv64gc : valid_input_hwcap_rv64gc (witness_input false).
Proof. unfold valid_input_hwcap_rv64gc, witness_input, valid_argv, valid_envp. witness_valid. Qed.

Lemma witness_valid_input_abort_hwcap_rv64gc :
  valid_input_abort_hwcap_rv64gc (witness_input true).
Proof.
  unfold valid_input_abort_hwcap_rv64gc, witness_input, valid_argv, valid_envp. witness_valid.
Qed.

Lemma witness_valid_input : valid_input (witness_input false).
Proof. exact (valid_input_of_valid_input_hwcap_rv64gc _ witness_valid_input_hwcap_rv64gc). Qed.

Lemma witness_valid_input_abort : valid_input_abort (witness_input true).
Proof.
  exact (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _
           witness_valid_input_abort_hwcap_rv64gc).
Qed.

(** ** One lemma per shape

    Each states that the premises of the shape other than the budget
    premise hold together, for any well-formed images: there are an input
    of the shape's kind and valid entries of each image on it.  For
    [halts_may_fail] that is every premise. *)
Lemma halts_within_budget_premises : forall img,
  image_wf img -> exists en inp, valid_entry img en inp /\ valid_input inp.
Proof.
  intros img Hwf.
  destruct (valid_input_entry img _ Hwf witness_valid_input) as [en Hen].
  exists en, (witness_input false). exact (conj Hen witness_valid_input).
Qed.

Lemma halts_may_fail_premises : forall img,
  image_wf img -> exists en inp, valid_entry img en inp /\ valid_input inp.
Proof. exact halts_within_budget_premises. Qed.

(** The agreement shapes, by input predicate. *)
Lemma pair_premises : forall (P : ProcInput -> Prop) inp plain san,
  P inp ->
  (forall img, image_wf img -> P inp -> exists en, valid_entry img en inp) ->
  image_wf plain -> image_wf san ->
  exists en_plain en_san inp,
    valid_entry plain en_plain inp /\ valid_entry san en_san inp /\ P inp.
Proof.
  intros P inp plain san Hp Hent Hwp Hws.
  destruct (Hent plain Hwp Hp) as [ep Hep]. destruct (Hent san Hws Hp) as [es Hes].
  exists ep, es, inp. exact (conj Hep (conj Hes Hp)).
Qed.

Lemma agrees_premises : forall plain san,
  image_wf plain -> image_wf san ->
  exists en_plain en_san inp,
    valid_entry plain en_plain inp /\ valid_entry san en_san inp /\ valid_input inp.
Proof.
  intros plain san. apply (pair_premises valid_input (witness_input false));
    [exact witness_valid_input | intros img Hwf; exact (valid_input_entry img _ Hwf)].
Qed.

Lemma agrees_in_premises : forall plain san,
  image_wf plain -> image_wf san ->
  exists en_plain en_san inp,
    valid_entry plain en_plain inp /\ valid_entry san en_san inp /\ valid_input inp.
Proof. exact agrees_premises. Qed.

Lemma agrees_abort_modelled_premises : forall plain san,
  image_wf plain -> image_wf san ->
  exists en_plain en_san inp,
    valid_entry plain en_plain inp /\ valid_entry san en_san inp /\ valid_input_abort inp.
Proof.
  intros plain san. apply (pair_premises valid_input_abort (witness_input true));
    [exact witness_valid_input_abort | intros img Hwf; exact (valid_input_abort_entry img _ Hwf)].
Qed.

Lemma agrees_in_abort_modelled_premises : forall plain san,
  image_wf plain -> image_wf san ->
  exists en_plain en_san inp,
    valid_entry plain en_plain inp /\ valid_entry san en_san inp /\ valid_input_abort inp.
Proof. exact agrees_abort_modelled_premises. Qed.

Lemma agrees_rv64gc_premises : forall plain san,
  image_wf plain -> image_wf san ->
  exists en_plain en_san inp,
    valid_entry plain en_plain inp /\ valid_entry san en_san inp
    /\ valid_input_hwcap_rv64gc inp.
Proof.
  intros plain san. apply (pair_premises valid_input_hwcap_rv64gc (witness_input false));
    [exact witness_valid_input_hwcap_rv64gc
    | intros img Hwf; exact (valid_input_hwcap_rv64gc_entry img _ Hwf)].
Qed.

Lemma agrees_in_rv64gc_premises : forall plain san,
  image_wf plain -> image_wf san ->
  exists en_plain en_san inp,
    valid_entry plain en_plain inp /\ valid_entry san en_san inp
    /\ valid_input_hwcap_rv64gc inp.
Proof. exact agrees_rv64gc_premises. Qed.

Lemma agrees_abort_modelled_rv64gc_premises : forall plain san,
  image_wf plain -> image_wf san ->
  exists en_plain en_san inp,
    valid_entry plain en_plain inp /\ valid_entry san en_san inp
    /\ valid_input_abort_hwcap_rv64gc inp.
Proof.
  intros plain san.
  apply (pair_premises valid_input_abort_hwcap_rv64gc (witness_input true));
    [exact witness_valid_input_abort_hwcap_rv64gc
    | intros img Hwf; exact (valid_input_abort_hwcap_rv64gc_entry img _ Hwf)].
Qed.

(** The bound and decidability shapes: a valid finite input exists, with
    the RV64GC word (for the [_rv64gc] forms), and each well-formed image
    has a valid entry on it.  The input is lps's own witness
    [FinInput.inhabited_fin_input]; lps proves it valid inside the
    existential [FinInput.valid_fin_input_inhabited], by this script, which
    is restated here so that the witness's word can be read. *)
Lemma inhabited_fin_input_valid : valid_fin_input inhabited_fin_input.
Proof.
  unfold valid_fin_input, to_proc_input, inhabited_fin_input,
         valid_input, valid_argv, valid_envp.
  cbn [fin_argv fin_envp fin_image_fs fin_stdin fin_uid fin_gid fin_groups
       fin_net fin_nofile fin_sigmask fin_hwcap fin_abort_terminal
       fin_va_size fin_urandom fin_tmp
       in_argv in_envp in_fs in_nofile in_sigmask in_hwcap
       in_abort_terminal in_va_size in_urandom].
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try (unfold valid_hwcap; left; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ].
  all: try (unfold valid_urandom; cbn [in_urandom];
            exact State.default_urandom_infinite).
Qed.

Lemma inhabited_fin_input_rv64gc : in_hwcap (to_proc_input inhabited_fin_input) = hwcap_rv64gc.
Proof. reflexivity. Qed.

Lemma fin_premises : forall plain san,
  image_wf plain -> image_wf san ->
  exists f en_plain en_san,
    valid_fin_input f /\ in_hwcap (to_proc_input f) = hwcap_rv64gc
    /\ valid_entry plain en_plain (to_proc_input f)
    /\ valid_entry san en_san (to_proc_input f).
Proof.
  intros plain san Hwp Hws.
  pose proof inhabited_fin_input_valid as Hf.
  destruct (fin_input_entry plain _ Hwp Hf) as [ep Hep].
  destruct (fin_input_entry san _ Hws Hf) as [es Hes].
  exists inhabited_fin_input, ep, es.
  exact (conj Hf (conj inhabited_fin_input_rv64gc (conj Hep Hes))).
Qed.

(** ** The shapes themselves

    Each lemma below takes the shape, as Shapes.v defines it, as its
    hypothesis, and applies it at the entries and the input the lemmas above
    supply.  What is left is the shape's conclusion, under the budget
    premise where the shape has one.  A premise added to a shape that these
    witnesses do not meet, or a change of its input predicate, makes the
    application ill-typed, and this file then fails to compile. *)

Lemma halts_within_budget_not_vacuous : forall lim allowed img,
  image_wf img -> halts_within_budget lim allowed img ->
  exists en inp,
    ~ run_scfg_budget_refused forced_only_cfg img lim en inp ->
    must_exit_in_scfg forced_only_cfg allowed img lim en inp.
Proof.
  intros lim allowed img Hwf H.
  destruct (halts_within_budget_premises img Hwf) as (en & inp & Hen & Hv).
  exists en, inp. exact (H en inp Hen Hv).
Qed.

Lemma halts_may_fail_not_vacuous : forall allowed img,
  image_wf img -> halts_may_fail allowed img ->
  exists en inp, must_exit_in_scfg may_fail_cfg allowed img source_alloc_limit en inp.
Proof.
  intros allowed img Hwf H.
  destruct (halts_may_fail_premises img Hwf) as (en & inp & Hen & Hv).
  exists en, inp. exact (H en inp Hen Hv).
Qed.

Lemma agrees_not_vacuous : forall lp ls plain san,
  image_wf plain -> image_wf san -> agrees lp ls plain san ->
  exists ep es inp,
    ~ run_budget_refused plain lp ep inp ->
    error_free (run plain lp ep inp) /\ error_free (run san ls es inp)
    /\ trace_equiv (bh_traces (run plain lp ep inp)) (bh_traces (run san ls es inp)).
Proof.
  intros lp ls plain san Hp Hs H.
  destruct (agrees_premises plain san Hp Hs) as (ep & es & inp & Hep & Hes & Hv).
  exists ep, es, inp. exact (H ep es inp Hep Hes Hv).
Qed.

Lemma agrees_in_not_vacuous : forall env lp ls plain san,
  image_wf plain -> image_wf san -> agrees_in env lp ls plain san ->
  exists ep es inp,
    ~ run_scfg_budget_refused env plain lp ep inp ->
    error_free (run_scfg env plain lp ep inp) /\ error_free (run_scfg env san ls es inp)
    /\ trace_equiv (bh_traces (run_scfg env plain lp ep inp))
                   (bh_traces (run_scfg env san ls es inp)).
Proof.
  intros env lp ls plain san Hp Hs H.
  destruct (agrees_in_premises plain san Hp Hs) as (ep & es & inp & Hep & Hes & Hv).
  exists ep, es, inp. exact (H ep es inp Hep Hes Hv).
Qed.

Lemma agrees_abort_modelled_not_vacuous : forall lp ls plain san,
  image_wf plain -> image_wf san -> agrees_abort_modelled lp ls plain san ->
  exists ep es inp,
    ~ run_budget_refused plain lp ep inp ->
    error_free_unkilled (run plain lp ep inp) /\ error_free_unkilled (run san ls es inp)
    /\ trace_equiv (bh_traces (run plain lp ep inp)) (bh_traces (run san ls es inp)).
Proof.
  intros lp ls plain san Hp Hs H.
  destruct (agrees_abort_modelled_premises plain san Hp Hs) as (ep & es & inp & Hep & Hes & Hv).
  exists ep, es, inp. exact (H ep es inp Hep Hes Hv).
Qed.

Lemma agrees_in_abort_modelled_not_vacuous : forall env lp ls plain san,
  image_wf plain -> image_wf san -> agrees_in_abort_modelled env lp ls plain san ->
  exists ep es inp,
    ~ run_scfg_budget_refused env plain lp ep inp ->
    error_free_unkilled (run_scfg env plain lp ep inp)
    /\ error_free_unkilled (run_scfg env san ls es inp)
    /\ trace_equiv (bh_traces (run_scfg env plain lp ep inp))
                   (bh_traces (run_scfg env san ls es inp)).
Proof.
  intros env lp ls plain san Hp Hs H.
  destruct (agrees_in_abort_modelled_premises plain san Hp Hs)
    as (ep & es & inp & Hep & Hes & Hv).
  exists ep, es, inp. exact (H ep es inp Hep Hes Hv).
Qed.

Lemma agrees_rv64gc_not_vacuous : forall lp ls plain san,
  image_wf plain -> image_wf san -> agrees_rv64gc lp ls plain san ->
  exists ep es inp,
    ~ run_budget_refused plain lp ep inp ->
    error_free (run plain lp ep inp) /\ error_free (run san ls es inp)
    /\ trace_equiv (bh_traces (run plain lp ep inp)) (bh_traces (run san ls es inp)).
Proof.
  intros lp ls plain san Hp Hs H.
  destruct (agrees_rv64gc_premises plain san Hp Hs) as (ep & es & inp & Hep & Hes & Hv).
  exists ep, es, inp. exact (H ep es inp Hep Hes Hv).
Qed.

Lemma agrees_in_rv64gc_not_vacuous : forall env lp ls plain san,
  image_wf plain -> image_wf san -> agrees_in_rv64gc env lp ls plain san ->
  exists ep es inp,
    ~ run_scfg_budget_refused env plain lp ep inp ->
    error_free (run_scfg env plain lp ep inp) /\ error_free (run_scfg env san ls es inp)
    /\ trace_equiv (bh_traces (run_scfg env plain lp ep inp))
                   (bh_traces (run_scfg env san ls es inp)).
Proof.
  intros env lp ls plain san Hp Hs H.
  destruct (agrees_in_rv64gc_premises plain san Hp Hs) as (ep & es & inp & Hep & Hes & Hv).
  exists ep, es, inp. exact (H ep es inp Hep Hes Hv).
Qed.

Lemma agrees_abort_modelled_rv64gc_not_vacuous : forall lp ls plain san,
  image_wf plain -> image_wf san -> agrees_abort_modelled_rv64gc lp ls plain san ->
  exists ep es inp,
    ~ run_budget_refused plain lp ep inp ->
    error_free_unkilled (run plain lp ep inp) /\ error_free_unkilled (run san ls es inp)
    /\ trace_equiv (bh_traces (run plain lp ep inp)) (bh_traces (run san ls es inp)).
Proof.
  intros lp ls plain san Hp Hs H.
  destruct (agrees_abort_modelled_rv64gc_premises plain san Hp Hs)
    as (ep & es & inp & Hep & Hes & Hv).
  exists ep, es, inp. exact (H ep es inp Hep Hes Hv).
Qed.

(** The bound shapes: at lps's finite-input witness, which weighs
    [w inhabited_fin_input], the shape bounds that weight whenever the
    builds disagree there; and agreement there ([good_input_s]) is not
    vacuously true, because both images have valid entries on a valid
    finite input. *)
Lemma good_input_s_not_vacuous : forall env plain san,
  image_wf plain -> image_wf san ->
  exists f ep es,
    valid_fin_input f /\ in_hwcap (to_proc_input f) = hwcap_rv64gc
    /\ (good_input_s env plain san (to_proc_input f) ->
        strong_equiv_error_free_scfg env plain san ep es (to_proc_input f)).
Proof.
  intros env plain san Hp Hs.
  destruct (fin_premises plain san Hp Hs) as (f & ep & es & Hf & Hhw & Hep & Hes).
  exists f, ep, es. exact (conj Hf (conj Hhw (fun Hg => Hg ep es Hep Hes))).
Qed.

Lemma disagrees_at_most_not_vacuous : forall env w M plain san b,
  disagrees_at_most env w M plain san b ->
  ~ good_input_s env plain san (to_proc_input inhabited_fin_input) ->
  (sum_weights w [inhabited_fin_input] <= b * M)%Q.
Proof.
  intros env w M plain san b H Hbad. apply H.
  - cbn. constructor; [intros [] | constructor].
  - intros f [<- | []]. exact (conj inhabited_fin_input_valid Hbad).
Qed.

Lemma disagrees_at_most_rv64gc_not_vacuous : forall env w M plain san b,
  disagrees_at_most_rv64gc env w M plain san b ->
  ~ good_input_s env plain san (to_proc_input inhabited_fin_input) ->
  (sum_weights w [inhabited_fin_input] <= b * M)%Q.
Proof.
  intros env w M plain san b H Hbad. apply H.
  - cbn. constructor; [intros [] | constructor].
  - intros f [<- | []].
    exact (conj inhabited_fin_input_valid (conj inhabited_fin_input_rv64gc Hbad)).
Qed.

(** The decidability shapes: the classifier they assert is well formed, so
    it has a valid entry on lps's finite-input witness, and there it gives a
    verdict that is exact. *)
Lemma agreement_decidable_not_vacuous : forall env plain san,
  agreement_decidable env plain san ->
  exists C en,
    image_wf C /\ valid_entry C en (to_proc_input inhabited_fin_input)
    /\ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en
          (to_proc_input inhabited_fin_input)
        <-> good_input_s env plain san (to_proc_input inhabited_fin_input))
    /\ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en
          (to_proc_input inhabited_fin_input)
        \/ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en
             (to_proc_input inhabited_fin_input)).
Proof.
  intros env plain san (C & Hwf & Hcls).
  destruct (fin_input_entry C _ Hwf inhabited_fin_input_valid) as [en Hen].
  exists C, en. exact (conj Hwf (conj Hen (Hcls _ inhabited_fin_input_valid en Hen))).
Qed.

Lemma agreement_decidable_rv64gc_not_vacuous : forall env plain san,
  agreement_decidable_rv64gc env plain san ->
  exists C en,
    image_wf C /\ valid_entry C en (to_proc_input inhabited_fin_input)
    /\ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en
          (to_proc_input inhabited_fin_input)
        <-> good_input_s env plain san (to_proc_input inhabited_fin_input))
    /\ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en
          (to_proc_input inhabited_fin_input)
        \/ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en
             (to_proc_input inhabited_fin_input)).
Proof.
  intros env plain san (C & Hwf & Hcls).
  destruct (fin_input_entry C _ Hwf inhabited_fin_input_valid) as [en Hen].
  exists C, en.
  exact (conj Hwf (conj Hen
    (Hcls _ inhabited_fin_input_valid inhabited_fin_input_rv64gc en Hen))).
Qed.
