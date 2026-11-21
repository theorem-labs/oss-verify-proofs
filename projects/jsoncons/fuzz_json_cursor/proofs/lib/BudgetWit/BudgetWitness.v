(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 arms of Pm10DrvMain.v's src0_realizes_spec_lim, over BudgetWit.SpinAlgB.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the four statements whose budget premise is on the plain build. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader fact, walks lifted to the run's segments, the vDSO): changed usage_never_refused, usage_never_refused_abort, usage_never_refused_sv48 and 1 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/BudgetWit/BudgetWitness.v, lines 68-74, 81-98, 104-116, 127-130, 141-146. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.jsoncons.fuzz_json_cursor Require Images Statements.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import RunEnv PropExec ShapeAlg SpinAlg Spec
  Pm10Startup Pm10MainEntry Pm10Usage.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Theorems.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.BudgetWit Require Import SpinAlgB Pm10StartupB Pm10UsageB.
Import ListNotations.

(** * jsoncons / fuzz_json_cursor: the budget premise on the plain build holds together with the other premises

    Four statements of [Statements] carry a budget premise on the plain build:
    [plain_halts] ([halts_within_budget], [forced_only_cfg],
    [Budgets.Standard.lim_source]) and the three abort-modelled agreements
    [ubsan_agrees] ([Budgets.Standard.lim_source]), [asan_agrees] and
    [asan_ubsan_agrees] ([Budgets.Asan.lim_source]), all three under
    [Env.alloc_forced_only].  A theorem whose premises never hold together
    proves nothing.  [OSSVerify.Core.Premises] gives the entry and input
    premises for every well-formed image and leaves the budget premise, which
    reads the run; this file gives it for this build, for every configuration
    and every limit.

    The inputs are [Premises.witness_input false] (for [valid_input]) and
    [Premises.witness_input true] (for [valid_input_abort]): one empty argument
    (so argc = 1), no environment, an empty file system.  With argc <> 2 the
    driver's [main] writes its usage line to fd 2 and exits with status 2.  On
    that path the program makes three kinds of system call: set_tid_address
    (96) in musl's start-up, writev (66) for the line, exit or exit_group
    (93, 94).  None is an allocation call (brk 214, mremap 216, mmap 222,
    mprotect 226), and no mapping is lazy ([m_vm_lazy = []] throughout), so no
    configuration the run reaches is refused by the budget.  This shows the
    budget premise satisfiable on the usage path, not yet on an input that
    reaches [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path ([Pm10Startup.ref_startup],
    the argc <> 2 arms of [Pm10DrvMain.src0_realizes_spec_lim],
    [Pm10Usage.ref_usage_w]) restated over [BudgetWit.SpinAlgB.rzb], the
    released [SpinAlg.srealizes] with a no-allocation-call check at each node
    ([BudgetWit.SpinAlgB] says why [srealizes] itself cannot carry the fact),
    at [may_fail_cfg], where the configured step is the unfiltered one.
    [usage_rzb] is that walk; [SpinAlgB.rzb_never_refused_cfg] turns it into
    the budget premise, for every spurious-failure configuration and every
    limit ([usage_never_refused]).  Each [<statement>_not_vacuous] gives the
    premises of one of the four statements at one input to the released proof
    of that statement (the term its [proofs/<statement>/Proof.v] is), so the
    statement's conclusion holds at a point that meets all its premises, with
    no hypothesis left. *)

#[local] Existing Instance PropExec.fx0.

(** The argc <> 2 arms of [Pm10DrvMain.src0_realizes_spec_lim], over [rzb] at
    [may_fail_cfg], at every limit: start-up ([Pm10StartupB.ref_startup_b]),
    then [main]'s usage path ([Pm10UsageB.ref_usage_w_b]).  The model is
    rewritten into the form [ref_usage_w] states it in, as
    [src0_realizes_spec_lim] does. *)
Lemma usage_rzb : forall sp brk mbase (rdraw : EntryDraw) (lim : Z) (inp : ProcInput),
  valid_sp sp -> valid_brk Plain.M.loaded_segments brk ->
  (* LPS 727298f3: the start-up walk reads the launch, so [Pm10StartupB.ref_startup_b] asks
     for the two facts [Run.valid_entry_sv48] and [Run.valid_input] supply, as
     [Pm10DrvMain.src0_realizes_spec_lim] does; and the reader, which [Pm10UsageB]'s writev
     needs ([Run.valid_input_channel_reader]).  All three are discharged at the launch in
     [usage_never_refused] and [usage_never_refused_abort] below. *)
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  in_channel_reader inp = true ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (length (in_argv inp) <> 2)%nat ->
  rzb Plain.M.loaded_segments may_fail_cfg
    (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase rdraw lim inp)
    (t_die (msg_usage (hd [] (in_argv inp))) (in_fs inp)).
Proof.
  intros sp brk mbase rdraw lim inp Hsp Hbrk Hvl Hlau Hrd Hva Hve Hargc.
  apply ref_startup_b; try assumption.
  intros tid regs mem Htid ME.
  rewrite with_tid_with_vdso_init_model_E.
  set (RE := run_env_at inp (Vdso.vdso_run_init (ed_vdso rdraw))).
  assert (RO : @ReaderOn RE) by exact Hrd.
  clearbody RE.
  exact (ref_usage_w_b may_fail_cfg sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw tid regs mem
           brk mbase (in_fs inp) (in_stdin inp) lim Hva Hve Hsp Htid inp _ ME Hargc).
Qed.

(** On every valid entry of the plain build and every input with a valid argv
    and envp, the Sv48 window, a valid launch, a channel reader and an argv that
    has not two entries, no configuration of the run is refused by the budget,
    whatever the spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused_sv48 : forall en inp,
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain en inp ->
  in_va_size inp = Sv48 -> valid_launch inp -> in_channel_reader inp = true ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_json_cursor.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hv Hvl Hrd Hva Hve Hlen cfg lim.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & _ & Hlau).
  (* [Run.run_scfg_budget_refused] reads the run against
     [run_segments Plain.M.loaded_segments inp sp mbase] and from the start configuration
     over that list, while [usage_rzb] is a walk over the binary's own segments.
     [SpinAlgB.rzb_run_init] lifts it; [vdso_image Plain.M.loaded_segments = None] by
     computation. *)
  exact (rzb_never_refused_cfg _ cfg _ _
           (rzb_run_init may_fail_cfg Plain.M.loaded_segments inp sp mbase
              Plain.M.init_pc Plain.M.phdrs brk rnd lim _ eq_refl
              (usage_rzb sp brk mbase rnd lim inp Hsp Hbrk Hvl Hlau Hrd Hva Hve Hlen))).
Qed.

Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_json_cursor.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp Hlen.
  pose proof (valid_input_va_size _ Hinp) as Hv.
  pose proof (valid_input_launch _ Hinp) as Hvl.
  pose proof (valid_input_channel_reader _ Hinp) as Hrd.
  destruct Hinp as (Hva & Hve & _).
  exact (usage_never_refused_sv48 en inp Hen Hv Hvl Hrd Hva Hve Hlen).
Qed.

Theorem usage_never_refused_abort : forall en inp,
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain en inp -> valid_input_abort inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_json_cursor.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp Hlen.
  pose proof (valid_input_abort_va_size _ Hinp) as Hv.
  (* [valid_input_abort] carries the launch and the reader as conjuncts; read them by
     shape, as [PmFinalSan.via_launch]/[via_channel_reader] do. *)
  assert (Hvl : valid_launch inp) by (red in Hinp; tauto).
  assert (Hrd : in_channel_reader inp = true) by (red in Hinp; tauto).
  destruct Hinp as (Hva & Hve & _).
  exact (usage_never_refused_sv48 en inp Hen Hv Hvl Hrd Hva Hve Hlen).
Qed.

(** An entry of the plain build at [Premises.witness_input b], the entry
    [Premises.valid_input_entry] or [Premises.valid_input_abort_entry] gives
    for it, at which the budget refuses nothing, whatever the configuration
    and the limit. *)
Lemma plain_witness_entry : exists en,
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain en (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_json_cursor.Images.plain lim en
      (Premises.witness_input false).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
              (Premises.witness_input false)
              OSSVerify.jsoncons.fuzz_json_cursor.Images.plain_wf Premises.witness_valid_input) as [en Hen].
  exists en. split; [exact Hen |].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

Lemma plain_witness_entry_abort : exists en,
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain en (Premises.witness_input true) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_json_cursor.Images.plain lim en
      (Premises.witness_input true).
Proof.
  destruct (Premises.valid_input_abort_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
              (Premises.witness_input true)
              OSSVerify.jsoncons.fuzz_json_cursor.Images.plain_wf Premises.witness_valid_input_abort) as [en Hen].
  exists en. split; [exact Hen |].
  apply (usage_never_refused_abort en _ Hen Premises.witness_valid_input_abort).
  cbn. discriminate.
Qed.

(** The budget premise of the plain group at one entry and one input, for
    each configuration and limit a statement of the group names. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_witness_entry as (en & Hen & Hnr).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | apply Hnr]].
Qed.

Theorem plain_budget_witness_abort :
  exists en inp, valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain en inp /\ valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
      Budgets.Standard.lim_source en inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
      Budgets.Asan.lim_source en inp.
Proof.
  destruct plain_witness_entry_abort as (en & Hen & Hnr).
  exists en, (Premises.witness_input true).
  split; [exact Hen | split; [exact Premises.witness_valid_input_abort | split; apply Hnr]].
Qed.

(** The three agreement statements: an entry of the plain build and one of the
    sanitizer build on the same input [Premises.witness_input true] (the pair
    [Premises.agrees_in_abort_modelled_premises] builds, constructed here so
    that the input stays the witness input), with the budget premise from
    [plain_witness_entry_abort]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain en_plain (Premises.witness_input true) /\
  valid_entry san en_san (Premises.witness_input true) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_json_cursor.Images.plain lim en_plain
      (Premises.witness_input true).
Proof.
  intros san Hwf.
  destruct plain_witness_entry_abort as (en_plain & Hep & Hnr).
  destruct (Premises.valid_input_abort_entry san (Premises.witness_input true) Hwf
              Premises.witness_valid_input_abort) as [en_san Hes].
  exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.plain_halts], which the released
    [Theorems.halts_allowed_jsoncons_fuzz_json_cursor_halts_plain] proves, at an
    entry and an input that meet all three of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem plain_halts_not_vacuous :
  exists en inp,
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain en inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
      Budgets.Standard.lim_source en inp /\
  must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_witness_entry as (en & Hen & Hnr).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]].
  exact ((OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Theorems.halts_allowed_jsoncons_fuzz_json_cursor_halts_plain
            : OSSVerify.jsoncons.fuzz_json_cursor.Statements.plain_halts)
           en (Premises.witness_input false) Hen Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_json_cursor_ubsan] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain en_plain inp /\
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.ubsan en_san inp /\
  valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
      Budgets.Standard.lim_source en_plain inp /\
  error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
      Budgets.Standard.lim_source en_plain inp)
  /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.ubsan
      Budgets.Standard.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.jsoncons.fuzz_json_cursor.Images.ubsan
              OSSVerify.jsoncons.fuzz_json_cursor.Images.ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Theorems.strong_universal_error_free_fuzz_json_cursor_ubsan
            : OSSVerify.jsoncons.fuzz_json_cursor.Statements.ubsan_agrees)
           ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_json_cursor_asan] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain en_plain inp /\
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.asan en_san inp /\
  valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.asan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.jsoncons.fuzz_json_cursor.Images.asan
              OSSVerify.jsoncons.fuzz_json_cursor.Images.asan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Theorems.strong_universal_error_free_fuzz_json_cursor_asan
            : OSSVerify.jsoncons.fuzz_json_cursor.Statements.asan_agrees)
           ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_json_cursor_both] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.plain en_plain inp /\
  valid_entry OSSVerify.jsoncons.fuzz_json_cursor.Images.asan_ubsan en_san inp /\
  valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.asan_ubsan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_json_cursor.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.jsoncons.fuzz_json_cursor.Images.asan_ubsan
              OSSVerify.jsoncons.fuzz_json_cursor.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Theorems.strong_universal_error_free_fuzz_json_cursor_both
            : OSSVerify.jsoncons.fuzz_json_cursor.Statements.asan_ubsan_agrees)
           ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.
