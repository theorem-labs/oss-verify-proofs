(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from D_Dir.v's ref_realizes_spec, its argc <> 2 branches only, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the three statements whose budget premise is on the plain build. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (usage_rzb takes the channel-reader premise and the launch facts valid_launch and entry_launch_ok_va, passes the launch facts to the start-up walk, and gives the usage path main's entry with the launch facts read back through the AMB world; usage_never_refused reads those premises from valid_input and valid_entry by name and lifts the walk onto the run's segments with the vDSO pair). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.Core Require Images.
From OSSVerify.varnish.esi_parse_fuzzer Require Images Statements.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Amb ShapeAlg Spec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Theorems.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Stmwg.   (* the *_C_of transport lemmas, qualified *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BudgetWit Require Import Rzb D_StmwgB D_UsageB.
Import ListNotations.
Open Scope Z_scope.

(** * varnish / esi_parse_fuzzer: the budget premise on the plain build holds together with the other premises

    Three statements of [Statements] carry a budget premise on the plain build,
    [~ run_scfg_budget_refused cfg Images.plain lim en inp], and are proved:
    - [ubsan_agrees] ([agrees_in]), at [Env.alloc_forced_only] and
      [Budgets.Standard.lim_source];
    - [asan_agrees] and [asan_ubsan_agrees] ([agrees_in]), at
      [Env.alloc_forced_only] and [Budgets.Asan.lim_source].
    ([plain_halts] also puts its budget premise on [Images.plain], but has no
    proof yet.)  A theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image and leaves the budget premise, which reads the run; this
    file gives it for this build, for every configuration and every limit.

    The input is [Premises.witness_input false]: one empty argument (so argc = 1),
    no environment, an empty file system.  With argc <> 2 the driver's [main] writes
    its usage line to fd 2 and exits with status 2.  On that path the program makes
    three kinds of system call: set_tid_address (96) in musl's start-up, writev (66)
    for the line, exit or exit_group (93, 94).  None is an allocation call (brk 214,
    mremap 216, mmap 222, mprotect 226), and no mapping is lazy ([m_vm_lazy = []]
    throughout), so no configuration the run reaches is refused by the budget.
    This shows the budget premise satisfiable on the usage path, not yet on an
    input that reaches [LLVMFuzzerTestOneInput].

    The released walk is stated over [ShapeAlg.realizes] in a budget world
    ([BWorld.BWorld]); in the world [BWorld.bw_premise lim] the released proofs
    take the budget premise as a hypothesis ([BWorld.never_excused_of_premise]),
    so they cannot give it.  The proof here is the released proof of the usage
    path ([D_Stmwg.ref_startup], then [D_Usage.ref_usage_w], the argc <> 2
    branches of [D_Dir.ref_realizes_spec]) restated over [BudgetWit.Rzb.rzb],
    [ShapeAlg.realizes0] with a no-allocation check at each node and no budget
    world.  [usage_rzb] is that walk; [Rzb.rzb_never_refused_cfg] turns it into
    the budget premise, for every spurious-failure configuration and every limit
    ([usage_never_refused]).  Each [<statement>_not_vacuous] gives the premises of
    one of the three statements at one input to the released proof of that
    statement (the term its [proofs/<statement>/Proof.v] is), so the statement's
    conclusion holds at a point that meets all its premises, with no hypothesis
    left. *)

(** [D_Dir.ref_realizes_spec] with only its argc <> 2 branches, over [rzb]:
    start-up ([D_StmwgB.ref_startup_b]), then [main]'s usage path
    ([D_UsageB.ref_usage_w_b]). *)
Lemma usage_rzb : forall sp brk mbase (rdraw : EntryDraw) lim inp,
  valid_sp sp -> valid_brk Plain.M.loaded_segments brk ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  in_abort_terminal inp = false ->
  in_channel_reader inp = true ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  (length (in_argv inp) <> 2)%nat ->
  rzb Plain.M.loaded_segments
      (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase rdraw lim inp)
      (t_die (msg_usage (hd [] (in_argv inp))) (in_fs inp)).
Proof.
  intros sp brk mbase rdraw lim inp Hsp Hbrk Hva Hve Hfit Hab Hrd Hvl Hlau Hlen.
  apply (ref_startup_b sp brk mbase rdraw lim inp _ Hsp Hbrk Hva Hve Hab Hvl Hlau).
  intros tid regs mem Htid ME.
  (* [ref_startup_b]'s continuation is over [with_tid tid (with_vdso .. (init_model .. inp))];
     [replace] rewrites the [init_model] under that wrapper *)
  replace (init_model (segments_reserved Plain.M.loaded_segments) brk mbase sp lim inp)
    with (init_model (segments_reserved Plain.M.loaded_segments) brk mbase sp lim
            (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)))
    by (rewrite (init_model_C_of _ _ _ _ _ inp Hab); reflexivity).
  (* LPS 727298f3: the usage path takes [D_Manqc.main_launch] over the AMB world's input: the launch
     facts and main's entry, each read back through [amb_of inp] ([D_Stmwg]'s *_C_of lemmas),
     as [D_Dir.ref_realizes_spec] builds it *)
  exact (@D_UsageB.ref_usage_w_b (amb_of inp) sp (in_argv inp) (in_envp inp) rdraw tid regs mem brk mbase
           (in_fs inp) (in_stdin inp) lim Hva Hve Hsp Htid
           (conj (D_Stmwg.valid_launch_C_of inp Hab Hvl)
              (conj (D_Stmwg.entry_launch_ok_C_of inp sp brk mbase rdraw Hab Hlau)
                 (D_Stmwg.main_entry_C_of inp mbase _ sp rdraw tid regs mem Hab ME)))
           Hfit Hlen Hrd).
Qed.

(** On every valid entry of the plain build and every valid input whose argv has
    not two entries, no configuration of the run is refused by the budget, whatever
    the spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.varnish.esi_parse_fuzzer.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.varnish.esi_parse_fuzzer.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rdraw] inp Hen Hinp Hlen cfg lim.
  pose proof (valid_input_va_size _ Hinp) as Hv.
  unfold OSSVerify.varnish.esi_parse_fuzzer.Images.plain in Hen.
  rewrite (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfit & Hlau).
  pose proof (valid_input_argv _ Hinp) as Hva. pose proof (valid_input_envp _ Hinp) as Hve.
  pose proof (valid_input_abort_terminal _ Hinp) as Hab.
  pose proof (valid_input_channel_reader _ Hinp) as Hrd. pose proof (valid_input_launch _ Hinp) as Hvl.
  (* LPS 727298f3: [Run.run_scfg_budget_refused] reads the run against
     [run_segments Plain.M.loaded_segments inp sp mbase] (the binary's segments with the
     run's vDSO pair appended) and from the start configuration over that list, while
     [usage_rzb] is a walk over the binary's own segments.  [Rzb.rzb_run_init] lifts it;
     [vdso_image Plain.M.loaded_segments = None] by computation. *)
  exact (rzb_never_refused_cfg _ cfg _ _
           (rzb_run_init Plain.M.loaded_segments inp sp mbase
              Plain.M.init_pc Plain.M.phdrs brk rdraw lim _ eq_refl
              (usage_rzb sp brk mbase rdraw lim inp Hsp Hbrk Hva Hve Hfit Hab Hrd Hvl Hlau Hlen))).
Qed.

(** An entry of the plain build at [Premises.witness_input false], the entry
    [Premises.valid_input_entry] gives for it, at which the budget refuses
    nothing, whatever the configuration and the limit. *)
Lemma plain_witness_entry : exists en,
  valid_entry OSSVerify.varnish.esi_parse_fuzzer.Images.plain en (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.varnish.esi_parse_fuzzer.Images.plain lim en
      (Premises.witness_input false).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.varnish.esi_parse_fuzzer.Images.plain
              (Premises.witness_input false)
              OSSVerify.varnish.esi_parse_fuzzer.Images.plain_wf Premises.witness_valid_input) as [en Hen].
  exists en. split; [exact Hen |].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** The plain build's budget premise holds together with its entry and input
    premises: at [Premises.witness_input false] and the entry
    [Premises.valid_input_entry] gives for it, at the configuration and limit of
    [ubsan_agrees]. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.varnish.esi_parse_fuzzer.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_witness_entry as (en & Hen & Hnr).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | apply Hnr]].
Qed.

(** The three agreement statements: an entry of the plain build and one of the
    sanitizer build on the same input [Premises.witness_input false] (the pair
    [Premises.agrees_in_premises] builds, constructed here so that the input stays
    the witness input), with the budget premise from [plain_witness_entry]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
  valid_entry OSSVerify.varnish.esi_parse_fuzzer.Images.plain en_plain (Premises.witness_input false) /\
  valid_entry san en_san (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.varnish.esi_parse_fuzzer.Images.plain lim en_plain
      (Premises.witness_input false).
Proof.
  intros san Hwf.
  destruct plain_witness_entry as (en_plain & Hep & Hnr).
  destruct (Premises.valid_input_entry san (Premises.witness_input false) Hwf Premises.witness_valid_input)
    as [en_san Hes].
  exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_esi_parse_fuzzer_ubsan] proves, at
    entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.varnish.esi_parse_fuzzer.Images.plain en_plain inp /\
  valid_entry OSSVerify.varnish.esi_parse_fuzzer.Images.ubsan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.plain
      Budgets.Standard.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.plain
      Budgets.Standard.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.ubsan
      Budgets.Standard.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.varnish.esi_parse_fuzzer.Images.ubsan
              OSSVerify.varnish.esi_parse_fuzzer.Images.ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Theorems.strong_universal_error_free_esi_parse_fuzzer_ubsan
            : OSSVerify.varnish.esi_parse_fuzzer.Statements.ubsan_agrees)
           ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_esi_parse_fuzzer_asan] proves, at
    entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.varnish.esi_parse_fuzzer.Images.plain en_plain inp /\
  valid_entry OSSVerify.varnish.esi_parse_fuzzer.Images.asan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.asan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.varnish.esi_parse_fuzzer.Images.asan
              OSSVerify.varnish.esi_parse_fuzzer.Images.asan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Theorems.strong_universal_error_free_esi_parse_fuzzer_asan
            : OSSVerify.varnish.esi_parse_fuzzer.Statements.asan_agrees)
           ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_esi_parse_fuzzer_both] proves, at
    entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.varnish.esi_parse_fuzzer.Images.plain en_plain inp /\
  valid_entry OSSVerify.varnish.esi_parse_fuzzer.Images.asan_ubsan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.asan_ubsan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.varnish.esi_parse_fuzzer.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.varnish.esi_parse_fuzzer.Images.asan_ubsan
              OSSVerify.varnish.esi_parse_fuzzer.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Theorems.strong_universal_error_free_esi_parse_fuzzer_both
            : OSSVerify.varnish.esi_parse_fuzzer.Statements.asan_ubsan_agrees)
           ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.
