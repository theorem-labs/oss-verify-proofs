(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Drv/S1UsageTop.v's s1_usage_top and Drv/S1MainInst.v's use of it, over BudgetWit.SRealizes.srealizes; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the four statements whose budget premise is on the plain build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revised entry stack block, with the strings at its top, and the launch facts; the run's mmap base; the model's channel reader as a premise of the writes; the usage walk lifted to the run's segments, run_segments, from the run's own start). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer Require Images Statements.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Theorems.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ShapeAlg ArgvEnv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1Spec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit Require Import SRealizes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit.Drv Require Import S1UsageTop.
Import ListNotations.
Open Scope Z_scope.

(** * spirv-tools / spvtools_binary_parser_fuzzer: the budget premise on the plain build holds together with the other premises

    Four statements of [Statements] carry a budget premise on the plain build,
    [~ run_scfg_budget_refused cfg Images.plain lim en inp]:
    - [plain_halts] ([halts_within_budget]), at [forced_only_cfg] and
      [Budgets.Standard.lim_source];
    - [ubsan_agrees] ([agrees_in_abort_modelled]), at [Env.alloc_forced_only] and
      [Budgets.Standard.lim_source];
    - [asan_agrees] and [asan_ubsan_agrees] ([agrees_in_abort_modelled]), at
      [Env.alloc_forced_only] and [Budgets.Asan.lim_source].
    A theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image and leaves the budget premise, which reads the run; this
    file gives it for this build, for every configuration and every limit.

    The input is [Premises.witness_input false] for [plain_halts], whose input
    premise is [valid_input], and [Premises.witness_input true] for the three
    agreement statements, whose input premise is [valid_input_abort].  Either has one
    empty argument (so argc = 1), no environment and an empty file system.  With
    argc <> 2 the driver's [main] writes its usage line to fd 2 and exits with status
    2.  On that path the program makes three kinds of system call: set_tid_address
    (96) in musl's start-up, writev (66) for the line, exit or exit_group (93, 94).
    None is an allocation call (brk 214, mremap 216, mmap 222, mprotect 226), and no
    mapping is lazy, so no configuration the run reaches is refused by the budget.
    This shows the budget premise satisfiable on the usage path, not yet on an input
    that reaches [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path, [Drv/S1UsageTop.s1_usage_top] (one
    theorem from the initial configuration to the usage trace, start-up included),
    replayed over [BudgetWit.SRealizes.srealizes], the released [srealizes] with a
    no-allocation-call check at each node ([BudgetWit.SRealizes] says why the
    released relation cannot carry the fact).  [BudgetWit.Drv.S1UsageTop.s1_usage_top]
    is that walk; [SRealizes.srz_never_refused_cfg] turns it into the budget premise,
    for every spurious-failure configuration and every limit ([usage_never_refused]).
    Each [<statement>_not_vacuous] gives the premises of one of the four statements
    at one input to the released proof of that statement (the term its
    [proofs/<statement>/Proof.v] is), so the statement's conclusion holds at a point
    that meets all its premises, with no hypothesis left. *)

(** On every valid entry of the plain build and every input whose argv is valid
    and has not two entries, no configuration of the run is refused by the budget,
    whatever the spurious-failure configuration and whatever the limit. *)
Lemma usage_srz_never_refused : forall en inp,
  valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain en inp ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> in_va_size inp = Sv48 ->
  valid_launch inp -> in_channel_reader inp = true ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hva Hve Hv Hvl Hrd Hlen cfg lim.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & _ & _ & Hfits & Hlau).
  (* LPS 08b1429: the run reads the binary against [run_segments] from the run's own start;
     [SRealizes.srun_init] lifts the walk over the binary's own segments ([vdso_image] of
     them is [None] by computation). *)
  exact (srz_never_refused_cfg _ cfg _ _
           (SRealizes.srun_init M.loaded_segments inp sp mbase M.init_pc M.phdrs brk rnd lim _ eq_refl
              (s1_usage_top sp brk mbase rnd lim inp Hsp Hva Hve Hfits Hvl Hlau Hrd Hlen))).
Qed.

(** The same, for the inputs [halts_within_budget] quantifies over. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp.
  pose proof (valid_input_va_size _ Hinp) as Hv.
  pose proof (valid_input_channel_reader _ Hinp) as Hrd.
  assert (Hvl : valid_launch inp) by (clear - Hinp; unfold valid_input in Hinp; tauto).
  destruct Hinp as (Hva & Hve & _).
  exact (usage_srz_never_refused en inp Hen Hva Hve Hv Hvl Hrd).
Qed.

(** The same, for the abort-modelled inputs [agrees_in_abort_modelled] quantifies over. *)
Theorem usage_never_refused_abort : forall en inp,
  valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain en inp -> valid_input_abort inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp.
  pose proof (valid_input_abort_va_size _ Hinp) as Hv.
  assert (Hrd : in_channel_reader inp = true) by (clear - Hinp; unfold valid_input_abort in Hinp; tauto).
  assert (Hvl : valid_launch inp) by (clear - Hinp; unfold valid_input_abort in Hinp; tauto).
  destruct Hinp as (Hva & Hve & _).
  exact (usage_srz_never_refused en inp Hen Hva Hve Hv Hvl Hrd).
Qed.

(** [plain_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem plain_budget_witness :
  exists en inp,
    valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain en inp /\ valid_input inp /\
    ~ run_scfg_budget_refused forced_only_cfg OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
        Budgets.Standard.lim_source en inp.
Proof.
  destruct (Premises.valid_input_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
              (Premises.witness_input false) OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain_wf
              Premises.witness_valid_input) as [en Hen].
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input |]].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** [Statements.plain_halts], which the released
    [Theorems.halts_allowed_spirv_tools_spvtools_binary_parser_fuzzer_halts_plain]
    proves, at an entry and an input that meet all three of its premises: its
    conclusion holds there with no hypothesis left. *)
Theorem plain_halts_not_vacuous :
  exists en inp,
    valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain en inp /\ valid_input inp /\
    ~ run_scfg_budget_refused forced_only_cfg OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
        Budgets.Standard.lim_source en inp /\
    must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
        Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact (OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Theorems.halts_allowed_spirv_tools_spvtools_binary_parser_fuzzer_halts_plain
           en inp Hen Hinp Hnr).
Qed.

(** The three agreement statements: an entry of the plain build and one of the
    sanitizer build on the same input [Premises.witness_input true], with the budget
    premise at every configuration and every limit. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
    valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain en_plain (Premises.witness_input true) /\
    valid_entry san en_san (Premises.witness_input true) /\
    forall (cfg : SpuriousCfg) (lim : Z),
    ~ run_scfg_budget_refused cfg OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain lim en_plain
        (Premises.witness_input true).
Proof.
  intros san Hwf.
  destruct (Premises.valid_input_abort_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
              (Premises.witness_input true) OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain_wf
              Premises.witness_valid_input_abort) as [en_plain Hep].
  destruct (Premises.valid_input_abort_entry san (Premises.witness_input true) Hwf
              Premises.witness_valid_input_abort) as [en_san Hes].
  exists en_plain, en_san. split; [exact Hep | split; [exact Hes |]].
  intros cfg lim.
  apply (usage_never_refused_abort en_plain _ Hep Premises.witness_valid_input_abort).
  cbn. discriminate.
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_spvtools_binary_parser_fuzzer_ubsan] proves,
    at entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain en_plain inp /\
    valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
        Budgets.Standard.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
        Budgets.Standard.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan
        Budgets.Standard.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan
              OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Theorems.strong_universal_error_free_spvtools_binary_parser_fuzzer_ubsan
           ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_spvtools_binary_parser_fuzzer_asan] proves,
    at entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain en_plain inp /\
    valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.asan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
        Budgets.Asan.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.asan
        Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.asan
              OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.asan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Theorems.strong_universal_error_free_spvtools_binary_parser_fuzzer_asan
           ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_spvtools_binary_parser_fuzzer_both] proves,
    at entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain en_plain inp /\
    valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.asan_ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
        Budgets.Asan.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.asan_ubsan
        Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.asan_ubsan
              OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Theorems.strong_universal_error_free_spvtools_binary_parser_fuzzer_both
           ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.
