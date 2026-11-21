(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: adds the budget-premise witness for the plain build on the argc <> 2 path, and the lemmas that apply the released proofs of plain_halts, ubsan_agrees, asan_agrees and asan_ubsan_agrees there. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.yajl_ruby.json_fuzzer Require Images Statements.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Theorems.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BudgetWit Require StartB.
Import ListNotations.
Open Scope Z_scope.

(** * yajl-ruby / json_fuzzer: the plain build meets its budget premise

    Four released statements carry a budget premise on the plain build:
    [plain_halts] ([halts_within_budget], at [Budgets.Standard.lim_source] and
    [forced_only_cfg]) and [ubsan_agrees], [asan_agrees], [asan_ubsan_agrees]
    ([agrees_in], at [Env.alloc_forced_only], the first at
    [Budgets.Standard.lim_source], the other two at [Budgets.Asan.lim_source]).
    The premise is [~ run_scfg_budget_refused env Images.plain lim en inp].  A
    theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image and leaves the budget premise, which reads the run; this
    file gives it for this build, for every configuration and every limit,
    so one witness serves all four statements.

    The input is [Premises.witness_input false]: one empty argument (so
    argc = 1), no environment, an empty file system.  With argc <> 2 the
    driver's [main] writes its usage line to fd 2 and exits with status 2.  On
    that path the program makes three kinds of system call: set_tid_address (96)
    in musl's start-up, writev (66) for the line, exit or exit_group (93, 94);
    the exit path's stdout flush has an ioctl (29) and writev in its tree but
    nothing to write.  None is an allocation call (brk 214, mremap 216, mmap
    222, mprotect 226), and no mapping is lazy, so no configuration the run
    reaches is refused by the budget.  The input never reaches
    [LLVMFuzzerTestOneInput]: this shows the statements non-vacuous on the
    usage path, not yet on a fuzz input.

    The proof is the released proof of that path ([R_Startup.rstartup_spec],
    the argc <> 2 branch of [R_TopCfg.R_realizes_cfg_lim], [RDrv_A.main_usage])
    restated over [BudgetWit.RzbCfg.rzb_cfg] ([StartB.usage_rzb]);
    [StartB.plain_usage_never_refused_run] turns it into the unfiltered
    premise, and [Run.run_scfg_budget_refused_sub] into the configured one for
    every configuration ([usage_never_refused]).  Each [_not_vacuous] lemma
    gives the premises at one entry (one per image) and one input to the released proof
    (the term that the statement's [Proof.v] is), so the statement's
    conclusion holds there with no hypothesis left. *)

(** On every valid entry of the plain build and every valid input whose argv
    has not two entries, the unfiltered run is never refused by the budget,
    whatever the limit. *)
Theorem usage_never_refused_run : forall en inp,
  valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall lim : Z, ~ run_budget_refused OSSVerify.yajl_ruby.json_fuzzer.Images.plain lim en inp.
Proof. exact StartB.plain_usage_never_refused_run. Qed.

(** ... and so no configured run is, whatever the spurious-failure
    configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.yajl_ruby.json_fuzzer.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp Hlen cfg lim Hr.
  exact (usage_never_refused_run en inp Hen Hinp Hlen lim (run_scfg_budget_refused_sub cfg _ lim en inp Hr)).
Qed.

(** [plain_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.yajl_ruby.json_fuzzer.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct (Premises.valid_input_entry OSSVerify.yajl_ruby.json_fuzzer.Images.plain (Premises.witness_input false)
    OSSVerify.yajl_ruby.json_fuzzer.Images.plain_wf Premises.witness_valid_input) as [en Hen].
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input |]].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** [Statements.plain_halts], which the released
    [Theorems.halts_allowed_yajl_ruby_json_fuzzer_halts_plain] proves, at an entry
    and an input that meet all three of its premises. *)
Theorem plain_halts_not_vacuous :
  exists en inp, valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.yajl_ruby.json_fuzzer.Images.plain
      Budgets.Standard.lim_source en inp /\
  must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.yajl_ruby.json_fuzzer.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  pose proof (OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Theorems.halts_allowed_yajl_ruby_json_fuzzer_halts_plain
    : OSSVerify.yajl_ruby.json_fuzzer.Statements.plain_halts) as HP.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact (HP en inp Hen Hinp Hnr).
Qed.

(** An [agrees_in Env.alloc_forced_only] statement with the plain build as its
    first image, at the witness input: its four premises hold together and so
    its conclusion holds there. *)
Lemma agrees_witness : forall (san : Image) (lim_p lim_s : Z),
  (exists es, valid_entry san es (Premises.witness_input false)) ->
  agrees_in Env.alloc_forced_only lim_p lim_s OSSVerify.yajl_ruby.json_fuzzer.Images.plain san ->
  exists ep es inp,
    valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.plain ep inp /\
    valid_entry san es inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain lim_p ep inp /\
    (error_free (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain lim_p ep inp)
     /\ error_free (run_scfg Env.alloc_forced_only san lim_s es inp)
     /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain lim_p ep inp))
                    (bh_traces (run_scfg Env.alloc_forced_only san lim_s es inp))).
Proof.
  intros san lim_p lim_s [es Hs] H.
  destruct (Premises.valid_input_entry OSSVerify.yajl_ruby.json_fuzzer.Images.plain (Premises.witness_input false)
    OSSVerify.yajl_ruby.json_fuzzer.Images.plain_wf Premises.witness_valid_input) as [ep Hp].
  assert (Hnr : ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain
                  lim_p ep (Premises.witness_input false)).
  { apply (usage_never_refused ep _ Hp Premises.witness_valid_input). cbn. discriminate. }
  exists ep, es, (Premises.witness_input false).
  split; [exact Hp | split; [exact Hs | split; [exact Premises.witness_valid_input | split; [exact Hnr |]]]].
  exact (H ep es _ Hp Hs Premises.witness_valid_input Hnr).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_json_fuzzer_ubsan] proves, at entries
    and an input that meet all four of its premises. *)
Theorem ubsan_agrees_not_vacuous :
  exists ep es inp,
    valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.plain ep inp /\
    valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan es inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain
        Budgets.Standard.lim_source ep inp /\
    (error_free (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain Budgets.Standard.lim_source ep inp)
     /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan Budgets.Standard.lim_target es inp)
     /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain Budgets.Standard.lim_source ep inp))
                    (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan Budgets.Standard.lim_target es inp))).
Proof.
  exact (agrees_witness OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan Budgets.Standard.lim_source Budgets.Standard.lim_target
    (Premises.valid_input_entry _ _ OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan_wf Premises.witness_valid_input)
    (OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Theorems.strong_universal_error_free_json_fuzzer_ubsan
      : OSSVerify.yajl_ruby.json_fuzzer.Statements.ubsan_agrees)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_json_fuzzer_asan] proves, at entries
    and an input that meet all four of its premises. *)
Theorem asan_agrees_not_vacuous :
  exists ep es inp,
    valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.plain ep inp /\
    valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.asan es inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain
        Budgets.Asan.lim_source ep inp /\
    (error_free (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain Budgets.Asan.lim_source ep inp)
     /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.asan Budgets.Asan.lim_target es inp)
     /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain Budgets.Asan.lim_source ep inp))
                    (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.asan Budgets.Asan.lim_target es inp))).
Proof.
  exact (agrees_witness OSSVerify.yajl_ruby.json_fuzzer.Images.asan Budgets.Asan.lim_source Budgets.Asan.lim_target
    (Premises.valid_input_entry _ _ OSSVerify.yajl_ruby.json_fuzzer.Images.asan_wf Premises.witness_valid_input)
    (OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Theorems.strong_universal_error_free_json_fuzzer_asan
      : OSSVerify.yajl_ruby.json_fuzzer.Statements.asan_agrees)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_json_fuzzer_both] proves, at entries
    and an input that meet all four of its premises. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists ep es inp,
    valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.plain ep inp /\
    valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.asan_ubsan es inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain
        Budgets.Asan.lim_source ep inp /\
    (error_free (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain Budgets.Asan.lim_source ep inp)
     /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.asan_ubsan Budgets.Asan.lim_target es inp)
     /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.plain Budgets.Asan.lim_source ep inp))
                    (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.yajl_ruby.json_fuzzer.Images.asan_ubsan Budgets.Asan.lim_target es inp))).
Proof.
  exact (agrees_witness OSSVerify.yajl_ruby.json_fuzzer.Images.asan_ubsan Budgets.Asan.lim_source Budgets.Asan.lim_target
    (Premises.valid_input_entry _ _ OSSVerify.yajl_ruby.json_fuzzer.Images.asan_ubsan_wf Premises.witness_valid_input)
    (OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Theorems.strong_universal_error_free_json_fuzzer_both
      : OSSVerify.yajl_ruby.json_fuzzer.Statements.asan_ubsan_agrees)).
Qed.
