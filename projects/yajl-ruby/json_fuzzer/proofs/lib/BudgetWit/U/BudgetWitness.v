(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from BudgetWit/BudgetWitness.v at the UBSan build: adds the budget-premise witness for the UBSan build on the argc <> 2 path, and the lemma that applies the released proof of ubsan_halts there. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.yajl_ruby.json_fuzzer Require Images Statements.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Theorems.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BudgetWit.U Require StartB.
Import ListNotations.
Open Scope Z_scope.

(** * yajl-ruby / json_fuzzer: the UBSan build meets its budget premise

    One released statement carries a budget premise on the UBSan build:
    [ubsan_halts] ([halts_within_budget], at [Budgets.Standard.lim_source] and
    [forced_only_cfg]).  (The agreement statements carry theirs on the plain
    build; [BudgetWit.BudgetWitness] ties those off.)  The premise is
    [~ run_scfg_budget_refused env Images.ubsan lim en inp].  A theorem whose
    premises never hold together proves nothing.  [OSSVerify.Core.Premises]
    gives the entry and input premises for every well-formed image and leaves
    the budget premise, which reads the run; this file gives it for this build,
    for every configuration and every limit.

    The input is [Premises.witness_input false]: one empty argument (so
    argc = 1), no environment, an empty file system.  With argc <> 2 the
    driver's [main] writes its usage line to fd 2 and exits with status 2.  The
    UBSan build's start-up and usage path are the plain build's at other
    addresses ([lib/U] is the plain [lib/R] proof tree at the UBSan build's
    addresses): set_tid_address (96), writev (66), exit or exit_group (93, 94),
    the exit path's stdout flush with an ioctl (29) and writev in its tree but
    nothing to write.  None is an allocation call (brk 214, mremap 216, mmap
    222, mprotect 226), and no mapping is lazy, so no configuration the run
    reaches is refused by the budget.  The input never reaches
    [LLVMFuzzerTestOneInput]: this shows [ubsan_halts] non-vacuous on the usage
    path, not yet on a fuzz input.

    The proof is [BudgetWit.BudgetWitness]'s at the UBSan build's walk:
    [BudgetWit.U.StartB], [BudgetWit.U.UsageB] and [BudgetWit.U.KioB] are the
    plain build's BudgetWit walk files made from [lib/U] instead of [lib/R]
    ([U_Startup.rstartup_spec], the argc <> 2 branch of
    [U_TopCfg.U_realizes_cfg_lim], [UDrv_A.main_usage]);
    [BudgetWit.RzbCfg] and [BudgetWit.ImplRzb] are shared, since [rzb_cfg] and
    its soundness are stated for every segment list.
    [U.StartB.ubsan_usage_never_refused_run] gives the unfiltered premise, and
    [Run.run_scfg_budget_refused_sub] the configured one for every
    configuration ([usage_never_refused]). *)

(** On every valid entry of the UBSan build and every valid input whose argv
    has not two entries, the unfiltered run is never refused by the budget,
    whatever the limit. *)
Theorem usage_never_refused_run : forall en inp,
  valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall lim : Z, ~ run_budget_refused OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan lim en inp.
Proof. exact StartB.ubsan_usage_never_refused_run. Qed.

(** ... and so no configured run is, whatever the spurious-failure
    configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan lim en inp.
Proof.
  intros en inp Hen Hinp Hlen cfg lim Hr.
  exact (usage_never_refused_run en inp Hen Hinp Hlen lim (run_scfg_budget_refused_sub cfg _ lim en inp Hr)).
Qed.

(** [ubsan_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem ubsan_budget_witness :
  exists en inp, valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan
      Budgets.Standard.lim_source en inp.
Proof.
  destruct (Premises.valid_input_entry OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan (Premises.witness_input false)
    OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan_wf Premises.witness_valid_input) as [en Hen].
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input |]].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** [Statements.ubsan_halts], which the released
    [Theorems.halts_allowed_yajl_ruby_json_fuzzer_halts_ubsan] proves, at an entry
    and an input that meet all three of its premises: its conclusion holds there
    with no hypothesis left. *)
Theorem ubsan_halts_not_vacuous :
  exists en inp, valid_entry OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan
      Budgets.Standard.lim_source en inp /\
  must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.yajl_ruby.json_fuzzer.Images.ubsan
      Budgets.Standard.lim_source en inp.
Proof.
  pose proof (OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Theorems.halts_allowed_yajl_ruby_json_fuzzer_halts_ubsan
    : OSSVerify.yajl_ruby.json_fuzzer.Statements.ubsan_halts) as HU.
  destruct ubsan_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact (HU en inp Hen Hinp Hnr).
Qed.
