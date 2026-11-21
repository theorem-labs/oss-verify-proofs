(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Theorems.v and Top/AssembleP0.v: the budget-premise witness for the plain build on the usage path, and the lemmas that apply the released proofs of the three statements whose budget premise names the plain build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's input, mmap base and entry draw). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.pupnp.FuzzHttp Require Images Statements.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Segs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib Require Theorems.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.BudgetWit Require Import UsageRun.
Import ListNotations.
Open Scope Z_scope.

(** * pupnp / FuzzHttp: the plain build's budget premise holds on the usage path

    Three statements of [Statements] carry a budget premise on the plain
    build, [~ run_scfg_budget_refused Env.alloc_forced_only Images.plain lim
    en inp], all three of the shape [agrees_in]:
    - [asan_agrees] and [asan_ubsan_agrees], at [Budgets.Asan.lim_source];
    - [ubsan_agrees], at [Budgets.Standard.lim_source].
    A statement whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image; the budget premise reads the run, and this file gives
    it for the plain build, for every spurious-failure configuration and
    every limit.

    The input is [Premises.witness_input false]: one empty argument (so
    argc = 1), no environment, an empty file system.  With argc <> 2 the
    driver's [main] writes its usage line to fd 2 and exits with status 2.
    On that path the program makes set_tid_address (96) in musl's start-up,
    writev (66) for the line, possibly ioctl (29) and writev on fd 1 when
    stdout is flushed, and exit or exit_group (93, 94).  None is an
    allocation call (brk 214, mremap 216, mmap 222, mprotect 226), and no
    mapping is lazy ([Nodes.minv]).  This shows the budget premise
    satisfiable on the usage path, not yet on an input that reaches
    [LLVMFuzzerTestOneInput].

    The proof uses the released walk of that path unchanged
    ([P0.Startup.rstartup_spec], [P0.RF_main_A.main_usage], and the tree
    safety [Top.DriverModel.drv_pre_twf] that [Top.AssembleP0.p0_realizes]
    uses): [UsageRun.usage_unfiltered] shows that the unfiltered run from
    the start configuration reaches no budget-refused configuration, and
    [usage_never_refused] gives the budget premise for every configuration
    and every limit.  Each [<statement>_not_vacuous] gives the premises of
    one statement at one input to the released proof of that statement (the
    term its [proofs/<statement>/Proof.v] is), so the statement's
    conclusion holds at a point that meets all its premises, with no
    hypothesis left. *)

(** On every valid entry of the plain build and every valid input whose argv
    has not two entries, no configuration of the run is refused by the
    budget, whatever the limit: the run-level form. *)
Theorem usage_never_refused_run : forall en inp,
  valid_entry OSSVerify.pupnp.FuzzHttp.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall lim : Z, ~ run_budget_refused OSSVerify.pupnp.FuzzHttp.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp Hlen lim.
  pose proof (valid_input_va_size _ Hinp) as Hv.
  rewrite (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (VSP & VBRK & VMB & _ & LOK).
  exact (usage_unfiltered sp brk mbase rnd lim inp VSP VBRK VMB Hinp LOK Hlen).
Qed.

(** ...and so whatever the spurious-failure configuration
    ([Run.run_scfg_budget_refused_sub]). *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.pupnp.FuzzHttp.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.pupnp.FuzzHttp.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp Hlen cfg lim Hr.
  exact (usage_never_refused_run en inp Hen Hinp Hlen lim
           (run_scfg_budget_refused_sub cfg OSSVerify.pupnp.FuzzHttp.Images.plain lim en inp Hr)).
Qed.

(** An entry of the plain build at [Premises.witness_input false], the entry
    [Premises.valid_input_entry] gives for it, at which the budget refuses
    nothing, whatever the configuration and the limit. *)
Lemma plain_witness_entry : exists en,
  valid_entry OSSVerify.pupnp.FuzzHttp.Images.plain en (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.pupnp.FuzzHttp.Images.plain lim en (Premises.witness_input false).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.pupnp.FuzzHttp.Images.plain (Premises.witness_input false)
    OSSVerify.pupnp.FuzzHttp.Images.plain_wf Premises.witness_valid_input) as [en Hen].
  exists en. split; [exact Hen |].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** The budget premise of the three statements at one entry and one input. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.pupnp.FuzzHttp.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.plain
      Budgets.Asan.lim_source en inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_witness_entry as (en & Hen & Hnr).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | split; apply Hnr]].
Qed.

(** The three agreement statements: an entry of the plain build and one of
    the sanitizer build on the same input [Premises.witness_input false]
    (the pair [Premises.agrees_in_premises] builds, constructed here so that
    the input stays the witness input), with the budget premise from
    [plain_witness_entry]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
  valid_entry OSSVerify.pupnp.FuzzHttp.Images.plain en_plain (Premises.witness_input false) /\
  valid_entry san en_san (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.pupnp.FuzzHttp.Images.plain lim en_plain (Premises.witness_input false).
Proof.
  intros san Hwf.
  destruct plain_witness_entry as (en_plain & Hep & Hnr).
  destruct (Premises.valid_input_entry san (Premises.witness_input false) Hwf Premises.witness_valid_input)
    as [en_san Hes].
  exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzzhttp_asan] proves, at entries
    and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.pupnp.FuzzHttp.Images.plain en_plain inp /\
  valid_entry OSSVerify.pupnp.FuzzHttp.Images.asan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.asan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.pupnp.FuzzHttp.Images.asan OSSVerify.pupnp.FuzzHttp.Images.asan_wf)
    as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.pupnp.FuzzHttp.lib.Theorems.strong_universal_error_free_fuzzhttp_asan
    ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzzhttp_both] proves, at entries
    and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.pupnp.FuzzHttp.Images.plain en_plain inp /\
  valid_entry OSSVerify.pupnp.FuzzHttp.Images.asan_ubsan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.asan_ubsan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.pupnp.FuzzHttp.Images.asan_ubsan
    OSSVerify.pupnp.FuzzHttp.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.pupnp.FuzzHttp.lib.Theorems.strong_universal_error_free_fuzzhttp_both
    ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzzhttp_ubsan] proves, at entries
    and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.pupnp.FuzzHttp.Images.plain en_plain inp /\
  valid_entry OSSVerify.pupnp.FuzzHttp.Images.ubsan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.plain
      Budgets.Standard.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.plain
      Budgets.Standard.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.ubsan
      Budgets.Standard.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.pupnp.FuzzHttp.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.pupnp.FuzzHttp.Images.ubsan OSSVerify.pupnp.FuzzHttp.Images.ubsan_wf)
    as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.pupnp.FuzzHttp.lib.Theorems.strong_universal_error_free_fuzzhttp_ubsan
    ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.
