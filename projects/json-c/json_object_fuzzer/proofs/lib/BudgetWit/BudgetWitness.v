(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Theorems.v: the budget-premise witness for the plain build and the lemmas that apply the three agreement proofs there. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.json_c.json_object_fuzzer Require Images Statements.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Theorems.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.BudgetWit Require Import UsageB.
Import ListNotations.
Open Scope Z_scope.

(** * json-c / json_object_fuzzer: the plain build meets the agreement statements' premises together

    [Statements.asan_agrees], [Statements.ubsan_agrees] and
    [Statements.asan_ubsan_agrees] are [agrees_in_abort_modelled
    Env.alloc_forced_only lim_plain lim_san Images.plain san].  Each
    quantifies over entries [en_plain], [en_san] and an input [inp] and has
    four premises: [valid_entry Images.plain en_plain inp], [valid_entry san
    en_san inp], [valid_input_abort inp] and the budget premise [~
    run_scfg_budget_refused Env.alloc_forced_only Images.plain lim_plain
    en_plain inp], with lim_plain [Budgets.Asan.lim_source] (2 GiB) for the
    two ASan pairs and [Budgets.Standard.lim_source] (16 GiB) for the UBSan
    pair.  [OSSVerify.Core.Premises] gives the first three for every
    well-formed image and leaves the fourth, which reads the run; this file
    gives the fourth.

    The input is [Premises.witness_input true]: one empty argument (so argc =
    1), no environment, an empty file system, abort declared as death by
    SIGABRT.  With argc <> 2 the driver writes its usage line to fd 2 and
    exits with status 2.  On that path the program makes three kinds of system
    call: set_tid_address (96) in musl's start-up, writev (66) for the line,
    exit or exit_group (93, 94).  None is an allocation call (brk 214, mremap
    216, mmap 222, mprotect 226), so no configuration the run reaches is
    refused by the budget.

    The proof is the released proof of that path: the start-up walk
    [QFOH.Mq1.ref_startup] (as [QHdY.drv_start_spec_lim] uses it) continued by
    the usage walk [QmsF.ref_usage_w], restated over [BudgetWit.QRjHB.realizes],
    the released [QRjH.realizes] with a budget check at each node
    ([BudgetWit.QRjHB] says why [QRjH.realizes] itself cannot carry the fact).
    [BudgetWit.UsageB.usage_realizes] is that walk;
    [BudgetWit.UsageB.usage_never_refused] turns it into the budget premise,
    for every spurious-failure configuration and every limit.

    [plain_budget_witness] is the four premises at one pair of entries and one
    input; [asan_agrees_not_vacuous], [ubsan_agrees_not_vacuous] and
    [asan_ubsan_agrees_not_vacuous] give them to the released proofs (the
    terms that each statement's [Proof.v] is), so each statement's conclusion
    holds at entries and an input that meet all its premises, with no
    hypothesis left.  Non-vacuous; shown on the usage path, not yet on a fuzz
    input. *)

(** The four premises of each agreement statement hold together, at
    [Premises.witness_input true] and the entries [Premises.valid_input_abort_entry]
    gives for it: the plain build's budget premise at both limits, and valid
    entries of all four builds on the same input. *)
Theorem plain_budget_witness :
  exists en inp,
    valid_entry OSSVerify.json_c.json_object_fuzzer.Images.plain en inp /\ valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.plain
        Budgets.Asan.lim_source en inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.plain
        Budgets.Standard.lim_source en inp /\
    (exists e, valid_entry OSSVerify.json_c.json_object_fuzzer.Images.asan e inp) /\
    (exists e, valid_entry OSSVerify.json_c.json_object_fuzzer.Images.ubsan e inp) /\
    (exists e, valid_entry OSSVerify.json_c.json_object_fuzzer.Images.asan_ubsan e inp).
Proof.
  destruct (Premises.valid_input_abort_entry OSSVerify.json_c.json_object_fuzzer.Images.plain
              (Premises.witness_input true) OSSVerify.json_c.json_object_fuzzer.Images.plain_wf
              Premises.witness_valid_input_abort) as [en Hen].
  exists en, (Premises.witness_input true).
  split; [exact Hen | split; [exact Premises.witness_valid_input_abort |]].
  split; [apply (usage_never_refused en _ Hen Premises.witness_valid_input_abort); cbn; discriminate |].
  split; [apply (usage_never_refused en _ Hen Premises.witness_valid_input_abort); cbn; discriminate |].
  split; [exact (Premises.valid_input_abort_entry _ _ OSSVerify.json_c.json_object_fuzzer.Images.asan_wf
                   Premises.witness_valid_input_abort) |].
  split; [exact (Premises.valid_input_abort_entry _ _ OSSVerify.json_c.json_object_fuzzer.Images.ubsan_wf
                   Premises.witness_valid_input_abort) |].
  exact (Premises.valid_input_abort_entry _ _ OSSVerify.json_c.json_object_fuzzer.Images.asan_ubsan_wf
           Premises.witness_valid_input_abort).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_json_object_fuzzer_asan] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry OSSVerify.json_c.json_object_fuzzer.Images.plain en_plain inp /\
    valid_entry OSSVerify.json_c.json_object_fuzzer.Images.asan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    (error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.plain
                            Budgets.Asan.lim_source en_plain inp)
     /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.asan
                               Budgets.Asan.lim_target en_san inp)
     /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.plain
                                  Budgets.Asan.lim_source en_plain inp))
                    (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.asan
                                  Budgets.Asan.lim_target en_san inp))).
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr & _ & (es & Hes) & _ & _).
  exists en, es, inp.
  split; [exact Hen | split; [exact Hes | split; [exact Hinp | split; [exact Hnr |]]]].
  exact ((OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Theorems.strong_universal_error_free_json_object_fuzzer_asan
          : OSSVerify.json_c.json_object_fuzzer.Statements.asan_agrees) en es inp Hen Hes Hinp Hnr).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_json_object_fuzzer_ubsan] proves, at
    entries and an input that meet all four of its premises. *)
Theorem ubsan_agrees_not_vacuous :
  exists (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry OSSVerify.json_c.json_object_fuzzer.Images.plain en_plain inp /\
    valid_entry OSSVerify.json_c.json_object_fuzzer.Images.ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.plain
        Budgets.Standard.lim_source en_plain inp /\
    (error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.plain
                            Budgets.Standard.lim_source en_plain inp)
     /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.ubsan
                               Budgets.Standard.lim_target en_san inp)
     /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.plain
                                  Budgets.Standard.lim_source en_plain inp))
                    (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.ubsan
                                  Budgets.Standard.lim_target en_san inp))).
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & _ & Hnr & _ & (es & Hes) & _).
  exists en, es, inp.
  split; [exact Hen | split; [exact Hes | split; [exact Hinp | split; [exact Hnr |]]]].
  exact ((OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Theorems.strong_universal_error_free_json_object_fuzzer_ubsan
          : OSSVerify.json_c.json_object_fuzzer.Statements.ubsan_agrees) en es inp Hen Hes Hinp Hnr).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_json_object_fuzzer_both] proves, at
    entries and an input that meet all four of its premises. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry OSSVerify.json_c.json_object_fuzzer.Images.plain en_plain inp /\
    valid_entry OSSVerify.json_c.json_object_fuzzer.Images.asan_ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    (error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.plain
                            Budgets.Asan.lim_source en_plain inp)
     /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.asan_ubsan
                               Budgets.Asan.lim_target en_san inp)
     /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.plain
                                  Budgets.Asan.lim_source en_plain inp))
                    (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.json_c.json_object_fuzzer.Images.asan_ubsan
                                  Budgets.Asan.lim_target en_san inp))).
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr & _ & _ & _ & (es & Hes)).
  exists en, es, inp.
  split; [exact Hen | split; [exact Hes | split; [exact Hinp | split; [exact Hnr |]]]].
  exact ((OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Theorems.strong_universal_error_free_json_object_fuzzer_both
          : OSSVerify.json_c.json_object_fuzzer.Statements.asan_ubsan_agrees) en es inp Hen Hes Hinp Hnr).
Qed.
