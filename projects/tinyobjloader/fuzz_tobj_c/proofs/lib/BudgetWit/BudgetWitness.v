(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Theorems.v: adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the three statements whose budget premise is on the plain build there. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.tinyobjloader.fuzz_tobj_c Require Images Statements.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitLayout.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require Theorems.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.BudgetWit Require TopB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(** * tinyobjloader / fuzz_tobj_c: the budget premise on the plain build holds together with the other premises

    Three proved statements of [Statements] carry a budget premise on the plain build,
    [~ run_scfg_budget_refused Env.alloc_forced_only Images.plain lim en inp], all of
    the shape [agrees_in_abort_modelled]:
    - [ubsan_agrees], at [Budgets.Standard.lim_source];
    - [asan_agrees] and [asan_ubsan_agrees], at [Budgets.Asan.lim_source].
    ([plain_halts] puts its budget premise on [Images.plain] too, at [forced_only_cfg];
    it is not proved on main, so there is nothing to tie off; [plain_budget_witness]
    gives its three premises together.)
    A theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image and leaves the budget premise, which reads the run; this
    file gives it for this build, for every configuration and every limit.

    The input is [Premises.witness_input true] (the abort-modelled shape's
    input; [witness_input false] for [plain_budget_witness]): one empty argument
    (so argc = 1), no environment, an empty file system.  With argc <> 2 the
    driver's [main] writes its usage line to fd 2 and exits with status 2.  On
    that path the program makes three kinds of system call: set_tid_address (96)
    in musl's start-up, writev (66) for the line, exit or exit_group (93, 94).
    None is an allocation call (brk 214, mremap 216, mmap 222, mprotect 226), and
    no mapping is lazy, so no configuration the run reaches is refused by the
    budget.  This shows the budget premise satisfiable on the usage path, not yet
    on an input that reaches [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path in the Fw safety framework
    ([P/Init.v init_smatch_P], [P/Start.v start_sum_P], the argc <> 2 branch of
    [P/Top.v main_safe], [P/Drv_usage__G3.v usage_safe]), run again for a
    stronger world predicate, [BudgetWit.NoAlloc.okB]: the released target
    obligation, no budget refusal at the world, and no pending allocation call
    there.  The released walk is generic in its world predicate but asks for it
    at a pending system call of any number, where [okB] does not hold; the
    copies [BudgetWit.StartB], [BudgetWit.UsageB] and [BudgetWit.SysNA] ask for it
    only at a call number that is not an allocation call, and each syscall site
    discharges that from the number it pins.  The walk is over the filtered step
    at [Env.alloc_forced_only]; [NoAlloc.okB_never_refused] lifts it to the
    unfiltered run, since no step from a configuration whose pending call is not
    an allocation call is filtered out.  [TopB.top_never_refused] is the result;
    [usage_never_refused] states it as the budget premise. *)

(** On every valid entry of the plain build and every valid input (either reading
    of abort) whose argv has not two entries, no configuration of the run is refused
    by the budget, whatever the spurious-failure configuration and whatever the
    limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain en inp -> valid_input_either inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain lim en inp.
Proof.
  intros [sp brk mb draw] inp Hen Hinp Hlen cfg lim Hr.
  pose proof (InitLayout.valid_entry48_of_input_either _ _ _ Hinp Hen) as Hen48.
  exact (TopB.top_never_refused sp brk mb draw lim inp Hen48 Hinp Hlen
           (run_scfg_budget_refused_sub cfg OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain lim _ inp Hr)).
Qed.

(** An entry of the plain build at [Premises.witness_input true], the entry
    [Premises.valid_input_abort_entry] gives for it, at which the budget refuses
    nothing, whatever the configuration and the limit. *)
Lemma plain_witness_entry : exists en,
  valid_entry OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain en (Premises.witness_input true) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
      lim en (Premises.witness_input true).
Proof.
  destruct (Premises.valid_input_abort_entry OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
    (Premises.witness_input true) OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain_wf
    Premises.witness_valid_input_abort) as [en Hen].
  exists en. split; [exact Hen |]. intros cfg lim.
  apply (usage_never_refused en _ Hen
    (valid_input_either_of_valid_input_abort _ Premises.witness_valid_input_abort)).
  cbn. discriminate.
Qed.

(** The three premises of the [halts_within_budget] shape on the plain build hold
    together, at [Premises.witness_input false] and the entry
    [Premises.valid_input_entry] gives for it.  ([plain_halts] has that shape and is
    not proved on main; this is its premise, not a tie-off.) *)
Theorem plain_budget_witness :
  exists en inp,
    valid_entry OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain en inp /\ valid_input inp /\
    ~ run_scfg_budget_refused forced_only_cfg OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
        Budgets.Standard.lim_source en inp.
Proof.
  destruct (Premises.valid_input_entry OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
    (Premises.witness_input false) OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain_wf
    Premises.witness_valid_input) as [en Hen].
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input |]].
  apply (usage_never_refused en _ Hen
    (valid_input_either_of_valid_input _ Premises.witness_valid_input)).
  cbn. discriminate.
Qed.

(** The three agreement statements: an entry of the plain build and one of the
    sanitizer build on the same input [Premises.witness_input true] (the pair
    [Premises.agrees_in_abort_modelled_premises] builds, constructed here so
    that the input stays the witness input), with the budget premise from
    [plain_witness_entry]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
    valid_entry OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain en_plain (Premises.witness_input true) /\
    valid_entry san en_san (Premises.witness_input true) /\
    forall (cfg : SpuriousCfg) (lim : Z),
    ~ run_scfg_budget_refused cfg OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
        lim en_plain (Premises.witness_input true).
Proof.
  intros san Hwf.
  destruct plain_witness_entry as (en_plain & Hep & Hnr).
  destruct (Premises.valid_input_abort_entry san (Premises.witness_input true) Hwf
    Premises.witness_valid_input_abort) as [en_san Hes].
  exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_tobj_c_ubsan] proves, at entries
    and an input that meet all four of its premises: its conclusion holds there
    with no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain en_plain inp /\
    valid_entry OSSVerify.tinyobjloader.fuzz_tobj_c.Images.ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
        Budgets.Standard.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
        Budgets.Standard.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.ubsan
        Budgets.Standard.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
                       Budgets.Standard.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.ubsan
                       Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.tinyobjloader.fuzz_tobj_c.Images.ubsan
    OSSVerify.tinyobjloader.fuzz_tobj_c.Images.ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Theorems.strong_universal_error_free_fuzz_tobj_c_ubsan
    ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr Env.alloc_forced_only Budgets.Standard.lim_source)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_tobj_c_asan] proves, at entries
    and an input that meet all four of its premises: its conclusion holds there
    with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain en_plain inp /\
    valid_entry OSSVerify.tinyobjloader.fuzz_tobj_c.Images.asan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
        Budgets.Asan.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.asan
        Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
                       Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.asan
                       Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.tinyobjloader.fuzz_tobj_c.Images.asan
    OSSVerify.tinyobjloader.fuzz_tobj_c.Images.asan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Theorems.strong_universal_error_free_fuzz_tobj_c_asan
    ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr Env.alloc_forced_only Budgets.Asan.lim_source)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_tobj_c_both] proves, at entries
    and an input that meet all four of its premises: its conclusion holds there
    with no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain en_plain inp /\
    valid_entry OSSVerify.tinyobjloader.fuzz_tobj_c.Images.asan_ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
        Budgets.Asan.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.asan_ubsan
        Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.plain
                       Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.tinyobjloader.fuzz_tobj_c.Images.asan_ubsan
                       Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.tinyobjloader.fuzz_tobj_c.Images.asan_ubsan
    OSSVerify.tinyobjloader.fuzz_tobj_c.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Theorems.strong_universal_error_free_fuzz_tobj_c_both
    ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr Env.alloc_forced_only Budgets.Asan.lim_source)).
Qed.
