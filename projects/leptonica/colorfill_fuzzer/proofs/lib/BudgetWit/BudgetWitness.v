(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 arms of O8/O8Main.v's ref_realizes_spec, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the three statements whose budget premise is on the plain build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader and launch facts proved at the launch, and the budget walk lifted to the run segment list with the vDSO). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Plain.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.leptonica.colorfill_fuzzer Require Images Statements.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require Import Amb.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import PropExec RefLayout ArgvEnv.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require O8Kit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib Require Theorems.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.BudgetWit Require Import Rzb O8KitB O8UsageB.
Import O8Kit.O8Startup O8KitB.O8StartupB O8UsageB.O8UsageB.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.

(** * leptonica / colorfill_fuzzer: the budget premise on the plain build holds together with the other premises

    Three statements of [Statements] carry a budget premise on the plain build,
    [~ run_scfg_budget_refused Env.alloc_forced_only Images.plain lim en inp]
    ([agrees_in]): [ubsan_agrees] at [Budgets.Standard.lim_source], and
    [asan_agrees] and [asan_ubsan_agrees] at [Budgets.Asan.lim_source].
    A theorem whose premises never hold together proves nothing.
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

    The proof is the released proof of that path ([O8Kit.O8Startup.ref_startup],
    the argc <> 2 arms of [O8Main.ref_realizes_spec], [O8Drv1.O8Usage.ref_usage_w])
    restated over [BudgetWit.Rzb.rzb], the released [Common.ShapeAlg.realizes]
    with a no-allocation-call check at each node ([BudgetWit.Rzb] says why
    [realizes] itself cannot carry the fact).  [usage_rzb] is that walk;
    [Rzb.rzb_never_refused_cfg] turns it into the budget premise, for every
    spurious-failure configuration and every limit ([usage_never_refused]).
    Each [<statement>_not_vacuous] gives the premises of one of the three
    statements at one input to the released proof of that statement (the term
    its [proofs/<statement>/Proof.v] is), so the statement's conclusion holds at
    a point that meets all its premises, with no hypothesis left. *)

(** The argc <> 2 arms of [O8Main.ref_realizes_spec], over [rzb], at every
    limit: start-up ([O8KitB.O8StartupB.ref_startup_b]), then [main]'s usage
    path ([O8UsageB.O8UsageB.ref_usage_w_b]).  The model is rewritten into the
    form [ref_usage_w] states it in, as [ref_realizes_spec] does.  Unlike
    [ref_realizes_spec], this needs no lower bound on the limit and none of the
    allocator pins: the usage path never reaches the allocator. *)
Lemma usage_rzb : forall sp brk mbase (draw : EntryDraw) (lim : Z) (inp : ProcInput),
  valid_sp sp ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  (* LPS 727298f3: the start-up walk reads the launch and the usage line's write needs a
     reader on fd 2, so the walk takes the three facts [O8Main.ref_realizes_spec] takes.
     [usage_never_refused] below PROVES them at the launch ([Run.valid_entry_sv48],
     [Run.valid_input_launch], [Run.valid_input_channel_reader]); nothing is assumed. *)
  in_channel_reader inp = true -> valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (length (in_argv inp) <> 2)%nat ->
  rzb Plain.M.loaded_segments
    (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase draw lim inp)
    (t_die (msg_usage (hd [] (in_argv inp))) (in_fs inp)).
Proof.
  intros sp brk mbase draw lim inp Hsp Hva Hve Hfits Hrd Hvl Hlau Hargc.
  apply (ref_startup_b sp brk mbase draw lim inp _ Hrd Hsp Hva Hve Hvl Hlau).
  intros tid regs mem Htid ME.
  rewrite <- (init_model_C_of (segments_reserved Plain.M.loaded_segments) brk mbase sp lim inp draw mbase Hrd).
  set (AMB := amb_of inp draw mbase Hrd) in *.
  remember (in_argv inp) as argv eqn:Eargv. remember (in_envp inp) as envp eqn:Eenvp.
  remember (in_fs inp) as fs0 eqn:Efs0. remember (in_stdin inp) as stdin0 eqn:Estdin0.
  clear Eargv Eenvp Efs0 Estdin0.
  exact (ref_usage_w_b sp argv envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits Hargc).
Qed.

(** On every valid entry of the plain build and every valid input whose argv has
    not two entries, no configuration of the run is refused by the budget, whatever
    the spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.leptonica.colorfill_fuzzer.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.leptonica.colorfill_fuzzer.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp Hlen cfg lim.
  pose proof (valid_input_va_size _ Hinp) as Hv.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfits & Hlau).
  pose proof (valid_input_channel_reader _ Hinp) as Hrd. pose proof (valid_input_launch _ Hinp) as Hvl.
  destruct Hinp as (Hva & Hve & _).
  (* LPS 08b1429: [Run.run_scfg_budget_refused] reads the run against
     [run_segments Plain.M.loaded_segments inp sp mbase] -- the binary's segments with the
     run's vDSO appended -- and from the start configuration over that list, while
     [usage_rzb] is a walk over the binary's own segments.  [Rzb.rzb_run_init] lifts it,
     as [Common.Cfg.RomStable.run_init] lifts the released walk in [Top.BaseColorfillAsan];
     [vdso_image Plain.M.loaded_segments = None] by computation. *)
  exact (rzb_never_refused_cfg _ cfg _ _
           (rzb_run_init Plain.M.loaded_segments inp sp mbase
              Plain.M.init_pc Plain.M.phdrs brk rnd lim _ eq_refl
              (usage_rzb sp brk mbase rnd lim inp Hsp Hva Hve Hfits Hrd Hvl Hlau Hlen))).
Qed.

(** An entry of the plain build at [Premises.witness_input false], the entry
    [Premises.valid_input_entry] gives for it, at which the budget refuses
    nothing, whatever the configuration and the limit. *)
Lemma plain_witness_entry : exists en,
  valid_entry OSSVerify.leptonica.colorfill_fuzzer.Images.plain en (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.leptonica.colorfill_fuzzer.Images.plain lim en
      (Premises.witness_input false).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.leptonica.colorfill_fuzzer.Images.plain
              (Premises.witness_input false)
              OSSVerify.leptonica.colorfill_fuzzer.Images.plain_wf Premises.witness_valid_input) as [en Hen].
  exists en. split; [exact Hen |].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** The budget premise of the plain group at one entry and one input, for both
    of its limits. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.leptonica.colorfill_fuzzer.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.plain
      Budgets.Standard.lim_source en inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.plain
      Budgets.Asan.lim_source en inp.
Proof.
  destruct plain_witness_entry as (en & Hen & Hnr).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | split; apply Hnr]].
Qed.

(** The three agreement statements: an entry of the plain build and one of the
    sanitizer build on the same input [Premises.witness_input false] (the pair
    [Premises.agrees_in_premises] builds, constructed here so that the input stays
    the witness input), with the budget premise from [plain_witness_entry]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
  valid_entry OSSVerify.leptonica.colorfill_fuzzer.Images.plain en_plain (Premises.witness_input false) /\
  valid_entry san en_san (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.leptonica.colorfill_fuzzer.Images.plain lim en_plain
      (Premises.witness_input false).
Proof.
  intros san Hwf.
  destruct plain_witness_entry as (en_plain & Hep & Hnr).
  destruct (Premises.valid_input_entry san (Premises.witness_input false) Hwf Premises.witness_valid_input)
    as [en_san Hes].
  exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_colorfill_fuzzer_ubsan] proves, at
    entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.leptonica.colorfill_fuzzer.Images.plain en_plain inp /\
  valid_entry OSSVerify.leptonica.colorfill_fuzzer.Images.ubsan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.plain
      Budgets.Standard.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.plain
      Budgets.Standard.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.ubsan
      Budgets.Standard.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.leptonica.colorfill_fuzzer.Images.ubsan
              OSSVerify.leptonica.colorfill_fuzzer.Images.ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Theorems.strong_universal_error_free_colorfill_fuzzer_ubsan
    ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_colorfill_fuzzer_asan] proves, at
    entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.leptonica.colorfill_fuzzer.Images.plain en_plain inp /\
  valid_entry OSSVerify.leptonica.colorfill_fuzzer.Images.asan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.asan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.leptonica.colorfill_fuzzer.Images.asan
              OSSVerify.leptonica.colorfill_fuzzer.Images.asan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Theorems.strong_universal_error_free_colorfill_fuzzer_asan
    ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_colorfill_fuzzer_both] proves, at
    entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.leptonica.colorfill_fuzzer.Images.plain en_plain inp /\
  valid_entry OSSVerify.leptonica.colorfill_fuzzer.Images.asan_ubsan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.asan_ubsan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.leptonica.colorfill_fuzzer.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.leptonica.colorfill_fuzzer.Images.asan_ubsan
              OSSVerify.leptonica.colorfill_fuzzer.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Theorems.strong_universal_error_free_colorfill_fuzzer_both
    ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.
