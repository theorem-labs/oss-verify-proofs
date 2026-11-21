(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from TopSides.v and PSide.v: the budget-premise witness for the plain build on the usage path, and the lemmas that apply the released proofs of the three statements whose budget premise names the plain build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start state over the run's whole input and the entry's mmap base; mo0_minv's channel-reader premise from valid_input_core; usage_unfiltered over the run's segments with the vDSO pair appended, the released tree lifted onto them by impl_lift, and usage_never_refused_run reading the run's ledger with run_segments_reserved). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs X1c2 X1c6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopLevel.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib Require TopSides PSide.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1r6 X1r7.
Require OSSVerify.speex.speex_decode_fuzzer_float.images.Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib Require Theorems.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.BudgetWit Require Import NoAlloc UsageNA.
From OSSVerify.speex.speex_decode_fuzzer_float Require Images.
From OSSVerify.Core Require Premises.
From OSSVerify.Core Require Import Shapes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(** * speex / speex_decode_fuzzer_float: the plain build's budget premise holds on the usage path

    Three statements of this harness carry the budget premise
    [~ run_scfg_budget_refused Env.alloc_forced_only Images.plain lim en inp]
    on the plain build, all three of shape [agrees_in_abort_modelled]:
    [ubsan_agrees] at [Budgets.Standard.lim_source], [asan_agrees] and
    [asan_ubsan_agrees] at [Budgets.Asan.lim_source].  A statement whose
    premises never hold together proves nothing.  [OSSVerify.Core.Premises]
    gives the entry and input premises for every well-formed image; the budget
    premise reads the run, and this file gives it for the plain build.

    The three statements quantify over [Run.valid_input_abort], so the input
    is [Premises.witness_input true]: one empty argument (argc = 1), no
    environment, an empty file system, abort() read as death by SIGABRT.  With
    argc <> 2 the driver writes its usage line to fd 2 and exits with status
    2.  On that path the program makes set_tid_address (96), writev (66),
    possibly ioctl (29) and writev on fd 1 when stdout is flushed, and exit or
    exit_group (93, 94).  None is an allocation call (brk 214, mremap 216,
    mmap 222, mprotect 226), and no mapping is lazy.

    The proof uses the released tree of the plain build ([X1r6.prog] at
    [X1r6.RSTAGE_plain], with [PSide.HP_plain] and
    [X1r7.prog_plain_model_ok_at]) unchanged: [UsageNA.usage_tree_na] shows
    that, when argc <> 2, every node of that tree is one of the four
    non-allocating nodes, and [NoAlloc.tree_never_refused] turns that into the
    budget premise, for every spurious-failure configuration and every limit
    ([usage_never_refused]).  [plain_budget_witness] is the plain build's
    three premises at one entry and one input, for every configuration and
    every limit; each [<statement>_not_vacuous] gives the premises of that
    statement together to its released proof, so its conclusion holds at
    entries and an input that meet all of them, with no hypothesis left. *)

(** [TopLevel.mo0] at one limit is [mo0] at another with the limit set. *)
Lemma mo0_setL : forall segs L lim en inp, setL L (mo0 segs lim en inp) = mo0 segs L en inp.
Proof. intros segs L lim [sp brk mb rnd] inp. reflexivity. Qed.

(** The run of the plain build reaches no budget-refused configuration under
    the unfiltered step, when argv has not two entries.  LPS 727298f3: the run
    walks the binary's segments with the kernel's vDSO pair appended
    ([Run.run_segments]) from [Run.init_machine_state] over them; the released
    tree is lifted onto those segments by [TopLevel.impl_lift], as
    [TopLevel.run_of_treeF] lifts it. *)
Lemma usage_unfiltered : forall en inp lim,
  valid_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.plain en inp -> valid_input_core inp ->
  (length (in_argv inp) <> 2)%nat ->
  ~ reaches_budget_refused (Plain.M.loaded_segments ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
      (mkCfg (init_machine_state (Plain.M.loaded_segments ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
                Plain.M.init_pc Plain.M.phdrs (en_sp en) (en_mmap_base en) (en_draw en) inp)
             (mo0 Plain.M.loaded_segments lim en inp)).
Proof.
  intros en inp lim Hen Hi Hlen.
  destruct (X1r7.prog_plain_model_ok_at SanitizerBudgets.lim_source en inp TopSides.LBUDGET_le_sanitizer Hen Hi)
    as [Hl _].
  pose proof (usage_tree_na Plain.M.loaded_segments X1r6.RSTAGE_plain (ceil_of en) (in_argv inp) Hlen) as Hna.
  pose proof (impl_lift Plain.M.loaded_segments (vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
    _ _ (ms0F Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs en inp) (vdso_nonexec _ _ _)
    (PSide.HP_plain en inp Hen Hi)) as Himpl.
  rewrite set_rom_ms0F in Himpl.
  eapply (tree_never_refused (Plain.M.loaded_segments ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)) _
            (X1r6.prog Plain.M.loaded_segments X1r6.RSTAGE_plain (ceil_of en) (in_argv inp))
            _
            (init_msF (Plain.M.loaded_segments ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
               Plain.M.init_pc Plain.M.phdrs (en_sp en) (en_mmap_base en) (en_draw en) inp)).
  - exact (init_machine_state_eqvF (Plain.M.loaded_segments ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
             Plain.M.init_pc Plain.M.phdrs (en_sp en) (en_mmap_base en) (en_draw en) inp).
  - split; [exact Himpl|].
    split.
    { apply (leaves_setL _ _ (mo0 Plain.M.loaded_segments lim en inp) SanitizerBudgets.lim_source Hna).
      rewrite mo0_setL. exact Hl. }
    split; [apply mo0_not_halted|]. split; [exact (mo0_minv _ _ _ _ (valid_input_core_reader _ Hi))|].
    exact (tsafe_na _ _ _ Hna).
  - exact Hna.
Qed.

(** On every valid entry of the plain build and every input with the core
    validity conditions whose argv has not two entries, no configuration of
    the run is refused by the budget, whatever the limit: the run-level form. *)
Theorem usage_never_refused_run : forall en inp,
  valid_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.plain en inp -> valid_input_core inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall lim : Z, ~ run_budget_refused OSSVerify.speex.speex_decode_fuzzer_float.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp Hlen lim.
  pose proof (usage_unfiltered en inp lim Hen Hinp Hlen) as H.
  destruct en as [sp brk mbase rnd].
  (* [Run.init_config] reserves [segments_reserved] of the run's segments, which
     [TopLevel.run_segments_reserved] reads as the binary's own *)
  cbn [run_budget_refused Images.plain].
  unfold init_config. rewrite (run_segments_reserved Plain.M.loaded_segments inp sp mbase).
  exact H.
Qed.

(** ...and so whatever the spurious-failure configuration
    ([Run.run_scfg_budget_refused_sub]), on every valid abort-modelled input
    whose argv has not two entries. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.plain en inp -> valid_input_abort inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.speex.speex_decode_fuzzer_float.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp Hlen cfg lim Hr.
  exact (usage_never_refused_run en inp Hen (valid_input_core_of_valid_input_abort inp Hinp) Hlen lim
           (run_scfg_budget_refused_sub cfg OSSVerify.speex.speex_decode_fuzzer_float.Images.plain lim en inp Hr)).
Qed.

(** At [Premises.witness_input true], argc = 1. *)
Lemma witness_never_refused : forall en (cfg : SpuriousCfg) (lim : Z),
  valid_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.plain en (Premises.witness_input true) ->
  ~ run_scfg_budget_refused cfg OSSVerify.speex.speex_decode_fuzzer_float.Images.plain lim en
      (Premises.witness_input true).
Proof.
  intros en cfg lim Hen.
  apply (usage_never_refused en _ Hen Premises.witness_valid_input_abort).
  cbn. discriminate.
Qed.

(** The plain build's three premises hold together, at
    [Premises.witness_input true] and the entry [Premises.valid_input_abort_entry]
    gives for it, for every configuration and every limit. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.plain en inp /\
  valid_input_abort inp /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.speex.speex_decode_fuzzer_float.Images.plain lim en inp.
Proof.
  destruct (Premises.valid_input_abort_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
    (Premises.witness_input true) OSSVerify.speex.speex_decode_fuzzer_float.Images.plain_wf
    Premises.witness_valid_input_abort) as [en Hen].
  exists en, (Premises.witness_input true).
  split; [exact Hen | split; [exact Premises.witness_valid_input_abort |]].
  intros cfg lim. exact (witness_never_refused en cfg lim Hen).
Qed.

(** [Statements.ubsan_agrees] ([agrees_in_abort_modelled Env.alloc_forced_only
    Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain
    Images.ubsan]), which the released
    [Theorems.strong_universal_error_free_speexdec_fuzzer_ubsan] proves, at
    entries and an input that meet all four of its premises. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.plain en_plain inp /\
    valid_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
        Budgets.Standard.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
                           Budgets.Standard.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.ubsan
                              Budgets.Standard.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
                                 Budgets.Standard.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.ubsan
                                 Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (Premises.valid_input_abort_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
    (Premises.witness_input true) OSSVerify.speex.speex_decode_fuzzer_float.Images.plain_wf
    Premises.witness_valid_input_abort) as [ep Hep].
  destruct (Premises.valid_input_abort_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.ubsan
    (Premises.witness_input true) OSSVerify.speex.speex_decode_fuzzer_float.Images.ubsan_wf
    Premises.witness_valid_input_abort) as [es Hes].
  pose proof (witness_never_refused ep Env.alloc_forced_only Budgets.Standard.lim_source Hep) as Hnr.
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [exact Hnr |]]]].
  exact (OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Theorems.strong_universal_error_free_speexdec_fuzzer_ubsan
           ep es _ Hep Hes Premises.witness_valid_input_abort Hnr).
Qed.

(** [Statements.asan_agrees] ([agrees_in_abort_modelled Env.alloc_forced_only
    Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain
    Images.asan]), which the released
    [Theorems.strong_universal_error_free_speexdec_fuzzer_asan] proves, at
    entries and an input that meet all four of its premises. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.plain en_plain inp /\
    valid_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.asan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
                           Budgets.Asan.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.asan
                              Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
                                 Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.asan
                                 Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (Premises.valid_input_abort_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
    (Premises.witness_input true) OSSVerify.speex.speex_decode_fuzzer_float.Images.plain_wf
    Premises.witness_valid_input_abort) as [ep Hep].
  destruct (Premises.valid_input_abort_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.asan
    (Premises.witness_input true) OSSVerify.speex.speex_decode_fuzzer_float.Images.asan_wf
    Premises.witness_valid_input_abort) as [es Hes].
  pose proof (witness_never_refused ep Env.alloc_forced_only Budgets.Asan.lim_source Hep) as Hnr.
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [exact Hnr |]]]].
  exact (OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Theorems.strong_universal_error_free_speexdec_fuzzer_asan
           ep es _ Hep Hes Premises.witness_valid_input_abort Hnr).
Qed.

(** [Statements.asan_ubsan_agrees] ([agrees_in_abort_modelled
    Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target
    Images.plain Images.asan_ubsan]), which the released
    [Theorems.strong_universal_error_free_speexdec_fuzzer_both] proves, at
    entries and an input that meet all four of its premises. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.plain en_plain inp /\
    valid_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.asan_ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
                           Budgets.Asan.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.asan_ubsan
                              Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
                                 Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.speex.speex_decode_fuzzer_float.Images.asan_ubsan
                                 Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (Premises.valid_input_abort_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.plain
    (Premises.witness_input true) OSSVerify.speex.speex_decode_fuzzer_float.Images.plain_wf
    Premises.witness_valid_input_abort) as [ep Hep].
  destruct (Premises.valid_input_abort_entry OSSVerify.speex.speex_decode_fuzzer_float.Images.asan_ubsan
    (Premises.witness_input true) OSSVerify.speex.speex_decode_fuzzer_float.Images.asan_ubsan_wf
    Premises.witness_valid_input_abort) as [es Hes].
  pose proof (witness_never_refused ep Env.alloc_forced_only Budgets.Asan.lim_source Hep) as Hnr.
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [exact Hnr |]]]].
  exact (OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Theorems.strong_universal_error_free_speexdec_fuzzer_both
           ep es _ Hep Hes Premises.witness_valid_input_abort Hnr).
Qed.
