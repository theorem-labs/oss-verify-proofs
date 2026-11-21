(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 branch of RefMain.v's ref_realizes_spec and from Theorems.v: the budget-premise witness for the plain build and the lemmas that apply the three agreement proofs there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's validity hypotheses; the process input's new fields; the new initial stack layout; the vDSO mapping; the reader fact of the output channels; the usage walk lifted from the binary's own segments to the run's segment list). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.double_conversion.string_to_double_fuzzer Require Images Statements.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require ImgP PropExec ModelAmb Spec RefUsage Theorems.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.BudgetWit Require Rzb RefStartupB RefUsageB.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec.fx0.

(** * double-conversion / string_to_double_fuzzer: the plain build meets the agreement statements' premises together

    [Statements.asan_agrees], [Statements.ubsan_agrees] and
    [Statements.asan_ubsan_agrees] are [agrees_abort_modelled lim_plain
    lim_san Images.plain san].  Each quantifies over entries [en_plain],
    [en_san] and an input [inp] and has four premises: [valid_entry
    Images.plain en_plain inp], [valid_entry san en_san inp],
    [valid_input_abort inp] and the budget premise [~ run_budget_refused
    Images.plain lim_plain en_plain inp], with lim_plain
    [Budgets.Asan.lim_source] (2 GiB) for the two ASan pairs and
    [Budgets.Standard.lim_source] (16 GiB) for the UBSan pair.
    [OSSVerify.Core.Premises] gives the first three for every well-formed
    image and leaves the fourth, which reads the run; this file gives the
    fourth.

    The input is [Premises.witness_input true]: one empty argument (so argc =
    1), no environment, an empty file system, abort declared as death by
    SIGABRT.  With argc <> 2 the driver writes its usage line to fd 2 and
    exits with status 2.  On that path the program makes three kinds of
    system call: set_tid_address (96) in musl's start-up, writev (66) for the
    line, exit or exit_group (93, 94).  None is an allocation call (brk 214,
    mremap 216, mmap 222, mprotect 226), and no mapping is lazy
    ([m_vm_lazy = []] throughout), so no configuration the run reaches is
    refused by the budget.

    The proof is the released proof of that path, restated over
    [BudgetWit.Rzb.rzb], the released [ShapeAlg.realizes] with a grant check
    at each node ([BudgetWit.Rzb] says why [realizes] itself cannot carry the
    fact): start-up [RefStartup.ref_startup] as [RefStartupB.ref_startup_b],
    then [main]'s usage path [RefUsage.ref_usage_w] as
    [RefUsageB.ref_usage_w_b], composed as the argc <> 2 arms of
    [RefMain.ref_realizes_spec] compose them.  [usage_rzb] is that walk;
    [Rzb.rzb_never_refused] turns it into the budget premise, for every
    limit ([usage_never_refused]) and every spurious-failure configuration
    ([usage_never_refused_cfg]).

    [plain_budget_witness] is the four premises at one pair of entries and
    one input; [asan_agrees_not_vacuous], [ubsan_agrees_not_vacuous] and
    [asan_ubsan_agrees_not_vacuous] give them to the released proofs (the
    terms that each statement's [Proof.v] is), so each statement's
    conclusion holds at entries and an input that meet all its premises,
    with no hypothesis left.  Non-vacuous; shown on the usage path, not yet
    on a fuzz input. *)

(** The argc <> 2 arms of [RefMain.ref_realizes_spec], over [rzb]: start-up
    ([RefStartupB.ref_startup_b]), then [main]'s usage path
    ([RefUsageB.ref_usage_w_b]). *)
Lemma usage_rzb : forall sp brk mbase rdraw lim inp,
  valid_sp sp -> valid_brk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.loaded_segments brk ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp -> in_channel_reader inp = true ->
  (length (in_argv inp) <> 2)%nat ->
  Rzb.rzb OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.loaded_segments
    (init_config OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.loaded_segments
                 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.init_pc
                 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.phdrs
                 sp brk mbase rdraw lim inp)
    (OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec.t_die
       (OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec.msg_usage (hd [] (in_argv inp)))
       (in_fs inp)).
Proof.
  intros sp brk mbase rdraw lim inp Hsp Hbrk Hva Hve Hfits Hvl Hlau Hcr Hlen.
  (* LPS 727298f3: as RefMain.ref_realizes_spec -- the walks' ambient input carries the launch's
     vDSO run; its channel reader is the input's. *)
  set (stdin0 := OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ModelAmb.amb_set_vdso
                   (OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ModelAmb.amb_of inp)
                   (Vdso.vdso_run_init (ed_vdso rdraw))).
  assert (Hcr0 : OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ModelAmb.ia_channel_reader stdin0 = true)
    by exact Hcr.
  change (init_config OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.loaded_segments
            OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.init_pc
            OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.phdrs
            sp brk mbase rdraw lim inp)
    with (init_config OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.loaded_segments
            OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.init_pc
            OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.phdrs
            sp brk mbase rdraw lim
            (OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ModelAmb.mkProcInputA
               (in_argv inp) (in_envp inp) (in_fs inp) stdin0)).
  assert (Hvl' : valid_launch (OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ModelAmb.mkProcInputA
                                 (in_argv inp) (in_envp inp) (in_fs inp) stdin0)) by exact Hvl.
  assert (Hlau' : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw)
                    (OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ModelAmb.mkProcInputA
                       (in_argv inp) (in_envp inp) (in_fs inp) stdin0)) by exact Hlau.
  clear Hvl Hlau. rename Hvl' into Hvl. rename Hlau' into Hlau.
  apply (RefStartupB.ref_startup_b sp brk mbase rdraw lim
           (OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ModelAmb.mkProcInputA
              (in_argv inp) (in_envp inp) (in_fs inp) stdin0));
    [exact Hsp | exact Hbrk | exact Hva | exact Hve | exact Hvl | exact Hlau |].
  intros tid regs mem Htid ME.
  exact (RefUsageB.ref_usage_w_b sp (in_argv inp) (in_envp inp) rdraw tid regs mem brk mbase (in_fs inp) stdin0 lim
           Hva Hve Hsp Hfits Htid ME Hvl Hlau Hlen Hcr0).
Qed.

(** On every valid entry of the plain build and every abort-modelled input
    whose argv has not two entries, no configuration of the run is refused
    by the budget, whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain en inp -> valid_input_abort inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (lim : Z),
  ~ run_budget_refused OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp Hlen lim.
  pose proof (valid_input_abort_va_size _ Hinp) as Hv.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfits & Hlau).
  destruct Hinp as (Hva & Hve & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvl & Hcr & _).
  (* LPS 727298f3: [Run.run_budget_refused] reads the run against
     [run_segments ImgP.M.loaded_segments inp sp mbase] -- the binary's segments with the run's
     vDSO appended -- and from the start configuration over that list, while [usage_rzb] is a
     walk over the binary's own segments.  [Rzb.rzb_run_init] lifts it, as
     [RomStable.run_init] lifts a [realizes] walk; [vdso_image ImgP.M.loaded_segments = None]
     by computation. *)
  exact (Rzb.rzb_never_refused _ _ _
           (Rzb.rzb_run_init OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.loaded_segments
              inp sp mbase
              OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.init_pc
              OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ImgP.M.phdrs
              brk rnd lim _ eq_refl
              (usage_rzb sp brk mbase rnd lim inp Hsp Hbrk Hva Hve Hfits Hvl Hlau Hcr Hlen))).
Qed.

(** The same under every spurious-failure configuration
    ([Run.run_scfg_budget_refused]). *)
Theorem usage_never_refused_cfg : forall en inp,
  valid_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain en inp -> valid_input_abort inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp Hlen cfg lim Hr.
  exact (usage_never_refused en inp Hen Hinp Hlen lim
           (run_scfg_budget_refused_sub cfg _ lim en inp Hr)).
Qed.

(** The four premises of each agreement statement hold together, at
    [Premises.witness_input true] and the entries
    [Premises.valid_input_abort_entry] gives for it: the plain build's
    budget premise at both limits, and valid entries of all four builds on
    the same input. *)
Theorem plain_budget_witness :
  exists en inp,
    valid_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain en inp /\ valid_input_abort inp /\
    ~ run_budget_refused OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
        Budgets.Asan.lim_source en inp /\
    ~ run_budget_refused OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
        Budgets.Standard.lim_source en inp /\
    (exists e, valid_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.asan e inp) /\
    (exists e, valid_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.ubsan e inp) /\
    (exists e, valid_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.asan_ubsan e inp).
Proof.
  destruct (Premises.valid_input_abort_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
              (Premises.witness_input true) OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain_wf
              Premises.witness_valid_input_abort) as [en Hen].
  exists en, (Premises.witness_input true).
  split; [exact Hen | split; [exact Premises.witness_valid_input_abort |]].
  split; [apply (usage_never_refused en _ Hen Premises.witness_valid_input_abort); cbn; discriminate |].
  split; [apply (usage_never_refused en _ Hen Premises.witness_valid_input_abort); cbn; discriminate |].
  split; [exact (Premises.valid_input_abort_entry _ _ OSSVerify.double_conversion.string_to_double_fuzzer.Images.asan_wf
                   Premises.witness_valid_input_abort) |].
  split; [exact (Premises.valid_input_abort_entry _ _ OSSVerify.double_conversion.string_to_double_fuzzer.Images.ubsan_wf
                   Premises.witness_valid_input_abort) |].
  exact (Premises.valid_input_abort_entry _ _ OSSVerify.double_conversion.string_to_double_fuzzer.Images.asan_ubsan_wf
           Premises.witness_valid_input_abort).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_string_to_double_fuzzer_asan]
    proves, at entries and an input that meet all four of its premises: its
    conclusion holds there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain en_plain inp /\
    valid_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.asan en_san inp /\
    valid_input_abort inp /\
    ~ run_budget_refused OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    (error_free_unkilled (run OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
                            Budgets.Asan.lim_source en_plain inp)
     /\ error_free_unkilled (run OSSVerify.double_conversion.string_to_double_fuzzer.Images.asan
                               Budgets.Asan.lim_target en_san inp)
     /\ trace_equiv (bh_traces (run OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
                                  Budgets.Asan.lim_source en_plain inp))
                    (bh_traces (run OSSVerify.double_conversion.string_to_double_fuzzer.Images.asan
                                  Budgets.Asan.lim_target en_san inp))).
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr & _ & (es & Hes) & _ & _).
  exists en, es, inp.
  split; [exact Hen | split; [exact Hes | split; [exact Hinp | split; [exact Hnr |]]]].
  exact ((OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Theorems.strong_universal_error_free_string_to_double_fuzzer_asan
          : OSSVerify.double_conversion.string_to_double_fuzzer.Statements.asan_agrees) en es inp Hen Hes Hinp Hnr).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_string_to_double_fuzzer_ubsan]
    proves, at entries and an input that meet all four of its premises. *)
Theorem ubsan_agrees_not_vacuous :
  exists (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain en_plain inp /\
    valid_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_budget_refused OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
        Budgets.Standard.lim_source en_plain inp /\
    (error_free_unkilled (run OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
                            Budgets.Standard.lim_source en_plain inp)
     /\ error_free_unkilled (run OSSVerify.double_conversion.string_to_double_fuzzer.Images.ubsan
                               Budgets.Standard.lim_target en_san inp)
     /\ trace_equiv (bh_traces (run OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
                                  Budgets.Standard.lim_source en_plain inp))
                    (bh_traces (run OSSVerify.double_conversion.string_to_double_fuzzer.Images.ubsan
                                  Budgets.Standard.lim_target en_san inp))).
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & _ & Hnr & _ & (es & Hes) & _).
  exists en, es, inp.
  split; [exact Hen | split; [exact Hes | split; [exact Hinp | split; [exact Hnr |]]]].
  exact ((OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Theorems.strong_universal_error_free_string_to_double_fuzzer_ubsan
          : OSSVerify.double_conversion.string_to_double_fuzzer.Statements.ubsan_agrees) en es inp Hen Hes Hinp Hnr).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_string_to_double_fuzzer_both]
    proves, at entries and an input that meet all four of its premises. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain en_plain inp /\
    valid_entry OSSVerify.double_conversion.string_to_double_fuzzer.Images.asan_ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_budget_refused OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    (error_free_unkilled (run OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
                            Budgets.Asan.lim_source en_plain inp)
     /\ error_free_unkilled (run OSSVerify.double_conversion.string_to_double_fuzzer.Images.asan_ubsan
                               Budgets.Asan.lim_target en_san inp)
     /\ trace_equiv (bh_traces (run OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
                                  Budgets.Asan.lim_source en_plain inp))
                    (bh_traces (run OSSVerify.double_conversion.string_to_double_fuzzer.Images.asan_ubsan
                                  Budgets.Asan.lim_target en_san inp))).
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr & _ & _ & _ & (es & Hes)).
  exists en, es, inp.
  split; [exact Hen | split; [exact Hes | split; [exact Hinp | split; [exact Hnr |]]]].
  exact ((OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Theorems.strong_universal_error_free_string_to_double_fuzzer_both
          : OSSVerify.double_conversion.string_to_double_fuzzer.Statements.asan_ubsan_agrees) en es inp Hen Hes Hinp Hnr).
Qed.
