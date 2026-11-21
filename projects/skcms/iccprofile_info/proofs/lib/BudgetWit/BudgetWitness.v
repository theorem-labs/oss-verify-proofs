(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Info/RefMain.v's ref_realizes_spec and the argc <> 2 branch of Info/RefDriver.v's ref_main_phase, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the four statements whose budget premise is on the plain build. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the witness reads the launch facts and the channel reader from its premises, its walks carry the launch's vDSO run (vdso_run_init), and it lifts the walk to the run's segments (rzb_run_init). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.Core Require Images.
From OSSVerify.skcms.iccprofile_info Require Images Statements.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import Amb PropExec ShapeAlg Spec RefStartup.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefMain.
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
From OSSVerify.Proofs.skcms.iccprofile_info.lib Require Theorems.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts Require HaltsTops.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.BudgetWit Require Import Rzb RefStartupB RefUsageB.
Import ListNotations.
Unset Lia Cache.
#[local] Existing Instance PropExec.fp0.
Open Scope Z_scope.

(** * skcms / iccprofile_info: the budget premise on the plain build holds together with the other premises

    Four statements of [Statements] carry a budget premise on the plain build,
    [~ run_scfg_budget_refused cfg Images.plain lim en inp]:
    - [plain_halts] ([halts_within_budget]), at [forced_only_cfg] and
      [Budgets.Standard.lim_source];
    - [ubsan_agrees] ([agrees_in]), at [Env.alloc_forced_only] and
      [Budgets.Standard.lim_source];
    - [asan_agrees] and [asan_ubsan_agrees] ([agrees_in]), at
      [Env.alloc_forced_only] and [Budgets.Asan.lim_source].
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

    The proof is the released proof of that path ([Info.RefStartup.ref_startup],
    then [Info.RefDriver]'s [RefUsage.ref_usage_w], the argc <> 2 branch of
    [RefDriver.ref_main_phase]) restated over [BudgetWit.Rzb.rzb], the released
    [Info.ShapeAlg.realizes] with a no-allocation check at each node
    ([BudgetWit.Rzb] says why [realizes] itself cannot carry the fact).
    [usage_rzb] is that walk; [Rzb.rzb_never_refused_cfg] turns it into the
    budget premise, for every spurious-failure configuration and every limit
    ([usage_never_refused]).  [plain_budget_witness] is [plain_halts]'s three
    premises at one entry and one input.  Each [<statement>_not_vacuous] gives the
    premises of one of the four statements at one input to the released proof of
    that statement (the term its [proofs/<statement>/Proof.v] is), so the
    statement's conclusion holds at a point that meets all its premises, with no
    hypothesis left. *)

(** [Info.RefMain.ref_realizes_spec] with the argc <> 2 branch of
    [Info.RefDriver.ref_main_phase] in place of the whole main phase, over [rzb]:
    start-up ([RefStartupB.ref_startup_b]), then [main]'s usage path
    ([RefUsageB.ref_usage_w_b]). *)
Lemma usage_rzb : forall sp brk mbase (rnd : EntryDraw) lim inp,
  valid_sp sp -> valid_brk Plain.M.loaded_segments brk ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (* LPS 727298f3: the start-up walk reads the launch ([RefStartupB.ref_startup_b]), and the
     usage line's writev needs the channel reader (LPS #38), as [Info.RefMain.ref_realizes_spec]
     has them.  [usage_never_refused] below proves all three from [valid_entry] and
     [valid_input]. *)
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  in_channel_reader inp = true ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  (length (in_argv inp) <> 2)%nat ->
  rzb Plain.M.loaded_segments
      (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd lim inp)
      (t_die (msg_usage (hd [] (in_argv inp))) (in_fs inp)).
Proof.
  intros sp brk mbase rnd lim inp Hsp Hbrk Hva Hve Hvl Hlau Hrdr Hfit Hlen.
  (* the walks' ambient carries the launch's vDSO run, as in [Info.RefMain.ref_realizes_spec];
     [RefMain.main_entry_amb_of] carries [main_entry] over to the ambient's input *)
  pose proof (RefMain.main_entry_amb_of sp inp mbase rnd) as MEC.
  destruct inp as [argv envp ifs sin uid gid groups net nofile sigmask hwc abt vsz urnd tmp kb efn rdr sdef sterm].
  apply (ref_startup_b sp brk mbase rnd lim _ _ Hsp Hbrk Hva Hve Hvl Hlau).
  intros tid regs mem Htid ME.
  exact (@RefUsageB.ref_usage_w_b _
           (amb_set_vdso (amb_of (mkProcInput_full argv envp ifs sin uid gid groups net nofile sigmask hwc abt vsz
                                    urnd tmp kb efn rdr sdef sterm))
                         (Vdso.vdso_run_init (ed_vdso rnd)))
           sp argv envp tid rnd regs mem brk mbase (fs_seed_tmp ifs tmp) sin lim Hva Hve Hsp Htid Hfit
           (MEC tid regs mem (Vdso.vdso_run_init (ed_vdso rnd)) ME) Hvl Hlau Hlen Hrdr).
Qed.

(** On every valid entry of the plain build and every valid input whose argv has
    not two entries, no configuration of the run is refused by the budget, whatever
    the spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.skcms.iccprofile_info.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.skcms.iccprofile_info.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp Hlen cfg lim.
  pose proof (valid_input_va_size _ Hinp) as Hv.
  unfold OSSVerify.skcms.iccprofile_info.Images.plain in Hen.
  rewrite (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfit & Hlau).
  pose proof (valid_input_launch _ Hinp) as Hvl.
  pose proof (valid_input_channel_reader _ Hinp) as Hrdr.
  destruct Hinp as (Hva & Hve & _).
  (* LPS 08b1429: [Run.run_scfg_budget_refused] reads the run against
     [run_segments Plain.M.loaded_segments inp sp mbase], from the start configuration over
     that list, while [usage_rzb] walks the binary's own segments; [Rzb.rzb_run_init] lifts
     it, as [Info.RomStable.run_init] lifts a [realizes] walk.  [vdso_image] of the binary's
     segments is [None] by computation. *)
  exact (rzb_never_refused_cfg _ cfg _ _
           (rzb_run_init Plain.M.loaded_segments inp sp mbase Plain.M.init_pc Plain.M.phdrs brk rnd lim _ eq_refl
              (usage_rzb sp brk mbase rnd lim inp Hsp Hbrk Hva Hve Hvl Hlau Hrdr Hfit Hlen))).
Qed.

(** An entry of the plain build at [Premises.witness_input false], the entry
    [Premises.valid_input_entry] gives for it, at which the budget refuses
    nothing, whatever the configuration and the limit. *)
Lemma plain_witness_entry : exists en,
  valid_entry OSSVerify.skcms.iccprofile_info.Images.plain en (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.skcms.iccprofile_info.Images.plain lim en (Premises.witness_input false).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.skcms.iccprofile_info.Images.plain (Premises.witness_input false)
              OSSVerify.skcms.iccprofile_info.Images.plain_wf Premises.witness_valid_input) as [en Hen].
  exists en. split; [exact Hen |].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** [plain_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.skcms.iccprofile_info.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.skcms.iccprofile_info.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_witness_entry as (en & Hen & Hnr).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | apply Hnr]].
Qed.

(** [Statements.plain_halts], which the released
    [Halts.HaltsTops.halts_skcms_iccprofile_info_plain] proves, at an entry and an
    input that meet all three of its premises: its conclusion holds there with no
    hypothesis left. *)
Theorem plain_halts_not_vacuous :
  exists en inp, valid_entry OSSVerify.skcms.iccprofile_info.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.skcms.iccprofile_info.Images.plain
      Budgets.Standard.lim_source en inp /\
  must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.skcms.iccprofile_info.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact ((OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.HaltsTops.halts_skcms_iccprofile_info_plain
            : OSSVerify.skcms.iccprofile_info.Statements.plain_halts) en inp Hen Hinp Hnr).
Qed.

(** The three agreement statements: an entry of the plain build and one of the
    sanitizer build on the same input [Premises.witness_input false] (the pair
    [Premises.agrees_in_premises] builds, constructed here so that the input stays
    the witness input), with the budget premise from [plain_witness_entry]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
  valid_entry OSSVerify.skcms.iccprofile_info.Images.plain en_plain (Premises.witness_input false) /\
  valid_entry san en_san (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.skcms.iccprofile_info.Images.plain lim en_plain
      (Premises.witness_input false).
Proof.
  intros san Hwf.
  destruct plain_witness_entry as (en_plain & Hep & Hnr).
  destruct (Premises.valid_input_entry san (Premises.witness_input false) Hwf Premises.witness_valid_input)
    as [en_san Hes].
  exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_iccprofile_info_ubsan] proves, at
    entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.skcms.iccprofile_info.Images.plain en_plain inp /\
  valid_entry OSSVerify.skcms.iccprofile_info.Images.ubsan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.plain
      Budgets.Standard.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.plain
      Budgets.Standard.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.ubsan
      Budgets.Standard.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.skcms.iccprofile_info.Images.ubsan OSSVerify.skcms.iccprofile_info.Images.ubsan_wf)
    as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.skcms.iccprofile_info.lib.Theorems.strong_universal_error_free_fuzz_iccprofile_info_ubsan
            : OSSVerify.skcms.iccprofile_info.Statements.ubsan_agrees)
           ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_iccprofile_info_asan] proves, at
    entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.skcms.iccprofile_info.Images.plain en_plain inp /\
  valid_entry OSSVerify.skcms.iccprofile_info.Images.asan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.asan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.skcms.iccprofile_info.Images.asan OSSVerify.skcms.iccprofile_info.Images.asan_wf)
    as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.skcms.iccprofile_info.lib.Theorems.strong_universal_error_free_fuzz_iccprofile_info_asan
            : OSSVerify.skcms.iccprofile_info.Statements.asan_agrees)
           ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_iccprofile_info_both] proves, at
    entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.skcms.iccprofile_info.Images.plain en_plain inp /\
  valid_entry OSSVerify.skcms.iccprofile_info.Images.asan_ubsan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.asan_ubsan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.skcms.iccprofile_info.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.skcms.iccprofile_info.Images.asan_ubsan
              OSSVerify.skcms.iccprofile_info.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.skcms.iccprofile_info.lib.Theorems.strong_universal_error_free_fuzz_iccprofile_info_both
            : OSSVerify.skcms.iccprofile_info.Statements.asan_ubsan_agrees)
           ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.
