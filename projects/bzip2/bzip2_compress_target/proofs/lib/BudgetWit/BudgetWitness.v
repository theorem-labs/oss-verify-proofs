(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 arms of S0Main.v's ref_realizes_spec, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the three statements whose budget premise is on the plain build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader and launch facts proved at the launch, the budget walk lifted to the run segment list with the vDSO, and the plain S0MainEntry named in full). *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ModelAmb.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Plain.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.bzip2.bzip2_compress_target Require Images Statements.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW ShapeAlg Spec S0Startup.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Theorems.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require S0MainEntry.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.BudgetWit Require Import Rzb S0StartupB S0UsageB.
Import ListNotations.

(** * bzip2 / bzip2_compress_target: the budget premise on the plain build holds together with the other premises

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

    The proof is the released proof of that path ([S0Startup.ref_startup], the
    argc <> 2 arms of [S0Main.ref_realizes_spec], [S0Usage.ref_usage_w]) restated
    over [BudgetWit.Rzb.rzb], the released [ShapeAlg.realizes] with a
    no-allocation-call check at each node ([BudgetWit.Rzb] says why [realizes]
    itself cannot carry the fact).  [usage_rzb] is that walk;
    [Rzb.rzb_never_refused_cfg] turns it into the budget premise, for every
    spurious-failure configuration and every limit ([usage_never_refused]).
    Each [<statement>_not_vacuous] gives the premises of one of the three
    statements at one input to the released proof of that statement (the term
    its [proofs/<statement>/Proof.v] is), so the statement's conclusion holds at
    a point that meets all its premises, with no hypothesis left. *)

(** The usage walk is stated under the two classes the released library
    threads through it ([ACeil], [RunW]); the budget premise does not mention
    them, so any instances do. *)
#[local] Instance bw_aceil : ACeil := aceil_of_sp 0.
#[local] Instance bw_runw : RunW := mkRunW (Z_to_bv 64 0) (Z_to_bv 64 0).

(** The argc <> 2 arms of [S0Main.ref_realizes_spec], over [rzb], at every
    limit: start-up ([S0StartupB.ref_startup_b]), then [main]'s usage path
    ([S0UsageB.ref_usage_w_b]).  The input is rewritten into the form
    [ref_usage_w] states its model in, as [ref_realizes_spec] does. *)
Lemma usage_rzb : forall sp brk mbase (rnd : EntryDraw) (lim : Z) (inp : ProcInput),
  valid_sp sp -> valid_brk Plain.M.loaded_segments brk ->
  (* LPS 727298f3: the start-up walk reads the launch, so [S0StartupB.ref_startup_b] asks
     for the two facts [Run.valid_entry_sv48] and [Run.valid_input] supply, exactly as the
     sibling [S0Main.ref_realizes_spec] does.  They are DISCHARGED at the launch in
     [usage_never_refused] below, never assumed there. *)
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  (* and the reader, which [S0UsageB]'s walk needs because a reader-gone writev raises
     SIGPIPE at the revision.  [Run.valid_input_channel_reader] PROVES it from the
     validity premise [usage_never_refused] already has, so nothing is narrowed. *)
  in_channel_reader inp = true ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (length (in_argv inp) <> 2)%nat ->
  rzb Plain.M.loaded_segments
    (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd lim inp)
    (t_die (msg_usage (hd [] (in_argv inp))) (in_fs inp)).
Proof.
  intros sp brk mbase rnd lim
    [argv envp ifs0 sin uid0 gid groups net nofile sigmask hwc abt vsz urnd0 tmp0 kb efn rdr sdef sterm]
    Hsp Hbrk Hvl Hlau Hrdr Hfits Hva Hve Hargc.
  cbn [in_argv in_envp in_channel_reader] in *.
  change (in_fs (mkProcInput_full argv envp ifs0 sin uid0 gid groups net nofile sigmask hwc abt vsz urnd0 tmp0 kb efn rdr sdef sterm))
    with (fs_seed_tmp ifs0 tmp0) in *.
  set (stdin0 := mkAmbIn sin uid0 gid groups net nofile sigmask hwc abt vsz urnd0 kb efn rdr sdef sterm
                         (Vdso.vdso_run_init (ed_vdso rnd))).
  lazymatch goal with
  | |- rzb ?sg (init_config ?a ?b ?c ?d ?e ?f ?g ?h _) ?T =>
      change (rzb sg (init_config a b c d e f g h (mkProcInputA argv envp (fs_seed_tmp ifs0 tmp0) stdin0)) T)
  end.
  change (valid_launch (mkProcInputA argv envp (fs_seed_tmp ifs0 tmp0) stdin0)) in Hvl.
  change (entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd)
            (mkProcInputA argv envp (fs_seed_tmp ifs0 tmp0) stdin0)) in Hlau.
  change rdr with (ia_channel_reader stdin0) in Hrdr.
  set (fs0 := fs_seed_tmp ifs0 tmp0) in *. clearbody fs0. clear ifs0 tmp0.
  apply ref_startup_b; rewrite ?in_argv_A, ?in_envp_A, ?in_fs_A; try assumption.
  (* [ref_startup_b] hands back [main_entry]; [ref_usage_w_b] states its model over
     [main_launch], which packs the launch facts beside it.  Built exactly as the ported
     sibling [S0Main.ref_realizes_spec] builds it, from the two facts
     [usage_never_refused] proved at the launch.
     The module path is written out in full: this tree carries a [lib/U/S0MainEntry.v]
     twin whose [main_launch] holds the ubsan build's entry (0x13434), and the partial
     prefix [S0MainEntry.] resolves to whichever of the two was loaded last.  The plain
     build's [main_launch] (0x133fc) is the one [S0UsageB.ref_usage_w_b] is stated over
     -- [S0UsageB.v:955] imports that same full path -- and the one [ref_startup_b]
     hands back, so it is named here in a way no later [Require] can shadow. *)
  intros tid regs mem Htid ME0.
  set (hw := ia_hwcap stdin0).
  assert (ME : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0MainEntry.main_launch
                 (mkProcInputA argv envp fs0 stdin0) hw mbase sp brk rnd tid regs mem)
    by (split; [reflexivity | split; [exact Hvl | split; [exact Hlau | exact ME0]]]).
  clear ME0 Hvl Hlau.
  exact (ref_usage_w_b sp argv envp hw rnd tid regs mem brk mbase fs0 stdin0 lim
           Hva Hsp Htid ME Hrdr Hargc).
Qed.

(** On every valid entry of the plain build and every valid input whose argv has
    not two entries, no configuration of the run is refused by the budget, whatever
    the spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.bzip2.bzip2_compress_target.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.bzip2.bzip2_compress_target.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp Hlen cfg lim.
  pose proof (valid_input_va_size _ Hinp) as Hv.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfits & Hlau).
  pose proof (valid_input_launch _ Hinp) as Hvl.
  pose proof (valid_input_channel_reader _ Hinp) as Hrdr.
  destruct Hinp as (Hva & Hve & _).
  (* LPS 08b1429: [Run.run_scfg_budget_refused] reads the run against
     [run_segments Plain.M.loaded_segments inp sp mbase] -- the binary's segments with the
     run's vDSO appended -- and from the start configuration over that list, while
     [usage_rzb] is a walk over the binary's own segments.  [Rzb.rzb_run_init] lifts it,
     exactly as [Common.Cfg.RomStable.run_init] lifts the [realizes] walk of
     [ThmCompressAsan.s0_side04]; [vdso_image Plain.M.loaded_segments = None] by
     computation. *)
  exact (rzb_never_refused_cfg _ cfg _ _
           (rzb_run_init Plain.M.loaded_segments inp sp mbase
              Plain.M.init_pc Plain.M.phdrs brk rnd lim _ eq_refl
              (usage_rzb sp brk mbase rnd lim inp Hsp Hbrk Hvl Hlau Hrdr Hfits Hva Hve Hlen))).
Qed.

(** An entry of the plain build at [Premises.witness_input false], the entry
    [Premises.valid_input_entry] gives for it, at which the budget refuses
    nothing, whatever the configuration and the limit. *)
Lemma plain_witness_entry : exists en,
  valid_entry OSSVerify.bzip2.bzip2_compress_target.Images.plain en (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.bzip2.bzip2_compress_target.Images.plain lim en
      (Premises.witness_input false).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.bzip2.bzip2_compress_target.Images.plain
              (Premises.witness_input false)
              OSSVerify.bzip2.bzip2_compress_target.Images.plain_wf Premises.witness_valid_input) as [en Hen].
  exists en. split; [exact Hen |].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** The budget premise of the plain group at one entry and one input, for both
    of its limits. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.bzip2.bzip2_compress_target.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.plain
      Budgets.Standard.lim_source en inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.plain
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
  valid_entry OSSVerify.bzip2.bzip2_compress_target.Images.plain en_plain (Premises.witness_input false) /\
  valid_entry san en_san (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.bzip2.bzip2_compress_target.Images.plain lim en_plain
      (Premises.witness_input false).
Proof.
  intros san Hwf.
  destruct plain_witness_entry as (en_plain & Hep & Hnr).
  destruct (Premises.valid_input_entry san (Premises.witness_input false) Hwf Premises.witness_valid_input)
    as [en_san Hes].
  exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_bzip2_compress_target_ubsan] proves, at
    entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.bzip2.bzip2_compress_target.Images.plain en_plain inp /\
  valid_entry OSSVerify.bzip2.bzip2_compress_target.Images.ubsan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.plain
      Budgets.Standard.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.plain
      Budgets.Standard.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.ubsan
      Budgets.Standard.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.bzip2.bzip2_compress_target.Images.ubsan
              OSSVerify.bzip2.bzip2_compress_target.Images.ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Theorems.strong_universal_error_free_bzip2_compress_target_ubsan
    ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_bzip2_compress_target_asan] proves, at
    entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.bzip2.bzip2_compress_target.Images.plain en_plain inp /\
  valid_entry OSSVerify.bzip2.bzip2_compress_target.Images.asan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.asan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.bzip2.bzip2_compress_target.Images.asan
              OSSVerify.bzip2.bzip2_compress_target.Images.asan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Theorems.strong_universal_error_free_bzip2_compress_target_asan
    ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_bzip2_compress_target_both] proves, at
    entries and an input that meet all four of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.bzip2.bzip2_compress_target.Images.plain en_plain inp /\
  valid_entry OSSVerify.bzip2.bzip2_compress_target.Images.asan_ubsan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.asan_ubsan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.bzip2.bzip2_compress_target.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.bzip2.bzip2_compress_target.Images.asan_ubsan
              OSSVerify.bzip2.bzip2_compress_target.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Theorems.strong_universal_error_free_bzip2_compress_target_both
    ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.
