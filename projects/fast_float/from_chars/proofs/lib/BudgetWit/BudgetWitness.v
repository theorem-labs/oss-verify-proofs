(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from PTop.v's plain_realizes_lim with the argc <> 2 branch of plain_main in place of the whole main phase, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the four statements whose budget premise is on the plain build. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput; the launch premises valid_launch and entry_launch_ok_va; the channel-reader premise of writev; the run's segment list run_segments; RomBase.sys_rob at the system-call nodes; the launch's reservations with the vDSO pair; the conjuncts of valid_input_either). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.Core Require Images.
From OSSVerify.fast_float.from_chars Require Images Statements.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RomBase RomStable PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Spec.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Theorems.
From OSSVerify.Proofs.fast_float.from_chars.lib.BudgetWit Require Import Rzb RefStartupRzB PUsageB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(** * fast_float / from_chars: the budget premise on the plain build holds together with the other premises

    Four statements of [Statements] carry a budget premise on the plain build,
    [~ run_scfg_budget_refused cfg Images.plain lim en inp]:
    - [plain_halts] ([halts_within_budget]), at [forced_only_cfg] and
      [Budgets.Standard.lim_source];
    - [ubsan_agrees] ([agrees_in_abort_modelled]), at [Env.alloc_forced_only] and
      [Budgets.Standard.lim_source];
    - [asan_agrees] and [asan_ubsan_agrees] ([agrees_in_abort_modelled]), at
      [Env.alloc_forced_only] and [Budgets.Asan.lim_source].
    A theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image and leaves the budget premise, which reads the run; this
    file gives it for this build, for every configuration and every limit.

    The input is [Premises.witness_input b]: one empty argument (so argc = 1), no
    environment, an empty file system; [b = true] for the three abort-modelled
    agreement statements, [false] for [plain_halts].  With argc <> 2 the driver's
    [main] writes its usage line to fd 2 and exits with status 2.  On that path the
    program makes three kinds of system call: set_tid_address (96) in musl's
    start-up, writev (66) for the line and the stdio flush, exit or exit_group
    (93, 94).  None is an allocation call (brk 214, mremap 216, mmap 222,
    mprotect 226), so no configuration the run reaches is refused by the budget.
    This shows the budget premise satisfiable on the usage path, not yet on an
    input that reaches [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path ([RefStartupRz.ref_startup_rz],
    then [PUsage.usage_path], the argc <> 2 branch of [PTop.plain_main], as
    [PTop.plain_realizes_lim] composes them) restated over [BudgetWit.Rzb.rzb],
    the released [RealizesCfg.realizes_cfg] with a no-allocation check at each
    node ([BudgetWit.Rzb] says why [realizes_cfg] itself cannot carry the fact,
    and how the check also covers the steps the released index [DriverCfg.DCFG]
    filters out).  The released usage arm is stated with [DriverCfg]'s
    abbreviation [realizes segs c T := realizes_cfg segs DCFG c T], so the
    start-up and the usage arm are one relation at one configuration and need no
    bridge.  [usage_rzb] is that walk; [Rzb.rzb_never_refused] turns it into the
    budget premise for the unfiltered run, and [Run.run_scfg_budget_refused_sub]
    into the configured one, for every spurious-failure configuration and every
    limit ([usage_never_refused]).  Each [<statement>_not_vacuous] gives the
    premises of one of the four statements at one input to the released proof of
    that statement (the term its [proofs/<statement>/Proof.v] is), so the
    statement's conclusion holds at a point that meets all its premises, with no
    hypothesis left. *)

(** [PTop.plain_realizes_lim] with the argc <> 2 branch of [PTop.plain_main]
    in place of the whole main phase, over [Rzb.rzb]: start-up
    ([RefStartupRzB.ref_startup_rz_b]), then [main]'s usage path
    ([PUsageB.usage_path_b]).  The usage path needs no heap invariant, so this
    holds for every limit.

    LPS 727298f3: the start-up walk is over the run's segment list
    [run_segments Plain.M.loaded_segments inp sp mbase], and the usage path is a walk over
    the binary's own segments, lifted at the entry of [main] ([Rzb.rzb_lift_run]), as
    [PTop.plain_realizes_lim] lifts [plain_main].  The start-up walk reads the launch and the
    usage path's writev reads the reader ([valid_launch], [entry_launch_ok_va],
    [in_channel_reader]); [usage_never_refused] proves all three from its premises. *)
Lemma usage_rzb : forall sp brk mbase (rnd : EntryDraw) lim inp,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  in_channel_reader inp = true ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  (length (in_argv inp) <> 2)%nat ->
  Rzb.rzb (run_segments Plain.M.loaded_segments inp sp mbase) DCFG
    (init_config (run_segments Plain.M.loaded_segments inp sp mbase) Plain.M.init_pc Plain.M.phdrs
       sp brk mbase rnd lim inp)
    (t_die (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
  intros sp brk mbase rnd lim inp Hsp Hva Hve Hvl Hlau Hrdi Hfit Hlen.
  apply (RefStartupRzB.ref_startup_rz_b DCFG _ sp brk mbase rnd lim inp Hsp Hva Hve Hvl Hlau).
  intros tid regs mem Htid ME.
  rewrite RomStable.init_model_run_segments.
  set (md := with_tid tid (cfg_model (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs
                                        sp brk mbase rnd lim inp))).
  lazymatch goal with
  | |- Rzb.rzb _ _ (mkCfg (@PropExec.mkst ?fx ?r ?p ?m _) _) ?T =>
      change (Rzb.rzb (run_segments Plain.M.loaded_segments inp sp mbase) DCFG
                (mkCfg (RomBase.wrom (@PropExec.mkst fx r p m (PropExec.seg_rom Plain.M.loaded_segments))
                         (RomStable.seg_rom1 (run_segments Plain.M.loaded_segments inp sp mbase))) md) T)
  end.
  apply Rzb.rzb_lift_run; [reflexivity | reflexivity |].
  set (md0 := with_tid tid (init_model (segments_reserved Plain.M.loaded_segments) brk mbase sp lim inp)).
  assert (Hfs : m_fs md = in_fs inp)
    by (change (m_fs md) with (m_fs md0); unfold md0; rewrite m_fs_with_tid, m_fs_init_model; reflexivity).
  rewrite <- Hfs.
  replace (0x22638%bv : word) with (Z_to_bv 64 0x22638) by (apply bv_eq; reflexivity).
  apply (PUsageB.usage_path_b inp mbase (0x224ec : word) sp brk tid rnd regs mem md
           Hsp Hva Hve Hvl Hlau Hfit ltac:(unfold PID_MAX_ENVELOPE in Htid; lia) ME Hlen).
  - change (m_halted md) with (m_halted md0). unfold md0. rewrite m_halted_with_tid, m_halted_init_model. reflexivity.
  - reflexivity.
  - change (m_fds md) with (m_fds md0). unfold md0. rewrite m_fds_with_tid, m_fds_init_model. vm_compute. reflexivity.
  - transitivity (in_channel_reader inp); [reflexivity | exact Hrdi].
Qed.

(** On every valid entry of the plain build and every input the three agreement statements
    or [plain_halts] admit whose argv has not two entries, no configuration of the run is
    refused by the budget, whatever the spurious-failure configuration and whatever the
    limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.fast_float.from_chars.Images.plain en inp ->
  valid_input_either inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.fast_float.from_chars.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp Hlen cfg lim Hr.
  (* the conjuncts of [valid_input_either] by type, as [PTop.plain_realizes_lim] takes them *)
  assert (Hrdi : in_channel_reader inp = true)
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hva : valid_argv (in_argv inp))
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hve : valid_envp (in_envp inp))
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hvl : valid_launch inp)
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hv : in_va_size inp = Sv48)
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  unfold OSSVerify.fast_float.from_chars.Images.plain in Hen, Hr.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfit & Hlau).
  exact (Rzb.rzb_never_refused (run_segments Plain.M.loaded_segments inp sp mbase) DCFG Rzb.alloc_only_off _ _
           (usage_rzb sp brk mbase rnd lim inp Hsp Hva Hve Hvl Hlau Hrdi Hfit Hlen)
           (run_scfg_budget_refused_sub cfg _ lim _ inp Hr)).
Qed.

(** An entry of the plain build at [Premises.witness_input b], the entry
    [Premises.valid_input_entry] or [Premises.valid_input_abort_entry] gives for
    it, at which the budget refuses nothing, whatever the configuration and the
    limit. *)
Lemma plain_witness_entry : forall b, exists en,
  valid_entry OSSVerify.fast_float.from_chars.Images.plain en (Premises.witness_input b) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.fast_float.from_chars.Images.plain lim en (Premises.witness_input b).
Proof.
  intros b.
  assert (Hen : exists en, valid_entry OSSVerify.fast_float.from_chars.Images.plain en (Premises.witness_input b)).
  { destruct b.
    - exact (Premises.valid_input_abort_entry _ _ OSSVerify.fast_float.from_chars.Images.plain_wf
               Premises.witness_valid_input_abort).
    - exact (Premises.valid_input_entry _ _ OSSVerify.fast_float.from_chars.Images.plain_wf
               Premises.witness_valid_input). }
  destruct Hen as [en Hen]. exists en. split; [exact Hen |].
  apply (usage_never_refused en _ Hen); [| cbn; discriminate].
  destruct b;
    [ exact (valid_input_either_of_valid_input_abort _ Premises.witness_valid_input_abort)
    | exact (valid_input_either_of_valid_input _ Premises.witness_valid_input) ].
Qed.

(** [plain_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.fast_float.from_chars.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.fast_float.from_chars.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct (plain_witness_entry false) as (en & Hen & Hnr).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | apply Hnr]].
Qed.

(** [Statements.plain_halts], which the released
    [Theorems.halts_allowed_fast_float_from_chars_halts_plain] proves, at an entry
    and an input that meet all three of its premises: its conclusion holds there
    with no hypothesis left. *)
Theorem plain_halts_not_vacuous :
  exists en inp, valid_entry OSSVerify.fast_float.from_chars.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.fast_float.from_chars.Images.plain
      Budgets.Standard.lim_source en inp /\
  must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.fast_float.from_chars.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact ((OSSVerify.Proofs.fast_float.from_chars.lib.Theorems.halts_allowed_fast_float_from_chars_halts_plain
            : OSSVerify.fast_float.from_chars.Statements.plain_halts) en inp Hen Hinp Hnr).
Qed.

(** The three agreement statements: an entry of the plain build and one of the
    sanitizer build on the same input [Premises.witness_input true], with the
    budget premise from [plain_witness_entry]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
  valid_entry OSSVerify.fast_float.from_chars.Images.plain en_plain (Premises.witness_input true) /\
  valid_entry san en_san (Premises.witness_input true) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.fast_float.from_chars.Images.plain lim en_plain
      (Premises.witness_input true).
Proof.
  intros san Hwf.
  destruct (plain_witness_entry true) as (en_plain & Hep & Hnr).
  destruct (Premises.valid_input_abort_entry san (Premises.witness_input true) Hwf
              Premises.witness_valid_input_abort) as [en_san Hes].
  exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_from_chars_ubsan] proves, at entries
    and an input that meet all four of its premises: its conclusion holds there
    with no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.fast_float.from_chars.Images.plain en_plain inp /\
  valid_entry OSSVerify.fast_float.from_chars.Images.ubsan en_san inp /\
  valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.plain
      Budgets.Standard.lim_source en_plain inp /\
  error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.plain
      Budgets.Standard.lim_source en_plain inp)
  /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.ubsan
      Budgets.Standard.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.fast_float.from_chars.Images.ubsan OSSVerify.fast_float.from_chars.Images.ubsan_wf)
    as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.fast_float.from_chars.lib.Theorems.strong_universal_error_free_from_chars_ubsan
            : OSSVerify.fast_float.from_chars.Statements.ubsan_agrees)
           ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_from_chars_asan] proves, at entries and
    an input that meet all four of its premises: its conclusion holds there with
    no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.fast_float.from_chars.Images.plain en_plain inp /\
  valid_entry OSSVerify.fast_float.from_chars.Images.asan en_san inp /\
  valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.asan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.fast_float.from_chars.Images.asan OSSVerify.fast_float.from_chars.Images.asan_wf)
    as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.fast_float.from_chars.lib.Theorems.strong_universal_error_free_from_chars_asan
            : OSSVerify.fast_float.from_chars.Statements.asan_agrees)
           ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_from_chars_both] proves, at entries and
    an input that meet all four of its premises: its conclusion holds there with
    no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.fast_float.from_chars.Images.plain en_plain inp /\
  valid_entry OSSVerify.fast_float.from_chars.Images.asan_ubsan en_san inp /\
  valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.asan_ubsan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.fast_float.from_chars.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.fast_float.from_chars.Images.asan_ubsan
              OSSVerify.fast_float.from_chars.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.fast_float.from_chars.lib.Theorems.strong_universal_error_free_from_chars_both
            : OSSVerify.fast_float.from_chars.Statements.asan_ubsan_agrees)
           ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.
