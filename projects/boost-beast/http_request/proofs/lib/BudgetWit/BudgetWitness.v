(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 arms of RefTop.v's ref_realizes_spec_lim, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the four statements whose budget premise is on the plain build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.boost_beast.http_request Require Images Statements.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Amb Scfg PropExec ShapeAlg Spec RefStartup MainDefs.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Theorems.
From OSSVerify.Proofs.boost_beast.http_request.lib.BudgetWit Require Import Rzb RefStartupB MainTopB.
Import ListNotations.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

(** * boost-beast / http_request: the budget premise on the plain build holds together with the other premises

    Four statements of [Statements] carry a budget premise on the plain build,
    [~ run_scfg_budget_refused cfg Images.plain lim en inp]:
    - [plain_halts] ([halts_within_budget]), at [forced_only_cfg] and
      [Budgets.Standard.lim_source];
    - [ubsan_agrees] ([agrees_in_abort_modelled]), at [Env.alloc_forced_only]
      and [Budgets.Standard.lim_source];
    - [asan_agrees] and [asan_ubsan_agrees] ([agrees_in_abort_modelled]), at
      [Env.alloc_forced_only] and [Budgets.Asan.lim_source].
    A theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image and leaves the budget premise, which reads the run; this
    file gives it for this build, for every configuration and every limit.

    The input is [Premises.witness_input b]: one empty argument (so argc = 1),
    no environment, an empty file system; [b] is [false] for [plain_halts]
    ([valid_input]) and [true] for the three agreement statements, which read
    abort() as death by SIGABRT ([valid_input_abort]).  With argc <> 2 the
    driver's [main] writes its usage line to fd 2 and exits with status 2.  On
    that path the program makes three kinds of system call: set_tid_address
    (96) in musl's start-up, writev (66) for the line, exit or exit_group (93,
    94).  None has an injected arm, so none is an allocation call (brk 214,
    mremap 216, mmap 222, mprotect 226), and no mapping is lazy
    ([m_vm_lazy = []] throughout), so no configuration the run reaches is
    refused by the budget.  This shows the budget premise satisfiable on the
    usage path, not yet on an input that reaches [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path ([RefStartup.ref_startup],
    the argc <> 2 arms of [RefTop.ref_realizes_spec_lim], [MainTop.ref_usage])
    restated over [BudgetWit.Rzb.rzb], the released [ShapeAlg.realizes] with a
    no-allocation check at each node ([BudgetWit.Rzb] says why [realizes]
    itself cannot carry the fact).  [usage_rzb] is that walk;
    [Rzb.rzb_never_refused_cfg] turns it into the budget premise, for every
    spurious-failure configuration and every limit ([usage_never_refused]).
    Each [<statement>_not_vacuous] gives the premises of one of the four
    statements at one input to the released proof of that statement (the term
    its [proofs/<statement>/Proof.v] is), so the statement's conclusion holds
    at a point that meets all its premises, with no hypothesis left. *)

(** The argc <> 2 arms of [RefTop.ref_realizes_spec_lim], over [rzb]: start-up
    ([RefStartupB.ref_startup_b]), then [main]'s usage path
    ([MainTopB.ref_usage_b]).  The argc = 2 arm is excluded by [Hlen]. *)
Lemma usage_rzb : forall (sp brk mbase : word) (rnd : EntryDraw) (lim : Z) (inp : ProcInput),
  valid_sp sp -> valid_brk Plain.M.loaded_segments brk ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (* the launch facts the start-up and [main]'s argv reads take ([RefStartup.v:274-275],
     [MainTopB.v] Section UsageTop): [Run.valid_input]'s launch clause and the last
     conjunct of [Run.valid_entry]; and the stdout/stderr reader [main]'s usage message
     is written to ([Run.valid_input_channel_reader]). *)
  in_channel_reader inp = true ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  (length (in_argv inp) <> 2)%nat ->
  rzb Plain.M.loaded_segments
    (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd lim inp)
    (spec (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mbase rnd lim inp Hsp Hbrk Hfit Hva Hve Hrd Hvl Hlau Hlen.
  apply (ref_startup_b sp brk mbase rnd lim inp); try assumption.
  intros tid regs mem Htid ME.
  lazymatch goal with |- rzb _ (mkCfg (mkst _ ?pc _ _) _) _ =>
    replace pc with (Z_to_bv 64 0x2ac68) by (apply bv_eq; reflexivity) end.
  (* [ProcInput] has twenty fields ([RefTop.v] ref_realizes_spec_lim names them the same way). *)
  destruct inp as [argv envp fs0 stdin0 uid gid groups net nf sm hw abt vasz urnd tmp0
                   kb execfn chrdr sigdfl sigterm].
  unfold in_fs in *. cbn [in_argv in_envp in_image_fs in_tmp in_stdin] in *.
  pose (AMB := amb_of (mkProcInput_full argv envp fs0 stdin0 uid gid groups net nf sm hw abt vasz urnd tmp0
                         kb execfn chrdr sigdfl sigterm)).
  change (amb_of _) with AMB in ME.
  change (mkProcInput_full argv envp fs0 stdin0 uid gid groups net nf sm hw abt vasz urnd tmp0
            kb execfn chrdr sigdfl sigterm)
    with (@mkProcInputC AMB argv envp fs0 stdin0).
  change (fs_seed_tmp fs0 tmp0) with (@fsC AMB fs0).
  destruct argv as [|a0s [|path [|x l]]].
  - apply (ref_usage_b sp [] envp rnd tid regs mem brk mbase lim fs0 stdin0 Hva Hve Hsp Htid ME Hvl Hlau ltac:(cbn; lia) Hfit Hrd).
  - apply (ref_usage_b sp [a0s] envp rnd tid regs mem brk mbase lim fs0 stdin0 Hva Hve Hsp Htid ME Hvl Hlau ltac:(cbn; lia) Hfit Hrd).
  - exfalso. apply Hlen. reflexivity.
  - apply (ref_usage_b sp (a0s :: path :: x :: l) envp rnd tid regs mem brk mbase lim fs0 stdin0 Hva Hve Hsp Htid ME Hvl Hlau
             ltac:(cbn; lia) Hfit Hrd).
Qed.

(** On every valid entry of the plain build and every input whose argv is
    valid, has not two entries and whose environment is valid, no
    configuration of the run is refused by the budget, whatever the
    spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.boost_beast.http_request.Images.plain en inp ->
  in_va_size inp = Sv48 -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  in_channel_reader inp = true -> valid_launch inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.boost_beast.http_request.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hv Hva Hve Hrd Hvl Hlen cfg lim.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  (* [Run.valid_entry_sv48]: five conjuncts, the launch conjunct last. *)
  destruct Hen as (Hsp & Hbrk & _ & Hfits & Hlau).
  (* [Run.run_scfg_budget_refused] reads the run against [run_segments Plain.M.loaded_segments
     inp sp mbase] and from the start configuration over that list; [usage_rzb] is a walk
     over the binary's own segments, which [Rzb.rzb_run_init] lifts, the vDSO premise by
     computation. *)
  exact (rzb_never_refused_cfg _ cfg _ _
           (rzb_run_init Plain.M.loaded_segments inp sp mbase
              Plain.M.init_pc Plain.M.phdrs brk rnd lim _ eq_refl
              (usage_rzb sp brk mbase rnd lim inp Hsp Hbrk Hfits Hva Hve Hrd Hvl Hlau Hlen))).
Qed.

(** [Premises.witness_input b] meets [usage_never_refused]'s input premises
    when it is valid in either reading. *)
Lemma witness_never_refused : forall (b : bool) en,
  valid_entry OSSVerify.boost_beast.http_request.Images.plain en (Premises.witness_input b) ->
  in_va_size (Premises.witness_input b) = Sv48 ->
  valid_argv (in_argv (Premises.witness_input b)) -> valid_envp (in_envp (Premises.witness_input b)) ->
  in_channel_reader (Premises.witness_input b) = true -> valid_launch (Premises.witness_input b) ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.boost_beast.http_request.Images.plain lim en (Premises.witness_input b).
Proof.
  intros b en Hen Hs Hva Hve Hrd Hvl.
  exact (usage_never_refused en _ Hen Hs Hva Hve Hrd Hvl ltac:(cbn; discriminate)).
Qed.

(** [plain_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.boost_beast.http_request.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.boost_beast.http_request.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct (Premises.valid_input_entry OSSVerify.boost_beast.http_request.Images.plain (Premises.witness_input false)
              OSSVerify.boost_beast.http_request.Images.plain_wf Premises.witness_valid_input) as [en Hen].
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input |]].
  pose proof Premises.witness_valid_input as Hv.
  pose proof (valid_input_va_size _ Hv) as Hs.
  (* [Run.valid_input_launch]: the launch clause of [valid_input]. *)
  pose proof (valid_input_launch _ Hv) as Hvl.
  pose proof (valid_input_channel_reader _ Hv) as Hrd.
  destruct Hv as (Hva & Hve & _).
  exact (witness_never_refused false en Hen Hs Hva Hve Hrd Hvl _ _).
Qed.

(** [Statements.plain_halts], which the released
    [Theorems.halts_allowed_boost_beast_halts_plain] proves, at an entry and an
    input that meet all three of its premises: its conclusion holds there with
    no hypothesis left. *)
Theorem plain_halts_not_vacuous :
  exists en inp, valid_entry OSSVerify.boost_beast.http_request.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.boost_beast.http_request.Images.plain
      Budgets.Standard.lim_source en inp /\
  must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.boost_beast.http_request.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact (OSSVerify.Proofs.boost_beast.http_request.lib.Theorems.halts_allowed_boost_beast_halts_plain
           en inp Hen Hinp Hnr).
Qed.

(** The three agreement statements: an entry of the plain build and one of the
    sanitizer build on the same input [Premises.witness_input true] (the pair
    [Premises.agrees_in_abort_modelled_premises] builds, constructed here so
    that the input stays the witness input), with the budget premise from
    [witness_never_refused]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
  valid_entry OSSVerify.boost_beast.http_request.Images.plain en_plain (Premises.witness_input true) /\
  valid_entry san en_san (Premises.witness_input true) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.boost_beast.http_request.Images.plain lim en_plain
      (Premises.witness_input true).
Proof.
  intros san Hwf.
  destruct (Premises.valid_input_abort_entry OSSVerify.boost_beast.http_request.Images.plain
              (Premises.witness_input true) OSSVerify.boost_beast.http_request.Images.plain_wf
              Premises.witness_valid_input_abort) as [ep Hep].
  destruct (Premises.valid_input_abort_entry san (Premises.witness_input true) Hwf
              Premises.witness_valid_input_abort) as [es Hes].
  exists ep, es. split; [exact Hep | split; [exact Hes |]].
  pose proof Premises.witness_valid_input_abort as Hv.
  pose proof (valid_input_abort_va_size _ Hv) as Hs.
  (* [valid_input_abort]'s launch clause ([Run.valid_input_abort] states it as a conjunct;
     the model has no projection lemma for it), read off the conjunction. *)
  assert (Hvl : valid_launch (Premises.witness_input true))
    by (pose proof Hv as Hv'; red in Hv';
        repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  (* its reader clause, read the same way ([PairAsan.v] asan_base) *)
  assert (Hrd : in_channel_reader (Premises.witness_input true) = true)
    by (pose proof Hv as Hv'; red in Hv';
        repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  destruct Hv as (Hva & Hve & _).
  exact (witness_never_refused true ep Hep Hs Hva Hve Hrd Hvl).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_boost_beast_ubsan] proves, at entries
    and an input that meet all four of its premises: its conclusion holds there
    with no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.boost_beast.http_request.Images.plain en_plain inp /\
  valid_entry OSSVerify.boost_beast.http_request.Images.ubsan en_san inp /\
  valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.plain
      Budgets.Standard.lim_source en_plain inp /\
  error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.plain
      Budgets.Standard.lim_source en_plain inp)
  /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.ubsan
      Budgets.Standard.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.boost_beast.http_request.Images.ubsan
              OSSVerify.boost_beast.http_request.Images.ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.boost_beast.http_request.lib.Theorems.strong_universal_error_free_boost_beast_ubsan
           ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_boost_beast_asan] proves, at entries
    and an input that meet all four of its premises: its conclusion holds there
    with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.boost_beast.http_request.Images.plain en_plain inp /\
  valid_entry OSSVerify.boost_beast.http_request.Images.asan en_san inp /\
  valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.asan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.boost_beast.http_request.Images.asan
              OSSVerify.boost_beast.http_request.Images.asan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.boost_beast.http_request.lib.Theorems.strong_universal_error_free_boost_beast_asan
           ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_boost_beast_both] proves, at entries
    and an input that meet all four of its premises: its conclusion holds there
    with no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.boost_beast.http_request.Images.plain en_plain inp /\
  valid_entry OSSVerify.boost_beast.http_request.Images.asan_ubsan en_san inp /\
  valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.asan_ubsan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.boost_beast.http_request.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.boost_beast.http_request.Images.asan_ubsan
              OSSVerify.boost_beast.http_request.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.boost_beast.http_request.lib.Theorems.strong_universal_error_free_boost_beast_both
           ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.
