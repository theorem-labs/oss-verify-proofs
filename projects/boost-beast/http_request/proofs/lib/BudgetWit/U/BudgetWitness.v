(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 arms of Ub/UbTop.v's walk, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the UBSan build and the lemma that applies the released proof of ubsan_halts there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.boost_beast.http_request Require Images Statements.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Amb Scfg PropExec ShapeAlg Spec.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Theorems.
From OSSVerify.Proofs.boost_beast.http_request.lib.BudgetWit Require Import Rzb.
From OSSVerify.Proofs.boost_beast.http_request.lib.BudgetWit.U Require Import RefStartupB MainTopB.
Import ListNotations.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

(** * boost-beast / http_request: the budget premise on the UBSan build holds together with the other premises

    One statement of [Statements] carries a budget premise on the UBSan build:
    [ubsan_halts] ([halts_within_budget]), at [forced_only_cfg] and
    [Budgets.Standard.lim_source].  A theorem whose premises never hold
    together proves nothing.  [OSSVerify.Core.Premises] gives the entry and
    input premises for every well-formed image and leaves the budget premise,
    which reads the run; this file gives it for this build, for every
    configuration and every limit.

    The input is [Premises.witness_input false]: one empty argument (so argc =
    1), no environment, an empty file system.  With argc <> 2 the driver's
    [main] writes its usage line to fd 2 and exits with status 2.  On that path
    the program makes three kinds of system call: set_tid_address (96) in
    musl's start-up, writev (66) for the line, exit or exit_group (93, 94).
    None has an injected arm, so none is an allocation call (brk 214, mremap
    216, mmap 222, mprotect 226), and no mapping is lazy ([m_vm_lazy = []]
    throughout), so no configuration the run reaches is refused by the budget.
    This shows the budget premise satisfiable on the usage path, not yet on an
    input that reaches [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path for this build
    ([Ub.RefStartup.ref_startup], the argc <> 2 arms of the walk [Ub/UbTop.v]
    composes, [Ub.MainTop.ref_usage]) restated over [BudgetWit.Rzb.rzb], the
    carrier the plain build's witness ([BudgetWit.BudgetWitness]) uses: the
    two builds share [ShapeAlg.realizes] and its node lemmas.  [usage_rzb] is
    that walk; [Rzb.rzb_never_refused_cfg] turns it into the budget premise,
    for every spurious-failure configuration and every limit
    ([usage_never_refused]).  [ubsan_halts_not_vacuous] gives the premises of
    [ubsan_halts] at one input to the released proof of that statement (the
    term its [proofs/ubsan_halts/Proof.v] is), so its conclusion holds at a
    point that meets all its premises, with no hypothesis left. *)

(** The argc <> 2 arms of the UBSan walk, over [rzb]: start-up
    ([U.RefStartupB.ref_startup_b]), then [main]'s usage path
    ([U.MainTopB.ref_usage_b]).  The argc = 2 arm is excluded by [Hlen]. *)
Lemma usage_rzb : forall (sp brk mbase : word) (rnd : EntryDraw) (lim : Z) (inp : ProcInput),
  valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (* the launch facts the start-up and [main]'s argv reads take ([Ub/RefStartup.v:265-266],
     [U/MainTopB.v] Section UsageTop): [Run.valid_input]'s launch clause and the last
     conjunct of [Run.valid_entry]; and the stdout/stderr reader [main]'s usage message
     is written to ([Run.valid_input_channel_reader]). *)
  in_channel_reader inp = true ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  (length (in_argv inp) <> 2)%nat ->
  rzb Ubsan.M.loaded_segments
    (init_config Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rnd lim inp)
    (spec (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mbase rnd lim inp Hsp Hbrk Hfit Hva Hve Hrd Hvl Hlau Hlen.
  apply (ref_startup_b sp brk mbase rnd lim inp); try assumption.
  intros tid regs mem Htid ME.
  lazymatch goal with |- rzb _ (mkCfg (mkst _ ?pc _ _) _) _ =>
    replace pc with (Z_to_bv 64 0x2baec) by (apply bv_eq; reflexivity) end.
  (* [ProcInput] has twenty fields ([Ub/UbTop.v] names them the same way). *)
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

(** On every valid entry of the UBSan build and every input whose argv is
    valid, has not two entries and whose environment is valid, no
    configuration of the run is refused by the budget, whatever the
    spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.boost_beast.http_request.Images.ubsan en inp ->
  in_va_size inp = Sv48 -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  in_channel_reader inp = true -> valid_launch inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.boost_beast.http_request.Images.ubsan lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hv Hva Hve Hrd Hvl Hlen cfg lim.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  (* [Run.valid_entry_sv48]: five conjuncts, the launch conjunct last. *)
  destruct Hen as (Hsp & Hbrk & _ & Hfits & Hlau).
  (* the walk over the binary's own segments, lifted to the run's segment list by
     [Rzb.rzb_run_init] (BudgetWitness.v [usage_never_refused]) *)
  exact (rzb_never_refused_cfg _ cfg _ _
           (rzb_run_init Ubsan.M.loaded_segments inp sp mbase
              Ubsan.M.init_pc Ubsan.M.phdrs brk rnd lim _ eq_refl
              (usage_rzb sp brk mbase rnd lim inp Hsp Hbrk Hfits Hva Hve Hrd Hvl Hlau Hlen))).
Qed.

(** [ubsan_halts]'s three premises hold together: at
    [Premises.witness_input false] and the entry [Premises.valid_input_entry]
    gives for it. *)
Theorem ubsan_budget_witness :
  exists en inp, valid_entry OSSVerify.boost_beast.http_request.Images.ubsan en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.boost_beast.http_request.Images.ubsan
      Budgets.Standard.lim_source en inp.
Proof.
  destruct (Premises.valid_input_entry OSSVerify.boost_beast.http_request.Images.ubsan (Premises.witness_input false)
              OSSVerify.boost_beast.http_request.Images.ubsan_wf Premises.witness_valid_input) as [en Hen].
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input |]].
  pose proof Premises.witness_valid_input as Hv.
  pose proof (valid_input_va_size _ Hv) as Hs.
  (* [Run.valid_input_launch]: the launch clause of [valid_input]. *)
  pose proof (valid_input_launch _ Hv) as Hvl.
  pose proof (valid_input_channel_reader _ Hv) as Hrd.
  destruct Hv as (Hva & Hve & _).
  exact (usage_never_refused en _ Hen Hs Hva Hve Hrd Hvl ltac:(cbn; discriminate) _ _).
Qed.

(** [Statements.ubsan_halts], which the released
    [Theorems.halts_allowed_boost_beast_halts_ubsan] proves, at an entry and an
    input that meet all three of its premises: its conclusion holds there with
    no hypothesis left. *)
Theorem ubsan_halts_not_vacuous :
  exists en inp, valid_entry OSSVerify.boost_beast.http_request.Images.ubsan en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.boost_beast.http_request.Images.ubsan
      Budgets.Standard.lim_source en inp /\
  must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.boost_beast.http_request.Images.ubsan
      Budgets.Standard.lim_source en inp.
Proof.
  destruct ubsan_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact (OSSVerify.Proofs.boost_beast.http_request.lib.Theorems.halts_allowed_boost_beast_halts_ubsan
           en inp Hen Hinp Hnr).
Qed.
