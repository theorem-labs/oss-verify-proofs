(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 branch of DrvRootP.v's main_sound and P_root_f_at, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the three statements whose budget premise is on the plain build. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (usage_main and usage_rzb over the launch's ProcInput: valid_launch, the launch entry, the channel reader and the vDSO reservation, as DrvRootP's main_sound and P_root_f_at; usage_never_refused lifted to the run's segment list by RomStable.rzb_run_init). *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1 OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.TopProof4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ShapeHalts OSSVerify.Proofs.glaze.binary_reflection.lib.TopHalts OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhMalloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvInstP OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Plan. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1.RefStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.RefStartupFacts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.ShapeLaws OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRoot OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzEntry OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.Spec4KF OSSVerify.Proofs.glaze.binary_reflection.lib.TopProof4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ShapeHalts OSSVerify.Proofs.glaze.binary_reflection.lib.TopHalts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.MhMalloc3.MhMSpecI OSSVerify.Proofs.glaze.binary_reflection.lib.MhMalloc3.MhMallocR0 OSSVerify.Proofs.glaze.binary_reflection.lib.MhMalloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.GpFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.DrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan.DrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Sound.DrvGSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.DrvS0Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.DrvS1Open OSSVerify.Proofs.glaze.binary_reflection.lib.DrvInstP OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes2 OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.DrvNodes2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.DrvESound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.DrvS0Glue OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := PSEGS.
(* [comment removed for export] *)
Ltac lia ::= Zify.zify; xlia zchecker.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Core Require Premises.
From OSSVerify.glaze.binary_reflection Require Images Statements.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.DrvRootP OSSVerify.Proofs.glaze.binary_reflection.lib.Theorems OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StartB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.UsageB.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RomStable.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.DrvRootP.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb.RzbAlg OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb.ShapeRelB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StartB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.UsageB.DrvS0GlueB.
From OSSVerify.Core Require Import Shapes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(** * glaze / binary_reflection: the budget premise on the plain build holds together with the other premises

    Three statements of [Statements] carry a budget premise on the plain build,
    [~ run_scfg_budget_refused cfg Images.plain lim en inp], all of shape
    [agrees_in_abort_modelled] at [Env.alloc_forced_only]:
    - [ubsan_agrees], at [Budgets.Standard.lim_source];
    - [asan_agrees] and [asan_ubsan_agrees], at [Budgets.Asan.lim_source].
    A theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image and leaves the budget premise, which reads the run; this
    file gives it for this build, for every configuration and every limit.

    The input is [Premises.witness_input true] (the shapes here are
    abort-modelled): one empty argument (so argc = 1), no environment, an
    empty file system.  With argc <> 2 the driver's [main] writes its usage
    line to fd 2 and exits with status 2.  On that path the program makes
    three kinds of system call: set_tid_address (96) in musl's start-up,
    writev (66) for the line, and exit or exit_group (93, 94).  (The
    plan-checker soundness the walk reuses also proves its ioctl (29) and
    read (63) nodes with the same check; this path reaches neither.)
    None is an allocation call (brk 214, mremap 216, mmap 222, mprotect 226),
    and the walk keeps [m_vm_lazy = []] throughout, so no configuration the run
    reaches is refused by the budget.  This shows the budget premise
    satisfiable on the usage path, not yet on an input that reaches
    [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path ([RefStartup.ref_startup],
    the argc <> 2 branch of [DrvRootP.main_sound], [DrvS0Glue.usage_sound]
    and the plan-checker soundness it applies) restated over
    [BudgetWit.Rzb.rzb], the released [ShapeAlg.realizes] with a
    no-allocation-call check at each node ([BudgetWit.Rzb] says why
    [realizes] itself cannot carry the fact).  [usage_rzb] is that walk;
    [Rzb.RzbAlg.rzb_never_refused_cfg] turns it into the budget premise, for
    every spurious-failure configuration and every limit
    ([usage_never_refused]).  Each [<statement>_not_vacuous] gives the premises
    of one of the three statements at one input to the released proof of that
    statement (the term its [proofs/<statement>/Proof.v] is), so the
    statement's conclusion holds at a point that meets all its premises, with
    no hypothesis left. *)

(** The argc <> 2 branch of [DrvRootP.main_sound], over [rzb]. *)
Lemma usage_main : forall (RC : run_ceil) sp0 inp mbase brk rdraw tid regs mem model,
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_sp sp0 ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp -> 0 < bv_unsigned tid < 4194304 ->
  main_entry sp0 inp mbase rdraw tid regs mem ->
  m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] -> m_fds model = fds_std ->
  @GlzConst.RunCeil.CEIL RC <= bv_unsigned sp0 - 8388608 ->
  m_channel_reader model = true ->
  incl (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model))) (vm_reserved (m_vmmaps model)) ->
  (length (in_argv inp) <> 2)%nat ->
  rzb RSEGS (cfgF RSEGS fx0 regs P_MAIN mem model) (t_die (msg_usage (nth 0 (in_argv inp) [])) (m_fs model)).
Proof.
  intros RC sp0 inp mbase brk rdraw tid regs mem model Hva Hve Hvsp Hvl Hlau Htid ME Mh Ml Mm Mfd MC Mrd MVdso Hne.
  exact (@usage_sound RC (SR_rzb RSEGS) (exact_rzb RSEGS) sp0 inp mbase brk rdraw tid regs mem model
           Hva Hve Hvsp Hvl Hlau Htid ME Mh Ml Mm Mfd MC Mrd MVdso Hne).
Qed.

(** Start-up ([StartB.ref_startup_rzb]) then [main]'s usage path ([usage_main]):
    the argc <> 2 branch of [DrvRootP.P_root_f_at], over [rzb].  No limit
    condition: the usage path needs none. *)
Lemma usage_rzb : forall sp brk0 mb rnd lim inp,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk0 mb rnd) inp ->
  in_channel_reader inp = true ->
  (length (in_argv inp) <> 2)%nat ->
  rzb Plain.M.loaded_segments
      (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk0 mb rnd lim inp)
      (t_die (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
  intros sp brk0 mb rnd lim inp Hsp Hva Hve Hvl Hlau Hrdr Hlen.
  apply (ref_startup_rzb sp brk0 mb rnd lim inp _ Hsp Hva Hve Hvl Hlau).
  intros tid regs mem Htid ME.
  pose proof (MDL_facts tid brk0 mb sp lim inp rnd) as (Mh & Ml & Mm & Mfd & Mrd & Mfs & _).
  pose proof (usage_main (RC_of sp Hsp) sp inp mb brk0 rnd tid regs mem
                (MDL tid brk0 mb sp lim inp rnd) Hva Hve Hsp Hvl Hlau ltac:(unfold PID_MAX_ENVELOPE in Htid; lia) ME Mh Ml Mm Mfd
                (CEIL_init sp Hsp) ltac:(rewrite Mrd; exact Hrdr) (MDL_vdso tid brk0 mb sp lim inp rnd) Hlen) as X.
  rewrite Mfs in X. unfold cfgF, mkstF, MDL, P_MAIN in X.
  match goal with |- rzb _ (mkCfg (mkst _ ?pcw _ _) _) _ => replace pcw with (Z_to_bv 64 189324) by (apply bv_eq; reflexivity) end.
  exact X.
Qed.

(** On every valid entry of the plain build and every valid input whose argv has
    not two entries, no configuration of the run is refused by the budget, whatever
    the spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.glaze.binary_reflection.Images.plain en inp -> valid_input_abort inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.glaze.binary_reflection.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp Hlen cfg lim.
  pose proof (valid_input_abort_va_size _ Hinp) as Hv.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & _ & _ & _ & Hlau).
  (* [valid_input_abort]'s conjuncts: argv, envp, fs, the image keys, the real image, creds,
     nofile, sigmask, hwcap, the abort stance, the VA size, urandom, the launch (13th) and the
     channel reader (14th), then sigpipe and the kernel. *)
  destruct Hinp as (Hva & Hve & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvl & Hrdr & _).
  (* LPS 727298f3: the run reads [run_segments ..] from [init_config (run_segments ..) ..]; the
     walk over the binary's own segments is lifted there (the image carries no vDSO text). *)
  exact (rzb_never_refused_cfg _ cfg _ _
           (RomStable.rzb_run_init Plain.M.loaded_segments inp sp mbase Plain.M.init_pc Plain.M.phdrs
              brk rnd lim _ ltac:(RomStable.vdso_none)
              (usage_rzb sp brk mbase rnd lim inp Hsp Hva Hve Hvl Hlau Hrdr Hlen))).
Qed.

(** An entry of the plain build at [Premises.witness_input true], the entry
    [Premises.valid_input_abort_entry] gives for it, at which the budget refuses
    nothing, whatever the configuration and the limit. *)
Lemma plain_witness_entry : exists en,
  valid_entry OSSVerify.glaze.binary_reflection.Images.plain en (Premises.witness_input true) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.glaze.binary_reflection.Images.plain lim en (Premises.witness_input true).
Proof.
  destruct (Premises.valid_input_abort_entry OSSVerify.glaze.binary_reflection.Images.plain (Premises.witness_input true)
    OSSVerify.glaze.binary_reflection.Images.plain_wf Premises.witness_valid_input_abort) as [en Hen].
  exists en. split; [exact Hen |].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input_abort).
  cbn. discriminate.
Qed.

(** The plain build's premises at [Premises.witness_input true]: the entry
    above, the input premise, and the budget premise at the plain build's
    configuration and limits of the three statements. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.glaze.binary_reflection.Images.plain en inp /\ valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.plain
      Budgets.Asan.lim_source en inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_witness_entry as (en & Hen & Hnr).
  exists en, (Premises.witness_input true).
  split; [exact Hen | split; [exact Premises.witness_valid_input_abort | split; apply Hnr]].
Qed.

(** The three agreement statements: an entry of the plain build and one of the
    sanitizer build on the same input [Premises.witness_input true] (the pair
    [Premises.agrees_in_abort_modelled_premises] builds, constructed here so
    that the input stays the witness input), with the budget premise from
    [plain_witness_entry]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
  valid_entry OSSVerify.glaze.binary_reflection.Images.plain en_plain (Premises.witness_input true) /\
  valid_entry san en_san (Premises.witness_input true) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.glaze.binary_reflection.Images.plain lim en_plain (Premises.witness_input true).
Proof.
  intros san Hwf.
  destruct plain_witness_entry as (en_plain & Hep & Hnr).
  destruct (Premises.valid_input_abort_entry san (Premises.witness_input true) Hwf Premises.witness_valid_input_abort)
    as [en_san Hes].
  exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_binary_reflection_asan] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.glaze.binary_reflection.Images.plain en_plain inp /\
  valid_entry OSSVerify.glaze.binary_reflection.Images.asan en_san inp /\
  valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.asan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.glaze.binary_reflection.Images.asan OSSVerify.glaze.binary_reflection.Images.asan_wf)
    as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.glaze.binary_reflection.lib.Theorems.strong_universal_error_free_binary_reflection_asan
    ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_binary_reflection_ubsan] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.glaze.binary_reflection.Images.plain en_plain inp /\
  valid_entry OSSVerify.glaze.binary_reflection.Images.ubsan en_san inp /\
  valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.plain
      Budgets.Standard.lim_source en_plain inp /\
  error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.plain
      Budgets.Standard.lim_source en_plain inp)
  /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.ubsan
      Budgets.Standard.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.glaze.binary_reflection.Images.ubsan OSSVerify.glaze.binary_reflection.Images.ubsan_wf)
    as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.glaze.binary_reflection.lib.Theorems.strong_universal_error_free_binary_reflection_ubsan
    ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_binary_reflection_both] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.glaze.binary_reflection.Images.plain en_plain inp /\
  valid_entry OSSVerify.glaze.binary_reflection.Images.asan_ubsan en_san inp /\
  valid_input_abort inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.asan_ubsan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.glaze.binary_reflection.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.glaze.binary_reflection.Images.asan_ubsan
    OSSVerify.glaze.binary_reflection.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input true).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.glaze.binary_reflection.lib.Theorems.strong_universal_error_free_binary_reflection_both
    ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.
