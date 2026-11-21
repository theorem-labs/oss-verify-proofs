(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Top/AssembleP0.v's p0_realizes and the argc <> 2 branch of P0/RF_main.v's rmain_pre_proof (P0/RF_main_A.v's main_usage): the plain build's run, when argv has not two entries, reaches no budget-refused configuration. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO pair; walks lifted to the run's segment list; the channel-reader fact; the launch's input, mmap base and entry draw). *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Keeps RegsEquiv Ceiling InitStack EntrySecret MState.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Stdio_base Printf_lib Startup RefImpl Stdio_iface RDriver_kit RDriver_ctx RDriver_iface RF_main RF_main_A RF_main_post RDriver_seams RDriver_close RDriver_parser AllocInst AllocInit AllocLink H_fuzz_stmt.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require F_printf_diag.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog KInv KStepK.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import MSafe.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF CeilP.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require DriverModel AssembleP0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require RomStable.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.BudgetWit Require Import NoAlloc UsageNA Rzb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(** * The plain build's usage path, under the unfiltered step

    The released plain proof ([Top.AssembleP0.p0_realizes]) walks the
    program tree [AssembleP0.prog_pre argv] (set_tid_address, then
    [Driver.drv_pre]) from the run's start: [P0.Startup.rstartup_spec] is
    the walk to [main], and [P0.RF_main_A.main_usage] the walk of [main]
    when argv has not two entries, for every postcondition.  This file
    takes the same two walks with the postcondition [False] at every
    [Ok] leaf ([Qu]), and the released safety of the tree
    ([DriverModel.drv_pre_twf], as [p0_realizes] uses it), whose
    postcondition is [False] at every [Unr] leaf ([Pu]); so no leaf is
    reached.  [UsageNA.drv_pre_usage_na] says every node of that tree is
    writev, ioctl, set_tid_address or exit, and [NoAlloc.utree_never_refused]
    turns the three into [usage_unfiltered]: from the run's start
    configuration, the unfiltered run reaches no budget-refused
    configuration.  The section hypotheses are [p0_realizes]'s, less the
    harness statement, which the usage path does not reach. *)

Definition Qu : exc (at_parser (ptr:=bptr) * PState) -> machine_state -> Prop :=
  epost (fun _ _ => False).

Definition Pu : exc (at_parser (ptr:=bptr) * PState) -> Model -> Prop :=
  fun r _ => match r with Unr => False | Ok _ => True end.

Lemma QPu : forall r ms mo, Qu r ms -> Pu r mo -> False.
Proof. intros [|a] ms mo HQ HP; [exact HP | exact HQ]. Qed.

(** The whole tree, when argv has not two entries. *)
Lemma prog_pre_usage_na {HCEIL : HasCeiling} : forall argv,
  (length argv <> 2)%nat -> tna (@AssembleP0.prog_pre HCEIL argv).
Proof.
  intros argv Hlen. unfold AssembleP0.prog_pre.
  apply tna_ebind.
  - unfold enode. split; [reflexivity|]. intros rsp. cbv beta. destruct (dec_set_tid rsp); exact I.
  - intros a.
    assert (Hz : Z.of_nat (length (argv_Z argv)) <> 2) by (unfold argv_Z; rewrite length_map; lia).
    exact (drv_pre_usage_na _ _ _ _ _ _ _ _ Hz _).
Qed.

Section USAGE.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  (* LPS 727298f3: as [AssembleP0]'s RUN section: argv/envp are the input's, the launch facts the
     chain reads are [InitStack.stack_launch_ok], and the start model carries the vDSO draw. *)
  Variables (sp0 : word) (inp : ProcInput) (mbase : word) (rnd : EntryDraw).
  Variables (brk0 : word) (lim : Z).
  Notation argv := (in_argv inp).
  Notation envp := (in_envp inp).
  Notation mo0 := (with_vdso (Vdso.vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved rsegs) brk0 mbase sp0 lim inp)).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = bv_unsigned sp0 - 8388608.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis ESF : stack_launch_ok inp argv envp sp0 mbase rnd.
  Hypothesis GW : guard_word = entry_guard rnd.
  Hypothesis GS : secret_word = entry_secret rnd.
  Hypothesis VBRK : valid_brk rsegs brk0.
  Hypothesis ARGC : (length argv <> 2)%nat.
  Hypothesis VMB : valid_mmap_base mbase.
  Hypothesis VCR : in_channel_reader inp = true.

  (** [p0_realizes]'s walk, with no leaf reached. *)
  Lemma usage_impl :
    impl rsegs (at_node rsegs) (AssembleP0.prog_pre argv) Qu
      (init_ms rsegs Plain_init_pc Plain_phdrs sp0 mbase rnd inp).
  Proof.
    unfold AssembleP0.prog_pre, Qu. eapply impl_ebind.
    - exact (rstartup_spec sp0 inp mbase rnd VSP VARGV VENVP ESF).
    - intros u ms' HRM. cbn in HRM.
      exact (main_usage sp0 argv envp inp mbase rnd VSP CEIL VARGV VENVP ESF GW GS
               rauxv_init_proof (@F_printf_diag.fprintf_diag_proof PState) exit_k_proof
               ms' (fun _ _ _ => False) HRM ltac:(lia)).
  Qed.

  (** [p0_realizes]'s safety of the tree, at the run's start model. *)
  Lemma usage_twf :
    twf (AssembleP0.prog_pre argv) mo0 Pu.
  Proof.
    assert (MI0 : minv mo0).
    { apply minv_wvdso. apply minv_init; [destruct VSP as (V1 & V2 & _); split; [exact V1| exact V2]| exact VCR]. }
    unfold AssembleP0.prog_pre, ebind. apply twf_bind. unfold enode. cbn [twf]. split; [exact I|].
    intros rsp mo1 evs Hst.
    destruct (nstep_dec_set_tid _ _ _ _ MI0 Hst) as (_ & t & D & Ht & Hmo1). rewrite D. cbn [twf ITree.bind].
    assert (HO1 : OWN [] DriverModel.G0 (ps_init (reservedZ rsegs) alloc_ceiling) mo1).
    { destruct Hmo1 as [[E _] | [_ ->]].
      - exfalso. rewrite m_tid_wvdso, m_tid_init_model in E. discriminate.
      - apply AssembleP0.OWN_with_tid;
          [| rewrite unsigned_lit by (unfold PID_MAX_ENVELOPE in Ht; lia); exact Ht| exact I].
        pose proof (P0_link_init_vdso (Vdso.vdso_run_init (ed_vdso rnd)) brk0 mbase sp0 lim inp VBRK VSP VMB VCR CEIL) as L0.
        cbn [LINK AI_P0] in L0. unfold P0_LINK in L0. cbn [map] in L0. exact L0. }
    eapply twf_mono.
    - apply (DriverModel.drv_pre_twf RSV [] (argv_Z argv) (ps_init (reservedZ rsegs) alloc_ceiling) mo1
               (AssembleP0.argvZ_small inp VARGV) HO1). cbn. lia.
    - intros [|[ap s']] mo'; cbn; [intros F; exact F|]. intros _. exact I.
  Qed.

  Lemma usage_tree_ok :
    utree_ok rsegs Qu Pu (AssembleP0.prog_pre argv)
      (init_ms rsegs Plain_init_pc Plain_phdrs sp0 mbase rnd inp) mo0.
  Proof.
    refine (conj usage_impl (conj usage_twf (conj _ (conj _ (prog_pre_usage_na argv ARGC))))).
    - rewrite m_halted_wvdso. apply m_halted_init_model.
    - apply minv_wvdso. apply minv_init; [destruct VSP as (V1 & V2 & _); split; [exact V1| exact V2]| exact VCR].
  Qed.
End USAGE.

(** From the plain build's run start ([Run.init_config] over [run_segments rsegs inp sp mbase],
    the binary's segments with the run's vDSO pair, which [Run.run_budget_refused] reads), when
    argv has not two entries, the unfiltered run reaches no budget-refused configuration.  LPS
    727298f3: the walk is over [rsegs] from [RegsEquiv.init_ms]; [Rzb.utree_rzb] makes it an
    [rzb] derivation, [Rzb.rzb_run_rom] lifts it to the run's segment list and backing (where
    [init_ms] is the run's own, as in [CeilP.realizes_run_fields]), and
    [Rzb.rzb_eqv_never_refused] reads it from the run's start state, which is [ms_eqv] to it
    ([RegsEquiv.init_machine_state_eqv]).  The launch facts are the ones [valid_entry] (at Sv48,
    [valid_entry_sv48]) and [valid_input] give. *)
Theorem usage_unfiltered : forall sp brk mbase rnd lim inp,
  valid_sp sp -> valid_brk rsegs brk -> valid_mmap_base mbase -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> (length (in_argv inp) <> 2)%nat ->
  ~ reaches_budget_refused (run_segments rsegs inp sp mbase)
      (init_config (run_segments rsegs inp sp mbase) Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp).
Proof.
  intros sp brk mbase rnd lim inp VSP VBRK VMB VI LOK ARGC.
  pose proof VI as (VARGV & VENVP & _).
  pose proof (stack_launch_ok_of_launch inp sp brk mbase rnd (valid_input_launch _ VI) LOK) as ESF.
  pose proof (@usage_tree_ok (guardP rnd) (ceilP sp VSP) sp inp mbase rnd brk lim VSP eq_refl VARGV VENVP ESF
                eq_refl eq_refl VBRK ARGC VMB (valid_input_channel_reader _ VI)) as HT.
  pose proof (utree_rzb rsegs Qu Pu QPu _ _ _ HT) as HR.
  (* [eq_refl] for the backing is checked once [HR] has fixed the start state *)
  pose proof (fun Hrom => rzb_run_rom rsegs inp sp mbase _ _ _ eq_refl Hrom HR) as HR'.
  specialize (HR' eq_refl).
  change (RomBase.wrom (init_ms rsegs Plain_init_pc Plain_phdrs sp mbase rnd inp)
            (RomStable.seg_rom1 (run_segments rsegs inp sp mbase)))
    with (init_ms (run_segments rsegs inp sp mbase) Plain_init_pc Plain_phdrs sp mbase rnd inp) in HR'.
  unfold init_config. rewrite RomStable.segments_reserved_run_segments.
  apply (rzb_eqv_never_refused _ _ _ _ HR').
  unfold cfg_eqv. cbn [cfg_ms cfg_model]. split; [| reflexivity].
  exact (init_machine_state_eqv (run_segments rsegs inp sp mbase) Plain_init_pc Plain_phdrs sp mbase rnd inp).
Qed.
