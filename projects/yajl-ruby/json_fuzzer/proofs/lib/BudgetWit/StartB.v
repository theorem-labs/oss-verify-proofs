(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Top/R_TopCfg.v: the start-up and the argc <> 2 branch of R_realizes_cfg_lim over BudgetWit.RzbCfg.rzb_cfg, with a heap invariant that holds for every limit, and the budget premise for the plain build on that path. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (main_rzb and usage_rzb over the launch's entry block (launch_of, valid_entry_launch) and the channel-reader premise of mo0_minv; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); the start-up spec no longer takes the envp premise it does not use; the budget premise from the run's own start over run_segments, through RzbCfg.rzb_never_refused_run). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Exec Step ITree ITreeCfg Nodes NodesCfg Decode RegsEquiv RegsEquivCfg InitMem RunInit Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg TrzNodesCfg TrzStdioCfg SpecT GlueCfg RunInitCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Malloc RawAlloc KArena MSuccIface MSuccRaw.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocKown.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import R_StartupLib R_Startup RMallocRep RMalloc_iface RMalloc_ifaceP RAlloc_rz.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajl_iface RDrv_iface RDrv_ctx.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import R_TopCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BudgetWit Require Import RzbCfg ImplRzb UsageB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(** * The plain build's argc <> 2 path, from the initial configuration

    [R_TopCfg.R_realizes_cfg_lim] runs musl's start-up ([R_Startup.rstartup_spec],
    one [set_tid_address] node, through the [impl]-to-[realizes_cfg] bridge) and
    then [main] under the heap invariant [RAlloc_rz.RHKG].  Establishing [RHKG]
    at [main]'s entry needs [VMINc <= lim] ([MSuccRaw.HEADc_init_lim]), because
    the fuzz path allocates.  The usage path does not allocate, so this file
    runs it under [HKU]: the heap representation [RHEAP] (which carries the
    stack-protector and libc-head cells the path reads) with [minv], without
    [RHKG]'s ownership and head-room parts.  [HKU] holds at [main]'s entry for
    every limit ([RMalloc_ifaceP.RHEAP_init_proof]), so [usage_rzb] and the
    budget premise hold for every limit.

    [usage_rzb] is the start-up ([ImplRzb.impl_trz_rzb_leaf] over
    [rstartup_spec]; the tree is one [set_tid_address] node) followed by
    [UsageB.main_usage_b], at [alloc_only_cfg false], from [RunInit.ms0].
    [plain_usage_never_refused_run] carries it to the run's own initial
    configuration ([RegsEquiv.init_machine_state_eqv],
    [RzbCfg.rzb_never_refused_run]: the run reads the binary's segments with the
    vDSO pair appended, and the plain binary carries no vDSO segment). *)

Section HKU.
Context {RC__ : RunCeiling}.

(** The heap representation and the model invariant, without ownership. *)
Definition HKU : HK_T := fun s LB m mo =>
  RHEAP s LB m /\ minv mo /\ m_halted mo = None.

Lemma HKU_run : HK_run_stmt HKU.
Proof. intros s LB m mo (_ & Hmi & Hh). split; [exact Hmi|]. split; [exact Hh | exact (minv_lazy _ Hmi)]. Qed.

Lemma HKU_frame : HK_frame_stmt HKU.
Proof.
  intros s LB m m' mo W (HR & Hmi & Hh) MU WM FW.
  split; [eapply RHEAP_frame_proof; eauto | split; [exact Hmi | exact Hh]].
Qed.

Lemma HKU_ssp : HK_ssp_stmt HKU.
Proof.
  intros s LB m mo ((st & LB0 & _ & _ & MREP & _) & _). destruct MREP as (_ & _ & (_ & _ & _ & G1 & G2) & _).
  split; [exact G1 | exact G2].
Qed.

Lemma HKU_libc_head : HK_libc_head_stmt HKU.
Proof.
  intros s LB m mo ((st & LB0 & _ & _ & MREP & _) & _). destruct MREP as (_ & _ & (_ & NL & _) & _).
  exact (libc_head_cells m NL).
Qed.
End HKU.

(** The start-up tree is one [set_tid_address] node. *)
Lemma tfree_set_tid : tfree (enode NSetTid dec_set_tid).
Proof.
  unfold enode. cbn [tfree]. split; [reflexivity|]. intros rsp. destruct (dec_set_tid rsp); exact I.
Qed.

(** [main] on the argc <> 2 path, from its entry, for every limit
    (the argc <> 2 case of [R_TopCfg.main_rz], under [HKU]). *)
Lemma main_rzb : forall (lim : Z) (en : ExecEntry) (inp : ProcInput) (tw : word) (ms : machine_state),
  let RC := rc_of en in
  valid_entry (mkImage rsegs r_init_pc r_phdrs) en inp -> valid_input inp ->
  0 < bv_unsigned tw < PID_MAX_ENVELOPE ->
  (length (in_argv inp) <> 2)%nat ->
  rat_main (RC__:=RC) (LT:=launch_of inp (en_sp en) (en_mmap_base en) (en_draw en)) (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) ms ->
  rzb_cfg acfg rsegs (mkCfg ms (with_tid tw (mo0 rsegs lim en inp))) (TU (in_argv inp) (in_fs inp)).
Proof.
  intros lim en inp tw ms RC VE VI Ht Hlen AM.
  destruct (valid_entry_unpack _ _ _ _ _ VE VI) as (VSP & VBRK & _ & EFIT).
  destruct (valid_input_unpack _ VI) as (VA & VEN & _ & _).
  assert (Hsp : bv_unsigned (en_sp en) = rc_sp) by reflexivity.
  assert (MOmi : minv (with_tid tw (mo0 rsegs lim en inp))).
  { apply minv_with_tid; [apply mo0_minv; [exact Hsp | exact VSP | exact (valid_input_channel_reader _ VI)] | exact Ht]. }
  set (MO := with_tid tw (mo0 rsegs lim en inp)) in *.
  assert (MOFS : m_fs MO = in_fs inp) by reflexivity.
  unfold TU. rewrite <- MOFS.
  apply (@main_usage_b RC (launch_of inp (en_sp en) (en_mmap_base en) (en_draw en)) (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)
           VSP (eq_sym Hsp) eq_refl EFIT VA VEN (HKU (RC__:=RC)) (HKU_run (RC__:=RC)) (HKU_frame (RC__:=RC))
           (HKU_ssp (RC__:=RC)) (HKU_libc_head (RC__:=RC)) MO).
  - intros m NONE LC LC2 GOT GUARD MI.
    destruct (RHEAP_init_proof m _ NONE LC LC2 GOT GUARD MI) as [HR AUXC].
    split; [| exact AUXC]. split; [exact HR|]. split; [exact MOmi | reflexivity].
  - reflexivity.
  - reflexivity.
  - exact AM.
  - intros HE. apply Hlen. lia.
Qed.

(** Start-up, then [main_rzb]: the argc <> 2 case of
    [R_TopCfg.R_realizes_cfg_lim] over [rzb_cfg], for every limit. *)
Theorem usage_rzb : forall (lim : Z) en inp,
  valid_entry (mkImage rsegs r_init_pc r_phdrs) en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  rzb_cfg acfg rsegs (mkCfg (ms0 rsegs r_init_pc r_phdrs en inp) (mo0 rsegs lim en inp))
          (TU (in_argv inp) (in_fs inp)).
Proof.
  intros lim en inp VE VI Hlen.
  pose proof (valid_entry_launch _ _ _ _ _ VE VI) as LOK.
  pose proof VI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VL & _).
  destruct en as [sp brk mb draw].
  pose (RC := rc_of (mkEntry sp brk mb draw)).
  destruct (valid_entry_unpack _ _ _ _ _ VE VI) as (VSP & _ & _ & _).
  destruct (valid_input_unpack _ VI) as (VA & VEN & _ & _).
  assert (Hsp : bv_unsigned (en_sp (mkEntry sp brk mb draw)) = rc_sp) by reflexivity.
  assert (RCG : rc_guard = guard_of (at_random_bytes (ed_random draw))) by reflexivity.
  change (ms0 rsegs r_init_pc r_phdrs (mkEntry sp brk mb draw) inp)
    with (init_ms rsegs r_init_pc r_phdrs sp mb draw inp).
  apply (impl_trz_rzb_leaf acfg rsegs acfg_off (enode NSetTid dec_set_tid)
           (epost (fun _ => rat_main (LT:=launch_of inp sp mb draw) sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw))
           _ (mo0 rsegs lim (mkEntry sp brk mb draw) inp) (fun _ _ => TU (in_argv inp) (in_fs inp)) _
           (rstartup_spec sp brk mb draw inp VSP VA VL LOK RCG)
           (trz_startup_set_tid_cfg _ _ _ _ Hsp VSP (valid_input_channel_reader _ VI) (TU_nil _ _)) tfree_set_tid
           (mo0_not_halted _ _ _ _) (mo0_minv _ _ _ _ Hsp VSP (valid_input_channel_reader _ VI))).
  intros [|t] ms' mo' HQ L Hh Hmi.
  - destruct (mo0_set_tid_leaf_cfg _ _ _ _ _ Hsp VSP (valid_input_channel_reader _ VI) L) as (t & _ & E & _). discriminate.
  - destruct (mo0_set_tid_leaf_cfg _ _ _ _ _ Hsp VSP (valid_input_channel_reader _ VI) L) as (t' & Ht & E & ->). cbn in HQ.
    apply (main_rzb lim (mkEntry sp brk mb draw) inp (Z_to_bv 64 t') ms' VE VI);
      [rewrite unsigned_lit; unfold PID_MAX_ENVELOPE in *; lia | exact Hlen | exact HQ].
Qed.

(** The run's initial configuration and the walk's are equivalent. *)
Lemma init_cfg_eqv : forall lim en inp,
  cfg_eqv (init_config rsegs r_init_pc r_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp)
          (mkCfg (ms0 rsegs r_init_pc r_phdrs en inp) (mo0 rsegs lim en inp)).
Proof.
  intros lim en inp. rewrite init_config_eq.
  split; cbn [cfg_ms cfg_model]; [unfold ms0; apply init_machine_state_eqv | reflexivity].
Qed.

(** On every valid entry of the plain build and every valid input whose argv
    has not two entries, the unfiltered run reaches no budget-refused
    configuration, whatever the limit. *)
Theorem plain_usage_never_refused_run : forall en inp,
  valid_entry (mkImage rsegs r_init_pc r_phdrs) en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall lim : Z, ~ run_budget_refused (mkImage rsegs r_init_pc r_phdrs) lim en inp.
Proof.
  intros en inp Hen Hinp Hlen lim.
  pose proof (usage_rzb lim en inp Hen Hinp Hlen) as H.
  pose proof (init_cfg_eqv lim en inp) as E.
  destruct en as [sp brk mbase rnd].
  assert (Hvi : vdso_image rsegs = None) by reflexivity.
  exact (rzb_never_refused_run acfg rsegs inp sp mbase r_init_pc r_phdrs brk rnd lim _ _ Hvi E H).
Qed.
