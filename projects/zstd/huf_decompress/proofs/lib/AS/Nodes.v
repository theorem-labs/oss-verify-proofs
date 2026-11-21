(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (3 recorded proofs replaced by written proofs (sstep_svc_inv, sstep_of_check, rz_exit_chk); rz_ret_only, rz_ret_only_copyins, their silent forms, rz_det, rz_cases and rz_open take RomBase.sys_rob and pass it to the node rules; imports RomBase). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import SimInv ExitSim CatSim FileSim ShapeAlg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import RomBase.
Ltac2 kr_t_Nodes () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesK47Corelib4Init9Datatypes4list01c59OSSVerify5KrLib2AS5Nodes7halt_evC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputI47Corelib4Init5Logic3and00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic9False_indK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesI47Corelib4Init5Logic2or00C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsDcheck_syscall_ok_iffK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04C4ELinuxProcessSemantics?LinuxProcessSem5StateIm_killed_of_m_halted_noneK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsEcheck_syscall_err_iffC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01K47Corelib4Init5Logic2ex01I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC47Corelib4Init5Logic3notK4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg04C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunCinjected_family_offC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00c59OSSVerify5KrLib2AS5NodesBsstep_cfg_of_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5NodesEsstep_cfg_svc_inv_chkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Cfg<sstep_of_cfgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Nodes=sstep_svc_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Nodes;node_chk_evC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib4Init5Logic5proj2c59OSSVerify5KrLib2AS5NodesDuniform_not_spuriousC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib2AS5Nodes?node_chk_ev_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Nodes8node_chkC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeEcheck_ret_only_ok_iffC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeKcheck_ret_only_no_unmodeledc59OSSVerify5KrLib2AS5Nodes8node_detC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C59OSSVerify5KrLib2AS6CatSimEapply_effect_no_writeC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeFcheck_ret_only_copyinsC4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeMcheck_ret_only_copyins_ok_iffC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeScheck_ret_only_copyins_no_unmodeledC59OSSVerify5KrLib2AS6CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Nodes=node_ret_onlyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg8rz_emit1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5NodesEnode_ret_only_copyinsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg:rz_silent1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg5t_altC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS8ShapeAlg8realizes01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlgArealizes_nonemptyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib2AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg7rz_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Nodes6open_IC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib3Cfg:alloc_no_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7FileSimIcheck_open_result_copyinsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State8alloc_fdc59OSSVerify5KrLib2AS5Nodes7open_nxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3CfgGtransparent_nonalloc_noC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif3sig00K47Corelib4Init9Datatypes3sum01C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC59OSSVerify5KrLib2AS7FileSimPcheck_open_result_copyins_ok_iffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Nodes>sstep_of_checkC1?~~~~~~~~~~~~~~~K47Corelib4Init6Specif3sig01K47Corelib4Init9Datatypes3sum02C59OSSVerify5KrLib2AS7FileSimYcheck_open_result_copyins_never_unmodeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC46Stdlib5Lists4List2InI47Corelib7Numbers7BinNums1Z00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I47Corelib4Init9Datatypes3sum00c59OSSVerify5KrLib2AS5Nodes9node_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg7rz_alt2C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC59OSSVerify5KrLib2AS7FileSimGENOMEM_in_openat_errnosC1?~~~~~~~~~~~~~~~".

Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition halt_ev (m' : Model) (code : word) : event :=
  match m_killed m' with
  | Some sig => KillEv sig (m_fs m')
  | None => ExitEv code (m_fs m')
  end.

Lemma sstep_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e st ->
  (exists eff model' evs,
      check_syscall (sys_input segs ms x8) eff model = CheckOk model' evs
      /\ ((exists model'', m_halted model' = None /\ e = evs
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (m_halted model' = None /\ e = []
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code
              /\ e = evs ++ [halt_ev model' code]
              /\ st = SNext (mkCfg ms model'))))
  \/ (exists eff, check_syscall (sys_input segs ms x8) eff model = CheckUnmodeled
      /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + left. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. left. repeat split; auto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. right. eexists. repeat split; eauto.
      unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. right.
      match goal with Hk : m_killed ?mm = Some _ |- _ =>
        destruct (m_halted mm) as [code|] eqn:Hhc;
          [| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
        exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
      end.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
    apply check_syscall_err_iff. assumption.
Qed.

(* [comment removed for export] *)
Lemma sstep_of_check : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hlazy.
  apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hh'.
  - apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.

Lemma sstep_cfg_of_check : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  sstep_cfg segs ACFG (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hns Hh' Hlazy.
  apply (sstep_cfg_syscall segs ACFG ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hns.
  - exact Hh'.
  - apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.

Lemma uniform_not_spurious : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event) (b : bool),
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = b) ->
  forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i).
Proof.
  intros ms model x8 I effs ms' evs b Hinv Hb i (Hoff & Hr & eff' & m' & ev' & Hspec & Hnr).
  apply check_syscall_ok_iff in Hspec.
  destruct (Hinv _ _ _ Hspec) as (j & -> & _ & _).
  rewrite Hb in Hr. rewrite Hb in Hnr. congruence.
Qed.

Lemma sstep_cfg_svc_inv_chk : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs ACFG (mkCfg ms model) e st ->
  (exists eff model' evs,
      check_syscall (sys_input segs ms x8) eff model = CheckOk model' evs
      /\ ((~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff
           /\ m_halted model' = None
           /\ ((exists model'', e = evs
                   /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
                   /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
               \/ (e = [] /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
                   /\ st = SError)))
          \/ (exists code, m_halted model' = Some code
                 /\ e = evs ++ [halt_ev model' code]
                 /\ st = SNext (mkCfg ms model'))))
  \/ (exists eff, check_syscall (sys_input segs ms x8) eff model = CheckUnmodeled
      /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + left. split; [assumption|]. split; [assumption|]. left. eexists. repeat split; eauto.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + left. split; [assumption|]. split; [assumption|]. right. repeat split; auto.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. eexists. repeat split; eauto.
      unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right.
      match goal with Hk : m_killed ?mm = Some _ |- _ =>
        destruct (m_halted mm) as [code|] eqn:Hhc;
          [| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
        exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
      end.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
    apply check_syscall_err_iff. assumption.
Qed.

Lemma node_chk_ev_gen : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev -> m_halted m' = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hnf Hinv Hnu Hnh Hlazy. split.
  - intros i. apply (sstep_cfg_of_check ms model x8); auto. exact (Hnh _ _ _ (Hok i)).
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv_chk ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(Hnsp & Hh2 & [(m'' & -> & Hmat & ->) | (-> & Hmat & ->)]) | (code & Hh2 & -> & ->)])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + rewrite (Hnh _ _ _ Hc) in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
Lemma node_chk_ev : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hlazy Hns. split.
  - intros i. apply (sstep_cfg_of_check ms model x8); auto.
  - intros e st Hss. apply sstep_of_cfg in Hss.
    destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
Lemma node_chk : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
     exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hnu Hh' Hlazy Hns.
  apply (node_chk_ev ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.

(* [comment removed for export] *)
Lemma node_det : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hlazy0.
  assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
            exists i : unit, eff = (fun _ => eff0) i /\ m' = (fun _ => m0) i /\ ev = (fun _ => evs0) i).
  { intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto. }
  apply (node_chk_ev ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - exact Hinv.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hlazy0.
  - apply (uniform_not_spurious ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
             (refusal_b (sys_input segs ms x8) model (eff_ret eff0)) Hinv).
    intros []. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_ret_only : forall ms model x8 r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_no_write ms r).
  apply (node_det ms model x8 (mkEffect r [] []) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
  - exact Hh'.
  - exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma node_ret_only_copyins : forall ms model x8 reads r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_det ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_copyins_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - exact Hh'.
  - exact Hlazy.
Qed.

Lemma rz_ret_only : forall ms model x8 r m' evs T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  sys_rob segs (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) (t_emit evs T).
Proof.
  intros ms model x8 r m' evs T Hh Hsvc Hrob Hchk Hh' Hlazy Hc.
  eapply rz_emit1; [eapply node_ret_only; eassumption | exact Hrob | exact Hc].
Qed.

Lemma rz_ret_only_copyins : forall ms model x8 reads r m' evs T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  sys_rob segs (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) (t_emit evs T).
Proof.
  intros ms model x8 reads r m' evs T Hh Hsvc Hrob Hchk Hh' Hlazy Hc.
  eapply rz_emit1; [eapply node_ret_only_copyins; eassumption | exact Hrob | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rz_ret_only_silent : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  sys_rob segs (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 r m' T Hh Hsvc Hrob Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only; eassumption | exact Hrob | exact Hc].
Qed.

Lemma rz_ret_only_copyins_silent : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  sys_rob segs (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hrob Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only_copyins; eassumption | exact Hrob | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rz_det : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  sys_rob segs (mkCfg ms model) ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hrob Hchk Hnu Hh0 Hlazy0 Hc.
  eapply rz_silent1; [eapply node_det; eassumption | exact Hrob | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx -> sys_rob segs c ->
  (forall i, realizes segs (nx i) (T i)) ->
  realizes segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hrob Hc.
  apply (rz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (rz_node segs c I (fun _ => []) nx T i0 Hnode Hrob Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

(* [comment removed for export] *)
Lemma rz_exit_chk : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes segs (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof. intros. eapply rz_exit; eassumption. Qed.

(* [comment removed for export] *)
Definition open_I (model : Model) : Type := {e : Z | In e openat_errnos} + unit.

Definition open_nx (ms : machine_state) (model : Model) (mk : word -> Model)
  (i : open_I model) : config :=
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr _ => mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                   (mk (alloc_fd (m_fds model)))
  end.

Lemma node_open : forall ms model x8 reads (mk : word -> Model),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  alloc_no_b (bv_unsigned x8) = false ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
  intros ms model x8 reads mk Hh Hlazy Hsvc Hno Hchk Hmk Hmklazy Hfree.
  apply node_ok_of_pnode; [apply (transparent_nonalloc_no segs ms model x8 _ Hsvc eq_refl Hno) |]. split.
  - intros [[e He] | []]; cbn [open_nx].
    + rewrite <- (apply_effect_copyins_no_write ms (errno_ret e) reads).
      apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | | exact Hh | exact Hlazy].
      rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
    + rewrite <- (apply_effect_copyins_no_write ms (alloc_fd (m_fds model)) reads).
      apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | | apply Hmk | apply Hmklazy].
      rewrite Hchk. apply check_open_result_copyins_ok_iff.
      right. exists (alloc_fd (m_fds model)). auto.
  - intros e st Hss.
    destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. injection Hmat as <-.
        exists (inl (exist _ er Her)). cbn [open_nx].
        rewrite apply_effect_copyins_no_write. split; reflexivity.
      * subst fd. rewrite (materialize_model_accesses_no_lazy _ _ (Hmklazy _)) in Hmat.
        injection Hmat as <-.
        exists (inr tt). cbn [open_nx]. rewrite apply_effect_copyins_no_write. split; reflexivity.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. discriminate.
      * rewrite (materialize_model_accesses_no_lazy _ _ (Hmklazy _)) in Hmat. discriminate.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * congruence.
      * rewrite Hmk in Hh2. discriminate.
    + exfalso. rewrite Hchk in Hc. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hc).
Qed.

Lemma rz_open : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  alloc_no_b (bv_unsigned x8) = false ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  sys_rob segs (mkCfg ms model) ->
  (forall e, In e openat_errnos ->
     realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                       (mk (alloc_fd (m_fds model)))) B ->
  realizes segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hlazy Hsvc Hno Hchk Hmk Hmklazy Hfree Hrob HA HB.
  apply (rz_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - eapply node_open; eassumption.
  - exact Hrob.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.

End WithSegs.
