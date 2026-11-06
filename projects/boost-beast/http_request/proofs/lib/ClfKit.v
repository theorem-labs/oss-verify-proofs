(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg ExitSim ShapeAlg Nodes AgentLib RefNodes AgentNodes StartupTac ClfME.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Kit.
  Variable segs : list Segment.
  Context {SC : StepCfg}.
  Variable code : word.
  #[local] Notation "'MEX'" := (must_exit_at_cfg the_scfg segs code).

  (* [comment removed for export] *)
  Lemma mex_step : forall ms ms' model,
    m_halted model = None -> m_vm_lazy model = [] ->
    ms_svc_pending ms = None -> RiscvSemantics.step segs ms = MachineOk ms' ->
    MEX (mkCfg ms' model) -> MEX (mkCfg ms model).
  Proof.
    intros ms ms' model Hh Hl Hsvc Hst K.
    eapply (me_node segs code _ unit tt); [exact Hh | apply node_instr; eassumption | intros []; exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma mex_msteps : forall ms ms' model,
    m_halted model = None -> m_vm_lazy model = [] ->
    msteps segs ms ms' -> MEX (mkCfg ms' model) -> MEX (mkCfg ms model).
  Proof.
    intros ms ms' model Hh Hl MS K. induction MS as [ms | ms ms1 ms2 Hsvc Hst H2 IH]; [exact K|].
    eapply mex_step; [exact Hh | exact Hl | exact Hsvc | exact Hst | apply IH; exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma bwd_mex : forall model,
    m_halted model = None -> m_vm_lazy model = [] ->
    bwd segs (fun st => MEX (mkCfg st model)).
  Proof. intros model Hh Hl st st' MS K. eapply mex_msteps; eassumption. Qed.

  (* [comment removed for export] *)
  Lemma mex_set_tid : forall regs (pc : word) mem rom model w,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 96 -> m_tid model = None ->
    (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       MEX (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model))) ->
    MEX (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros regs pc mem rom model w HF HE Hh Hl H17 Htid K.
    eapply mex_step; [exact Hh | exact Hl | reflexivity | eapply step_ecall_epend; eassumption |].
    eapply (me_node segs code _ tid_I (exist _ (Z_to_bv 64 1) one_tid_ok));
      [exact Hh | eapply node_set_tid; [exact Hh | exact Hl | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
    intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply K. exact Ht.
  Qed.

  (* [comment removed for export] *)
  Lemma mex_exit : forall regs (pc : word) mem rom model w,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
    bv_and (getr regs 10) (Z_to_bv 64 255) = code ->
    MEX (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros regs pc mem rom model w HF HE Hh Hl H17 H10.
    eapply mex_step; [exact Hh | exact Hl | reflexivity | eapply step_ecall_epend; eassumption |].
    set (ms1 := epend regs pc mem rom (getr regs 17)).
    assert (Hsvc : ms_svc_pending ms1 = Some (getr regs 17)) by reflexivity.
    assert (Hx8 : is_exit_no (getr regs 17)).
    { unfold is_exit_no. destruct H17 as [-> | ->]; [right | left]; reflexivity. }
    assert (Hgpr : ms_gpr ms1 0 = getr regs 10) by apply ms_gpr_epend0.
    apply must_exit_at_cfg_running.
    - exact Hh.
    - do 2 eexists. eapply sstep_cfg_exit; [exact Hh | exact Hsvc | | apply m_halted_with_halted | apply m_killed_with_halted].
      apply exit_dispatch_ok. rewrite in_sysno_sys_input. exact Hx8.
    - intros evs Hss. apply sstep_cfg_sub in Hss.
      destruct (sstep_exit_inv segs _ _ _ _ _ Hh Hsvc Hx8 Hss) as [_ D]. discriminate D.
    - intros evs cq Hss. apply sstep_cfg_sub in Hss.
      destruct (sstep_exit_inv segs _ _ _ _ _ Hh Hsvc Hx8 Hss) as [_ E]. injection E as E2. rewrite E2.
      apply must_exit_at_cfg_halted; cbn [cfg_model].
      + rewrite m_halted_with_halted, Hgpr, H10. reflexivity.
      + apply m_killed_with_halted.
  Qed.
End Kit.
