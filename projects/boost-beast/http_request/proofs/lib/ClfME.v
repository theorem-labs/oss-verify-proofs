(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg ExitSim ShapeAlg RefNodes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition fo_scfg : StepCfg := {| the_scfg := Run.forced_only_cfg |}.

Lemma must_exit_with_fo : forall code img lim en inp,
  (match img, en with
   | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
       @must_exit_at_cfg (@the_scfg fo_scfg) segs code (init_config segs pc ph sp brk0 mbase rnd lim inp)
   end) ->
  must_exit_with_scfg Run.forced_only_cfg code img lim en inp.
Proof. intros code [segs pc ph] lim [sp brk0 mbase rnd] inp H. exact H. Qed.

Section ME.
  Variable segs : list Segment.
  Context {SC : StepCfg}.
  Variable code : word.
  #[local] Notation "'must_exit_at'" := (must_exit_at_cfg the_scfg).

  (* [comment removed for export] *)
  Lemma me_node : forall c (I : Type) (i0 : I) (evs : I -> list event) (nx : I -> config),
    m_halted (cfg_model c) = None -> node_ok segs c I evs nx ->
    (forall i, must_exit_at segs code (nx i)) -> must_exit_at segs code c.
  Proof.
    intros c I i0 evs nx Hh [N1 N2] K. apply must_exit_at_cfg_running.
    - exact Hh.
    - exists (evs i0), (SNext (nx i0)). apply N1.
    - intros e Hss. destruct (N2 e SError Hss) as (i & _ & D). discriminate D.
    - intros e cq Hss. destruct (N2 e _ Hss) as (i & _ & E). injection E as E2. rewrite E2. apply K.
  Qed.

  (* [comment removed for export] *)
  Lemma me_mstep : forall ms ms' model,
    m_halted model = None -> m_vm_lazy model = [] -> mstep segs ms ms' ->
    must_exit_at segs code (mkCfg ms' model) -> must_exit_at segs code (mkCfg ms model).
  Proof.
    intros ms ms' model Hh Hl [Hsvc Hst] K.
    eapply (me_node _ unit tt); [exact Hh| apply (node_instr segs); eassumption| intros []; exact K].
  Qed.

  Lemma me_msteps : forall ms ms' model,
    m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
    must_exit_at segs code (mkCfg ms' model) -> must_exit_at segs code (mkCfg ms model).
  Proof.
    intros ms ms' model Hh Hl MS K. induction MS as [ms | ms ms1 ms2 H1 H2 IH]; [exact K|].
    eapply me_mstep; [exact Hh| exact Hl| exact H1| apply IH; exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma me_evt : forall (P : machine_state -> Prop) ms model,
    m_halted model = None -> m_vm_lazy model = [] -> evt segs P ms ->
    (forall ms', P ms' -> must_exit_at segs code (mkCfg ms' model)) -> must_exit_at segs code (mkCfg ms model).
  Proof. intros P ms model Hh Hl (ms' & MS & HP) K. eapply me_msteps; [exact Hh| exact Hl| exact MS| apply K; exact HP]. Qed.

  (* [comment removed for export] *)
  Definition ecall_of (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) (m ro : word -> option byte) : machine_state :=
    {| ms_regs := R; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := Some (reg_get R 17);
       ms_resv := rv; ms_fcsr := fc; ms_mem := m; ms_rom := ro |}.

  Lemma step_ecall_MS : forall R F pc fc rv m ro w,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    RiscvSemantics.step segs (MS R F pc fc rv m ro) = MachineOk (ecall_of R F pc fc rv m ro).
  Proof.
    intros R F pc fc rv m ro w HF HE. unfold RiscvSemantics.step, step_accesses, ms_pc. cbn [ms_pc_val MS]. rewrite HF.
    unfold decode_exec_accesses. rewrite HE. reflexivity.
  Qed.

  Lemma adv_set_ecall_of : forall R F pc fc rv m ro v,
    advance_past_svc (set_gpr0 (ecall_of R F pc fc rv m ro) v) = MS (bvmap_set 10 v R) F (pc + Z_to_bv 64 4)%bv fc rv m ro.
  Proof. intros. unfold set_gpr0, set_reg. assert (E : bv_eqb (10 : reg) 0 = false) by (vm_compute; reflexivity). rewrite E. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma me_set_tid : forall R F (pc : Z) fc rv m ro model w,
    fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] -> m_tid model = None ->
    reg_get R 17 = Z_to_bv 64 96 -> 0 <= pc -> pc + 4 < 2^64 ->
    (forall tid, 0 < bv_unsigned tid < PID_MAX_ENVELOPE ->
       must_exit_at segs code (mkCfg (MS (bvmap_set 10 tid R) F (Z_to_bv 64 (pc + 4)) fc rv m ro) (with_tid tid model))) ->
    must_exit_at segs code (mkCfg (MS R F (Z_to_bv 64 pc) fc rv m ro) model).
  Proof.
    intros R F pc fc rv m ro model w HF HE Hh Hl Ht H17 P0 P4 K.
    eapply me_mstep; [exact Hh| exact Hl| split; [reflexivity| eapply step_ecall_MS; eassumption]|].
    assert (ND : node_ok segs (mkCfg (ecall_of R F (Z_to_bv 64 pc) fc rv m ro) model) tid_I (fun _ => [])
              (fun i => mkCfg (advance_past_svc (set_gpr0 (ecall_of R F (Z_to_bv 64 pc) fc rv m ro) (proj1_sig i))) (with_tid (proj1_sig i) model))).
    { eapply (node_set_tid segs); [exact Hh| exact Hl| cbn [ms_svc_pending ecall_of]; rewrite H17; reflexivity| rewrite Z_to_bv_unsigned; reflexivity| exact Ht]. }
    eapply (me_node _ tid_I (exist _ (Z_to_bv 64 1) one_tid_ok)); [exact Hh| exact ND|].
    intros [tid Htid]. cbn [proj1_sig].
    rewrite adv_set_ecall_of. replace (Z_to_bv 64 pc + Z_to_bv 64 4)%bv with (Z_to_bv 64 (pc + 4)).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite !Z.mod_small by lia. reflexivity. }
    apply K. exact Htid.
  Qed.

  (* [comment removed for export] *)
  Lemma me_exit : forall R F (pc : word) fc rv m ro model w,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    (reg_get R 17 = Z_to_bv 64 94 \/ reg_get R 17 = Z_to_bv 64 93) ->
    bv_and (reg_get R 10) (Z_to_bv 64 255) = code ->
    must_exit_at segs code (mkCfg (MS R F pc fc rv m ro) model).
  Proof.
    intros R F pc fc rv m ro model w HF HE Hh Hl H17 H10.
    eapply me_mstep; [exact Hh| exact Hl| split; [reflexivity| eapply step_ecall_MS; eassumption]|].
    set (ms1 := ecall_of R F pc fc rv m ro).
    assert (Hsvc : ms_svc_pending ms1 = Some (reg_get R 17)) by reflexivity.
    assert (Hx8 : is_exit_no (reg_get R 17)).
    { unfold is_exit_no. destruct H17 as [-> | ->]; rewrite Z_to_bv_unsigned; [right| left]; reflexivity. }
    assert (Hgpr : ms_gpr ms1 0 = reg_get R 10) by reflexivity.
    apply must_exit_at_cfg_running.
    - exact Hh.
    - do 2 eexists. eapply sstep_cfg_exit; [exact Hh| exact Hsvc| | apply m_halted_with_halted | apply m_killed_with_halted].
      apply exit_dispatch_ok. rewrite in_sysno_sys_input. exact Hx8.
    - intros evs Hss. apply sstep_cfg_sub in Hss.
      destruct (sstep_exit_inv segs _ _ _ _ _ Hh Hsvc Hx8 Hss) as [_ D]. discriminate D.
    - intros evs cq Hss. apply sstep_cfg_sub in Hss.
      destruct (sstep_exit_inv segs _ _ _ _ _ Hh Hsvc Hx8 Hss) as [_ E]. injection E as E2. rewrite E2.
      apply must_exit_at_cfg_halted; cbn [cfg_model].
      + rewrite m_halted_with_halted, Hgpr, H10. reflexivity.
      + apply m_killed_with_halted.
  Qed.
End ME.
