(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

Lemma in_sysno_sys_input : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Lemma in_arg0_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

Lemma gpr0_reg_eq : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : bv 5).
Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ms_gpr0_apply_effect : forall ms eff,
  ms_gpr (advance_past_svc (apply_effect ms eff)) 0 = eff_ret eff.
Proof.
  intros ms eff. unfold ms_gpr, advance_past_svc, apply_effect. cbn [ms_regs].
  unfold set_reg. change (bv_eqb 10 0) with false. cbv iota. cbn [ms_regs].
  rewrite gpr0_reg_eq.
  unfold Riscv.Sem.reg_get. rewrite Riscv.Prelude.bvmap_get_set_same. reflexivity.
Qed.

Lemma ms_gpr0_set_gpr0 : forall ms r,
  ms_gpr (advance_past_svc (set_gpr0 ms r)) 0 = r.
Proof.
  intros ms r. unfold ms_gpr, advance_past_svc, set_gpr0. cbn [ms_regs].
  unfold set_reg. change (bv_eqb 10 0) with false. cbv iota. cbn [ms_regs].
  rewrite gpr0_reg_eq.
  unfold Riscv.Sem.reg_get. rewrite Riscv.Prelude.bvmap_get_set_same. reflexivity.
Qed.

Lemma m_halted_materialize : forall m accesses m',
  materialize_model_accesses m accesses = Some m' -> m_halted m' = m_halted m.
Proof.
  intros m accesses m' H.
  destruct (materialize_model_accesses_frame m accesses m' H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold m_halted. rewrite Hp. reflexivity.
Qed.

Lemma m_halted_account_step : forall segs ms model ms' model',
  mi_account_step segs ms model = MachineOk (ms', model') -> m_halted model' = m_halted model.
Proof.
  intros segs ms model ms' model' H.
  destruct (mi_account_step_model_frame segs ms model ms' model' H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold m_halted. rewrite Hp. reflexivity.
Qed.

(* [comment removed for export] *)

Definition is_exit_no (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Lemma syscall_spec_exit : forall i m o,
  is_exit_no (in_sysno i) ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof.
  intros i m o [E|E]; unfold syscall_spec, dispatch; rewrite E; reflexivity.
Qed.

Lemma exit_dispatch_ok : forall i m,
  is_exit_no (in_sysno i) ->
  syscall_spec i m
    (Ok (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []).
Proof.
  intros i m Hno. apply (proj2 (syscall_spec_exit i m _ Hno)).
  unfold exit_spec, set_halted, ret_only, modify, bind, pure. cbn.
  eexists tt, (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m),
    [], []. repeat split; reflexivity.
Qed.

Lemma exit_dispatch_ok_inv : forall i m eff m' evs,
  is_exit_no (in_sysno i) ->
  syscall_spec i m (Ok eff m' evs) ->
  eff = mkEffect (Z_to_bv 64 0) [] [] /\
  m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m /\ evs = [].
Proof.
  intros i m eff m' evs Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct. rewrite app_nil_l in *. repeat split; congruence.
Qed.

Lemma exit_dispatch_no_unmodeled : forall i m,
  is_exit_no (in_sysno i) -> ~ syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct.
Qed.

Lemma m_halted_with_halted : forall c m, m_halted (with_halted c m) = Some c.
Proof. intros c m. autorewrite with model. reflexivity. Qed.

Lemma m_killed_with_halted : forall c m, m_killed (with_halted c m) = None.
Proof. intros c m. autorewrite with model. reflexivity. Qed.

Lemma m_fs_with_halted : forall c m, m_fs (with_halted c m) = m_fs m.
Proof. intros c m. autorewrite with model. reflexivity. Qed.

Section WithCfg.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_cfg_instr_inv : forall ms model ms' model' e st,
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  sstep_cfg segs cfg (mkCfg ms model) e st ->
  e = [] /\ st = SNext (mkCfg ms' model').
Proof.
  intros ms model ms' model' e st Hsvc Hstep Hss.
  inversion Hss; subst; try congruence.
  match goal with
  | H : mi_account_step segs ms model = MachineOk (_, _) |- _ =>
      rewrite Hstep in H; inversion H; subst
  end.
  split; reflexivity.
Qed.

Lemma node_instr_cfg : forall ms model ms' model',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  node_ok_cfg cfg segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model').
Proof.
  intros ms model ms' model' Hh Hsvc Hstep. split.
  - intros []. apply sstep_cfg_instr; assumption.
  - intros e st Hss.
    destruct (sstep_cfg_instr_inv ms model ms' model' e st Hsvc Hstep Hss) as [-> ->].
    exists tt. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rzc_step : forall ms model ms' model' T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  realizes_cfg cfg segs (mkCfg ms' model') T ->
  realizes_cfg cfg segs (mkCfg ms model) T.
Proof.
  intros ms model ms' model' T Hh Hsvc Hstep Hc.
  eapply rzc_silent1; [apply node_instr_cfg; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma account_step_no_lazy_ok : forall ms model ms',
  m_vm_lazy model = [] ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  mi_account_step segs ms model = MachineOk (ms', model).
Proof.
  intros ms model ms' Hlazy Hstep.
  rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma node_instr_cfg_no_lazy : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  node_ok_cfg cfg segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep.
  apply node_instr_cfg; [exact Hh | exact Hsvc | apply account_step_no_lazy_ok; assumption].
Qed.

Lemma rzc_step_no_lazy : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes_cfg cfg segs (mkCfg ms' model) T ->
  realizes_cfg cfg segs (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rzc_silent1; [apply node_instr_cfg_no_lazy; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Fixpoint asteps (n : nat) (s : machine_state * Model) {struct n}
    : machine_result (machine_state * Model) :=
  match n with
  | O => MachineOk s
  | S n' =>
    match ms_svc_pending (fst s) with
    | Some _ => MachineOk s
    | None =>
      match mi_account_step segs (fst s) (snd s) with
      | MachineOk s' => asteps n' s'
      | MachineFault => MachineFault
      | MachineUnmodeled => MachineUnmodeled
      end
    end
  end.

Lemma asteps_O : forall s, asteps 0 s = MachineOk s.
Proof. reflexivity. Qed.

Lemma asteps_svc_pending : forall n s x8,
  ms_svc_pending (fst s) = Some x8 -> asteps n s = MachineOk s.
Proof. intros [|n] s x8 H; cbn [asteps]; [reflexivity | rewrite H; reflexivity]. Qed.

Lemma asteps_S : forall n s,
  ms_svc_pending (fst s) = None ->
  asteps (S n) s =
    match mi_account_step segs (fst s) (snd s) with
    | MachineOk s' => asteps n s'
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof. intros n s H. cbn [asteps]. rewrite H. reflexivity. Qed.

Lemma asteps_add : forall n m s,
  asteps (n + m) s =
    match asteps n s with
    | MachineOk s' => asteps m s'
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof.
  induction n as [|n IH]; intros m s; [reflexivity|].
  cbn [Nat.add asteps].
  destruct (ms_svc_pending (fst s)) as [x8|] eqn:Hsvc.
  - symmetry. apply (asteps_svc_pending m s x8 Hsvc).
  - destruct (mi_account_step segs (fst s) (snd s)) as [s'| |]; [apply IH | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma asteps_trans : forall n m s1 s2 s3,
  asteps n s1 = MachineOk s2 -> asteps m s2 = MachineOk s3 ->
  asteps (n + m) s1 = MachineOk s3.
Proof. intros n m s1 s2 s3 H1 H2. rewrite asteps_add, H1. exact H2. Qed.

(* [comment removed for export] *)
Lemma asteps_frame : forall n ms model ms' model',
  asteps n (ms, model) = MachineOk (ms', model') ->
  m_fd model' = m_fd model /\
  m_vmmaps model' = m_vmmaps model /\
  m_vm_lazy model' = m_vm_lazy model /\
  m_io model' = m_io model /\
  m_fsys model' = m_fsys model /\
  m_proc model' = m_proc model /\
  m_lim model' = m_lim model.
Proof.
  induction n as [|n IH]; intros ms model ms' model' H.
  - cbn in H. inversion H; subst. repeat split; reflexivity.
  - cbn [asteps fst snd] in H.
    destruct (ms_svc_pending ms) as [x8|].
    + inversion H; subst. repeat split; reflexivity.
    + destruct (mi_account_step segs ms model) as [[ms1 model1]| |] eqn:Hstep;
        [| discriminate H | discriminate H].
      destruct (mi_account_step_model_frame segs ms model ms1 model1 Hstep)
        as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
      destruct (IH ms1 model1 ms' model' H) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      repeat split; congruence.
Qed.

Lemma asteps_halted : forall n ms model ms' model',
  asteps n (ms, model) = MachineOk (ms', model') -> m_halted model' = m_halted model.
Proof.
  intros n ms model ms' model' H.
  destruct (asteps_frame n ms model ms' model' H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold m_halted. rewrite Hp. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma asteps_det_path : forall n ms model ms' model',
  m_halted model = None ->
  asteps n (ms, model) = MachineOk (ms', model') ->
  det_path_cfg cfg segs (mkCfg ms model) [] (mkCfg ms' model').
Proof.
  induction n as [|n IH]; intros ms model ms' model' Hh H.
  - cbn in H. inversion H; subst. apply dpc_refl.
  - cbn [asteps fst snd] in H.
    destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
    + inversion H; subst. apply dpc_refl.
    + destruct (mi_account_step segs ms model) as [[ms1 model1]| |] eqn:Hstep;
        [| discriminate H | discriminate H].
      change (@nil event) with (@nil event ++ @nil event).
      eapply dpc_step.
      * apply node_instr_cfg; eassumption.
      * apply IH; [| exact H].
        rewrite (m_halted_account_step segs ms model ms1 model1 Hstep). exact Hh.
Qed.

(* [comment removed for export] *)
Lemma asteps_star_cfg : forall n ms model ms' model',
  m_halted model = None ->
  asteps n (ms, model) = MachineOk (ms', model') ->
  star_cfg segs cfg (mkCfg ms model) [] (mkCfg ms' model').
Proof.
  intros n ms model ms' model' Hh H.
  apply det_path_cfg_star. eapply asteps_det_path; eassumption.
Qed.

Lemma asteps_star : forall n ms model ms' model',
  m_halted model = None ->
  asteps n (ms, model) = MachineOk (ms', model') ->
  star segs (mkCfg ms model) [] (mkCfg ms' model').
Proof.
  intros n ms model ms' model' Hh H.
  eapply star_cfg_sub. eapply asteps_star_cfg; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rzc_asteps : forall n ms model ms' model' T,
  m_halted model = None ->
  asteps n (ms, model) = MachineOk (ms', model') ->
  realizes_cfg cfg segs (mkCfg ms' model') T ->
  realizes_cfg cfg segs (mkCfg ms model) T.
Proof.
  intros n ms model ms' model' T Hh H Hc.
  eapply rzc_det_path_silent; [eapply asteps_det_path; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma within_budget_asteps : forall n ms model ms' model',
  m_halted model = None ->
  asteps n (ms, model) = MachineOk (ms', model') ->
  within_budget_cfg cfg segs (mkCfg ms model) -> within_budget_cfg cfg segs (mkCfg ms' model').
Proof.
  intros n ms model ms' model' Hh H Hwb.
  eapply within_budget_cfg_star; [exact Hwb | eapply asteps_star_cfg; eassumption].
Qed.

(* [comment removed for export] *)
Fixpoint rsteps (n : nat) (ms : machine_state) {struct n} : machine_result machine_state :=
  match n with
  | O => MachineOk ms
  | S n' =>
    match ms_svc_pending ms with
    | Some _ => MachineOk ms
    | None =>
      match RiscvSemantics.step segs ms with
      | MachineOk ms' => rsteps n' ms'
      | MachineFault => MachineFault
      | MachineUnmodeled => MachineUnmodeled
      end
    end
  end.

Lemma rsteps_svc_pending : forall n ms x8,
  ms_svc_pending ms = Some x8 -> rsteps n ms = MachineOk ms.
Proof. intros [|n] ms x8 H; cbn [rsteps]; [reflexivity | rewrite H; reflexivity]. Qed.

Lemma rsteps_add : forall n m ms,
  rsteps (n + m) ms =
    match rsteps n ms with
    | MachineOk ms' => rsteps m ms'
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof.
  induction n as [|n IH]; intros m ms; [reflexivity|].
  cbn [Nat.add rsteps].
  destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - symmetry. apply (rsteps_svc_pending m ms x8 Hsvc).
  - destruct (RiscvSemantics.step segs ms) as [ms'| |]; [apply IH | reflexivity | reflexivity].
Qed.

Lemma rsteps_trans : forall n m ms1 ms2 ms3,
  rsteps n ms1 = MachineOk ms2 -> rsteps m ms2 = MachineOk ms3 ->
  rsteps (n + m) ms1 = MachineOk ms3.
Proof. intros n m ms1 ms2 ms3 H1 H2. rewrite rsteps_add, H1. exact H2. Qed.

(* [comment removed for export] *)
Lemma asteps_no_lazy : forall n ms model,
  m_vm_lazy model = [] ->
  asteps n (ms, model) =
    match rsteps n ms with
    | MachineOk ms' => MachineOk (ms', model)
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof.
  induction n as [|n IH]; intros ms model Hlazy; [reflexivity|].
  cbn [asteps rsteps fst snd].
  destruct (ms_svc_pending ms) as [x8|]; [reflexivity|].
  rewrite (mi_account_step_no_lazy segs ms model Hlazy).
  destruct (RiscvSemantics.step segs ms) as [ms'| |]; [apply IH; exact Hlazy | reflexivity | reflexivity].
Qed.

Lemma asteps_of_rsteps : forall n ms model ms',
  m_vm_lazy model = [] ->
  rsteps n ms = MachineOk ms' ->
  asteps n (ms, model) = MachineOk (ms', model).
Proof. intros n ms model ms' Hlazy H. rewrite (asteps_no_lazy n ms model Hlazy), H. reflexivity. Qed.

Lemma rzc_rsteps : forall n ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  rsteps n ms = MachineOk ms' ->
  realizes_cfg cfg segs (mkCfg ms' model) T ->
  realizes_cfg cfg segs (mkCfg ms model) T.
Proof.
  intros n ms model ms' T Hh Hlazy H Hc.
  eapply rzc_asteps; [exact Hh | apply asteps_of_rsteps; eassumption | exact Hc].
Qed.

Lemma rsteps_det_path : forall n ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  rsteps n ms = MachineOk ms' ->
  det_path_cfg cfg segs (mkCfg ms model) [] (mkCfg ms' model).
Proof.
  intros n ms model ms' Hh Hlazy H.
  eapply asteps_det_path; [exact Hh | apply asteps_of_rsteps; eassumption].
Qed.

Lemma rsteps_star_cfg : forall n ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  rsteps n ms = MachineOk ms' ->
  star_cfg segs cfg (mkCfg ms model) [] (mkCfg ms' model).
Proof.
  intros n ms model ms' Hh Hlazy H.
  eapply asteps_star_cfg; [exact Hh | apply asteps_of_rsteps; eassumption].
Qed.

(* [comment removed for export] *)

Lemma reaches_error_cfg_star : forall c tr c',
  star_cfg segs cfg c tr c' ->
  reaches_error_cfg segs cfg c' -> reaches_error_cfg segs cfg c.
Proof.
  intros c tr c' Hstar (tr' & c'' & evs & Hstar' & Herr).
  exists (tr ++ tr'), c'', evs. split; [| exact Herr].
  eapply star_cfg_trans; eassumption.
Qed.

Lemma reaches_error_cfg_det_path : forall c tr c',
  det_path_cfg cfg segs c tr c' ->
  reaches_error_cfg segs cfg c' -> reaches_error_cfg segs cfg c.
Proof.
  intros c tr c' Hp. apply (reaches_error_cfg_star c tr c').
  apply det_path_cfg_star. exact Hp.
Qed.

Lemma reaches_error_cfg_here : forall c evs,
  sstep_cfg segs cfg c evs SError -> reaches_error_cfg segs cfg c.
Proof. intros c evs H. exists [], c, evs. split; [apply star_cfg_refl | exact H]. Qed.

(* [comment removed for export] *)
Lemma reaches_error_cfg_unmodeled_here : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model Unmodeled ->
  reaches_error_cfg segs cfg (mkCfg ms model).
Proof.
  intros ms model x8 Hh Hsvc Hspec.
  apply (reaches_error_cfg_here _ []).
  apply (sstep_cfg_syscall_unmodeled segs cfg ms model x8); assumption.
Qed.

Lemma reaches_error_cfg_unmodeled_syscall : forall c tr ms model x8,
  star_cfg segs cfg c tr (mkCfg ms model) ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model Unmodeled ->
  reaches_error_cfg segs cfg c.
Proof.
  intros c tr ms model x8 Hstar Hh Hsvc Hspec.
  eapply reaches_error_cfg_star; [exact Hstar |].
  eapply reaches_error_cfg_unmodeled_here; eassumption.
Qed.

Lemma reaches_error_cfg_instr_fault : forall ms model,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineFault ->
  reaches_error_cfg segs cfg (mkCfg ms model).
Proof.
  intros ms model Hh Hsvc Hstep.
  apply (reaches_error_cfg_here _ []). apply sstep_cfg_instr_fault; assumption.
Qed.

Lemma reaches_error_cfg_instr_unmodeled : forall ms model,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineUnmodeled ->
  reaches_error_cfg segs cfg (mkCfg ms model).
Proof.
  intros ms model Hh Hsvc Hstep.
  apply (reaches_error_cfg_here _ []). apply sstep_cfg_instr_unmodeled; assumption.
Qed.

(* [comment removed for export] *)
Lemma asteps_bad_reaches_error : forall n ms model,
  m_halted model = None ->
  (asteps n (ms, model) = MachineFault \/ asteps n (ms, model) = MachineUnmodeled) ->
  reaches_error_cfg segs cfg (mkCfg ms model).
Proof.
  induction n as [|n IH]; intros ms model Hh H.
  - cbn in H. destruct H as [H | H]; discriminate H.
  - cbn [asteps fst snd] in H.
    destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
    + destruct H as [H | H]; discriminate H.
    + destruct (mi_account_step segs ms model) as [[ms1 model1]| |] eqn:Hstep.
      * eapply reaches_error_cfg_star.
        { apply star_cfg_one. apply sstep_cfg_instr; eassumption. }
        apply IH; [| exact H].
        rewrite (m_halted_account_step segs ms model ms1 model1 Hstep). exact Hh.
      * apply reaches_error_cfg_instr_fault; assumption.
      * apply reaches_error_cfg_instr_unmodeled; assumption.
Qed.

Lemma asteps_fault_reaches_error : forall n ms model,
  m_halted model = None ->
  asteps n (ms, model) = MachineFault ->
  reaches_error_cfg segs cfg (mkCfg ms model).
Proof. intros n ms model Hh H. eapply asteps_bad_reaches_error; [exact Hh | left; exact H]. Qed.

Lemma asteps_unmodeled_reaches_error : forall n ms model,
  m_halted model = None ->
  asteps n (ms, model) = MachineUnmodeled ->
  reaches_error_cfg segs cfg (mkCfg ms model).
Proof. intros n ms model Hh H. eapply asteps_bad_reaches_error; [exact Hh | right; exact H]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition spurious_ret (i : SyscallInput) (m : Model) (ret : word) : Prop :=
  injected_family_off cfg i = true
  /\ refusal_b i m ret = true
  /\ (exists eff' m' evs',
        syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false).

Lemma spurious_refusal_cfg_ret : forall i m eff,
  spurious_refusal_cfg cfg i m eff <-> spurious_ret i m (eff_ret eff).
Proof. intros i m eff. unfold spurious_refusal_cfg, spurious_ret. reflexivity. Qed.

(* [comment removed for export] *)
Definition sysno_family_off (no : Z) : bool :=
  match injected_arm no with
  | Some a => negb (family_may_fail cfg (ia_family a))
  | None => false
  end.

Lemma injected_family_off_sysno : forall ms x8,
  injected_family_off cfg (sys_input segs ms x8) = sysno_family_off (bv_unsigned x8).
Proof. reflexivity. Qed.

Lemma injected_family_off_sysno' : forall i,
  injected_family_off cfg i = sysno_family_off (bv_unsigned (in_sysno i)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_syscall_on : forall ms model x8 eff model' model'' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  injected_family_off cfg (sys_input segs ms x8) = false ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
  sstep_cfg segs cfg (mkCfg ms model) evs
    (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
Proof.
  intros ms model x8 eff model' model'' evs Hh Hsvc Hspec Hon Hh' Hmat.
  eapply sstep_cfg_syscall; try eassumption.
  apply spurious_refusal_family_on. exact Hon.
Qed.

Lemma sstep_cfg_syscall_nonrefusal : forall ms model x8 eff model' model'' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
  sstep_cfg segs cfg (mkCfg ms model) evs
    (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
Proof.
  intros ms model x8 eff model' model'' evs Hh Hsvc Hspec Hnr Hh' Hmat.
  eapply sstep_cfg_syscall; try eassumption.
  apply spurious_refusal_not_refusal. exact Hnr.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_next_running_spec : forall ms model x8 e c',
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e (SNext c') ->
  m_halted (cfg_model c') = None ->
  exists eff m',
    syscall_spec (sys_input segs ms x8) model (Ok eff m' e)
    /\ eff_ret eff = ms_gpr (cfg_ms c') 0.
Proof.
  intros ms model x8 e c' Hsvc Hss Hrun.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    eexists _, _. split; [eassumption |].
    cbn [cfg_ms]. rewrite ms_gpr0_apply_effect. reflexivity.
  - (* [comment removed for export] *) cbn [cfg_model] in Hrun. congruence.
  - (* [comment removed for export] *)
    cbn [cfg_model] in Hrun.
    match goal with Hk : m_killed _ = Some _ |- _ =>
      rewrite (m_killed_of_m_halted_none _ Hrun) in Hk; discriminate Hk end.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_of_sstep_next : forall ms model e c',
  sstep segs (mkCfg ms model) e (SNext c') ->
  (forall x8, ms_svc_pending ms = Some x8 ->
              m_halted (cfg_model c') = None ->
              ~ spurious_ret (sys_input segs ms x8) model (ms_gpr (cfg_ms c') 0)) ->
  sstep_cfg segs cfg (mkCfg ms model) e (SNext c').
Proof.
  intros ms model e c' Hss Hns.
  inversion Hss; subst.
  - apply sstep_cfg_instr; assumption.
  - eapply sstep_cfg_syscall; try eassumption.
    intro Hsp. apply spurious_refusal_cfg_ret in Hsp.
    match goal with Hs : ms_svc_pending ms = Some ?y |- _ =>
      apply (Hns y Hs) end.
    + cbn [cfg_model].
      match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ =>
        rewrite (m_halted_materialize _ _ _ Hm) end. assumption.
    + cbn [cfg_ms]. rewrite ms_gpr0_apply_effect. exact Hsp.
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_next_not_spurious : forall ms model x8 e c',
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs cfg (mkCfg ms model) e (SNext c') ->
  m_halted (cfg_model c') = None ->
  ~ spurious_ret (sys_input segs ms x8) model (ms_gpr (cfg_ms c') 0).
Proof.
  intros ms model x8 e c' Hsvc Hss Hrun.
  inversion Hss; subst; try congruence.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    cbn [cfg_ms]. rewrite ms_gpr0_apply_effect.
    intro Hsp. apply spurious_refusal_cfg_ret in Hsp. contradiction.
  - cbn [cfg_model] in Hrun. congruence.
  - cbn [cfg_model] in Hrun.
    match goal with Hk : m_killed _ = Some _ |- _ =>
      rewrite (m_killed_of_m_halted_none _ Hrun) in Hk; discriminate Hk end.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_ok_plain (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).

(* [comment removed for export] *)
Lemma node_ok_cfg_of_plain_gen : forall ms model (I J : Type)
    (evs : I -> list event) (nx : I -> config) (sel : J -> I),
  node_ok_plain (mkCfg ms model) I evs nx ->
  (forall j x8, ms_svc_pending ms = Some x8 ->
     m_halted (cfg_model (nx (sel j))) = None ->
     ~ spurious_ret (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (sel j))) 0)) ->
  (forall i, (exists j, i = sel j)
             \/ (m_halted (cfg_model (nx i)) = None
                 /\ exists x8, ms_svc_pending ms = Some x8
                    /\ spurious_ret (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0))) ->
  node_ok_cfg cfg segs (mkCfg ms model) J (fun j => evs (sel j)) (fun j => nx (sel j)).
Proof.
  intros ms model I J evs nx sel [Hcomp Hsound] Hkeep Hdrop. split.
  - intros j. apply sstep_cfg_of_sstep_next; [apply Hcomp |].
    intros x8 Hsvc Hrun. exact (Hkeep j x8 Hsvc Hrun).
  - intros e st Hss.
    destruct (Hsound e st (sstep_cfg_sub segs cfg _ _ _ Hss)) as (i & -> & ->).
    destruct (Hdrop i) as [(j & ->) | (Hrun & x8 & Hsvc & Hsp)].
    + exists j. split; reflexivity.
    + exfalso. exact (sstep_cfg_next_not_spurious ms model x8 _ _ Hsvc Hss Hrun Hsp).
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_of_plain_on : forall ms model (I : Type)
    (evs : I -> list event) (nx : I -> config),
  (forall x8, ms_svc_pending ms = Some x8 ->
              injected_family_off cfg (sys_input segs ms x8) = false) ->
  node_ok_plain (mkCfg ms model) I evs nx ->
  node_ok_cfg cfg segs (mkCfg ms model) I evs nx.
Proof.
  intros ms model I evs nx Hon Hnode.
  apply (node_ok_cfg_of_plain_gen ms model I I evs nx (fun i => i) Hnode).
  - intros j x8 Hsvc _ (Hoff & _). rewrite (Hon x8 Hsvc) in Hoff. discriminate Hoff.
  - intros i. left. exists i. reflexivity.
Qed.

Lemma node_ok_cfg_of_plain_sysno : forall ms model x8 (I : Type)
    (evs : I -> list event) (nx : I -> config),
  ms_svc_pending ms = Some x8 ->
  sysno_family_off (bv_unsigned x8) = false ->
  node_ok_plain (mkCfg ms model) I evs nx ->
  node_ok_cfg cfg segs (mkCfg ms model) I evs nx.
Proof.
  intros ms model x8 I evs nx Hsvc Hon Hnode.
  apply node_ok_cfg_of_plain_on; [| exact Hnode].
  intros y Hy. rewrite Hsvc in Hy. inversion Hy; subst y.
  rewrite injected_family_off_sysno. exact Hon.
Qed.

Lemma node_ok_cfg_of_plain_instr : forall ms model (I : Type)
    (evs : I -> list event) (nx : I -> config),
  ms_svc_pending ms = None ->
  node_ok_plain (mkCfg ms model) I evs nx ->
  node_ok_cfg cfg segs (mkCfg ms model) I evs nx.
Proof.
  intros ms model I evs nx Hsvc Hnode.
  apply node_ok_cfg_of_plain_on; [| exact Hnode].
  intros x8 Hx8. congruence.
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_of_plain_nonrefusal : forall ms model x8 (I : Type)
    (evs : I -> list event) (nx : I -> config),
  ms_svc_pending ms = Some x8 ->
  (forall i, m_halted (cfg_model (nx i)) = None ->
     refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0) = false) ->
  node_ok_plain (mkCfg ms model) I evs nx ->
  node_ok_cfg cfg segs (mkCfg ms model) I evs nx.
Proof.
  intros ms model x8 I evs nx Hsvc Hnr Hnode.
  apply (node_ok_cfg_of_plain_gen ms model I I evs nx (fun i => i) Hnode).
  - intros j y Hy Hrun (_ & Hr & _).
    rewrite Hsvc in Hy. inversion Hy; subst y.
    rewrite (Hnr j Hrun) in Hr. discriminate Hr.
  - intros i. left. exists i. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_ok_plain_outcome_listed : forall ms model x8 (I : Type)
    (evs : I -> list event) (nx : I -> config),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  node_ok_plain (mkCfg ms model) I evs nx ->
  (forall i, m_halted (cfg_model (nx i)) = None) ->
  forall eff m' evs',
    syscall_spec (sys_input segs ms x8) model (Ok eff m' evs') ->
    exists i, eff_ret eff = ms_gpr (cfg_ms (nx i)) 0.
Proof.
  intros ms model x8 I evs nx Hh Hsvc [_ Hsound] Hrun eff m' evs' Hspec.
  destruct (m_halted m') as [code|] eqn:Hh'.
  - exfalso. destruct (m_killed m') as [sig|] eqn:Hk.
    + destruct (Hsound _ _ (sstep_killed segs ms model x8 eff m' evs' sig Hh Hsvc Hspec Hk))
        as (i & _ & Hst).
      inversion Hst as [Hc]. pose proof (Hrun i) as Hr. rewrite <- Hc in Hr.
      cbn [cfg_model] in Hr. congruence.
    + destruct (Hsound _ _ (sstep_exit segs ms model x8 eff m' evs' code Hh Hsvc Hspec Hh' Hk))
        as (i & _ & Hst).
      inversion Hst as [Hc]. pose proof (Hrun i) as Hr. rewrite <- Hc in Hr.
      cbn [cfg_model] in Hr. congruence.
  - destruct (materialize_model_accesses m' (syscall_effect_accesses eff)) as [m''|] eqn:Hmat.
    + destruct (Hsound _ _ (sstep_syscall segs ms model x8 eff m' m'' evs' Hh Hsvc Hspec Hh' Hmat))
        as (i & _ & Hst).
      inversion Hst as [Hc]. exists i. rewrite <- Hc. cbn [cfg_ms].
      rewrite ms_gpr0_apply_effect. reflexivity.
    + exfalso.
      destruct (Hsound _ _ (sstep_syscall_materialization_fault segs ms model x8 eff m' evs'
                              Hh Hsvc Hspec Hh' Hmat)) as (i & _ & Hst).
      discriminate Hst.
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_of_plain_forced : forall ms model x8 (I : Type)
    (evs : I -> list event) (nx : I -> config),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  node_ok_plain (mkCfg ms model) I evs nx ->
  (forall i, m_halted (cfg_model (nx i)) = None) ->
  (forall i, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0) = true) ->
  node_ok_cfg cfg segs (mkCfg ms model) I evs nx.
Proof.
  intros ms model x8 I evs nx Hh Hsvc Hnode Hrun Hall.
  apply (node_ok_cfg_of_plain_gen ms model I I evs nx (fun i => i) Hnode).
  - intros j y Hy _ (_ & _ & (eff' & m' & evs' & Hspec & Hnr)).
    rewrite Hsvc in Hy. inversion Hy; subst y.
    destruct (node_ok_plain_outcome_listed ms model x8 I evs nx Hh Hsvc Hnode Hrun
                eff' m' evs' Hspec) as (i & Hret).
    rewrite Hret, (Hall i) in Hnr. discriminate Hnr.
  - intros i. left. exists i. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sstep_plain_halted_none : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma node_ok_cfg_of_plain_det : forall ms model
    (evs : unit -> list event) (nx : unit -> config),
  node_ok_plain (mkCfg ms model) unit evs nx ->
  node_ok_cfg cfg segs (mkCfg ms model) unit evs nx.
Proof.
  intros ms model evs nx Hnode.
  apply (node_ok_cfg_of_plain_gen ms model unit unit evs nx (fun i => i) Hnode).
  - intros [] x8 Hsvc Hrun (_ & Hr & (eff' & m' & evs' & Hspec & Hnr)).
    pose proof (sstep_plain_halted_none _ _ _ (proj1 Hnode tt)) as Hh. cbn [cfg_model] in Hh.
    assert (Hrun' : forall i : unit, m_halted (cfg_model (nx i)) = None)
      by (intros []; exact Hrun).
    destruct (node_ok_plain_outcome_listed ms model x8 unit evs nx Hh Hsvc Hnode Hrun'
                eff' m' evs' Hspec) as ([] & Hret).
    rewrite Hret, Hr in Hnr. discriminate Hnr.
  - intros i. left. exists i. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_of_plain_filter : forall ms model x8 (I J : Type)
    (evs : I -> list event) (nx : I -> config) (sel : J -> I) (j0 : J),
  ms_svc_pending ms = Some x8 ->
  injected_family_off cfg (sys_input segs ms x8) = true ->
  node_ok_plain (mkCfg ms model) I evs nx ->
  (forall i, m_halted (cfg_model (nx i)) = None) ->
  (forall j, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (sel j))) 0) = false) ->
  (forall i, (exists j, i = sel j)
             \/ refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0) = true) ->
  node_ok_cfg cfg segs (mkCfg ms model) J (fun j => evs (sel j)) (fun j => nx (sel j)).
Proof.
  intros ms model x8 I J evs nx sel j0 Hsvc Hoff Hnode Hrun Hkeep Hdrop.
  apply (node_ok_cfg_of_plain_gen ms model I J evs nx sel Hnode).
  - intros j y Hy _ (_ & Hr & _).
    rewrite Hsvc in Hy. inversion Hy; subst y.
    rewrite (Hkeep j) in Hr. discriminate Hr.
  - intros i. destruct (Hdrop i) as [Hsel | Hr]; [left; exact Hsel | right].
    split; [apply Hrun |]. exists x8. split; [exact Hsvc |].
    split; [exact Hoff | split; [exact Hr |]].
    destruct (sstep_next_running_spec ms model x8 _ _ Hsvc (proj1 Hnode (sel j0)) (Hrun (sel j0)))
      as (eff' & m' & Hspec & Hret).
    exists eff', m', (evs (sel j0)). split; [exact Hspec |].
    rewrite Hret. apply Hkeep.
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_of_plain_sum_r : forall ms model x8 (IA IB : Type)
    (evs : IA + IB -> list event) (nx : IA + IB -> config) (b0 : IB),
  ms_svc_pending ms = Some x8 ->
  injected_family_off cfg (sys_input segs ms x8) = true ->
  node_ok_plain (mkCfg ms model) (IA + IB) evs nx ->
  (forall i, m_halted (cfg_model (nx i)) = None) ->
  (forall a, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (inl a))) 0) = true) ->
  (forall b, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (inr b))) 0) = false) ->
  node_ok_cfg cfg segs (mkCfg ms model) IB (fun b => evs (inr b)) (fun b => nx (inr b)).
Proof.
  intros ms model x8 IA IB evs nx b0 Hsvc Hoff Hnode Hrun HA HB.
  apply (node_ok_cfg_of_plain_filter ms model x8 (IA + IB) IB evs nx inr b0
           Hsvc Hoff Hnode Hrun HB).
  intros [a | b]; [right; apply HA | left; exists b; reflexivity].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_sys_cfg_gen : forall ms model x8 (J : Type)
    (E : J -> SyscallEffect) (M MM : J -> Model) (EV : J -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall j, syscall_spec (sys_input segs ms x8) model (Ok (E j) (M j) (EV j))) ->
  (forall j, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model (E j)) ->
  (forall j, m_halted (M j) = None) ->
  (forall j, materialize_model_accesses (M j) (syscall_effect_accesses (E j)) = Some (MM j)) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     (exists j, eff = E j /\ m' = M j /\ evs = EV j)
     \/ (m_halted m' = None
         /\ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff)) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  node_ok_cfg cfg segs (mkCfg ms model) J EV
    (fun j => mkCfg (advance_past_svc (apply_effect ms (E j))) (MM j)).
Proof.
  intros ms model x8 J E M MM EV Hh Hsvc Hcomp Hns Hnh Hmat Hsound Hnu. split.
  - intro j. eapply sstep_cfg_syscall; [exact Hh | exact Hsvc | apply Hcomp | apply Hns
                                        | apply Hnh | apply Hmat].
  - intros e st Hss.
    inversion Hss; subst; try congruence;
      try (exfalso; apply Hnu; assumption);
      match goal with H : ms_svc_pending ms = Some ?y |- _ =>
        rewrite Hsvc in H; inversion H; subst end.
    + (* [comment removed for export] *)
      match goal with Hs : syscall_spec _ _ (Ok _ _ _) |- _ =>
        destruct (Hsound _ _ _ Hs) as [(j & -> & -> & ->) | (_ & Hsp)] end;
        [| contradiction].
      match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ =>
        rewrite (Hmat j) in Hm; inversion Hm; subst end.
      exists j. split; reflexivity.
    + (* [comment removed for export] *)
      exfalso.
      match goal with Hs : syscall_spec _ _ (Ok _ _ _) |- _ =>
        destruct (Hsound _ _ _ Hs) as [(j & -> & -> & ->) | (_ & Hsp)] end;
        [| contradiction].
      match goal with Hm : materialize_model_accesses _ _ = None |- _ =>
        rewrite (Hmat j) in Hm; discriminate Hm end.
    + (* [comment removed for export] *)
      exfalso.
      match goal with Hs : syscall_spec _ _ (Ok _ _ _), Hc : m_halted _ = Some _ |- _ =>
        destruct (Hsound _ _ _ Hs) as [(j & -> & -> & ->) | (Hn & _)];
          [rewrite (Hnh j) in Hc | rewrite Hn in Hc]; discriminate Hc end.
    + (* [comment removed for export] *)
      exfalso.
      match goal with Hs : syscall_spec _ _ (Ok _ _ _), Hk : m_killed _ = Some _ |- _ =>
        destruct (Hsound _ _ _ Hs) as [(j & -> & -> & ->) | (Hn & _)];
          [rewrite (m_killed_of_m_halted_none _ (Hnh j)) in Hk
          | rewrite (m_killed_of_m_halted_none _ Hn) in Hk]; discriminate Hk end.
Qed.

(* [comment removed for export] *)
Lemma node_sys_cfg_on : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M MM : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  injected_family_off cfg (sys_input segs ms x8) = false ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) (EV i))) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall i, m_halted (M i) = None) ->
  (forall i, materialize_model_accesses (M i) (syscall_effect_accesses (E i)) = Some (MM i)) ->
  node_ok_cfg cfg segs (mkCfg ms model) I EV
    (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (MM i)).
Proof.
  intros ms model x8 I E M MM EV Hh Hsvc Hon Hcomp Hsound Hnu Hnh Hmat.
  apply (node_sys_cfg_gen ms model x8 I E M MM EV Hh Hsvc Hcomp); try assumption.
  - intro i. apply spurious_refusal_family_on. exact Hon.
  - intros eff m' evs Hs. left. exact (Hsound eff m' evs Hs).
Qed.

(* [comment removed for export] *)
Lemma node_sys_cfg_nonrefusal : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M MM : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (E i)) = false) ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) (EV i))) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall i, m_halted (M i) = None) ->
  (forall i, materialize_model_accesses (M i) (syscall_effect_accesses (E i)) = Some (MM i)) ->
  node_ok_cfg cfg segs (mkCfg ms model) I EV
    (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (MM i)).
Proof.
  intros ms model x8 I E M MM EV Hh Hsvc Hnr Hcomp Hsound Hnu Hnh Hmat.
  apply (node_sys_cfg_gen ms model x8 I E M MM EV Hh Hsvc Hcomp); try assumption.
  - intro i. apply spurious_refusal_not_refusal. apply Hnr.
  - intros eff m' evs Hs. left. exact (Hsound eff m' evs Hs).
Qed.

(* [comment removed for export] *)
Lemma node_sys_cfg_filter : forall ms model x8 (J : Type)
    (E : J -> SyscallEffect) (M MM : J -> Model) (EV : J -> list event) (j0 : J),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  injected_family_off cfg (sys_input segs ms x8) = true ->
  (forall j, syscall_spec (sys_input segs ms x8) model (Ok (E j) (M j) (EV j))) ->
  (forall j, refusal_b (sys_input segs ms x8) model (eff_ret (E j)) = false) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     m_halted m' = None
     /\ ((exists j, eff = E j /\ m' = M j /\ evs = EV j)
         \/ refusal_b (sys_input segs ms x8) model (eff_ret eff) = true)) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall j, materialize_model_accesses (M j) (syscall_effect_accesses (E j)) = Some (MM j)) ->
  node_ok_cfg cfg segs (mkCfg ms model) J EV
    (fun j => mkCfg (advance_past_svc (apply_effect ms (E j))) (MM j)).
Proof.
  intros ms model x8 J E M MM EV j0 Hh Hsvc Hoff Hcomp Hnr Hsound Hnu Hmat.
  apply (node_sys_cfg_gen ms model x8 J E M MM EV Hh Hsvc Hcomp); try assumption.
  - intro j. apply spurious_refusal_not_refusal. apply Hnr.
  - intro j. exact (proj1 (Hsound _ _ _ (Hcomp j))).
  - intros eff m' evs Hs. destruct (Hsound eff m' evs Hs) as (Hn & [Hl | Hr]);
      [left; exact Hl | right].
    split; [exact Hn |]. split; [exact Hoff | split; [exact Hr |]].
    exists (E j0), (M j0), (EV j0). split; [apply Hcomp | apply Hnr].
Qed.

(* [comment removed for export] *)
Lemma node_sys_cfg_forced : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M MM : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) (EV i))) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     refusal_b (sys_input segs ms x8) model (eff_ret eff) = true
     /\ exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall i, m_halted (M i) = None) ->
  (forall i, materialize_model_accesses (M i) (syscall_effect_accesses (E i)) = Some (MM i)) ->
  node_ok_cfg cfg segs (mkCfg ms model) I EV
    (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (MM i)).
Proof.
  intros ms model x8 I E M MM EV Hh Hsvc Hcomp Hsound Hnu Hnh Hmat.
  apply (node_sys_cfg_gen ms model x8 I E M MM EV Hh Hsvc Hcomp); try assumption.
  - intros i (_ & _ & (eff' & m' & evs' & Hs & Hnr)).
    rewrite (proj1 (Hsound _ _ _ Hs)) in Hnr. discriminate Hnr.
  - intros eff m' evs Hs. left. exact (proj2 (Hsound eff m' evs Hs)).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_cfg_exit_inv : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  sstep_cfg segs cfg (mkCfg ms model) evs st ->
  evs = [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)] /\
  st = SNext (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
Proof.
  intros ms model x8 evs st Hh Hsvc Hx8 Hss.
  assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x8))) by exact Hx8.
  inversion Hss; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
  - exfalso.
    match goal with Hs : syscall_spec _ _ (Ok _ ?m' _), Hn : m_halted ?m' = None |- _ =>
      destruct (exit_dispatch_ok_inv _ _ _ _ _ Hxe Hs) as (_ & Hm & _);
      rewrite Hm, m_halted_with_halted in Hn; discriminate Hn end.
  - exfalso.
    match goal with Hs : syscall_spec _ _ (Ok _ ?m' _), Hn : m_halted ?m' = None |- _ =>
      destruct (exit_dispatch_ok_inv _ _ _ _ _ Hxe Hs) as (_ & Hm & _);
      rewrite Hm, m_halted_with_halted in Hn; discriminate Hn end.
  - match goal with Hs : syscall_spec _ _ (Ok _ ?m' _), Hc : m_halted ?m' = Some _ |- _ =>
      destruct (exit_dispatch_ok_inv _ _ _ _ _ Hxe Hs) as (_ & Hm & Hev);
      rewrite in_arg0_sys_input in Hm; subst;
      rewrite m_halted_with_halted in Hc; inversion Hc; subst end.
    rewrite m_fs_with_halted. split; reflexivity.
  - exfalso.
    match goal with Hs : syscall_spec _ _ (Ok _ ?m' _), Hk : m_killed ?m' = Some _ |- _ =>
      destruct (exit_dispatch_ok_inv _ _ _ _ _ Hxe Hs) as (_ & Hm & _);
      rewrite Hm, m_killed_with_halted in Hk; discriminate Hk end.
  - exfalso.
    match goal with Hs : syscall_spec _ _ Unmodeled |- _ =>
      exact (exit_dispatch_no_unmodeled _ _ Hxe Hs) end.
Qed.

Lemma node_exit_cfg : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  node_ok_cfg cfg segs (mkCfg ms model) unit
    (fun _ => [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)])
    (fun _ => mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8. split.
  - intros [].
    pose proof (sstep_cfg_exit segs cfg ms model x8
                  (mkEffect (Z_to_bv 64 0) [] [])
                  (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
                  (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) Hh Hsvc) as Hstep.
    rewrite m_fs_with_halted in Hstep. cbn [app] in Hstep.
    apply Hstep.
    + rewrite <- (in_arg0_sys_input segs ms x8). apply exit_dispatch_ok. exact Hx8.
    + apply m_halted_with_halted.
    + apply m_killed_with_halted.
  - intros e st Hss.
    destruct (sstep_cfg_exit_inv ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
    exists tt. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rzc_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes_cfg cfg segs (mkCfg ms model)
    (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8. unfold t_exit.
  eapply rzc_emit1; [apply (node_exit_cfg ms model x8 Hh Hsvc Hx8) |].
  apply rzc_halt. cbn [cfg_model]. rewrite m_halted_with_halted. discriminate.
Qed.

(* [comment removed for export] *)
Lemma rzc_exit_code : forall ms model x8 code,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  bv_and (ms_gpr ms 0) (Z_to_bv 64 255) = code ->
  realizes_cfg cfg segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof. intros ms model x8 code Hh Hsvc Hx8 <-. eapply rzc_exit; eassumption. Qed.

(* [comment removed for export] *)
Fixpoint exits_b (code : word) (fuel : nat) (ms : machine_state) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match ms_svc_pending ms with
      | Some x8 =>
          ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
          && bv_eqb (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) code
      | None =>
          match RiscvSemantics.step segs ms with
          | MachineOk ms' => exits_b code fuel' ms'
          | MachineFault | MachineUnmodeled => false
          end
      end
  end.

Lemma exits_b_realizes : forall code fuel ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  exits_b code fuel ms = true ->
  realizes_cfg cfg segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
  intros code fuel. induction fuel as [|fuel IH]; intros ms model Hh Hlazy Hc;
    [discriminate Hc|].
  cbn [exits_b] in Hc.
  destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - apply andb_true_iff in Hc as [Hx8 Hcode].
    apply bv_eqb_eq in Hcode.
    eapply rzc_exit_code; [exact Hh | exact Hsvc | | exact Hcode].
    apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
      [left | right]; exact H.
  - destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
      [| discriminate Hc | discriminate Hc].
    eapply rzc_step_no_lazy; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep |].
    apply IH; assumption.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma within_budget_alloc_not_refused : forall ms model x8,
  within_budget_cfg cfg segs (mkCfg ms model) ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_budget_refused_b (sys_input segs ms x8) model = false.
Proof.
  intros ms model x8 Hwb Hh Hsvc.
  destruct (alloc_budget_refused_b (sys_input segs ms x8) model) eqn:Hb; [| reflexivity].
  exfalso. apply (within_budget_cfg_here cfg segs _ Hwb).
  split; [exact Hh |]. right. exists x8. split; [exact Hsvc |]. left. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma within_budget_syscall_materializes : forall ms model x8 eff model' evs,
  within_budget_cfg cfg segs (mkCfg ms model) ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  m_halted model' = None ->
  exists model'', materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''.
Proof.
  intros ms model x8 eff model' evs Hwb Hh Hsvc Hspec Hh'.
  destruct (materialize_model_accesses model' (syscall_effect_accesses eff)) as [m''|] eqn:Hmat;
    [exists m''; reflexivity |].
  exfalso. apply (within_budget_cfg_here cfg segs _ Hwb).
  split; [exact Hh |]. right. exists x8. split; [exact Hsvc |]. right.
  exists eff, model', evs. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma within_budget_instr_materializes : forall ms model report,
  within_budget_cfg cfg segs (mkCfg ms model) ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk report ->
  exists model', materialize_model_accesses model (@accessed_ranges _ report) = Some model'.
Proof.
  intros ms model report Hwb Hh Hsvc Hstep.
  destruct (materialize_model_accesses model (@accessed_ranges _ report)) as [m'|] eqn:Hmat;
    [exists m'; reflexivity |].
  exfalso. apply (within_budget_cfg_here cfg segs _ Hwb).
  split; [exact Hh |]. left. split; [exact Hsvc |]. exists report. split; assumption.
Qed.

End WithCfg.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sysno_family_off_alloc_only : forall no,
  sysno_family_off (alloc_only_cfg false) no
  = (Z.eqb no 214 || Z.eqb no 216 || Z.eqb no 222 || Z.eqb no 226)%bool.
Proof.
  intros no. unfold sysno_family_off, injected_arm, injected_table.
  cbn [lookup_injected ia_no].
  repeat match goal with
  | |- context [Z.eqb ?k no] =>
      let E := fresh "E" in
      destruct (Z.eqb k no) eqn:E;
      [ apply Z.eqb_eq in E; subst no; reflexivity | apply Z.eqb_neq in E ]
  end.
  repeat match goal with
  | H : ?k <> no |- _ =>
      let E := fresh "E" in
      assert (E : Z.eqb no k = false) by (apply Z.eqb_neq; congruence); clear H;
      try rewrite E
  end.
  reflexivity.
Qed.

Lemma sysno_family_off_alloc_only_false : forall no,
  no <> 214%Z -> no <> 216%Z -> no <> 222%Z -> no <> 226%Z ->
  sysno_family_off (alloc_only_cfg false) no = false.
Proof.
  intros no H1 H2 H3 H4. rewrite sysno_family_off_alloc_only.
  apply Z.eqb_neq in H1, H2, H3, H4. rewrite H1, H2, H3, H4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma refusal_b_brk : forall i m ret,
  bv_unsigned (in_sysno i) = 214%Z ->
  refusal_b i m ret = brk_refusal_b m (in_arg i 0) ret.
Proof. intros i m ret H. unfold refusal_b. rewrite H. reflexivity. Qed.

Lemma refusal_b_enomem_arm : forall i m ret,
  (bv_unsigned (in_sysno i) = 216%Z \/ bv_unsigned (in_sysno i) = 222%Z
   \/ bv_unsigned (in_sysno i) = 226%Z) ->
  refusal_b i m ret = bv_eqb ret (errno_ret ENOMEM).
Proof.
  intros i m ret [H | [H | H]]; unfold refusal_b; rewrite H;
    cbn [Z.eqb Pos.eqb]; unfold injected_arm, injected_table;
    cbn [lookup_injected ia_no Z.eqb Pos.eqb ia_errnos];
    unfold mremap_errnos, mmap_errnos, mprotect_errnos, ret_in_errnos;
    cbn [existsb]; apply orb_false_r.
Qed.

Lemma refusal_b_no_arm : forall i m ret,
  bv_unsigned (in_sysno i) <> 214%Z ->
  injected_arm (bv_unsigned (in_sysno i)) = None ->
  refusal_b i m ret = false.
Proof.
  intros i m ret Hne Harm. unfold refusal_b.
  apply Z.eqb_neq in Hne. rewrite Hne, Harm. reflexivity.
Qed.

Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e Hin. unfold ret_in_errnos. apply existsb_exists.
  exists e. split; [exact Hin | apply bv_eqb_eq; reflexivity].
Qed.

Lemma ret_in_errnos_false : forall es r,
  (forall e, In e es -> r <> errno_ret e) -> ret_in_errnos es r = false.
Proof.
  intros es r H. unfold ret_in_errnos.
  destruct (existsb (fun e => bv_eqb r (errno_ret e)) es) eqn:E; [| reflexivity].
  apply existsb_exists in E as (e & Hin & Heq). apply bv_eqb_eq in Heq.
  exfalso. exact (H e Hin Heq).
Qed.

(* [comment removed for export] *)
Lemma errno_ret_unsigned : forall e, (0 < e <= 4095)%Z ->
  bv_unsigned (errno_ret e) = (2 ^ 64 - e)%Z.
Proof.
  intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite <- (Z.mod_add (- e) 1 (2 ^ 64)) by lia.
  replace (- e + 1 * 2 ^ 64)%Z with (2 ^ 64 - e)%Z by lia.
  apply Z.mod_small. lia.
Qed.

Lemma ret_in_errnos_below : forall es r,
  Forall (fun e => (0 < e <= 4095)%Z) es ->
  (bv_unsigned r < 2 ^ 64 - 4095)%Z ->
  ret_in_errnos es r = false.
Proof.
  intros es r Hes Hr. apply ret_in_errnos_false. intros e Hin ->.
  rewrite Forall_forall in Hes. pose proof (Hes e Hin) as He.
  rewrite (errno_ret_unsigned e He) in Hr. lia.
Qed.

Lemma not_enomem_below : forall r,
  (bv_unsigned r < 2 ^ 64 - 4095)%Z -> bv_eqb r (errno_ret ENOMEM) = false.
Proof.
  intros r Hr. destruct (bv_eqb r (errno_ret ENOMEM)) eqn:E; [| reflexivity].
  apply bv_eqb_eq in E. subst r.
  rewrite (errno_ret_unsigned ENOMEM) in Hr by (unfold ENOMEM; lia). unfold ENOMEM in Hr. lia.
Qed.

(* [comment removed for export] *)
Lemma not_enomem_page_aligned : forall r,
  (bv_unsigned r mod page_size = 0)%Z -> bv_eqb r (errno_ret ENOMEM) = false.
Proof.
  intros r Hr. destruct (bv_eqb r (errno_ret ENOMEM)) eqn:E; [| reflexivity].
  apply bv_eqb_eq in E. subst r. exfalso.
  rewrite (errno_ret_unsigned ENOMEM) in Hr by (unfold ENOMEM; lia).
  unfold ENOMEM, page_size in Hr.
  change ((2 ^ 64 - 12) mod 4096)%Z with 4084%Z in Hr. discriminate Hr.
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_may_fail_of_plain : forall segs c (I : Type)
    (evs : I -> list event) (nx : I -> config),
  node_ok_plain segs c I evs nx -> node_ok_cfg may_fail_cfg segs c I evs nx.
Proof.
  intros segs c I evs nx [Hcomp Hsound]. split.
  - intro i. apply sstep_cfg_may_fail. apply Hcomp.
  - intros e st Hss. apply Hsound. apply sstep_cfg_may_fail. exact Hss.
Qed.

(* [comment removed for export] *)

Lemma run_scfg_errors_of_reaches : forall cfg img lim en inp,
  reaches_error_cfg (img_segments img) cfg (init_cfg img lim en inp) ->
  bh_errors (run_scfg cfg img lim en inp).
Proof. intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp H. exact H. Qed.

Lemma run_scfg_errors_iff_reaches : forall cfg img lim en inp,
  bh_errors (run_scfg cfg img lim en inp)
  <-> reaches_error_cfg (img_segments img) cfg (init_cfg img lim en inp).
Proof. intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp. split; intro H; exact H. Qed.

(* [comment removed for export] *)
Lemma good_input_s_refuted_by_reaches_error : forall cfg O1 O2 inp en1 en2,
  valid_entry O1 en1 inp ->
  valid_entry O2 en2 inp ->
  reaches_error_cfg (img_segments O1) cfg (init_cfg O1 source_alloc_limit en1 inp) ->
  ~ good_input_s cfg O1 O2 inp.
Proof.
  intros cfg O1 O2 inp en1 en2 H1 H2 Herr.
  apply (good_input_s_refuted_by_source_error cfg O1 O2 inp en1 en2 H1 H2).
  apply run_scfg_errors_of_reaches. exact Herr.
Qed.
