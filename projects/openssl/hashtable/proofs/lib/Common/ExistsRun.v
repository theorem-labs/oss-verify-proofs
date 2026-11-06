(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence Classifier.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CatSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section WithSegs.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Definition reach (c c' : config) : Prop := star segs c [] c'.

  Lemma reach_refl : forall c, reach c c.
  Proof. intros c. apply star_refl. Qed.

  Lemma reach_trans : forall c1 c2 c3, reach c1 c2 -> reach c2 c3 -> reach c1 c3.
  Proof.
    intros c1 c2 c3 H1 H2. unfold reach.
    rewrite <- (app_nil_r []). eapply star_trans; eassumption.
  Qed.

  Lemma reach_star : forall c1 c2 tr c3, reach c1 c2 -> star segs c2 tr c3 -> star segs c1 tr c3.
  Proof.
    intros c1 c2 tr c3 H1 H2. change tr with ([] ++ tr). eapply star_trans; eassumption.
  Qed.

  Lemma reach_step : forall c c', sstep segs c [] (SNext c') -> reach c c'.
  Proof. intros c c' H. apply star_one. exact H. Qed.

  (* [comment removed for export] *)
  Lemma reach_instr : forall ms model ms',
    m_halted model = None ->
    m_vm_lazy model = [] ->
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    reach (mkCfg ms model) (mkCfg ms' model).
  Proof.
    intros ms model ms' Hh Hlazy Hsvc Hstep. apply reach_step.
    apply (sstep_instr segs ms model ms' model Hh Hsvc).
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma reach_msteps : forall ms ms' model,
    m_halted model = None ->
    m_vm_lazy model = [] ->
    msteps segs ms ms' ->
    reach (mkCfg ms model) (mkCfg ms' model).
  Proof.
    intros ms ms' model Hh Hlazy Hms.
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH].
    - apply reach_refl.
    - eapply reach_trans; [eapply reach_instr; eassumption | exact IH].
  Qed.

  (* [comment removed for export] *)
  Lemma reach_syscall : forall ms model x8 eff model' model'',
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ->
    m_halted model' = None ->
    materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
    reach (mkCfg ms model) (mkCfg (advance_past_svc (apply_effect ms eff)) model'').
  Proof.
    intros ms model x8 eff model' model'' Hh Hsvc Hspec Hh' Hmat. apply reach_step.
    exact (sstep_syscall segs ms model x8 eff model' model'' [] Hh Hsvc Hspec Hh' Hmat).
  Qed.

  (* [comment removed for export] *)
  Lemma reaches_error_of_unmodeled_syscall : forall c0 ms model x8,
    reach c0 (mkCfg ms model) ->
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input segs ms x8) model Unmodeled ->
    reaches_error segs c0.
  Proof.
    intros c0 ms model x8 Hr Hh Hsvc Hun.
    exists [], (mkCfg ms model), []. split; [exact Hr |].
    exact (sstep_syscall_unmodeled segs ms model x8 Hh Hsvc Hun).
  Qed.
End WithSegs.

(* [comment removed for export] *)
Lemma bh_errors_run_of_reaches_error : forall segs pc ph lim sp brk0 mbase rnd inp,
  reaches_error segs (init_config segs pc ph sp brk0 mbase rnd lim inp) ->
  bh_errors (run (mkImage segs pc ph) lim (mkEntry sp brk0 mbase rnd) inp).
Proof. intros. cbn [run bh_errors]. exact H. Qed.

Lemma bh_errors_scfg_may_fail : forall img lim en inp,
  bh_errors (run img lim en inp) -> bh_errors (run_scfg may_fail_cfg img lim en inp).
Proof.
  intros img lim en inp H. destruct (run_scfg_may_fail img lim en inp) as (_ & He & _ & _).
  apply He. exact H.
Qed.

(* [comment removed for export] *)
Lemma good_input_s_of_good_input : forall O1 O2 inp,
  good_input O1 O2 inp -> good_input_s may_fail_cfg O1 O2 inp.
Proof. intros O1 O2 inp H. apply good_input_s_may_fail. exact H. Qed.
