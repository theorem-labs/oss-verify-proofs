(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize.
Import ListNotations.

Section WithSegs.
Variable segs : list Segment.

Inductive safe_reach (Q : config -> Prop) : config -> Prop :=
| sr_done : forall c, Q c -> safe_reach Q c
| sr_node : forall c (I : Type) (nx : I -> config) (i0 : I),
    node_ok segs c I (fun _ => []) nx ->
    (forall i, safe_reach Q (nx i)) ->
    safe_reach Q c.

#[using="Type"] Lemma sr_bind : forall (P Q : config -> Prop) c,
  safe_reach P c -> (forall c', P c' -> safe_reach Q c') -> safe_reach Q c.
Proof.
  intros P Q c H K. induction H as [c HP | c I nx i0 Hn Hk IH].
  - apply K. exact HP.
  - apply (sr_node Q c I nx i0 Hn). exact IH.
Qed.

#[using="Type"] Lemma sr_mono : forall (P Q : config -> Prop) c,
  safe_reach P c -> (forall c', P c' -> Q c') -> safe_reach Q c.
Proof. intros P Q c H K. eapply sr_bind; [exact H|]. intros c' HP. apply sr_done. auto. Qed.

#[using="Type"] Lemma sr_realizes : forall (Q : config -> Prop) c T,
  safe_reach Q c -> (forall c', Q c' -> realizes segs c' T) -> realizes segs c T.
Proof.
  intros Q c T H K. induction H as [c HP | c I nx i0 Hn Hk IH].
  - apply K. exact HP.
  - apply (rz_silent_all segs c I nx T i0 Hn). exact IH.
Qed.

#[using="Type"] Lemma sr_must_exit : forall (Q : config -> Prop) c code,
  safe_reach Q c -> (forall c', Q c' -> must_exit_at_cfg ACFG segs code c') -> must_exit_at_cfg ACFG segs code c.
Proof.
  intros Q c code H K. induction H as [c HP | c I nx i0 [Hc Hs] Hk IH].
  - apply K. exact HP.
  - apply must_exit_at_cfg_running.
    + eapply sstep_halted_none. apply (Hc i0).
    + exists [], (SNext (nx i0)). apply Hc.
    + intros evs Herr. destruct (Hs evs SError Herr) as (i & _ & Hx). discriminate.
    + intros evs c' Hss. destruct (Hs evs (SNext c') Hss) as (i & -> & Hx).
      inversion Hx; subst. apply IH.
Qed.

#[using="Type"] Lemma sr_no_error : forall (Q : config -> Prop) c,
  safe_reach Q c -> (forall c', Q c' -> ~ reaches_error_cfg segs ACFG c') -> ~ reaches_error_cfg segs ACFG c.
Proof.
  intros Q c H K. induction H as [c HP | c I nx i0 [Hc Hs] Hk IH].
  - apply K. exact HP.
  - intros (tr & c' & evs & Hstar & Herr).
    inversion Hstar as [| c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + destruct (Hs evs SError Herr) as (i & _ & Hx). discriminate.
    + destruct (Hs e (SNext c2) Hss) as (i & -> & Hx). inversion Hx; subst.
      apply (IH i). exists tr2, c', evs. auto.
Qed.

#[using="Type"] Lemma sr_step : forall Q ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  safe_reach Q (mkCfg ms' model) ->
  safe_reach Q (mkCfg ms model).
Proof.
  intros. eapply (sr_node Q _ unit (fun _ => mkCfg ms' model) tt); [eapply node_instr; eauto|].
  intros []; assumption.
Qed.

End WithSegs.

Arguments safe_reach segs Q c.
