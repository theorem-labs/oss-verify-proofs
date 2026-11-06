(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import CatSim LazyRestrict.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive dsteps : config -> config -> Prop :=
| ds_refl : forall c, dsteps c c
| ds_step : forall ms model ms' model' c3,
    m_halted model = None ->
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms', model') ->
    dsteps (mkCfg ms' model') c3 ->
    dsteps (mkCfg ms model) c3.

Lemma dsteps_trans : forall c1 c2 c3, dsteps c1 c2 -> dsteps c2 c3 -> dsteps c1 c3.
Proof.
  intros c1 c2 c3 H; induction H; [auto|].
  intros H23. eapply ds_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma sstep_account_inv : forall ms model ms' model' e st,
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  sstep segs (mkCfg ms model) e st ->
  e = [] /\ st = SNext (mkCfg ms' model').
Proof.
  intros ms model ms' model' e st Hsvc Hacc Hss.
  inversion Hss; subst; try congruence.
  match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
    rewrite Hacc in H; inversion H; subst end.
  split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_account_inv : forall cfg ms model ms' model' e st,
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  sstep_cfg segs cfg (mkCfg ms model) e st ->
  e = [] /\ st = SNext (mkCfg ms' model').
Proof.
  intros cfg ms model ms' model' e st Hsvc Hacc Hss.
  apply (sstep_account_inv ms model ms' model' e st Hsvc Hacc). eapply sstep_cfg_sub. exact Hss.
Qed.

Lemma dsteps_account : forall ms model ms' model' c3,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  dsteps (mkCfg ms' model') c3 ->
  dsteps (mkCfg ms model) c3.
Proof. intros. eapply ds_step; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithLazy.
Variables L S : list (word * word).
Hypothesis HL : lazy_ranges_okb segs L = true.

Theorem account_step_restrict : forall msF ms1 model,
  lazy_inv L S model ->
  RiscvSemantics.step segs (restrict L S msF) = MachineOk ms1 ->
  exists model',
    mi_account_step segs msF model = MachineOk (unrestrict_to L S msF ms1, model')
    /\ lazy_inv L S model'
    /\ same_but_materialized model model'
    /\ (forall a, hiddenb L S a = true -> ms_mem ms1 a = None).
Proof.
  intros msF ms1 model Hinv Hstep.
  destruct (step_restrict segs L S msF ms1 HL Hstep) as (rep & Hsa & Hval & Hvis & Hnone & _).
  destruct (materialize_restrict L S model (accessed_ranges _ rep) Hinv Hvis) as (pages & Hmat & Hinv').
  exists (with_vm_backing (m_vm_lazy model) pages model).
  unfold mi_account_step. rewrite Hsa, Hmat, Hval.
  split; [reflexivity|]. split; [exact Hinv'|]. split; [|exact Hnone].
  apply same_but_materialized_with_vm_backing.
Qed.

(* [comment removed for export] *)
Theorem msteps_restrict_gen : forall ms0 ms1,
  msteps segs ms0 ms1 ->
  forall msF model,
    ms0 = restrict L S msF ->
    lazy_inv L S model ->
    m_halted model = None ->
    exists model',
      dsteps (mkCfg msF model) (mkCfg (unrestrict_to L S msF ms1) model')
      /\ lazy_inv L S model'
      /\ same_but_materialized model model'
      /\ restrict L S (unrestrict_to L S msF ms1) = ms1.
Proof.
  intros ms0 ms1 Hms; induction Hms as [ms | ms ms' ms'' Hsvc Hstep Hms IH];
    intros msF model -> Hinv Hh.
  - exists model. rewrite unrestrict_restrict_self.
    split; [apply ds_refl|]. split; [exact Hinv|].
    split; [apply same_but_materialized_refl | reflexivity].
  - destruct (account_step_restrict msF ms' model Hinv Hstep) as (model1 & Hacc & Hinv1 & Hsame1 & Hnone).
    specialize (IH (unrestrict_to L S msF ms') model1).
    rewrite (restrict_unrestrict_to L S msF ms' Hnone) in IH.
    assert (Hh1 : m_halted model1 = None)
      by (rewrite (same_but_materialized_halted _ _ Hsame1); exact Hh).
    destruct (IH eq_refl Hinv1 Hh1) as (model' & Hd & Hinv' & Hsame' & Hr).
    rewrite unrestrict_to_idem in Hd, Hr.
    exists model'. split; [|split; [exact Hinv'|split; [|exact Hr]]].
    + eapply dsteps_account; [exact Hh | exact Hsvc | exact Hacc | exact Hd].
    + eapply same_but_materialized_trans; eassumption.
Qed.

Theorem msteps_restrict : forall msF ms1 model,
  lazy_inv L S model ->
  m_halted model = None ->
  msteps segs (restrict L S msF) ms1 ->
  exists model',
    dsteps (mkCfg msF model) (mkCfg (unrestrict_to L S msF ms1) model')
    /\ lazy_inv L S model'
    /\ same_but_materialized model model'
    /\ m_halted model' = None
    /\ restrict L S (unrestrict_to L S msF ms1) = ms1.
Proof.
  intros msF ms1 model Hinv Hh Hms.
  destruct (msteps_restrict_gen _ _ Hms msF model eq_refl Hinv Hh) as (model' & Hd & Hinv' & Hsame & Hr).
  exists model'. repeat (split; [assumption|]).
  split; [|exact Hr].
  rewrite (same_but_materialized_halted _ _ Hsame). exact Hh.
Qed.

End WithLazy.
End WithSegs.
