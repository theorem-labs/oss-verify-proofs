(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BCatSim BazyRestrict.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.

Inductive dsteps : config -> config -> Prop :=
| ds_refl : forall c, dsteps c c
| ds_step : forall ms model ms' model' c3,
    m_halted model = None ->
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms', model') ->
    dsteps (mkCfg ms' model') c3 ->
    dsteps (mkCfg ms model) c3.

Lemma dsteps_account : forall ms model ms' model' c3,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  dsteps (mkCfg ms' model') c3 ->
  dsteps (mkCfg ms model) c3.
Proof. intros. eapply ds_step; eassumption. Qed.

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
