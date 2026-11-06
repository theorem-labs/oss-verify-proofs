(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg CatSim ShapeAlg LazyRestrict LazyRestrictRun.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.   (* [comment removed for export] *)

Lemma node_account : forall ms model ms' model',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model').
Proof. intros. apply node_instr_acct; assumption. Qed.

Lemma rz_dsteps : forall c c' T,
  dsteps segs c c' -> realizes segs c' T -> realizes segs c T.
Proof.
  intros c c' T H; induction H as [c | ms model ms' model' c3 Hh Hsvc Hacc H IH]; intros Hr; [exact Hr|].
  eapply rz_silent1; [apply node_account; [exact Hh | exact Hsvc | exact Hacc] | apply IH; exact Hr].
Qed.

(* [comment removed for export] *)
Lemma rz_account_step : forall ms model ms' model' T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  realizes segs (mkCfg ms' model') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model ms' model' T Hh Hsvc Hacc Hr.
  eapply rz_silent1; [apply node_account; eassumption | exact Hr].
Qed.

Section WithLazy.
Variables L S : list (word * word).
Hypothesis HL : lazy_ranges_okb segs L = true.

(* [comment removed for export] *)
Lemma rz_step_lazy : forall msF ms1 model T,
  lazy_inv L S model ->
  m_halted model = None ->
  ms_svc_pending msF = None ->
  RiscvSemantics.step segs (restrict L S msF) = MachineOk ms1 ->
  (forall model', lazy_inv L S model' -> same_but_materialized model model' ->
     realizes segs (mkCfg (unrestrict_to L S msF ms1) model') T) ->
  realizes segs (mkCfg msF model) T.
Proof.
  intros msF ms1 model T Hinv Hh Hsvc Hstep Hk.
  destruct (account_step_restrict segs L S HL msF ms1 model Hinv Hstep)
    as (model' & Hacc & Hinv' & Hsame & _).
  eapply rz_account_step; [exact Hh | exact Hsvc | exact Hacc |].
  apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Theorem rz_msteps_lazy : forall msF ms1 model T,
  lazy_inv L S model ->
  m_halted model = None ->
  msteps segs (restrict L S msF) ms1 ->
  (forall model', lazy_inv L S model' -> same_but_materialized model model' ->
     m_halted model' = None ->
     restrict L S (unrestrict_to L S msF ms1) = ms1 ->
     realizes segs (mkCfg (unrestrict_to L S msF ms1) model') T) ->
  realizes segs (mkCfg msF model) T.
Proof.
  intros msF ms1 model T Hinv Hh Hms Hk.
  destruct (msteps_restrict segs L S HL msF ms1 model Hinv Hh Hms)
    as (model' & Hd & Hinv' & Hsame & Hh' & Hr).
  eapply rz_dsteps; [exact Hd|]. apply Hk; assumption.
Qed.

End WithLazy.
End WithSegs.
