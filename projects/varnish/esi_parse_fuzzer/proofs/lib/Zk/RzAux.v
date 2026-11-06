(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import PropExec MState Mem Exec RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Context {BW : BWorld}.

(* [comment removed for export] *)
Lemma realizes_unique : forall c A B, realizes0 segs c A -> realizes0 segs c B -> t_eq A B.
Proof.
  intros c A B HA HB tr. rewrite <- (realizes0_obs_iff segs c A HA tr), <- (realizes0_obs_iff segs c B HB tr). tauto.
Qed.

(* [comment removed for export] *)
Lemma rz_step_fwd : forall ms md ms' T,
  m_halted md = None -> m_vm_lazy md = [] ->
  ms_svc_pending ms = None -> RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes segs (mkCfg ms md) T -> realizes segs (mkCfg ms' md) T.
Proof.
  intros ms md ms' T Hh Hl Hsvc Hst H.
  assert (Hss : sstep_cfg segs ACFG (mkCfg ms md) [] (SNext (mkCfg ms' md))).
  { apply (sstep_cfg_instr segs ACFG ms md ms' md Hh Hsvc). rewrite (mi_account_step_no_lazy segs ms md Hl), Hst. reflexivity. }
  constructor. intros Hne'.
  pose proof (rz_unwrap segs _ T H (never_excused_instr_back segs ms md ms' Hl Hsvc Hst Hne')) as H0.
  destruct (realizes0_step segs _ _ _ _ H0 Hss) as [T' H'].
  apply (rz_conseq0 segs _ T' T H').
  apply (realizes_unique (mkCfg ms md)); [| exact H0].
  eapply rz_step0; eauto.
Qed.

Lemma rz_msteps_fwd : forall ms ms' md T,
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.msteps segs ms ms' ->
  realizes segs (mkCfg ms md) T -> realizes segs (mkCfg ms' md) T.
Proof.
  intros ms ms' md T Hh Hl Hms. induction Hms as [ms | ms ms1 ms2 [Hsvc Hst] Hrest IH]; intros H; [exact H|].
  apply IH. eapply rz_step_fwd; eauto.
Qed.

(* [comment removed for export] *)
Lemma rz_evt_fwd : forall ms ms1 md T,
  evt segs (fun ms' => ms' = ms1) ms ->
  m_halted md = None -> m_vm_lazy md = [] ->
  realizes segs (mkCfg ms md) T -> realizes segs (mkCfg ms1 md) T.
Proof.
  intros ms ms1 md T (ms' & Hrun & ->) Hh Hl H. eapply rz_msteps_fwd; eauto.
Qed.

End WithSegs.
