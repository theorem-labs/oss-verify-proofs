(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Frame RegsEquiv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma sstep_scfg_eqv_ms : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
  exists X', sstep_cfg segs cfg (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv segs ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hms <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_cfg_instr; auto; congruence|]. split; [exact Hms| reflexivity].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_unmodeled; auto; congruence| exact I].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_cfg_syscall segs cfg ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption
        | rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  - (* [comment removed for export] *)
    exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_materialization_fault segs cfg ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption
      | rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption| assumption| assumption].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_exit segs cfg ms' mo x8 eff model' evs0 code);
        [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_killed segs cfg ms' mo x8 eff model' evs0 sig);
        [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_unmodeled segs cfg ms' mo x8);
      [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption].
Qed.

Lemma sstep_scfg_eqv : forall c c' evs X, cfg_eqv c c' ->
  sstep_cfg segs cfg c evs X -> exists X', sstep_cfg segs cfg c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_scfg_eqv_ms ms ms'); assumption.
Qed.

Lemma star_scfg_eqv : forall c tr c1, star_cfg segs cfg c tr c1 ->
  forall c', cfg_eqv c c' -> exists c1', star_cfg segs cfg c' tr c1' /\ cfg_eqv c1 c1'.
Proof.
  intros c tr c1 H. induction H as [c | c evs c2 tr c3 Hst Hstar IH]; intros c' Heqv.
  - exists c'. split; [apply star_cfg_refl| exact Heqv].
  - destruct (sstep_scfg_eqv c c' evs (SNext c2) Heqv Hst) as (X' & Hst' & HX).
    destruct X' as [c2'|]; simpl in HX; [|contradiction].
    destruct (IH c2' HX) as (c3' & Hstar' & H3).
    exists c3'. split; [eapply star_cfg_step; eassumption| exact H3].
Qed.

Lemma obs_trace_scfg_eqv : forall c c' tr, cfg_eqv c c' ->
  obs_trace_cfg segs cfg c tr -> obs_trace_cfg segs cfg c' tr.
Proof.
  intros c c' tr Heqv (tr' & c1 & Hstar & Hp).
  destruct (star_scfg_eqv c tr' c1 Hstar c' Heqv) as (c1' & Hstar' & _).
  exists tr', c1'. split; assumption.
Qed.

Lemma reaches_error_scfg_eqv : forall c c', cfg_eqv c c' ->
  reaches_error_cfg segs cfg c -> reaches_error_cfg segs cfg c'.
Proof.
  intros c c' Heqv (tr & c1 & evs & Hstar & Hst).
  destruct (star_scfg_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  destruct (sstep_scfg_eqv c1 c1' evs SError H1 Hst) as (X' & Hst' & HX).
  destruct X'; simpl in HX; [contradiction|].
  exists tr, c1', evs. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma behaves_cfg_eqv : forall c c' T, cfg_eqv c c' ->
  behaves_cfg cfg segs c T -> behaves_cfg cfg segs c' T.
Proof.
  intros c c' T Heqv [Hobs Herr]. pose proof (cfg_eqv_sym _ _ Heqv) as Heqv'. split.
  - intros tr. split; intros H.
    + apply Hobs. exact (obs_trace_scfg_eqv _ _ tr Heqv' H).
    + exact (obs_trace_scfg_eqv _ _ tr Heqv (proj2 (Hobs tr) H)).
  - intros H. apply Herr. exact (reaches_error_scfg_eqv _ _ Heqv' H).
Qed.

End WithSegs.
