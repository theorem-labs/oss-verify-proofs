(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib.Logic Require Import Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run RiscvSemantics MemImageType StackLayout.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
intros cfg i m _.
destruct (classic (exists eff' m' evs',
syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false))
as [H | H]; [left; exact H | right].
intros eff' m' evs' Hspec.
destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity |].
exfalso. apply H. exists eff', m', evs'. split; [exact Hspec | exact E].
Qed.
Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.
Lemma run_decided_classic : forall cfg img lim en inp, run_decided cfg img lim en inp.
Proof. intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp. cbn [run_decided]. apply decided_from_classic. Qed.
Lemma must_exit_in_at_cfg_down : forall cfg1 cfg2 segs S c,
cfg_le cfg1 cfg2 ->
must_exit_in_at_cfg cfg2 segs S c ->
must_exit_in_at_cfg cfg1 segs S c.
Proof.
intros cfg1 cfg2 segs S c Hle H.
exact (must_exit_in_at_cfg_mono cfg1 cfg2 segs S c Hle (decided_from_classic cfg1 segs c) H).
Qed.
Lemma must_exit_in_scfg_down : forall cfg1 cfg2 S img lim en inp,
cfg_le cfg1 cfg2 ->
must_exit_in_scfg cfg2 S img lim en inp ->
must_exit_in_scfg cfg1 S img lim en inp.
Proof.
intros cfg1 cfg2 S img lim en inp Hle H.
exact (must_exit_in_scfg_mono cfg1 cfg2 S img lim en inp Hle (run_decided_classic cfg1 img lim en inp) H).
Qed.
Lemma must_exit_in_scfg_forced_only : forall cfg S img lim en inp,
must_exit_in_scfg cfg S img lim en inp ->
must_exit_in_scfg forced_only_cfg S img lim en inp.
Proof.
intros cfg S img lim en inp H.
exact (must_exit_in_scfg_down forced_only_cfg cfg S img lim en inp (forced_only_cfg_least cfg) H).
Qed.
Lemma must_exit_in_at_cfg_forced_only : forall cfg segs S c,
must_exit_in_at_cfg cfg segs S c ->
must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
intros cfg segs S c H.
exact (must_exit_in_at_cfg_down forced_only_cfg cfg segs S c (forced_only_cfg_least cfg) H).
Qed.
