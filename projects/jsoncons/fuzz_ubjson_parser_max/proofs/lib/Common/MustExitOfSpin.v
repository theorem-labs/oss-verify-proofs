(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Common Require Import MustExitOfShape.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Theorem srealizes_must_exit : forall S c T,
srealizes segs scfg c T ->
exits_in S T ->
m_halted (cfg_model c) = None ->
must_exit_in_at_cfg scfg segs S c.
Proof.
intros S c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh Hsl | c T T' H IH Heq];
intros HX Hrun.
- destruct Hnode as [Hcomp Hsound].
apply must_exit_in_at_cfg_running.
+ exact Hrun.
+ exists (evs i0), (SNext (nx i0)). apply Hcomp.
+ intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Hbad). discriminate Hbad.
+ intros e c' Hss.
destruct (Hsound e (SNext c') Hss) as (i & -> & Heqc). injection Heqc as ->.
destruct (sstep_cfg_next_halts_by_exit _ _ _ _ _ Hss)
as [Hnone | [(evs0 & code & Hevs & Hcode & Hnk) | (evs0 & sig & Hevs & Hsig)]].
* apply IH; [| exact Hnone]. eapply exits_in_alt_branch. exact HX.
* apply (must_exit_in_at_cfg_halted scfg segs S (nx i) code Hcode); [| exact Hnk].
destruct HX as [HE _]. apply (HE evs0 code (m_fs (cfg_model (nx i)))).
rewrite <- Hevs. apply node_branch_trace.
* exfalso. destruct HX as [_ HK]. apply (HK evs0 sig (m_fs (cfg_model (nx i)))).
rewrite <- Hevs. apply node_branch_trace.
- exfalso. exact (Hh Hrun).
- exfalso. exact Hsl.
- apply IH; [| exact Hrun]. eapply exits_in_t_eq; [apply t_eq_sym; exact Heq | exact HX].
Qed.
Corollary srealizes_must_exit_init : forall S pc ph sp brk0 mbase rnd lim inp T,
srealizes segs scfg (init_config segs pc ph sp brk0 mbase rnd lim inp) T ->
exits_in S T ->
must_exit_in_at_cfg scfg segs S (init_config segs pc ph sp brk0 mbase rnd lim inp).
Proof.
intros S pc ph sp brk0 mbase rnd lim inp T H HX.
apply (srealizes_must_exit S _ T H HX). reflexivity.
Qed.
Lemma realizes_of_srealizes : forall c T,
srealizes segs scfg c T -> realizes segs scfg c T.
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh Hsl | c T T' H IH Heq].
- exact (rz_node segs scfg c I evs nx T i0 Hnode IH).
- exact (rz_halt segs scfg c Hh).
- exfalso. exact Hsl.
- exact (rz_conseq segs scfg c T T' IH Heq).
Qed.
End WithSegs.
