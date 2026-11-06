(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run RiscvSemantics MemImageType StackLayout.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Common Require Import
BudgetBridgeCore BudgetBridgeMm BudgetBridgeStep BudgetBridgeRun BudgetBridgeMove BudgetBridgeInvArms BudgetBridge.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section Transfer.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable L : Z.
Lemma m_halted_setlim : forall m, m_halted (setlim L m) = m_halted m.
Proof. reflexivity. Qed.
Lemma m_killed_setlim : forall m, m_killed (setlim L m) = m_killed m.
Proof. reflexivity. Qed.
Lemma must_exit_in_at_cfg_budget_transfer : forall S c2,
must_exit_in_at_cfg cfg segs S c2 ->
forall c, c2 = liftc L c ->
nref segs cfg c -> okl L c ->
must_exit_in_at_cfg cfg segs S c.
Proof.
intros S c2 H.
induction H as [c2 code Hh Hin Hk | c2 Hnone Hprog Hnoerr Hnext IH]; intros c Ec Hn Hl; subst c2.
- apply (must_exit_in_at_cfg_halted cfg segs S c code).
+ rewrite <- Hh. unfold liftc. cbn [cfg_model]. symmetry. apply m_halted_setlim.
+ exact Hin.
+ rewrite <- Hk. unfold liftc. cbn [cfg_model]. symmetry. apply m_killed_setlim.
- pose proof (okc_of segs cfg L c Hn Hl) as Hok.
apply must_exit_in_at_cfg_running.
+ rewrite <- Hnone. unfold liftc. cbn [cfg_model]. symmetry. apply m_halted_setlim.
+ destruct Hprog as (evs & st & Hss).
destruct (step_bwd segs cfg L move_charge_le c evs st Hok Hss) as (r1 & Hss1 & _).
exists evs, r1. exact Hss1.
+ intros evs Herr. apply (Hnoerr evs).
exact (step_fwd segs cfg L move_charge_le c evs SError Hok Herr).
+ intros evs c' Hss1.
apply (IH evs (liftc L c')).
* exact (step_fwd segs cfg L move_charge_le c evs (SNext c') Hok Hss1).
* reflexivity.
* exact (nref_step segs cfg c evs c' Hn Hss1).
* exact (okl_step segs cfg L move_charge_le bounded_pres c evs c' Hn Hl Hss1).
Qed.
End Transfer.
Theorem must_exit_in_scfg_budget_transfer : forall cfg S img L1 L2 en inp,
L1 <= L2 ->
must_exit_in_scfg cfg S img L2 en inp ->
~ run_scfg_budget_refused cfg img L1 en inp ->
must_exit_in_scfg cfg S img L1 en inp.
Proof.
intros cfg S [segs pc ph] L1 L2 [sp brk0 mbase rnd] inp Hle Hme Hnr.
unfold must_exit_in_scfg, run_scfg_budget_refused in *.
set (c0 := init_config segs pc ph sp brk0 mbase rnd L1 inp) in *.
assert (Hn : nref segs cfg c0).
{ intros tr c Hst Hb. apply Hnr. exists tr, c. split; assumption. }
pose proof (init_config_okl segs pc ph sp brk0 mbase rnd L1 L2 inp Hle) as Hl. fold c0 in Hl.
rewrite (init_config_setlim segs pc ph sp brk0 mbase rnd L1 L2 inp) in Hme. fold c0 in Hme.
exact (must_exit_in_at_cfg_budget_transfer segs cfg L2 S _ Hme c0 eq_refl Hn Hl).
Qed.
Corollary must_exit_in_scfg_of_larger_budget : forall cfg S img L1 L2 en inp,
L1 <= L2 ->
source_within_budget_scfg cfg L1 img en inp ->
must_exit_in_scfg cfg S img L2 en inp ->
must_exit_in_scfg cfg S img L1 en inp.
Proof.
intros cfg S img L1 L2 en inp Hle Hwb Hme.
exact (must_exit_in_scfg_budget_transfer cfg S img L1 L2 en inp Hle Hme Hwb).
Qed.
Lemma source_le_target : source_alloc_limit <= target_alloc_limit.
Proof. unfold source_alloc_limit, target_alloc_limit. lia. Qed.
