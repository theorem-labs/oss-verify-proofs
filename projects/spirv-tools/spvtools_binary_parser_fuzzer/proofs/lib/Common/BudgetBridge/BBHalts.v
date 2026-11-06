(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.BudgetBridge Require Import BBCore.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma relimc_halted : forall L c, m_halted (cfg_model (relimc L c)) = m_halted (cfg_model c).
Proof. intros L [ms m]. reflexivity. Qed.
Lemma relimc_killed : forall L c, m_killed (cfg_model (relimc L c)) = m_killed (cfg_model c).
Proof. intros L [ms m]. reflexivity. Qed.

Lemma must_exit_relim_down : forall segs cfg S L c2,
  must_exit_in_at_cfg cfg segs S c2 ->
  forall c, c2 = relimc L c -> climit c <= L -> ~ reaches_budget_refused_cfg segs cfg c -> cfit c ->
  must_exit_in_at_cfg cfg segs S c.
Proof.
  intros segs cfg S L c2 H.
  induction H as [c2 code Hh Hin Hk | c2 Hnone Hprog Hnoerr Hnext IH]; intros c E HL Hn Hf; subst c2.
  - rewrite relimc_halted in Hh. rewrite relimc_killed in Hk.
    exact (must_exit_in_at_cfg_halted cfg segs S c code Hh Hin Hk).
  - rewrite relimc_halted in Hnone.
    pose proof (nreach_here segs cfg c Hn) as Hn1.
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + destruct Hprog as (evs & st & Hs).
      destruct (sstep_relim_down segs cfg L c evs st HL Hn1 Hf Hs) as (r1 & Hs1 & _).
      exists evs, r1. exact Hs1.
    + intros evs Herr. apply (Hnoerr evs).
      exact (sstep_relim_up segs cfg L c evs SError HL Hn1 Hf Herr).
    + intros evs c' Hs.
      pose proof (sstep_relim_up segs cfg L c evs (SNext c') HL Hn1 Hf Hs) as Hs2. cbn [relim_to] in Hs2.
      apply (IH evs (relimc L c') Hs2 c' eq_refl).
      * rewrite (sstep_limit segs cfg c evs c' Hn1 Hf Hs). exact HL.
      * exact (nreach_step segs cfg c evs c' Hn Hs).
      * exact (sstep_fit segs cfg c evs c' Hs Hf).
Qed.

Theorem must_exit_in_scfg_budget_down : forall cfg S img en inp L1 L2, L1 <= L2 ->
  ~ run_scfg_budget_refused cfg img L1 en inp ->
  must_exit_in_scfg cfg S img L2 en inp -> must_exit_in_scfg cfg S img L1 en inp.
Proof.
  intros cfg S [segs pc ph] [sp brk mb rnd] inp L1 L2 HL Hn H. cbn [must_exit_in_scfg run_scfg_budget_refused] in *.
  apply (must_exit_relim_down segs cfg S L2 _ H (init_config segs pc ph sp brk mb rnd L1 inp)).
  - symmetry. apply init_config_relim.
  - rewrite init_config_limit. exact HL.
  - exact Hn.
  - apply init_config_fit.
Qed.

Theorem halts_budgets_of_larger : forall cfg S img L1 L2, L1 <= L2 ->
  (forall en inp, valid_entry img en inp -> valid_input inp -> must_exit_in_scfg cfg S img L2 en inp) ->
  halts_allowed_T_scfg_budgets cfg L1 S img.
Proof.
  intros cfg S img L1 L2 HL H en inp Hen Hinp Hb.
  exact (must_exit_in_scfg_budget_down cfg S img en inp L1 L2 HL Hb (H en inp Hen Hinp)).
Qed.
