(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import ShapeAlg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Cfg ITree Nodes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import HaltsTrace.
Import ListNotations.
Section WithSegs.
Variable segs : list Segment.
Inductive mreach : config -> Prop :=
| mr_halted : forall c, m_halted (cfg_model c) <> None -> mreach c
| mr_run : forall c,
(exists evs st, sstep_cfg segs ACFG c evs st) ->
(forall evs st, sstep_cfg segs ACFG c evs st -> exists c', st = SNext c') ->
(forall evs c', sstep_cfg segs ACFG c evs (SNext c') -> mreach c') ->
mreach c.
#[using="Type"] Lemma realizes_mreach : forall c T, realizes segs c T -> mreach c.
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
- destruct Hnode as [Hcomp Hsound]. apply mr_run.
+ exists (evs i0), (SNext (nx i0)). apply Hcomp.
+ intros e st Hss. destruct (Hsound e st Hss) as (i & -> & ->). exists (nx i). reflexivity.
+ intros e c' Hss. destruct (Hsound e (SNext c') Hss) as (i & -> & E). injection E as ->. apply IH.
- apply mr_halted. exact Hh.
- exact IH.
Qed.
#[using="Type"] Lemma sstep_into_halted : forall c evs c',
sstep_cfg segs ACFG c evs (SNext c') -> m_halted (cfg_model c') <> None ->
(exists evs0 code, evs = evs0 ++ [ExitEv code (m_fs (cfg_model c'))]
/\ m_halted (cfg_model c') = Some code /\ m_killed (cfg_model c') = None)
\/ (exists evs0 sig, evs = evs0 ++ [KillEv sig (m_fs (cfg_model c'))]).
Proof.
intros c evs c' H Hh. inversion H; subst; cbn [cfg_model] in *.
-
exfalso. apply Hh. match goal with Ha : mi_account_step _ _ _ = MachineOk _ |- _ =>
destruct (mi_account_step_model_frame _ _ _ _ _ Ha) as (_ & _ & _ & _ & _ & Hp & _) end.
unfold m_halted in *. rewrite Hp. assumption.
-
exfalso. apply Hh. match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ =>
destruct (materialize_model_accesses_frame _ _ _ Hm) as (_ & _ & _ & _ & _ & Hp & _) end.
unfold m_halted in *. rewrite Hp. assumption.
- left. eexists _, _. split; [reflexivity|]. split; assumption.
- right. eexists _, _. reflexivity.
Qed.
#[using="Type"] Lemma mreach_must_exit : forall (S : list word) c0 tr c,
star_cfg segs ACFG c0 tr c -> m_halted (cfg_model c) = None -> mreach c ->
(forall tr1 sig fs c1, star_cfg segs ACFG c0 (tr1 ++ [KillEv sig fs]) c1 -> False) ->
(forall tr1 code fs c1, star_cfg segs ACFG c0 (tr1 ++ [ExitEv code fs]) c1 -> In code S) ->
must_exit_in_at_cfg ACFG segs S c.
Proof.
intros S c0 tr c Hstar Hh Hm NK CS. revert tr Hstar Hh.
induction Hm as [c Hh' | c Hex Hsafe Hall IH]; intros tr Hstar Hh; [congruence|].
apply must_exit_in_at_cfg_running.
- exact Hh.
- exact Hex.
- intros evs Hss. destruct (Hsafe evs SError Hss) as (c' & Hc'). discriminate.
- intros evs c' Hss.
pose proof (star_cfg_trans _ _ _ _ _ _ _ Hstar (star_cfg_one _ _ _ _ _ Hss)) as Hstar'.
destruct (m_halted (cfg_model c')) as [code|] eqn:Hh2.
+ destruct (sstep_into_halted c evs c' Hss ltac:(congruence))
as [(evs0 & code' & -> & Hcode & Hk) | (evs0 & sig & ->)].
* rewrite app_assoc in Hstar'. apply (must_exit_in_at_cfg_halted _ _ _ _ code'); [exact Hcode | exact (CS _ _ _ _ Hstar') | exact Hk].
* rewrite app_assoc in Hstar'. destruct (NK _ _ _ _ Hstar').
+ exact (IH evs c' Hss (tr ++ evs) Hstar' Hh2).
Qed.
#[using="Type"] Theorem realizes_must_exit : forall (S : list word) c T,
realizes segs c T ->
m_halted (cfg_model c) = None ->
(forall tr sig fs, ~ T (tr ++ [KillEv sig fs])) ->
(forall tr code fs, T (tr ++ [ExitEv code fs]) -> In code S) ->
must_exit_in_at_cfg ACFG segs S c.
Proof.
intros S c T HR Hh NK CS.
apply (mreach_must_exit S c [] c (star_cfg_refl _ _ _) Hh (realizes_mreach c T HR)).
- intros tr1 sig fs c1 Hstar. exact (NK _ _ _ (realizes_star_only segs c T HR _ _ Hstar)).
- intros tr1 code fs c1 Hstar. exact (CS _ _ _ (realizes_star_only segs c T HR _ _ Hstar)).
Qed.
#[using="Type"] Corollary realizes_must_exit_cfg : forall (S : list word) c T,
realizes segs c T -> m_halted (cfg_model c) = None ->
(forall tr sig fs, ~ T (tr ++ [KillEv sig fs])) ->
(forall tr code fs, T (tr ++ [ExitEv code fs]) -> In code S) ->
must_exit_in_at_cfg ACFG segs S c.
Proof. intros. eapply realizes_must_exit; eauto. Qed.
End WithSegs.
