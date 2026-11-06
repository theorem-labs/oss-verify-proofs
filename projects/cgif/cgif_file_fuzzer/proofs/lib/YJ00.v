(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs Monad State Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK15.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Section a.
Variable segs : list Segment.
Definition exits_only_with (v : word) (T : TSet) : Prop :=
(forall tr k fs, T (tr ++ [ExitEv k fs]) -> k = v)
/\ (forall tr sig fs, ~ T (tr ++ [KillEv sig fs])).
Lemma exits_only_with_eq : forall v T T',
t_eq T T' -> exits_only_with v T' -> exits_only_with v T.
Proof.
intros v T T' Heq [He Hk]. split.
- intros tr k fs H. apply (He tr k fs). apply Heq. exact H.
- intros tr sig fs H. apply (Hk tr sig fs). apply Heq. exact H.
Qed.
Lemma exits_only_with_branch : forall v (I : Type) (evs : I -> list event) (T : I -> TSet) i,
exits_only_with v (t_alt (fun i => t_emit (evs i) (T i))) ->
exits_only_with v (T i).
Proof.
intros v I evs T i [He Hk]. split.
- intros tr k fs H. apply (He (evs i ++ tr) k fs).
exists i. right. exists (tr ++ [ExitEv k fs]). split; [|exact H].
rewrite <- app_assoc. reflexivity.
- intros tr sig fs H. apply (Hk (evs i ++ tr) sig fs).
exists i. right. exists (tr ++ [KillEv sig fs]). split; [|exact H].
rewrite <- app_assoc. reflexivity.
Qed.
Lemma t_emit_self : forall evs T, T [] -> t_emit evs T evs.
Proof. intros evs T H. right. exists []. split; [rewrite app_nil_r; reflexivity | exact H]. Qed.
Theorem realizes_must_exit_at : forall c T,
realizes segs c T ->
forall v,
m_halted (cfg_model c) = None ->
exits_only_with v T ->
must_exit_at_cfg ACFG segs v c.
Proof using segs.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
intros v Hnone Hx.
- destruct Hnode as [Hsound Hinv].
apply must_exit_at_cfg_running.
+ exact Hnone.
+ eexists _, _. exact (Hsound i0).
+ intros e Herr. destruct (Hinv e SError Herr) as (i & _ & Habs). discriminate Habs.
+ intros e c' Hs.
destruct (Hinv e (SNext c') Hs) as (i & -> & Hc'). injection Hc' as ->.
pose proof (exits_only_with_branch v I evs T i Hx) as Hxi.
destruct (sstep_cfg_next_halts_by_exit segs ACFG c (evs i) (nx i) Hs)
as [Hn | [(evs0 & code & Hevs & Hh & Hk) | (evs0 & sig & Hevs & Hk)]].
* apply IH; assumption.
*
assert (Hcode : code = v).
{ destruct Hx as [He _]. apply (He evs0 code (m_fs (cfg_model (nx i)))).
exists i. rewrite <- Hevs. apply t_emit_self. exact (realizes_nonempty segs _ _ (Hcont i)). }
subst code. apply must_exit_at_cfg_halted; assumption.
* exfalso. destruct Hx as [_ HK]. apply (HK evs0 sig (m_fs (cfg_model (nx i)))).
exists i. rewrite <- Hevs. apply t_emit_self. exact (realizes_nonempty segs _ _ (Hcont i)).
- exfalso. apply Hh. exact Hnone.
- apply IH; [exact Hnone|]. eapply exits_only_with_eq; eauto.
Qed.
Lemma is_prefix_snoc_single {A} : forall (tr : list A) e e',
is_prefix (tr ++ [e]) [e'] -> tr = [] /\ e = e'.
Proof.
intros tr e e' H. destruct tr as [|x tr]; cbn in H.
- destruct H as [H _]. split; [reflexivity | exact H].
- destruct H as [_ H]. destruct tr; cbn in H; contradiction.
Qed.
Lemma snoc_eq_single {A} : forall (tr : list A) e e' (l : list A),
tr ++ [e] = [e'] ++ l -> l = [] -> tr = [] /\ e = e'.
Proof.
intros tr e e' l H ->. rewrite app_nil_r in H. destruct tr as [|x tr]; cbn in H.
- injection H as H. split; [reflexivity | exact H].
- injection H as _ H. destruct tr; discriminate H.
Qed.
Lemma exits_only_with_t_exit : forall v fs, exits_only_with v (t_exit v fs).
Proof.
intros v fs. unfold t_exit, t_emit, t_nil. split.
- intros tr k fs' [Hp | (tr' & Heq & Hn)].
+ apply is_prefix_snoc_single in Hp as [_ H]. congruence.
+ destruct (snoc_eq_single tr _ _ tr' Heq Hn) as [_ H]. congruence.
- intros tr sig fs' [Hp | (tr' & Heq & Hn)].
+ apply is_prefix_snoc_single in Hp as [_ H]. discriminate H.
+ destruct (snoc_eq_single tr _ _ tr' Heq Hn) as [_ H]. discriminate H.
Qed.
End a.
Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
intros cfg i m _.
destruct (classic (exists eff' m' evs',
syscall_spec i m (Monad.Ok eff' m' evs')
/\ refusal_b i m (eff_ret eff') = false)) as [H | H].
- left. exact H.
- right. intros eff' m' evs' Hs.
destruct (refusal_b i m (eff_ret eff')) eqn:Hr; [reflexivity|].
exfalso. apply H. exists eff', m', evs'. split; assumption.
Qed.
Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.
Lemma run_decided_classic : forall cfg img lim en inp, run_decided cfg img lim en inp.
Proof. intros cfg [segs pc ph] lim [sp brk mb rnd] inp. cbn. apply decided_from_classic. Qed.
Theorem must_exit_with_scfg_classic : forall cfg code img lim en inp,
must_exit_with code img lim en inp -> must_exit_with_scfg cfg code img lim en inp.
Proof.
intros cfg code img lim en inp H.
apply must_exit_with_scfg_of_must_exit_with; [apply run_decided_classic | exact H].
Qed.
Theorem realizes_exit_verdict : forall cfg segs pc ph sp brk mb rnd lim inp v fs,
cfg_le cfg ACFG ->
realizes segs (init_config segs pc ph sp brk mb rnd lim inp) (t_exit v fs) ->
must_exit_with_scfg cfg v (mkImage segs pc ph) lim (mkEntry sp brk mb rnd) inp.
Proof.
intros cfg segs pc ph sp brk mb rnd lim inp v fs Hle H.
apply (must_exit_with_scfg_mono cfg ACFG); [exact Hle | apply run_decided_classic |]. cbn [must_exit_with_scfg].
apply (realizes_must_exit_at segs _ _ H); [reflexivity | apply exits_only_with_t_exit].
Qed.
