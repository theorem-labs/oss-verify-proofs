(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: whole copy of projects/jsoncons/fuzz_ubjson_parser_max/proofs/lib/Common/MustExitOfShape.v at c395a1e0dfa, with OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib renamed to OSSVerify.Proofs.jsoncons.fuzz_bigint.lib and its Common.MustExit* requires renamed to Corpus.Corpus*. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ShapeAlg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition exits_in (S : list word) (T : TSet) : Prop :=
(forall tr code fs, T (tr ++ [ExitEv code fs]) -> In code S)
/\ (forall tr sig fs, ~ T (tr ++ [KillEv sig fs])).
Lemma exits_in_t_eq : forall S T T', t_eq T T' -> exits_in S T -> exits_in S T'.
Proof.
intros S T T' Heq [HE HK]. split.
- intros tr code fs H. apply (HE tr code fs). apply Heq. exact H.
- intros tr sig fs H. apply (HK tr sig fs). apply Heq. exact H.
Qed.
Lemma exits_in_mono : forall S1 S2 T,
(forall code, In code S1 -> In code S2) -> exits_in S1 T -> exits_in S2 T.
Proof.
intros S1 S2 T Hsub [HE HK]. split; [| exact HK].
intros tr code fs H. apply Hsub. exact (HE tr code fs H).
Qed.
Lemma exits_in_sub : forall S (T T' : TSet),
(forall tr, T' tr -> T tr) -> exits_in S T -> exits_in S T'.
Proof.
intros S T T' Hsub [HE HK]. split.
- intros tr code fs H. exact (HE tr code fs (Hsub _ H)).
- intros tr sig fs H. exact (HK tr sig fs (Hsub _ H)).
Qed.
Lemma exits_in_nil : forall S, exits_in S t_nil.
Proof.
intros S. split.
- intros tr code fs H. unfold t_nil in H. destruct tr; discriminate H.
- intros tr sig fs H. unfold t_nil in H. destruct tr; discriminate H.
Qed.
Lemma is_prefix_snoc_app {A} : forall (tr : list A) (x : A) (evs tr' : list A),
is_prefix (tr ++ [x]) (evs ++ tr') ->
In x evs \/ exists tr0, is_prefix (tr0 ++ [x]) tr' /\ tr ++ [x] = evs ++ tr0 ++ [x].
Proof.
intros tr x evs. revert tr. induction evs as [|e evs IH]; intros tr tr' Hp.
- right. exists tr. split; [exact Hp | reflexivity].
- destruct tr as [|y tr].
+ cbn in Hp. destruct Hp as [-> _]. left. left. reflexivity.
+ cbn in Hp. destruct Hp as [-> Hp].
destruct (IH tr tr' Hp) as [Hin | (tr0 & Hp0 & Heq)].
* left. right. exact Hin.
* right. exists tr0. split; [exact Hp0 |]. cbn. rewrite Heq. reflexivity.
Qed.
Lemma snoc_eq_app {A} : forall (tr : list A) (x : A) (evs tr' : list A),
tr ++ [x] = evs ++ tr' ->
(tr' = [] /\ tr ++ [x] = evs) \/ exists tr0, tr' = tr0 ++ [x] /\ tr = evs ++ tr0.
Proof.
intros tr x evs tr' H.
destruct tr' as [|y tr'] using rev_ind.
- left. rewrite app_nil_r in H. split; [reflexivity | exact H].
- right. exists tr'.
rewrite app_assoc in H. apply app_inj_tail in H as [-> ->]. split; reflexivity.
Qed.
Definition ev_exit_ok (S : list word) (e : event) : Prop :=
match e with
| ExitEv code _ => In code S
| KillEv _ _ => False
| _ => True
end.
Lemma exits_in_emit : forall S evs T,
Forall (ev_exit_ok S) evs -> exits_in S T -> exits_in S (t_emit evs T).
Proof.
intros S evs T Hevs [HE HK]. split.
- intros tr code fs [Hp | (tr' & Heq & HT)].
+ destruct (is_prefix_snoc_app tr (ExitEv code fs) evs [] ) as [Hin | (tr0 & Hp0 & _)].
* rewrite app_nil_r. exact Hp.
* pose proof (proj1 (Forall_forall _ _) Hevs _ Hin) as Hok. exact Hok.
* destruct tr0; cbn in Hp0; destruct Hp0.
+ destruct (snoc_eq_app tr (ExitEv code fs) evs tr' Heq) as [[-> Heq'] | (tr0 & -> & ->)].
* assert (Hin : In (ExitEv code fs) evs) by (rewrite <- Heq'; apply in_app_iff; right; left; reflexivity).
exact (proj1 (Forall_forall _ _) Hevs _ Hin).
* exact (HE tr0 code fs HT).
- intros tr sig fs [Hp | (tr' & Heq & HT)].
+ destruct (is_prefix_snoc_app tr (KillEv sig fs) evs []) as [Hin | (tr0 & Hp0 & _)].
* rewrite app_nil_r. exact Hp.
* exact (proj1 (Forall_forall _ _) Hevs _ Hin).
* destruct tr0; cbn in Hp0; destruct Hp0.
+ destruct (snoc_eq_app tr (KillEv sig fs) evs tr' Heq) as [[-> Heq'] | (tr0 & -> & ->)].
* assert (Hin : In (KillEv sig fs) evs) by (rewrite <- Heq'; apply in_app_iff; right; left; reflexivity).
exact (proj1 (Forall_forall _ _) Hevs _ Hin).
* exact (HK tr0 sig fs HT).
Qed.
Lemma exits_in_alt_branch : forall S (I : Type) (evs : I -> list event) (T : I -> TSet) (i : I),
exits_in S (t_alt (fun i => t_emit (evs i) (T i))) -> exits_in S (T i).
Proof.
intros S I evs T i H.
apply (exits_in_sub S (fun tr => t_alt (fun i => t_emit (evs i) (T i)) (evs i ++ tr))).
- intros tr HT. exists i. right. exists tr. split; [reflexivity | exact HT].
- destruct H as [HE HK]. split.
+ intros tr code fs HT. apply (HE (evs i ++ tr) code fs). rewrite <- app_assoc. exact HT.
+ intros tr sig fs HT. apply (HK (evs i ++ tr) sig fs). rewrite <- app_assoc. exact HT.
Qed.
Lemma exits_in_alt : forall S (I : Type) (f : I -> TSet),
(forall i, exits_in S (f i)) -> exits_in S (t_alt f).
Proof.
intros S I f H. split.
- intros tr code fs [i Hi]. exact (proj1 (H i) tr code fs Hi).
- intros tr sig fs [i Hi]. exact (proj2 (H i) tr sig fs Hi).
Qed.
Lemma exits_in_alt2 : forall S A B, exits_in S A -> exits_in S B -> exits_in S (t_alt2 A B).
Proof.
intros S A B [AE AK] [BE BK]. split.
- intros tr code fs [H | H]; [exact (AE _ _ _ H) | exact (BE _ _ _ H)].
- intros tr sig fs [H | H]; [exact (AK _ _ _ H) | exact (BK _ _ _ H)].
Qed.
Lemma exits_in_exit : forall S code fs, In code S -> exits_in S (t_exit code fs).
Proof.
intros S code fs Hin. unfold t_exit. apply exits_in_emit; [| apply exits_in_nil].
constructor; [exact Hin | constructor].
Qed.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma node_branch_trace : forall (I : Type) (evs : I -> list event) (T : I -> TSet) (i : I),
t_alt (fun i => t_emit (evs i) (T i)) (evs i).
Proof. intros I evs T i. exists i. left. apply is_prefix_refl. Qed.
Theorem realizes_must_exit : forall S c T,
realizes segs scfg c T ->
exits_in S T ->
m_halted (cfg_model c) = None ->
must_exit_in_at_cfg scfg segs S c.
Proof.
intros S c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
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
- apply IH; [| exact Hrun]. eapply exits_in_t_eq; [apply t_eq_sym; exact Heq | exact HX].
Qed.
Corollary realizes_must_exit_init : forall S pc ph sp brk0 mbase rnd lim inp T,
realizes segs scfg (init_config segs pc ph sp brk0 mbase rnd lim inp) T ->
exits_in S T ->
must_exit_in_at_cfg scfg segs S (init_config segs pc ph sp brk0 mbase rnd lim inp).
Proof.
intros S pc ph sp brk0 mbase rnd lim inp T H HX.
apply (realizes_must_exit S _ T H HX). reflexivity.
Qed.
End WithSegs.
