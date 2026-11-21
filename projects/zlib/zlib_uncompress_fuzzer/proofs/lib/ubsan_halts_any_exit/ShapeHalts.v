(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import ShapeAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition ends_in (S : list word) (T : TSet) : Prop :=
  (forall tr code fs, T (tr ++ [ExitEv code fs]) -> In code S)
  /\ (forall tr sig fs, ~ T (tr ++ [KillEv sig fs])).

Lemma ends_in_t_eq : forall S T T', t_eq T T' -> ends_in S T -> ends_in S T'.
Proof.
  intros S T T' Heq [HE HK]. split.
  - intros tr code fs H. apply (HE tr code fs). apply (proj2 (Heq _)). exact H.
  - intros tr sig fs H. apply (HK tr sig fs). apply (proj2 (Heq _)). exact H.
Qed.

Lemma is_prefix_snoc_inv {A} : forall (l : list A) x evs,
  is_prefix (l ++ [x]) evs -> exists evs', evs = (l ++ [x]) ++ evs'.
Proof.
  induction l as [|y l IH]; intros x evs H; cbn in *.
  - destruct evs as [|e evs]; cbn in H; [contradiction|]. destruct H as [-> _]. exists evs. reflexivity.
  - destruct evs as [|e evs]; cbn in H; [contradiction|]. destruct H as [-> H].
    destruct (IH x evs H) as [evs' ->]. exists evs'. reflexivity.
Qed.

Lemma ends_in_alt_emit : forall S (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  ends_in S (t_alt (fun i => t_emit (evs i) (T i))) ->
  ends_in S (T i)
  /\ (forall evs0 code fs, evs i = evs0 ++ [ExitEv code fs] -> In code S)
  /\ (forall evs0 sig fs, evs i <> evs0 ++ [KillEv sig fs]).
Proof.
  intros S I evs T i [HE HK]. split; [split|split].
  - intros tr code fs H. apply (HE (evs i ++ tr) code fs). exists i. right.
    exists (tr ++ [ExitEv code fs]). split; [symmetry; apply app_assoc | exact H].
  - intros tr sig fs H. apply (HK (evs i ++ tr) sig fs). exists i. right.
    exists (tr ++ [KillEv sig fs]). split; [symmetry; apply app_assoc | exact H].
  - intros evs0 code fs He. apply (HE evs0 code fs). exists i. left. rewrite <- He. apply is_prefix_refl.
  - intros evs0 sig fs He. apply (HK evs0 sig fs). exists i. left. rewrite <- He. apply is_prefix_refl.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition halts_pre (S : list word) (c : config) : Prop :=
  m_halted (cfg_model c) = None
  \/ exists code, m_halted (cfg_model c) = Some code /\ m_killed (cfg_model c) = None /\ In code S.

Theorem realizes_must_exit : forall S c T,
  realizes segs c T -> ends_in S T -> halts_pre S c -> must_exit_in_at segs S c.
Proof.
  intros S c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros Hend Hpre.
  - destruct Hnode as [Hstep Hinv].
    pose proof (sstep_not_halted segs c (evs i0) (SNext (nx i0)) (Hstep i0)) as Hnone.
    apply must_exit_in_at_running.
    + exact Hnone.
    + exists (evs i0), (SNext (nx i0)). exact (Hstep i0).
    + intros e Herr. destruct (Hinv e SError Herr) as (i & _ & E). discriminate E.
    + intros e c' Hss. destruct (Hinv e (SNext c') Hss) as (i & -> & E). injection E as ->.
      destruct (ends_in_alt_emit S I evs T i Hend) as (Hend' & HEx & HKi).
      apply (IH i Hend').
      destruct (sstep_next_halts_by_exit segs c (evs i) (nx i) (Hstep i))
        as [Hn | [(evs0 & code & He & Hh' & Hk') | (evs0 & sig & He & Hk')]].
      * left. exact Hn.
      * right. exists code. split; [exact Hh' | split; [exact Hk' | exact (HEx evs0 code _ He)]].
      * exfalso. exact (HKi evs0 sig _ He).
  - destruct Hpre as [Hn | (code & Hh' & Hk & Hin)]; [congruence|].
    exact (must_exit_in_at_halted segs S c code Hh' Hin Hk).
  - apply IH; [| exact Hpre]. apply (ends_in_t_eq S T' T); [| exact Hend].
    intros tr. split; intros Htr; apply Heq; exact Htr.
Qed.

Corollary realizes_must_exit_init : forall S c T,
  realizes segs c T -> ends_in S T -> m_halted (cfg_model c) = None -> must_exit_in_at segs S c.
Proof. intros S c T H He Hn. apply (realizes_must_exit S c T H He). left. exact Hn. Qed.

End WithSegs.


Lemma ends_in_nil : forall S, ends_in S t_nil.
Proof.
  intros S. split; intros tr x fs H; unfold t_nil in H; destruct tr; discriminate H.
Qed.

Definition no_terminal (evs : list event) : Prop :=
  forall e, In e evs -> match e with ExitEv _ _ | KillEv _ _ => False | _ => True end.

Lemma snoc_eq_app_inv {A} : forall (tr l : list A) (x : A) tr',
  tr ++ [x] = l ++ tr' ->
  (tr' = [] /\ tr ++ [x] = l) \/ (exists t0, tr' = t0 ++ [x] /\ tr = l ++ t0).
Proof.
  intros tr l x tr' H. destruct tr' as [|y tr'] using rev_ind.
  - left. rewrite app_nil_r in H. split; [reflexivity | exact H].
  - right. rewrite app_assoc in H. apply app_inj_tail in H. destruct H as [-> ->]. exists tr'. split; reflexivity.
Qed.

Lemma in_snoc {A} : forall (l : list A) x, In x (l ++ [x]).
Proof. intros l x. apply in_or_app. right. left. reflexivity. Qed.

Lemma in_snoc_app {A} : forall (l m : list A) x, In x ((l ++ [x]) ++ m).
Proof. intros l m x. apply in_or_app. left. apply in_snoc. Qed.

Lemma ends_in_emit : forall S evs T,
  no_terminal evs -> ends_in S T -> ends_in S (t_emit evs T).
Proof.
  intros S evs T Hnt [HE HK]. split.
  - intros tr code fs [Hp | (tr' & Heq & HT)].
    + exfalso. destruct (is_prefix_snoc_inv tr (ExitEv code fs) evs Hp) as [evs' ->].
      exact (Hnt (ExitEv code fs) (in_snoc_app tr evs' (ExitEv code fs))).
    + destruct (snoc_eq_app_inv tr evs (ExitEv code fs) tr' Heq) as [[-> He] | (t0 & -> & ->)].
      * exfalso. rewrite <- He in Hnt. exact (Hnt (ExitEv code fs) (in_snoc tr (ExitEv code fs))).
      * exact (HE t0 code fs HT).
  - intros tr sig fs [Hp | (tr' & Heq & HT)].
    + destruct (is_prefix_snoc_inv tr (KillEv sig fs) evs Hp) as [evs' ->].
      exact (Hnt (KillEv sig fs) (in_snoc_app tr evs' (KillEv sig fs))).
    + destruct (snoc_eq_app_inv tr evs (KillEv sig fs) tr' Heq) as [[-> He] | (t0 & -> & ->)].
      * rewrite <- He in Hnt. exact (Hnt (KillEv sig fs) (in_snoc tr (KillEv sig fs))).
      * exact (HK t0 sig fs HT).
Qed.

Lemma ends_in_alt : forall S (I : Type) (f : I -> TSet),
  (forall i, ends_in S (f i)) -> ends_in S (t_alt f).
Proof.
  intros S I f H. split.
  - intros tr code fs [i Hi]. exact (proj1 (H i) tr code fs Hi).
  - intros tr sig fs [i Hi]. exact (proj2 (H i) tr sig fs Hi).
Qed.

Lemma ends_in_alt2 : forall S A B, ends_in S A -> ends_in S B -> ends_in S (t_alt2 A B).
Proof.
  intros S A B HA HB. split.
  - intros tr code fs [H|H]; [exact (proj1 HA tr code fs H) | exact (proj1 HB tr code fs H)].
  - intros tr sig fs [H|H]; [exact (proj2 HA tr sig fs H) | exact (proj2 HB tr sig fs H)].
Qed.

Lemma ends_in_exit : forall S code fs, In code S -> ends_in S (t_exit code fs).
Proof.
  intros S code fs Hin. unfold t_exit. split.
  - intros tr code' fs' [Hp | (tr' & Heq & HT)].
    + destruct (is_prefix_snoc_inv tr (ExitEv code' fs') [ExitEv code fs] Hp) as [evs' E].
      destruct tr; cbn in E; [injection E as <- _; exact Hin | destruct tr; discriminate E].
    + unfold t_nil in HT. subst tr'. rewrite app_nil_r in Heq.
      destruct tr; cbn in Heq; [injection Heq as <- _; exact Hin | destruct tr; discriminate Heq].
  - intros tr sig fs' [Hp | (tr' & Heq & HT)].
    + destruct (is_prefix_snoc_inv tr (KillEv sig fs') [ExitEv code fs] Hp) as [evs' E].
      destruct tr; cbn in E; [discriminate E | destruct tr; discriminate E].
    + unfold t_nil in HT. subst tr'. rewrite app_nil_r in Heq.
      destruct tr; cbn in Heq; [discriminate Heq | destruct tr; discriminate Heq].
Qed.

Lemma ends_in_exit_any : forall a fs, ends_in AnyExit.codes (t_exit (bv_and a (Z_to_bv 64 255)) fs).
Proof. intros a fs. apply ends_in_exit. apply any_exit_covers. Qed.
