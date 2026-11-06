(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.openssl.ct.lib.AS Require Import ShapeAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m _.
  destruct (classic (exists eff' m' evs', syscall_spec i m (Monad.Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false)) as [H | H].
  - left. exact H.
  - right. intros eff' m' evs' Hs.
    destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity |].
    exfalso. apply H. exists eff', m', evs'. split; assumption.
Qed.

Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.

Lemma run_decided_classic : forall cfg img lim en inp, run_decided cfg img lim en inp.
Proof. intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp. cbn [run_decided]. apply decided_from_classic. Qed.

(* [comment removed for export] *)
Definition ev_is_kill (e : event) : Prop := match e with KillEv _ _ => True | _ => False end.

Definition shape_exits_in (S : list word) (T : TSet) : Prop :=
  forall tr, T tr ->
    (forall e, In e tr -> ~ ev_is_kill e)
    /\ (forall tr0 code fs, tr = tr0 ++ [ExitEv code fs] -> In code S).

Lemma shape_exits_in_teq : forall S T T', t_eq T T' -> shape_exits_in S T -> shape_exits_in S T'.
Proof. intros S T T' He H tr Ht. apply H. apply He. exact Ht. Qed.

Section WithSegs.
Variable segs : list Segment.

Theorem realizes_must_exit_ncfg : forall S c T,
  realizes segs c T ->
  forall pre, (forall tr, T tr -> (forall e, In e (pre ++ tr) -> ~ ev_is_kill e)
                               /\ (forall tr0 code fs, pre ++ tr = tr0 ++ [ExitEv code fs] -> In code S)) ->
  m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg ncfg segs S c.
Proof.
  intros S c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros pre HT Hnh.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running; [exact Hnh | | |].
    + exists (evs i0), (SNext (nx i0)). apply Hcomp.
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Hbad). discriminate Hbad.
    + intros e c' Hss. destruct (Hsound e (SNext c') Hss) as (i & -> & Hc'). injection Hc' as ->.
      destruct (sstep_cfg_next_halts_by_exit segs ncfg c (evs i) (nx i) Hss)
        as [Hn | [(evs0 & code & Hev & Hh & Hk) | (evs0 & sig & Hev & Hk)]].
      * apply (IH i (pre ++ evs i)); [| exact Hn].
        intros tr Htr.
        assert (HTi : t_alt (fun i => t_emit (evs i) (T i)) (evs i ++ tr)).
        { exists i. right. exists tr. split; [reflexivity | exact Htr]. }
        destruct (HT _ HTi) as [Hnk Hex]. rewrite <- app_assoc. split; [exact Hnk | exact Hex].
      * assert (HTi : t_alt (fun i => t_emit (evs i) (T i)) (evs i)).
        { exists i. left. apply is_prefix_refl. }
        destruct (HT _ HTi) as [_ Hex].
        apply (must_exit_in_at_cfg_halted ncfg segs S (nx i) code Hh); [| exact Hk].
        apply (Hex (pre ++ evs0) code (m_fs (cfg_model (nx i)))). rewrite Hev, app_assoc. reflexivity.
      * exfalso.
        assert (HTi : t_alt (fun i => t_emit (evs i) (T i)) (evs i)).
        { exists i. left. apply is_prefix_refl. }
        destruct (HT _ HTi) as [Hnk _].
        apply (Hnk (KillEv sig (m_fs (cfg_model (nx i))))); [| exact Logic.I].
        apply in_or_app. right. rewrite Hev. apply in_or_app. right. left. reflexivity.
  - congruence.
  - apply (IH pre); [| exact Hnh]. intros tr Htr. apply HT. apply Heq. exact Htr.
Qed.

Corollary realizes_must_exit_forced_only : forall S c T,
  realizes segs c T -> shape_exits_in S T -> m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros S c T Hr HT Hnh.
  apply (must_exit_in_at_cfg_mono forced_only_cfg ncfg segs S c).
  - apply forced_only_cfg_least.
  - apply decided_from_classic.
  - apply (realizes_must_exit_ncfg S c T Hr []); [| exact Hnh]. intros tr Htr. cbn [app]. exact (HT tr Htr).
Qed.

End WithSegs.
