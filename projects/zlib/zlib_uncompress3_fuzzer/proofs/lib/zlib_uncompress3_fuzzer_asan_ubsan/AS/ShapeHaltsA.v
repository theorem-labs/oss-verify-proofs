(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.AS Require Import ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.FO Require Import FOCore.
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
  realizes segs c T -> ends_in S T -> halts_pre S c -> must_exit_in_at_cfg alloc_forced_cfg segs S c.
Proof.
  intros S c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros Hend Hpre.
  - destruct Hnode as [Hstep Hinv].
    pose proof (sstep_cfg_not_halted segs alloc_forced_cfg c (evs i0) (SNext (nx i0)) (Hstep i0)) as Hnone.
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + exists (evs i0), (SNext (nx i0)). exact (Hstep i0).
    + intros e Herr. destruct (Hinv e SError Herr) as (i & _ & E). discriminate E.
    + intros e c' Hss. destruct (Hinv e (SNext c') Hss) as (i & -> & E). injection E as ->.
      destruct (ends_in_alt_emit S I evs T i Hend) as (Hend' & HEx & HKi).
      apply (IH i Hend').
      destruct (sstep_next_halts_by_exit segs c (evs i) (nx i) (sstep_cfg_sub segs alloc_forced_cfg _ _ _ (Hstep i)))
        as [Hn | [(evs0 & code & He & Hh' & Hk') | (evs0 & sig & He & Hk')]].
      * left. exact Hn.
      * right. exists code. split; [exact Hh' | split; [exact Hk' | exact (HEx evs0 code _ He)]].
      * exfalso. exact (HKi evs0 sig _ He).
  - destruct Hpre as [Hn | (code & Hh' & Hk & Hin)]; [congruence|].
    exact (must_exit_in_at_cfg_halted alloc_forced_cfg segs S c code Hh' Hin Hk).
  - apply IH; [| exact Hpre]. apply (ends_in_t_eq S T' T); [| exact Hend].
    intros tr. split; intros Htr; apply Heq; exact Htr.
Qed.

Corollary realizes_must_exit_init : forall S c T,
  realizes segs c T -> ends_in S T -> m_halted (cfg_model c) = None -> must_exit_in_at_cfg alloc_forced_cfg segs S c.
Proof. intros S c T H He Hn. apply (realizes_must_exit S c T H He). left. exact Hn. Qed.

End WithSegs.
