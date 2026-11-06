(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import List ZArith Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeEF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
Unset Nia Cache. Unset Nra Cache.

Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Definition kill_free (T : TSet) : Prop :=
  forall tr sig fs, T tr -> ~ In (KillEv sig fs) tr.

Lemma kill_free_t_eq : forall T T', t_eq T T' -> kill_free T -> kill_free T'.
Proof. intros T T' Heq Hk tr sig fs Htr. apply (Hk tr sig fs). apply (proj2 (Heq tr)). exact Htr. Qed.

Lemma kill_free_t_nil : kill_free t_nil.
Proof. intros tr sig fs Htr Hin. unfold t_nil in Htr. subst tr. exact Hin. Qed.

Lemma kill_free_t_emit : forall evs T,
  (forall sig fs, ~ In (KillEv sig fs) evs) -> kill_free T -> kill_free (t_emit evs T).
Proof.
  intros evs T Hevs Hk tr sig fs Htr Hin. unfold t_emit in Htr.
  destruct Htr as [Hpre | (tr' & -> & HT)].
  -
    apply (Hevs sig fs). clear Hevs Hk T. revert evs Hpre Hin. induction tr as [|x xs IH]; intros evs Hpre Hin; [destruct Hin|].
    destruct evs as [|y ys]; [destruct Hpre|]. destruct Hpre as [<- Hpre].
    destruct Hin as [<-|Hin]; [left; reflexivity | right; exact (IH ys Hpre Hin)].
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (Hevs sig fs Hin) | exact (Hk tr' sig fs HT Hin)].
Qed.

Lemma kill_free_t_exit : forall code fs, kill_free (t_exit code fs).
Proof.
  intros code fs. unfold t_exit. apply kill_free_t_emit; [|apply kill_free_t_nil].
  intros sig fs' Hin. cbn in Hin. destruct Hin as [H|H]; [discriminate|exact H].
Qed.

Lemma kill_free_t_alt : forall (I : Type) (f : I -> TSet),
  (forall i, kill_free (f i)) -> kill_free (t_alt f).
Proof. intros I f Hf tr sig fs (i & Hi). exact (Hf i tr sig fs Hi). Qed.

Lemma kill_free_t_alt2 : forall A B, kill_free A -> kill_free B -> kill_free (t_alt2 A B).
Proof. intros A B HA HB tr sig fs [H|H]; [exact (HA _ _ _ H) | exact (HB _ _ _ H)]. Qed.

Lemma kill_free_t_write_ch : forall ch buf T, kill_free T -> kill_free (t_write_ch ch buf T).
Proof.
  intros ch buf T Hk. unfold t_write_ch. apply kill_free_t_alt. intros i.
  apply kill_free_t_emit; [|exact Hk].
  intros sig fs Hin. apply in_map_iff in Hin. destruct Hin as (x & Hx & _). discriminate.
Qed.

Lemma kill_free_t_writes_pick : forall bufs T, kill_free T -> kill_free (t_writes_pick bufs T).
Proof.
  induction bufs as [|b bufs IH]; intros T Hk; cbn; [exact Hk|].
  apply kill_free_t_write_ch. apply IH. exact Hk.
Qed.

Lemma kill_free_t_writes_ch : forall ch bufs T, kill_free T -> kill_free (t_writes_ch ch bufs T).
Proof.
  intros ch. induction bufs as [|b bufs IH]; intros T Hk; cbn; [exact Hk|].
  apply kill_free_t_emit; [|apply IH; exact Hk].
  intros sig fs Hin. apply in_map_iff in Hin. destruct Hin as (x & Hx & _). discriminate.
Qed.

Lemma realizes_unkilled : forall segs pc ph sp brk0 mb rnd lim inp T,
  realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  kill_free T ->
  ~ dies_by_signal (run_scfg fcfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp T Hr Hk (tr & sig & fs & Htr & Hin).
  apply (Hk tr sig fs); [|exact Hin].
  apply (proj1 (realizes_traces_iff segs pc ph sp brk0 mb rnd lim inp T tr Hr)). exact Htr.
Qed.

Theorem shape_strong_equiv_efa :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  kill_free T ->
  error_free_unkilled (run_scfg fcfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free_unkilled (run_scfg fcfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg fcfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg fcfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim T inp Hs Ht Hk.
  destruct (shape_strong_equiv_ef source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim T inp Hs Ht)
    as (E1 & E2 & E3).
  split; [|split; [|exact E3]]; split.
  - exact E1. - eapply realizes_unkilled; [exact Hs | exact Hk].
  - exact E2. - eapply realizes_unkilled; [exact Ht | exact Hk].
Qed.

Corollary shape_strong_equiv_efa_eq :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' -> kill_free T ->
  error_free_unkilled (run_scfg fcfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free_unkilled (run_scfg fcfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg fcfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg fcfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until T'. intros inp Hs Ht Heq Hk.
  eapply shape_strong_equiv_efa; [| exact Ht | eapply kill_free_t_eq; [exact Heq | exact Hk]].
  eapply rz_conseq; [exact Hs | exact Heq].
Qed.
