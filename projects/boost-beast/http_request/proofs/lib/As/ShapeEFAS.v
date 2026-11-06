(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg ShapeEF ShapeEFA SpinAlg.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCfg.
Context {SC : StepCfg}.

Lemma srealizes_not_dies : forall segs pc ph sp brk0 mb rnd lim inp T,
  srealizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  kill_free T ->
  ~ dies_by_signal (run_scfg the_scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp T Hrz HK (tr & sig & fs & Htr & Hin).
  cbn in Htr. apply (srealizes_obs_iff segs _ T Hrz tr) in Htr.
  pose proof (HK tr Htr _ Hin) as Hk. discriminate Hk.
Qed.

Theorem shape_strong_equiv_ef_abort_s :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  kill_free T ->
  strong_equiv_error_free_budgets_scfg_abort the_scfg rlim alim
    (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget HK.
  unfold strong_equiv_error_free_budgets_scfg_abort, error_free_unkilled.
  repeat split.
  - cbn. eapply realizes_no_error; exact Hsource.
  - eapply realizes_not_dies; eassumption.
  - cbn. eapply srealizes_no_error; exact Htarget.
  - eapply srealizes_not_dies; eassumption.
  - intros H. cbn in H |- *.
    apply (srealizes_obs_iff target_segs _ T Htarget tr).
    apply (realizes_obs_iff source_segs _ T Hsource tr). exact H.
  - intros H. cbn in H |- *.
    apply (realizes_obs_iff source_segs _ T Hsource tr).
    apply (srealizes_obs_iff target_segs _ T Htarget tr). exact H.
Qed.

(* [comment removed for export] *)
Corollary shape_strong_equiv_ef_abort_s_eq :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  kill_free T ->
  strong_equiv_error_free_budgets_scfg_abort the_scfg rlim alim
    (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros until T'. intros inp Hs Ht Heq HK.
  eapply shape_strong_equiv_ef_abort_s; [| exact Ht | eapply kill_free_eq; eauto].
  eapply rz_conseq; [exact Hs | exact Heq].
Qed.

End WithCfg.
