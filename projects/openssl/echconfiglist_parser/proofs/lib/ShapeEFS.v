(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the walks are stated over run_segments, the binary's segments and the vDSO pair, as in ShapeEF). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg ShapeEF SpinAlg.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCfg.
Context {SC : StepCfg}.

(* LPS 08b1429: a run reads each binary against [run_segments ..] (its segments and the vDSO
   pair) from [init_config (run_segments ..) ..], so the walks are asked over the run's segment
   list, as in [ShapeEF]; [Common/Cfg/RomStable.run_init] and [RomStableS.srun_init] lift a walk
   over the binary's own segments to that form. *)
Theorem shape_strong_equiv_ef_s :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
  strong_equiv_error_free_budgets_scfg the_scfg rlim alim
    (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  unfold strong_equiv_error_free_budgets_scfg.
  repeat split.
  - cbn. eapply realizes_no_error; exact Hsource.
  - cbn. exact (srealizes_no_error _ _ _ Htarget).
  - intros H. cbn in H |- *.
    apply (srealizes_obs_iff (run_segments target_segs inp asp amb) _ T Htarget tr).
    apply (realizes_obs_iff (run_segments source_segs inp rsp rmb) _ T Hsource tr). exact H.
  - intros H. cbn in H |- *.
    apply (realizes_obs_iff (run_segments source_segs inp rsp rmb) _ T Hsource tr).
    apply (srealizes_obs_iff (run_segments target_segs inp asp amb) _ T Htarget tr). exact H.
Qed.

End WithCfg.
