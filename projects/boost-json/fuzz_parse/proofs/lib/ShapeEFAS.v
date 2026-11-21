(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text, the run's segment list (run_segments), the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg ShapeEF ShapeEFA SpinAlg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14list37Corelib4Init5Logicm03not01N01Z3h5LinuxProcessSemanticsh5EquivalenceDefinitionbEquivalenceo0edies_by_signal3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypesc8PhdrInfosc7Segmentsc7mkImage3h5LinuxProcessSemanticsfLinuxProcessSem3Runhi0binit_confighi07mkEntryhi08run_scfg3h5LinuxProcessSemanticsfLinuxProcessSembStackLayouthn29EntryDraw3h5LinuxProcessSemanticsfLinuxProcessSem5Statehr39ProcInput69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~hue8the_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~ij14TSet69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeEFA~~~~~~in49kill_free69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SpinAlg~~~~~~irc9srealizeso0iastrong_equiv_error_free_budgets_scfg_abortij18realizeso0hcstrong_equiv_error_free_scfghr3h2source_alloc_limithr3h2target_alloc_limit" s.   (* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCfg.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Context {SC : StepCfg}.

(* LPS 08b1429: stated over the run's segment list, as ShapeEF / ShapeEFA. *)
Lemma srealizes_not_dies : forall segs pc ph sp brk0 mb rnd lim inp T,
  srealizes (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  kill_free T ->
  ~ dies_by_signal (run_scfg the_scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp T Hrz HK (tr & sig & fs & Htr & Hin).
  cbn in Htr. apply (srealizes_obs_iff (run_segments segs inp sp mb) _ T Hrz tr) in Htr.
  pose proof (HK tr Htr _ Hin) as Hk. discriminate Hk.
Qed.

Theorem shape_strong_equiv_ef_abort_s :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
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
    apply (srealizes_obs_iff (run_segments target_segs inp asp amb) _ T Htarget tr).
    apply (realizes_obs_iff (run_segments source_segs inp rsp rmb) _ T Hsource tr). exact H.
  - intros H. cbn in H |- *.
    apply (realizes_obs_iff (run_segments source_segs inp rsp rmb) _ T Hsource tr).
    apply (srealizes_obs_iff (run_segments target_segs inp asp amb) _ T Htarget tr). exact H.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Corollary shape_strong_equiv_ef_scfg_s :
  forall source_segs rpc rph rsp rbrk rmb rrnd
         target_segs apc aph asp abrk amb arnd
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd source_alloc_limit inp) T ->
  srealizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd target_alloc_limit inp) T ->
  strong_equiv_error_free_scfg the_scfg (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T inp Hsource Htarget.
  unfold strong_equiv_error_free_scfg. split; [| split].
  - cbn. eapply realizes_no_error; exact Hsource.
  - cbn. eapply srealizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff (run_segments source_segs inp rsp rmb) _ T Hsource tr).
    rewrite (srealizes_obs_iff (run_segments target_segs inp asp amb) _ T Htarget tr).
    reflexivity.
Qed.

End WithCfg.
(* [comment removed for export] *)
