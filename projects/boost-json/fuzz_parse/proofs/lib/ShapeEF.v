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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypek17mkImage3h5LinuxProcessSemanticsfLinuxProcessSem3Runo07mkEntryo08run_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~s18the_scfg37Corelib4Init9Datatypeshg34list37Corelib4Init5Logichi33and01N01Z3h5LinuxProcessSemanticsh5EquivalenceDefinitionbEquivalencehk4aerror_freek18PhdrInfok17Segmento09bh_traceso0binit_config3h5LinuxProcessSemanticsfLinuxProcessSembStackLayouthrc9EntryDraw69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~hvd8realizeshk4btrace_equiv3h5LinuxProcessSemanticsfLinuxProcessSem5Stateil39ProcInputhvd4TSethk4hcstrong_equiv_error_free_scfgil3h2source_alloc_limitil3h2target_alloc_limit" s.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section WithCfg.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Context {SC : StepCfg}.

(* LPS 08b1429: [run_scfg] runs the image against [run_segments segs inp sp mb] from
   [init_config (run_segments ..) ..], so the shape walks are stated there (as in
   boost-beast and openssl/echconfiglist_parser). *)
Theorem shape_strong_equiv_ef :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg the_scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg the_scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg the_scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg the_scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  split; [| split].
  - cbn. eapply realizes_no_error; exact Hsource.
  - cbn. eapply realizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff (run_segments source_segs inp rsp rmb) _ T Hsource tr).
    rewrite (realizes_obs_iff (run_segments target_segs inp asp amb) _ T Htarget tr).
    reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Corollary shape_strong_equiv_ef_scfg :
  forall source_segs rpc rph rsp rbrk rmb rrnd
         target_segs apc aph asp abrk amb arnd
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd source_alloc_limit inp) T ->
  realizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd target_alloc_limit inp) T ->
  strong_equiv_error_free_scfg the_scfg (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros. unfold strong_equiv_error_free_scfg. eapply shape_strong_equiv_ef; eassumption.
Qed.

(* [comment removed for export] *)

End WithCfg.
(* [comment removed for export] *)
