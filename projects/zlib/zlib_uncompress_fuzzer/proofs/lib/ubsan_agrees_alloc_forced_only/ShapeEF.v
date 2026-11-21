(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import SimInv ExitSim CatSim ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Theorem shape_strong_equiv_ef :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  (* each side realizes over its RUN's list, as the start-up chains do *)
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg alloc_forced_cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg alloc_forced_cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg alloc_forced_cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg alloc_forced_cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
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



