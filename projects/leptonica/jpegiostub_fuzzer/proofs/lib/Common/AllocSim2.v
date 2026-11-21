(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (alloc_mmap_strong_equiv and alloc_mmap_omni_strong_equiv stated over the run segment list, the new init_machine_state and the vDSO start state, with an in_channel_reader premise; the Vdso import). *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run OmniRun Vdso.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import SimInv ExitSim PropExec CatSim CatExec AllocSim MmapSim.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition two_outcomes (bf : list (list byte)) (cf : word)
    (bs : list (list byte)) (cs : word)
    : (list (list byte) * word) -> Prop :=
  fun o => o = (bf, cf) \/ o = (bs, cs).

(* [comment removed for export] *)
Lemma alloc_mmap_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp,
  to_outcomes (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (StackLayout.ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
          rlim inp))
    (two_outcomes bf cf bs cs) ->
  tmw (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (StackLayout.ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
          alim inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs
    inp Hsource Htarget Hbf Hbs Hr.
  split.
  { apply no_error_run_modeled.
    apply (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp
             (two_outcomes bf cf bs cs) Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp
               (two_outcomes bf cf bs cs) Hsource tr).
    rewrite (mmap_obs_iff_te (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd
               alim inp
               bf cf bs cs Htarget Hbf Hbs Hr tr).
    unfold two_traces, two_outcomes, outcome_trace.
    split.
    + intros (o & [-> | ->] & Hp); cbn [fst snd] in Hp; [left | right]; exact Hp.
    + intros [Hp | Hp]; [exists (bf, cf) | exists (bs, cs)];
        cbn [fst snd]; auto.
  - cbn.
    apply (mmap_no_error_run_te (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd
             alim inp
             bf cf bs cs Htarget Hbf Hbs Hr).
Qed.

(* [comment removed for export] *)
Lemma alloc_mmap_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp,
  to_outcomes (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (StackLayout.ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
          source_alloc_limit inp))
    (two_outcomes bf cf bs cs) ->
  tmw (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (StackLayout.ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
          target_alloc_limit inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs
    inp Hsource Htarget Hbf Hbs Hr.
  apply strong_equiv_iff.
  apply (alloc_mmap_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit
           target_segs apc aph asp abrk amb arnd target_alloc_limit bf cf bs cs inp
           Hsource Htarget Hbf Hbs Hr).
Qed.
