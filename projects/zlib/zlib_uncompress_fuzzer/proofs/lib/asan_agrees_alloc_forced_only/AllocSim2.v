(** * Common.AllocSim2 — mixed-allocator equivalence glue.

    TRUST BOUNDARY: shared proof library, not the trusted specification.
    Image-INDEPENDENT.

    Glue for the allocator-divergence examples: a SOURCE binary whose
    behavior is characterized as an [AllocSim.to_outcomes] set (brk
    branching) and a TARGET binary characterized as a [MmapSim.tmw]
    derivation (one mmap with a failure tail and a success tail).  When
    the source's outcome set is exactly the two-element set
    { (bf, cf); (bs, cs) } matching the target's two tails, the two
    binaries are observably equivalent: allocation emits no trace
    events, so each side's trace set is the prefixes of the same two
    candidate traces even though the failing/succeeding resolutions
    come from different syscalls. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require Import SimInv ExitSim PropExec CatSim CatExec AllocSim MmapSim.

Import ListNotations.
Open Scope bv_scope.

(** The two-element outcome set of a fail/succeed allocator run. *)
Definition two_outcomes (bf : list (list byte)) (cf : word)
    (bs : list (list byte)) (cs : word)
    : (list (list byte) * word) -> Prop :=
  fun o => o = (bf, cf) \/ o = (bs, cs).

(** [Equivalence.equiv] for a brk-allocating source whose outcome set is
    [two_outcomes bf cf bs cs] and an mmap-allocating target with the
    same failure tail [(bf, cf)] and success tail [(bs, cs)], on a launch
    with a reader on stdout: the target side is [MmapSim]'s, whose write
    nodes need one (a reader-gone write KILLS the process). *)
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

(** The omni equivalence of a brk-branching source against a mmap-branching
    target with the same two outcomes, at the two role budgets. *)
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
