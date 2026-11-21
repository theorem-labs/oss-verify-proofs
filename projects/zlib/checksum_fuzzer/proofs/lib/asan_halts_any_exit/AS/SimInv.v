(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* AS/SimInv := 's own theories/Common/SimInv.v IN PLACE (md5 ), Common requires -> AS/; the old text is kept aside *)
(** * Common.SimInv — generic path-invariant / no-error combinator.

    TRUST BOUNDARY: this file is part of the shared proof library, not the
    trusted specification.  Nothing here knows about any particular
    binary.

    Every "sim" file in [Common/] (ExitSim, CatSim, StreamSim, AllocSim,
    MmapSim, FileSim, DrainSim) closes the [~ reaches_error] obligation the
    same way: it defines a per-file configuration invariant [Inv], proves
    that [Inv] is preserved by every [sstep] to a [SNext] successor, proves
    that [Inv] excludes the [SError] transition, and then lifts these two
    facts along [star] to conclude that no reachable configuration errors.

    The [star]-lifting induction and the final [reaches_error] closure are
    byte-identical across all those files, so they are factored here once:

      - [star_inv]              : [Inv] is preserved along [star]
      - [inv_no_reaches_error]  : [Inv c -> ~ reaches_error segs c]

    Each sim file supplies only its two genuinely per-file hypotheses (the
    step-preservation and no-error lemmas) and instantiates these two
    combinators; its [star_X]/[X_no_error] lemmas become thin corollaries.

    This file is also where the shared ABI-boundary normalization tactics
    live ([norm_fd32], [fd32_ok]): every "sim" file and every per-binary
    proof imports it (directly or through CatSim/StreamSim/FileSim), and
    proof automation shaped by particular example proofs has no business
    sitting in the trusted [LinuxProcessSem.Specs]. *)

From Stdlib Require Import List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.

Import ListNotations.

(* =========================================================================
   ABI-boundary truncation ([Syscall.fd32]) — proof kit
   ========================================================================= *)

(** Proof kit for the per-binary proofs: the fds they step through are
    concrete ([Z_to_bv 64 1], AT_FDCWD, …), and on those [fd32] is the
    identity BY CONVERSION — so normalizing it away wherever it blocks a
    rewrite needs no side condition.  ([fd32] of a symbolic register is
    left alone; the match simply stops there.) *)
Ltac norm_fd32 :=
  repeat match goal with
         | |- context [fd32 AT_FDCWD] =>
             change (fd32 AT_FDCWD) with AT_FDCWD32
         | H : context [fd32 AT_FDCWD] |- _ =>
             change (fd32 AT_FDCWD) with AT_FDCWD32 in H
         | |- context [fd32 ?x] => change (fd32 x) with x
         | H : context [fd32 ?x] |- _ => change (fd32 x) with x in H
         end.

(** Discharge an [fd32 fd = fd] premise: by conversion for a concrete
    fd, otherwise from the [< 2^31] / [< 2^32] bound the caller carries
    for the fd it holds. *)
Ltac fd32_ok :=
  solve [ reflexivity
        | assumption
        | apply fd32_lt31; assumption
        | apply fd32_id; assumption
        | apply fd32_lt31; lia
        | apply fd32_id; lia ].

(** [Inv] is preserved along any [star] run, given that it is preserved by
    every single [sstep] to a [SNext] successor. *)
Lemma star_inv (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star segs c tr c' -> Inv c'.
Proof.
  intros c tr c' HInv Hstar. induction Hstar; [exact HInv|].
  apply IHHstar. eapply Hstep; eauto.
Qed.

(** If [Inv] is preserved by [sstep]-to-[SNext] and excludes the [SError]
    transition, then any configuration satisfying [Inv] never reaches the
    explicit error step. *)
Lemma inv_no_reaches_error (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> ~ reaches_error segs c.
Proof.
  intros c HInv (tr & c' & evs & Hstar & Hss).
  eapply Hnoerr; [| exact Hss].
  eapply star_inv; eauto.
Qed.

(** The same invariant delivers the omni safety judgment directly: an
    invariant that excludes the error transition is a proof of
    [OmniRun.coexec … never_errors], by coinduction along the
    preservation clause — no [Run.star] in sight. *)
Lemma inv_coexec (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> OmniRun.coexec segs c never_errors.
Proof.
  cofix CH. intros c HInv.
  destruct (m_halted (cfg_model c)) as [code |] eqn:Hh.
  - apply coexec_halt; [rewrite Hh; discriminate | exact (fun h => h)].
  - apply coexec_step; [exact Hh | |].
    + intros evs Hss. exfalso. exact (Hnoerr c evs HInv Hss).
    + intros evs c' Hss. exact (CH c' (Hstep c evs c' HInv Hss)).
Qed.

(** ... and the bridge from the library's [~ reaches_error] shape to it,
    for combinators that already have the negative fact in hand. *)
Lemma no_error_run_corun :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
         (lim : Z) (inp : ProcInput),
  ~ reaches_error (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) ->
  omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp H. cbn [omni_corun].
  apply no_error_coexec, H.
Qed.

(* =========================================================================
   The [Equivalence.modeled] conjunct, once
   ========================================================================= *)

(** Turn a source [~ reaches_error] proof into the source-coverage
    conjunct of [Equivalence.strong_equiv].  Every combinator below
    ([AllocSim], [AllocSim2], [CatSim], [DrainSim], [ExitSim], [FileSim],
    [MmapSim], [StreamSim]) discharges [modeled] this way — the run never
    errors at all, so a fortiori it never reaches a configuration the
    model declined to interpret ([Run.no_error_no_unmodeled]).  It lives
    here, applied uniformly, so that the ten combinators cannot drift:
    the argument [~ reaches_error] must be about the SOURCE image, pc, sp
    and brk that [run] is applied to, and stating it once makes the
    unifier check that rather than leaving it to a copy-pasted script.

    The combinators whose source is EXPECTED to error need a direct proof
    instead: [ErrEscape.err_escape_modeled] (a deterministic
    [MachineFault]) and [AllocMixSim.tom_no_unmodeled] (a may-faulting
    brk mix). *)
Lemma no_error_run_modeled :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
         (lim : Z) (inp : ProcInput),
  ~ reaches_error (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) ->
  Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp H.
  apply modeled_iff.
  cbn [image_run_segments img_segments en_sp en_mmap_base].
  eapply coexec_conseq; [apply no_error_run_corun, H | apply never_errors_covered].
Qed.
