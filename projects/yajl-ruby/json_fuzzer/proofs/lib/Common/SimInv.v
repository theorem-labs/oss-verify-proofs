(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the source's no-error premise over run_segments, the binary's segments plus the vDSO pair). *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import LiaTuning.
From Stdlib Require Import List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac norm_fd32 :=
  repeat match goal with
         | |- context [fd32 AT_FDCWD] =>
             change (fd32 AT_FDCWD) with AT_FDCWD32
         | H : context [fd32 AT_FDCWD] |- _ =>
             change (fd32 AT_FDCWD) with AT_FDCWD32 in H
         | |- context [fd32 ?x] => change (fd32 x) with x
         | H : context [fd32 ?x] |- _ => change (fd32 x) with x in H
         end.

(* [comment removed for export] *)
Ltac fd32_ok :=
  solve [ reflexivity
        | assumption
        | apply fd32_lt31; assumption
        | apply fd32_id; assumption
        | apply fd32_lt31; lia
        | apply fd32_id; lia ].

(* [comment removed for export] *)
Lemma star_inv (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star segs c tr c' -> Inv c'.
Proof.
  intros c tr c' HInv Hstar. induction Hstar; [exact HInv|].
  apply IHHstar. eapply Hstep; eauto.
Qed.

(* [comment removed for export] *)
Lemma inv_no_reaches_error (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> ~ reaches_error segs c.
Proof.
  intros c HInv (tr & c' & evs & Hstar & Hss).
  eapply Hnoerr; [| exact Hss].
  eapply star_inv; eauto.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
