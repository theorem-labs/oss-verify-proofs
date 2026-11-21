(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/fast_float/from_chars/proofs/lib/Common/RealizesHalts.v at commit theorem-labs/oss-verify-proofs@c5665593c2d8 (its whole content bar the abort section: refusal_decided_classic, decided_from_classic, the two cfg-monotonicity lemmas, exits_in, kill_free and their closure lemmas, realizes_cfg_must_exit_in and the three corollaries), with [realizes_cfg segs cfg] replaced throughout by skcms/iccprofile_info's Info.ShapeAlg.realizes, whose node relation is pinned to Info.ShapeAlg.CFG, and with the image premise taken as Info.ProofInfoPlan.realizes_spec_stmt rather than from_chars's image_realizes_cfg_e. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the walk induction names the read-only-backing premise (sys_rob), the bridge lifts the walk to the run's segments (RomStable.run_init) for an image with no vDSO, the launch facts are read from valid_entry, and the cited source commit is named by its public id; of that whole content, HaltsBridge.v does not hold must_exit_in_scfg_mono_classic, realizes_cfg_must_exit_in_le, spec_exits_in, no_kill_kill_free, must_exit_in_scfg_of_realizes, halts_allowed_of_realizes, halts_allowed_forced_only_of_realizes and halts_allowed_scfg_of_realizes: its must_exit_of_realizes_spec applies must_exit_in_at_cfg_mono_classic and realizes_must_exit_in directly, its exits_in_spec and kill_free_spec state exits_in and kill_free for this target's spec, and its halts_of_realizes_spec is the one halting theorem, at forced_only_cfg with budgets; every comment of the public RealizesHalts.v after its licence lines reads [comment removed for export], so the comments of HaltsBridge.v are its own. *)
(* Modified by Theorem Labs, 2026-11: made from this unit's lib/Halts/HaltsBridge.v, its walk realizes_must_exit_in (lines 92-127) and its must_exit_of_realizes_spec (lines 145-180), restated for Asan.SpinAlgCfg.srealizes_cfg (whose spin case is closed by the False that srz_cfg_spin takes, as in projects/libpcap/fuzz_pcap/proofs/lib/E2/Top/HaltsAsanKit.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6) and for the ASan target statement over run_segments; the halting theorem halts_of_srealizes_tgt takes the shape of that commit's Halts_asan.v (must exit at the large budget, then lim_transfer_scfg); HaltsBridge.v's other declarations (refusal_decided_classic, decided_from_classic, must_exit_in_at_cfg_mono_classic, exits_in, kill_free, exits_in_eq, kill_free_eq, node_shape_cont, exits_in_cont, kill_free_cont, node_shape_self, exits_in_spec, kill_free_spec, halts_of_realizes_spec) are not copied: the proofs here use what they need of them from HaltsBridge; this file holds none of the eight RealizesHalts.v declarations that line 4 names either: its must_exit_of_srealizes_tgt applies must_exit_in_at_cfg_mono_classic and srealizes_cfg_must_exit_in directly, HaltsBridge's exits_in_spec and kill_free_spec give exits_in and kill_free for spec, and its halts_of_srealizes_tgt is the one halting theorem, at forced_only_cfg with budgets; taken from projects/skcms/iccprofile_info/proofs/lib/Halts/HaltsBridge.v, lines 14-24, 92-127, 153-161, 173-180 and 185-191, as in the LPS 727298f3 update. *)
(** Halting of a sanitizer build from the [srealizes_cfg] fact of its
    equivalence proof.

    [Asan.SpinAlgCfg.srealizes_cfg] has no spinning leaf: its [srz_cfg_spin]
    constructor takes a proof of False.  So a derivation of it is a finite
    tree of steps that covers every step the configured relation admits and
    ends in halted configurations, and when the realized set admits only the
    allowed exit statuses and no death by a signal, the configuration must
    exit with an allowed status ([srealizes_cfg_must_exit_in]).

    The ASan target statement of this harness ([InfoAsanTop.asan_tgt_stmt],
    [InfoBothTop.asan_tgt_stmt]) gives that fact at the start configuration,
    for the plain build's trace set [spec], whose exits are 0 and 2
    ([HaltsBridge.exits_in_spec], [HaltsBridge.kill_free_spec]). *)

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import ShapeAlg SpinAlgCfg AsanSpec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require RunSegsCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts Require Import SpecHalts.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts Require HaltsBridge.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.Lim Require LimTransfer.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** ** The walk *)

Section WithSegs.
Variable segs : list Segment.
Variable S : list word.

Theorem srealizes_cfg_must_exit_in : forall c T,
  srealizes_cfg segs c T ->
  m_halted (cfg_model c) = None ->
  HaltsBridge.exits_in S T ->
  HaltsBridge.kill_free T ->
  must_exit_in_at_cfg CFG segs S c.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c Hspin Hh | c T T' H IH Heq];
    intros Hnone HE HK.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + exists (evs i0), (SNext (nx i0)). apply Hcomp.
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Hbad). discriminate Hbad.
    + intros e c' Hss.
      destruct (Hsound e (SNext c') Hss) as (i & He & Hc'). injection Hc' as Hc'. subst e c'.
      destruct (m_halted (cfg_model (nx i))) as [code |] eqn:Hh.
      * destruct (sstep_cfg_next_halts_by_exit _ _ _ _ _ Hss)
          as [Hn | [(evs0 & code0 & Hevs & Hcode0 & Hk0) | (evs0 & sig & Hevs & Hsig)]].
        -- exfalso. rewrite Hn in Hh. discriminate Hh.
        -- apply (must_exit_in_at_cfg_halted CFG segs S (nx i) code0 Hcode0); [| exact Hk0].
           apply (HE evs0 code0 (m_fs (cfg_model (nx i)))). rewrite <- Hevs.
           exact (HaltsBridge.node_shape_self I evs T i).
        -- exfalso. apply (HK evs0 sig (m_fs (cfg_model (nx i)))). rewrite <- Hevs.
           exact (HaltsBridge.node_shape_self I evs T i).
      * apply (IH i Hh).
        -- exact (HaltsBridge.exits_in_cont S I evs T i HE).
        -- exact (HaltsBridge.kill_free_cont I evs T i HK).
  - exfalso. exact (Hh Hnone).
  - destruct Hspin as [[] _].
  - apply IH; [exact Hnone | exact (HaltsBridge.exits_in_eq S T T' Heq HE)
              | exact (HaltsBridge.kill_free_eq T T' Heq HK)].
Qed.

End WithSegs.

(** ** From the ASan target statement to the halting statement *)

(** The target statement's form ([InfoAsanTop.asan_tgt_stmt]): the run of
    the image at [lim] from every valid entry realizes [spec]. *)
Definition srealizes_tgt (segs : list Segment) pc ph (lim : Z) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
    match en with
    | mkEntry sp brk0 mbase rnd =>
        srealizes_cfg segs (init_config segs pc ph sp brk0 mbase rnd lim inp) (spec (in_argv inp) (in_fs inp))
    end.

Theorem must_exit_of_srealizes_tgt : forall segs pc ph lim,
  (* the run's segment list, as in [HaltsBridge.must_exit_of_realizes_spec] *)
  vdso_image segs = None ->
  srealizes_tgt segs pc ph lim ->
  forall en inp,
    valid_entry (mkImage segs pc ph) en inp ->
    valid_input inp ->
    must_exit_in_scfg forced_only_cfg HALT_CODES (mkImage segs pc ph) lim en inp.
Proof.
  intros segs pc ph lim Hvi HT [sp brk0 mbase rnd] inp Hen Hinp.
  pose proof (HT (mkEntry sp brk0 mbase rnd) inp Hen Hinp) as H. cbv beta iota in H.
  cbn [must_exit_in_scfg].
  apply (HaltsBridge.must_exit_in_at_cfg_mono_classic forced_only_cfg CFG (run_segments segs inp sp mbase) HALT_CODES _
           (forced_only_cfg_least CFG)).
  apply (srealizes_cfg_must_exit_in (run_segments segs inp sp mbase) HALT_CODES _ (spec (in_argv inp) (in_fs inp))
           (RunSegsCfg.srealizes_cfg_run_init segs pc ph inp sp brk0 mbase rnd lim _ Hvi H)).
  - cbn [init_config cfg_model]. reflexivity.
  - exact (HaltsBridge.exits_in_spec (in_argv inp) (in_fs inp)).
  - exact (HaltsBridge.kill_free_spec (in_argv inp) (in_fs inp)).
Qed.

(** The statement's own form: the target fact is proved at the larger budget
    [lim], and [Halts.Lim.LimTransfer] carries "must exit" down to [lim_small]
    on the inputs where the run is never refused memory for exceeding
    [lim_small], which is the statement's own premise. *)
Theorem halts_of_srealizes_tgt : forall segs pc ph lim_small lim,
  (lim_small <= lim)%Z ->
  vdso_image segs = None ->
  srealizes_tgt segs pc ph lim ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim_small HALT_CODES (mkImage segs pc ph).
Proof.
  intros segs pc ph lim_small lim Hle Hvi HT en inp Hen Hinp Hbud.
  exact (LimTransfer.lim_transfer_scfg forced_only_cfg HALT_CODES (mkImage segs pc ph) en inp lim_small lim Hle
           (must_exit_of_srealizes_tgt segs pc ph lim Hvi HT en inp Hen Hinp) Hbud).
Qed.
