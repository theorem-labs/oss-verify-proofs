(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable Safety.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Lemma obs_trace_no_kill :
  forall segs (c0 : config) (Spec : list event -> Prop),
  (forall t, Spec t -> forall sig fs, ~ In (KillEv sig fs) t) ->
  SOUND segs c0 Spec ->
  forall tr sig fs, obs_trace_a segs c0 tr -> ~ In (KillEv sig fs) tr.
Proof.
  intros segs c0 Spec Hnk Hs tr sig fs (tr' & c & Hst & Hp) Hin.
  destruct (Hs _ _ Hst) as (t & Ht & Hp').
  apply (Hnk t Ht sig fs).
  eapply in_is_prefix; [exact Hp'|].
  eapply in_is_prefix; [exact Hp|]. exact Hin.
Qed.

Theorem strong_equiv_error_free_budgets_scfg_abort_of_facts_lim :
  forall (ls lt : Z) (src tgt : Image) (en_s en_t : ExecEntry) (inp : ProcInput)
         (Spec : list event -> Prop),
  (forall t, Spec t -> forall sig fs, ~ In (KillEv sig fs) t) ->
  let cs := match src, en_s, inp with
            | mkImage segs pc ph, mkEntry sp brk0 mb rnd, _ =>
                init_config segs pc ph sp brk0 mb rnd ls inp end in
  let ct := match tgt, en_t, inp with
            | mkImage segs pc ph, mkEntry sp brk0 mb rnd, _ =>
                init_config segs pc ph sp brk0 mb rnd lt inp end in
  SOUND (img_segments src) cs Spec ->
  COMPLETE (img_segments src) cs Spec ->
  ~ reaches_error_a (img_segments src) cs ->
  SOUND (img_segments tgt) ct Spec ->
  COMPLETE (img_segments tgt) ct Spec ->
  ~ reaches_error_a (img_segments tgt) ct ->
  strong_equiv_error_free_budgets_scfg_abort ACFG ls lt src tgt en_s en_t inp.
Proof.
  intros ls lt [ssegs spc sph] [tsegs tpc tph] [ssp sbrk smb srnd] [tsp tbrk tmb trnd] inp Spec Hnk.
  cbn. intros Ss Cs Es St Ct Et.
  unfold strong_equiv_error_free_budgets_scfg_abort, error_free_unkilled, error_free, dies_by_signal. cbn.
  split; [|split].
  - split; [exact Es|].
    intros (tr & sig & fs & Htr & Hin). exact (@obs_trace_no_kill _ _ _ Hnk Ss tr sig fs Htr Hin).
  - split; [exact Et|].
    intros (tr & sig & fs & Htr & Hin). exact (@obs_trace_no_kill _ _ _ Hnk St tr sig fs Htr Hin).
  - intros tr. split; intro H.
    + exact (proj2 (obs_trace_iff St Ct tr) (proj1 (obs_trace_iff Ss Cs tr) H)).
    + exact (proj2 (obs_trace_iff Ss Cs tr) (proj1 (obs_trace_iff St Ct tr) H)).
Qed.
