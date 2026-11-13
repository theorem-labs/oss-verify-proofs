(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by gabelogan195, 2026-11: made from this harness's proofs/lib/Mh_0055.v at commit f92feaf8b7, module HaltsKit (its import block, changed to require Mh_0055 and Mh_0055.HaltsKit and to leave out the BvWfKernel require at line 730 and the Zify setting at line 740 of Mh_0055.v; the theorem srealizes_must_exit_fo and the theorem srealizes_init_must_exit), restated for a realization whose budget-refused leaf is off (bm_on = false): the no-refusal hypothesis, the reach_fo bookkeeping it needed and the budget premise are dropped, and the budget-refused case is closed by bm_on = false instead. *)
(** A realization made with its budget-refused leaf off must exit, whatever the budget.

    [HaltsKit.srealizes_init_must_exit] walks a [srealizes0] derivation to
    [must_exit_in_scfg] under [forced_only_cfg].  It needs the run never to be
    refused memory at the budget the realization is proved at, because that is
    how it closes a budget-refused leaf.  A realization made with [bm_on = false]
    has no such leaf, and no spinning leaf either ([spin_leaves] is [False]), so
    the same walk needs no premise on the budget. *)

From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.BigintSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.KillFree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.HaltsKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Off.
Context {bmK : BMode}.
Hypothesis BMOFF : @bm_on bmK = false.

(** The walk of [HaltsKit.srealizes_must_exit_fo], with the budget-refused
    case closed by [BMOFF]. *)
Theorem srealizes_must_exit_fo_off : forall (segs : list Segment) (scfgD : SpuriousCfg) (S : list word) c T,
  @srealizes0 bmK segs scfgD c T ->
  exit_codes_in S T ->
  kill_free T ->
  (forall code, m_halted (cfg_model c) = Some code -> In code S /\ m_killed (cfg_model c) = None) ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros segs scfgD S c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh Hmode | c T T' H IH Heq | c T Hon Hbr HT0];
    intros HE HK Hhalt.
  - destruct Hnode as [Hcomp Hsound].
    assert (Hnh : m_halted (cfg_model c) = None).
    { exact (sstep_cfg_not_halted _ _ _ _ _ (Hcomp i0)). }
    apply must_exit_in_at_cfg_running.
    + exact Hnh.
    + destruct (fo_progress segs _ _ _ _ (Hcomp i0)) as (evs' & st' & Hfo). eexists _, _. exact Hfo.
    + intros evs' Herr.
      destruct (Hsound evs' SError (sstep_cfg_mono _ _ _ _ _ _ (forced_only_cfg_least scfgD) Herr)) as (i & _ & Habs).
      discriminate Habs.
    + intros evs' c' Hfo.
      destruct (Hsound evs' (SNext c') (sstep_cfg_mono _ _ _ _ _ _ (forced_only_cfg_least scfgD) Hfo)) as (i & -> & Hc').
      injection Hc' as Ec. subst c'.
      apply (IH i).
      * eapply exit_codes_in_branch; exact HE.
      * eapply kill_free_branch; exact HK.
      * intros code Hcode.
        pose proof (srealizes0_nonempty _ _ _ _ (Hcont i)) as H0.
        pose proof (node_evs_trace I evs T i H0) as Htr.
        destruct (sstep_cfg_into_halted segs _ _ _ _ _ Hfo Hcode) as [(Hk & evs0 & fs & Hevs) | (evs0 & sig & fs & Hevs)].
        { split; [| exact Hk]. apply (HE (evs i) Htr code fs). rewrite Hevs. apply in_app_iff. right. left. reflexivity. }
        { exfalso. pose proof (HK (evs i) Htr) as HF. rewrite Hevs in HF.
          apply Forall_app in HF as [_ HF]. inversion HF as [| x l Hx _]; subst. exact Hx. }
  - destruct (m_halted (cfg_model c)) as [code |] eqn:Hc; [| congruence].
    destruct (Hhalt code eq_refl) as [Hin Hk].
    eapply must_exit_in_at_cfg_halted; eassumption.
  - exfalso. exact Hmode.
  - apply IH; [ eapply exit_codes_in_t_eq; [apply t_eq_sym; exact Heq | exact HE]
              | eapply kill_free_t_eq; [apply t_eq_sym; exact Heq | exact HK]
              | exact Hhalt ].
  - exfalso. rewrite BMOFF in Hon. discriminate Hon.
Qed.

(** The statement's form, as [HaltsKit.srealizes_init_must_exit] has it, less
    its budget premise. *)
Theorem srealizes_init_must_exit_off : forall scfgD segs pc ph sp brk0 mb rnd lim inp S T,
  @srealizes0 bmK segs scfgD (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  exit_codes_in S T -> kill_free T ->
  must_exit_in_scfg forced_only_cfg S (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros scfgD segs pc ph sp brk0 mb rnd lim inp S T Hs HE HK.
  cbn [must_exit_in_scfg].
  apply (srealizes_must_exit_fo_off segs scfgD S _ T Hs HE HK).
  intros code Hh. exfalso. unfold init_config in Hh. cbn [cfg_model] in Hh. rewrite m_halted_init_model in Hh. discriminate Hh.
Qed.
End Off.
