(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ITreeA NodesA NodesSil NodesAS NodesCov.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section AdequacyA.
Variable segs : list Segment.
Variable NMAX : nat.
Variable SHM : list (Z * Z).
Variable fstep : node -> resp -> footprint -> footprint -> Prop.

(* [comment removed for export] *)
Definition tree_atAA {R} (RNG : footprint) (A : alw) (t : itree node R) Q (ms : machine_state) (mo mo_ : Model) : Prop :=
  tree_atA segs (at_nodeA segs) (silA SHM) (npeekA segs) nstepA (minvA SHM) (nsafeA NMAX SHM) fstep NMAX RNG A t Q ms mo mo_.

(* [comment removed for export] *)
#[using="Type"] Theorem implA_adequate : forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atAA RNG A t Q ms mo mo_ ->
  adequate segs (npeekA segs) nstepA nexitA t mo (mkCfg ms mo_).
Proof.
  intros R t RNG A Q ms mo mo_ HT.
  exact (implF_adequate segs (at_nodeA segs) (silA SHM) (npeekA segs) nstepA nexitA (minvA SHM) (nsafeA NMAX SHM) fstep NMAX
           (nodesA_sound_closed segs NMAX SHM) (silA_sound segs NMAX SHM) t RNG A Q ms mo mo_ HT).
Qed.

#[using="Type"] Corollary implA_obs_sound : forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atAA RNG A t Q ms mo mo_ ->
  forall tr, obs_trace_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms mo_) tr -> ptraces nstepA nexitA t mo tr.
Proof. intros R t RNG A Q ms mo mo_ HT. exact (proj1 (proj2 (implA_adequate t RNG A Q ms mo mo_ HT))). Qed.

#[using="Type"] Corollary implA_obs_complete : forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atAA RNG A t Q ms mo mo_ ->
  forall W : list event -> Prop, wins (npeekA segs) nstepA nexitA t mo W ->
    exists tr, obs_trace_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms mo_) tr /\ W tr.
Proof. intros R t RNG A Q ms mo mo_ HT. exact (proj2 (proj2 (implA_adequate t RNG A Q ms mo mo_ HT))). Qed.

#[using="Type"] Corollary implA_no_error : forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atAA RNG A t Q ms mo mo_ -> ~ reaches_error_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms mo_).
Proof. intros R t RNG A Q ms mo mo_ HT. eapply SpinAlg.srealizes_no_error. exact (proj1 (implA_adequate t RNG A Q ms mo mo_ HT)). Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem implA_srealizes : forall {R} (t : itree node R) RNG A Q ms mo mo_,
  npfree (npeekA segs) t ->
  tree_atAA RNG A t Q ms mo mo_ ->
  SpinAlg.srealizes segs (mkCfg ms mo_) (ptraces nstepA nexitA t mo).
Proof.
  intros R t RNG A Q ms mo mo_ NP HT.
  exact (implF_srealizes segs (at_nodeA segs) (silA SHM) (npeekA segs) nstepA nexitA (minvA SHM) (nsafeA NMAX SHM) fstep NMAX
           (nodesA_sound_closed segs NMAX SHM) (silA_sound segs NMAX SHM) t RNG A Q ms mo mo_ NP HT).
Qed.

#[using="Type"] Corollary implA_obs_trace : forall {R} (t : itree node R) RNG A Q ms mo mo_,
  npfree (npeekA segs) t ->
  tree_atAA RNG A t Q ms mo mo_ ->
  forall tr, obs_trace_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms mo_) tr <-> ptraces nstepA nexitA t mo tr.
Proof. intros R t RNG A Q ms mo mo_ NP HT. apply SpinAlg.srealizes_obs_iff. eapply implA_srealizes; eassumption. Qed.

End AdequacyA.
