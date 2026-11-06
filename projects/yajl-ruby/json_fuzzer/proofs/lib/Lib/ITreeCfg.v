(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section ITreeCfg.

Variable cfg : SpuriousCfg.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.

Record node_sound_cfg : Prop := {
  nsc_pending : forall n ms, at_node n ms -> ms_svc_pending ms <> None;
  nsc_complete : forall n ms mo evs X, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      sstep_cfg segs cfg (mkCfg ms mo) evs X ->
        (exists rsp mo', X = SNext (mkCfg (nret ms rsp) mo') /\ nstep n mo rsp mo' evs)
     \/ (exists code mo', X = SNext (mkCfg ms mo') /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')]);
  nsc_sound : forall n ms mo rsp mo' evs, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nstep n mo rsp mo' evs ->
      m_halted mo' = None /\ minv mo'
      /\ sstep_cfg segs cfg (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo'));
  nsc_exit : forall n ms mo code mo', at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nexit n mo code mo' ->
      m_halted mo' = Some code /\ sstep_cfg segs cfg (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo'));
  nsc_progress : forall n ms mo, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      (exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo');
  nsc_lazy : forall mo, minv mo -> m_vm_lazy mo = []
}.

End ITreeCfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Antitone.
Variable node : Type.
Variables nstep nstep' : node -> Model -> resp -> Model -> list event -> Prop.
Variable nsafe : node -> Model -> Prop.
Hypothesis SUB : forall n mo rsp mo' evs, nstep' n mo rsp mo' evs -> nstep n mo rsp mo' evs.

Lemma tsafe_antitone : forall {R} (t : itree node R) mo,
  tsafe nstep nsafe t mo -> tsafe nstep' nsafe t mo.
Proof.
  intros R t; induction t as [r | n k IH]; intros mo H; cbn in *; [exact I|].
  destruct H as [Hs Hk]. split; [exact Hs|].
  intros rsp mo' evs Hst. apply IH. eapply Hk. apply SUB. exact Hst.
Qed.

Lemma tpath_monotone : forall {R} (t : itree node R) mo tr r mo',
  tpath nstep' t mo tr r mo' -> tpath nstep t mo tr r mo'.
Proof.
  intros R t; induction t as [r0 | n k IH]; intros mo tr r mo' H; cbn in *.
  - exact H.
  - destruct H as (rsp & mo1 & evs & tr' & Hst & Hp & E).
    exists rsp, mo1, evs, tr'. split; [apply SUB; exact Hst|]. split; [apply IH; exact Hp | exact E].
Qed.

Lemma leaves_unreachable_m_antitone : forall {R} (t : itree node R) mo,
  leaves_unreachable_m nstep t mo -> leaves_unreachable_m nstep' t mo.
Proof.
  intros R t mo H tr r mo' Hp. apply (H tr r mo'). apply tpath_monotone. exact Hp.
Qed.

End Antitone.
