(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatSim ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import MState Exec.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.

Lemma msteps_lib_cat : forall ms ms', Exec.msteps segs ms ms' -> CatSim.msteps segs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 [Hsvc Hst] Hms IH].
  - apply CatSim.mst_refl.
  - eapply CatSim.mst_step; [exact Hsvc | exact Hst | exact IH].
Qed.

Lemma msteps_realizes : forall ms ms' model T,
  m_halted model = None -> m_vm_lazy model = nil ->
  Exec.msteps segs ms ms' ->
  realizes segs (mkCfg ms' model) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hl Hms Hr.
  eapply ShapeAlg.rz_msteps; [exact Hh | exact Hl | apply msteps_lib_cat; exact Hms | exact Hr].
Qed.

(* [comment removed for export] *)
Lemma evt_realizes : forall (Q : machine_state -> Prop) ms model T,
  m_halted model = None -> m_vm_lazy model = nil ->
  evt segs Q ms ->
  (forall ms', Q ms' -> realizes segs (mkCfg ms' model) T) ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros Q ms model T Hh Hl (ms' & Hms & HQ) K.
  eapply msteps_realizes; [exact Hh | exact Hl | exact Hms | apply K; exact HQ].
Qed.

End WithSegs.
