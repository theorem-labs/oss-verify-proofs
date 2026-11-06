(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac SysStep Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim Prog KLink KLink3.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import Malloc_iface.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs RMalloc_iface RMalloc_ifaceP RMalloc_iface_stmt HeapSR_iface MallocSR.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import SReach SReachTree SReachCjNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma SR_laws_proof : HeapSR_iface.SR_laws HS.
Proof. try hcb. try hsb.
  unfold HeapSR_iface.SR_laws. cbn [HeapSR_iface.hs_SR HS]. splits.
  - apply sreach_done.
  - intros Q Q' c H HQ. eapply sreach_mono; eauto.
  - intros Q1 Q2 c H1 H2. eapply sreach_seq; eauto.
  - intros P ms mo HH HL EV. eapply sreach_mono; [eapply (cj_evt_sreach usegs _ _ mo HH HL EV)|]. intros c [A B]; auto.
Qed.

Lemma bptr_eqb_eq : forall p q, bptr_eqb p q = true <-> p = q.
Proof. try hcb. try hsb.
  intros [a i] [b j]. unfold bptr_eqb. cbn [fst snd]. rewrite andb_true_iff, aptr_eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros H; injection H; auto].
Qed.
Lemma bptr_eqb_refl : forall p, bptr_eqb p p = true.
Proof. try hcb. try hsb. intros p. apply bptr_eqb_eq. reflexivity. Qed.
Lemma lb_remove_laws_proof : HeapSR_iface.lb_remove_laws HS.
Proof. try hcb. try hsb.
  unfold HeapSR_iface.lb_remove_laws. cbn [HeapSR_iface.hs_lb_remove HS]. unfold lb_remove. splits.
  - intros p A n LB Hn. cbn -[bptr_eqb]. rewrite bptr_eqb_refl. cbn -[bptr_eqb].
    induction LB as [|b LB IH]; [reflexivity|]. cbn -[bptr_eqb]. cbn in Hn.
    destruct (bptr_eqb (MallocBlocks.blk_id b) p) eqn:E; cbn -[bptr_eqb].
    + exfalso. apply Hn. left. apply bptr_eqb_eq in E. exact E.
    + f_equal. apply IH. intros H; apply Hn; right; exact H.
  - intros p b LB Hne. cbn -[bptr_eqb]. destruct (bptr_eqb (MallocBlocks.blk_id b) p) eqn:E; cbn -[bptr_eqb]; [| reflexivity].
    exfalso. apply Hne. apply bptr_eqb_eq in E. exact E.
  - intros p LB b H. induction LB as [|c LB IH]; [exact H|]. cbn -[bptr_eqb] in H.
    destruct (bptr_eqb (MallocBlocks.blk_id c) p); cbn -[bptr_eqb] in H; [right; apply IH; exact H|].
    destruct H as [<-|H]; [left; reflexivity| right; apply IH; exact H].
Qed.

Theorem heap_sr_hyps_of_gap : PHASE2 -> HeapSR_iface.heap_sr_hyps HS.
Proof. try hcb. try hsb.
  intros P2. unfold HeapSR_iface.heap_sr_hyps. splits.
  - apply SR_laws_proof.
  - apply KREL_laws_proof.
  - apply MPRES_laws_proof.
  - apply alloc_ok_of_live_proof.
  - exact RHEAP_frame_proof.
  - exact RHEAP_block_range_proof.
  - exact RHEAP_blocks_disjoint_proof.
  - exact RHEAP_blocks_nodup_proof.
  - exact rauxv_frame_mirror.
  - apply lb_remove_laws_proof.
  - apply (malloc_sr P2).
  - apply (opnew_sr P2).
  - apply free_sr.
  - apply opdel_sr.
  - apply opdel2_sr.
  - apply opdel_null_sr.
  - apply opdel2_null_sr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hx_sr_proof : forall Q c, HeapSR_iface.hs_SR HS Q c -> sreach usegs Q c.
Proof. try hcb. try hsb. intros Q c H. exact H. Qed.

Lemma hx_mpres_proof : forall mo mo', HeapSR_iface.hs_MPRES HS mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo.
Proof. try hcb. try hsb. intros mo mo' (H1 & H2 & _). auto. Qed.

End HCW.


From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Step.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RMallocRep.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RBand.

Section HCW2.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rw_cells_rdn1 : forall m A cs, rw_cells usegs m A cs ->
  Lib.PropExec.rdn usegs m (Z_to_bv 64 A) (cells_size cs) = Some (cells_bytes cs).
Proof. try hcb. try hsb.
  intros m A cs [[WF BA] _].
  pose proof (bytes_at_rdn usegs m A (cells_bytes cs) 0 (cells_size cs) BA) as R.
  rewrite Z.add_0_r, firstn_all2 in R; [| cbn [skipn]; rewrite cells_bytes_length by exact WF; lia].
  apply R. cbn [skipn]. rewrite cells_bytes_length by exact WF. lia.
Qed.

Lemma hx_statics_proof : forall s LB m, RHEAP s LB m ->
  Lib.PropExec.rdn usegs m (Z_to_bv 64 0xb6c03) 1 = Some [Z_to_bv 8 0]
  /\ Lib.PropExec.rdn usegs m (Z_to_bv 64 0x83b30) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb69b0))
  /\ Lib.PropExec.rdn usegs m (Z_to_bv 64 0xb69b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 hcanary)).
Proof. try hcb. try hsb.
  intros s LB m (st & LB0 & _ & _ & MR & _).
  destruct MR as (_ & _ & (G1 & G2 & G3 & G4 & G5 & G6) & _).
  split; [| split].
  - exact (rw_cells_rdn1 _ _ _ G2).
  - exact (rw_cells_rdn1 _ _ _ G4).
  - exact (rw_cells_rdn1 _ _ _ G5).
Qed.

End HCW2.

