(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: the ubsan binary's copy of Ref/HeapSRRun.v (the heap interface's run instance hsr_run over usegs ++ tail, and hsr_vc's additions for the vDSO pair), with usegs in place of rsegs. *)
(* The heap interface's second instance, over the run's
   segment list.  [MallocSR.HS] reaches its targets over the binary's own segments
   ([hs_SR HS = sreach usegs]); a run that calls time() executes in the vDSO pair, so the library
   that calls it is instantiated at [hsr_run H]: the same heap relations, and an [hs_SR] that
   reaches over [usegs ++ tail] from the state with the larger list's read-only backing
   ([RunTail.sreach_lift_tail]).  Every [heap_sr_hyps_x] field of [hsr_run H] is a proved lift of
   [H]'s ([heap_sr_hyps_x_run]); [time_sr_stmt] is not one of them (it is the vDSO call).
   This is the copy for the ubsan binary's [HeapSR_iface]: [rsegs] replaced by [usegs]. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil Scfg SReach.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Exec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase RomStable RunTail.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import VdsoClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import MmVdso.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Run.
  Context {HCEIL : HeapCeil}.
  Variable tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image usegs = None.

  Local Notation VS := (usegs ++ tail) (only parsing).
  Local Notation rV := (OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.seg_rom (usegs ++ tail)) (only parsing).

  (** reaching [Q] over the run's list, from the state with the run's backing *)
  Definition sr_run (Q : config -> Prop) (c : config) : Prop :=
    sreach VS (fun c' => exists c0, c' = cwrom c0 rV /\ Q c0) (cwrom c rV).

  Definition hsr_run (H : hsr) : hsr :=
    {| hs_SR := sr_run; hs_KREL := hs_KREL H; hs_MPRES := hs_MPRES H; hs_RHEAP := hs_RHEAP H;
       hs_rauxv_ok := hs_rauxv_ok H; hs_lb_remove := hs_lb_remove H; hs_alloc_ok := hs_alloc_ok H;
       hs_LIVE_MAX := hs_LIVE_MAX H; hs_LIVE_CNT_MAX := hs_LIVE_CNT_MAX H;
       hs_LIVE_BIG_MAX := hs_LIVE_BIG_MAX H; hs_canary := hs_canary H |}.

  Variable H : hsr.
  Hypothesis Hsr : forall Q c, hs_SR H Q c -> sreach usegs Q c.

  (** [H]'s reach from a state with the binary's backing is a reach of [hsr_run H]. *)
  Lemma sr_run_of : forall Q c, hs_SR H Q c ->
    ms_rom (cfg_ms c) = OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.seg_rom usegs -> sr_run Q c.
  Proof.
    intros Q c HQ Hr. unfold sr_run.
    exact (sreach_lift_tail usegs tail Hnx Hnw Hvi Q c (Hsr Q c HQ) Hr).
  Qed.

  Lemma SR_laws_run : SR_laws (hsr_run H).
  Proof.
    unfold SR_laws. cbn [hs_SR hsr_run]. split; [|split; [|split]].
    - intros Q c HQ. apply sr_done. exists c. split; [reflexivity | exact HQ].
    - intros Q Q' c HQ Himp. eapply sreach_mono; [exact HQ|].
      intros c' (c0 & -> & H0). exists c0. split; [reflexivity | exact (Himp c0 H0)].
    - intros Q1 Q2 c H1 H2. eapply sreach_seq; [exact H1|].
      intros c' (c0 & -> & H0). exact (H2 c0 H0).
    - intros P ms mo Hh Hl EV. exact (exec_evt_sreach_tail usegs tail Hnx Hnw P ms mo rV Hh Hl EV).
  Qed.

  (* [eapply]: a statement's binders that only its premises mention ([s], [errv]) are fixed by
     the premises in context, not by the conclusion *)
  Ltac lift_stmt HM :=
    intros; apply sr_run_of; [eapply HM; eassumption | reflexivity].

  Theorem heap_sr_hyps_run : heap_sr_hyps H -> heap_sr_hyps (hsr_run H).
  Proof.
    intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & M1 & M2 & M3).
    split; [exact SR_laws_run|].
    do 9 (split; [assumption|]).
    split; [unfold malloc_sr_stmt, malloc_sr_stmt_at in *; lift_stmt M1|].
    split; [unfold free_sr_stmt, free_sr_stmt_at in *; lift_stmt M2|].
    unfold free_null_sr_stmt, free_null_sr_stmt_at in *; lift_stmt M3.
  Qed.

  Theorem heap_sr_hyps_x_run : heap_sr_hyps_x H -> heap_sr_hyps_x (hsr_run H).
  Proof.
    intros (X0 & X1 & X2 & X3 & X4 & X5 & X6).
    split; [exact (heap_sr_hyps_run X0)|].
    split; [unfold realloc_sr_stmt, realloc_sr_stmt_at in *; lift_stmt X1|].
    split; [unfold aalloc_sr_stmt, aalloc_sr_stmt_at in *; lift_stmt X2|].
    split; [exact X3|]. split; [exact X4|]. split; [exact X5| exact X6].
  Qed.
End Run.

(** The relations of a run instance the library can be closed at.  The vDSO walk of time() reads
   the vDSO pair's bytes from the segment list, so the overlay must hold no byte of the pair
   [[vlo, vhi)] when time() runs ([VdsoClean.vclean]), and the pair must stay the launch's reserved
   pair: its vvar entry [[vlo, vmid)] and its text entry [[vmid, vhi)] are entries of
   [State.vdso_reserved] (State.v:6559-6564), which [vm_reserved] holds ([MmVdso.mm_vinv], once per
   entry).  [hsr_vc] adds both to an instance: the heap relation adds the clean pair and every
   client block's distance from it, the kernel relation adds [pair_inv].  The model refuses every
   write a run could make into the pair ([VdsoClean]'s header).  The auxv relation adds that its
   stack bound [B] is at most [State.TASK_SIZE]: time()'s vDSO call answers only for a timespec
   below it ([Spec/VdNode.vd_at_node]), and every bound a run starts with is an sp of the launch's
   window (State.v:160-161).  Generic in [H]: a unit with this [HeapSR_iface] copies it whole. *)
Section RunVC.
  Variables vlo vmid vhi : Z.

  Definition blk_off (b : block) : Prop := blk_addr b + blk_size b <= vlo \/ vhi <= blk_addr b.

  Definition pair_inv (mo : Model) : Prop := mm_vinv vlo vmid mo /\ mm_vinv vmid vhi mo.

  (** the invariant a heap call's own tree carries ([MallocSR.HSI]) *)
  Definition run_inv (c : config) : Prop := vclean vlo vhi (ms_mem (cfg_ms c)) /\ pair_inv (cfg_model c).

  Definition hsr_vc (H : hsr) : hsr :=
    {| hs_SR := hs_SR H;
       hs_KREL := fun s mo => hs_KREL H s mo /\ pair_inv mo;
       hs_MPRES := hs_MPRES H;
       hs_RHEAP := fun s LB m => hs_RHEAP H s LB m /\ vclean vlo vhi m /\ Forall blk_off LB;
       hs_rauxv_ok := fun m B => hs_rauxv_ok H m B /\ B <= TASK_SIZE;
       hs_lb_remove := hs_lb_remove H; hs_alloc_ok := hs_alloc_ok H;
       hs_LIVE_MAX := hs_LIVE_MAX H; hs_LIVE_CNT_MAX := hs_LIVE_CNT_MAX H;
       hs_LIVE_BIG_MAX := hs_LIVE_BIG_MAX H; hs_canary := hs_canary H |}.
End RunVC.
