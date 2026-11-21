(* SPDX-License-Identifier: MIT *)
(* The two bridges to the statement's run, for the sanitizer builds' [SpinAlg.srealizes].

   The plain builds' [ShapeAlg.realizes] has them already:
     (B1) Common/RunSegTail.realizes_run_segments        the run's segment INDEX
     (B2) Common/Cfg/RomStable.realizes_run_init         the run's start CONFIGURATION
   [srealizes] differs from [realizes] by one constructor, [srz_spin] (a silent loop at a
   configuration reaching [to_spin]).  Each bridge below is the [realizes] one with that case
   added, and the case is a transport of [to_spin] along the same step identity the node case
   already uses:
     (B1) [RunSegTail.mi_account_step_app_nx] (the tail is neither executable nor writable)
     (B2) [RomStable.mi_account_step_wrom]
   (B2) needs [RomBase.sys_rob] at every node, which [srz_node] asks just as [rz_node] does.
   The order at a top is the plain one: (B2), then (B1).  The plain builds' bridge (A)
   (Common/VdsoBridge, the launch's vDSO draw) has no twin here: no sanitizer top applies one. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg DivergeSim SpinAlg.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.Cfg.RomBase.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.Cfg.RomStable.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RunSegTail.

(** * (B1): the run's segment index *)

Section SAppTail.
Variables segs tail : list Segment.
Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.

Lemma to_spin_app_tail : forall ms m, to_spin segs ms m -> to_spin (segs ++ tail) ms m.
Proof.
  intros ms m H.
  induction H as [ms m Hs Hst | ms m ms' m' Hs Hst H IH].
  - apply ts_spin; [exact Hs|]. eapply RunSegTail.mi_account_step_app_nx; eassumption.
  - eapply ts_step; [exact Hs | | exact IH]. eapply RunSegTail.mi_account_step_app_nx; eassumption.
Qed.

Hypothesis Hvi : vdso_image segs = None.

(* The flag and the dead-arm witnesses pass unchanged: [HaltsFO.dead_sib] reads only the machine states. *)
Theorem srealizes_app_tail {b : bool} : forall c T, srealizesM segs b c T -> srealizesM (segs ++ tail) b c T.
Proof.
  intros c T H.
  induction H as [b c I evs nx T i0 bi Hnode Hrob Hcont IH Hdead | b c Hh | c Hsp Hh | b c T T' H IH Heq].
  - apply (srzM_node (segs ++ tail) b c I evs nx T i0 bi).
    + (* section arguments: segs tail Hnx Hnw Hvi *)
      exact (RunSegTail.node_ok_app_tail _ _ Hnx Hnw Hvi c I evs nx i0 Hnode).
    + eapply RunSegTail.sys_rob_app_tail; eassumption.
    + exact IH.
    + exact Hdead.
  - exact (srzM_halt (segs ++ tail) b c Hh).
  - apply srzM_spin; [apply to_spin_app_tail; exact Hsp | exact Hh].
  - exact (srzM_conseq (segs ++ tail) b c T T' IH Heq).
Qed.
End SAppTail.

Theorem srealizes_run_segments {b : bool} : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  srealizesM segs b c T -> srealizesM (run_segments segs inp sp mb) b c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply (srealizes_app_tail segs _
           (fun s Hs => RunSegTail.vdso_segments_nx _ _ _ s Hs)
           (fun s Hs => RunSegTail.vdso_segments_nw _ _ _ s Hs) Hvi).
  exact H.
Qed.

(** * (B2): the run's start configuration *)

Lemma to_spin_wrom : forall segs ms m r,
  to_spin segs ms m -> to_spin segs (RomBase.wrom ms r) m.
Proof.
  intros segs ms m r H.
  induction H as [ms m Hs Hst | ms m ms' m' Hs Hst H IH].
  - apply ts_spin; [exact Hs|]. rewrite RomStable.mi_account_step_wrom, Hst. reflexivity.
  - eapply ts_step; [exact Hs | | exact IH]. rewrite RomStable.mi_account_step_wrom, Hst. reflexivity.
Qed.

Section SWrom.
Variable segs : list Segment.
Hypothesis Hvi : vdso_image segs = None.

(* The flag and the dead-arm witnesses pass unchanged: [RomBase.wrom] keeps the registers and the pending call. *)
Theorem srealizes_wrom {b : bool} : forall c T, srealizesM segs b c T ->
  forall r, RomBase.rom_ext (ms_rom (cfg_ms c)) r -> srealizesM segs b (RomBase.cwrom c r) T.
Proof.
  intros c T H.
  induction H as [b c I evs nx T i0 bi Hn Hrob Hc IH Hdead | b c Hh | c Hsp Hh | b c T T' H IH Heq]; intros r Hr.
  - apply (srzM_node segs b (RomBase.cwrom c r) I evs (fun i => RomBase.cwrom (nx i) r) T i0 bi).
    + eapply RomStable.node_wrom; eassumption.
    + eapply RomStable.sys_rob_wrom; eassumption.
    + intros i. apply IH. erewrite RomStable.node_rom; eassumption.
    + intros i Hb Hbi. destruct (Hdead i Hb Hbi) as [j Hj]. exists j. exact Hj.
  - apply srzM_halt. exact Hh.
  - apply srz_spin; unfold RomBase.cwrom; cbn [cfg_ms cfg_model].
    + apply to_spin_wrom. exact Hsp.
    + exact Hh.
  - eapply srz_conseq; [apply IH; exact Hr | exact Heq].
Qed.
End SWrom.

Theorem srealizes_run_init {b : bool} : forall segs inp (sp brk mb : word) pc ph rnd lim T,
  vdso_image segs = None ->
  srealizesM segs b (init_config segs pc ph sp brk mb rnd lim inp) T ->
  srealizesM segs b (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp brk mb pc ph rnd lim T Hvi H.
  rewrite RomStable.init_config_run_segments.
  apply (srealizes_wrom segs Hvi _ T H).
  cbn [cfg_ms init_config]. apply RomStable.seg_rom_run_segments_ext.
Qed.
