(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start and main states per CONFIG_RSEQ, taken at the launch's flag; the initial-valuation invariant Jinit taking the launch's mmap base, rebuilt from a valuation that agrees below 14 for the exec-file-name value; the launch model's channel reader passed to the drivers, LPS 08b1429; the spine statements' malloc-entry state taken at the run's own flag, and their JM over the mmap base; main_safe and top_sound_U proved from the same walk stated for every world predicate that meets the frame obligations, which top_rob_U runs at RobReach.ok_rob for the read-only backing's robustness at every reached configuration, RunSeg.rob_reach, LPS 75d69e00). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Kernel.Fork.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymCall SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec SpecTop.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Start OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open_all.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require RunSeg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require RobReach.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Start OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G3.Drv_usage OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G3.Drv_usage_all OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open_all.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Jinit_agree : forall segs pc ph sp mb draw inp n rho rho',
  agree_below n rho rho' -> (14 <= n)%positive -> Jinit segs pc ph sp mb draw inp rho -> Jinit segs pc ph sp mb draw inp rho'.
Proof.
  intros segs pc ph sp mb draw inp n rho rho' (Hw & Hl & Hm) Hn HJ.
  destruct HJ; constructor; try (rewrite <- Hw by lia; assumption); try (rewrite <- Hl; assumption).
  intros a. rewrite <- Hm. auto.
Qed.

Lemma hd_nth0 : forall l : list (list byte), hd [] l = nth 0 l [].
Proof. intros [|]; reflexivity. Qed.

Section Top.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hent : valid_entry48 imgU (mkEntry sp brk mb draw) inp.
Hypothesis Hinp : valid_input_either inp.
Let argv := in_argv inp.
Let argv0 : list byte := nth 0 argv [].
Let argv1 : list byte := nth 1 argv [].
Let fs := in_fs inp.
Let c0 : config := c0U sp brk mb draw lim inp.
Let m0 : Model := cfg_model c0.
Let SpecT : list event -> Prop := Spec inp.

(* [comment removed for export] *)
Definition md_main (tid : word) : Model := with_tid tid m0.

Lemma md_main_fds : forall tid, m_fds (md_main tid) = std_fds.
Proof using . intros tid. reflexivity. Qed.
Lemma md_main_fs : forall tid, m_fs (md_main tid) = fs.
Proof using . intros tid. reflexivity. Qed.
Lemma md_main_fd2 : forall tid, fd_lookup (m_fds (md_main tid)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof using . intros tid. reflexivity. Qed.
(* LPS 08b1429: [init_model] copies [in_channel_reader] into the model and no step writes it;
   [valid_input_either]'s thirteenth conjunct pins it true. *)
Lemma md_main_rdr : forall tid, m_channel_reader (md_main tid) = true.
Proof using Hinp.
  intros tid. destruct Hinp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition spine_safe_stmt : Prop :=
  forall (tid : word) (ok : world -> Prop),
    0 < bv_unsigned tid < PID_MAX_ENVELOPE ->
    (forall K, K_tcons SpecT K -> ok_frame segsU ok K) ->
    (forall K, K_tcons SpecT K -> ok_pframe segsU ok K) ->
    ok_halted ok SpecT ->
    length argv = 2%nat -> open_may_succeed argv1 fs ->
    forall rho, JM sp mb draw inp rho ->
      triple segsU ok (SP segsU (Kx [] (md_open (md_main tid) argv1)) (S_M (kb_rseq (in_kernel inp))) rho) (fun _ => False).

Definition spine_ex_stmt : Prop :=
  forall (tid : word) (t : list event),
    0 < bv_unsigned tid < PID_MAX_ENVELOPE ->
    length argv = 2%nat -> open_may_succeed argv1 fs -> In t (post_open_traces argv1 fs) ->
    forall rho, JM sp mb draw inp rho ->
      etriple segsU (SP segsU (Kx [] (md_open (md_main tid) argv1)) (S_M (kb_rseq (in_kernel inp))) rho) (fun w => w_tr w = t).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tcons_nil : tcons SpecT [].
Proof using inp. destruct (Spec_nonempty inp) as [t Ht]. exists t. split; [exact Ht | apply is_prefix_nil]. Qed.

Lemma Ktc_K0 : K_tcons SpecT (K0 m0).
Proof using c0. intros tr md [-> _]. apply tcons_nil. Qed.
Lemma Ktc_K1 : K_tcons SpecT (K1 m0).
Proof using c0. intros tr md [-> _]. apply tcons_nil. Qed.

Let okT : world -> Prop := ok_tgt segsU SpecT.
Lemma HokK : forall K, K_tcons SpecT K -> ok_frame segsU okT K. Proof using inp. intros K HK. apply ok_frame_tgt_K. exact HK. Qed.
Lemma HokP : forall K, K_tcons SpecT K -> ok_pframe segsU okT K. Proof using inp. intros K HK. apply ok_pframe_tgt_K. exact HK. Qed.
Lemma Hokh : ok_halted okT SpecT. Proof using inp. apply ok_halted_tgt. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* LPS 75d69e00: [main_safe] for every world predicate that meets the three frame obligations;
   [main_safe] is it at [okT], and [top_rob_U] runs it at [RobReach.ok_rob]. *)
Lemma main_safe_ok : spine_safe_stmt -> forall (ok : world -> Prop),
  (forall K, K_tcons SpecT K -> ok_frame segsU ok K) ->
  (forall K, K_tcons SpecT K -> ok_pframe segsU ok K) ->
  ok_halted ok SpecT ->
  forall tid rho,
  0 < bv_unsigned tid < PID_MAX_ENVELOPE -> Jinit segsU pcU phU sp mb draw inp rho ->
  triple segsU ok (SP segsU (U.Drv_open__G1.Drv_open.Kx [] (md_main tid)) (S_main (kb_rseq (in_kernel inp))) rho) (fun _ => False).
Proof using Hent Hinp.
  intros Hspine ok HK HP Hh tid rho Htid HJ.
  destruct (Nat.eq_dec (length argv) 2) as [E|NE].
  - apply (open_safe sp brk mb draw inp Hent Hinp E (md_main tid) (md_main_fds tid) (md_main_fs tid) (md_main_rdr tid) ok HK HP Hh); [|exact HJ].
    intros Hmay rho' HJM. exact (Hspine tid ok Htid HK HP Hh E Hmay rho' HJM).
  - exact (usage_safe sp brk mb draw inp Hent Hinp NE (md_main tid) (md_main_fd2 tid) (md_main_fs tid) (md_main_rdr tid) ok HK HP Hh rho HJ).
Qed.

Lemma main_safe : spine_safe_stmt -> forall tid rho,
  0 < bv_unsigned tid < PID_MAX_ENVELOPE -> Jinit segsU pcU phU sp mb draw inp rho ->
  triple segsU okT (SP segsU (U.Drv_open__G1.Drv_open.Kx [] (md_main tid)) (S_main (kb_rseq (in_kernel inp))) rho) (fun _ => False).
Proof using Hent Hinp. intros Hspine. exact (main_safe_ok Hspine okT HokK HokP Hokh). Qed.

(* LPS 75d69e00: [top_sound_U] for every world predicate that meets the three frame
   obligations. *)
Theorem top_sound_ok : spine_safe_stmt -> forall (ok : world -> Prop),
  (forall K, K_tcons SpecT K -> ok_frame segsU ok K) ->
  (forall K, K_tcons SpecT K -> ok_pframe segsU ok K) ->
  ok_halted ok SpecT ->
  forall n, safe segsU ok n (w0 c0).
Proof using Hent Hinp.
  intros Hspine ok HK HP Hh.
  destruct (init_smatch_U sp brk mb draw lim inp Hent Hinp) as (rhoI & Hsm & HJ).
  apply (triple_init_safe c0 (Init := SP segsU (K0 m0) (S0_U (kb_rseq (in_kernel inp))) rhoI)).
  { split; [exact Hsm | split; reflexivity]. }
  eapply triple_seq.
  { apply (start_sum_U sp brk mb draw lim inp Hent Hinp rhoI HJ ok); [apply HK; apply Ktc_K0 | apply HP; apply Ktc_K0 | apply HK; apply Ktc_K1]. }
  unfold LQ, LQJ. apply triple_ex; intros L. apply triple_ex; intros rho'.
  apply triple_pure; intros [<-|[]]. apply triple_pure; intros Hag. cbn [lf_state].
  eapply triple_conseq with (P := fun w => exists tid, 0 < bv_unsigned tid < PID_MAX_ENVELOPE /\ SP segsU (U.Drv_open__G1.Drv_open.Kx [] (md_main tid)) (S_main (kb_rseq (in_kernel inp))) rho' w);
    [| intros w Hw; exact Hw |].
  { intros w [Hsm' [Htr (tid & Htid & Hmd)]]. exists tid. split; [exact Htid|]. split; [exact Hsm'|]. split; [exact Htr | exact Hmd]. }
  apply triple_ex; intros tid. apply triple_pure; intros Htid.
  apply (main_safe_ok Hspine ok HK HP Hh tid rho' Htid). exact (Jinit_agree _ _ _ _ _ _ _ 20 rhoI rho' Hag ltac:(lia) HJ).
Qed.

Theorem top_sound_U : spine_safe_stmt -> forall n, safe segsU okT n (w0 c0).
Proof using Hent Hinp. intros Hspine. exact (top_sound_ok Hspine okT HokK HokP Hokh). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma main_exists : spine_ex_stmt -> forall tid rho t,
  0 < bv_unsigned tid < PID_MAX_ENVELOPE -> Jinit segsU pcU phU sp mb draw inp rho -> SpecT t ->
  etriple segsU (SP segsU (U.Drv_open__G1.Drv_open.Kx [] (md_main tid)) (S_main (kb_rseq (in_kernel inp))) rho) (fun w => w_tr w = t).
Proof using Hent Hinp.
  intros Hspine tid rho t Htid HJ Ht.
  destruct (Spec_cases inp t Ht) as [[NE ->] | [[E ->] | (E & Hmay & Hin)]].
  - pose proof (usage_exists sp brk mb draw inp Hent Hinp NE (md_main tid) (md_main_fd2 tid) (md_main_fs tid) (md_main_rdr tid) rho HJ) as X.
    unfold die. rewrite (hd_nth0 (in_argv inp)). exact X.
  - exact (cannot_open_exists sp brk mb draw inp Hent Hinp E (md_main tid) (md_main_fds tid) (md_main_fs tid) (md_main_rdr tid) rho HJ).
  - apply (open_exists sp brk mb draw inp Hent Hinp E (md_main tid) (md_main_fds tid) (md_main_fs tid) Hmay); [|exact HJ].
    intros rho' HJM. exact (Hspine tid t Htid E Hmay Hin rho' HJM).
Qed.

Theorem top_complete_U : spine_ex_stmt -> COMPLETE segsU c0 SpecT.
Proof using Hent Hinp.
  intros Hspine. apply etriple_complete. intros t Ht w ->.
  destruct (init_smatch_U sp brk mb draw lim inp Hent Hinp) as (rhoI & Hsm & HJ).
  assert (Hsp0 : SP segsU (K0 m0) (S0_U (kb_rseq (in_kernel inp))) rhoI (w0 c0)) by (split; [exact Hsm | split; reflexivity]).
  destruct (start_sum_ex_U sp brk mb draw lim inp Hent Hinp rhoI HJ (w0 c0) Hsp0) as (w1 & Hst1 & L & rho' & [<-|[]] & Hag & Hsm' & Htr & tid & Htid & Hmd).
  cbn [lf_state] in Hsm'.
  assert (Hsp1 : SP segsU (U.Drv_open__G1.Drv_open.Kx [] (md_main tid)) (S_main (kb_rseq (in_kernel inp))) rho' w1) by (split; [exact Hsm' | split; [exact Htr | exact Hmd]]).
  destruct (main_exists Hspine tid rho' t Htid (Jinit_agree _ _ _ _ _ _ _ 20 rhoI rho' Hag ltac:(lia) HJ) Ht w1 Hsp1) as (w2 & Hst2 & Htr2).
  exists w2. split; [eapply wsteps_trans; eauto | exact Htr2].
Qed.

Theorem top_U : spine_safe_stmt -> spine_ex_stmt ->
  SOUND segsU c0 SpecT /\ COMPLETE segsU c0 SpecT /\ ~ reaches_error_a segsU c0.
Proof using Hent Hinp.
  intros Hs He. split; [|split].
  - apply (safe_tgt_sound SpecT). exact (top_sound_U Hs).
  - exact (top_complete_U He).
  - apply (safe_tgt_noerror SpecT). exact (top_sound_U Hs).
Qed.

(* LPS 75d69e00: the read-only backing is robust at every configuration the run reaches over
   the binary's own segments ([RunSeg.rob_reach]), the premise of the lift of [top_U]'s facts
   to the run's segment list (RobReach.facts_run_init): the walk of [top_sound_ok] at
   [RobReach.ok_rob]. *)
Theorem top_rob_U : spine_safe_stmt -> RunSeg.rob_reach segsU c0.
Proof using Hent Hinp.
  intros Hspine. apply (RobReach.safe_rob_reach segsU SpecT c0).
  exact (top_sound_ok Hspine (RobReach.ok_rob segsU SpecT) (RobReach.ok_frame_rob_K segsU SpecT)
           (RobReach.ok_pframe_rob_K segsU SpecT) (RobReach.ok_halted_rob segsU SpecT)).
Qed.

End Top.
