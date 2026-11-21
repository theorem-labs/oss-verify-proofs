(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from P/Top.v (Jinit_agree, top_sound_P and main_safe's argc <> 2 branch): the same walk over BudgetWit.StartB and BudgetWit.UsageB, safe for BudgetWit.NoAlloc.okB, so that the run of the plain build reaches no budget-refused configuration when argc <> 2. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the initial-valuation invariant Jinit taking the launch's mmap base, rebuilt from a valuation that agrees below 14 for the exec-file-name value; the start state and the main entry at this run's CONFIG_RSEQ, as P/Top.v takes them; the launch model's channel reader, LPS 08b1429, given to UsageB by md_main_rdr, as P/Top.v does; top_never_refused states the budget premise over the run's segment list and the run's start, where Run.run_budget_refused reads the binary, LPS 75d69e00, by NoAlloc.okB_never_refused_run with top_rob_B, the released argc <> 2 walk of P/Top.v at RobReach.ok_rob). *)

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Kernel.Fork.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymCall SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec SpecTop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Import Init StartStates.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Start OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require RunSeg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require RobReach.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.BudgetWit Require Import NoAlloc.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.BudgetWit.StartB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.BudgetWit.UsageB.
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

Section TopB.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hent : valid_entry48 imgP (mkEntry sp brk mb draw) inp.
Hypothesis Hinp : valid_input_either inp.
Hypothesis Hargc : length (in_argv inp) <> 2%nat.
Let c0 : config := c0P sp brk mb draw lim inp.
Let m0 : Model := cfg_model c0.
Let SpecT : list event -> Prop := Spec inp.

Definition md_main (tid : word) : Model := with_tid tid m0.

Lemma md_main_fd2 : forall tid, fd_lookup (m_fds (md_main tid)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof using . intros tid. reflexivity. Qed.
Lemma md_main_fs : forall tid, m_fs (md_main tid) = in_fs inp.
Proof using . intros tid. reflexivity. Qed.
(* LPS 08b1429: [init_model] copies [in_channel_reader] into the model and no step writes it;
   [valid_input_either]'s thirteenth conjunct pins it true (as P/Top.v's [md_main_rdr]). *)
Lemma md_main_rdr : forall tid, m_channel_reader (md_main tid) = true.
Proof using Hinp.
  intros tid. destruct Hinp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma tcons_nil : tcons SpecT [].
Proof using inp. destruct (Spec_nonempty inp) as [t Ht]. exists t. split; [exact Ht | apply is_prefix_nil]. Qed.

Lemma Ktc_K0 : K_tcons SpecT (P.Start.K0 m0).
Proof using c0. intros tr md [-> _]. apply tcons_nil. Qed.
Lemma Ktc_K1 : K_tcons SpecT (P.Start.K1 m0).
Proof using c0. intros tr md [-> _]. apply tcons_nil. Qed.

Let okT : world -> Prop := okB segsP SpecT.

(** [P/Top.v top_sound_P] with [okT] in place of the target obligation, and with the
    argc <> 2 branch of [main_safe] in place of [main_safe]. *)
Theorem top_safe_B : forall n, safe segsP okT n (w0 c0).
Proof using Hargc Hent Hinp.
  destruct (init_smatch_P sp brk mb draw lim inp Hent Hinp) as (rhoI & Hsm & HJ).
  apply (triple_init_safe c0 (Init := SP segsP (P.Start.K0 m0) (S0_P (kb_rseq (in_kernel inp))) rhoI)).
  { split; [exact Hsm | split; reflexivity]. }
  eapply triple_seq.
  { apply (StartB.start_sum_P sp brk mb draw lim inp Hent Hinp rhoI HJ okT).
    - exact (okB_frame segsP SpecT (P.Start.K0 m0) Ktc_K0).
    - exact (okB_pframe segsP SpecT (P.Start.K0 m0) Ktc_K0).
    - exact (okB_frame segsP SpecT (P.Start.K1 m0) Ktc_K1). }
  unfold LQ, LQJ. apply triple_ex; intros L. apply triple_ex; intros rho'.
  apply triple_pure; intros [<-|[]]. apply triple_pure; intros Hag. cbn [lf_state].
  eapply triple_conseq with (P := fun w => exists tid, 0 < bv_unsigned tid < PID_MAX_ENVELOPE /\ SP segsP (P.Drv_open__G1.Drv_open.Kx [] (md_main tid)) (S_main (kb_rseq (in_kernel inp))) rho' w);
    [| intros w Hw; exact Hw |].
  { intros w [Hsm' [Htr (tid & Htid & Hmd)]]. exists tid. split; [exact Htid|]. split; [exact Hsm'|]. split; [exact Htr | exact Hmd]. }
  apply triple_ex; intros tid. apply triple_pure; intros Htid.
  exact (UsageB.Drv_usage_all.usage_safe sp brk mb draw inp Hent Hinp Hargc (md_main tid) (md_main_fd2 tid) (md_main_fs tid) (md_main_rdr tid) okT
           (fun K HK => okB_frame segsP SpecT K HK) (fun K HK => okB_pframe segsP SpecT K HK) (okB_halted segsP SpecT)
           rho' (Jinit_agree _ _ _ _ _ _ _ 20 rhoI rho' Hag ltac:(lia) HJ)).
Qed.

(** LPS 75d69e00: the read-only backing is robust at every configuration the run reaches over
    the binary's own segments ([RunSeg.rob_reach]): the released walk of [P/Top.v top_sound_P]
    on the argc <> 2 path ([P/Start.v start_sum_P], the argc <> 2 branch of [main_safe],
    [P/Drv_usage__G3.v usage_safe]), which is generic in its world predicate, at
    [RobReach.ok_rob]. *)
Theorem top_rob_B : RunSeg.rob_reach segsP c0.
Proof using Hargc Hent Hinp.
  apply (RobReach.safe_rob_reach segsP SpecT c0).
  destruct (init_smatch_P sp brk mb draw lim inp Hent Hinp) as (rhoI & Hsm & HJ).
  apply (triple_init_safe c0 (Init := SP segsP (P.Start.K0 m0) (S0_P (kb_rseq (in_kernel inp))) rhoI)).
  { split; [exact Hsm | split; reflexivity]. }
  eapply triple_seq.
  { apply (P.Start.start_sum_P sp brk mb draw lim inp Hent Hinp rhoI HJ (RobReach.ok_rob segsP SpecT)).
    - exact (RobReach.ok_frame_rob_K segsP SpecT (P.Start.K0 m0) Ktc_K0).
    - exact (RobReach.ok_pframe_rob_K segsP SpecT (P.Start.K0 m0) Ktc_K0).
    - exact (RobReach.ok_frame_rob_K segsP SpecT (P.Start.K1 m0) Ktc_K1). }
  unfold LQ, LQJ. apply triple_ex; intros L. apply triple_ex; intros rho'.
  apply triple_pure; intros [<-|[]]. apply triple_pure; intros Hag. cbn [lf_state].
  eapply triple_conseq with (P := fun w => exists tid, 0 < bv_unsigned tid < PID_MAX_ENVELOPE /\ SP segsP (P.Drv_open__G1.Drv_open.Kx [] (md_main tid)) (S_main (kb_rseq (in_kernel inp))) rho' w);
    [| intros w Hw; exact Hw |].
  { intros w [Hsm' [Htr (tid & Htid & Hmd)]]. exists tid. split; [exact Htid|]. split; [exact Hsm'|]. split; [exact Htr | exact Hmd]. }
  apply triple_ex; intros tid. apply triple_pure; intros Htid.
  exact (P.Drv_usage__G3.Drv_usage_all.usage_safe sp brk mb draw inp Hent Hinp Hargc (md_main tid) (md_main_fd2 tid) (md_main_fs tid) (md_main_rdr tid)
           (RobReach.ok_rob segsP SpecT)
           (fun K HK => RobReach.ok_frame_rob_K segsP SpecT K HK) (fun K HK => RobReach.ok_pframe_rob_K segsP SpecT K HK)
           (RobReach.ok_halted_rob segsP SpecT)
           rho' (Jinit_agree _ _ _ _ _ _ _ 20 rhoI rho' Hag ltac:(lia) HJ)).
Qed.

End TopB.

(** On every entry of the plain build whose stack fits a 48-bit address space, and every
    input whose argv has not two entries, the unfiltered run over the run's segment list from
    the run's start reaches no budget-refused configuration, whatever the limit. *)
Theorem top_never_refused : forall sp brk mb draw lim inp,
  valid_entry48 imgP (mkEntry sp brk mb draw) inp -> valid_input_either inp ->
  length (in_argv inp) <> 2%nat ->
  ~ reaches_budget_refused (run_segments segsP inp sp mb)
      (init_config (run_segments segsP inp sp mb) pcP phP sp brk mb draw lim inp).
Proof.
  intros sp brk mb draw lim inp Hent Hinp Hargc.
  exact (okB_never_refused_run segsP inp sp brk mb pcP phP draw lim (Spec inp) ltac:(reflexivity)
           (top_rob_B sp brk mb draw lim inp Hent Hinp Hargc)
           (top_safe_B sp brk mb draw lim inp Hent Hinp Hargc)).
Qed.
