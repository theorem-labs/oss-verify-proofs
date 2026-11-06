(* lib/B/Prog/record_sum_closesF_on.v -- route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane): the PROOF of
   record_sum_closes_contract_F_on (statement in lib/B/Prog/record_sum_closes_c_on.v). record_sum_closes_c.v,
   record_sum_closes.v (not in this delivery) and record_sum_closesF.v keep their code byte-identical.
   rule 24: no function proved here that is not already proved: the run is record_sum_closesF.v's
   record_sum_closes_holds_F (record_sum_closesF.v:115-177), re-run by the same script with the same loop lemma
   (record_sum_closes_loopF, reused), without the dropped shadow_rw premise.
   record_sum_closes_holds_F never uses that premise HSW (introduced at :119, cleared on the a1 = 0 path at :129,
   specialized on the a1 >= 1 path at :141, not used after). The run's shadow loads (the 1-byte load at shadow_addr x
   for each byte x of [a0, a0 + a1), :92-98) are closed from RK, which asan_shadow_read (:87-88) takes from HSR,
   rt_shadow_rd's asan_shadow_rd of the addressable premise HADR (:148).
   So the only changes to the script are that HSW is no longer introduced, cleared or specialized; the rest of the
   script is record_sum_closes_holds_F's, character for character. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT record_sum_closes_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import record_sum_closes_c_on record_sum_closesF.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Theorem record_sum_closes_holds_F_on : record_sum_closes_contract_F_on.
Proof.
  unfold record_sum_closes_contract_F_on, RECORD_SUM_CLOSES, RECORD_SUM_CLOSES_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo bs Hlen Hpre ST HLO HCE HADR HW RFR RGK RCK RDAT RSH.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  destruct (Z.eq_dec (bv_unsigned a1) 0) as [H0 | Hn].
  - assert (E : bs = []) by (destruct bs; [reflexivity | cbn in Hlen; lia]). subst bs.
    clear HCE HADR HW Hpre RGK RCK RDAT RSH.
    carve_frame 16%nat ST.
    step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    step.
    rewrite (rc_eq0w a1) by exact H0.
    step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. cbv beta. do 9 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV) | exact ST].
  - destruct Hpre as [H0 | (Hq & Hqn & HB & HD)]; [contradiction|].
    specialize (HCE ltac:(lia)). specialize (HADR ltac:(lia)).
    specialize (HW ltac:(lia)).
    specialize (RGK ltac:(lia)). specialize (RCK ltac:(lia)). specialize (RDAT ltac:(lia)).
    specialize (RSH ltac:(lia)).
    (* the two runtime cells are read at literal addresses *)
    unfold GOT_CELL_K, CELL_K in RGK, RCK.
    pose proof (rt_asan_rt m _ HCE HW) as HRT.
    pose proof (rt_shadow_rd m _ _ _ HADR (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
    pose proof (rt_addressable m _ _ HADR) as HAD.
    set (off := ASAN_K) in HRT, HSR, HAD, RSH. clearbody off.
    assert (Hlen' : Z.of_nat (length bs) = bv_unsigned a1) by lia.
    carve_frame 16%nat ST.
    step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    step.
    rewrite (rc_neq0w a1) by exact Hn.
    pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_shadow_rd_munch rsegs m m1 off _ _ _ _ HSR MU (fun x Hx => Hx)) as HSR1.
    pose proof (asan_addressable_munch rsegs m m1 off _ _ _ _ HAD HSR MU (fun x Hx => Hx)) as HAD1.
    rewrite <- Hlen' in HSR1, HAD1, RDAT, RSH.
    pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    step. step. step. step.
    clear RG RC.
    step. step. step.
    refine (record_sum_closes_loopF ra _ gp tp t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m1 off bs _ _ RNG Hq ltac:(lia) HB HSR1 HAD1 RDAT RSH _ (length bs) 0 t0 a1 a0 a0 a7
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    intros x5 x11 x12 x16 x17.
    step. step. step. step. step. step.
    rewrite rc_fin1.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. cbv beta. unfold recsum. do 9 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV) | exact ST].
Qed.
