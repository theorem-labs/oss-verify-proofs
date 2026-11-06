(* The footprint twin of reac_ctrl_record_cksum_verify.v: the same run as an ExecF.evtF under a footprint RNG
   (reac_ctrl_record_cksum_verify_contract_F), by the script of reac_ctrl_record_cksum_verify.v over StepF's step.
   Each access of the run is closed from one rng premise: the frame store/load of ra, the two 8-byte loads of the
   GOT cell and the runtime cell, and, per data byte, the 1-byte load of its shadow byte and the 1-byte load of the
   byte itself. The empty buffer (a1 = 0) reads nothing but the frame, so the data and shadow premises are guarded
   by 1 <= bv_unsigned a1, as the asan premises of the old contract are.
   reac_ctrl_record_cksum_verify_holds_of_F re-derives the old contract from the footprint form with RNG_all. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT reac_ctrl_record_cksum_verify_c reac_ctrl_record_cksum_verify.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Section LoopF.
  Variables (ra sp1 gp tp t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (off : Z) (bs : list byte) (W : list ivl)
    (Q : machine_state -> Prop) (RNG : footprint).
  Hypothesis Hq : bv_unsigned a0 <> 0.
  Hypothesis Hqn : bv_unsigned a0 + Z.of_nat (length bs) <= 2^64.
  Hypothesis HB : bytes_at rsegs m (bv_unsigned a0) bs.
  Hypothesis HSR : asan_shadow_rd rsegs m off (bv_unsigned a0) (Z.of_nat (length bs)) W.
  Hypothesis HAD : asan_addressable rsegs m off (bv_unsigned a0) (Z.of_nat (length bs)).
  Hypothesis RDAT : rng RNG (bv_unsigned a0) (Z.of_nat (length bs)).
  Hypothesis RSH : rng RNG (bv_unsigned a0 / 8 + off)
                     ((bv_unsigned a0 + Z.of_nat (length bs) - 1) / 8 - bv_unsigned a0 / 8 + 1).

  Abbreviation ST pc x5 x11 x12 x13 x16 x17 :=
    (MS (mkR ra sp1 gp tp x5 t1 t2 s0 s1 a0 x11 x12 x13 (Z_to_bv 64 off) (v_sltu (Z_to_bv 64 0) a0) x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x5 x11 x12 x16 x17,
    evtF rsegs RNG Q (ST 0x83d74 x5 x11 x12 (Z_to_bv 64 (psum bs (length bs))) x16 x17).

  Lemma loop_F : forall n i x5 x11 x12 x16 x17,
    (i + n = length bs)%nat -> (0 < n)%nat ->
    bv_unsigned x11 = Z.of_nat n ->
    bv_unsigned x12 = bv_unsigned a0 + Z.of_nat i ->
    bv_unsigned x16 = bv_unsigned a0 + Z.of_nat i ->
    evtF rsegs RNG Q (ST 0x83d24 x5 x11 x12 (Z_to_bv 64 (psum bs i)) x16 x17).
  Proof using Hq Hqn HB HSR HAD RDAT RSH EXIT.
    induction n as [|n IH]; intros i x5 x11 x12 x16 x17 Hin Hn H11 H12 H16; [lia|].
    pose proof (zr_word a0) as Ra. unfold inr64 in Ra.
    (* The shadow byte of data byte i: inside RSH. *)
    assert (RSi : rng RNG ((bv_unsigned a0 + Z.of_nat i) / 8 + off) 1).
    { apply (rng_sub' RNG (bv_unsigned a0 / 8 + off)
               ((bv_unsigned a0 + Z.of_nat (length bs) - 1) / 8 - bv_unsigned a0 / 8 + 1) _ _ RSH).
      pose proof (Z.div_le_mono (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat i) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_mono (bv_unsigned a0 + Z.of_nat i) (bv_unsigned a0 + Z.of_nat (length bs) - 1) 8
                    ltac:(lia) ltac:(lia)).
      split; lia. }
    assert (BODY : forall y5 y17,
      evtF rsegs RNG Q (ST 0x83d48 y5 x11 x12 (Z_to_bv 64 (psum bs i)) x16 y17)).
    { intros y5 y17.
      pose proof (rd_byte rsegs m (bv_unsigned a0) bs i HB ltac:(lia)) as RD.
      rewrite <- H16 in RD. rewrite (wa_of_var x16 (bv_unsigned x16) eq_refl) in RD.
      step. step. step. step. step.
      rewrite psum_S_zxb.
      step.
      rewrite (rc_eqb0 (bv_unsigned x11 + -1)) by lia.
      destruct n as [|n].
      - replace (bv_unsigned x11 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbv iota.
        replace (S i) with (length bs) by lia.
        apply EXIT.
      - replace (bv_unsigned x11 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbv iota. step.
        apply (IH (S i)); first [lia | rewrite unsigned_lit by lia; lia]. }
    step.
    rewrite (rc_ltu_ge a0 x12) by lia.
    step. step. step.
    rewrite (rc_ubchk a0 x12) by lia.
    step.
    rewrite (rc_neq0w a0) by exact Hq.
    destruct (asan_shadow_read rsegs m off (bv_unsigned a0) (Z.of_nat (length bs)) W (Z.of_nat i) HSR
                ltac:(lia)) as (k & RK & BK).
    pose proof (HAD (Z.of_nat i) k ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    step.
    rewrite H12. rewrite rc_shr3.
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step.
      rewrite H12. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((bv_unsigned a0 + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (bv_unsigned a0 + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((bv_unsigned a0 + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.
End LoopF.

Theorem reac_ctrl_record_cksum_verify_holds_F_on : reac_ctrl_record_cksum_verify_contract_F_on.
Proof.
  unfold reac_ctrl_record_cksum_verify_contract_F_on, REAC_CTRL_RECORD_CKSUM_VERIFY,
    REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo bs Hlen Hpre ST HLO HCE HADR HW RFR RGOT RCELL RDAT RSH.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  destruct (Z.eq_dec (bv_unsigned a1) 0) as [H0 | Hn].
  - assert (E : bs = []) by (destruct bs; [reflexivity | cbn in Hlen; lia]). subst bs.
    clear HCE HADR HW Hpre RDAT RSH.
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
    specialize (HW ltac:(lia)). specialize (RDAT ltac:(lia)). specialize (RSH ltac:(lia)).
    pose proof (rt_asan_rt m _ HCE HW) as HRT.
    pose proof (rt_shadow_rd m _ _ _ HADR (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
    pose proof (rt_addressable m _ _ HADR) as HAD.
    replace (shadow_addr (bv_unsigned a0 + bv_unsigned a1 - 1) - shadow_addr (bv_unsigned a0) + 1)
      with ((bv_unsigned a0 + bv_unsigned a1 - 1) / 8 - bv_unsigned a0 / 8 + 1) in RSH
      by (unfold shadow_addr; lia).
    unfold shadow_addr in RSH.
    set (off := ASAN_K) in HRT, HSR, HAD, RSH. clearbody off.
    assert (Hlen' : Z.of_nat (length bs) = bv_unsigned a1) by lia.
    rewrite <- Hlen' in RDAT, RSH.
    unfold GOT_CELL_K, CELL_K in RGOT, RCELL.
    carve_frame 16%nat ST.
    step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    step.
    rewrite (rc_neq0w a1) by exact Hn.
    pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_shadow_rd_munch rsegs m m1 off _ _ _ _ HSR MU (fun x Hx => Hx)) as HSR1.
    pose proof (asan_addressable_munch rsegs m m1 off _ _ _ _ HAD HSR MU (fun x Hx => Hx)) as HAD1.
    rewrite <- Hlen' in HSR1, HAD1.
    pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    step. step. step. step.
    clear RG RC.
    step. step. step.
    refine (loop_F ra _ gp tp t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m1 off bs _ _ RNG Hq ltac:(lia) HB HSR1 HAD1 RDAT RSH _ (length bs) 0 t0 a1 a0 a0 a7
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    intros x5 x11 x12 x16 x17.
    step. step. step. step. step. step. step.
    rewrite rc_fin2.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. cbv beta. unfold recsum. do 9 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV) | exact ST].
Qed.

(* The old footprint statement, one line from the _on one (route (C): the guarded shadow_rw premise dropped). *)
Theorem reac_ctrl_record_cksum_verify_holds_F : reac_ctrl_record_cksum_verify_contract_F.
Proof. exact (reac_ctrl_record_cksum_verify_contract_F_of_on reac_ctrl_record_cksum_verify_holds_F_on). Qed.

(* The old contract as a corollary: evtF_evt of the footprint form at RNG_all, each rng premise by rng_all. *)
Theorem reac_ctrl_record_cksum_verify_holds_of_F : reac_ctrl_record_cksum_verify_contract.
Proof.
  unfold reac_ctrl_record_cksum_verify_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo bs Hlen Hpre ST HLO HCE HSW HADR HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (zr_word a1) as Ra1. unfold inr64 in Ra1.
  pose proof ST as (ST0 & _ & _).
  pose proof HLO as HLO'. unfold REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME in HLO'.
  assert (HA : bv_unsigned a0 + bv_unsigned a1 <= 2^64)
    by (destruct Hpre as [Hz | (_ & Hqn & _ & _)]; lia).
  apply (evtF_evt rsegs RNG_all).
  apply (reac_ctrl_record_cksum_verify_holds_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo bs); try assumption;
    intros; apply rng_all; unfold REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K;
    Z.div_mod_to_equations; lia.
Qed.
