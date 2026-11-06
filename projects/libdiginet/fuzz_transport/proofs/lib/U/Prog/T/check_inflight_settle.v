From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract
  diginet_session_deadline_c check_inflight_settle_c.
Import ListNotations.
Open Scope Z_scope.

(* check_inflight_settle (fuzz/fuzz_transport.c:744-771), entry 0x1657c, 44 instructions (the plain code at other
   addresses, plus an `unimp` after `jal abort`), FRAME 32 (addi sp,sp,-32; saves ra, s0, s1). s0 = 0x430c8
   (W_BASE_UBSAN + OFF_g_fail_next), s1 = 0x33300 (M); every load is a world load.
   It calls diginet_session_deadline (jal 0x17c5c at 0x165d4) with a0 = &g_s = 0x33970, a1 = g_now; that call is
   cut in by diginet_session_deadline_contract, a hypothesis of the theorem.
   The model's Some (check_inflight_settle_m, TCb.v) gives every fact the walk needs: each abort() branch of the
   binary (all to `jal abort` at 0x16624) is not taken because its condition is the negation of one of these:
     0x1659c bne  GOT.acked, OW.acked                          GOT_acked B = OW_acked B (:750-751)
     0x165c8 bgeu g_now - M.fly.sent, ack_timeout_ms * 1000     M.fly.on <> 0 -> u64 (..) < h_ms_m (..) (:756-757)
     0x165dc bltu d, g_now                                      g_now B <= d (:763-764)
     0x165ec bltu g_now + 1000000, d                            d <= u64 (g_now B + 1000000) (:763-764)
     0x1660c bltu ack_timeout_ms * 1000 + M.fly.sent, d         M.fly.on <> 0 -> d <= u64 (..) (:769-770) *)
Lemma cis_m_facts : forall B B',
  check_inflight_settle_m B = Some (B', tt) ->
  B' = B /\ GOT_acked B = OW_acked B /\
  (M_fly_on B <> 0 -> u64 (g_now B - M_fly_sent B) < h_ms_m (Cfg_ack_timeout_ms B)) /\
  exists d, diginet_session_deadline_m B (g_now B) = Some d /\
    g_now B <= d /\ d <= u64 (g_now B + 1000000) /\
    (M_fly_on B <> 0 -> d <= u64 (M_fly_sent B + h_ms_m (Cfg_ack_timeout_ms B))).
Proof.
  intros B B' H. unfold check_inflight_settle_m in H.
  destruct (Z.eqb_spec (GOT_acked B) (OW_acked B)) as [E1|E1]; cbv beta iota delta [negb] in H; [|discriminate H].
  destruct (truth (M_fly_on B) && (h_ms_m (Cfg_ack_timeout_ms B) <=? u64 (g_now B - M_fly_sent B))) eqn:E2;
    cbv beta iota in H; [discriminate H|].
  destruct (diginet_session_deadline_m B (g_now B)) as [d|] eqn:Ed; cbv beta iota in H; [|discriminate H].
  destruct ((d <? g_now B) || (u64 (g_now B + 1000000) <? d)) eqn:E3; cbv beta iota in H; [discriminate H|].
  destruct (truth (M_fly_on B) && (u64 (M_fly_sent B + h_ms_m (Cfg_ack_timeout_ms B)) <? d)) eqn:E4;
    cbv beta iota in H; [discriminate H|].
  injection H as HB.
  apply Bool.orb_false_iff in E3 as [E3a E3b]. apply Z.ltb_ge in E3a. apply Z.ltb_ge in E3b.
  split; [symmetry; exact HB|]. split; [exact E1|]. split.
  - intros N. apply Bool.andb_false_iff in E2 as [E2|E2].
    + unfold truth in E2. apply Bool.negb_false_iff, Z.eqb_eq in E2. contradiction.
    + apply Z.leb_gt in E2. exact E2.
  - exists d. split; [reflexivity|]. split; [exact E3a|]. split; [exact E3b|].
    intros N. apply Bool.andb_false_iff in E4 as [E4|E4].
    + unfold truth in E4. apply Bool.negb_false_iff, Z.eqb_eq in E4. contradiction.
    + apply Z.ltb_ge in E4. exact E4.
Qed.

(* a branch whose condition the context decides *)
Ltac cis_br b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b;
      [ cbv iota
      | symmetry; unfold_cond; rewrite ?w0_lit; fold_lit_ux; rewrite ?unsigned_lit_wrap; solve_cond_rec ]
  end.

Theorem check_inflight_settle_holds : diginet_session_deadline_contract -> check_inflight_settle_contract.
Proof.
  intros DL. unfold check_inflight_settle_contract, check_inflight_settle_ENTRY, check_inflight_settle_FRAME.
  unfold diginet_session_deadline_contract, diginet_session_deadline_ENTRY, diginet_session_deadline_FRAME in DL.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B B'
    WM HM Hsp ST LO WS MI.
  destruct (cis_m_facts B B' HM) as (-> & EA & FLY1 & d & HD & D1 & D2 & FLY2). clear HM.
  assert (RN : 0 <= g_now B < 2 ^ 64) by exact (u_at_range B OFF_g_now 8).
  assert (RS : 0 <= M_fly_sent B < 2 ^ 64) by exact (u_at_range B A_M_fly_sent 8).
  assert (RC : 0 <= Cfg_ack_timeout_ms B < 2 ^ 32) by exact (u_at_range B A_Cfg_ack_timeout_ms 4).
  assert (RF : -2^31 <= M_fly_on B < 2^31) by apply s32_range.
  assert (HMS : h_ms_m (Cfg_ack_timeout_ms B) = Cfg_ack_timeout_ms B * 1000)
    by (unfold h_ms_m, u64; apply Z.mod_small; lia).
  rewrite HMS in FLY1, FLY2. clear HMS. unfold u64 in D2, FLY1, FLY2.
  wk_facts.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold w_off_stack in WS.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 32%nat ST.
  do 4 step.                              (* 0x1657c addi sp; sd ra, s0, s1 *)
  do 2 step.                              (* 0x1658c auipc a0; addi s0 = 0x430c8 *)
  step.                                   (* 0x16594 lw a0, 332(s0) = GOT.acked *)
  step.                                   (* 0x16598 lw a1, 560(s0) = OW.acked *)
  change (s32_at B 65300) with (GOT_acked B). change (s32_at B 65528) with (OW_acked B). rewrite EA.
  step.                                   (* 0x1659c bne a0, a1 -> abort *)
  cis_br false.
  do 4 step.                              (* auipc a0; addi s1 = M; lw a0, 96(s1) = M.fly.on; ld a1, 32(s0) = g_now *)
  change (s32_at B 96) with (M_fly_on B). change (u_at B 65000 8) with (g_now B).
  pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as USP.
  assert (TAIL : forall x10 x12 x13 : word,
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2
                          (Z_to_bv 64 274632) (Z_to_bv 64 209664) x10 (Z_to_bv 64 (g_now B)) x12 x13 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x165cc) fc None m0 (seg_rom rsegs))).
  { intros x10 x12 x13.
    do 3 step.                            (* 0x165cc auipc a0; addi a0 = &g_s; jal diginet_session_deadline *)
    eapply evt_cut.
    { eapply DL with (now := g_now B) (r := d) (B := B) (lo := lo).
      - reflexivity.
      - reflexivity.
      - exact RN.
      - exact WM.
      - exact HD.
      - rewrite USP. replace (bv_unsigned sp + -32) with (bv_unsigned sp + (-2) * 16) by lia.
        rewrite Z.mod_add by lia. exact Hsp.
      - rewrite USP. exact ST.
      - rewrite USP. lia.
      - unfold w_off_stack. rewrite USP. lia.
      - exact MI. }
    wk_post_call rsegs m0.
    step.                                 (* 0x165d8 ld a1, 32(s0) = g_now *)
    change (u_at B 65000 8) with (g_now B).
    step.                                 (* 0x165dc bltu a0, a1 -> abort: d >= g_now *)
    cis_br false.
    do 3 step.                            (* lui a2; addiw a2 = 1000000; add a1 = g_now + 1000000 *)
    step.                                 (* 0x165ec bltu a1, a0 -> abort: d <= g_now + 1000000 *)
    cis_br false.
    step.                                 (* 0x165f0 lw a1, 96(s1) = M.fly.on *)
    change (s32_at B 96) with (M_fly_on B).
    step.                                 (* 0x165f4 beqz a1, 0x16610 *)
    destruct (Z.eq_dec (M_fly_on B) 0) as [F0|F0].
    - cis_br true.
      do 3 step.                          (* 0x16610 ld ra, s0, s1 *)
      release_frame FR ST (bv_unsigned sp).
      do 2 step.                          (* 0x1661c addi sp, sp, 32; ret *)
      apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [reflexivity|]. eassumption.
    - cis_br false.
      do 5 step.                          (* lwu a1, 84(s0); ld a2, 112(s1); li a3, 1000; mul a1; add a1 *)
      change (u_at B 65052 4) with (Cfg_ack_timeout_ms B). change (u_at B 112 8) with (M_fly_sent B).
      step.                               (* 0x1660c bltu a1, a0 -> abort: d <= M.fly.sent + ms(ack_timeout) *)
      specialize (FLY2 F0).
      cis_br false.
      do 3 step.                          (* 0x16610 ld ra, s0, s1 *)
      release_frame FR ST (bv_unsigned sp).
      do 2 step.                          (* 0x1661c addi sp, sp, 32; ret *)
      apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [reflexivity|]. eassumption. }
  step.                                   (* 0x165b0 beqz a0, 0x165cc *)
  destruct (Z.eq_dec (M_fly_on B) 0) as [F0|F0].
  - cis_br true. apply TAIL.
  - cis_br false.
    do 5 step.                            (* ld a0, 112(s1); lwu a2, 84(s0); li a3, 1000; sub a0; mul a2 *)
    change (u_at B 65052 4) with (Cfg_ack_timeout_ms B). change (u_at B 112 8) with (M_fly_sent B).
    step.                                 (* 0x165c8 bgeu a0, a2 -> abort: g_now - M.fly.sent < ms(ack_timeout) *)
    specialize (FLY1 F0).
    cis_br false.
    apply TAIL.
Qed.
