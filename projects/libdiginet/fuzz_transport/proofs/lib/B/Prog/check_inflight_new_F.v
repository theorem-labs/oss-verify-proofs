From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_inflight_new_c check_inflight_new_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_inflight_new_contract_F (image B, entry 0x84654, frame 16 bytes), with StepF's step: each access
   side goal is closed from an rng fact for the accessed range.

   The walk (listing DgnTransportBList.v, slots 3309-3327, AF_check_inflight_new = 0x33b4):
     0x84654-0x84658  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x8465c-0x84660  auipc a0; addi a0,a0,..: a0 = 0x5dede0 = TB_M (listing A_OBJ 8).
     0x84664          lw a1,12(a0): a1 = the 4-byte load at 0x5dedec = M.state, sign-extended.
     0x84668-0x8466c  li a2,2; bne a1,a2, 0x84694.
     0x84670          lw a1,96(a0): a1 = the 4-byte load at 0x5dee40 = M.fly.on, sign-extended.
     0x84674          bnez a1, 0x84694.
     0x84678-0x8467c  auipc a1; ld a1,..(a1): a1 = the 8-byte load at 0x5ded80 = TB_g_now (listing A_OBJ 28).
     0x84680          ld a0,56(a0): a0 = the 8-byte load at 0x5dee18 = M.backoff_until.
     0x84684          bltu a1,a0, 0x84694.
     0x84688-0x84690  ld ra,8(sp); addi sp,sp,16; ret.
   The trap path 0x84694 / 0x84698 / 0x8469c (TB___asan_handle_no_return, TB_abort, then the unimp word 0xc0001073)
   is never reached: the model premise check_inflight_new_m Bw = Some (Bw', tt) gives M_state Bw = 2,
   M_fly_on Bw = 0, g_now Bw >= M_backoff_until Bw and Bw' = Bw. By the world relation the loaded bytes are sub Bw A c
   for each accessor's offset A (tw_bytes_at), so the two lw leave Z_to_bv 64 (s32_at ..) (lw_world) and the two ld
   leave Z_to_bv 64 (u_at .. 8) (ld_world): the three branches fall through. The unimp word at 0x8469c is reached only
   from the abort call at 0x84698, so the same facts rule it out. The function has no UBSan check of its own.

   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 payload ranges (off_stk premise), so tw_at holds of the same Bw
   (TMAP_B_kept). *)

(* A world bytes_at fact survives a munch of a range it does not meet (image B's rsegs). *)
Lemma cin_bytes_tp : forall m m' lo hi a bs, munch [(lo, hi)] m m' ->
  a + Z.of_nat (length bs) <= lo \/ hi <= a -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo hi a bs MU Hd H. eapply bytes_at_transport; [exact H | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Theorem check_inflight_new_holds_F : check_inflight_new_contract_F.
Proof.
  unfold check_inflight_new_contract_F, CHECK_INFLIGHT_NEW, CHECK_INFLIGHT_NEW_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' HW HM ST HLO HOFF RFR RST RFL RNW RBK.
  (* the model: M.state = 2, M.fly.on = 0, g_now >= M.backoff_until, and Bw' = Bw *)
  unfold TC.check_inflight_new_m in HM.
  lazymatch type of HM with
  | (if ?c then _ else _) = _ => destruct c eqn:C1; [discriminate HM|]
  end.
  lazymatch type of HM with
  | (if ?c then _ else _) = _ => destruct c eqn:C2; [discriminate HM|]
  end.
  pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end) HM)
    as HB.
  cbv beta iota in HB. subst Bw'. clear HM.
  apply orb_false_iff in C1 as [C1 C3].
  apply negb_false_iff, Z.eqb_eq in C1. unfold TC.S_ONLINE in C1.
  unfold TC.truth in C3. apply negb_false_iff, Z.eqb_eq in C3.
  assert (R1 : 0 <= TW.g_now Bw < 2 ^ 64) by exact (TWorldLemmas.u_at_range Bw TW.OFF_g_now 8).
  assert (R2 : 0 <= TW.M_backoff_until Bw < 2 ^ 64)
    by exact (TWorldLemmas.u_at_range Bw TW.A_M_backoff_until 8).
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in HOFF.
  rewrite check_inflight_new_state_at in RST.
  rewrite check_inflight_new_fly_on_at in RFL.
  rewrite check_inflight_new_now_at in RNW.
  rewrite check_inflight_new_backoff_at in RBK.
  (* the world bytes the four loads read, as raw memory *)
  assert (L1 : length (TW.sub Bw TW.A_M_state 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_M_state, TW.OFF_M; lia|].
    rewrite (tw_len TMAP_B _ Bw HW). unfold TW.A_M_state, TW.OFF_M, TW.W_LEN. lia. }
  assert (L2 : length (TW.sub Bw TW.A_M_fly_on 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_M_fly_on, TW.OFF_M; lia|].
    rewrite (tw_len TMAP_B _ Bw HW). unfold TW.A_M_fly_on, TW.OFF_M, TW.W_LEN. lia. }
  assert (L3 : length (TW.sub Bw TW.OFF_g_now 8) = 8%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.OFF_g_now; lia|].
    rewrite (tw_len TMAP_B _ Bw HW). unfold TW.OFF_g_now, TW.W_LEN. lia. }
  assert (L4 : length (TW.sub Bw TW.A_M_backoff_until 8) = 8%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_M_backoff_until, TW.OFF_M; lia|].
    rewrite (tw_len TMAP_B _ Bw HW). unfold TW.A_M_backoff_until, TW.OFF_M, TW.W_LEN. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 12 4 TMAP_B_ok HW TMAP_B_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BF1.
  change (TB_M + 12) with 0x5dedec in BF1. change (TW.OFF_M + 12) with TW.A_M_state in BF1.
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 96 4 TMAP_B_ok HW TMAP_B_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BF2.
  change (TB_M + 96) with 0x5dee40 in BF2. change (TW.OFF_M + 96) with TW.A_M_fly_on in BF2.
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_g_now TB_g_now TW.SZ_g_now 0 8 TMAP_B_ok HW TMAP_B_g_now
    ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)) as BF3.
  change (TB_g_now + 0) with 0x5ded80 in BF3. change (TW.OFF_g_now + 0) with TW.OFF_g_now in BF3.
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 56 8 TMAP_B_ok HW TMAP_B_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BF4.
  change (TB_M + 56) with 0x5dee18 in BF4. change (TW.OFF_M + 56) with TW.A_M_backoff_until in BF4.
  (* keep the world's bytes off transport_chunks: they are transported by hand past the ra store *)
  pose proof (conj BF1 (conj BF2 (conj BF3 (conj BF4 I)))) as BFC. clear BF1 BF2 BF3 BF4.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x84654-0x84658: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  destruct BFC as (BF1 & BF2 & BF3 & BF4 & _).
  pose proof (cin_bytes_tp m m0 _ _ 0x5dedec (TW.sub Bw TW.A_M_state 4) MU1 ltac:(rewrite L1; lia) BF1) as BF1'.
  pose proof (cin_bytes_tp m m0 _ _ 0x5dee40 (TW.sub Bw TW.A_M_fly_on 4) MU1 ltac:(rewrite L2; lia) BF2) as BF2'.
  pose proof (cin_bytes_tp m m0 _ _ 0x5ded80 (TW.sub Bw TW.OFF_g_now 8) MU1 ltac:(rewrite L3; lia) BF3) as BF3'.
  pose proof (cin_bytes_tp m m0 _ _ 0x5dee18 (TW.sub Bw TW.A_M_backoff_until 8) MU1 ltac:(rewrite L4; lia) BF4)
    as BF4'.
  assert (RD1 : ov_read_bytes rsegs m0 (wa 0x5dedec) 4 = Some (TW.sub Bw TW.A_M_state 4)).
  { replace (wa 0x5dedec) with (wa (0x5dedec + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 0x5dedec _ 0 4 BF1' ltac:(lia)) by (rewrite L1; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L1. lia. }
  assert (RD2 : ov_read_bytes rsegs m0 (wa 0x5dee40) 4 = Some (TW.sub Bw TW.A_M_fly_on 4)).
  { replace (wa 0x5dee40) with (wa (0x5dee40 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 0x5dee40 _ 0 4 BF2' ltac:(lia)) by (rewrite L2; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L2. lia. }
  assert (RD3 : ov_read_bytes rsegs m0 (wa 0x5ded80) 8 = Some (TW.sub Bw TW.OFF_g_now 8)).
  { replace (wa 0x5ded80) with (wa (0x5ded80 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 0x5ded80 _ 0 8 BF3' ltac:(lia)) by (rewrite L3; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L3. lia. }
  assert (RD4 : ov_read_bytes rsegs m0 (wa 0x5dee18) 8 = Some (TW.sub Bw TW.A_M_backoff_until 8)).
  { replace (wa 0x5dee18) with (wa (0x5dee18 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 0x5dee18 _ 0 8 BF4' ltac:(lia)) by (rewrite L4; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L4. lia. }
  clear BF1 BF2 BF3 BF4 BF1' BF2' BF3' BF4'.
  (* 0x8465c-0x84664: a0 = &M; a1 = M.state = 2 *)
  step. step. step.
  rewrite lw_world. change (TW.s32_at Bw TW.A_M_state) with (TW.M_state Bw). rewrite C1.
  (* 0x84668-0x8466c: a2 = 2; bne a1,a2 falls through *)
  step. step. if_false.
  (* 0x84670: a1 = M.fly.on = 0 *)
  step.
  rewrite lw_world. change (TW.s32_at Bw TW.A_M_fly_on) with (TW.M_fly_on Bw). rewrite C3.
  (* 0x84674: bnez a1 falls through *)
  step. if_false.
  (* 0x84678-0x8467c: a1 = g_now *)
  step. step.
  rewrite ld_world. change (TW.u_at Bw TW.OFF_g_now 8) with (TW.g_now Bw).
  (* 0x84680: a0 = M.backoff_until *)
  step.
  rewrite ld_world. change (TW.u_at Bw TW.A_M_backoff_until 8) with (TW.M_backoff_until Bw).
  (* 0x84684: bltu a1,a0 falls through: g_now >= M.backoff_until *)
  step.
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; rewrite bv_ltu_Z, !unsigned_lit by lia; exact C2]
  end.
  (* 0x84688-0x84690: ld ra; addi sp; ret *)
  step. step. step.
  apply evtF_done. do 4 eexists. split; [reflexivity|].
  split; [exact MU1|].
  split; [match goal with WM' : wmono rsegs m m0 |- _ => exact WM' end|].
  split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  split; [reflexivity|].
  apply (@TMAP_B_kept rsegs m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
Qed.

Print Assumptions check_inflight_new_holds_F.
