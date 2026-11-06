(* Segment of the ubsan walk of on_announce (on_announce.v): the e0 announce (diginet_session.c:200-206), from
   0x171b4, after the DESK notice, f->h.cmd == DIGINET_CMD_ANNOUNCE:
     0x171b4 lw    a0, 112(s0)     s->state
     0x171b8 li    a1, 2
     0x171bc sw    zero, 136(s0)   :201 s->foreign = 0
     0x171c0 bne   a0, a1, 0x171e0  :202 not ONLINE
     0x171c4 sw    zero, 168(s0)   session_lost inlined (:162-163): desk_counter_valid = 0, inflight = 0
     0x171c8 sw    zero, 212(s0)
     0x171cc li    a2, 3           DIGINET_R_DESK_OFFLINE
     0x171d0 mv    a0, s0
     0x171d4 li    a1, 0           DIGINET_S_IDLE
     0x171d8 jal   set_state       :164
     0x171dc lw    a0, 112(s0)
     0x171e0 ...                   oa_wake (on_announce_tail.v) *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC
  set_state_c diginet_session_wake_c on_announce_model on_announce_lib on_announce_tail.
Import ListNotations.
Open Scope Z_scope.

Lemma oa_e0 : set_state_contract -> diginet_session_wake_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo : Z) (B' : list byte) (TF : option tframe) (now off : Z) (b : list byte)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B2 : list byte) (c0 cx cf1 cf2 cn1 cn2 ca : list cell),
  bv_unsigned sp mod 16 = 0 -> lo + 1056 <= bv_unsigned sp -> W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 1056 ->
  0 <= now < 2 ^ 64 -> tframe_at m0 sp 1056 TF -> relro_img m0 ->
  munch [(bv_unsigned sp - 1056, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -304) ->
  oa_low m sp c0 cx cf1 cf2 cn1 cn2 ca ->
  rw_cells rsegs m (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B2 -> g_fail_next B2 <= 1 ->
  fr_cmd b = DIGINET_CMD_ANNOUNCE ->
  oa_after_m timg_ubsan TF B2 b off now = Some (B', tt) ->
  evt rsegs (oa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp t0 t1 t2
             (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 now) a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171b4) fc None m (seg_rom rsegs)).
Proof.
  intros SETST WAKE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' TF now off b
    x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m B2
    c0 cx cf1 cf2 cn1 cn2 ca SP16 LO WOS Hnow TFA RR MU WMO MI ST LOW FRs WM GF CMD HM.
  unfold set_state_contract, set_state_ENTRY, set_state_FRAME in SETST.
  oa_low_unpack LOW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -304)) = bv_unsigned sp + -304) by (apply unsigned_lit; lia).
  pose proof (wm_len _ _ _ _ WM) as LB2.
  unfold oa_after_m in HM. rewrite CMD, Z.eqb_refl in HM. cbv zeta in HM.
  set (B3 := set_S_foreign B2 0) in HM.
  assert (LB3 : length B3 = Z.to_nat W_LEN) by (unfold B3, set_S_foreign; wlen).
  assert (SB3 : S_state B3 = S_state B2)
    by (unfold B3, S_state, set_S_foreign; apply s32_upd_W; wside).
  assert (GB3 : g_fail_next B3 = g_fail_next B2) by (unfold B3, set_S_foreign; apply gfn_upd; wside).
  pose proof (s32_range B2 A_S_state) as RS. change (s32_at B2 A_S_state) with (S_state B2) in RS.
  (* lw a0, 112(s0); li a1, 2; sw zero, 136(s0) *)
  step. step. step.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
    replace X with B3 in H; [rename H into WM3 |] end.
  2:{ unfold B3, set_S_foreign, A_S_foreign. rewrite ?le4_put. reflexivity. }
  change (s32_at B2 1760) with (S_state B2).
  (* bne a0, a1: not ONLINE *)
  step. rewrite oa_eqbk by (unfold DIGINET_S_ONLINE; lia).
  rewrite SB3 in HM.
  destruct (S_state B2 =? 2) eqn:EON; cbn [negb] in HM |- *.
  2:{ (* not ONLINE: the wake test at 0x171e0 on the world B3 *)
    change DIGINET_S_ONLINE with 2 in HM. rewrite EON in HM. cbv iota in HM.
    eapply oa_wake; try eassumption.
    - oa_low_pack.
    - rewrite GB3. exact GF.
    - rewrite SB3. reflexivity. }
  change DIGINET_S_ONLINE with 2 in HM. rewrite EON in HM. cbv iota in HM.
  (* ONLINE: session_lost (:202-203), the two stores, then set_state (IDLE, DESK_OFFLINE) *)
  unfold session_lost_m in HM. cbv zeta in HM.
  set (B4 := set_S_desk_counter_valid (set_S_inflight B3 0) 0) in HM.
  destruct (set_state_m timg_ubsan TF B4 DIGINET_S_IDLE DIGINET_R_DESK_OFFLINE) as [[B5 []]|] eqn:HS;
    [|discriminate HM].
  cbv beta iota in HM.
  assert (LB4 : length B4 = Z.to_nat W_LEN) by (unfold B4, set_S_desk_counter_valid, set_S_inflight; wlen).
  assert (GB4 : g_fail_next B4 = g_fail_next B3)
    by (unfold B4, set_S_desk_counter_valid, set_S_inflight; rewrite !gfn_upd by wside; reflexivity).
  (* sw zero, 168(s0); sw zero, 212(s0) *)
  step. step.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
    replace X with B4 in H; [rename H into WM4 |] end.
  2:{ unfold B4, set_S_desk_counter_valid, set_S_inflight, A_S_desk_counter_valid, A_S_inflight.
      rewrite ?le4_put. apply upd_comm_W; wside. }
  (* li a2, 3; mv a0, s0; li a1, 0; jal set_state *)
  do 4 step.
  eapply evt_cut.
  { eapply SETST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - exact WM4.
    - rewrite GB4, GB3. exact GF.
    - exact HS.
    - eapply tframe_at_move; [exact TFA | exact MU | rewrite Hsp; lia | rewrite Hsp; lia].
    - eapply relro_img_move; [exact RR | exact MU | exact WOS].
    - rewrite Hsp. Z.div_mod_to_equations. lia.
    - rewrite Hsp. exact ST.
    - rewrite Hsp. lia.
    - unfold w_off_stack. rewrite Hsp. lia.
    - exact MI. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & ST2 & WM5 & GF5).
  subst ms'. rewrite Hsp in MUc, ST2. clear WM4.
  lazymatch type of MUc with munch _ ?mm m2 => transport_after_call rsegs mm m2 MUc WMc end.
  clear MUc WMc MI.
  rewrite (ret_pc_even 0x171dc) by (first [lia | reflexivity]).
  (* lw a0, 112(s0): the state after set_state *)
  step.
  change (s32_at B5 1760) with (S_state B5).
  eapply oa_wake; try eassumption.
  - oa_low_pack.
  - reflexivity.
Qed.
