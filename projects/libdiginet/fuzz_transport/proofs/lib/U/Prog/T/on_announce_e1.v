(* Segment of the ubsan walk of on_announce (on_announce.v): the e1 announce (diginet_session.c:209-220), from
   0x171fc, after the DESK notice, f->h.cmd != DIGINET_CMD_ANNOUNCE; s5 holds find_mac's off:
     0x171fc bltz  s5, 0x17218
     0x17200 li    a0, 1           :211-212 as one store: foreign = 0 (bytes 136..139), e1_named_us = 1 (140..143)
     0x17204 slli  a0, a0, 0x20
     0x17208 sd    a0, 136(s0)
     0x1720c mv    a0, s0
     0x17210 jal   maybe_online    :213
     0x17214 j     0x17070
     0x17218 li    s1, 1           off < 0
     0x1721c lw    a0, 112(s0)     s->state
     0x17220 addi  a1, sp, 160     &a
     0x17224 sd    a1, 40(sp)      fn.announce (fn at sp + 16)
     0x17228 li    a1, 6           DIGINET_N_FOREIGN
     0x1722c sw    s1, 136(s0)     :216 s->foreign = 1
     0x17230 sw    a1, 16(sp)      fn.kind
     0x17234 sw    a0, 20(sp)      fn.state
     0x17238 sd    zero, 24(sp)    fn.old_state, fn.reason
     0x1723c sd    s2, 32(sp)      fn.frame
     0x17240 addi  a0, sp, 48      the rest of fn: memset (&fn.personality, 0, 40)
     0x17244 li    a2, 40
     0x17248 li    a1, 0
     0x1724c jal   memset
     0x17250 ld    a2, 96(s0)      s->notify = notice (call_notify)
     0x17254 ld    a0, 104(s0)     s->notify_ctx
     0x17258 addi  a1, sp, 16
     0x1725c jalr  a2              :218
     0x17260 lw    a0, 112(s0)
     0x17264 addiw a0, a0, -1
     0x17268 bltu  s1, a0, 0x17070 :219 neither WAKING (1) nor ONLINE (2)
     0x1726c sw    zero, 168(s0)   session_lost inlined (:162-163)
     0x17270 sw    zero, 212(s0)
     0x17274 li    a2, 5           DIGINET_R_FOREIGN
     0x17278 mv    a0, s0
     0x1727c li    a1, 0           DIGINET_S_IDLE
     0x17280 jal   set_state       :164
     0x17284 j     0x17070 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c diginet_announce_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC
  notice_c set_state_c maybe_online_c on_announce_model on_announce_lib on_announce_tail.
Import ListNotations.
Open Scope Z_scope.

Lemma oa_e1 : memset_contract -> notice_contract -> set_state_contract -> maybe_online_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo : Z) (B' : list byte) (TF : option tframe) (now off fp buf : Z) (b : list byte)
    (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B2 : list byte) (c0 cx cn1 cn2 : list cell) (jf1 jf2 aj : list byte),
  bv_unsigned sp mod 16 = 0 -> lo + 1056 <= bv_unsigned sp -> W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 1056 ->
  tframe_at m0 sp 1056 TF -> relro_img m0 ->
  munch [(bv_unsigned sp - 1056, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -304) ->
  rw_cells rsegs m (bv_unsigned sp + -304) c0 -> cells_size c0 = 8%nat ->
  rw_cells rsegs m (bv_unsigned sp + -296) cx -> cells_size cx = 8%nat ->
  rw_cells rsegs m (bv_unsigned sp + -288) [CB 32 jf1] ->
  rw_cells rsegs m (bv_unsigned sp + -256) [CB 40 jf2] ->
  rw_cells rsegs m (bv_unsigned sp + -216) cn1 -> cells_size cn1 = 44%nat ->
  rw_cells rsegs m (bv_unsigned sp + -172) cn2 -> cells_size cn2 = 28%nat ->
  rw_cells rsegs m (bv_unsigned sp + -144) (ann_cells (buf + 30) (fr_body b) aj) -> length aj = 40%nat ->
  rw_cells rsegs m (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B2 -> g_fail_next B2 <= 1 ->
  x21 = Z_to_bv 64 off -> -1 <= off <= 9 ->
  fr_cmd b <> DIGINET_CMD_ANNOUNCE ->
  oa_after_m timg_ubsan TF B2 b off now = Some (B', tt) ->
  evt rsegs (oa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp t0 t1 t2
             (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) x9 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 fp) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171fc) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET NOTICE SETST MAYBE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' TF now off fp buf b
    x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m B2
    c0 cx cn1 cn2 jf1 jf2 aj SP16 LO WOS TFA RR MU WMO MI ST F0 S0 Fx Sx Ff1 Ff2 Fn1 Sn1 Fn2 Sn2 Fa La FRs
    WM GF -> Hoff CMD HM.
  unfold notice_contract, notice_ENTRY, notice_FRAME in NOTICE.
  unfold set_state_contract, set_state_ENTRY, set_state_FRAME in SETST.
  unfold maybe_online_contract, maybe_online_ENTRY, maybe_online_FRAME in MAYBE.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -304)) = bv_unsigned sp + -304) by (apply unsigned_lit; lia).
  pose proof (wm_len _ _ _ _ WM) as LB2.
  unfold oa_after_m in HM.
  replace (fr_cmd b =? DIGINET_CMD_ANNOUNCE) with false in HM by (symmetry; apply Z.eqb_neq; exact CMD).
  cbv beta iota zeta in HM.
  (* bltz s5 *)
  step. rewrite oa_ltz by lia.
  destruct (Z.ltb_spec off 0) as [EO|EO]; cbv iota.
  2:{ (* off >= 0: :211-214 *)
    replace (0 <=? off) with true in HM by (symmetry; apply Z.leb_le; exact EO). cbv iota in HM.
    set (B3 := set_S_e1_named_us (set_S_foreign B2 0) 1) in HM.
    assert (GB3 : g_fail_next B3 = g_fail_next B2)
      by (unfold B3, set_S_e1_named_us, set_S_foreign; rewrite !gfn_upd by wside; reflexivity).
    (* li a0, 1; slli a0, a0, 32; sd a0, 136(s0) *)
    step. step. step.
    lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
      replace X with B3 in H; [rename H into WM3 |] end.
    2:{ unfold B3. rewrite foreign_e1_store by exact LB2. unfold A_S_foreign. reflexivity. }
    (* mv a0, s0; jal maybe_online *)
    step. step.
    eapply evt_cut.
    { eapply MAYBE.
      - reflexivity.
      - exact WM3.
      - rewrite GB3. exact GF.
      - exact HM.
      - eapply tframe_at_move; [exact TFA | exact MU | rewrite Hsp; lia | rewrite Hsp; lia].
      - eapply relro_img_move; [exact RR | exact MU | exact WOS].
      - rewrite Hsp. Z.div_mod_to_equations. lia.
      - rewrite Hsp. exact ST.
      - rewrite Hsp. lia.
      - unfold w_off_stack. rewrite Hsp. lia.
      - exact MI. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & ST2 & WM4 & GF4).
    subst ms'. rewrite Hsp in MUc, ST2. clear WM3.
    lazymatch type of MUc with munch _ ?mm m2 => transport_after_call rsegs mm m2 MUc WMc end.
    clear MUc WMc MI.
    rewrite (ret_pc_even 0x17214) by (first [lia | reflexivity]).
    (* j 0x17070 *)
    step.
    eapply oa_epi; try eassumption. oa_low_pack. }
  (* off < 0: the FOREIGN notice (:216-218) *)
  replace (0 <=? off) with false in HM by (symmetry; apply Z.leb_gt; exact EO). cbv iota in HM.
  set (B3 := set_S_foreign B2 1) in HM.
  assert (LB3 : length B3 = Z.to_nat W_LEN) by (unfold B3, set_S_foreign; wlen).
  assert (SB3 : S_state B3 = S_state B2) by (unfold B3, S_state, set_S_foreign; apply s32_upd_W; wside).
  assert (NB3 : S_notify B3 = S_notify B2) by (unfold B3, S_notify, set_S_foreign; apply u_upd_W; wside).
  assert (GB3 : g_fail_next B3 = g_fail_next B2) by (unfold B3, set_S_foreign; apply gfn_upd; wside).
  unfold call_notify in HM.
  destruct (S_notify B3 =? ti_notice timg_ubsan) eqn:EN; [|discriminate HM].
  apply Z.eqb_eq in EN. change (ti_notice timg_ubsan) with 0x14bc8 in EN.
  change (S_notify B3) with (u_at B3 1744 8) in EN.
  destruct (notice_m timg_ubsan TF B3 (Ntc DIGINET_N_FOREIGN (S_state B3) 0 0 0 0 0 0 (Some (oa_ann b)) [] 0))
    as [[B4 []]|] eqn:HN; [|discriminate HM].
  cbv beta iota in HM.
  pose proof (s32_range B2 A_S_state) as RS. change (s32_at B2 A_S_state) with (S_state B2) in RS.
  pose proof (ann_cells_ann m (bv_unsigned sp + -144) (buf + 30) (fr_body b) aj La Fa) as (AV & AN).
  (* li s1, 1; lw a0, 112(s0); addi a1, sp, 160; sd a1, 40(sp); li a1, 6 *)
  do 5 step.
  (* sw s1, 136(s0): s->foreign = 1 *)
  step.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
    replace X with B3 in H; [rename H into WM3 |] end.
  2:{ unfold B3, set_S_foreign, A_S_foreign. rewrite ?le4_put. reflexivity. }
  (* sw a1, 16(sp); sw a0, 20(sp); sd zero, 24(sp); sd s2, 32(sp) *)
  do 4 step.
  (* addi a0, sp, 48; li a2, 40; li a1, 0; jal memset *)
  do 4 step.
  assert (Um256 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply MEMSET; [ | exact MI ].
    rewrite Um256. change (Z.to_nat (bv_unsigned (Z_to_bv 64 40))) with 40%nat. exact Ff2. }
  intros ms' PO. unfold memset_post in PO. destruct_exs PO. destruct PO as (E & MUc & WMc & MIc & DST). subst ms'.
  rewrite Um256 in MUc, DST. change (bv_unsigned (Z_to_bv 64 40)) with 40 in MUc, DST.
  change (Z.to_nat 40) with 40%nat in DST.
  replace (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in DST by reflexivity.
  lazymatch type of MUc with munch _ ?mm ?m2 => transport_after_call rsegs mm m2 MUc WMc end.
  clear MUc WMc MI. rename MIc into MI. rename DST into Ff2.
  rewrite (ret_pc_even 0x17250) by (first [lia | reflexivity]).
  (* ld a2, 96(s0): s->notify; ld a0, 104(s0); addi a1, sp, 16; jalr a2 *)
  step. rewrite EN.
  step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mN end.
  assert (BNF : bytes_at rsegs mN (bv_unsigned sp + -288) (foreign_nb (S_state B3) fp (bv_unsigned sp + -144))).
  { pose proof (rw_cells_bytes _ _ _ Ff1) as BF1. pose proof (rw_cells_bytes _ _ _ Ff2) as BF2.
    cbn [cells_bytes cbytes] in BF1, BF2. rewrite ?app_nil_r in BF1, BF2. rewrite ?le4_put, ?le8_put in BF1.
    replace (foreign_nb (S_state B3) fp (bv_unsigned sp + -144))
      with ((put 4 6 ++ put 4 (S_state B3) ++ put 8 0 ++ put 8 fp ++ put 8 (bv_unsigned sp + -144))
            ++ repeat (Z_to_bv 8 0) 40) by (unfold foreign_nb; rewrite <- !app_assoc; reflexivity).
    apply (proj2 (bytes_at_app rsegs _ _ _ _)). split.
    - rewrite SB3. exact BF1.
    - rewrite !length_app, !length_put.
      match goal with |- bytes_at _ _ ?A _ => replace A with (bv_unsigned sp + -256) by lia end. exact BF2. }
  assert (Um288 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -288)) = bv_unsigned sp + -288) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply (NOTICE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mN lo B3 B4
              (bv_unsigned sp + -288) (Ntc DIGINET_N_FOREIGN (S_state B3) 0 0 0 0 0 0 (Some (oa_ann b)) [] 0) TF).
    - reflexivity.
    - apply (ntc_foreign_at mN _ _ _ _ fp (bv_unsigned sp + -144)); try exact BNF; try exact AV; try exact AN;
        unfold off_world, off_window; rewrite ?Hsp; try lia.
    - eapply tframe_at_move; [exact TFA | exact MU | rewrite Hsp; lia | rewrite Hsp; lia].
    - eapply relro_img_move; [exact RR | exact MU | exact WOS].
    - exact WM3.
    - exact HN.
    - rewrite Hsp. Z.div_mod_to_equations. lia.
    - rewrite Hsp. exact ST.
    - rewrite Hsp. lia.
    - unfold w_off_stack. rewrite Hsp. lia.
    - exact MI. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & Eq & MUc & WMc & MI3 & ST3 & WM4).
  subst ms'. rewrite Hsp in MUc, ST3. clear WM3.
  lazymatch type of MUc with munch _ ?mm m3 => transport_after_call rsegs mm m3 MUc WMc end.
  clear MUc WMc MI.
  assert (GB4 : g_fail_next B4 = g_fail_next B3)
    by exact (notice_foreign_fail_next timg_ubsan TF B3
             (Ntc DIGINET_N_FOREIGN (S_state B3) 0 0 0 0 0 0 (Some (oa_ann b)) [] 0) B4 LB3 eq_refl HN).
  rewrite (ret_pc_even 0x17260) by (first [lia | reflexivity]).
  (* lw a0, 112(s0); addiw a0, a0, -1; bltu s1, a0 *)
  step. step. step.
  pose proof (s32_range B4 A_S_state) as RS4. change (s32_at B4 A_S_state) with (S_state B4) in RS4.
  change (s32_at B4 1760) with (S_state B4).
  rewrite oa_state_test by exact RS4.
  change DIGINET_S_ONLINE with 2 in HM. change DIGINET_S_WAKING with 1 in HM.
  destruct ((S_state B4 =? 2) || (S_state B4 =? 1)) eqn:EW; cbn [negb]; cbv iota in HM.
  2:{ (* neither WAKING nor ONLINE: the epilogue *)
    injection HM as <-. eapply oa_epi; try eassumption.
    - oa_low_pack.
    - rewrite GB4, GB3. exact GF. }
  (* WAKING or ONLINE: session_lost (:219-220) *)
  unfold session_lost_m in HM. cbv zeta in HM.
  pose proof (wm_len _ _ _ _ WM4) as LB4.
  set (B5 := set_S_desk_counter_valid (set_S_inflight B4 0) 0) in HM.
  assert (GB5 : g_fail_next B5 = g_fail_next B4)
    by (unfold B5, set_S_desk_counter_valid, set_S_inflight; rewrite !gfn_upd by wside; reflexivity).
  (* sw zero, 168(s0); sw zero, 212(s0) *)
  step. step.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
    replace X with B5 in H; [rename H into WM5 |] end.
  2:{ unfold B5, set_S_desk_counter_valid, set_S_inflight, A_S_desk_counter_valid, A_S_inflight.
      rewrite ?le4_put. apply upd_comm_W; wside. }
  (* li a2, 5; mv a0, s0; li a1, 0; jal set_state *)
  do 4 step.
  eapply evt_cut.
  { eapply SETST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - exact WM5.
    - rewrite GB5, GB4, GB3. exact GF.
    - exact HM.
    - eapply tframe_at_move; [exact TFA | exact MU | rewrite Hsp; lia | rewrite Hsp; lia].
    - eapply relro_img_move; [exact RR | exact MU | exact WOS].
    - rewrite Hsp. Z.div_mod_to_equations. lia.
    - rewrite Hsp. exact ST3.
    - rewrite Hsp. lia.
    - unfold w_off_stack. rewrite Hsp. lia.
    - exact MI3. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & Eq & MUc & WMc & MI4 & ST4 & WM6 & GF6).
  subst ms'. rewrite Hsp in MUc, ST4. clear WM5.
  lazymatch type of MUc with munch _ ?mm m4 => transport_after_call rsegs mm m4 MUc WMc end.
  clear MUc WMc MI3.
  rewrite (ret_pc_even 0x17284) by (first [lia | reflexivity]).
  (* j 0x17070 *)
  step.
  eapply oa_epi; try eassumption. oa_low_pack.
Qed.
