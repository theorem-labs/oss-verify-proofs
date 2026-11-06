(* Segment of the ubsan walk of on_announce (on_announce.v): the DESK notice (diginet_session.c:196-198), from
   0x1715c; s3 holds the personality pointer pv, s5 find_mac's off, s6 the UBSan check of :197 (1 = s aligned):
     0x1715c li    a0, 1           DIGINET_N_DESK
     0x17160 sw    a0, 88(sp)      n.kind (n at sp + 88)
     0x17164 beqz  s6, 0x17288     the trap (unimp); not taken: s6 = 1
     0x17168 lw    a0, 112(s0)     s->state
     0x1716c addi  a1, sp, 160     &a
     0x17170 sd    s3, 120(sp)     n.personality
     0x17174 sw    s5, 128(sp)     n.mac_offset
     0x17178 sw    a0, 92(sp)      n.state
     0x1717c sd    zero, 96(sp)    n.old_state, n.reason
     0x17180 sd    s2, 104(sp)     n.frame
     0x17184 sd    a1, 112(sp)     n.announce
     0x17188 addi  a0, sp, 132     the rest of n: memset (&n + 44, 0, 28)
     0x1718c li    a2, 28
     0x17190 li    a1, 0
     0x17194 jal   memset
     0x17198 ld    a2, 96(s0)      s->notify = notice (call_notify)
     0x1719c ld    a0, 104(s0)     s->notify_ctx
     0x171a0 addi  a1, sp, 88
     0x171a4 jalr  a2              :198
     0x171a8 lbu   a0, 30(s2)      f->h.cmd
     0x171ac li    a1, 224
     0x171b0 bne   a0, a1, 0x171fc :200; e0: on_announce_e0.v, else on_announce_e1.v *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c diginet_announce_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC
  notice_c set_state_c maybe_online_c diginet_session_wake_c on_announce_model on_announce_lib on_announce_tail
  on_announce_e0 on_announce_e1.
Import ListNotations.
Open Scope Z_scope.

Lemma oa_desk : memset_contract -> notice_contract -> set_state_contract -> diginet_session_wake_contract ->
  maybe_online_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo : Z) (B' : list byte) (TF : option tframe) (now pv off fp buf : Z)
    (b fj : list byte)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B1 : list byte) (c0 cx : list cell) (jf1 jf2 jn1 jn2 aj : list byte),
  bv_unsigned sp mod 16 = 0 -> lo + 1056 <= bv_unsigned sp -> W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 1056 ->
  0 <= now < 2 ^ 64 -> tframe_at m0 sp 1056 TF -> relro_img m0 ->
  munch [(bv_unsigned sp - 1056, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -304) ->
  rw_cells rsegs m (bv_unsigned sp + -304) c0 -> cells_size c0 = 8%nat ->
  rw_cells rsegs m (bv_unsigned sp + -296) cx -> cells_size cx = 8%nat ->
  rw_cells rsegs m (bv_unsigned sp + -288) [CB 32 jf1] ->
  rw_cells rsegs m (bv_unsigned sp + -256) [CB 40 jf2] ->
  rw_cells rsegs m (bv_unsigned sp + -216) [CB 44 jn1] ->
  rw_cells rsegs m (bv_unsigned sp + -172) [CB 28 jn2] ->
  rw_cells rsegs m (bv_unsigned sp + -144) (ann_cells (buf + 30) (fr_body b) aj) -> length aj = 40%nat ->
  rw_cells rsegs m (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m fp (dframe_cells buf b fj) -> arg_blk sp 1056 fp 64 ->
  wmem rsegs m B1 -> g_fail_next B1 <= 1 ->
  x19 = Z_to_bv 64 pv -> 0 <= pv < 2 ^ 63 ->
  x21 = Z_to_bv 64 off -> -1 <= off <= 9 ->
  x22 = Z_to_bv 64 1 ->
  oa_desk_m timg_ubsan TF B1 b pv off now = Some (B', tt) ->
  evt rsegs (oa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp t0 t1 t2
             (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 now) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 fp) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1715c) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET NOTICE SETST WAKE MAYBE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' TF
    now pv off fp buf b fj x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6
    m B1 c0 cx jf1 jf2 jn1 jn2 aj SP16 LO WOS Hnow TFA RR MU WMO MI ST F0 S0 Fx Sx Ff1 Ff2 Fn1 Fn2 Fa La FRs
    FCELLS ABf WM GF -> Hpv -> Hoff -> HM.
  pose proof NOTICE as NOTICE0.
  unfold notice_contract, notice_ENTRY, notice_FRAME in NOTICE.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -304)) = bv_unsigned sp + -304) by (apply unsigned_lit; lia).
  pose proof (wm_len _ _ _ _ WM) as LB1.
  unfold arg_blk, off_world, off_window in ABf.
  unfold dframe_cells in FCELLS.
  pose proof (ann_cells_ann m (bv_unsigned sp + -144) (buf + 30) (fr_body b) aj La Fa) as (AV & AN).
  (* the model: the DESK notice of :196-198 through s->notify *)
  unfold oa_desk_m, call_notify in HM. cbv zeta in HM.
  destruct (S_notify B1 =? ti_notice timg_ubsan) eqn:EN; [|discriminate HM].
  apply Z.eqb_eq in EN. change (ti_notice timg_ubsan) with 0x14bc8 in EN.
  change (S_notify B1) with (u_at B1 1744 8) in EN.
  destruct (notice_m timg_ubsan TF B1 (Ntc DIGINET_N_DESK (S_state B1) 0 0 0 0 off pv (Some (oa_ann b)) [] 0))
    as [[B2 []]|] eqn:HN; [|discriminate HM].
  cbv beta iota in HM.
  pose proof (s32_range B1 A_S_state) as RS. change (s32_at B1 A_S_state) with (S_state B1) in RS.
  (* li a0, 1; sw a0, 88(sp); beqz s6 *)
  step. step. step. if_false.
  (* lw a0, 112(s0); addi a1, sp, 160; sd s3, 120(sp); sw s5, 128(sp); sw a0, 92(sp); sd zero, 96(sp);
     sd s2, 104(sp); sd a1, 112(sp) *)
  do 8 step.
  (* addi a0, sp, 132; li a2, 28; li a1, 0; jal memset *)
  do 4 step.
  assert (Um172 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -172)) = bv_unsigned sp + -172) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply MEMSET; [ | exact MI ].
    rewrite Um172. change (Z.to_nat (bv_unsigned (Z_to_bv 64 28))) with 28%nat. exact Fn2. }
  intros ms' PO. unfold memset_post in PO. destruct_exs PO. destruct PO as (E & MUc & WMc & MIc & DST). subst ms'.
  rewrite Um172 in MUc, DST. change (bv_unsigned (Z_to_bv 64 28)) with 28 in MUc, DST.
  change (Z.to_nat 28) with 28%nat in DST.
  replace (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in DST by reflexivity.
  lazymatch type of MUc with munch _ ?mm ?m2 => transport_after_call rsegs mm m2 MUc WMc end.
  clear MUc WMc MI. rename MIc into MI. rename DST into Fn2.
  rewrite (ret_pc_even 0x17198) by (first [lia | reflexivity]).
  (* ld a2, 96(s0): s->notify; ld a0, 104(s0); addi a1, sp, 88; jalr a2 *)
  step. rewrite EN.
  step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mN end.
  assert (BND : bytes_at rsegs mN (bv_unsigned sp + -216) (desk_nb (S_state B1) fp (bv_unsigned sp + -144) pv off)).
  { pose proof (rw_cells_bytes _ _ _ Fn1) as BN1. pose proof (rw_cells_bytes _ _ _ Fn2) as BN2.
    cbn [cells_bytes cbytes] in BN1, BN2. rewrite ?app_nil_r in BN1, BN2. rewrite ?le4_put, ?le8_put in BN1.
    replace (desk_nb (S_state B1) fp (bv_unsigned sp + -144) pv off)
      with ((put 4 1 ++ put 4 (S_state B1) ++ put 8 0 ++ put 8 fp ++ put 8 (bv_unsigned sp + -144) ++ put 8 pv
             ++ put 4 off) ++ repeat (Z_to_bv 8 0) 28) by (unfold desk_nb; rewrite <- !app_assoc; reflexivity).
    apply (proj2 (bytes_at_app rsegs _ _ _ _)). split.
    - exact BN1.
    - rewrite !length_app, !length_put.
      match goal with |- bytes_at _ _ ?A _ => replace A with (bv_unsigned sp + -172) by lia end. exact BN2. }
  eapply evt_cut.
  { eapply (NOTICE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mN lo B1 B2
              (bv_unsigned sp + -216) (Ntc DIGINET_N_DESK (S_state B1) 0 0 0 0 off pv (Some (oa_ann b)) [] 0) TF).
    - reflexivity.
    - apply (ntc_desk_at mN _ _ _ _ fp (bv_unsigned sp + -144)); try exact BND; try exact AV; try exact AN;
        unfold off_world, off_window; rewrite ?Hsp; try lia.
    - eapply tframe_at_move; [exact TFA | exact MU | rewrite Hsp; lia | rewrite Hsp; lia].
    - eapply relro_img_move; [exact RR | exact MU | exact WOS].
    - exact WM.
    - exact HN.
    - rewrite Hsp. Z.div_mod_to_equations. lia.
    - rewrite Hsp. exact ST.
    - rewrite Hsp. lia.
    - unfold w_off_stack. rewrite Hsp. lia.
    - exact MI. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & Eq & MUc & WMc & MI3 & ST3 & WM2).
  subst ms'. rewrite Hsp in MUc, ST3. clear WM.
  lazymatch type of MUc with munch _ ?mm m3 => transport_after_call rsegs mm m3 MUc WMc end.
  clear MUc WMc MI.
  assert (GB2 : g_fail_next B2 = g_fail_next B1)
    by exact (notice_desk_fail_next timg_ubsan TF B1
             (Ntc DIGINET_N_DESK (S_state B1) 0 0 0 0 off pv (Some (oa_ann b)) [] 0) B2 LB1 eq_refl HN).
  rewrite (ret_pc_even 0x171a8) by (first [lia | reflexivity]).
  (* lbu a0, 30(s2): f->h.cmd; li a1, 224; bne a0, a1 *)
  step. step. step.
  assert (CR : 0 <= fr_cmd b < 2^8) by (unfold fr_cmd; apply at8_range).
  rewrite zxb_b8 by exact CR. rewrite oa_eqbk by lia.
  destruct (Z.eqb_spec (fr_cmd b) 224) as [E0|E0]; cbn [negb].
  - (* e0: on_announce_e0.v *)
    eapply oa_e0; try eassumption.
    all: first [ oa_low_pack | (rewrite GB2; exact GF) | exact E0 ].
  - (* e1: on_announce_e1.v *)
    eapply oa_e1; try eassumption.
    all: first [ reflexivity | lia | (rewrite GB2; exact GF) | exact E0 ].
Qed.
