(* The walk of diginet_session_poll (transport/src/diginet_session.c:505-527) in the plain image, 0x174e4, 324 bytes
   (stripped pin bb20ce415827, disassembled by symbol from its unstripped twin c2d42d895415; the bytes of the
   function are the same in both). Frame: addi sp,sp,-1568; ra, s0, s1, s2 at sp+1560 .. sp+1536; buf[1514] at
   sp+22. The walk follows TModel/TPoll.v's cuts of diginet_session_poll_m: the tests of :508-509 (0x174fc-0x17514),
   now through g_s.io.now_us (io_now, :510), diginet_session_deadline (:511), the wait of :512-515 (0x17530-0x1756c,
   only passed to io_recv as its timeout, which io_recv does not read), recv through g_s.io.recv (io_recv, :516)
   and its error exit (:517-518, 0x1758c), now (:519), diginet_session_rx when recv handed over a frame (:520-521),
   diginet_session_tick (:522), and the drain loop 0x175c4-0x17608 (:524-525, by well-founded induction on
   poll_drain_m's fuel) to the return of :526 (0x1760c). *)
From Stdlib Require Import ZArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldLemmas TWorldMem TSess0 TCb
  TSess TPoll.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import io_now_c io_recv_c
  diginet_session_deadline_c diginet_session_rx_c diginet_session_tick_c diginet_session_poll_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- register values ---- *)
Lemma pl_signed : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.ltb_spec 0 (z + 1)).
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
  - replace (z mod 2^64) with (z + 2^64).
    + destruct (Z.ltb_spec (z + 2^64) (2^63)); lia.
    + symmetry. rewrite <- (Z.mod_add z 1 (2^64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma pl_sext32 : forall z, -2^31 <= z < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 0)) = Z_to_bv 64 z.
Proof.
  intros z Hz. f_equal. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma pl_now_range : forall B, 0 <= io_now_m B < 2 ^ 64.
Proof.
  intros B. unfold io_now_m, g_now. pose proof (u_at_range B OFF_g_now 8) as R.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R. exact R.
Qed.

(* ---- the heap frame and the RELRO tables, from the entry memory to a callee (WalkNotify.v's form) ---- *)
Lemma pl_tframe_move : forall m m' (sp sp' : word) K K' TF,
  tframe_at m sp K TF ->
  munch [(bv_unsigned sp - K, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  bv_unsigned sp - K <= bv_unsigned sp' - K' -> bv_unsigned sp' <= bv_unsigned sp ->
  tframe_at m' sp' K' TF.
Proof.
  intros m m' sp sp' K K' TF T MU H1 H2. destruct TF as [fr|]; [|exact I].
  unfold tframe_at in *. destruct T as (P & BA & OW & OWin). unfold off_world, off_window in *.
  refine (conj P (conj _ (conj OW _))); [| lia].
  eapply bytes_at_transport; [exact BA | exact MU |]. cbn [disjoint_from].
  refine (conj _ (conj _ I)); lia.
Qed.

Lemma pl_relro_move : forall m m' (sp : word) K, relro_img m ->
  munch [(bv_unsigned sp - K, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  W_BASE_PLAIN + W_LEN <= bv_unsigned sp - K -> relro_img m'.
Proof.
  intros m m' sp K R MU H i Hi. unfold mrd. rewrite (MU (wa (RELRO_BASE + i))); [exact (R i Hi) |].
  unfold RELRO_BASE, RELRO_LEN in *. cbn [outside]. rewrite wa_unsigned by lia.
  unfold W_BASE_PLAIN, W_LEN in *. refine (conj _ (conj _ I)); lia.
Qed.

(* io_recv's buffer (poll's buf at sp - 1546, 1514 bytes) misses the current heap frame *)
Lemma pl_sep : forall m (sp : word) TF, tframe_at m sp 3840 TF -> io_recv_sep TF (bv_unsigned sp + -1546) 1514.
Proof.
  intros m sp TF T. destruct TF as [fr|]; [|exact I]. unfold io_recv_sep, blk_sep.
  destruct T as (_ & _ & _ & OWin). unfold off_window in OWin. lia.
Qed.

(* ---- the bytes recv handed over, at the start of poll's buf ---- *)
Lemma pl_buf_bytes : forall m A n X got, rw_cells rsegs m A [CB n X] -> firstn (length got) X = got ->
  bytes_at rsegs m A got.
Proof.
  intros m A n X got [[_ Hb] _] FX. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  rewrite <- (firstn_skipn (length got) X) in Hb. apply bytes_at_app in Hb as [Hb _]. rewrite FX in Hb. exact Hb.
Qed.

Lemma pl_buf_len : forall m A n X got, rw_cells rsegs m A [CB n X] -> firstn (length got) X = got ->
  (length got <= n)%nat.
Proof.
  intros m A n X got [[[Hwf _] _] _] FX. cbn [cell_wf] in Hwf.
  assert (L : length (firstn (length got) X) = length got) by (rewrite FX; reflexivity).
  rewrite length_firstn in L. lia.
Qed.

Theorem diginet_session_poll_holds :
  io_now_contract -> io_recv_contract -> diginet_session_deadline_contract -> diginet_session_rx_contract ->
  diginet_session_tick_contract -> diginet_session_poll_contract.
Proof.
  intros NOW RECV DL RX TICK.
  unfold io_now_contract, io_now_ENTRY, io_now_FRAME in NOW.
  unfold io_recv_contract, io_recv_ENTRY, io_recv_FRAME in RECV.
  unfold diginet_session_deadline_contract, diginet_session_deadline_ENTRY, diginet_session_deadline_FRAME in DL.
  unfold diginet_session_rx_contract, diginet_session_rx_ENTRY, diginet_session_rx_FRAME in RX.
  unfold diginet_session_tick_contract, diginet_session_tick_ENTRY, diginet_session_tick_FRAME in TICK.
  unfold diginet_session_poll_contract, diginet_session_poll_ENTRY, diginet_session_poll_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo w r B B' TF HA0 HA1 Hw WM GF HM TFA TFO RR S16 ST LO WOS MI.
  subst a0 a1.
  unfold w_off_stack in WOS.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Hlo & _ & _).
  wk_facts.
  assert (EOFF : OFF_g_s = 1648) by reflexivity.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -1568)) = bv_unsigned sp + -1568)
    by (apply unsigned_lit; lia).
  assert (UG : bv_unsigned (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) = W_BASE_PLAIN + OFF_g_s)
    by (apply unsigned_lit; unfold W_BASE_PLAIN, OFF_g_s; lia).
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (munch_refl [(bv_unsigned sp - 3840, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  carve_frame 32%nat ST. rename FR into FRs.
  carve_frame 1514%nat ST. rename FR into FRb.
  carve_frame 22%nat ST. rename FR into FRp.
  (* prologue: addi sp,sp,-1568; sd ra, s0, s1, s2 *)
  do 5 step.
  (* addi s1, zero, -1; beqz a0 (:508 !s is false); mv s0, a0 *)
  step. step. if_false. step.
  lazymatch goal with
  | H : rw_cells rsegs _ (bv_unsigned sp + -32) ?cs |- _ => pose (CS := cs); rename H into FS0
  end.
  lazymatch goal with
  | H : rw_cells rsegs _ (bv_unsigned sp + -1568) ?cs |- _ => pose (CP := cs); rename H into FP0
  end.
  rename FRb into FB0.
  (* ---- the return (0x1760c): a0 = s1; ld ra, s0, s1, s2; addi sp; ret ---- *)
  assert (EXIT : forall (xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 : word)
      (mk : word -> option byte) (J : list byte),
    xs1 = Z_to_bv 64 r ->
    wmem rsegs mk B' -> g_fail_next B' <= 1 -> mem_inv rsegs mk ->
    stk rsegs mk lo (bv_unsigned sp + -1568) ->
    rw_cells rsegs mk (bv_unsigned sp + -1568) CP ->
    rw_cells rsegs mk (bv_unsigned sp + -1546) [CB (Z.to_nat 1514) J] ->
    rw_cells rsegs mk (bv_unsigned sp + -32) CS ->
    munch [(bv_unsigned sp - 3840, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m mk ->
    wmono rsegs m mk ->
    evt rsegs QQ (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -1568)) gp tp xt0 xt1 xt2 xs0 xs1
                          xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x1760c) fc None mk (seg_rom rsegs))).
  { intros xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mk J -> WMk GFk MIk STk
      FPk FBk FSk MUk WMok.
    unfold CS, CP in *.
    do 7 step.                                 (* mv a0, s1; ld ra, s0, s1, s2; addi sp; ret *)
    release_frame FPk STk (bv_unsigned sp + -1546).
    release_frame FBk STk (bv_unsigned sp + -32).
    release_frame FSk STk (bv_unsigned sp).
    apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity |].
    refine (conj MUk (conj WMok (conj MIk (conj STk (conj WMk GFk))))). }
  destruct (poll_cases _ _ _ _ _ _ HM) as [(EA & EB & Er) | (ER0 & EN0 & now & due & B1 & r1 & got & CN & DD & CR & CASES)].
  - (* :508-509: recv or now_us is NULL: return DIGINET_E_ARG *)
    change (S_io_recv B) with (u_at B 1728 8) in EA. change (S_io_now_us B) with (u_at B 1736 8) in EA.
    pose proof (u_at_range B 1728 8) as R1. pose proof (u_at_range B 1736 8) as R2.
    change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R1, R2.
    assert (U1 : bv_unsigned (Z_to_bv 64 (u_at B 1728 8)) = u_at B 1728 8) by (apply unsigned_lit; lia).
    assert (U2 : bv_unsigned (Z_to_bv 64 (u_at B 1736 8)) = u_at B 1736 8) by (apply unsigned_lit; lia).
    assert (ER1 : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1) = Z_to_bv 64 r)
      by (rewrite Er; apply bv_eq; vm_compute; reflexivity).
    step.                                      (* ld a0, 80(a0): s->io.recv *)
    destruct (Z.eqb_spec (u_at B 1728 8) 0) as [Z1 | Z1].
    + step. if_true.
      eapply EXIT; [ first [exact ER1 | rewrite <- Er; apply bv_eq; vm_compute; reflexivity]
                   | rewrite EB; exact WM | rewrite EB; exact GF | exact MI | exact ST | exact FP0 | exact FB0
                   | exact FS0
                   | exact MU | exact WMo ].
    + destruct EA as [EA | EA]; [contradiction |].
      step. if_false.
      step. step.                              (* mv s2, a1; ld a1, 88(s0): s->io.now_us *)
      step. if_true.
      eapply EXIT; [ first [exact ER1 | rewrite <- Er; apply bv_eq; vm_compute; reflexivity]
                   | rewrite EB; exact WM | rewrite EB; exact GF | exact MI | exact ST | exact FP0 | exact FB0
                   | exact FS0
                   | exact MU | exact WMo ].
  - destruct (call_now_inv _ _ _ CN) as (ENW & Enow). subst now.
    destruct (call_recv_inv _ _ _ _ _ _ _ CR) as (ERV & HR).
    (* ---- the drain loop (0x175c4): recv; blez a0 -> return; now; rx; j 0x175c4 ---- *)
    assert (LOOP : forall (fuel : nat)
        (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 : word)
        (mk : word -> option byte) (Bk J : list byte),
      wmem rsegs mk Bk -> g_fail_next Bk <= 1 -> mem_inv rsegs mk ->
      stk rsegs mk lo (bv_unsigned sp + -1568) ->
      rw_cells rsegs mk (bv_unsigned sp + -1568) CP ->
      rw_cells rsegs mk (bv_unsigned sp + -1546) [CB (Z.to_nat 1514) J] ->
      rw_cells rsegs mk (bv_unsigned sp + -32) CS ->
      munch [(bv_unsigned sp - 3840, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m mk ->
      wmono rsegs m mk ->
      poll_drain_m timg_plain TF Bk fuel = Some (B', r) ->
      evt rsegs QQ (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -1568)) gp tp xt0 xt1 xt2
                            (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) xs1
                            xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                       F (Z_to_bv 64 0x175c4) fc None mk (seg_rom rsegs))).
    { intros fuel. pattern fuel. apply (well_founded_ind lt_wf). clear fuel. intros fuel IH.
      intros xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mk Bk J
        WMk GFk MIk STk FPk FBk FSk MUk WMok HD.
      unfold CS, CP in *.
      destruct (poll_drain_cases _ _ _ _ _ _ HD) as (Bq & rq & gotq & CRq & CASESq).
      destruct (call_recv_inv _ _ _ _ _ _ _ CRq) as (ERq & HRq).
      destruct (io_recv_m_ret _ _ _ DIGINET_MAX_FRAME_LEN _ _ _ ltac:(unfold DIGINET_MAX_FRAME_LEN; lia) HRq)
        as (Rq & Lq).
      step.                                    (* ld a0, 64(s0): s->io.ctx *)
      step.                                    (* ld a4, 80(s0): s->io.recv = io_recv *)
      replace (u_at Bk 1728 8) with 0x1492c by (symmetry; exact ERq).
      do 4 step.                               (* addi a1, sp, 22; li a2, 1514; li a3, 0; jalr a4 *)
      eapply evt_cut.
      { eapply (RECV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
                  (bv_unsigned sp + -1546) 1514 rq J gotq TF Bk Bq).
        - try rewrite Hsp; f_equal; lia.
        - reflexivity.
        - lia.
        - exact FBk.
        - unfold arg_blk, off_world, off_window. rewrite Hsp. lia.
        - exact (pl_sep _ _ _ TFA).
        - eapply pl_tframe_move; [exact TFA | exact MUk | rewrite Hsp; lia | rewrite Hsp; lia].
        - exact TFO.
        - exact WMk.
        - exact GFk.
        - exact HRq.
        - rewrite Hsp. Z.div_mod_to_equations. lia.
        - rewrite Hsp. exact STk.
        - rewrite Hsp. lia.
        - unfold w_off_stack. rewrite Hsp. lia.
        - exact MIk. }
      intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & X & m2 &
                  Eq & MUc & WMc & MI2 & ST2 & WM2 & GF2 & FB2 & FX).
      subst ms'. rewrite Hsp in MUc, ST2.
      transport_after_call rsegs mk m2 MUc WMc. clear MUc WMc MIk. try clear mk.
      rewrite (ret_pc_even 0x175dc) by (first [lia | reflexivity]).
      assert (SRq : bv_signed (Z_to_bv 64 rq) = rq) by (apply pl_signed; lia).
      step.                                    (* mv s1, a0 *)
      destruct CASESq as [(Hle & EBq & Erq) | (Hgt & f & nowq & B2 & r2 & Ef & CNq & RXq & HD2)].
      + (* :526: recv gave no frame: return its result *)
        step. if_true.
        subst Bq. eapply EXIT; [ rewrite Erq; reflexivity | exact WM2 | exact GF2 | exact MI2 | exact ST2
                               | exact FPk | exact FB2 | exact FSk | exact MUk | exact WMok ].
      + step. if_false.
        destruct (call_now_inv _ _ _ CNq) as (ENq & Enq). subst nowq.
        step.                                  (* ld a0, 64(s0) *)
        step.                                  (* ld a1, 88(s0): s->io.now_us = io_now *)
        replace (u_at Bq 1736 8) with 0x149d8 by (symmetry; exact ENq).
        step.                                  (* sext.w s1, s1 *)
        step.                                  (* jalr a1 *)
        eapply evt_cut.
        { eapply (NOW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo Bq).
          - exact WM2.
          - rewrite Hsp. Z.div_mod_to_equations. lia.
          - rewrite Hsp. exact ST2.
          - rewrite Hsp. lia.
          - unfold w_off_stack. rewrite Hsp. lia.
          - exact MI2. }
        intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m3 &
                    Eq & MUc & WMc & MI3 & ST3 & WM3).
        subst ms'. rewrite Hsp in MUc, ST3. clear WM2.
        transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI2. try clear m2.
        rewrite (ret_pc_even 0x175f4) by (first [lia | reflexivity]).
        do 4 step.                             (* mv a3, a0; addi a1, sp, 22; mv a0, s0; mv a2, s1 *)
        step.                                  (* jal diginet_session_rx *)
        pose proof (pl_buf_len _ _ _ _ _ FB2 FX) as LG. change (Z.to_nat 1514) with 1514%nat in LG.
        eapply evt_cut.
        { eapply (RX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
                    (bv_unsigned sp + -1546) (io_now_m Bq) r2 gotq Bq B2 TF).
          - reflexivity.
          - try rewrite Hsp; f_equal; lia.
          - rewrite (pl_sext32 rq) by lia. f_equal. symmetry. exact (Lq Hgt).
          - reflexivity.
          - exact (pl_now_range Bq).
          - exact (pl_buf_bytes _ _ _ _ _ FB2 FX).
          - unfold arg_blk, off_world, off_window. rewrite Hsp. lia.
          - exact WM3.
          - exact GF2.
          - exact RXq.
          - eapply pl_tframe_move; [exact TFA | exact MUk | rewrite Hsp; lia | rewrite Hsp; lia].
          - eapply pl_relro_move; [exact RR | exact MUk | lia].
          - rewrite Hsp. Z.div_mod_to_equations. lia.
          - rewrite Hsp. exact ST3.
          - rewrite Hsp. lia.
          - unfold w_off_stack. rewrite Hsp. lia.
          - exact MI3. }
        intros ms' (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m4 &
                    Eq & MUc & WMc & MI4 & ST4 & WM4 & GF4).
        subst ms'. rewrite Hsp in MUc, ST4.
        transport_after_call rsegs m3 m4 MUc WMc. clear MUc WMc MI3. try clear m3.
        rewrite (ret_pc_even 0x17608) by (first [lia | reflexivity]).
        step.                                  (* j 0x175c4 *)
        eapply (IH f ltac:(lia)); [ exact WM4 | exact GF4 | exact MI4 | exact ST4 | exact FPk | exact FB2
                                  | exact FSk | exact MUk | exact WMok | exact HD2 ]. }
    (* ---- :522 tick (0x175b8): mv a0, s0; mv a1, s2; jal diginet_session_tick; then the loop ---- *)
    assert (TK : forall (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word)
        (mk : word -> option byte) (Bk J B3 : list byte) (nw r3 : Z),
      0 <= nw < 2 ^ 64 ->
      wmem rsegs mk Bk -> g_fail_next Bk <= 1 -> mem_inv rsegs mk ->
      stk rsegs mk lo (bv_unsigned sp + -1568) ->
      rw_cells rsegs mk (bv_unsigned sp + -1568) CP ->
      rw_cells rsegs mk (bv_unsigned sp + -1546) [CB (Z.to_nat 1514) J] ->
      rw_cells rsegs mk (bv_unsigned sp + -32) CS ->
      munch [(bv_unsigned sp - 3840, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m mk ->
      wmono rsegs m mk ->
      diginet_session_tick_m timg_plain TF Bk nw = Some (B3, r3) ->
      poll_drain_m timg_plain TF B3 (Z.to_nat (g_rx_times B3)) = Some (B', r) ->
      evt rsegs QQ (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -1568)) gp tp xt0 xt1 xt2
                            (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) xs1
                            xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 nw) s3 s4 s5 s6 s7 s8 s9 s10 s11
                            xt3 xt4 xt5 xt6)
                       F (Z_to_bv 64 0x175b8) fc None mk (seg_rom rsegs))).
    { intros xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mk Bk J B3 nw r3 Hnw
        WMk GFk MIk STk FPk FBk FSk MUk WMok HT HD.
      unfold CS, CP in *.
      do 3 step.                               (* mv a0, s0; mv a1, s2; jal diginet_session_tick *)
      eapply evt_cut.
      { eapply (TICK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo nw r3 Bk B3 TF).
        - reflexivity.
        - reflexivity.
        - exact Hnw.
        - exact WMk.
        - exact GFk.
        - exact HT.
        - eapply pl_tframe_move; [exact TFA | exact MUk | rewrite Hsp; lia | rewrite Hsp; lia].
        - eapply pl_relro_move; [exact RR | exact MUk | lia].
        - rewrite Hsp. Z.div_mod_to_equations. lia.
        - rewrite Hsp. exact STk.
        - rewrite Hsp. lia.
        - unfold w_off_stack. rewrite Hsp. lia.
        - exact MIk. }
      intros ms' (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m4 &
                  Eq & MUc & WMc & MI4 & ST4 & WM4 & GF4).
      subst ms'. rewrite Hsp in MUc, ST4.
      transport_after_call rsegs mk m4 MUc WMc. clear MUc WMc MIk. try clear mk.
      rewrite (ret_pc_even 0x175c4) by (first [lia | reflexivity]).
      eapply (LOOP (Z.to_nat (g_rx_times B3))); [ exact WM4 | exact GF4 | exact MI4 | exact ST4 | exact FPk
                                                | exact FBk | exact FSk | exact MUk | exact WMok | exact HD ]. }
    (* ---- the first recv (0x17570, :516) and what follows it, for any value of the wait (a3) ---- *)
    assert (JOIN : forall (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 : word)
        (mk : word -> option byte) (J : list byte),
      wmem rsegs mk B -> mem_inv rsegs mk ->
      stk rsegs mk lo (bv_unsigned sp + -1568) ->
      rw_cells rsegs mk (bv_unsigned sp + -1568) CP ->
      rw_cells rsegs mk (bv_unsigned sp + -1546) [CB (Z.to_nat 1514) J] ->
      rw_cells rsegs mk (bv_unsigned sp + -32) CS ->
      munch [(bv_unsigned sp - 3840, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m mk ->
      wmono rsegs m mk ->
      evt rsegs QQ (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -1568)) gp tp xt0 xt1 xt2
                            (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) xs1
                            xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                       F (Z_to_bv 64 0x17570) fc None mk (seg_rom rsegs))).
    { intros xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mk J
        WMk MIk STk FPk FBk FSk MUk WMok.
      unfold CS, CP in *.
      destruct (io_recv_m_ret _ _ _ DIGINET_MAX_FRAME_LEN _ _ _ ltac:(unfold DIGINET_MAX_FRAME_LEN; lia) HR)
        as (R1 & L1).
      step.                                    (* ld a0, 64(s0): s->io.ctx *)
      step.                                    (* ld a4, 80(s0): s->io.recv = io_recv *)
      replace (u_at B 1728 8) with 0x1492c by (symmetry; exact ERV).
      do 4 step.                               (* sext.w a3, a3; addi a1, sp, 22; li a2, 1514; jalr a4 *)
      eapply evt_cut.
      { eapply (RECV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
                  (bv_unsigned sp + -1546) 1514 r1 J got TF B B1).
        - try rewrite Hsp; f_equal; lia.
        - reflexivity.
        - lia.
        - exact FBk.
        - unfold arg_blk, off_world, off_window. rewrite Hsp. lia.
        - exact (pl_sep _ _ _ TFA).
        - eapply pl_tframe_move; [exact TFA | exact MUk | rewrite Hsp; lia | rewrite Hsp; lia].
        - exact TFO.
        - exact WMk.
        - exact GF.
        - exact HR.
        - rewrite Hsp. Z.div_mod_to_equations. lia.
        - rewrite Hsp. exact STk.
        - rewrite Hsp. lia.
        - unfold w_off_stack. rewrite Hsp. lia.
        - exact MIk. }
      intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & X & m2 &
                  Eq & MUc & WMc & MI2 & ST2 & WM2 & GF2 & FB2 & FX).
      subst ms'. rewrite Hsp in MUc, ST2.
      transport_after_call rsegs mk m2 MUc WMc. clear MUc WMc MIk. try clear mk.
      rewrite (ret_pc_even 0x17588) by (first [lia | reflexivity]).
      assert (SR1 : bv_signed (Z_to_bv 64 r1) = r1) by (apply pl_signed; lia).
      step.                                    (* mv s1, a0 *)
      destruct CASES as [(Hlt & EB1 & Er1) | (Hge & now2 & B2 & B3 & r3 & CN2 & RXC & HT & HD)].
      - (* :517-518: recv failed: return its error *)
        step. if_true.
        subst B1. eapply EXIT; [ rewrite Er1; reflexivity | exact WM2 | exact GF2 | exact MI2 | exact ST2
                               | exact FPk | exact FB2 | exact FSk | exact MUk | exact WMok ].
      - step. if_false.
        destruct (call_now_inv _ _ _ CN2) as (EN2 & En2). subst now2.
        step.                                  (* ld a0, 64(s0) *)
        step.                                  (* ld a1, 88(s0): s->io.now_us = io_now *)
        replace (u_at B1 1736 8) with 0x149d8 by (symmetry; exact EN2).
        step.                                  (* jalr a1 *)
        eapply evt_cut.
        { eapply (NOW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo B1).
          - exact WM2.
          - rewrite Hsp. Z.div_mod_to_equations. lia.
          - rewrite Hsp. exact ST2.
          - rewrite Hsp. lia.
          - unfold w_off_stack. rewrite Hsp. lia.
          - exact MI2. }
        intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m3 &
                    Eq & MUc & WMc & MI3 & ST3 & WM3).
        subst ms'. rewrite Hsp in MUc, ST3. clear WM2.
        transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI2. try clear m2.
        rewrite (ret_pc_even 0x1759c) by (first [lia | reflexivity]).
        assert (UR1 : bv_unsigned (Z_to_bv 64 r1) = r1) by (apply unsigned_lit; lia).
        step.                                  (* mv s2, a0 *)
        destruct RXC as [(Z1 & EB2) | (P1 & r2 & RXm)].
        + (* :520: no frame: no rx *)
          step. if_true.
          subst B2. eapply (TK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 B1 X B3 (io_now_m B1) r3);
            [ exact (pl_now_range B1) | exact WM3 | exact GF2 | exact MI3 | exact ST3 | exact FPk | exact FB2
            | exact FSk | exact MUk | exact WMok | exact HT | exact HD ].
        + (* :521: rx (s, buf, r, now) *)
          step. if_false.
          do 4 step.                           (* addi a1, sp, 22; mv a0, s0; mv a2, s1; mv a3, s2 *)
          step.                                (* jal diginet_session_rx *)
          pose proof (pl_buf_len _ _ _ _ _ FB2 FX) as LG. change (Z.to_nat 1514) with 1514%nat in LG.
          eapply evt_cut.
          { eapply (RX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
                      (bv_unsigned sp + -1546) (io_now_m B1) r2 got B1 B2 TF).
            - reflexivity.
            - try rewrite Hsp; f_equal; lia.
            - f_equal. symmetry. exact (L1 P1).
            - reflexivity.
            - exact (pl_now_range B1).
            - exact (pl_buf_bytes _ _ _ _ _ FB2 FX).
            - unfold arg_blk, off_world, off_window. rewrite Hsp. lia.
            - exact WM3.
            - exact GF2.
            - exact RXm.
            - eapply pl_tframe_move; [exact TFA | exact MUk | rewrite Hsp; lia | rewrite Hsp; lia].
            - eapply pl_relro_move; [exact RR | exact MUk | lia].
            - rewrite Hsp. Z.div_mod_to_equations. lia.
            - rewrite Hsp. exact ST3.
            - rewrite Hsp. lia.
            - unfold w_off_stack. rewrite Hsp. lia.
            - exact MI3. }
          intros ms' (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m4 &
                      Eq & MUc & WMc & MI4 & ST4 & WM4 & GF4).
          subst ms'. rewrite Hsp in MUc, ST4.
          transport_after_call rsegs m3 m4 MUc WMc. clear MUc WMc MI3. try clear m3.
          rewrite (ret_pc_even 0x175b8) by (first [lia | reflexivity]).
          eapply (TK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 B2 X B3 (io_now_m B1) r3);
            [ exact (pl_now_range B1) | exact WM4 | exact GF4 | exact MI4 | exact ST4 | exact FPk | exact FB2
            | exact FSk | exact MUk | exact WMok | exact HT | exact HD ]. }
    (* ---- :509-515 from 0x17504: the two pointer tests, now, the deadline and the wait ---- *)
    change (S_io_recv B) with (u_at B 1728 8) in ER0, ERV.
    change (S_io_now_us B) with (u_at B 1736 8) in EN0, ENW.
    step.                                      (* ld a0, 80(a0): s->io.recv *)
    replace (u_at B 1728 8) with 0x1492c by (symmetry; exact ERV).
    step. if_false.
    step. step.                                (* mv s2, a1; ld a1, 88(s0): s->io.now_us = io_now *)
    replace (u_at B 1736 8) with 0x149d8 by (symmetry; exact ENW).
    step. if_false.
    step.                                      (* ld a0, 64(s0) *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE end.
    step.                                      (* jalr a1 *)
    eapply evt_cut.
    { eapply (NOW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo B).
      - exact WM.
      - rewrite Hsp. Z.div_mod_to_equations. lia.
      - rewrite Hsp. exact ST.
      - rewrite Hsp. lia.
      - unfold w_off_stack. rewrite Hsp. lia.
      - exact MI. }
    intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m3 &
                Eq & MUc & WMc & MI3 & ST3 & WM3).
    subst ms'. rewrite Hsp in MUc, ST3. clear WM.
    transport_after_call rsegs mE m3 MUc WMc. clear MUc WMc MI. try clear mE.
    rewrite (ret_pc_even 0x17520) by (first [lia | reflexivity]).
    do 4 step.                                 (* mv s1, a0; mv a0, s0; mv a1, s1; jal diginet_session_deadline *)
    eapply evt_cut.
    { eapply (DL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (io_now_m B) due B).
      - reflexivity.
      - reflexivity.
      - exact (pl_now_range B).
      - exact WM3.
      - exact DD.
      - rewrite Hsp. Z.div_mod_to_equations. lia.
      - rewrite Hsp. exact ST3.
      - rewrite Hsp. lia.
      - unfold w_off_stack. rewrite Hsp. lia.
      - exact MI3. }
    intros ms' (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m4 &
                Eq & MUc & WMc & MI4 & ST4 & WM4).
    subst ms'. rewrite Hsp in MUc, ST4. clear WM3.
    transport_after_call rsegs m3 m4 MUc WMc. clear MUc WMc MI3. try clear m3.
    rewrite (ret_pc_even 0x17530) by (first [lia | reflexivity]).
    (* :512-515: sub, the clamp to 0, (wait_us + 999) / 1000, the max_wait_ms clamp *)
    do 12 step.
    step.                                      (* blt s2, a1 *)
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end;
      [ cbv iota | cbv iota; step ].
    all: step.                                 (* bltz s2 *)
    all: lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end;
      [ cbv iota | cbv iota; step ].
    all: eapply JOIN; [ exact WM4 | exact MI4 | exact ST4 | exact FP0 | exact FB0 | exact FS0 | exact MU
                      | exact WMo ].
Qed.
