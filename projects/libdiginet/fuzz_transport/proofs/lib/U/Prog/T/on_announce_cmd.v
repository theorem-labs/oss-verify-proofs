(* Segment of the ubsan walk of on_announce (on_announce.v): find_mac's setup (diginet_session.c:194). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c bcmp_c diginet_announce_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC
  notice_c set_state_c maybe_online_c diginet_session_wake_c on_announce_model on_announce_lib on_announce_tail
  on_announce_desk on_announce_loop.
Import ListNotations.
Open Scope Z_scope.

(* 0x170c8-0x1710c: from the world B1 after the personality store, f->h.cmd decides find_mac (:194):
     0x170c8 andi  a0, s2, 7; bnez a0, 0x17288     the UBSan alignment check of f (trap; not taken: f mod 8 = 0)
     0x170d0 lbu   a1, 30(s2)                      f->h.cmd
     0x170d4 andi  a0, s0, 7                       the alignment check of s, tested at 0x170e4 or 0x17164
     0x170d8 li    a2, 225
     0x170dc li    s5, -1                          off
     0x170e0 bne   a1, a2, 0x1714c                 not e1: off = -1
     0x170e4 bnez  a0, 0x17288                     (trap; not taken)
     0x170e8 ld    s7, 192(sp)                     a.unknown_len (15)
     0x170ec li    s8, 6
     0x170f0 li    s6, 1
     0x170f4 bltu  s7, s8, 0x1715c                 not taken: 15 >= 6
     0x170f8 sd    s1, 8(sp)                       now
     0x170fc li    s9, 0                           i
     0x17100 ld    s1, 184(sp)                     a.unknown = f->body = buf + 30
     0x17104 snez  s11, s1
     0x17108 mv    s4, s1
     0x1710c mv    s10, s1                         the loop at 0x17110 (oa_loop)
     0x1714c seqz  s6, a0                          s6 = 1: s is aligned
     0x17150 j     0x1715c                         the DESK notice (on_announce_desk.v) *)
Lemma oa_cmd : bcmp_contract -> memset_contract -> notice_contract -> set_state_contract ->
  diginet_session_wake_contract -> maybe_online_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo : Z) (B' : list byte) (TF : option tframe) (now pv fp buf : Z)
    (b fj : list byte)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B1 : list byte) (jx jf1 jf2 jn1 jn2 j0 aj : list byte),
  bv_unsigned sp mod 16 = 0 -> lo + 1056 <= bv_unsigned sp -> W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 1056 ->
  0 <= now < 2 ^ 64 -> tframe_at m0 sp 1056 TF -> relro_img m0 ->
  munch [(bv_unsigned sp - 1056, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -304) ->
  rw_cells rsegs m (bv_unsigned sp + -304) [CB 8 j0] ->
  rw_cells rsegs m (bv_unsigned sp + -296) [CB 8 jx] ->
  rw_cells rsegs m (bv_unsigned sp + -288) [CB 32 jf1] ->
  rw_cells rsegs m (bv_unsigned sp + -256) [CB 40 jf2] ->
  rw_cells rsegs m (bv_unsigned sp + -216) [CB 44 jn1] ->
  rw_cells rsegs m (bv_unsigned sp + -172) [CB 28 jn2] ->
  rw_cells rsegs m (bv_unsigned sp + -144) (ann_cells (buf + 30) (fr_body b) aj) -> length aj = 40%nat ->
  rw_cells rsegs m (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m fp (dframe_cells buf b fj) -> arg_blk sp 1056 fp 64 -> fp mod 8 = 0 ->
  bytes_at rsegs m (buf + 30) (ann_unknown (fr_body b)) -> length (ann_unknown (fr_body b)) = 15%nat ->
  arg_blk sp 1056 (buf + 30) 15 ->
  wmem rsegs m B1 -> g_fail_next B1 <= 1 ->
  x19 = Z_to_bv 64 pv -> 0 <= pv < 2 ^ 63 ->
  oa_desk_m timg_ubsan TF B1 b pv (oa_off B1 b) now = Some (B', tt) ->
  evt rsegs (oa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp t0 t1 t2
             (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 now) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 fp) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x170c8) fc None m (seg_rom rsegs)).
Proof.
  intros BCMP MEMSET NOTICE SETST WAKE MAYBE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' TF
    now pv fp buf b fj x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6
    m B1 jx jf1 jf2 jn1 jn2 j0 aj SP16 LO WOS Hnow TFA RR MU WMO MI ST F0 Fx Ff1 Ff2 Fn1 Fn2 Fa La FRs
    FCELLS ABf FP8 BODY LBODY ABu WM GF -> Hpv HM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  pose proof ABf as ABf'. unfold arg_blk, off_world, off_window in ABf'.
  pose proof ABu as ABu'. unfold arg_blk, off_world, off_window in ABu'.
  pose proof FCELLS as FC'. unfold dframe_cells in FC'.
  pose proof Fa as Fa'. unfold ann_cells in Fa'.
  assert (CR : 0 <= fr_cmd b < 2^8) by (unfold fr_cmd; apply at8_range).
  (* andi a0, s2, 7; bnez a0 *)
  step. rewrite fp_land7 by lia. step. if_false.
  (* lbu a1, 30(s2); andi a0, s0, 7; li a2, 225; li s5, -1; bne a1, a2 *)
  step. step. rewrite gs_land7. step. step. step.
  rewrite zxb_b8 by exact CR. rewrite oa_eqbk by lia.
  unfold oa_off in HM. change DIGINET_CMD_ANNOUNCE_SESSION with 225 in HM.
  destruct (fr_cmd b =? 225) eqn:E1; cbn [negb]; try rewrite E1 in HM; cbv iota in HM.
  - (* e1: find_mac's loop *)
    unfold find_mac_m in HM. change (Z.to_nat (15 - DIGINET_MAC_LEN + 1)) with 10%nat in HM.
    (* bnez a0; ld s7, 192(sp); li s8, 6; li s6, 1; bltu s7, s8 *)
    step. if_false.
    step. step. step. step. if_false.
    (* sd s1, 8(sp); li s9, 0; ld s1, 184(sp); snez s11, s1; mv s4, s1; mv s10, s1 *)
    do 6 step.
    assert (UB : bv_unsigned (Z_to_bv 64 (buf + 30)) = buf + 30) by (apply unsigned_lit; lia).
    assert (FCf : rw_cells rsegs _ fp (dframe_cells buf b fj)) by exact FC'.
    refine (oa_loop BCMP MEMSET NOTICE SETST WAKE MAYBE 10%nat ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              F fc m0 lo B' TF now pv fp buf 0 b fj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              B1 [CB 8 j0] jf1 jf2 jn1 jn2 aj _ _ _ SP16 LO WOS Hnow TFA RR MU WMO MI ST F0 _ Fx Ff1 Ff2 Fn1 Fn2
              Fa La FRs FCf ABf BODY LBODY ABu WM GF _ _ Hpv _ _ _ _ _ _ _ _ HM).
    all: first [ lia | (rewrite UB; lia) | (apply snez_pos; lia) | oa_refl ].
  - (* not e1: seqz s6, a0; j 0x1715c; the DESK notice with off = -1 *)
    step. step.
    assert (FCf : rw_cells rsegs _ fp (dframe_cells buf b fj)) by exact FC'.
    refine (oa_desk MEMSET NOTICE SETST WAKE MAYBE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              F fc m0 lo B' TF now pv (-1) fp buf b fj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              B1 [CB 8 j0] [CB 8 jx] jf1 jf2 jn1 jn2 aj SP16 LO WOS Hnow TFA RR MU WMO MI ST F0 _ Fx _
              Ff1 Ff2 Fn1 Fn2 Fa La FRs FCf ABf WM GF _ Hpv _ _ _ HM).
    all: first [ lia | oa_refl ].
Qed.
