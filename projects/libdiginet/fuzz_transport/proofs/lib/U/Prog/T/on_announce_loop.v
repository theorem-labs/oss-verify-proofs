(* Segment of the ubsan walk of on_announce (on_announce.v): find_mac inlined (diginet_session.c:168-174, :194),
   the loop at 0x17110; turn i (0 .. 9) compares the 6 bytes at a.unknown + i with s->cfg.host_mac:
     0x17110 bltu  s10, s1, 0x17288   the UBSan pointer-overflow check of a.unknown + i (trap; not taken)
     0x17114 seqz  a0, s10
     0x17118 xor   a0, s11, a0        a.unknown + i is NULL exactly when a.unknown is (s11 = a.unknown != NULL)
     0x1711c beqz  a0, 0x17288        the trap; not taken
     0x17120 li    a2, 6
     0x17124 mv    a0, s4             a.unknown + i
     0x17128 mv    a1, s0             s->cfg.host_mac (offset 0 of g_s)
     0x1712c jal   bcmp
     0x17130 beqz  a0, 0x17154        found: off = i
     0x17134 addiw s9, s9, 1          i + 1
     0x17138 addi  s10, s10, 1
     0x1713c addi  s8, s8, 1          i + 1 + 6
     0x17140 addi  s4, s4, 1
     0x17144 bgeu  s7, s8, 0x17110    i + 1 + 6 <= unknown_len = 15
     0x17148 j     0x17158            not found: off = -1 (s5)
     0x17154 mv    s5, s9
     0x17158 ld    s1, 8(sp)          now, saved by the loop's setup
     0x1715c ...                      on_announce_desk.v *)
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
  on_announce_desk.
Import ListNotations.
Open Scope Z_scope.

Lemma oa_loop : bcmp_contract -> memset_contract -> notice_contract -> set_state_contract ->
  diginet_session_wake_contract -> maybe_online_contract ->
  forall (f : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo : Z) (B' : list byte) (TF : option tframe) (now pv fp buf i : Z)
    (b fj : list byte)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r1 r3 r4 r5 r6 r7 r8 r9 r10 r11 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B1 : list byte) (c0 : list cell) (jf1 jf2 jn1 jn2 aj : list byte),
  (1 <= f)%nat -> (f <= 10)%nat -> i + Z.of_nat f = 10 ->
  bv_unsigned sp mod 16 = 0 -> lo + 1056 <= bv_unsigned sp -> W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 1056 ->
  0 <= now < 2 ^ 64 -> tframe_at m0 sp 1056 TF -> relro_img m0 ->
  munch [(bv_unsigned sp - 1056, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -304) ->
  rw_cells rsegs m (bv_unsigned sp + -304) c0 -> cells_size c0 = 8%nat ->
  rw_cells rsegs m (bv_unsigned sp + -296) [C8 (Z_to_bv 64 now)] ->
  rw_cells rsegs m (bv_unsigned sp + -288) [CB 32 jf1] ->
  rw_cells rsegs m (bv_unsigned sp + -256) [CB 40 jf2] ->
  rw_cells rsegs m (bv_unsigned sp + -216) [CB 44 jn1] ->
  rw_cells rsegs m (bv_unsigned sp + -172) [CB 28 jn2] ->
  rw_cells rsegs m (bv_unsigned sp + -144) (ann_cells (buf + 30) (fr_body b) aj) -> length aj = 40%nat ->
  rw_cells rsegs m (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m fp (dframe_cells buf b fj) -> arg_blk sp 1056 fp 64 ->
  bytes_at rsegs m (buf + 30) (ann_unknown (fr_body b)) -> length (ann_unknown (fr_body b)) = 15%nat ->
  arg_blk sp 1056 (buf + 30) 15 ->
  wmem rsegs m B1 -> g_fail_next B1 <= 1 ->
  bv_unsigned r1 = buf + 30 -> r3 = Z_to_bv 64 pv -> 0 <= pv < 2 ^ 63 ->
  bv_unsigned r4 = buf + 30 + i -> r5 = Z_to_bv 64 (-1) -> r6 = Z_to_bv 64 1 -> bv_unsigned r7 = 15 ->
  bv_unsigned r8 = 6 + i -> bv_unsigned r9 = i -> bv_unsigned r10 = buf + 30 + i -> bv_unsigned r11 = 1 ->
  oa_desk_m timg_ubsan TF B1 b pv
    (find_mac_loop (ann_unknown (fr_body b)) (S_cfg_host_mac B1) i f) now = Some (B', tt) ->
  evt rsegs (oa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp t0 t1 t2
             (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) r1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 fp) r3 r4 r5 r6 r7 r8 r9 r10 r11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17110) fc None m (seg_rom rsegs)).
Proof.
  intros BCMP MEMSET NOTICE SETST WAKE MAYBE f.
  induction f as [|f IH]; intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' TF now pv fp buf i
    b fj x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r1 r3 r4 r5 r6 r7 r8 r9 r10 r11 t3 t4 t5 t6 m B1 c0 jf1 jf2 jn1 jn2 aj
    Hf Hf10 Hi SP16 LO WOS Hnow TFA RR MU WMO MI ST F0 S0 Fx Ff1 Ff2 Fn1 Fn2 Fa La FRs FCELLS ABf BODY LBODY ABu
    WM GF H1 H3 Hpv H4 H5 H6 H7 H8 H9 H10 H11 HM; [lia|].
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  pose proof ABu as ABu'. unfold arg_blk, off_world, off_window in ABu'.
  (* bltu s10, s1: a.unknown + i did not wrap *)
  step. if_false.
  (* seqz a0, s10; xor a0, s11, a0; beqz a0: a.unknown + i is not NULL *)
  step. step. step.
  rewrite (loop_nn r10 r11 H11 ltac:(lia)). if_false.
  (* li a2, 6; mv a0, s4; mv a1, s0; jal bcmp *)
  do 4 step.
  set (U := ann_unknown (fr_body b)) in HM.
  set (mac := S_cfg_host_mac B1) in HM.
  assert (LU : length U = 15%nat) by exact LBODY.
  assert (Hi0 : 0 <= i <= 9) by lia.
  set (ls := skipn (Z.to_nat i) U).
  assert (Lls : (6 <= length ls)%nat) by (unfold ls; rewrite length_skipn; lia).
  pose proof (wm_len _ _ _ _ WM) as LB1.
  assert (Lmac : length mac = 6%nat)
    by (unfold mac, S_cfg_host_mac; apply length_sub; unfold A_S_cfg_host_mac; [lia | rewrite LB1; unfold W_LEN; lia]).
  destruct (memcmp_memeq 6 ls mac Lls ltac:(lia)) as (v & MC & Vr & Veq).
  assert (LS : bytes_at rsegs m (buf + 30 + i) ls).
  { unfold ls, U.
    pose proof (bytes_at_skipn m (buf + 30) _ (Z.to_nat i) BODY ltac:(lia)) as Bi.
    replace (buf + 30 + Z.of_nat (Z.to_nat i)) with (buf + 30 + i) in Bi by lia. exact Bi. }
  assert (RS : bytes_at rsegs m (W_BASE_UBSAN + OFF_g_s) mac).
  { unfold mac, S_cfg_host_mac.
    eapply (wm_src rsegs W_BASE_UBSAN m B1 A_S_cfg_host_mac 6);
      [exact WM | unfold A_S_cfg_host_mac; lia | unfold A_S_cfg_host_mac; lia | unfold A_S_cfg_host_mac, W_LEN; lia]. }
  eapply evt_cut.
  { eapply (BCMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m ls mac v).
    - rewrite H4. exact LS.
    - rewrite unsigned_lit by lia. exact RS.
    - change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat. exact MC.
    - exact MI. }
  intros ms' PO. unfold memcmp_post in PO. destruct_exs PO. destruct PO as (E & MUc & WMc & MIc & _ & _). subst ms'.
  lazymatch type of MUc with munch _ ?mm ?m2 => transport_after_call rsegs mm m2 MUc WMc end.
  clear MUc WMc MI. rename MIc into MI.
  rewrite (ret_pc_even 0x17130) by (first [lia | reflexivity]).
  (* beqz a0: bcmp's answer *)
  step. rewrite oa_eqb0 by lia. rewrite Veq.
  cbn [find_mac_loop] in HM.
  destruct (memeq 6 ls mac) eqn:EQ; cbv iota; unfold ls in EQ; rewrite EQ in HM; cbv iota in HM.
  - (* found at i: mv s5, s9; ld s1, 8(sp); then the DESK notice with off = i *)
    step. step.
    eapply oa_desk; try eassumption.
    all: first [ reflexivity | lia | (apply word_of_unsigned; exact H9) ].
  - (* not found at i: addiw s9; addi s10; addi s8; addi s4; bgeu s7, s8 *)
    step. step. step. step. step.
    assert (U8 : bv_unsigned (Z_to_bv 64 (bv_unsigned r8 + 1)) = 6 + i + 1) by (rewrite H8; apply unsigned_lit; lia).
    assert (U4 : bv_unsigned (Z_to_bv 64 (bv_unsigned r4 + 1)) = buf + 30 + (i + 1))
      by (rewrite H4; rewrite unsigned_lit by lia; lia).
    assert (U10 : bv_unsigned (Z_to_bv 64 (bv_unsigned r10 + 1)) = buf + 30 + (i + 1))
      by (rewrite H10; rewrite unsigned_lit by lia; lia).
    assert (U9 : bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned r9 + 1))) = i + 1)
      by (rewrite H9, swrap32_small by lia; apply unsigned_lit; lia).
    destruct f as [|f'].
    + (* i = 9, the last turn: j 0x17158; ld s1, 8(sp); the DESK notice with off = -1 *)
      assert (C : bv_ltu r7 (Z_to_bv 64 (bv_unsigned r8 + 1)) = true)
        by (unfold bv_ltu; rewrite H7, U8; apply Z.ltb_lt; lia).
      rewrite C. cbn [negb].
      cbn [find_mac_loop] in HM.
      step. step.
      eapply oa_desk; try eassumption.
      all: first [ reflexivity | lia ].
    + (* i <= 8: the next turn *)
      assert (C : bv_ltu r7 (Z_to_bv 64 (bv_unsigned r8 + 1)) = false)
        by (unfold bv_ltu; rewrite H7, U8; apply Z.ltb_ge; lia).
      rewrite C. cbn [negb].
      eapply (IH ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' TF now pv fp buf (i + 1) b fj);
        try eassumption.
      all: first [ lia | (rewrite U8; lia) | exact U4 | exact U10 | exact U9 ].
Qed.
