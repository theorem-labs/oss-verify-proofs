From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import send_control_c set_state_c
  diginet_session_close_c.
Import ListNotations.
Open Scope Z_scope.

Lemma close_eqb : forall v c, -2^63 <= v < 2^63 -> -2^63 <= c < 2^63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 c) = (v =? c).
Proof.
  intros v c Hv Hc. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec v c) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N. Z.div_mod_to_equations. nia.
Qed.

Lemma close_tframe : forall m m' (sp sp' : word) TF d K,
  tframe_at m sp 672 TF ->
  munch [(bv_unsigned sp - 672, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  bv_unsigned sp' = bv_unsigned sp - d -> 0 <= d -> d + K <= 672 ->
  tframe_at m' sp' K TF.
Proof.
  intros m m' sp sp' [fr|] d K TFm MU Esp Hd HK; [|exact I].
  destruct TFm as (Hp & Hb & Hw & Hwin). unfold tframe_at, off_world, off_window in *.
  split; [exact Hp|]. split.
  - eapply bytes_at_transport; [exact Hb | exact MU |]. cbn [disjoint_from]. repeat split; lia.
  - split; [exact Hw|]. rewrite Esp. lia.
Qed.

Lemma close_relro : forall m m' (sp : word),
  relro_img m ->
  munch [(bv_unsigned sp - 672, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 672 ->
  relro_img m'.
Proof.
  intros m m' sp R MU H i Hi. rewrite <- (R i Hi). unfold mrd.
  rewrite (MU (wa (RELRO_BASE + i))); [reflexivity|].
  unfold RELRO_BASE, RELRO_LEN, W_BASE_UBSAN, W_LEN in *.
  cbn [outside]. rewrite wa_unsigned by lia. lia.
Qed.

Lemma close_gfail : forall B, length B = Z.to_nat W_LEN -> g_fail_next (set_S_inflight B 0) = g_fail_next B.
Proof.
  intros B L. unfold g_fail_next, set_S_inflight.
  apply u_at_upd_out; rewrite ?length_put, ?L; rewrite ?Z2Nat.id by (unfold W_LEN; lia);
    unfold A_S_inflight, OFF_g_s, OFF_g_fail_next, W_LEN; lia.
Qed.

(* The common tail at 0x16dac: sw zero,212(s0) (s->inflight = 0, :155); li a1,3; li a2,8; mv a0,s0; jal set_state
   (DIGINET_S_CLOSED, DIGINET_R_CLOSED, :156); j; mv a0,s1; ld ra; ld s0; ld s1; addi sp,sp,32; ret. B1 is the world
   before the store, GFt the g_fail_next bound of the world after it, HSt set_state's model equation, EB / Er the
   model's result; the rest are the walk's facts by name (entry tframe / relro, the entry munch / wmono, Hsp, the
   window above the world, the stack, mem_inv, the frame cell, the post, the entry sp). *)
Ltac close_tail SS B1 GFt HSt EB Er TFm RO MU0 WMO0 Hsp WO ST MI FR QQ sp :=
  step;
  lazymatch goal with WMw : rw_cells rsegs ?mc W_BASE_UBSAN [CB _ (upd B1 1860 (put 4 0))] |- _ =>
    change (upd B1 1860 (put 4 0)) with (set_S_inflight B1 0) in WMw;
    do 4 step;
    let ms' := fresh "ms'" in let mS := fresh "mS" in let EqS := fresh "Eq" in
    let MUs := fresh "MUs" in let WMs := fresh "WMs" in let MIs := fresh "MIs" in
    let STs := fresh "STs" in let WMS := fresh "WMS" in let GFS := fresh "GFS" in
    eapply evt_cut;
    [ eapply SS with (st := 3) (why := 8);
      [ reflexivity | reflexivity | reflexivity | lia | lia | exact WMw | exact GFt | exact HSt
      | eapply close_tframe with (d := 32); [ exact TFm | exact MU0 | rewrite Hsp; lia | lia | lia ]
      | eapply close_relro; [ exact RO | exact MU0 | exact WO ]
      | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | exact MI ]
    | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mS &
                  EqS & MUs & WMs & MIs & STs & WMS & GFS);
      subst ms'; rewrite Hsp in MUs, STs; clear WMw;
      transport_after_call rsegs mc mS MUs WMs; clear MUs WMs MI; try clear mc;
      rewrite (ret_pc_even 93632) by (first [lia | reflexivity]);
      do 5 step;
      release_frame FR STs (bv_unsigned sp);
      do 2 step;
      apply evt_done; unfold QQ; rewrite <- Er, <- EB;
      do 15 eexists; split; [reflexivity|];
      split; [exact MU0|]; split; [exact WMO0|]; split; [exact MIs|]; split; [exact STs|];
      split; [exact WMS | exact GFS] ]
  end.

Theorem diginet_session_close_holds :
  send_control_contract -> set_state_contract -> diginet_session_close_contract.
Proof.
  intros SC SS.
  unfold send_control_contract, send_control_ENTRY, send_control_FRAME in SC.
  unfold set_state_contract, set_state_ENTRY, set_state_FRAME in SS.
  unfold diginet_session_close_contract, diginet_session_close_ENTRY, diginet_session_close_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo now r B B' TF A0 A1 NOW WM GF HM TFm RO SP16 ST LO WO MI.
  subst a0 a1.
  unfold w_off_stack in WO.
  wk_facts.
  assert (Eoff : OFF_g_s = 1648) by reflexivity.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 672, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU0.
  pose proof (wmono_refl rsegs m) as WMO0.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 32%nat ST.
  (* prologue: addi sp,sp,-32; sd ra,24(sp); sd s0,16(sp); sd s1,8(sp) *)
  do 4 step.
  (* beqz a0: s = &g_s is not NULL *)
  step.
  rewrite close_eqb by (unfold OFF_g_s; lia).
  change (W_BASE_UBSAN + OFF_g_s =? 0) with false. cbv iota.
  (* mv s0,a0; andi a0,a0,7 *)
  step. step.
  (* bnez a0: &g_s is 8-aligned *)
  step.
  assert (AL : Z.land (bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s))) 7 = 0)
    by (rewrite unsigned_lit by (unfold OFF_g_s; lia); reflexivity).
  rewrite AL. rewrite close_eqb by lia.
  change (negb (0 =? 0)) with false. cbv iota.
  (* lw a0,116(s0): s->desk_known *)
  step.
  change (s32_at B 1764) with (S_desk_known B).
  pose proof (s32_range B A_S_desk_known) as RDK. change (s32_at B A_S_desk_known) with (S_desk_known B) in RDK.
  (* beqz a0 *)
  step.
  rewrite close_eqb by lia.
  unfold diginet_session_close_m in HM.
  change DIGINET_S_CLOSED with 3 in HM. change DIGINET_R_CLOSED with 8 in HM.
  change DIGINET_CMD_DISCONNECT with 227 in HM.
  destruct (Z.eqb_spec (S_desk_known B) 0) as [D0|D0]; cbv iota.
  - (* desk not known: no send, r = 0 *)
    cbv beta iota zeta delta [negb andb] in HM.
    destruct (set_state_m timg_ubsan TF (set_S_inflight B 0) 3 8) as [[B2 []]|] eqn:HS; [|discriminate HM].
    injection HM as EB Er.
    assert (GFt : g_fail_next (set_S_inflight B 0) <= 1) by (rewrite close_gfail by exact (wm_len _ _ _ _ WM); exact GF).
    (* li s1,0 *)
    step.
    close_tail SS B GFt HS EB Er TFm RO MU0 WMO0 Hsp WO ST MI FR QQ sp.
  - (* desk known *)
    cbv beta iota zeta delta [negb andb] in HM.
    (* lw a0,136(s0): s->foreign *)
    step.
    change (s32_at B 1784) with (S_foreign B).
    pose proof (s32_range B A_S_foreign) as RFO. change (s32_at B A_S_foreign) with (S_foreign B) in RFO.
    (* bnez a0 *)
    step.
    rewrite close_eqb by lia.
    destruct (Z.eqb_spec (S_foreign B) 0) as [F0|F0]; cbv beta iota delta [negb].
    + cbv beta iota zeta delta [negb andb] in HM.
      (* lw a0,112(s0): s->state; li a1,3 *)
      step.
      change (s32_at B 1760) with (S_state B).
      pose proof (s32_range B A_S_state) as RST. change (s32_at B A_S_state) with (S_state B) in RST.
      step.
      (* bne a0,a1 *)
      step.
      rewrite close_eqb by lia.
      destruct (Z.eqb_spec (S_state B) 3) as [S3|S3]; cbv beta iota delta [negb].
      * (* already closed: no send, r = 0 *)
        cbv beta iota zeta delta [negb andb] in HM.
        destruct (set_state_m timg_ubsan TF (set_S_inflight B 0) 3 8) as [[B2 []]|] eqn:HS; [|discriminate HM].
        injection HM as EB Er.
        assert (GFt : g_fail_next (set_S_inflight B 0) <= 1)
          by (rewrite close_gfail by exact (wm_len _ _ _ _ WM); exact GF).
        step.
        close_tail SS B GFt HS EB Er TFm RO MU0 WMO0 Hsp WO ST MI FR QQ sp.
      * (* send_control (s, DIGINET_CMD_DISCONNECT, 0, NULL, NULL) *)
        cbv beta iota zeta delta [negb andb] in HM.
        destruct (send_control_m timg_ubsan TF B 227 0) as [[B1 [r1 f1]]|] eqn:HC; cbv beta iota in HM;
          [|discriminate HM].
        destruct (set_state_m timg_ubsan TF (set_S_inflight B1 0) 3 8) as [[B2 []]|] eqn:HS; [|discriminate HM].
        injection HM as EB Er.
        (* li a1,227; mv a0,s0; li a2,0; li a3,0; li a4,0; jal send_control *)
        do 6 step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          eapply evt_cut;
          [ eapply SC with (cmd := 227) (ack := 0) (kp := 0) (klp := 0) (K := []) (KL := []);
            [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | left; reflexivity
            | exact WM | exact GF | exact HC
            | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST | rewrite Hsp; lia
            | unfold w_off_stack; rewrite Hsp; lia | exact MI ]
          | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 &
                        Eq & MUc & WMc & MI2 & ST2 & WM2 & GF2 & _);
            subst ms'; cbn [Z.eqb app] in MUc; rewrite Hsp in MUc, ST2; clear WM;
            transport_after_call rsegs mc m2 MUc WMc; clear MUc WMc MI; try clear mc ]
        end.
        try clear ST. rename ST2 into ST. rename MI2 into MI.
        rewrite (ret_pc_even 93688) by (first [lia | reflexivity]).
        assert (GFt : g_fail_next (set_S_inflight B1 0) <= 1)
          by (rewrite close_gfail by exact (wm_len _ _ _ _ WM2); exact GF2).
        (* mv s1,a0; j 0x16dac *)
        do 2 step.
        close_tail SS B1 GFt HS EB Er TFm RO MU0 WMO0 Hsp WO ST MI FR QQ sp.
    + (* foreign desk: no send, r = 0 *)
      cbv beta iota zeta delta [negb andb] in HM.
      destruct (set_state_m timg_ubsan TF (set_S_inflight B 0) 3 8) as [[B2 []]|] eqn:HS; [|discriminate HM].
      injection HM as EB Er.
      assert (GFt : g_fail_next (set_S_inflight B 0) <= 1)
        by (rewrite close_gfail by exact (wm_len _ _ _ _ WM); exact GF).
      step.
      close_tail SS B GFt HS EB Er TFm RO MU0 WMO0 Hsp WO ST MI FR QQ sp.
Qed.
