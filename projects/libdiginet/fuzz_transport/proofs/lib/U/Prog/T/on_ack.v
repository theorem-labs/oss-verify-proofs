(* The walk of on_ack (transport/src/diginet_session.c:223-237) in the ubsan image, 0x1728c: the alignment checks
   of s and f, the test of :225 (inflight, then the frame's ack counter against s->inflight_counter); on a miss
   stats.rx_ignored++; on a match s->inflight = 0, the ACKED notice built on the stack (memset of :230, kind /
   state / frame / counter / retry) and the call of g_s.notify = notice (call_notify: the model's Some gives the
   cell value), then in WAKING wake_acked = 1 and the call of maybe_online. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC WalkNotify notice_c maybe_online_c on_ack_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the 32-bit compare of :225 and the 16-bit retry the notice carries ---- *)

Lemma swrap32_range : forall x, - 2 ^ 31 <= bv_swrap 32 x < 2 ^ 31.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma swrap32_inj : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> bv_swrap 32 x = bv_swrap 32 y -> x = y.
Proof.
  intros x y Hx Hy E. unfold bv_swrap, bv_wrap in E. change (bv_half_modulus 32) with (2 ^ 31) in E.
  change (bv_modulus 32) with (2 ^ 32) in E. Z.div_mod_to_equations. lia.
Qed.

Lemma put4_swrap32 : forall x, put 4 (bv_swrap 32 x) = put 4 x.
Proof.
  intros x. unfold put. rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 x) 32) by (change (Z.of_nat 4) with 4; lia).
  rewrite <- (Z_to_le_bytes_mod 4 x 32) by (change (Z.of_nat 4) with 4; lia). f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma put2_swrap16 : forall x, put 2 (bv_swrap 16 x) = put 2 x.
Proof.
  intros x. unfold put. rewrite <- (Z_to_le_bytes_mod 2 (bv_swrap 16 x) 16) by (change (Z.of_nat 2) with 2; lia).
  rewrite <- (Z_to_le_bytes_mod 2 x 16) by (change (Z.of_nat 2) with 2; lia). f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 16) with (2 ^ 15). change (bv_modulus 16) with (2 ^ 16).
  Z.div_mod_to_equations. lia.
Qed.

Lemma u_at_4_2 : forall (B : list byte) k, u_at B k 4 mod 2 ^ 16 = u_at B k 2.
Proof.
  intros B k. unfold u_at, sub. generalize (skipn (Z.to_nat k) B) as l. intros l.
  rewrite !bytes_le_to_Z_le_val.
  assert (R : forall x : byte, 0 <= bv_unsigned x < 256) by (intros x; exact (bv_unsigned_in_range 8 x)).
  destruct l as [|x0 [|x1 [|x2 [|x3 l]]]]; cbn [firstn map le_val].
  - reflexivity.
  - pose proof (R x0). Z.div_mod_to_equations. lia.
  - pose proof (R x0). pose proof (R x1). Z.div_mod_to_equations. lia.
  - pose proof (R x0). pose proof (R x1). pose proof (R x2). Z.div_mod_to_equations. lia.
  - pose proof (R x0). pose proof (R x1). pose proof (R x2). pose proof (R x3). Z.div_mod_to_equations. lia.
Qed.

(* lh then sh of the low 16 bits of s->inflight_retries: the bytes of the model's u16 *)
Lemma retry_put : forall (B : list byte) k, put 2 (bv_swrap 16 (u_at B k 2)) = put 2 (u16 (u_at B k 4)).
Proof. intros B k. rewrite put2_swrap16, <- u_at_4_2. unfold u16. reflexivity. Qed.

Theorem on_ack_holds : memset_contract -> notice_contract -> maybe_online_contract -> on_ack_contract.
Proof.
  intros MEMSET NOTICE MONLINE. unfold on_ack_contract, on_ack_ENTRY, on_ack_FRAME.
  unfold notice_contract, notice_ENTRY, notice_FRAME in NOTICE.
  unfold maybe_online_contract, maybe_online_ENTRY, maybe_online_FRAME in MONLINE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo fp buf b fj B B' TF -> -> DF WM GF HM TFA RR S16 ST LO WOS MI.
  destruct DF as (FC0 & BB & ABb & FRf & ABf & FP8). clear BB ABb.
  unfold arg_blk, off_world, off_window in ABf.
  unfold dframe_cells in FRf.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold w_off_stack in WOS.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  assert (Usp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 480, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  carve_frame 24%nat ST. rename FR into FRs.
  carve_frame 8%nat ST. rename FR into FRt.
  carve_frame 40%nat ST. rename FR into FRm.
  carve_frame 24%nat ST. rename FR into FRh.
  do 5 step.                                   (* addi sp; sd ra, s0, s1; mv s0, a0 *)
  step. step. try if_false.                    (* andi a0, a0, 7; bnez: s is 8-aligned *)
  step.                                        (* lw a0, 212(s0): s->inflight *)
  cbv beta zeta delta [on_ack_m call_notify] in HM.
  destruct (Z.eqb_spec (S_inflight B) 0) as [I0 | I0].
  - (* nothing in flight: stats.rx_ignored++ *)
    cbn [orb] in HM. injection HM as <-.
    assert (I0' : s32_at B 1860 = 0) by exact I0. rewrite I0'.
    step. if_true.
    step. step.                                (* lui a0, 0x4; add a0, s0, a0 *)
    step.                                      (* ld a1, 1800(a0): stats.rx_ignored *)
    step.                                      (* addi a1, a1, 1 *)
    step.                                      (* sd a1, 1800(a0) *)
    lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
      replace X with (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1))) in H
        by (unfold set_S_stats_rx_ignored, u64, S_stats_rx_ignored; rewrite put_mod64 by lia; reflexivity);
      try rename H into WMw end.
    do 5 step.                                 (* ld ra, s0, s1; addi sp; ret *)
    release_frame FRh ST (bv_unsigned sp + -72).
    release_frame FRm ST (bv_unsigned sp + -32).
    release_frame FRt ST (bv_unsigned sp + -24).
    release_frame FRs ST (bv_unsigned sp).
    apply evt_done. do 16 eexists. split; [reflexivity |].
    refine (conj MU (conj WMo (conj _ (conj ST (conj WMw _))))); [assumption |].
    unfold g_fail_next, set_S_stats_rx_ignored. rewrite rd_upd_W by wside. exact GF.
  - cbn [orb] in HM.
    assert (NZ : bv_unsigned (Z_to_bv 64 (s32_at B 1860)) <> 0)
      by (apply bv_unsigned_nz; [pose proof (s32_range B 1860); lia | exact I0]).
    step. if_false.
    assert (AL : Z.land fp 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact FP8).
    step.                                      (* andi a0, a1, 7 *)
    step.                                      (* bnez a0: f is 8-aligned *)
    rewrite (unsigned_lit fp) by lia. rewrite AL. if_false.
    pose proof (be32_range b 22) as RA. change (be32 b 22) with (fr_ack b) in RA.
    pose proof (u_at_range B 3392 4) as R4. change (8 * Z.of_nat 4) with 32 in R4.
    step.                                      (* lw s1, 24(a1): f->h.ack_counter *)
    step.                                      (* lw a0, 1744(s0): s->inflight_counter *)
    step.                                      (* bne s1, a0 *)
    assert (SX : sx32 (Z_to_bv 64 (fr_ack b)) = Z_to_bv 64 (bv_swrap 32 (fr_ack b)))
      by (unfold sx32; rewrite unsigned_lit by lia; reflexivity).
    rewrite SX.
    destruct (Z.eqb_spec (fr_ack b) (S_inflight_counter B)) as [EA | EA]; cbn [negb] in HM.
    2: { (* the counter does not match: stats.rx_ignored++ *)
      injection HM as <-.
      assert (NE : bv_unsigned (Z_to_bv 64 (bv_swrap 32 (fr_ack b))) <> bv_unsigned (Z_to_bv 64 (s32_at B 3392))).
      { apply bv_unsigned_ne; [pose proof (swrap32_range (fr_ack b)); lia | pose proof (s32_range B 3392); lia |].
        intro E. apply EA. exact (swrap32_inj _ _ RA R4 E). }
      if_true.
      step. step.                              (* lui a0, 0x4; add a0, s0, a0 *)
      step.                                    (* ld a1, 1800(a0): stats.rx_ignored *)
      step.                                    (* addi a1, a1, 1 *)
      step.                                    (* sd a1, 1800(a0) *)
      lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
        replace X with (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1))) in H
          by (unfold set_S_stats_rx_ignored, u64, S_stats_rx_ignored; rewrite put_mod64 by lia; reflexivity);
        try rename H into WMw end.
      do 5 step.                               (* ld ra, s0, s1; addi sp; ret *)
      release_frame FRh ST (bv_unsigned sp + -72).
      release_frame FRm ST (bv_unsigned sp + -32).
      release_frame FRt ST (bv_unsigned sp + -24).
      release_frame FRs ST (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity |].
      refine (conj MU (conj WMo (conj _ (conj ST (conj WMw _))))); [assumption |].
      unfold g_fail_next, set_S_stats_rx_ignored. rewrite rd_upd_W by wside. exact GF. }
    (* the counter matches: the ACKED notice *)
    assert (EA' : s32_at B 3392 = bv_swrap 32 (fr_ack b)) by (unfold s32_at; rewrite EA; reflexivity).
    rewrite EA'. if_false.
    step.                                      (* lw a0, 112(s0): s->state *)
    step.                                      (* sw zero, 212(s0): s->inflight = 0 *)
    set (B1 := set_S_inflight B 0) in HM.
    lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
      replace X with B1 in H by reflexivity; try rename H into WMw end.
    assert (LB1 : length B1 = Z.to_nat W_LEN) by (unfold B1, set_S_inflight; wlen).
    assert (SB1 : S_state B1 = S_state B)
      by (unfold B1, S_state, set_S_inflight; rewrite rd32_upd_W by wside; reflexivity).
    assert (GB1 : g_fail_next B1 = g_fail_next B)
      by (unfold B1, g_fail_next, set_S_inflight; rewrite rd_upd_W by wside; reflexivity).
    destruct (S_notify B1 =? ti_notice timg_ubsan) eqn:EN; [| cbv beta iota in HM; discriminate HM].
    apply Z.eqb_eq in EN. cbv beta iota in HM.
    assert (EN1 : u_at B1 1744 8 = 0x14bc8) by exact EN.
    lazymatch type of HM with context [notice_m _ _ _ ?n] => set (NT := n) in HM end.
    destruct (notice_m timg_ubsan TF B1 NT) as [[Bn []] |] eqn:HN; [| discriminate HM].
    cbv beta iota in HM.
    step.                                      (* li a2, 4 *)
    step. step. step. step.                    (* sw a2, 0(sp); sw a0, 4(sp); sd zero, 8(sp); sd a1, 16(sp) *)
    do 3 step.                                 (* addi a0, sp, 24; li a2, 40; li a1, 0 *)
    step.                                      (* jal memset: the notice's 40 bytes from .announce on *)
    assert (Um72 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -72)) = bv_unsigned sp + -72) by (apply unsigned_lit; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mS end.
    eapply evt_cut.
    { eapply (MEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mS junk1).
      - rewrite Um72. exact FRm.
      - exact MI. }
    intros ms' PO. unfold memset_post in PO. destruct_exs PO. destruct PO as (E & MUc & WMc & MIc & DST). subst ms'.
    rewrite Um72 in MUc, DST. change (bv_unsigned (Z_to_bv 64 40)) with 40 in MUc, DST.
    lazymatch type of MUc with munch _ _ ?m2 =>
      pose proof (wmem_transport _ _ _ _ WMw MUc WMc ltac:(cbn [disjoint_from]; split; [lia | exact I])) as WMw2;
      clear WMw; rename WMw2 into WMw;
      transport_after_call rsegs mS m2 MUc WMc end.
    clear MUc WMc MI. rename MIc into MI. rename DST into FRm.
    rewrite (ret_pc_even 94960) by (first [lia | reflexivity]).
    step.                                      (* lh a1, 1748(s0): s->inflight_retries *)
    step. rewrite EN1.                         (* ld a2, 96(s0): g_s.notify = notice *)
    step.                                      (* ld a0, 104(s0): g_s.notify_ctx *)
    step. step. step.                          (* sw s1, 64(sp); sh a1, 68(sp); sh zero, 70(sp) *)
    step.                                      (* mv a1, sp *)
    step.                                      (* jalr a2: notice *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mN end.
    assert (BN : bytes_at rsegs mN (bv_unsigned sp + -96)
                   (ntc_acked_bytes (S_state B1) fp (fr_ack b) (u16 (S_inflight_retries B1)))).
    { eapply bytes_at_ext.
      - eapply bytes_at_join; [ eapply bytes_at_join; [ eapply rw_cells_bytes_at; exact FRh
                                                      | eapply rw_cells_bytes_at; exact FRm | ]
                              | eapply rw_cells_bytes_at; exact FRt | ].
        + cbn [cells_bytes cbytes]. rewrite !length_app, !length_le8, !length_le4. cbn. lia.
        + cbn [cells_bytes cbytes]. rewrite !length_app, !length_le8, !length_le4, repeat_length. cbn. lia.
      - cbn [cells_bytes cbytes]. rewrite !app_nil_r, !le8_put, !le4_put, !le2_put.
        rewrite put4_swrap32, retry_put, SB1.
        unfold ntc_acked_bytes. rewrite <- !app_assoc. reflexivity. }
    eapply evt_cut.
    { eapply (NOTICE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
                B1 Bn (bv_unsigned sp + -96) NT TF).
      - reflexivity.
      - apply (ntc_acked_at _ _ _ _ _ fp); [ exact BN | lia | rewrite sp_mod8 by exact S16; reflexivity
                            | unfold off_world; lia | unfold off_window; rewrite Usp; lia | rewrite Usp; lia
                            | pose proof (s32_range B1 A_S_state); unfold S_state; lia | exact RA
                            | pose proof (Z.mod_pos_bound (S_inflight_retries B1) 65536 ltac:(lia)); unfold u16; lia ].
      - eapply tframe_at_move; [ exact TFA | exact MU | rewrite Usp; lia | rewrite Usp; lia ].
      - eapply relro_img_move; [ exact RR | exact MU | lia ].
      - exact WMw.
      - exact HN.
      - rewrite Usp, sp_mod16 by exact S16. reflexivity.
      - rewrite Usp. exact ST.
      - rewrite Usp. lia.
      - unfold w_off_stack. rewrite Usp. lia.
      - exact MI. }
    wk_post_call rsegs mN.
    lazymatch goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) |- _ =>
      rewrite Usp in H; try clear ST; rename H into ST end.
    lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ Bn] |- _ => rename H into WMn end.
    assert (GBn : g_fail_next Bn = g_fail_next B).
    { rewrite <- GB1. apply (notice_state_acked_fail_next timg_ubsan TF B1 NT); [ right; reflexivity | exact LB1 | exact HN ]. }
    pose proof (wm_len _ _ _ _ WMn) as LBn.
    step.                                      (* lw a1, 112(s0): s->state *)
    step.                                      (* li a0, 1 *)
    destruct (Z.eqb_spec (S_state Bn) DIGINET_S_WAKING) as [EW | EW]; cbv beta iota in HM.
    + (* WAKING: wake_acked = 1, then maybe_online *)
      assert (EW' : s32_at Bn 1760 = 1) by exact EW. rewrite EW'.
      step. if_false.                          (* bne a1, a0 *)
      step.                                    (* sw a0, 144(s0): s->wake_acked = 1 *)
      lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
        replace X with (set_S_wake_acked Bn 1) in H by reflexivity; try rename H into WMw end.
      step.                                    (* mv a0, s0 *)
      step.                                    (* jal maybe_online *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mM end.
      eapply evt_cut.
      { eapply (MONLINE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
                  (set_S_wake_acked Bn 1) B' TF).
        - reflexivity.
        - exact WMw.
        - unfold g_fail_next at 1, set_S_wake_acked. rewrite rd_upd_W by wside. fold (g_fail_next Bn). rewrite GBn. exact GF.
        - exact HM.
        - eapply tframe_at_move; [ exact TFA | exact MU | rewrite Usp; lia | rewrite Usp; lia ].
        - eapply relro_img_move; [ exact RR | exact MU | lia ].
        - rewrite Usp, sp_mod16 by exact S16. reflexivity.
        - rewrite Usp. exact ST.
        - rewrite Usp. lia.
        - unfold w_off_stack. rewrite Usp. lia.
        - assumption. }
      wk_post_call rsegs mM.
      lazymatch goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) |- _ =>
        rewrite Usp in H; try clear ST; rename H into ST end.
      step.                                    (* j 0x17340 *)
      do 5 step.                               (* ld ra, s0, s1; addi sp; ret *)
      release_frame FRh ST (bv_unsigned sp + -72).
      release_frame FRm ST (bv_unsigned sp + -32).
      release_frame FRt ST (bv_unsigned sp + -24).
      release_frame FRs ST (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity |].
      refine (conj MU (conj WMo (conj _ (conj ST (conj _ _))))); assumption.
    + (* not WAKING: return *)
      injection HM as <-.
      assert (NE1 : bv_unsigned (Z_to_bv 64 (s32_at Bn 1760)) <> bv_unsigned (Z_to_bv 64 1))
        by (apply bv_unsigned_ne; [pose proof (s32_range Bn 1760); lia | lia | exact EW]).
      change (bv_unsigned (Z_to_bv 64 1)) with 1 in NE1.
      step. if_true.                           (* bne a1, a0 *)
      do 5 step.                               (* ld ra, s0, s1; addi sp; ret *)
      release_frame FRh ST (bv_unsigned sp + -72).
      release_frame FRm ST (bv_unsigned sp + -32).
      release_frame FRt ST (bv_unsigned sp + -24).
      release_frame FRs ST (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity |].
      refine (conj MU (conj WMo (conj _ (conj ST (conj WMn _))))); [assumption | rewrite GBn; exact GF].
Qed.
