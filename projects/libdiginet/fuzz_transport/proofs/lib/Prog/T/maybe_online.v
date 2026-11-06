(* The walk of maybe_online (transport/src/diginet_session.c:176-182) in the plain image, 0x17628, ms and set_state
   inlined: the three tests of :178; then the next keepalive of :179 and set_state's ONLINE notice (memset of :83,
   kind / state / old / reason stored as two words), the store of the state and the call of g_s.notify = notice
   (call_notify: the model's Some gives the cell value). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC WalkNotify notice_c maybe_online_c.
Import ListNotations.
Open Scope Z_scope.

Theorem maybe_online_holds : memset_contract -> notice_contract -> maybe_online_contract.
Proof.
  intros MEMSET NOTICE. unfold maybe_online_contract, maybe_online_ENTRY, maybe_online_FRAME.
  unfold notice_contract, notice_ENTRY, notice_FRAME in NOTICE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo B B' TF -> WM GF HM TFA RR S16 ST LO WOS MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold w_off_stack in WOS.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  assert (Usp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  cbv beta zeta delta [maybe_online_m set_state_m call_notify] in HM.
  pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  carve_frame 16%nat ST. rename FR into FRs.
  carve_frame 56%nat ST. rename FR into FRm.
  carve_frame 16%nat ST. rename FR into FRh.
  carve_frame 8%nat ST. rename FR into FRu.
  do 4 step.                                   (* addi sp; sd ra, s0; mv s0, a0 *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE end.
  (* the exits of :178: the epilogue with the world unchanged *)
  assert (EXIT : forall x10 x11 x12 x13,
    B' = B ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 368, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) s1
               x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x176ac) fc None mE (seg_rom rsegs))).
  { intros x10 x11 x12 x13 ->.
    do 4 step.                                 (* ld ra, s0; addi sp; ret *)
    release_frame FRu ST (bv_unsigned sp + -88).
    release_frame FRh ST (bv_unsigned sp + -72).
    release_frame FRm ST (bv_unsigned sp + -16).
    release_frame FRs ST (bv_unsigned sp).
    apply evt_done. do 16 eexists. split; [reflexivity |].
    refine (conj MU (conj WMo (conj _ (conj ST (conj WM GF))))). assumption. }
  set (B2 := set_S_next_keepalive_us B (u64 (S_last_rx_us B + ms_m (S_cfg_keepalive_ms B)))) in HM.
  assert (LB2 : length B2 = Z.to_nat W_LEN) by (unfold B2, set_S_next_keepalive_us; wlen).
  assert (SB2 : S_state B2 = S_state B)
    by (unfold B2, S_state, set_S_next_keepalive_us; rewrite !rd32_upd_W by wside; reflexivity).
  assert (GB2 : g_fail_next B2 = g_fail_next B)
    by (unfold B2, g_fail_next, set_S_next_keepalive_us; rewrite !rd_upd_W by wside; reflexivity).
  step. step.                                  (* lw a0, 112(a0): s->state; li a1, 1 *)
  destruct (Z.eqb_spec (S_state B) DIGINET_S_WAKING) as [E1 | E1].
  2: { cbv beta iota delta [andb] in HM. injection HM as <-.
       assert (NE : bv_unsigned (Z_to_bv 64 (s32_at B 1760)) <> 1).
       { pose proof (bv_unsigned_ne (s32_at B 1760) 1 ltac:(pose proof (s32_range B 1760); lia) ltac:(lia) E1) as X.
         rewrite (unsigned_lit 1) in X by lia. exact X. }
       step. if_true. apply EXIT. reflexivity. }
  assert (E1' : s32_at B 1760 = 1) by exact E1. rewrite E1'.
  step. if_false.
  step.                                        (* lw a0, 144(s0): s->wake_acked *)
  destruct (Z.eqb_spec (S_wake_acked B) 0) as [E2 | E2].
  { cbv beta iota delta [andb negb] in HM. injection HM as <-.
    assert (E2' : s32_at B 1792 = 0) by exact E2. rewrite E2'.
    step. if_true. apply EXIT. reflexivity. }
  assert (NZ2 : bv_unsigned (Z_to_bv 64 (s32_at B 1792)) <> 0)
    by (apply bv_unsigned_nz; [pose proof (s32_range B 1792); lia | exact E2]).
  step. if_false.
  step.                                        (* lw a0, 140(s0): s->e1_named_us *)
  destruct (Z.eqb_spec (S_e1_named_us B) 0) as [E3 | E3].
  { cbv beta iota delta [andb negb] in HM. injection HM as <-.
    assert (E3' : s32_at B 1788 = 0) by exact E3. rewrite E3'.
    step. if_true. apply EXIT. reflexivity. }
  assert (NZ3 : bv_unsigned (Z_to_bv 64 (s32_at B 1788)) <> 0)
    by (apply bv_unsigned_nz; [pose proof (s32_range B 1788); lia | exact E3]).
  step. if_false.
  cbv beta iota delta [andb negb] in HM.
  replace (S_state B2) with 1 in HM by (rewrite SB2, E1; reflexivity).
  change (1 =? DIGINET_S_ONLINE) with false in HM. cbv beta iota in HM.
  destruct (S_notify (set_S_state B2 DIGINET_S_ONLINE) =? ti_notice timg_plain) eqn:EN;
    [| cbv beta iota in HM; discriminate HM].
  apply Z.eqb_eq in EN. cbv beta iota in HM.
  assert (EN1 : u_at (set_S_state B2 DIGINET_S_ONLINE) 1744 8 = 0x149e4) by exact EN.
  assert (GB' : g_fail_next B' = g_fail_next B).
  { transitivity (g_fail_next (set_S_state B2 DIGINET_S_ONLINE)).
    - apply (notice_state_acked_fail_next timg_plain TF _
               (Ntc DIGINET_N_STATE DIGINET_S_ONLINE 1 DIGINET_R_ONLINE 0 0 0 0 None [] 0));
        [ left; reflexivity | unfold set_S_state; wlen | exact HM ].
    - unfold g_fail_next at 1, set_S_state. rewrite rd_upd_W by wside. exact GB2. }
  step. step.                                  (* lwu a0, 24(s0): cfg.keepalive_ms; ld a1, 176(s0): last_rx_us *)
  step. step. step.                            (* li a2, 1000; mul; add *)
  step.                                        (* sd a0, 184(s0): next_keepalive_us (:179) *)
  lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?X] |- _ =>
    replace X with B2 in H; [try rename H into WMw |] end.
  2: { unfold B2, set_S_next_keepalive_us, A_S_next_keepalive_us, ms_m, u64.
       change (S_last_rx_us B) with (u_at B 1824 8). change (S_cfg_keepalive_ms B) with (u_at B 1672 4).
       pose proof (u_at_range B 1672 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
       rewrite (unsigned_lit (u_at B 1672 4)) by lia.
       f_equal. apply put8_mod_eq. rewrite ?Z.mod_mod by lia. rewrite ?Z.add_mod_idemp_r by lia. f_equal. lia. }
  do 3 step.                                   (* addi a0, sp, 24; li a2, 56; li a1, 0 *)
  step.                                        (* jal memset: the notice's 56 bytes from .announce on *)
  assert (Um72 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -72)) = bv_unsigned sp + -72) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mS end.
  eapply evt_cut.
  { eapply (MEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mS junk0).
    - rewrite Um72. exact FRm.
    - exact MI. }
  intros ms' PO. unfold memset_post in PO. destruct_exs PO. destruct PO as (E & MUc & WMc & MIc & DST). subst ms'.
  rewrite Um72 in MUc, DST. change (bv_unsigned (Z_to_bv 64 56)) with 56 in MUc, DST.
  lazymatch type of MUc with munch _ _ ?m2 =>
    pose proof (wmem_transport _ _ _ _ WMw MUc WMc ltac:(cbn [disjoint_from]; split; [lia | exact I])) as WMw2;
    clear WMw; rename WMw2 into WMw;
    transport_after_call rsegs mS m2 MUc WMc end.
  clear MUc WMc MI. rename MIc into MI. rename DST into FRm.
  rewrite (ret_pc_even 95868) by (first [lia | reflexivity]).
  step. step.                                  (* li a1, 1; li a0, 2 *)
  step.                                        (* sw a0, 112(s0): s->state = ONLINE *)
  lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?X] |- _ =>
    replace X with (set_S_state B2 DIGINET_S_ONLINE) in H by reflexivity; try rename H into WMw end.
  step. rewrite EN1.                           (* ld a2, 96(s0): g_s.notify = notice *)
  step.                                        (* ld a0, 104(s0): g_s.notify_ctx *)
  do 3 step.                                   (* slli a1, a1, 33; addi a3, a1, 2; addi a1, a1, 1 *)
  step. step.                                  (* sd a3, 8(sp); sd a1, 16(sp): kind, state, old, reason *)
  step.                                        (* addi a1, sp, 8 *)
  step.                                        (* jalr a2: notice *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mN end.
  assert (BN : bytes_at rsegs mN (bv_unsigned sp + -88) (ntc_state_bytes 2 1 2)).
  { eapply bytes_at_ext.
    - eapply bytes_at_join; [ eapply rw_cells_bytes_at; exact FRh | eapply rw_cells_bytes_at; exact FRm | ].
      cbn [cells_bytes cbytes]. rewrite !app_length, !length_le8. cbn. lia.
    - cbn [cells_bytes cbytes]. rewrite !app_nil_r, !le8_put. unfold ntc_state_bytes.
      apply bytes_eq_of_zs. vm_compute. reflexivity. }
  eapply evt_cut.
  { eapply (NOTICE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
              (set_S_state B2 DIGINET_S_ONLINE) B' (bv_unsigned sp + -88)
              (Ntc DIGINET_N_STATE DIGINET_S_ONLINE 1 DIGINET_R_ONLINE 0 0 0 0 None [] 0) TF).
    - reflexivity.
    - apply ntc_state_at; [ exact BN | lia | rewrite sp_mod8 by exact S16; reflexivity
                          | unfold off_world; lia | unfold off_window; rewrite Usp; lia | rewrite Usp; lia
                          | unfold DIGINET_S_ONLINE; lia | lia | unfold DIGINET_R_ONLINE; lia ].
    - eapply tframe_at_move; [ exact TFA | exact MU | rewrite Usp; lia | rewrite Usp; lia ].
    - eapply relro_img_move; [ exact RR | exact MU | lia ].
    - exact WMw.
    - exact HM.
    - rewrite Usp, sp_mod16 by exact S16. reflexivity.
    - rewrite Usp. exact ST.
    - rewrite Usp. lia.
    - unfold w_off_stack. rewrite Usp. lia.
    - exact MI. }
  wk_post_call rsegs mN.
  lazymatch goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) |- _ =>
    rewrite Usp in H; try clear ST; rename H into ST end.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB _ B'] |- _ => rename H into WMw' end.
  do 4 step.                                   (* ld ra, s0; addi sp; ret *)
  release_frame FRu ST (bv_unsigned sp + -88).
  release_frame FRh ST (bv_unsigned sp + -72).
  release_frame FRm ST (bv_unsigned sp + -16).
  release_frame FRs ST (bv_unsigned sp).
  apply evt_done. do 16 eexists. split; [reflexivity |].
  refine (conj MU (conj WMo (conj _ (conj ST (conj WMw' _))))); [assumption | rewrite GB'; exact GF].
Qed.
