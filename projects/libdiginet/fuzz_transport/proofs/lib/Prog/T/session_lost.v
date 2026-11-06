(* The walk of session_lost (transport/src/diginet_session.c:160-165) in the plain image, 0x16c64, set_state
   inlined: the two world stores of :162-163, then set_state's test and, when the state changes, the notice built
   on the stack (memset of :83, its kind / state / old / reason), the store of the state and the call of
   g_s.notify = notice (call_notify: the model's Some gives the cell value). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC WalkNotify notice_c session_lost_c.
Import ListNotations.
Open Scope Z_scope.

Theorem session_lost_holds : memset_contract -> notice_contract -> session_lost_contract.
Proof.
  intros MEMSET NOTICE. unfold session_lost_contract, session_lost_ENTRY, session_lost_FRAME.
  unfold notice_contract, notice_ENTRY, notice_FRAME in NOTICE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo why B B' TF -> -> Hwhy WM GF HM TFA RR S16 ST LO WOS MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold w_off_stack in WOS.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  assert (Usp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  (* the model: the two stores of :162-163, then set_state *)
  cbv beta zeta delta [session_lost_m set_state_m call_notify] in HM.
  set (B1 := set_S_desk_counter_valid (set_S_inflight B 0) 0) in HM.
  assert (LB1 : length B1 = Z.to_nat W_LEN) by (unfold B1, set_S_desk_counter_valid, set_S_inflight; wlen).
  assert (SB1 : S_state B1 = S_state B)
    by (unfold B1, S_state, set_S_desk_counter_valid, set_S_inflight; rewrite !rd32_upd_W by wside; reflexivity).
  assert (GB1 : g_fail_next B1 = g_fail_next B)
    by (unfold B1, g_fail_next, set_S_desk_counter_valid, set_S_inflight; rewrite !rd_upd_W by wside; reflexivity).
  rewrite SB1 in HM.
  pose proof (munch_refl [(bv_unsigned sp - 384, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  carve_frame 32%nat ST. rename FR into FRs.
  carve_frame 56%nat ST. rename FR into FRm.
  carve_frame 16%nat ST. rename FR into FRh.
  carve_frame 8%nat ST. rename FR into FRu.
  do 5 step.                                   (* addi sp; sd ra, s0, s1, s2 *)
  step.                                        (* lw s2, 112(a0): s->state *)
  step. step.                                  (* sw zero, 168(a0); sw zero, 212(a0) *)
  lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?X] |- _ =>
    replace X with B1 in H; [rename H into WMw |] end.
  2: { unfold B1, set_S_desk_counter_valid, set_S_inflight, A_S_desk_counter_valid, A_S_inflight.
       rewrite upd_comm_W by (rewrite ?length_le4; wside). reflexivity. }
  destruct (Z.eqb_spec (S_state B) DIGINET_S_IDLE) as [E0 | E0].
  - (* the state is IDLE already: no notice *)
    injection HM as <-.
    assert (E0' : s32_at B 1760 = 0) by exact E0. rewrite E0'.
    step. if_true.
    do 6 step.
    release_frame FRu ST (bv_unsigned sp + -104).
    release_frame FRh ST (bv_unsigned sp + -88).
    release_frame FRm ST (bv_unsigned sp + -32).
    release_frame FRs ST (bv_unsigned sp).
    apply evt_done. do 16 eexists. split; [reflexivity |].
    refine (conj MU (conj WMo (conj _ (conj ST (conj WMw _))))); [assumption | rewrite GB1; exact GF].
  - (* the state changes: the notice *)
    destruct (S_notify (set_S_state B1 DIGINET_S_IDLE) =? ti_notice timg_plain) eqn:EN; [| discriminate HM].
    apply Z.eqb_eq in EN. cbv beta iota in HM.
    assert (EN1 : u_at B1 1744 8 = 0x149e4).
    { unfold S_notify, set_S_state in EN. rewrite rd_upd_W in EN by wside. exact EN. }
    assert (NZ : bv_unsigned (Z_to_bv 64 (s32_at B 1760)) <> 0)
      by (apply bv_unsigned_nz; [pose proof (s32_range B 1760); lia | exact E0]).
    step. if_false.
    do 5 step.                                 (* mv s1, a1; mv s0, a0; addi a0, sp, 24; li a2, 56; li a1, 0 *)
    step.                                      (* jal memset: the notice's 56 bytes from .announce on *)
    assert (Um88 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -88)) = bv_unsigned sp + -88) by (apply unsigned_lit; lia).
    assert (GB' : g_fail_next B' = g_fail_next B).
    { transitivity (g_fail_next (set_S_state B1 DIGINET_S_IDLE)).
      - apply (notice_state_acked_fail_next timg_plain TF _ (Ntc DIGINET_N_STATE DIGINET_S_IDLE (S_state B) why 0 0 0 0 None [] 0));
          [ left; reflexivity | unfold set_S_state; wlen | exact HM ].
      - unfold g_fail_next at 1, set_S_state. rewrite rd_upd_W by wside. exact GB1. }
    eapply evt_cut.
    { eapply (MEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 junk0).
      - rewrite Um88. exact FRm.
      - exact MI. }
    intros ms' PO. unfold memset_post in PO. destruct_exs PO. destruct PO as (E & MUc & WMc & MIc & DST). subst ms'.
    rewrite Um88 in MUc, DST. change (bv_unsigned (Z_to_bv 64 56)) with 56 in MUc, DST.
    lazymatch type of MUc with munch _ _ ?m2 =>
      pose proof (wmem_transport _ _ _ _ WMw MUc WMc ltac:(cbn [disjoint_from]; split; [lia | exact I])) as WMw2;
      clear WMw; rename WMw2 into WMw;
      transport_after_call rsegs m1 m2 MUc WMc end.
    clear MUc WMc MI. rename MIc into MI. rename DST into FRm.
    rewrite (ret_pc_even 93344) by (first [lia | reflexivity]).
    step.                                      (* li a1, 2 *)
    step. rewrite EN1.                         (* ld a2, 96(s0): g_s.notify = notice *)
    step.                                      (* ld a0, 104(s0): g_s.notify_ctx *)
    step. step. step.                          (* sd a1, 8(sp); sw s2, 16(sp); sw s1, 20(sp): kind, state, old, reason *)
    step.                                      (* sw zero, 112(s0): s->state = IDLE *)
    lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?X] |- _ =>
      replace X with (set_S_state B1 DIGINET_S_IDLE) in H by reflexivity; try rename H into WMw end.
    step.                                      (* addi a1, sp, 8 *)
    step.                                      (* jalr a2: notice *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mN end.
    assert (BN : bytes_at rsegs mN (bv_unsigned sp + -104) (ntc_state_bytes DIGINET_S_IDLE (S_state B) why)).
    { eapply bytes_at_ext.
      - eapply bytes_at_join; [ eapply rw_cells_bytes_at; exact FRh | eapply rw_cells_bytes_at; exact FRm | ].
        cbn [cells_bytes cbytes]. rewrite !app_length, length_le8, !length_le4. cbn. lia.
      - cbn [cells_bytes cbytes]. rewrite !app_nil_r, !le4_put, le8_put.
        unfold ntc_state_bytes. change (put 8 2) with (put 4 2 ++ put 4 0). rewrite <- !app_assoc. reflexivity. }
    eapply evt_cut.
    { eapply (NOTICE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
                (set_S_state B1 DIGINET_S_IDLE) B' (bv_unsigned sp + -104)
                (Ntc DIGINET_N_STATE DIGINET_S_IDLE (S_state B) why 0 0 0 0 None [] 0) TF).
      - reflexivity.
      - apply ntc_state_at; [ exact BN | lia | rewrite sp_mod8 by exact S16; reflexivity
                            | unfold off_world; lia | unfold off_window; rewrite Usp; lia | rewrite Usp; lia
                            | unfold DIGINET_S_IDLE; lia | pose proof (s32_range B A_S_state); unfold S_state; lia
                            | lia ].
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
    lazymatch goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112))) |- _ =>
      rewrite Usp in H; try clear ST; rename H into ST end.
    lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB _ B'] |- _ => rename H into WMw' end.
    do 6 step.                                 (* ld ra, s0, s1, s2; addi sp; ret *)
    release_frame FRu ST (bv_unsigned sp + -104).
    release_frame FRh ST (bv_unsigned sp + -88).
    release_frame FRm ST (bv_unsigned sp + -32).
    release_frame FRs ST (bv_unsigned sp).
    apply evt_done. do 16 eexists. split; [reflexivity |].
    refine (conj MU (conj WMo (conj _ (conj ST (conj WMw' _))))); [assumption | rewrite GB'; exact GF].
Qed.
