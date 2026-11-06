(* The walk of set_state (transport/src/diginet_session.c:79-86) in the ubsan image, 0x16ce0: the alignment
   check of s, the test of :81, and, when the state changes, the notice built on the stack (memset of :83, its
   kind / state / old / reason), the store of the state and the call of g_s.notify = notice (call_notify: the
   model's Some gives the cell value). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC WalkNotify notice_c set_state_c.
Import ListNotations.
Open Scope Z_scope.

Theorem set_state_holds : memset_contract -> notice_contract -> set_state_contract.
Proof.
  intros MEMSET NOTICE. unfold set_state_contract, set_state_ENTRY, set_state_FRAME.
  unfold notice_contract, notice_ENTRY, notice_FRAME in NOTICE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo st why B B' TF -> -> -> Hst Hwhy WM GF HM TFA RR S16 ST LO WOS MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold w_off_stack in WOS.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  assert (Usp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  cbv beta zeta delta [set_state_m call_notify] in HM.
  pose proof (munch_refl [(bv_unsigned sp - 384, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  carve_frame 40%nat ST. rename FR into FRs.
  carve_frame 56%nat ST. rename FR into FRm.
  carve_frame 16%nat ST. rename FR into FRh.
  do 7 step.                                   (* addi sp; sd ra, s0, s1, s2, s3; mv s1, a0 *)
  step. step. try if_false.                    (* andi a0, a0, 7; bnez: s is 8-aligned *)
  step.                                        (* mv s2, a1 *)
  step.                                        (* lw s3, 112(s1): s->state *)
  destruct (Z.eqb_spec (S_state B) st) as [E0 | E0].
  - (* the state is st already: no notice *)
    cbv beta iota in HM. injection HM as <-.
    assert (E0' : s32_at B 1760 = st) by exact E0. rewrite E0'.
    step. if_true.
    do 7 step.                                 (* ld ra, s0, s1, s2, s3; addi sp; ret *)
    release_frame FRh ST (bv_unsigned sp + -96).
    release_frame FRm ST (bv_unsigned sp + -40).
    release_frame FRs ST (bv_unsigned sp).
    apply evt_done. do 16 eexists. split; [reflexivity |].
    refine (conj MU (conj WMo (conj _ (conj ST (conj WM GF))))). assumption.
  - (* the state changes: the notice *)
    destruct (S_notify (set_S_state B st) =? ti_notice timg_ubsan) eqn:EN; [| cbv beta iota in HM; discriminate HM].
    apply Z.eqb_eq in EN. cbv beta iota in HM.
    assert (EN1 : u_at B 1744 8 = 0x14bc8).
    { unfold S_notify, set_S_state in EN. rewrite rd_upd_W in EN by wside. exact EN. }
    assert (NE : bv_unsigned (Z_to_bv 64 (s32_at B 1760)) <> bv_unsigned (Z_to_bv 64 st))
      by (apply bv_unsigned_ne; [pose proof (s32_range B 1760); lia | lia | exact E0]).
    step. if_false.
    do 4 step.                                 (* mv s0, a2; addi a0, sp, 16; li a2, 56; li a1, 0 *)
    step.                                      (* jal memset: the notice's 56 bytes from .announce on *)
    assert (Um96 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
    assert (GB' : g_fail_next B' = g_fail_next B).
    { transitivity (g_fail_next (set_S_state B st)).
      - apply (notice_state_acked_fail_next timg_ubsan TF _ (Ntc DIGINET_N_STATE st (S_state B) why 0 0 0 0 None [] 0));
          [ left; reflexivity | unfold set_S_state; wlen | exact HM ].
      - unfold g_fail_next at 1, set_S_state. rewrite rd_upd_W by wside. reflexivity. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mS end.
    eapply evt_cut.
    { eapply (MEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mS junk0).
      - rewrite Um96. exact FRm.
      - exact MI. }
    intros ms' PO. unfold memset_post in PO. destruct_exs PO. destruct PO as (E & MUc & WMc & MIc & DST). subst ms'.
    rewrite Um96 in MUc, DST. change (bv_unsigned (Z_to_bv 64 56)) with 56 in MUc, DST.
    lazymatch type of MUc with munch _ _ ?m2 =>
      pose proof (wmem_transport _ _ _ _ WM MUc WMc ltac:(cbn [disjoint_from]; split; [lia | exact I])) as WM2;
      clear WM; rename WM2 into WM;
      transport_after_call rsegs mS m2 MUc WMc end.
    clear MUc WMc MI. rename MIc into MI. rename DST into FRm.
    rewrite (ret_pc_even 93476) by (first [lia | reflexivity]).
    step.                                      (* li a1, 2 *)
    step. rewrite EN1.                         (* ld a2, 96(s1): g_s.notify = notice *)
    step.                                      (* ld a0, 104(s1): g_s.notify_ctx *)
    step. step. step. step.                    (* sw a1, s2, s3, s0: kind, state, old, reason *)
    step.                                      (* sw s2, 112(s1): s->state = st *)
    lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
      replace X with (set_S_state B st) in H by reflexivity; try rename H into WM end.
    step.                                      (* mv a1, sp *)
    step.                                      (* jalr a2: notice *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mN end.
    assert (BN : bytes_at rsegs mN (bv_unsigned sp + -112) (ntc_state_bytes st (S_state B) why)).
    { eapply bytes_at_ext.
      - eapply bytes_at_join; [ eapply rw_cells_bytes_at; exact FRh | eapply rw_cells_bytes_at; exact FRm | ].
        cbn [cells_bytes cbytes]. rewrite !app_length, !length_le4. cbn. lia.
      - cbn [cells_bytes cbytes]. rewrite !app_nil_r, !le4_put.
        unfold ntc_state_bytes. rewrite <- !app_assoc. reflexivity. }
    eapply evt_cut.
    { eapply (NOTICE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
                (set_S_state B st) B' (bv_unsigned sp + -112)
                (Ntc DIGINET_N_STATE st (S_state B) why 0 0 0 0 None [] 0) TF).
      - reflexivity.
      - apply ntc_state_at; [ exact BN | lia | rewrite sp_mod8 by exact S16; reflexivity
                            | unfold off_world; lia | unfold off_window; rewrite Usp; lia | rewrite Usp; lia
                            | lia | pose proof (s32_range B A_S_state); unfold S_state; lia
                            | lia ].
      - eapply tframe_at_move; [ exact TFA | exact MU | rewrite Usp; lia | rewrite Usp; lia ].
      - eapply relro_img_move; [ exact RR | exact MU | lia ].
      - exact WM.
      - exact HM.
      - rewrite Usp, sp_mod16 by exact S16. reflexivity.
      - rewrite Usp. exact ST.
      - rewrite Usp. lia.
      - unfold w_off_stack. rewrite Usp. lia.
      - exact MI. }
    wk_post_call rsegs mN.
    lazymatch goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112))) |- _ =>
      rewrite Usp in H; try clear ST; rename H into ST end.
    lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ B'] |- _ => rename H into WM' end.
    do 7 step.                                 (* ld ra, s0, s1, s2, s3; addi sp; ret *)
    release_frame FRh ST (bv_unsigned sp + -96).
    release_frame FRm ST (bv_unsigned sp + -40).
    release_frame FRs ST (bv_unsigned sp).
    apply evt_done. do 16 eexists. split; [reflexivity |].
    refine (conj MU (conj WMo (conj _ (conj ST (conj WM' _))))); [assumption | rewrite GB'; exact GF].
Qed.
