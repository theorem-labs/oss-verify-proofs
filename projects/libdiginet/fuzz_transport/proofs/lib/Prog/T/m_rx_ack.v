From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import bcmp_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import m_rx_c desk_named_c m_lost_c m_wake_c m_maybe_online_c m_tick_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import m_rx_epi.
Import ListNotations.
Open Scope Z_scope.

(* 0x15654, cmd ACK (fuzz_transport.c:332-342): f.ack against the in-flight counter, OW.acked, M.fly_on = 0,
   M.e2_acked and m_maybe_online when WAKING, then m_tick. *)
Lemma mrx_ackl : m_maybe_online_contract -> m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (fr : tframe) (n : Z) (B2 B3 B4 : list byte) (X : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  mrx_fix sp lo fr n ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 8 X; C8 (Z_to_bv 64 (mrx_byte (tf_bytes fr) 24)); C8 (Z_to_bv 64 (mrx_byte (tf_bytes fr) 21));
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B2 ->
  mrx_ackb fr B2 = Some (B3, tt) ->
  m_tick_m B3 = Some (B4, tt) ->
  x9 = Z_to_bv 64 271704 ->
  x14 = Z_to_bv 64 (M_state B2) ->
  x15 = Z_to_bv 64 206736 ->
  x24 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 25) ->
  x25 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 22) ->
  x26 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 23) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo B4 1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15654) fc None m (seg_rom rsegs)).
Proof.
  intros MOC TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo fr n B2 B3 B4 X
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    FX MU WM0 MI ST FR WM SW TK -> -> -> -> -> ->.
  pose proof FX as FX'. mrx_fix_intro FX'.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  assert (LB2 : Z.of_nat (length B2) = 65616) by (rewrite LB; unfold W_LEN; lia).
  wk_facts.
  unfold mrx_ackb, truth in SW.
  (* 0x15654-0x15658: M.fly_on *)
  step.
  pose proof (s32_range B2 96) as RF.
  step.
  rewrite mrxk_eqb by lia.
  change (s32_at B2 96) with (M_fly_on B2) in *.
  destruct (Z.eqb_spec (M_fly_on B2) 0) as [F0|F1]; cbv iota.
  { replace (M_fly_on B2 =? 0) with true in SW by (symmetry; apply Z.eqb_eq; exact F0).
    cbn [negb andb] in SW. cbv iota in SW. injection SW as EB3. subst B3.
    mrx_fr_merge_tac.
    eapply (mrx_tick TC);
      [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ]. }
  replace (M_fly_on B2 =? 0) with false in SW by (symmetry; apply Z.eqb_neq; exact F1).
  cbn [negb andb] in SW.
  (* 0x1565c-0x1567c: f.ack against M.fly_counter *)
  do 8 step.
  rewrite (mrx_asm_be32 _ _ _ _ (mrx_byte_range _ 22) (mrx_byte_range _ 23) (mrx_byte_range _ 24)
             (mrx_byte_range _ 25)).
  assert (EA : mrx_byte (tf_bytes fr) 22 * 2^24 + mrx_byte (tf_bytes fr) 23 * 2^16 +
               mrx_byte (tf_bytes fr) 24 * 2^8 + mrx_byte (tf_bytes fr) 25 = mrx_ack fr)
    by (unfold mrx_ack; symmetry; apply mrx_be32; lia).
  rewrite EA.
  assert (RA : 0 <= mrx_ack fr < 2^32) by (unfold mrx_ack; apply mrx_be32_range; lia).
  pose proof (u_at_range B2 104 4) as RFC. change (8 * Z.of_nat 4) with 32 in RFC.
  step.
  change (s32_at B2 104) with (bv_swrap 32 (u_at B2 104 4)).
  rewrite mrx_eqb_sw by lia.
  change (u_at B2 104 4) with (M_fly_counter B2) in *.
  destruct (Z.eqb_spec (mrx_ack fr) (M_fly_counter B2)) as [EQ|NE]; cbn [negb]; cbv iota.
  2: { replace (mrx_ack fr =? M_fly_counter B2) with false in SW by (symmetry; apply Z.eqb_neq; exact NE).
       cbv iota in SW. injection SW as EB3. subst B3.
       mrx_fr_merge_tac.
       eapply (mrx_tick TC);
         [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ]. }
  replace (mrx_ack fr =? M_fly_counter B2) with true in SW by (symmetry; apply Z.eqb_eq; exact EQ).
  cbv iota in SW.
  unfold int_inc in SW. destruct (OW_acked B2 =? INT_MAX) eqn:IM; [discriminate|].
  cbv beta iota zeta in SW.
  (* 0x15680-0x1569c: OW.acked, OW.acked_counter, OW.acked_retry, M.fly_on *)
  do 9 step.
  lazymatch type of SW with context [M_state ?E =? S_WAKING] => set (B6 := E) in SW end.
  assert (P1 : put 4 (bv_swrap 32 (mrx_ack fr)) = put 4 (M_fly_counter (set_OW_acked B2 (OW_acked B2 + 1)))).
  { apply (mrx_put_eqm 4 _ _ 32); [lia|]. rewrite mrx_swrap_mod. f_equal. rewrite EQ.
    symmetry. mrx_unf. mrx_rw. reflexivity. }
  assert (P2 : put 4 (s32_at B2 108) =
               put 4 (M_fly_retries (set_OW_acked_counter (set_OW_acked B2 (OW_acked B2 + 1))
                                       (M_fly_counter (set_OW_acked B2 (OW_acked B2 + 1)))))).
  { apply (mrx_put_eqm 4 _ _ 32); [lia|]. unfold s32_at at 1. rewrite mrx_swrap_mod. f_equal.
    symmetry. mrx_unf. mrx_rw. reflexivity. }
  lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN [CB _ ?W] |- _ => rewrite P1, P2 in H end.
  lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN [CB _ ?W'] |- _ =>
    assert (EW : W' = B6) by (unfold B6; mrx_unf; mrx_upd_eq); rewrite EW in H; clear EW end.
  assert (MS6 : M_state B6 = M_state B2) by (unfold B6; mrx_unf; mrx_rw; reflexivity).
  (* from here on B6 is a name only: no conversion may unfold it *)
  clearbody B6.
  rewrite MS6 in SW. unfold S_WAKING in SW.
  assert (RS : -2^31 <= M_state B2 < 2^31) by apply s32_range.
  rewrite mrxk_eqb by lia.
  destruct (Z.eqb_spec (M_state B2) 1) as [W1|W1]; cbn [negb]; cbv iota.
  - (* 0x156a4-0x156a8: M.e2_acked = 1; m_maybe_online *)
    replace (M_state B2 =? 1) with true in SW by (symmetry; apply Z.eqb_eq; exact W1). cbv iota in SW.
    step. step.
    lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ =>
      change (upd B6 16 (put 4 1)) with (set_M_e2_acked B6 1) in H end.
    mrx_fr_merge_tac.
    eapply (mrx_mo MOC TC);
      [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp
      | exact SW | exact TK ].
  - replace (M_state B2 =? 1) with false in SW by (symmetry; apply Z.eqb_neq; exact W1). cbv iota in SW.
    injection SW as EB3. subst B3.
    mrx_fr_merge_tac.
    eapply (mrx_tick TC);
      [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ].
Qed.
