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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import m_rx_epi m_rx_ann m_rx_ack m_rx_data.
Import ListNotations.
Open Scope Z_scope.

(* 0x15568, the desk known and not CLOSED: M.last_rx = g_now, the switch on f.cmd, m_tick, return 1. *)
Lemma mrx_body : bcmp_contract -> desk_named_contract ->
  m_lost_contract -> m_wake_contract -> m_maybe_online_contract -> m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (fr : tframe) (n : Z) (B1 B' : list byte) (r : Z) (X : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  mrx_fix sp lo fr n ->
  bytes_at rsegs m (tf_addr fr) (tf_bytes fr) ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 8 X; C8 (Z_to_bv 64 (mrx_byte (tf_bytes fr) 24)); C8 (Z_to_bv 64 (mrx_byte (tf_bytes fr) 21));
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B1 ->
  M_state B1 <> S_CLOSED ->
  mrx_k timg_plain fr B1 = Some (B', r) ->
  x8 = Z_to_bv 64 (tf_addr fr) ->
  x14 = Z_to_bv 64 (M_state B1) ->
  x15 = Z_to_bv 64 206736 ->
  x18 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 19) ->
  x19 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 18) ->
  x20 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 26) ->
  x21 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 28) ->
  x22 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 27) ->
  x23 = Z_to_bv 64 (spec_be16 (zs (tf_bytes fr)) 14) ->
  x24 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 25) ->
  x25 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 22) ->
  x26 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 23) ->
  x27 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 20) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo B' r)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15568) fc None m (seg_rom rsegs)).
Proof.
  intros BC DN LC WC MOC TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo fr n B1 B' r X
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    FX HBYTES MU WM0 MI ST FR WM NCL MDL -> -> -> -> -> -> -> -> -> -> -> -> ->.
  pose proof FX as FX'. mrx_fix_intro FX'.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts.
  assert (FC : mrx_fc fr = mrx_byte (tf_bytes fr) 28) by (unfold mrx_fc; apply mrx_byte_at; lia).
  pose proof (mrx_byte_range (tf_bytes fr) 28) as RC.
  unfold mrx_k in MDL. replace (M_state B1 =? S_CLOSED) with false in MDL by (symmetry; apply Z.eqb_neq; exact NCL).
  cbv iota in MDL.
  destruct (mrx_sw timg_plain fr (set_M_last_rx B1 (g_now B1))) as [[B3 []]|] eqn:SW; [|discriminate].
  destruct (m_tick_m B3) as [[B4 []]|] eqn:TK; [|discriminate].
  injection MDL as EB Er. subst B' r.
  (* 0x15568-0x15580: s1 = &g_fail_next, M.last_rx = g_now, s0 = the body, s7 = body_len *)
  step. step. step.
  step. step. step. step.
  change (u_at B1 65000 8) with (g_now B1).
  lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ =>
    change (upd B1 32 (put 8 (u_at B1 65000 8))) with (set_M_last_rx B1 (g_now B1)) in H end.
  assert (LB1 : Z.of_nat (length B1) = 65616) by lia.
  assert (MS2 : M_state (set_M_last_rx B1 (g_now B1)) = M_state B1) by (mrx_unf; mrx_rw; reflexivity).
  assert (GN2 : g_now (set_M_last_rx B1 (g_now B1)) = g_now B1) by (mrx_unf; mrx_rw; reflexivity).
  set (B2 := set_M_last_rx B1 (g_now B1)) in *.
  unfold mrx_sw in SW. rewrite FC in SW.
  unfold SPEC_CMD_E0, SPEC_CMD_E1, SPEC_CMD_ACK, SPEC_CMD_DATA, SPEC_CMD_E3 in SW.
  (* 0x15584: bge 223, cmd *)
  step.
  rewrite mrxk_lts by lia.
  destruct (Z.ltb_spec 223 (mrx_byte (tf_bytes fr) 28)) as [CH|CL]; cbn [negb]; cbv iota.
  - (* 0x15588-0x15590: cmd - 224 <u 2 *)
    step. step. step.
    rewrite mrxk_ltu by lia.
    destruct (Z.ltb_spec (mrx_byte (tf_bytes fr) 28 + -224) 2) as [CA|CB]; cbn [negb]; cbv iota.
    + (* e0 / e1 *)
      assert (CE : (mrx_byte (tf_bytes fr) 28 =? 224) || (mrx_byte (tf_bytes fr) 28 =? 225) = true)
        by (apply orb_true_iff; destruct (Z.eq_dec (mrx_byte (tf_bytes fr) 28) 224) as [E|E];
            [left | right]; apply Z.eqb_eq; lia).
      rewrite CE in SW. cbv iota in SW.
      mrx_fr_merge_tac.
      eapply (mrx_annl BC DN LC WC MOC TC);
        [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp
        | rewrite FC; lia | exact SW | exact TK
        | first [reflexivity | rewrite MS2; reflexivity | rewrite FC; reflexivity] .. ].
    + (* 0x156ac-0x156b0: cmd != e3 goes to m_tick *)
      step. step.
      rewrite mrxk_eqb by lia.
      destruct (Z.eqb_spec (mrx_byte (tf_bytes fr) 28) 227) as [C3|C3]; cbn [negb]; cbv iota.
      * (* e3, 0x156b4-0x156c4: m_lost (R_DESK_DISCONNECT) when ONLINE or WAKING *)
        mrx_cmd_rw SW (mrx_byte (tf_bytes fr) 28).
        rewrite MS2 in SW. unfold S_ONLINE, S_WAKING in SW.
        assert (RS1 : -2^31 <= M_state B1 < 2^31) by apply s32_range.
        step. step. step.
        rewrite mrx_state12 by exact RS1.
        destruct ((M_state B1 =? 2) || (M_state B1 =? 1)) eqn:SO; cbn [negb]; cbv iota.
        -- cbv iota in SW. step. mrx_fr_merge_tac.
           eapply (mrx_lost LC TC);
             [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp
             | reflexivity | lia | exact SW | exact TK ].
        -- cbv iota in SW. injection SW as EB3. subst B3.
           mrx_fr_merge_tac.
           eapply (mrx_tick TC);
             [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp
             | exact TK ].
      * mrx_cmd_rw SW (mrx_byte (tf_bytes fr) 28). injection SW as EB3. subst B3.
        mrx_fr_merge_tac.
        eapply (mrx_tick TC);
          [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ].
  - (* 0x15648: beqz cmd *)
    step.
    rewrite mrxk_eqb by lia.
    destruct (Z.eqb_spec (mrx_byte (tf_bytes fr) 28) 0) as [C0|C0]; cbv iota.
    + mrx_cmd_rw SW (mrx_byte (tf_bytes fr) 28).
      eapply (mrx_datal TC);
        [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp
        | exact SW | exact TK
        | first [reflexivity | rewrite GN2; reflexivity] .. ].
    + step. step.
      rewrite mrxk_eqb by lia.
      destruct (Z.eqb_spec (mrx_byte (tf_bytes fr) 28) 160) as [CK|CK]; cbn [negb]; cbv iota.
      * mrx_cmd_rw SW (mrx_byte (tf_bytes fr) 28).
        eapply (mrx_ackl MOC TC);
          [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp
          | exact SW | exact TK
          | first [reflexivity | rewrite MS2; reflexivity] .. ].
      * mrx_cmd_rw SW (mrx_byte (tf_bytes fr) 28). injection SW as EB3. subst B3.
        mrx_fr_merge_tac.
        eapply (mrx_tick TC);
          [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ].
Qed.
