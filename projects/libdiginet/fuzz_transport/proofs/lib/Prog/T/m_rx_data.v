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

(* 0x15744, the world B5 after the desk counter: OW.dn[OW.ndata] when OW.ndata < 2, OW.ndata++, m_tick. *)
Lemma mrx_data6l : m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (fr : tframe) (n : Z) (B5 B3 Bf : list byte) (X : list byte) (w1 w2 : word)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  mrx_fix sp lo fr n ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 8 X; C8 w1; C8 w2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B5 ->
  mrx_data6 fr B5 = Some (B3, tt) ->
  m_tick_m B3 = Some (Bf, tt) ->
  x8 = Z_to_bv 64 (tf_addr fr + 30) ->
  x9 = Z_to_bv 64 271704 ->
  x10 = Z_to_bv 64 (mrx_retry fr) ->
  x11 = Z_to_bv 64 (bv_swrap 32 (mrx_send fr)) ->
  x13 = Z_to_bv 64 1 ->
  x23 = Z_to_bv 64 (mrx_blen fr) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo Bf 1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15744) fc None m (seg_rom rsegs)).
Proof.
  intros TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo fr n B5 B3 Bf X w1 w2
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    FX MU WM0 MI ST FR WM SW TK -> -> -> -> -> ->.
  pose proof FX as FX'. mrx_fix_intro FX'.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts.
  assert (LB5 : Z.of_nat (length B5) = 65616) by lia.
  assert (RS : 0 <= mrx_send fr < 2^32) by (unfold mrx_send; apply mrx_be32_range; lia).
  assert (PS : put 4 (bv_swrap 32 (mrx_send fr)) = put 4 (mrx_send fr))
    by (apply (mrx_put_eqm 4 _ _ 32); [lia | apply mrx_swrap_mod]).
  unfold mrx_data6 in SW.
  pose proof (s32_range B5 65532) as RN.
  step.
  change (s32_at B5 65532) with (OW_ndata B5) in *.
  step.
  rewrite mrxk_lts by lia.
  destruct (Z.ltb_spec 1 (OW_ndata B5)) as [NG|NL]; cbv iota.
  - (* OW.ndata >= 2: no OW.dn store *)
    replace (OW_ndata B5 <? 2) with false in SW by (symmetry; apply Z.ltb_ge; lia). cbv iota in SW.
    unfold int_inc in SW. destruct (OW_ndata B5 =? INT_MAX) eqn:NM; [discriminate|]. cbv iota in SW.
    injection SW as EB3. subst B3.
    step. step. step.
    lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ =>
      change (upd B5 65532 (put 4 (OW_ndata B5 + 1))) with (set_OW_ndata B5 (OW_ndata B5 + 1)) in H end.
    mrx_fr_merge_tac.
    eapply (mrx_tick TC);
      [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ].
  - (* 0 <= OW.ndata <= 1: OW.dn[OW.ndata] = {body, body_len, send, retry} *)
    replace (OW_ndata B5 <? 2) with true in SW by (symmetry; apply Z.ltb_lt; lia). cbv iota in SW.
    destruct (OW_ndata B5 <? 0) eqn:NNEG; [discriminate|]. apply Z.ltb_ge in NNEG. cbv iota in SW.
    unfold int_inc in SW.
    replace (OW_ndata B5 =? INT_MAX) with false in SW by (symmetry; apply Z.eqb_neq; unfold INT_MAX; lia).
    cbv iota in SW. injection SW as EB3. subst B3.
    assert (ND : OW_ndata B5 = 0 \/ OW_ndata B5 = 1) by lia.
    destruct ND as [ND|ND]; rewrite ND in *.
    all: do 11 step.
    all: lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ =>
           rewrite PS in H;
           lazymatch type of H with rw_cells _ _ _ [CB _ ?W'] =>
             lazymatch type of TK with m_tick_m ?M = _ =>
               let EW := fresh "EW" in
               assert (EW : W' = M)
                 by (unfold set_OW_ndata, set_OW_dn_retry, set_OW_dn_counter, set_OW_dn_len, set_OW_dn_body,
                       A_OW_ndata, A_OW_dn_retry, A_OW_dn_counter, A_OW_dn_len, A_OW_dn_body, OFF_OW;
                     mrx_upd_eq);
               rewrite EW in H; clear EW
             end
           end
         end.
    all: mrx_fr_merge_tac.
    all: eapply (mrx_tick TC);
      [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ].
Qed.

(* 0x1572c, the world B4 after the backoff and the duplicate check: M.desk_counter_valid = 1,
   M.desk_counter = send, then the keepalive (body_len 1, body[0] 0) goes to m_tick, else OW.dn. *)
Lemma mrx_data5l : m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (fr : tframe) (n : Z) (B4 B3 Bf : list byte) (X : list byte) (w1 w2 : word)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  mrx_fix sp lo fr n ->
  bytes_at rsegs m (tf_addr fr) (tf_bytes fr) ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 8 X; C8 w1; C8 w2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B4 ->
  mrx_data5 fr B4 = Some (B3, tt) ->
  m_tick_m B3 = Some (Bf, tt) ->
  x8 = Z_to_bv 64 (tf_addr fr + 30) ->
  x9 = Z_to_bv 64 271704 ->
  x10 = Z_to_bv 64 (mrx_retry fr) ->
  x11 = Z_to_bv 64 (bv_swrap 32 (mrx_send fr)) ->
  x15 = Z_to_bv 64 206736 ->
  x23 = Z_to_bv 64 (mrx_blen fr) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo Bf 1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1572c) fc None m (seg_rom rsegs)).
Proof.
  intros TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo fr n B4 B3 Bf X w1 w2
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    FX HBYTES MU WM0 MI ST FR WM SW TK -> -> -> -> -> ->.
  pose proof FX as FX'. mrx_fix_intro FX'.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts.
  assert (LB4 : Z.of_nat (length B4) = 65616) by lia.
  assert (RS : 0 <= mrx_send fr < 2^32) by (unfold mrx_send; apply mrx_be32_range; lia).
  assert (PS : put 4 (bv_swrap 32 (mrx_send fr)) = put 4 (mrx_send fr))
    by (apply (mrx_put_eqm 4 _ _ 32); [lia | apply mrx_swrap_mod]).
  (* 0x1572c-0x15734 *)
  step. step. step.
  lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ =>
    rewrite PS in H;
    rewrite (mrx_comm B4 (put 4 1) (put 4 (mrx_send fr)) 76 80) in H by mrx_side;
    change (upd (upd B4 80 (put 4 (mrx_send fr))) 76 (put 4 1))
      with (set_M_desk_counter_valid (set_M_desk_counter B4 (mrx_send fr)) 1) in H
  end.
  unfold mrx_data5 in SW.
  set (B5 := set_M_desk_counter_valid (set_M_desk_counter B4 (mrx_send fr)) 1) in *.
  clearbody B5.
  assert (RB : 0 <= mrx_blen fr < 65536)
    by (unfold mrx_blen; pose proof (mrx_be16_range (zs (tf_bytes fr)) 14); lia).
  (* 0x15738: bne body_len, 1 *)
  step.
  rewrite mrxk_eqb by lia.
  destruct (Z.eqb_spec (mrx_blen fr) 1) as [BL1|BL1]; cbn [negb]; cbv iota.
  - (* 0x1573c-0x15740: body[0]; body_len 1 puts it inside the block *)
    assert (L31 : 31 <= Z.of_nat (length (tf_bytes fr))) by (unfold mrx_blen in BL1; lia).
    pose proof (bytes_at_read rsegs _ (tf_addr fr) (tf_bytes fr) 30 1 HBYTES ltac:(lia) ltac:(lia)) as RD.
    step. clear RD.
    try change (firstn 1 (skipn (Z.to_nat 30) (tf_bytes fr))) with (sub (tf_bytes fr) 30 1).
    rewrite (wm_lbu (tf_bytes fr) 30).
    step.
    pose proof (u_at_range (tf_bytes fr) 30 1) as RU. change (8 * Z.of_nat 1) with 8 in RU.
    rewrite mrxk_eqb by lia.
    unfold mrx_body in SW. rewrite (mrx_at8 (tf_bytes fr)) in SW by lia.
    replace (mrx_blen fr =? 1) with true in SW by (symmetry; apply Z.eqb_eq; exact BL1). cbn [andb] in SW.
    destruct (Z.eqb_spec (u_at (tf_bytes fr) 30 1) 0) as [K0|K0]; cbv iota; cbv iota in SW.
    + injection SW as EB3. subst B3.
      mrx_fr_merge_tac.
      eapply (mrx_tick TC);
        [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ].
    + eapply (mrx_data6l TC);
        [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact SW | exact TK | reflexivity .. ].
  - replace (mrx_blen fr =? 1) with false in SW by (symmetry; apply Z.eqb_neq; exact BL1).
    cbn [andb] in SW. cbv iota in SW.
    eapply (mrx_data6l TC);
      [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact SW | exact TK | reflexivity .. ].
Qed.

(* 0x15710, the world B4 after OW.acks, M.fail and the backoff: the duplicate (a valid desk counter equal to
   send, with retry) goes to m_tick, else 0x1572c. a2 holds send's top three bytes (HA2). *)
Lemma mrx_data4l : m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (fr : tframe) (n : Z) (B4 B3 Bf : list byte) (X : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  mrx_fix sp lo fr n ->
  bytes_at rsegs m (tf_addr fr) (tf_bytes fr) ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 8 X; C8 (Z_to_bv 64 (mrx_byte (tf_bytes fr) 24)); C8 (Z_to_bv 64 (mrx_byte (tf_bytes fr) 21));
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B4 ->
  mrx_data4 fr B4 = Some (B3, tt) ->
  m_tick_m B3 = Some (Bf, tt) ->
  Z_to_bv 64 (Z.lor (bv_unsigned x12) (bv_unsigned (Z_to_bv 64 (mrx_byte (tf_bytes fr) 21)))) =
    Z_to_bv 64 (bv_swrap 32 (mrx_send fr)) ->
  x8 = Z_to_bv 64 (tf_addr fr + 30) ->
  x9 = Z_to_bv 64 271704 ->
  x10 = Z_to_bv 64 (mrx_retry fr) ->
  x15 = Z_to_bv 64 206736 ->
  x23 = Z_to_bv 64 (mrx_blen fr) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo Bf 1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15710) fc None m (seg_rom rsegs)).
Proof.
  intros TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo fr n B4 B3 Bf X
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    FX HBYTES MU WM0 MI ST FR WM SW TK HA2 -> -> -> -> ->.
  pose proof FX as FX'. mrx_fix_intro FX'.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts.
  assert (RS : 0 <= mrx_send fr < 2^32) by (unfold mrx_send; apply mrx_be32_range; lia).
  assert (RR : 0 <= mrx_retry fr < 65536) by apply mrx_be16_range.
  unfold mrx_data4, truth in SW.
  pose proof (s32_range B4 76) as RV.
  (* 0x15710-0x1571c: M.desk_counter_valid; a1 = send *)
  step. step. step.
  rewrite HA2.
  step.
  rewrite mrxk_eqb by lia.
  change (s32_at B4 76) with (M_desk_counter_valid B4) in *.
  destruct (Z.eqb_spec (M_desk_counter_valid B4) 0) as [V0|V1]; cbv iota.
  { replace (M_desk_counter_valid B4 =? 0) with true in SW by (symmetry; apply Z.eqb_eq; exact V0).
    cbn [negb andb] in SW. cbv iota in SW.
    eapply (mrx_data5l TC);
      [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact SW | exact TK
      | reflexivity .. ]. }
  replace (M_desk_counter_valid B4 =? 0) with false in SW by (symmetry; apply Z.eqb_neq; exact V1).
  cbn [negb andb] in SW.
  (* 0x15720-0x15724: M.desk_counter against send *)
  pose proof (u_at_range B4 80 4) as RC. change (8 * Z.of_nat 4) with 32 in RC.
  step. step.
  change (s32_at B4 80) with (bv_swrap 32 (u_at B4 80 4)).
  rewrite mrx_eqb_sw by lia.
  change (u_at B4 80 4) with (M_desk_counter B4) in *.
  destruct (Z.eqb_spec (mrx_send fr) (M_desk_counter B4)) as [SC|SC]; cbn [negb]; cbv iota.
  - (* 0x15728: bnez retry *)
    replace (mrx_send fr =? M_desk_counter B4) with true in SW by (symmetry; apply Z.eqb_eq; exact SC).
    cbn [andb] in SW.
    step.
    rewrite mrxk_eqb by lia.
    destruct (Z.eqb_spec (mrx_retry fr) 0) as [R0|R1]; cbn [negb]; cbv iota.
    + replace (mrx_retry fr =? 0) with true in SW by (symmetry; apply Z.eqb_eq; exact R0).
      cbn [negb] in SW. cbv iota in SW.
      eapply (mrx_data5l TC);
        [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact SW | exact TK
        | reflexivity .. ].
    + replace (mrx_retry fr =? 0) with false in SW by (symmetry; apply Z.eqb_neq; exact R1).
      cbn [negb] in SW. cbv iota in SW. injection SW as EB3. subst B3.
      mrx_fr_merge_tac.
      eapply (mrx_tick TC);
        [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ].
  - replace (mrx_send fr =? M_desk_counter B4) with false in SW by (symmetry; apply Z.eqb_neq; exact SC).
    cbn [andb] in SW. cbv iota in SW.
    eapply (mrx_data5l TC);
      [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact SW | exact TK
      | reflexivity .. ].
Qed.

(* 0x156cc, cmd DATA (fuzz_transport.c:344-365): OW.acks, M.fail, the backoff, the desk counter, the keepalive,
   OW.dn[OW.ndata] and OW.ndata, then m_tick. *)
Lemma mrx_datal : m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (fr : tframe) (n : Z) (B2 B3 B4 : list byte) (X : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  mrx_fix sp lo fr n ->
  bytes_at rsegs m (tf_addr fr) (tf_bytes fr) ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 8 X; C8 (Z_to_bv 64 (mrx_byte (tf_bytes fr) 24)); C8 (Z_to_bv 64 (mrx_byte (tf_bytes fr) 21));
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B2 ->
  mrx_data fr B2 = Some (B3, tt) ->
  m_tick_m B3 = Some (B4, tt) ->
  x8 = Z_to_bv 64 (tf_addr fr + 30) ->
  x9 = Z_to_bv 64 271704 ->
  x11 = Z_to_bv 64 (g_now B2) ->
  x15 = Z_to_bv 64 206736 ->
  x18 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 19) ->
  x19 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 18) ->
  x20 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 26) ->
  x22 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 27) ->
  x23 = Z_to_bv 64 (mrx_blen fr) ->
  x27 = Z_to_bv 64 (mrx_byte (tf_bytes fr) 20) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo B4 1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x156cc) fc None m (seg_rom rsegs)).
Proof.
  intros TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo fr n B2 B3 B4 X
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    FX HBYTES MU WM0 MI ST FR WM SW TK -> -> -> -> -> -> -> -> -> ->.
  pose proof FX as FX'. mrx_fix_intro FX'.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  assert (LB2 : Z.of_nat (length B2) = 65616) by (rewrite LB; unfold W_LEN; lia).
  wk_facts.
  unfold mrx_data, int_inc in SW. destruct (OW_acks B2 =? INT_MAX) eqn:IA; [discriminate|].
  cbv beta iota in SW.
  (* 0x156cc-0x156f8: send's top three bytes, OW.acks, M.fail, retry *)
  do 12 step.
  rewrite (mrx_or8 _ _ (mrx_byte_range _ 26) (mrx_byte_range _ 27)).
  assert (ER : mrx_byte (tf_bytes fr) 26 * 2^8 + mrx_byte (tf_bytes fr) 27 = mrx_retry fr)
    by (unfold mrx_retry; symmetry; apply mrx_be16; lia).
  rewrite ER.
  assert (RR : 0 <= mrx_retry fr < 65536) by apply mrx_be16_range.
  lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ =>
    change (upd (upd B2 65516 (put 4 (s32_at B2 65516 + 1))) 88 (put 4 0))
      with (set_M_fail (set_OW_acks B2 (OW_acks B2 + 1)) 0) in H end.
  set (B3w := set_M_fail (set_OW_acks B2 (OW_acks B2 + 1)) 0) in *.
  assert (GN3 : g_now B3w = g_now B2) by (unfold B3w; mrx_unf; mrx_rw; reflexivity).
  assert (LB3 : Z.of_nat (length B3w) = 65616) by (unfold B3w; mrx_unf; mrx_len).
  clearbody B3w.
  unfold truth in SW.
  rewrite mrxk_eqb by lia.
  destruct (Z.eqb_spec (mrx_retry fr) 0) as [R0|R1]; cbv iota.
  - (* retry 0: no backoff *)
    replace (mrx_retry fr =? 0) with true in SW by (symmetry; apply Z.eqb_eq; exact R0).
    cbn [negb] in SW. cbv iota in SW.
    eapply (mrx_data4l TC);
      [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact SW | exact TK
      | rewrite (mrx_asm_be32b _ _ _ _ (mrx_byte_range _ 18) (mrx_byte_range _ 19) (mrx_byte_range _ 20)
                   (mrx_byte_range _ 21));
        do 2 f_equal; unfold mrx_send; symmetry; apply mrx_be32; lia
      | reflexivity .. ].
  - (* 0x156fc-0x1570c: M.backoff_until = g_now + Cfg.backoff_ms * 1000 *)
    replace (mrx_retry fr =? 0) with false in SW by (symmetry; apply Z.eqb_neq; exact R1).
    cbn [negb] in SW. cbv iota in SW.
    do 5 step.
    assert (PB : put 8 (bv_unsigned (Z_to_bv 64 (u_at B3w 65060 4)) * 1000 + g_now B2) =
                 put 8 (u64 (g_now B3w + h_ms_m (Cfg_backoff_ms B3w)))).
    { apply (mrx_put_eqm 8 _ _ 64); [lia|].
      pose proof (u_at_range B3w 65060 4) as RU. change (8 * Z.of_nat 4) with 32 in RU.
      rewrite unsigned_lit by lia. rewrite GN3. unfold u64, h_ms_m, u64.
      change (Cfg_backoff_ms B3w) with (u_at B3w 65060 4).
      rewrite Zmod_mod. rewrite Zplus_mod_idemp_r. f_equal. lia. }
    lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ =>
      rewrite PB in H;
      change (upd B3w 56 (put 8 (u64 (g_now B3w + h_ms_m (Cfg_backoff_ms B3w)))))
        with (set_M_backoff_until B3w (u64 (g_now B3w + h_ms_m (Cfg_backoff_ms B3w)))) in H end.
    eapply (mrx_data4l TC);
      [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact SW | exact TK
      | rewrite (mrx_asm_be32b _ _ _ _ (mrx_byte_range _ 18) (mrx_byte_range _ 19) (mrx_byte_range _ 20)
                   (mrx_byte_range _ 21));
        do 2 f_equal; unfold mrx_send; symmetry; apply mrx_be32; lia
      | reflexivity .. ].
Qed.
