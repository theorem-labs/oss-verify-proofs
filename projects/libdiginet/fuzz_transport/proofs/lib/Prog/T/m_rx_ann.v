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

(* 0x157c0, cmd e0 after its m_lost (world B6, s9 = M.state): m_wake when IDLE and Cfg.auto_wake, then m_tick. *)
Lemma mrx_e0wl : m_wake_contract -> m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (B6 B3 B4 : list byte) (X : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  bv_unsigned sp mod 16 = 0 -> lo + 144 <= bv_unsigned sp -> W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 144 ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 24 X; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B6 ->
  mrx_e0w B6 = Some (B3, tt) ->
  m_tick_m B3 = Some (B4, tt) ->
  x9 = Z_to_bv 64 271704 ->
  x25 = Z_to_bv 64 (M_state B6) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo B4 1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x157c0) fc None m (seg_rom rsegs)).
Proof.
  intros WC TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo B6 B3 B4 X
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    HS16 LO WOF MU WM0 MI ST FR WM SW TK -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
  wk_facts.
  unfold m_wake_contract, m_wake_ENTRY, m_wake_FRAME in WC.
  unfold mrx_e0w, truth, S_IDLE in SW.
  assert (RS6 : -2^31 <= M_state B6 < 2^31) by apply s32_range.
  step.
  rewrite mrxk_eqb by lia.
  destruct (Z.eqb_spec (M_state B6) 0) as [I0|I1]; cbn [negb]; cbv iota.
  2: { replace (M_state B6 =? 0) with false in SW by (symmetry; apply Z.eqb_neq; exact I1).
       cbn [andb] in SW. cbv iota in SW. injection SW as EB3. subst B3.
       eapply (mrx_tick TC);
         [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ]. }
  replace (M_state B6 =? 0) with true in SW by (symmetry; apply Z.eqb_eq; exact I0). cbn [andb] in SW.
  (* 0x157c4-0x157c8: Cfg.auto_wake *)
  step.
  change (s32_at B6 65040) with (Cfg_auto_wake B6) in *.
  assert (RA : -2^31 <= Cfg_auto_wake B6 < 2^31) by apply s32_range.
  step.
  rewrite mrxk_eqb by lia.
  destruct (Z.eqb_spec (Cfg_auto_wake B6) 0) as [A0|A1]; cbv iota.
  { replace (Cfg_auto_wake B6 =? 0) with true in SW by (symmetry; apply Z.eqb_eq; exact A0).
    cbn [negb] in SW. cbv iota in SW. injection SW as EB3. subst B3.
    eapply (mrx_tick TC);
      [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ]. }
  replace (Cfg_auto_wake B6 =? 0) with false in SW by (symmetry; apply Z.eqb_neq; exact A1).
  cbn [negb] in SW. cbv iota in SW.
  destruct (m_wake_m B6) as [[B7 wr]|] eqn:WK; [|discriminate]. injection SW as EB3. subst B3.
  (* 0x157cc-0x157d0: m_wake, then m_tick *)
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply WC with (lo := lo) (B := B6) (B' := B7) (r := wr);
      [ rewrite Hsp; apply mrx_sp16; exact HS16 | rewrite Hsp; mrx_hyp | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | mrx_hyp | mrx_hyp | exact WK ]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; rewrite Hsp in PO; revert ms' PO; wk_post_call rsegs mm ]
  end.
  step.
  eapply (mrx_tick TC);
    [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ].
Qed.

(* 0x15780, once host_offset gave off (s3): OW.desk++, OW.desk_off, desk_named, OW.desk_p, OW.desk_body, then
   cmd e0 (M.foreign = 0, m_lost when ONLINE, 0x157c0) or e1 (M.e1_us, m_maybe_online / the foreign count). *)
Lemma mrx_annc : desk_named_contract ->
  m_lost_contract -> m_wake_contract -> m_maybe_online_contract -> m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (fr : tframe) (n : Z) (B2 B3 B4 : list byte) (X : list byte) (off : Z)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  mrx_fix sp lo fr n ->
  bytes_at rsegs m (tf_addr fr) (tf_bytes fr) ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 24 X; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B2 ->
  mrx_fc fr = 224 \/ mrx_fc fr = 225 ->
  -1 <= off <= 9 ->
  mrx_ann_tail timg_plain fr B2 off = Some (B3, tt) ->
  m_tick_m B3 = Some (B4, tt) ->
  x8 = Z_to_bv 64 (tf_addr fr + 30) ->
  x9 = Z_to_bv 64 271704 ->
  x19 = Z_to_bv 64 off ->
  x21 = Z_to_bv 64 (mrx_fc fr) ->
  x23 = Z_to_bv 64 206736 ->
  x25 = Z_to_bv 64 (M_state B2) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo B4 1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15780) fc None m (seg_rom rsegs)).
Proof.
  intros DN LC WC MOC TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo fr n B2 B3 B4 X off
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    FX HBYTES MU WM0 MI ST FR WM HC HO SW TK -> -> -> -> -> ->.
  pose proof FX as FX'. mrx_fix_intro FX'.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts.
  assert (LB2 : Z.of_nat (length B2) = 65616) by lia.
  assert (RS2 : -2^31 <= M_state B2 < 2^31) by apply s32_range.
  unfold desk_named_contract, desk_named_ENTRY, desk_named_FRAME in DN.
  unfold m_lost_contract, m_lost_ENTRY, m_lost_FRAME in LC.
  unfold mrx_ann_tail, int_inc in SW. destruct (OW_desk B2 =? INT_MAX) eqn:ID; [discriminate|]. cbv beta iota in SW.
  destruct (desk_named_m timg_plain (set_OW_desk_off (set_OW_desk B2 (OW_desk B2 + 1)) off) (mrx_body fr))
    as [[Bd dp]|] eqn:DNM; [|discriminate].
  cbv beta iota in SW.
  (* 0x15780-0x15794: OW.desk, OW.desk_off; desk_named (body) *)
  do 6 step.
  lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ =>
    change (upd (upd B2 65520 (put 4 (s32_at B2 65520 + 1))) 65544 (put 4 off))
      with (set_OW_desk_off (set_OW_desk B2 (OW_desk B2 + 1)) off) in H end.
  set (B3d := set_OW_desk_off (set_OW_desk B2 (OW_desk B2 + 1)) off) in *.
  assert (LB3 : Z.of_nat (length B3d) = 65616) by (unfold B3d; mrx_unf; mrx_len).
  assert (MS3 : M_state B3d = M_state B2) by (unfold B3d; mrx_unf; mrx_rw; reflexivity).
  clearbody B3d.
  assert (LBD : Z.of_nat (length (mrx_body fr)) = Z.of_nat (length (tf_bytes fr)) - 30)
    by (unfold mrx_body; rewrite length_skipn; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BB : bytes_at rsegs mm (tf_addr fr + 30) (mrx_body fr))
      by (pose proof (mrx_bytes_skipn mm (tf_addr fr) (tf_bytes fr) 30 ltac:(mrx_hyp) ltac:(lia)) as H0;
          exact H0);
    eapply evt_cut;
    [ eapply DN with (lo := lo) (B := B3d) (B' := Bd) (p := tf_addr fr + 30) (r := dp) (body := mrx_body fr);
      [ reflexivity | lia | exact BB | unfold off_window; rewrite Hsp; lia
      | rewrite Hsp; apply mrx_sp16; exact HS16 | rewrite Hsp; mrx_hyp | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | mrx_hyp | mrx_hyp | exact DNM ]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; rewrite Hsp in PO; revert ms' PO; wk_post_call rsegs mm ]
  end.
  clear BB.
  lazymatch goal with E : Bd = B3d |- _ => subst Bd end.
  (* 0x15798-0x157a4: OW.desk_p, OW.desk_body; cmd e0? *)
  step. step. step.
  lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ =>
    change (upd (upd B3d 65552 (put 8 dp)) 65560 (put 8 (tf_addr fr + 30)))
      with (set_OW_desk_body (set_OW_desk_p B3d dp) (tf_addr fr + 30)) in H end.
  set (B4d := set_OW_desk_body (set_OW_desk_p B3d dp) (tf_addr fr + 30)) in *.
  assert (LB4 : Z.of_nat (length B4d) = 65616) by (unfold B4d; mrx_unf; mrx_len).
  assert (MS4 : M_state B4d = M_state B2) by (rewrite <- MS3; unfold B4d; mrx_unf; mrx_rw; reflexivity).
  assert (OF4 : OW_foreign (set_M_foreign B4d 1) = OW_foreign B4d) by (mrx_unf; mrx_rw; reflexivity).
  clearbody B4d.
  step.
  rewrite mrxk_eqb by lia.
  destruct (Z.eqb_spec (mrx_fc fr) 224) as [E0|E1]; cbn [negb]; cbv iota.
  - (* cmd e0, 0x157a8-0x157bc *)
    replace (mrx_fc fr =? SPEC_CMD_E0) with true in SW by (symmetry; apply Z.eqb_eq; exact E0). cbv iota in SW.
    unfold mrx_e0 in SW.
    step. step.
    lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ =>
      change (upd B4d 24 (put 4 0)) with (set_M_foreign B4d 0) in H end.
    assert (MS5 : M_state (set_M_foreign B4d 0) = M_state B2) by (rewrite <- MS4; mrx_unf; mrx_rw; reflexivity).
    rewrite MS5 in SW. unfold S_ONLINE in SW.
    step.
    rewrite mrxk_eqb by lia.
    destruct (Z.eqb_spec (M_state B2) 2) as [ON|NON]; cbn [negb]; cbv iota.
    + replace (M_state B2 =? 2) with true in SW by (symmetry; apply Z.eqb_eq; exact ON). cbv iota in SW.
      destruct (m_lost_m (set_M_foreign B4d 0) R_DESK_OFFLINE) as [[B6 []]|] eqn:LM; [|discriminate].
      cbv beta iota in SW.
      step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply LC with (lo := lo) (B := set_M_foreign B4d 0) (B' := B6) (why := 3);
          [ reflexivity | lia | rewrite Hsp; apply mrx_sp16; exact HS16 | rewrite Hsp; mrx_hyp | rewrite Hsp; lia
          | unfold w_off_stack; rewrite Hsp; lia | mrx_hyp | mrx_hyp | exact LM ]
        | let ms' := fresh "ms'" in let PO := fresh "PO" in
          intros ms' PO; rewrite Hsp in PO; revert ms' PO; wk_post_call rsegs mm ]
      end.
      step.
      change (s32_at B6 12) with (M_state B6).
      eapply (mrx_e0wl WC TC);
        [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp
        | exact SW | exact TK | reflexivity | reflexivity ].
    + replace (M_state B2 =? 2) with false in SW by (symmetry; apply Z.eqb_neq; exact NON). cbv beta iota in SW.
      eapply (mrx_e0wl WC TC);
        [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp
        | exact SW | exact TK | reflexivity | rewrite MS5; reflexivity ].
  - (* cmd e1, 0x157d4: off < 0 is a foreign desk *)
    replace (mrx_fc fr =? SPEC_CMD_E0) with false in SW by (symmetry; apply Z.eqb_neq; exact E1). cbv iota in SW.
    unfold mrx_e1 in SW.
    step.
    rewrite mrxk_lts by lia.
    destruct (Z.ltb_spec off 0) as [ON|OP]; cbv iota.
    + (* 0x157f4-0x15814: M.foreign = 1, OW.foreign++, m_lost (R_FOREIGN) when ONLINE or WAKING *)
      replace (0 <=? off) with false in SW by (symmetry; apply Z.leb_gt; exact ON). cbv iota in SW.
      rewrite OF4 in SW. unfold int_inc in SW.
      assert (RF : -2^31 <= OW_foreign B4d < 2^31) by apply s32_range.
      destruct (OW_foreign B4d =? INT_MAX) eqn:FM; [discriminate|]. cbv iota in SW.
      do 6 step.
      lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ =>
        change (upd (upd B4d 24 (put 4 1)) 65524 (put 4 (s32_at B4d 65524 + 1)))
          with (set_OW_foreign (set_M_foreign B4d 1) (OW_foreign B4d + 1)) in H end.
      assert (MS6 : M_state (set_OW_foreign (set_M_foreign B4d 1) (OW_foreign B4d + 1)) = M_state B2)
        by (rewrite <- MS4; mrx_unf; mrx_rw; reflexivity).
      rewrite MS6 in SW. unfold S_ONLINE, S_WAKING in SW.
      step.
      rewrite mrx_state12 by exact RS2.
      destruct ((M_state B2 =? 2) || (M_state B2 =? 1)) eqn:SO; cbn [negb]; cbv iota.
      * cbv iota in SW. step. step.
        eapply (mrx_lost LC TC);
          [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp
          | reflexivity | lia | exact SW | exact TK ].
      * cbv iota in SW. injection SW as EB3. subst B3.
        eapply (mrx_tick TC);
          [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ].
    + (* 0x157d8-0x157e4: M.e1_us = 1, M.foreign = 0, m_maybe_online *)
      replace (0 <=? off) with true in SW by (symmetry; apply Z.leb_le; exact OP). cbv iota in SW.
      step. step. step.
      lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ =>
        rewrite (mrx_comm B4d (put 4 1) (put 4 0) 20 24) in H by mrx_side;
        change (upd (upd B4d 24 (put 4 0)) 20 (put 4 1)) with (set_M_e1_us (set_M_foreign B4d 0) 1) in H end.
      eapply (mrx_mo MOC TC);
        [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp
        | exact SW | exact TK ].
Qed.

(* 0x155c8, round i of host_offset's loop (fuzz_transport.c:258-261, inlined): s2 = body + i, s4 = i, s6 = 10 - i;
   bcmp (body + i, HOST, 6) == 0 gives off = i, ten misses give off = -1 (s3). By induction on the rounds left. *)
Lemma mrx_loopl : bcmp_contract -> desk_named_contract ->
  m_lost_contract -> m_wake_contract -> m_maybe_online_contract -> m_tick_contract ->
  forall (k : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (fr : tframe) (n : Z) (B2 B3 B4 : list byte) (X : list byte) (i off : Z)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Z.of_nat k = 10 - i -> 0 <= i -> (0 < k)%nat ->
  host_offset_loop k (mrx_body fr) i = Some off ->
  mrx_fc fr = 225 -> 33 <= mrx_blen fr ->
  mrx_fix sp lo fr n ->
  bytes_at rsegs m (tf_addr fr) (tf_bytes fr) ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 24 X; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B2 ->
  mrx_ann_tail timg_plain fr B2 off = Some (B3, tt) ->
  m_tick_m B3 = Some (B4, tt) ->
  x8 = Z_to_bv 64 (tf_addr fr + 30) ->
  x9 = Z_to_bv 64 66688 ->
  x18 = Z_to_bv 64 (tf_addr fr + 30 + i) ->
  x19 = Z_to_bv 64 (-1) ->
  x20 = Z_to_bv 64 i ->
  x21 = Z_to_bv 64 (mrx_fc fr) ->
  x22 = Z_to_bv 64 (10 - i) ->
  x23 = Z_to_bv 64 206736 ->
  x24 = Z_to_bv 64 271704 ->
  x25 = Z_to_bv 64 (M_state B2) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo B4 1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x155c8) fc None m (seg_rom rsegs)).
Proof.
  intros BC DN LC WC MOC TC k. induction k as [|k IH];
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo fr n B2 B3 B4 X i off
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      Hk Hi Hk0 HO HF HBL FX HBYTES MU WM0 MI ST FR WM SW TK -> -> -> -> -> -> -> -> -> ->; [lia|].
  pose proof FX as FX'. mrx_fix_intro FX'.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  wk_facts.
  assert (Hi9 : i <= 9) by lia.
  assert (LBF : 63 <= Z.of_nat (length (tf_bytes fr))) by (unfold mrx_blen in HBL; lia).
  unfold bcmp_contract, BCMP in BC.
  (* 0x155c8-0x155d4: bcmp (body + i, HOST, 6) *)
  do 4 step.
  assert (LS : length (sub (mrx_body fr) i 6) = 6%nat)
    by (apply length_sub; [lia | unfold mrx_body; rewrite length_skipn; lia]).
  destruct (mrx_bcmp6 (sub (mrx_body fr) i 6) HOST LS eq_refl) as (v & Hv & Rv & Ev).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply BC with (ls := sub (mrx_body fr) i 6) (rs := HOST) (v := v);
      [ rewrite unsigned_lit by lia; unfold mrx_body; rewrite mrx_sub_skipn by lia;
        replace (tf_addr fr + 30 + i) with (tf_addr fr + (30 + i)) by lia;
        apply mrx_bytes_sub; [mrx_hyp | lia | lia]
      | rewrite unsigned_lit by lia; apply mrx_host_at; mrx_hyp
      | rewrite unsigned_lit by lia; exact Hv
      | mrx_hyp ]
    | wk_post_call rsegs mm ]
  end.
  step.
  rewrite mrxk_eqb by lia. rewrite Ev.
  cbn [host_offset_loop] in HO.
  replace (i + SPEC_MAC <=? SPEC_ANN_UNKNOWN) with true in HO
    by (symmetry; apply Z.leb_le; unfold SPEC_MAC, SPEC_ANN_UNKNOWN; lia).
  replace (Z.of_nat (length (mrx_body fr)) <? i + SPEC_MAC) with false in HO
    by (symmetry; apply Z.ltb_ge; unfold SPEC_MAC, mrx_body; rewrite length_skipn; lia).
  cbv iota in HO.
  destruct (beq_bytes (sub (mrx_body fr) i 6) HOST) eqn:BH; cbv iota; cbv iota in HO.
  - (* found: 0x15778-0x1577c, off = i *)
    injection HO as HO. subst off.
    step. step.
    eapply (mrx_annc DN LC WC MOC TC) with (off := i);
      [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | lia | lia
      | exact SW | exact TK | reflexivity .. ].
  - (* 0x155dc-0x155e8: next round *)
    step. step. step. step.
    rewrite (mrx_addiw1 i) by lia.
    rewrite mrxk_eqb by lia.
    destruct (Z.eqb_spec (10 - i + -1) 0) as [Z0|Z1]; cbn [negb]; cbv iota.
    + (* ten misses: 0x155ec j 0x1577c; off = -1 *)
      assert (K0 : k = 0%nat) by lia. subst k. cbn [host_offset_loop] in HO. injection HO as HO. subst off.
      step. step.
      eapply (mrx_annc DN LC WC MOC TC) with (off := -1);
        [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | lia | lia
        | exact SW | exact TK | reflexivity .. ].
    + eapply (IH ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI _ lo fr n B2 B3 B4 X (i + 1) off);
        [ lia | lia | lia | exact HO | exact HF | exact HBL | exact FX
        | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact SW | exact TK
        | first [ reflexivity | f_equal; lia ] .. ].
Qed.


(* 0x15594, cmd e0 / e1 (fuzz_transport.c:303-330): host_offset (e1, the 10-round bcmp loop at 0x155b0-0x155ec),
   OW.desk, OW.desk_off, desk_named, OW.desk_p, OW.desk_body, then m_lost / m_wake (e0) or m_maybe_online / the
   foreign count and m_lost (e1), then m_tick. *)
Lemma mrx_annl : bcmp_contract -> desk_named_contract ->
  m_lost_contract -> m_wake_contract -> m_maybe_online_contract -> m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (fr : tframe) (n : Z) (B2 B3 B4 : list byte) (X : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  mrx_fix sp lo fr n ->
  bytes_at rsegs m (tf_addr fr) (tf_bytes fr) ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 24 X; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B2 ->
  mrx_fc fr = 224 \/ mrx_fc fr = 225 ->
  mrx_ann timg_plain fr B2 = Some (B3, tt) ->
  m_tick_m B3 = Some (B4, tt) ->
  x8 = Z_to_bv 64 (tf_addr fr + 30) ->
  x9 = Z_to_bv 64 271704 ->
  x14 = Z_to_bv 64 (M_state B2) ->
  x15 = Z_to_bv 64 206736 ->
  x21 = Z_to_bv 64 (mrx_fc fr) ->
  x23 = Z_to_bv 64 (mrx_blen fr) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo B4 1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15594) fc None m (seg_rom rsegs)).
Proof.
  intros BC DN LC WC MOC TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo fr n B2 B3 B4 X
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    FX HBYTES MU WM0 MI ST FR WM HC SW TK -> -> -> -> -> ->.
  pose proof FX as FX'. mrx_fix_intro FX'.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  wk_facts.
  assert (RB : 0 <= mrx_blen fr < 65536)
    by (unfold mrx_blen; pose proof (mrx_be16_range (zs (tf_bytes fr)) 14); lia).
  unfold mrx_ann in SW.
  (* 0x15594-0x15598: body_len < SPEC_ANN_MIN goes to m_tick *)
  step. step.
  rewrite mrxk_ltu by lia.
  destruct (Z.ltb_spec (mrx_blen fr) 33) as [BS|BL]; cbv iota.
  { replace (mrx_blen fr <? SPEC_ANN_MIN) with true in SW by (symmetry; apply Z.ltb_lt; exact BS).
    cbv iota in SW. injection SW as EB3. subst B3.
    eapply (mrx_tick TC);
      [ exact HS16 | exact LO | exact WOF | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact TK ]. }
  replace (mrx_blen fr <? SPEC_ANN_MIN) with false in SW by (symmetry; apply Z.ltb_ge; exact BL).
  cbv iota in SW.
  (* 0x1559c-0x155ac: s9 = M.state, s7 = &M, s3 = -1; e1 runs host_offset *)
  do 5 step.
  rewrite mrxk_eqb by lia.
  destruct (Z.eqb_spec (mrx_fc fr) 225) as [F1|F0]; cbn [negb]; cbv iota.
  - replace (mrx_fc fr =? SPEC_CMD_E1) with true in SW by (symmetry; apply Z.eqb_eq; exact F1).
    cbv iota in SW. unfold host_offset_m in SW.
    destruct (host_offset_loop 10 (mrx_body fr) 0) as [off|] eqn:HO; [|discriminate]. cbv iota in SW.
    (* 0x155b0-0x155c4 *)
    do 6 step.
    eapply (mrx_loopl BC DN LC WC MOC TC 10%nat ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI _ lo fr n
              B2 B3 B4 X 0 off);
      [ lia | lia | lia | exact HO | exact F1 | lia | exact FX
      | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact SW | exact TK
      | first [ reflexivity | f_equal; lia ] .. ].
  - replace (mrx_fc fr =? SPEC_CMD_E1) with false in SW by (symmetry; apply Z.eqb_neq; exact F0).
    cbv iota in SW.
    eapply (mrx_annc DN LC WC MOC TC) with (off := -1);
      [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact HC | lia
      | exact SW | exact TK | reflexivity .. ].
Qed.
