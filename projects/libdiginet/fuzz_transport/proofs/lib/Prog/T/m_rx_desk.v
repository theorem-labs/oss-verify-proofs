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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import m_rx_epi m_rx_body.
Import ListNotations.
Open Scope Z_scope.

(* 0x15528 (the frame is from not-HOST, to HOST or broadcast) to 0x15568: the known desk (bcmp with M.desk) or a new
   one (cmd e0 / e1, the Digidesign OUI, memcpy into M.desk, M.desk_known = 1), then CLOSED drops it. *)
Lemma mrx_desk : bcmp_contract -> memcpy_contract -> desk_named_contract ->
  m_lost_contract -> m_wake_contract -> m_maybe_online_contract -> m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (fr : tframe) (n : Z) (B B' : list byte) (r : Z) (X : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  mrx_fix sp lo fr n ->
  bytes_at rsegs m (tf_addr fr) (tf_bytes fr) ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 8 X; C8 (Z_to_bv 64 (mrx_byte (tf_bytes fr) 24)); C8 (Z_to_bv 64 (mrx_byte (tf_bytes fr) 21));
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B ->
  mrx_desk_m timg_plain fr B = Some (B', r) ->
  x8 = Z_to_bv 64 (tf_addr fr) ->
  x9 = Z_to_bv 64 (tf_addr fr + 6) ->
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
        F (Z_to_bv 64 0x15528) fc None m (seg_rom rsegs)).
Proof.
  intros BC MC DN LC WC MOC TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo fr n B B' r X
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    FX HBYTES MU WM0 MI ST FR WM MDL -> -> -> -> -> -> -> -> -> -> -> ->.
  pose proof FX as FX'. mrx_fix_intro FX'.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts.
  assert (FC : mrx_fc fr = mrx_byte (tf_bytes fr) 28) by (unfold mrx_fc; apply mrx_byte_at; lia).
  pose proof (mrx_byte_range (tf_bytes fr) 28) as RC.
  unfold bcmp_contract, BCMP in BC. unfold memcpy_contract in MC.
  unfold mrx_desk_m, truth in MDL.
  change (M_desk_known B) with (s32_at B 0) in MDL.
  (* 0x15528-0x15534: M.desk_known *)
  step. step. step.
  pose proof (s32_range B 0) as RK.
  step.
  rewrite mrxk_eqb by lia.
  destruct (Z.eqb_spec (s32_at B 0) 0) as [DK0|DK1]; cbv iota.
  2: {
    (* known desk: 0x15538-0x15564 *)
    replace (s32_at B 0 =? 0) with false in MDL by (symmetry; apply Z.eqb_neq; exact DK1).
    cbn [negb] in MDL. cbv iota in MDL.
    do 5 step.
    assert (LD : length (M_desk B) = 6%nat) by (unfold M_desk; apply length_sub; unfold A_M_desk, OFF_M; lia).
    destruct (mrx_bcmp6 (mrx_src fr) (M_desk B) ltac:(unfold mrx_src; apply length_sub; lia) LD)
      as (v & Hv & Rv & Ev).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply BC with (ls := mrx_src fr) (rs := M_desk B) (v := v);
        [ rewrite unsigned_lit by lia; unfold mrx_src; apply mrx_bytes_sub; [exact HBYTES | lia | lia]
        | rewrite unsigned_lit by lia; unfold M_desk, A_M_desk, OFF_M;
          apply (wm_src rsegs W_BASE_PLAIN mm B 4 6); [exact WM | lia | lia | lia]
        | rewrite unsigned_lit by lia; exact Hv
        | mrx_hyp ]
      | wk_post_call rsegs mm ]
    end.
    step. step. step.
    rewrite mrxk_eqb by lia. rewrite Ev.
    destruct (beq_bytes (mrx_src fr) (M_desk B)) eqn:SD; cbn [negb]; cbv iota.
    2: { cbv iota in MDL. injection MDL as EB Er. subst B' r. mrx_fr_merge_tac. mrx_epi_close. }
    pose proof (s32_range B 12) as RS.
    step. step. step. step.
    rewrite mrxk_eqb by lia.
    destruct (Z.eqb_spec (s32_at B 12) 3) as [CL|NCL]; cbv iota.
    { unfold mrx_k in MDL. change (M_state B) with (s32_at B 12) in MDL. rewrite CL in MDL.
      replace (3 =? S_CLOSED) with true in MDL by reflexivity. cbv iota in MDL.
      injection MDL as EB Er. subst B' r. mrx_fr_merge_tac. mrx_epi_close. }
    eapply (mrx_body BC DN LC WC MOC TC);
      [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | exact NCL | exact MDL
      | reflexivity .. ]. }
  (* new desk: 0x155f0-0x15644 *)
  replace (s32_at B 0 =? 0) with true in MDL by (symmetry; apply Z.eqb_eq; exact DK0).
  cbn [negb] in MDL. cbv iota in MDL. rewrite FC in MDL. unfold SPEC_CMD_E0, SPEC_CMD_E1 in MDL.
  step. step. step.
  rewrite mrx_cmd_ann by exact RC.
  destruct ((mrx_byte (tf_bytes fr) 28 =? 224) || (mrx_byte (tf_bytes fr) 28 =? 225)) eqn:CE; cbn [negb]; cbv iota.
  2: { cbn [negb] in MDL. cbv iota in MDL. injection MDL as EB Er. subst B' r.
       step. mrx_fr_merge_tac. mrx_epi_close. }
  cbn [negb] in MDL. cbv iota in MDL.
  step.
  do 5 step.
  destruct (mrx_bcmp3 (mrx_src fr) SPEC_OUI ltac:(unfold mrx_src; rewrite length_sub by lia; lia) eq_refl)
    as (v & Hv & Rv & Ev).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply BC with (ls := mrx_src fr) (rs := SPEC_OUI) (v := v);
      [ rewrite unsigned_lit by lia; unfold mrx_src; apply mrx_bytes_sub; [mrx_hyp | lia | lia]
      | rewrite unsigned_lit by lia; apply mrx_oui_at; mrx_hyp
      | rewrite unsigned_lit by lia; exact Hv
      | mrx_hyp ]
    | wk_post_call rsegs mm ]
  end.
  step.
  rewrite mrxk_eqb by lia. rewrite Ev.
  destruct (beq_bytes (firstn 3 (mrx_src fr)) SPEC_OUI) eqn:OU; cbn [negb]; cbv iota.
  2: { cbn [negb] in MDL. cbv iota in MDL. injection MDL as EB Er. subst B' r.
       step. mrx_fr_merge_tac. mrx_epi_close. }
  cbn [negb] in MDL. cbv iota in MDL.
  (* 0x15618-0x15628: memcpy (M.desk, src, 6) *)
  do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mC end.
  assert (DST : rw_cells rsegs mC 206740 [CB (Z.to_nat 6) (sub B 4 (Z.to_nat 6))])
    by (apply (wm_piece rsegs W_BASE_PLAIN mC B 4 6 206740); [mrx_hyp | lia | lia | lia | lia]).
  eapply evt_cut.
  { eapply MC with (src := mrx_src fr) (junk := sub B 4 (Z.to_nat 6)).
    - rewrite unsigned_lit by lia. unfold mrx_src. apply mrx_bytes_sub; [mrx_hyp | lia | lia].
    - rewrite unsigned_lit by lia. unfold mrx_src. apply length_sub; lia.
    - rewrite !unsigned_lit by lia. exact DST.
    - rewrite !unsigned_lit by lia. lia.
    - mrx_hyp. }
  clear DST.
  intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc [DC BS]]]]]. subst ms'.
  lazymatch type of MUc with munch _ _ ?mm => rename mm into mD end.
  rewrite !unsigned_lit in MUc, DC by lia.
  assert (ST1 : stk rsegs mD lo (bv_unsigned sp + -128)).
  { eapply mrx_stk_fill; [ | exact MUc | exact WMc | exact DC | lia].
    lazymatch goal with H : stk rsegs mC _ _ |- _ => exact H end. }
  clear BS.
  wk_facts. wk_world_after_call rsegs mC mD. transport_after_call rsegs mC mD MUc WMc. clear MUc WMc.
  lazymatch goal with H : mem_inv rsegs mC |- _ => clear H end. try clear mC.
  rewrite (ret_pc_even 87596) by (first [lia | reflexivity]).
  (* 0x1562c-0x15644: M.state of the new desk, M.desk_known = 1 *)
  assert (EST : s32_at (upd B 4 (mrx_src fr)) 12 = M_state (set_M_desk_known (set_M_desk B (mrx_src fr)) 1)).
  { unfold M_state, set_M_desk_known, set_M_desk, A_M_state, A_M_desk_known, A_M_desk, OFF_M.
    change (0 + 12) with 12. change (0 + 0) with 0. change (0 + 4) with 4.
    assert (LS : length (mrx_src fr) = 6%nat) by (unfold mrx_src; apply length_sub; lia).
    symmetry. apply s32_at_upd_out; [lia | lia | right; rewrite length_put; lia |].
    rewrite length_put. rewrite length_upd; lia. }
  pose proof (s32_range (upd B 4 (mrx_src fr)) 12) as RS.
  step. step. step. step. step. step.
  rewrite mrxk_eqb by lia.
  destruct (Z.eqb_spec (s32_at (upd B 4 (mrx_src fr)) 12) 3) as [CL|NCL]; cbv iota.
  { unfold mrx_k in MDL. rewrite <- EST, CL in MDL.
    replace (3 =? S_CLOSED) with true in MDL by reflexivity. cbv iota in MDL.
    injection MDL as EB Er. subst B' r. step. mrx_fr_merge_tac. mrx_epi_close. }
  step.
  lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -128) (C8 _ :: _) |- _ => apply mrx_c8_cb in FR end.
  eapply (mrx_body BC DN LC WC MOC TC);
    [ exact FX | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp | mrx_hyp
    | let HC := fresh in intro HC; apply NCL; rewrite EST; exact HC | exact MDL
    | first [reflexivity | rewrite EST; reflexivity] .. ].
Qed.
