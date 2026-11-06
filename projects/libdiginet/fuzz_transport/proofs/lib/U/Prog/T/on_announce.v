(* The walk of on_announce (transport/src/diginet_session.c:184-221) in the ubsan image, entry 0x17000, against
   on_announce_c.v. The prologue saves ra, s0-s11 in the 304-byte frame and keeps s = &g_s in s0, f in s2, now in s1;
   then:
     0x17044 addi  a1, sp, 160; mv a0, s2; jal diginet_announce_parse    :187 into the local announce a (sp + 160)
     0x17050 beqz  a0, 0x170ac
     0x17054 andi  a0, s0, 7; bnez a0, 0x17288                           the UBSan alignment check of s (trap)
     0x1705c lui / add / ld / addi / sd at s + 0x4708                    :188-189 s->stats.rx_ignored++
     0x17070 the epilogue (on_announce_tail.v oa_epi)
     0x170ac addi  a0, sp, 170; jal diginet_personality_from_name        :191 a.name
     0x170b4 mv    s3, a0; beqz a0, 0x170c8
     0x170bc andi  a0, s0, 7; bnez a0, 0x17288; sd s3, 128(s0)           :192-193 s->personality = p
     0x170c8 on_announce_loop.v oa_cmd: find_mac (:194), then the notices.
   Every branch to 0x17288 (unimp, the UBSan trap) is closed: the alignment checks of s and f by s = &g_s
   (0x33970, 8-aligned) and f mod 8 = 0 (dframe_at), the pointer checks of find_mac's loop by a.unknown = f->body =
   buf + 30 (dframe_at: 0 < buf, buf + length b < 2^64), the check at 0x17164 by s6 = 1 on every path into it. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c bcmp_c diginet_announce_parse_c
  diginet_personality_from_name_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require codec_cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC
  notice_c set_state_c maybe_online_c diginet_session_wake_c on_announce_c
  on_announce_model on_announce_lib on_announce_tail on_announce_cmd.
Import ListNotations.
Open Scope Z_scope.

Theorem on_announce_holds :
  bcmp_contract -> memset_contract -> diginet_announce_parse_contract ->
  diginet_personality_from_name_contract -> diginet_session_wake_contract -> maybe_online_contract ->
  set_state_contract -> notice_contract ->
  on_announce_contract.
Proof.
  intros BCMP MEMSET PARSE PERS WAKE MAYBE SETST NOTICE.
  unfold on_announce_contract, on_announce_ENTRY, on_announce_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo fp buf now b fj B B' TF -> -> -> Hnow DF WM GF HM TFA RR SP16 ST LO WOS MI.
  lazymatch goal with |- evt ?segs _ ?ms =>
    change (evt segs (oa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo B') ms) end.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold w_off_stack in WOS.
  pose proof ST as (Hlo & _ & _).
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  pose proof DF as (FC0 & BB & ABb & FCELLS & ABf & FP8).
  pose proof (fr_code_ok b FC0) as (L30 & _ & N16 & NL).
  pose proof (len_fr_body b FC0) as LBODY.
  pose proof (dframe_cmd m fp buf b fj FCELLS) as DFC.
  pose proof (dframe_body m fp buf b fj FCELLS) as DFB.
  pose proof (frame_body_at m buf b FC0 BB) as BODY.
  pose proof ABb as ABb'. pose proof ABf as ABf'.
  unfold arg_blk, off_world, off_window in ABb', ABf'.
  assert (LB2 : 30 + Z.of_nat (length (fr_body b)) <= Z.of_nat (length b)) by (rewrite LBODY; unfold fr_body_len; lia).
  unfold dframe_cells in FCELLS.
  pose proof (wm_len _ _ _ _ WM) as LB.
  rewrite on_announce_m_eq in HM.
  pose proof (munch_refl [(bv_unsigned sp - 1056, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  rename m into mI.
  carve_frame 104%nat ST. rename FR into FRs.
  carve_frame 40%nat ST. rename FR into Fa.
  lazymatch type of Fa with rw_cells _ _ _ [CB _ ?j] => rename j into aj end.
  carve_frame 28%nat ST. rename FR into Fn2.
  lazymatch type of Fn2 with rw_cells _ _ _ [CB _ ?j] => rename j into jn2 end.
  carve_frame 44%nat ST. rename FR into Fn1.
  lazymatch type of Fn1 with rw_cells _ _ _ [CB _ ?j] => rename j into jn1 end.
  carve_frame 40%nat ST. rename FR into Ff2.
  lazymatch type of Ff2 with rw_cells _ _ _ [CB _ ?j] => rename j into jf2 end.
  carve_frame 32%nat ST. rename FR into Ff1.
  lazymatch type of Ff1 with rw_cells _ _ _ [CB _ ?j] => rename j into jf1 end.
  carve_frame 8%nat ST. rename FR into Fx.
  lazymatch type of Fx with rw_cells _ _ _ [CB _ ?j] => rename j into jx end.
  carve_frame 8%nat ST. rename FR into F0.
  lazymatch type of F0 with rw_cells _ _ _ [CB _ ?j] => rename j into j0 end.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -304)) = bv_unsigned sp + -304) by (apply unsigned_lit; lia).
  (* the prologue: addi sp, sp, -304; sd ra, s0-s11; mv s1, a2; mv s2, a1; mv s0, a0; addi a1, sp, 160; mv a0, s2;
     jal diginet_announce_parse *)
  pose proof Fa as [[[La _] _] _].
  do 20 step.
  eapply evt_cut.
  { eapply (PARSE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _
              fp (bv_unsigned sp + -144) (fr_cmd b) (buf + 30) lo (fr_body b) aj).
    - lia.
    - lia.
    - exact FP8.
    - Z.div_mod_to_equations. lia.
    - unfold fr_cmd, at8, bz. pose proof (bv_unsigned_in_range 8 (nth 28 b (b8 0))) as R8. unfold bv_modulus in R8. exact R8.
    - lia.
    - exact DFC.
    - rewrite LBODY. exact DFB.
    - exact BODY.
    - exact Fa.
    - lia.
    - lia.
    - rewrite Hsp. exact ST.
    - rewrite Hsp. unfold ANN_STACK. lia.
    - rewrite Hsp. unfold ANN_STACK. lia.
    - rewrite Hsp. unfold ANN_STACK. lia.
    - rewrite Hsp. unfold ANN_STACK. lia.
    - exact MI. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & ST2 & ANN).
  subst ms'. rewrite Hsp in MUc, ST2. unfold ANN_STACK in MUc.
  lazymatch type of MUc with munch _ ?mm m2 => transport_after_call rsegs mm m2 MUc WMc end.
  clear MUc WMc MI.
  rewrite (ret_pc_even 0x17050) by (first [lia | reflexivity]).
  rewrite LBODY in ANN |- *.
  (* beqz a0: the parse's code *)
  step. rewrite oa_eqb0 by (pose proof (ann_code_range (fr_cmd b) (fr_body_len b)); lia).
  change DgnLib.DIGINET_OK with 0 in HM.
  destruct (ann_code (fr_cmd b) (fr_body_len b) =? 0) eqn:AC0; cbv iota; cbn [negb] in HM;
    try rewrite AC0 in ANN; cbv iota in ANN.
  2:{ (* not an announce of 33 bytes or more: s->stats.rx_ignored++ (:188-189) *)
    injection HM as <-.
    step. rewrite gs_land7. step. if_false.
    step. step. step. step. step.
    lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
      replace X with (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1))) in H; [rename H into WM1 |] end.
    2:{ unfold set_S_stats_rx_ignored, S_stats_rx_ignored, A_S_stats_rx_ignored, u64. rewrite put_mod64 by lia.
        reflexivity. }
    assert (GF1 : g_fail_next (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1))) <= 1)
      by (unfold set_S_stats_rx_ignored; rewrite gfn_upd by wside; exact GF).
    refine (oa_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo _
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              [CB 8 j0] [CB 8 jx] [CB 32 jf1] [CB 40 jf2] [CB 44 jn1] [CB 28 jn2] [CB 40 aj]
              LO MU WMO MI2 ST2 _ FRs WM1 GF1).
    oa_low_pack. }
  (* the announce parsed (:190-194): diginet_personality_from_name (a.name) *)
  apply Z.eqb_eq, ann_code_ok in AC0. destruct AC0 as [BL33 _].
  assert (LB33 : (33 <= length (fr_body b))%nat) by lia.
  pose proof (bytes_at_firstn _ _ _ 15 BODY ltac:(lia)) as BODY15.
  assert (L15 : length (firstn 15 (fr_body b)) = 15%nat) by (rewrite length_firstn; lia).
  assert (ABu : arg_blk sp 1056 (buf + 30) 15) by (unfold arg_blk, off_world, off_window; lia).
  (* addi a0, sp, 170; jal diginet_personality_from_name *)
  step. step.
  set (tb := ann_name (fr_body b) (firstn 10 (skipn 10 aj))).
  assert (TB : bytes_at rsegs m2 (bv_unsigned sp + -134) tb).
  { pose proof (rw_cells_cell_bytes m2 _ _ 10 (CB 10 tb) ANN ltac:(cells_cbv; reflexivity)) as R.
    cbn [cbytes] in R. replace (bv_unsigned sp + -144 + Z.of_nat 10) with (bv_unsigned sp + -134) in R by lia.
    exact R. }
  assert (TBz : In (b8 0) tb).
  { unfold tb, ann_name, copy_strz. apply in_or_app. right. left. reflexivity. }
  assert (U134 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -134)) = bv_unsigned sp + -134) by (apply unsigned_lit; lia).
  destruct (stk_split rsegs m2 lo (bv_unsigned sp - 1056) (bv_unsigned sp + -304) ST2 ltac:(lia)) as (STl & STh).
  clear ST2.
  eapply evt_cut.
  { eapply (PERS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (bv_unsigned sp - 1056) tb).
    unfold diginet_personality_from_name_pre, DIGINET_PERSONALITY_FROM_NAME_DEPTH.
    rewrite U134, Hsp.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj MI2 (conj STh _))))))).
    - lia.
    - split; [exact TB | exact TBz].
    - right. lia.
    - apply relro_codec. eapply relro_img_move; [exact RR | exact MU | exact WOS].
    - unfold codec_cells.disj, codec_cells.RELRO_BASE, codec_cells.RELRO_LEN. right. lia.
    - lia. }
  intros ms' (? & ? & ? & m3 & Eq & MUc & WMc & MI3 & ST3).
  subst ms'. rewrite Hsp in MUc, ST3. unfold DIGINET_PERSONALITY_FROM_NAME_DEPTH in MUc.
  lazymatch type of MUc with munch _ ?mm m3 => transport_after_call rsegs mm m3 MUc WMc end.
  clear MUc WMc MI2.
  pose proof (stk_merge rsegs m3 lo (bv_unsigned sp - 1056) (bv_unsigned sp + -304) STl ST3 ltac:(lia)) as ST.
  clear STl ST3.
  rewrite (ret_pc_even 0x170b4) by (first [lia | reflexivity]).
  unfold tb. rewrite from_name_res_pv.
  (* mv s3, a0; beqz a0 *)
  step. step.
  destruct (oa_pv_cases B b) as [(P0 & EB1) | (P1 & EB1)].
  - (* no personality: on to 0x170c8 *)
    rewrite P0. rewrite P0, EB1 in HM.
    rewrite oa_eqb0 by lia. cbv iota.
    assert (FCf : rw_cells rsegs _ fp (dframe_cells buf b fj)) by exact FCELLS.
    assert (BODYu : bytes_at rsegs _ (buf + 30) (ann_unknown (fr_body b))) by exact BODY15.
    assert (LU : length (ann_unknown (fr_body b)) = 15%nat) by exact L15.
    refine (oa_cmd BCMP MEMSET NOTICE SETST WAKE MAYBE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              F fc mI lo B' TF now 0 fp buf b fj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              B jx jf1 jf2 jn1 jn2 j0 aj SP16 LO WOS Hnow TFA RR MU WMO MI3 ST F0 Fx Ff1 Ff2 Fn1 Fn2
              ANN La FRs FCf ABf FP8 BODYu LU ABu WM GF _ _ HM).
    all: first [ lia | oa_refl ].
  - (* andi a0, s0, 7; bnez a0; sd s3, 128(s0): s->personality = p *)
    rewrite oa_eqb0 by lia. replace (oa_pv timg_ubsan b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbv iota.
    step. rewrite gs_land7. step. if_false.
    step.
    lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
      replace X with (oa_B1 timg_ubsan B b) in H
        by (rewrite EB1; unfold set_S_personality, A_S_personality; rewrite ?le8_put; reflexivity);
      rename H into WM1 end.
    assert (GF1 : g_fail_next (oa_B1 timg_ubsan B b) <= 1)
      by (rewrite EB1; unfold set_S_personality; rewrite gfn_upd by wside; exact GF).
    assert (FCf : rw_cells rsegs _ fp (dframe_cells buf b fj)) by exact FCELLS.
    assert (BODYu : bytes_at rsegs _ (buf + 30) (ann_unknown (fr_body b))) by exact BODY15.
    assert (LU : length (ann_unknown (fr_body b)) = 15%nat) by exact L15.
    refine (oa_cmd BCMP MEMSET NOTICE SETST WAKE MAYBE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              F fc mI lo B' TF now (oa_pv timg_ubsan b) fp buf b fj
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (oa_B1 timg_ubsan B b) jx jf1 jf2 jn1 jn2 j0 aj SP16 LO WOS Hnow TFA RR MU WMO MI3 ST F0 Fx Ff1 Ff2
              Fn1 Fn2 ANN La FRs FCf ABf FP8 BODYu LU ABu WM1 GF1 _ _ HM).
    all: first [ lia | oa_refl ].
Qed.
