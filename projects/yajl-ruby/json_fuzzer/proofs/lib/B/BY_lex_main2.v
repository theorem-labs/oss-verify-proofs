(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Image SFW1_lemmas Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLeaf YajlLex YajlFactsLex YajlFactsBuf YajlFactsDecode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RY_lex_number RY_lex_main1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BYajlAlign BY_ubkit BY_rz BY_lex_rdck BY_lex_kit BY_lex_kw BY_lex_main1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Open Scope yprog_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable K : alexK.
Variable m0 : mem.
Hypothesis ENV : kenvA K.
Hypothesis KP : kpolA K.
Hypothesis SH : alexsh K m0.
Hypothesis NUM : lex_number_stmt K m0.
Hypothesis STR : lex_string_stmt K m0.
Hypothesis CMT : lex_comment_stmt K m0.
Hypothesis BCLR : aybuf_clear_stmt.

Ltac leaf MS1 IA c lx1 tok o st1 :=
  apply evtA_done; cbv beta; unfold loop_post; exists lx1, tok, o, st1;
  split; [ apply MS1; mnav c IA; apply yl_ret
        | split; [ first [ assumption | apply lex_inv_set_error; assumption ]
                 | cbn [tok_post lex_error_code lx_error lx_set_error tok_code]; fin_at ] ].

Lemma lex_table_walk : forall (fuel : nat), loop_walk_at K m0 fuel ->
  forall (lx : ylexer) (rav s2v s6v s9v t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (off start : Z),
  lex_inv lx ->
  alexmem K m0 m (lex_error_code (lx_error lx)) (off + 1) start (wz ((k_L K + 32) / 8 + ASB)) (wz (k_L K + 32)) (wz 3) ->
  0 <= start <= off -> off < zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < S fuel)%nat ->
  9 <= znth (k_txt K) off <= 58 ->
  evtA bsegs (k_P K) (loop_post K m0 (S fuel) lx off start)
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz 0) (wz (znth (k_txt K) off + -9)) (wz 49) a2 a3 a4 a5 a6 a7
          s2v (wz (k_L K + 16)) (wz (k_L K + 24)) (wz ((k_H K + 32) / 8 + ASB)) s6v (wz (k_T K)) (wz (zlength (k_txt K))) s9v (wz ASB) (wz AY_JT_LEX)
          t3 t4 t5 t6)
        (k_F K) (wz 0x83288) (k_fc K) None m (seg_rom bsegs)).
Proof. aceil.
  intros fuel IH. unfold loop_walk_at in IH. intros until start; intros LI LM BS K0 FUEL CR9.
  pose proof LM as (MU & WM & MI & ST & FR & OFF & LX & BC). lex_prep ENV BC. unfold AY_JT_LEX in *.
  pose proof LI as (IU & IO & IL & ICH & IA & IV & IB).
  pose proof (lex_error_code_range (lx_error lx)) as ER.
  pose proof (loop_step_leaf K fuel lx off start ltac:(lia) K0) as MS1. cbv zeta in MS1.
  pose proof (txt_range K m0 SH off) as CR.
  set (c := znth (k_txt K) off) in *.
  polu KP kp_img PIMG. polu KP kp_Ls PLS. polu KP kp_L PL. polu KP kp_Hs PHS. polu KP kp_H PH. polu KP kp_stk PSTK.
  zstepA. zstepA.                                                            (* [comment removed for export] *)
  replace ((c + -9) ≪ 2 + 136032) with (136032 + 4 * (c - 9)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  (* [comment removed for export] *)
  Ltac jgo RD := unfold AY_JT_LEX in RD; cbv delta [jt_ws_b jt_def_b jt_str_b jt_comma_b jt_num_b jt_cmt_b jt_colon_b] in RD;
                 zstepA; zstepA; zstepA; clear RD.
  destruct (Z.eq_dec c 44) as [E44|N44].
  { pose proof (jt_read_lit _ c jt_comma_b MI ltac:(lia) ltac:(unfold jt_class; rewrite E44; reflexivity)) as RD. jgo RD.
    stepA. stepA. leaf MS1 IA c lx TK_comma (off + 1) start. }
  destruct (Z.eq_dec c 58) as [E58|N58].
  { pose proof (jt_read_lit _ c jt_colon_b MI ltac:(lia) ltac:(unfold jt_class; rewrite E58; reflexivity)) as RD. jgo RD.
    stepA. stepA. leaf MS1 IA c lx TK_colon (off + 1) start. }
  destruct (is_lex_ws c) eqn:WS.
  { (* [comment removed for export] *)
    pose proof (jt_read_ws _ c MI WS) as RD. jgo RD.
    zstepA. zstepA. zstoreA ENV.                                             (* [comment removed for export] *)
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.   (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by lia. zstepA. if_cases K3; zify_cond K3. 2:{ kill K3. }   (* [comment removed for export] *)
    eapply evtA_mono; [eapply (IH lx); [exact LI| fin_lexmem| lia| lia| lia]|].
    intros ms Hs. unfold loop_post in Hs |- *. destruct Hs as (lx1 & tok & o1 & st1 & YL & LI1 & TP).
    exists lx1, tok, o1, st1. split; [apply MS1; mnav c IA; exact YL| split; [exact LI1| exact TP]]. }
  destruct (Z.eq_dec c 34) as [E34|N34].
  { (* [comment removed for export] *)
    clear N44 N58 WS.
    pose proof (jt_read_lit _ c jt_str_b MI ltac:(lia) ltac:(unfold jt_class; rewrite E34; reflexivity)) as RD. jgo RD.
    eapply evtA_mono; [eapply STR; [fin_lexmem| lia| lia| lia]|].
    intros ms Hs. unfold loop_post.
    destruct (ylex_string 1 (k_txt K) (zlength (k_txt K)) (off + 1)) as [[tok o] err] eqn:ES. apply sub_post_tok in Hs.
    exists (lx_set_error_opt lx err), tok, o, start.
    split; [apply MS1; mnav c IA; rewrite IV, ?ES; cbv beta iota; apply yl_ret
          | split; [apply lex_inv_set_error_opt; exact LI| rewrite err_upd_set_error_opt; exact Hs]]. }
  destruct ((c =? c_minus) || is_digit c) eqn:ND.
  { (* [comment removed for export] *)
    pose proof (minus_digit_cases c ND) as NDC.
    pose proof (jt_read_num _ c MI WS N34 N44 ND) as RD. jgo RD. clear N44 N58 N34 WS.
    eapply evtA_mono; [eapply NUM; [fin_lexmem| lia| lia| lia]|].
    intros ms Hs. unfold loop_post.
    destruct (ylex_number (k_txt K) (zlength (k_txt K)) off) as [[tok o] err] eqn:EN. apply sub_post_tok in Hs.
    exists (lx_set_error_opt lx err), tok, o, start.
    split; [apply MS1; mnav c IA; rewrite ?ND, ?EN; cbv beta iota; rewrite ?EN; cbv beta iota; apply yl_ret
          | split; [apply lex_inv_set_error_opt; exact LI| rewrite err_upd_set_error_opt; exact Hs]]. }
  pose proof (minus_digit_not c ND) as NDN.
  destruct (Z.eq_dec c 47) as [E47|N47].
  { (* [comment removed for export] *)
    pose proof (jt_read_lit _ c jt_cmt_b MI ltac:(lia) ltac:(unfold jt_class; rewrite E47; reflexivity)) as RD. jgo RD.
    clear N44 N58 N34 WS ND NDN.
    eapply evtA_cut; [eapply CMT; [fin_lexmem| lia| lia| lia]|].
    intros ms Hs.
    pose proof (ylex_comment_spec (k_txt K) (zlength (k_txt K)) (off + 1) ltac:(lia)) as CS.
    destruct (ylex_comment (k_txt K) (zlength (k_txt K)) (off + 1)) as [[tok o] err] eqn:EC.
    destruct tok; cbn [cmt_post] in Hs; try (exfalso; exact (proj2 CS)).
    1,2: apply sub_post_tok in Hs; apply evtA_done; unfold loop_post;
         exists (lx_set_error_opt lx err); eexists; exists o, start;
         split; [apply MS1; mnav c IA; rewrite ?EC; cbv beta iota; apply yl_ret
               | split; [apply lex_inv_set_error_opt; exact LI| rewrite err_upd_set_error_opt; exact Hs]].
    (* [comment removed for export] *)
    destruct CS as (CO & -> & CO2). cbn [err_upd] in Hs.
    destruct Hs as (a0' & rav' & s2' & s6' & s9' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & k112' & m2 & -> & LM2).
    clear MU WM MI ST FR OFF LX BC.
    pose proof LM2 as (MU & WM & MI & ST & FR & OFF & LX & BC).
    unfold kSQ, kAF, kW, lexW, kframe, alex_frame, lxcells, buf_cells in MU, WM, MI, ST, FR, OFF, LX, BC |- *.
    cbn [buf_state_code yb_state yb_len yb_used ybuf_zero] in BC. unfold J_CMT, wz. unfold wz in MU, ST, FR, OFF, LX, BC.
    zstepA. shadow_addr. zstepA.                                             (* [comment removed for export] *)
    shld (rd_shL K m0 _ ENV SH MU WM 16 ltac:(lia)). zstepA. try if_true.    (* [comment removed for export] *)
    zstepA.                                                                  (* [comment removed for export] *)
    stepA.                                                                   (* [comment removed for export] *)
    pose proof (stat_now K m0 _ ENV SH MU WM) as STA1.
    pose proof (shLB_now K m0 _ ENV SH MU WM) as BSH1.
    pose proof (kLB_facts K ENV) as LBF.
    assert (USQ : bv_unsigned (Z_to_bv 64 (bv_unsigned (k_sp K) - 256)) = bv_unsigned (k_sp K) - 256) by (apply unsigned_lit; lia).
    seps ENV.
    pose proof (BCLR (k_P K) (k_LB K) 0 (k_H K + 72) (k_lo K) ybuf_zero) as CLR'. unfold aybuf_clear_rpost in CLR'. cbn [yb_data ybuf_zero app] in CLR'.
    call_spA CLR'; rewrite ?USQ.
    - unfold BA_aybuf_clear. clear -LBF CEILB. split; [lia| Z.div_mod_to_equations; lia].
    - exact STA1.
    - split; [unfold buf_cells; cbn [buf_state_code yb_state yb_len yb_used ybuf_zero]; exact BC| split; [split; reflexivity| cbn; lia]].
    - exact I.
    - reflexivity.
    - unfold buf_inv; cbn. repeat split; try lia; intros X; first [reflexivity| lia| exfalso; apply X; reflexivity].
    - lia.
    - unfold oshadow, block_shadow, A_SB, SIZEOF_BUF. split; [lia|]. split; [lia|]. exact BSH1.
    - unfold oshw_hi, A_SB, amem. cbn. lia.
    - unfold SIZEOF_BUF; aceil. lia.
    - intros X. exfalso. apply X. reflexivity.
    - exact MI.
    - exact ST.
    - aceil. lia.
    - lia.
    - lia.
    - reflexivity.
    - intros a k Ha Hk. apply PSTK; lia.
    - unfold AY_IMG_LO, AY_IMG_HI. intros a k Ha Hk. apply PIMG; lia.
    - unfold opol, SIZEOF_BUF, oshw_lo, oshw_hi, A_SB, amem. split; intros a k Ha Hk; [apply (kp_LB _ KP)| apply (kp_LBs _ KP)]; cbn in *; lia.
    - intros X. exfalso. apply X. reflexivity.
    - (* [comment removed for export] *)
      clear_seps.
      lazymatch goal with H : stk bsegs ?mx (k_lo K) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2; rewrite ?USQ in ST2 end.
      lazymatch goal with H : buf_struct _ _ _ _ _ _ |- _ => destruct H as (BC2 & _ & _ & _); unfold buf_cells, buf_cleared in BC2; cbn [yb_state yb_len yb_used yb_data buf_state_code ybuf_zero] in BC2 end.
      lazymatch goal with H : buf_data _ _ _ _ |- _ => clear H | _ => idtac end.
      try lazymatch goal with H : None <> None -> _ |- _ => clear H end.
      zstepA. shld (rd_shL K m0 _ ENV SH MU WM 28 ltac:(lia)). zstepA. try if_false.   (* [comment removed for export] *)
      zstepA. zstoreA ENV.                                                   (* [comment removed for export] *)
      shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false. (* [comment removed for export] *)
      zstepA. rewrite ?ysx32_small by lia.                                   (* [comment removed for export] *)
      stepA.                                                                 (* [comment removed for export] *)
      zstoreA ENV.                                                           (* [comment removed for export] *)
      shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false. (* [comment removed for export] *)
      zstepA. rewrite ?ysx32_small by lia. zstepA. if_cases K3; zify_cond K3. 2:{ kill K3. }   (* [comment removed for export] *)
      set (lx' := lx_set_buf lx (mkBuf BS_ok 0 0 None []) (lx_bufOff lx) 0).
      assert (LI' : lex_inv lx') by (unfold lex_inv; cbn; repeat split; auto).
      eapply evtA_mono; [eapply (IH lx'); [exact LI'| cbn [lx' lx_error lx_set_buf]; fin_lexmem| lia| lia| lia]|].
      intros ms Hs. unfold loop_post in Hs |- *. destruct Hs as (lx1 & tok1 & o1 & st1 & YL & LI1 & TP).
      exists lx1, tok1, o1, st1. split; [| split; [exact LI1| exact TP]].
      apply MS1. mnav c IA. rewrite ?EC. cbv beta iota.
      rewrite IB. unfold ybuf_clear. cbn [yb_state ybuf_zero ybind yb_len yb_data]. exact YL. }
  (* [comment removed for export] *)
  pose proof (jt_read_def _ c MI ltac:(lia) WS N34 N44 ND N47 N58) as RD. jgo RD.
  zstepA. zstepA. zstepA. shadow_addr. zstepA.                               (* [comment removed for export] *)
  shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)). zstepA. try if_true.      (* [comment removed for export] *)
  stepA. stepA. zstoreA ENV. stepA.                                         (* [comment removed for export] *)
  rewrite ND || idtac.
  leaf MS1 IA c (lx_set_error lx LE_invalid_char) TK_error (off + 1) start.
Qed.
End S.
End RC__1.
