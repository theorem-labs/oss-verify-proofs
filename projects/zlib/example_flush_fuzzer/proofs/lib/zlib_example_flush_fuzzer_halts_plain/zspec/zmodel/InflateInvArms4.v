(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit InflateInvArms1 InflateInvArms3.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

Section Arms.
  Variables (iv : ivariant) (flush : Z) (NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation pinv := (pinv NI NO WN TOT0).
  Local Notation pinv0 := (pinv0 NI NO WN TOT0).
  Local Notation apost := (apost NI NO WN TOT0).

  Hypothesis FAST : forall w, pinv w -> is_mode (w_s w) = LEN -> fastcond iv (w_r w) = true -> DEBT w ->
    gFAST w = true /\ pinv (LOAD (inflate_fast (RESTORE w))) /\ ir_bits (w_r (LOAD (inflate_fast (RESTORE w)))) < 8
    /\ PHI (LOAD (inflate_fast (RESTORE w))) < PHI w.

  Let P_DISTc := P_DIST iv NI NO WN TOT0 NI32 NO32.


  Lemma P_LENEXT : forall w, pinv w -> is_mode (w_s w) = LENEXT -> gLENEXT w = true /\ apost w (arm_LENEXT iv w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    destruct Qlenext as (QL & QE & QLE).
    assert (OL : wrap32 (r_out - r_left) = r_out - r_left) by (apply wrap32_id; glia).
    assert (P2' : 0 < Z.shiftl 1 f_extra) by (rewrite Z.shiftl_1_l; apply Z.pow_pos_nonneg; lia).
    destruct (dist_tab _ SIr eq_refl) as (extD & TD & HextD). cbn [is_codes is_distcode is_distbits] in TD, HextD.
    split.
    { unfold gLENEXT, gDIST, roomok, olen, cp0. cbn [w_s w_r w_c ir_left ir_out ir_put ic_outbuf]. rewrite OL.
      destruct (Z.eqb_spec r_left 0); [reflexivity|]. cbn [orb].
      apply andb_true_intro. split; [repeat (apply andb_true_intro; split); apply Z.leb_le; glia|].
      apply (dtable_ok_of_tab _ extD). cbn [is_distcode is_distbits]. exact TD. }
    unfold arm_LENEXT. wred.
    destruct (Z.eqb_spec f_extra 0) as [E0|E0]; wred.
    - pose proof (wrap32_range f_length) as WL. destruct (iv_aux iv); wred; chain2 P_DISTc; pinv_auto.
    - needbits_run f_extra RIr NI32 NO32 ClNI Cinb.
      2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
      needbits_arun NB r1 RI1. wred. rinv_open RI1.
      pose proof (BITSv_le ho1 f_extra ltac:(lia)) as BV. pose proof (BITSv_bound ho1 f_extra ltac:(lia)) as BV0.
      rewrite (wrap32_id (f_length + BITSv ho1 f_extra)) by glia.
      dropbits f_extra RI1 RI2 NI32 NO32. rinv_open RI2. auxstep.
      destruct (iv_aux iv); wred; chain2 P_DISTc; pinv_auto.
  Qed.


  Lemma LEN_fin : forall w e maxb, pinv0 w -> is_mode (w_s w) = LEN -> term_ok LENS maxb e = true -> code_bits e <= ir_bits (w_r w) ->
    ir_bits (w_r w) - code_bits e < 8 ->
    apost w ((DROPBITS (code_bits e) ;; add_back iv (code_bits e) ;;
            us (fun s => iset_length s (code_val e)) ;;
            if code_op e =? 0 then set_mode LIT
            else if negb (Z.land (code_op e) 32 =? 0) then set_back iv (-1) ;; set_mode TYPE
            else if negb (Z.land (code_op e) 64 =? 0) then go_bad MSG_invalid_literal_length_code
            else us (fun s => iset_extra s (Z.land (code_op e) 15)) ;; set_mode LENEXT ;; arm_LENEXT iv)%am w).
  Proof.
    intros w e maxb PI Hm TE HBe HX8. dworld w. cbn [w_s is_mode w_r ir_bits] in Hm, HBe, HX8. pinv0_open PI. subst f_mode. sinv_triage.
    pose proof (code_val_bound e) as VB. pose proof (code_op_bound e) as OB.
    destruct (term_ok_LENS _ _ TE) as (Be & CL).
    wred. dropbits (code_bits e) RIr RI6 NI32 NO32. rinv_open RI6. auxstep.
    destruct CL as [(Oe & Ve) | [(Oe & Ve & VE) | (Ie & I16)]].
    - rewrite Oe. bsimp. cbn [apost]. arun_post.
    - destruct (op_base_tests _ Oe) as (_ & E64 & E32 & _ & E15 & NZ).
      destruct (Z.eqb_spec (code_op e) 0); [lia|]. rewrite E32, E64, E15. bsimp.
      assert (HX : 0 <= code_op e - 16 <= 15) by lia.
      assert (P2' : 0 < Z.shiftl 1 (code_op e - 16)) by (rewrite Z.shiftl_1_l; apply Z.pow_pos_nonneg; lia).
      chain2 P_LENEXT. pinv_auto.
    -
      destruct (Z.eqb_spec (code_op e) 0) as [Z0|NZ0]. { exfalso. rewrite Z0 in Ie. apply Ie. reflexivity. } bsimp.
      destruct (negb (Z.land (code_op e) 32 =? 0)); wred.
      + auxstep. cbn [apost]. arun_post.
      + destruct (Z.eqb_spec (Z.land (code_op e) 64) 0); [lia|]. bsimp. cbn [apost]. arun_post.
  Qed.


  Lemma pinv_set_back : forall s c r v, pinv (mkW s c r) -> - 2 ^ 31 <= v < 2 ^ 31 ->
    pinv (mkW (iset_back s (sbv iv v (is_back s))) c r).
  Proof.
    intros s c r v PI Hv. revert PI.
    destruct s as [f_mode f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                 f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
                 f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk];
    destruct c as [c_input c_next_in c_avail_in c_outbuf c_next_out c_avail_out c_total_in c_total_out c_adler c_data_type c_msg];
    destruct r as [r_next r_have r_put r_left r_hold r_bits r_in r_out r_ret].
    intros PI. pinv_open PI. wred.
    unfold InflateInv.pinv. cbn [w_s]. split; [assumption|]. split; [| split; [| split; [xinv_close; exact (conj Xret (conj Xno Xol)) | split; [| kinv_close; exact (conj Yck (conj Yhdr (conj Yms (conj Yxck (conj Yhv Ylf)))))]]]].
    - apply LRNGq_mk; [srng_close; conj_solve | exact CIr | exact RIr | exact WI | exact CR].
    - revert SIr. unfold sinv, tables_ok, ctab_ok, tables_rep, ctab_rep.
      cbn -[Z.shiftl tables_okf ctab_okf rep_ok cat arr_get Z.pow Z.add Z.sub Z.le Z.lt codes_live]. exact (fun H => H).
    - revert BI. unfold binv, PEND, lcons, dcons, ccons. cbn -[Z.shiftl Z.land Z.ones Z.shiftr zmask code_at code_op code_bits code_val is_linkop clx Z.pow Z.add Z.sub Z.le Z.lt Z.eqb orb].
      exact (fun H => H).
  Qed.

  Lemma P_LEN : forall w, pinv w -> is_mode (w_s w) = LEN -> gLEN iv w = true /\ apost w (arm_LEN iv w).
  Proof.
    intros w PI Hm.
    destruct (fastcond iv (w_r w)) eqn:FC.
    {
      assert (HD : DEBT w).
      { dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
        destruct (len_tab _ SIr eq_refl) as (extL & TL & HextL). cbn [is_codes is_lencode is_lenbits] in TL, HextL.
        destruct (tab_ok_root _ _ _ _ TL) as (Rl1 & Rl2 & Rl3).
        pose proof (len_rep _ SIr eq_refl) as LREP. cbn [is_codes is_lencode is_lenbits] in LREP.
        binv_use. destruct BI as [B8 | BP].
        - apply (DEBT_small _ _ _ extL); [| cbn [ir_next]; lia | cbn [ir_bits]; exact B8].
          apply (tab_ok_ext LENS (fun i => cat f_codes f_lencode i)); [intros i Hi; rewrite code_at_cat; reflexivity | exact TL].
        - unfold DEBT. cbn [w_s w_r ir_bits ir_hold ir_next]. intros h' Hh' M.
          enough (G : r_bits < lcons (mkIS LEN f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk) h') by lia.
          apply (lcons_pending (cat f_codes f_lencode) f_lenbits extL LREP TL _ r_hold r_bits h');
            [intros; rewrite code_at_cat; reflexivity | reflexivity | lia | lia | exact M | exact BP]. }
      destruct (FAST w PI Hm FC HD) as (GF & PF & _ & MF). split; [unfold gLEN; rewrite FC; exact GF|].
      unfold arm_LEN. unfold fastcond in FC. unfold abind at 1. unfold gr. rewrite FC. unfold amodify, abind. cbn iota.
      set (w1 := LOAD (inflate_fast (RESTORE w))) in *. clearbody w1.
      unfold gs. cbn iota beta. destruct (is_mode (w_s w1) =? TYPE); [| cbn [apost aret]; exact (conj PF MF)].
      destruct w1 as [s1 c1 r1]. rewrite set_back_eq. cbn [apost]. split; [apply pinv_set_back; [exact PF | lia] |].
      revert MF. destruct s1. exact (fun H => H). }
    dworld w. cbn [w_s is_mode] in Hm. cbn [w_r] in FC. pinv_open PI. subst f_mode. sinv_triage.
    assert (OL : wrap32 (r_out - r_left) = r_out - r_left) by (apply wrap32_id; glia).
    destruct (dist_tab _ SIr eq_refl) as (extD & TD & HextD). cbn [is_codes is_distcode is_distbits] in TD, HextD.
    destruct (len_tab _ SIr eq_refl) as (extL & TL & HextL). cbn [is_codes is_lencode is_lenbits] in TL, HextL.
    destruct (tab_ok_root _ _ _ _ TL) as (Rl1 & Rl2 & Rl3).
    split.
    { unfold gLEN. cbn [w_r]. rewrite FC. unfold gDIST, roomok, olen, cp0. cbn [w_s w_r w_c ir_left ir_out ir_put ic_outbuf]. rewrite OL.
      destruct (Z.eqb_spec r_left 0); [reflexivity|]. cbn [orb].
      apply andb_true_intro. split; [repeat (apply andb_true_intro; split); apply Z.leb_le; glia|].
      apply (dtable_ok_of_tab _ extD). cbn [is_distcode is_distbits]. exact TD. }
    unfold arm_LEN. wred. unfold fastcond in FC. cbn [ir_have ir_left ir_bits] in FC. rewrite FC. wred. auxstep.
    assert (HN1 : forall h, 0 <= h -> code_bits (code_at
              (mkIS LEN f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane (sbv iv 0 f_back) f_was f_self_blk)
              f_lencode (BITSv h f_lenbits)) <= 15).
    { intros h Hh. rewrite code_at_cat. cbn [is_codes]. apply (need1_bound LENS _ _ _ h TL Hh). }
    assert (SB0 : - 2 ^ 31 <= sbv iv 0 f_back < 2 ^ 31) by (apply sbv_range; lia).
    decode_run RIr HN1 NI32 NO32 ClNI Cinb.
    2:{ decode_aleave DC r1 RI1. cbn [apost w_s]. leave_post. rinv_open RI1.
        right. eapply Z.lt_le_trans; [exact Hdlt | apply lcons_ge_root; cbn; lia]. }
    decode_arun DC r1 RI1 Hhere Hneed. rinv_open RI1. rewrite code_at_cat in Hhere. cbn [is_codes] in Hhere.
    pose proof (tab_root_entry LENS _ _ _ (BITSv ho1 f_lenbits) TL (BITSv_root ho1 f_lenbits ltac:(lia))) as RE.
    cbv beta in RE. rewrite <- Hhere in RE. destruct RE as (HB & _ & _ & CASES).
    destruct CASES as [[NL TM] | (L' & BB & V & X & SUB)]; [| assert (L : 1 <= code_op here <= 15) by liaq].
    -
      destruct (term_ok_LENS _ _ TM) as (_ & CL).
      assert (ELK : (negb (code_op here =? 0) && (Z.land (code_op here) 240 =? 0)) = false).
      { destruct CL as [(Oe & _) | [(Oe & _) | (Ie & _)]].
        - rewrite Oe. reflexivity.
        - destruct (op_base_tests _ Oe) as (_ & _ & _ & -> & _). destruct (code_op here =? 0); reflexivity.
        - pose proof (land64_240 _ Ie). destruct (Z.eqb_spec (Z.land (code_op here) 240) 0); [liaq|]. destruct (code_op here =? 0); reflexivity. }
      rewrite ELK. wred.
      pose proof (len_rep _ SIr eq_refl) as LREP. cbn [is_codes is_lencode is_lenbits] in LREP.
      rewrite code_at_cat in Hdmin. cbn [is_codes] in Hdmin.
      fin_apply2 LEN_fin here f_lenbits TM; [pinv0_auto | cbn; lia | cbn [w_r ir_bits]].
      destruct (dec1_exit _ _ LREP ltac:(lia) r_hold r_bits ho1 b1 here ltac:(lia) ltac:(lia) Hdpre Hhere NL ltac:(lia) Hdmin) as [DX | [Eb Eh]]; [exact DX|].
      subst ho1. binv_use. destruct BI as [B8 | BP]; [liaq|].
      match type of BP with _ < lcons ?S0 ?hh =>
        rewrite (lcons_term S0 hh here ltac:(liaq) ltac:(cbn; liaq)) in BP; [liaq | rewrite code_at_cat; cbn [is_codes is_lencode is_lenbits]; exact Hhere | exact NL] end.
    -
      destruct (op_link_tests _ L) as (_ & _ & E240 & NZ). rewrite E240. destruct (Z.eqb_spec (code_op here) 0); [lia|]. wred.
      assert (HN2 : forall h, 0 <= h -> (fun here2 => wrap32 (code_bits here + code_bits here2)) (code_at
              (mkIS LEN f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane (sbv iv 0 f_back) f_was f_self_blk)
              f_lencode (code_val here + Z.shiftr (BITSv h (code_bits here + code_op here)) (code_bits here))) <= 30).
      { intros h Hh. rewrite code_at_cat. cbn [is_codes]. apply (need2_bound LENS _ _ extL here h TL Hh L' BB). intros j Hj. apply (proj2 (SUB j Hj)). }
      decode_run RI1 HN2 NI32 NO32 ClNI Cinb.
      2:{ decode_aleave DC r2 RI2. cbn [apost w_s]. leave_post. rinv_open RI2.
          assert (LK : is_linkop (code_op here) = true) by (apply is_linkop_true; lia).
          right. cbv beta in Hdlt.
          rewrite wrap32_id in Hdlt by (match goal with |- context [code_bits here + code_bits ?e2] => pose proof (code_bits_bound e2) end; liaq).
          match goal with |- _ < lcons ?S0 ?hh =>
            rewrite (lcons_link S0 hh here ltac:(liaq) ltac:(cbn; liaq));
              [exact Hdlt | | exact LK | liaq | liaq | cbn; liaq];
            rewrite code_at_cat; cbn [is_codes is_lencode is_lenbits]; rewrite (BITSv_hpre hh ho1 b1 f_lenbits Hdpre0) by liaq; exact Hhere
          end. }
      decode_arun DC r2 RI2 Hhere2 Hneed2. rinv_open RI2. rewrite code_at_cat in Hhere2. cbn [is_codes] in Hhere2.
      set (j := Z.shiftr (BITSv ho0 (code_bits here + code_op here)) (code_bits here)) in Hhere2.
      pose proof (shiftr_BITSv_sub ho0 (code_bits here) (code_op here) ltac:(lia) ltac:(lia)) as Hj.
      destruct (SUB j Hj) as [NL2 TM2]. rewrite <- Hhere2 in TM2.
      pose proof (term_ok_bits _ _ _ TM2) as B2. rewrite (wrap32_id (code_bits here + code_bits here0)) in Hneed2 by liaq.
      wred. dropbits (code_bits here) RI2 RI3 NI32 NO32. rinv_open RI3. auxstep.
      pose proof (len_rep _ SIr eq_refl) as LREP. cbn [is_codes is_lencode is_lenbits] in LREP.
      rewrite code_at_cat in Hdmin. cbn [is_codes] in Hdmin. cbv beta in Hdmin0. rewrite code_at_cat in Hdmin0. cbn [is_codes] in Hdmin0.
      fin_apply2 LEN_fin here0 (15 - f_lenbits) TM2; [pinv0_auto | cbn; liaq | cbn [w_r ir_bits]].
      subst j.
      assert (LK : is_linkop (code_op here) = true) by (apply is_linkop_true; lia).
      pose proof (code_bits_bound here0) as CB0.
      assert (D2 : b0 = b1 \/ (b1 + 8 <= b0 /\ b0 - 8 < f_lenbits + code_bits (cat f_codes f_lencode
                     (code_val here + Z.shiftr (BITSv (htrunc ho0 (b0 - 8)) (f_lenbits + code_op here)) f_lenbits)))).
      { destruct Hdmin0 as [DX | [DX DY]]; [left; exact DX | right; split; [exact DX|]].
        rewrite BB in DY. rewrite wrap32_id in DY by (pose proof (code_bits_bound (cat f_codes f_lencode
            (code_val here + Z.shiftr (BITSv (htrunc ho0 (b0 - 8)) (f_lenbits + code_op here)) f_lenbits))); liaq). exact DY. }
      rewrite BB in Hhere2.
      destruct (dec2_exit _ _ LREP ltac:(liaq) ho1 b1 ho0 b0 here here0 Hhere LK ltac:(liaq) ltac:(liaq) BB ltac:(liaq) ltac:(liaq) ltac:(liaq) Hdpre0 Hhere2 ltac:(liaq) D2)
        as [DX | [Eb Eh]]; [rewrite BB; exact DX|].
      subst ho0.
      destruct (dec1_exit_link _ f_lenbits ltac:(liaq) r_hold r_bits ho1 b1 here ltac:(liaq) ltac:(liaq) Hdpre Hhere BB Hdmin) as [DX | [Eb1 Eh1]]; [liaq|].
      subst ho1. binv_use. destruct BI as [B8 | BP]; [liaq|].
      match type of BP with _ < lcons ?S0 ?hh =>
        rewrite (lcons_link S0 hh here ltac:(liaq) ltac:(cbn; liaq)) in BP;
          [| rewrite code_at_cat; cbn [is_codes is_lencode is_lenbits]; exact Hhere | exact LK | liaq | liaq | cbn; liaq] end.
      rewrite code_at_cat in BP. cbn [is_codes is_lencode] in BP. rewrite BB, <- Hhere2 in BP. liaq.
  Qed.

  Lemma P_LEN_ : forall w, pinv w -> is_mode (w_s w) = LEN_ -> gLEN_ iv w = true /\ apost w (arm_LEN_ iv w).
  Proof.
    intros w PI Hm.
    assert (PI1 : pinv (wset_s w (iset_mode (w_s w) LEN))).
    { dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage. wred. pinv_auto. }
    destruct (P_LEN _ PI1 ltac:(destruct w as [[] c r]; reflexivity)) as [G A].
    split.
    - unfold gLEN_, after. destruct w as [s c r]. exact G.
    - unfold arm_LEN_. destruct w as [s c r]. eapply apost_mono; [| exact A]. cbn [w_s is_mode] in Hm. destruct s; cbn in Hm; subst. phi_auto.
  Qed.
End Arms.
