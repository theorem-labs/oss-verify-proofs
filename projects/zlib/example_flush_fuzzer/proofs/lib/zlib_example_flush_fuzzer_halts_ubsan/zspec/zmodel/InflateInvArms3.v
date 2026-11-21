(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit InflateInvArms1.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.


Lemma forallb_intro : forall {A} (f : A -> bool) l, (forall x, In x l -> f x = true) -> forallb f l = true.
Proof. intros A f l H. apply forallb_forall. exact H. Qed.

Lemma dentry_ok_term : forall maxb e, term_ok DISTS maxb e = true -> dentry_ok e = true.
Proof.
  intros maxb e T. destruct (term_ok_DISTS _ _ T) as (_ & [(O & V & _) | (I & _ & _)]); unfold dentry_ok.
  - apply Bool.orb_true_intro. right. apply Z.leb_le. lia.
  - apply Bool.orb_true_intro. left. apply Bool.negb_true_iff. apply Z.eqb_neq. exact I.
Qed.

Lemma dtable_ok_of_tab : forall s ext,
  tab_ok DISTS (fun i => code_at s (is_distcode s) i) (is_distbits s) ext = true -> dtable_ok s = true.
Proof.
  intros s ext T. destruct (tab_ok_root _ _ _ _ T) as (R1 & R2 & R3). unfold dtable_ok.
  apply andb_true_intro. split; [apply Z.leb_le; lia|].
  apply forallb_intro. intros i Hi. apply zupto_spec in Hi. cbv beta.
  destruct (tab_root_entry DISTS _ _ _ i T Hi) as (B & _ & _ & [[L TM] | (L & BB & V & X & SUB)]).
  - destruct (term_ok_DISTS _ _ TM) as (_ & [(O & Vv & _) | (I & _ & _)]).
    + destruct (op_base_tests _ O) as (_ & _ & _ & E240 & _). rewrite E240. cbn. apply (dentry_ok_term _ _ TM).
    + destruct (Z.eqb_spec (Z.land (code_op (code_at s (is_distcode s) i)) 240) 0) as [E|E].
      * exfalso. exact (land64_240 _ I E).
      * apply (dentry_ok_term _ _ TM).
  - destruct (op_link_tests (code_op (code_at s (is_distcode s) i)) ltac:(lia)) as (_ & _ & E240 & _). rewrite E240. cbn [Z.eqb].
    apply forallb_intro. intros j Hj. apply zupto_spec in Hj.
    destruct (SUB j Hj) as [_ TM]. apply (dentry_ok_term _ _ TM).
Qed.

Section Arms.
  Variables (iv : ivariant) (flush : Z) (NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation pinv := (pinv NI NO WN TOT0).
  Local Notation pinv0 := (pinv0 NI NO WN TOT0).
  Local Notation apost := (apost NI NO WN TOT0).


  Lemma P_MATCH : forall w, pinv w -> is_mode (w_s w) = MATCH -> gMATCH w = true /\ apost w (arm_MATCH iv w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    destruct Qmatch as [QL QO].
    assert (OL : wrap32 (r_out - r_left) = r_out - r_left) by (apply wrap32_id; glia).
    split.
    { unfold gMATCH, roomok, olen. cbn [w_s w_r w_c is_offset ir_left ir_out ir_put ic_outbuf]. rewrite OL.
      destruct (Z.eqb_spec r_left 0); [reflexivity|]. cbn [orb].
      apply andb_true_intro. split; [repeat (apply andb_true_intro; split); apply Z.leb_le; glia|].
      destruct (Z.ltb_spec (r_out - r_left) f_offset); [reflexivity|]. cbn [orb].
      apply andb_true_intro; split; apply Z.leb_le; glia. }
    unfold arm_MATCH. wred. rewrite OL.
    destruct (Z.eqb_spec r_left 0) as [L0|L0]; wred.
    { cbn [apost w_s]. leave_post. }
    rewrite Ssane. cbn [Z.eqb negb].
    set (cp := r_out - r_left).
    destruct (Z.ltb_spec cp f_offset) as [LT|GE].
    -
      rewrite (wrap32_id (f_offset - cp)) by glia.
      replace (if iv_aux iv then true else true) with true by (destruct (iv_aux iv); reflexivity).
      destruct (Z.ltb_spec f_whave (f_offset - cp)) as [BADc|OKc]; wred.
      { cbn [apost]. arun_post. }
      assert (WS : f_wsize = WN) by (destruct WI as (_ & _ & _ & [Z0|E]); glia).
      destruct (Z.ltb_spec f_wnext (f_offset - cp)) as [WR|NW]; wred.
      + rewrite (wrap32_id (f_offset - cp - f_wnext)) by glia.
        set (copy := if f_length <? f_offset - cp - f_wnext then f_length else f_offset - cp - f_wnext).
        assert (Hc : 1 <= copy <= Z.min f_length 258 /\ copy <= f_offset - cp - f_wnext)
          by (subst copy; destruct (Z.ltb_spec f_length (f_offset - cp - f_wnext)); glia).
        set (cpy := if r_left <? copy then r_left else copy).
        assert (Hcpy : 1 <= cpy <= copy /\ cpy <= r_left) by (subst cpy; destruct (Z.ltb_spec r_left copy); glia).
        assert (HF : from_fits (FWin (f_wsize - (f_offset - cp - f_wnext))) cpy r_put WN) by (cbn; glia).
        destruct (match_copy f_window (c_outbuf, r_put, FWin (f_wsize - (f_offset - cp - f_wnext)), cpy)) as [[[ob put'] fr'] c'] eqn:EM. wred.
        destruct (match_copy_spec f_window c_outbuf r_put (FWin (f_wsize - (f_offset - cp - f_wnext))) cpy NO WN ob put' fr' c' ltac:(glia) ltac:(glia) ltac:(glia) Coutb ltac:(rewrite <- (proj1 WI); exact Swinb) HF EM) as (EP & EL & OB).
        rewrite (wrap32_id (f_length - cpy)) by glia. rewrite (wrap32_id (r_left - cpy)) by glia.
        destruct (Z.eqb_spec (f_length - cpy) 0); cbn [apost]; arun_post;
          (cross_close; rewrite EP; replace (c_total_out + (r_out - (r_left - cpy))) with (c_total_out + (r_out - r_left) + cpy) by liaq;
           rewrite (Z.add_assoc TOT0 r_put cpy); apply wrap64_add_eq; exact CR).
      + set (copy := if f_length <? f_offset - cp then f_length else f_offset - cp).
        assert (Hc : 1 <= copy <= Z.min f_length 258 /\ copy <= f_offset - cp)
          by (subst copy; destruct (Z.ltb_spec f_length (f_offset - cp)); glia).
        set (cpy := if r_left <? copy then r_left else copy).
        assert (Hcpy : 1 <= cpy <= copy /\ cpy <= r_left) by (subst cpy; destruct (Z.ltb_spec r_left copy); glia).
        assert (HF : from_fits (FWin (f_wnext - (f_offset - cp))) cpy r_put WN) by (cbn; glia).
        destruct (match_copy f_window (c_outbuf, r_put, FWin (f_wnext - (f_offset - cp)), cpy)) as [[[ob put'] fr'] c'] eqn:EM. wred.
        destruct (match_copy_spec f_window c_outbuf r_put (FWin (f_wnext - (f_offset - cp))) cpy NO WN ob put' fr' c' ltac:(glia) ltac:(glia) ltac:(glia) Coutb ltac:(rewrite <- (proj1 WI); exact Swinb) HF EM) as (EP & EL & OB).
        rewrite (wrap32_id (f_length - cpy)) by glia. rewrite (wrap32_id (r_left - cpy)) by glia.
        destruct (Z.eqb_spec (f_length - cpy) 0); cbn [apost]; arun_post;
          (cross_close; rewrite EP; replace (c_total_out + (r_out - (r_left - cpy))) with (c_total_out + (r_out - r_left) + cpy) by liaq;
           rewrite (Z.add_assoc TOT0 r_put cpy); apply wrap64_add_eq; exact CR).
    -
      wred.
        set (cpy := if r_left <? f_length then r_left else f_length).
        assert (Hcpy : 1 <= cpy <= f_length /\ cpy <= r_left) by (subst cpy; destruct (Z.ltb_spec r_left f_length); glia).
        assert (HF : from_fits (FOut (r_put - f_offset)) cpy r_put WN) by (cbn; glia).
        destruct (match_copy f_window (c_outbuf, r_put, FOut (r_put - f_offset), cpy)) as [[[ob put'] fr'] c'] eqn:EM. wred.
        destruct (match_copy_spec f_window c_outbuf r_put (FOut (r_put - f_offset)) cpy NO WN ob put' fr' c' ltac:(glia) ltac:(glia) ltac:(glia) Coutb ltac:(rewrite <- (proj1 WI); exact Swinb) HF EM) as (EP & EL & OB).
        rewrite (wrap32_id (f_length - cpy)) by glia. rewrite (wrap32_id (r_left - cpy)) by glia.
        destruct (Z.eqb_spec (f_length - cpy) 0); cbn [apost]; arun_post;
          (cross_close; rewrite EP; replace (c_total_out + (r_out - (r_left - cpy))) with (c_total_out + (r_out - r_left) + cpy) by liaq;
           rewrite (Z.add_assoc TOT0 r_put cpy); apply wrap64_add_eq; exact CR).
  Qed.


  Lemma P_DISTEXT : forall w, pinv w -> is_mode (w_s w) = DISTEXT -> gDISTEXT w = true /\ apost w (arm_DISTEXT iv w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    destruct Qdistext as (QL & QO & QE & QOE).
    assert (OL : wrap32 (r_out - r_left) = r_out - r_left) by (apply wrap32_id; glia).
    assert (P2' : 0 < Z.shiftl 1 f_extra) by (rewrite Z.shiftl_1_l; apply Z.pow_pos_nonneg; lia).
    split.
    { unfold gDISTEXT, roomok, olen, cp0. cbn [w_s w_r w_c is_offset is_extra ir_left ir_out ir_put ic_outbuf]. rewrite OL.
      destruct (Z.eqb_spec r_left 0); [reflexivity|]. cbn [orb].
      repeat (apply andb_true_intro; split); apply Z.leb_le; glia. }
    unfold arm_DISTEXT. wred.
    destruct (Z.eqb_spec f_extra 0) as [E0|E0]; wred.
    - chain2 P_MATCH. pinv_auto.
    - needbits_run f_extra RIr NI32 NO32 ClNI Cinb.
      2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
      needbits_arun NB r1 RI1. wred. rinv_open RI1.
      pose proof (BITSv_le ho1 f_extra ltac:(lia)) as BV. pose proof (BITSv_bound ho1 f_extra ltac:(lia)) as BV0.
      rewrite (wrap32_id (f_offset + BITSv ho1 f_extra)) by glia.
      dropbits f_extra RI1 RI2 NI32 NO32. rinv_open RI2.
      auxstep. chain2 P_MATCH. pinv_auto.
  Qed.


  Lemma DIST_fin : forall w e maxb, pinv0 w -> is_mode (w_s w) = DIST -> term_ok DISTS maxb e = true -> code_bits e <= ir_bits (w_r w) ->
    ir_bits (w_r w) - code_bits e < 8 ->
    apost w ((DROPBITS (code_bits e) ;; add_back iv (code_bits e) ;;
            if negb (Z.land (code_op e) 64 =? 0) then go_bad MSG_invalid_distance_code
            else us (fun s => iset_extra (iset_offset s (code_val e)) (Z.land (code_op e) 15)) ;; set_mode DISTEXT ;; arm_DISTEXT iv)%am w).
  Proof.
    intros w e maxb PI Hm TE HBe HX8. dworld w. cbn [w_s is_mode w_r ir_bits] in Hm, HBe, HX8. pinv0_open PI. subst f_mode. sinv_triage.
    pose proof (code_val_bound e) as VB. pose proof (code_op_bound e) as OB.
    destruct (term_ok_DISTS _ _ TE) as (Be & CL).
    wred. dropbits (code_bits e) RIr RI6 NI32 NO32. rinv_open RI6. auxstep.
    destruct CL as [(Oe & Ve & VE) | (Ie & I16 & I32)].
    - destruct (op_base_tests _ Oe) as (_ & E64 & _ & _ & E15 & _). rewrite E64, E15. bsimp.
      assert (HX : 0 <= code_op e - 16 <= 15) by lia.
      chain2 P_DISTEXT. pinv_auto.
    - destruct (Z.eqb_spec (Z.land (code_op e) 64) 0); [lia|]. bsimp. cbn [apost]. arun_post.
  Qed.

  Lemma P_DIST : forall w, pinv w -> is_mode (w_s w) = DIST -> gDIST w = true /\ apost w (arm_DIST iv w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    assert (OL : wrap32 (r_out - r_left) = r_out - r_left) by (apply wrap32_id; glia).
    destruct (dist_tab _ SIr eq_refl) as (extD & TD & HextD). cbn [is_codes is_distcode is_distbits] in TD, HextD.
    destruct (tab_ok_root _ _ _ _ TD) as (Rd1 & Rd2 & Rd3).
    split.
    { unfold gDIST, roomok, olen, cp0. cbn [w_s w_r w_c ir_left ir_out ir_put ic_outbuf]. rewrite OL.
      destruct (Z.eqb_spec r_left 0); [reflexivity|]. cbn [orb].
      apply andb_true_intro. split; [repeat (apply andb_true_intro; split); apply Z.leb_le; glia|].
      apply (dtable_ok_of_tab _ extD). cbn [is_distcode is_distbits]. intros. exact TD. }
    unfold arm_DIST. wred.
    assert (HN1 : forall h, 0 <= h -> code_bits (code_at
              (mkIS DIST f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
              f_distcode (BITSv h f_distbits)) <= 15).
    { intros h Hh. rewrite code_at_cat. cbn [is_codes]. apply (need1_bound DISTS _ _ _ h TD Hh). }
    decode_run RIr HN1 NI32 NO32 ClNI Cinb.
    2:{ decode_aleave DC r1 RI1. cbn [apost w_s]. leave_post. rinv_open RI1.
        right. eapply Z.lt_le_trans; [exact Hdlt | apply dcons_ge_root; cbn; lia]. }
    decode_arun DC r1 RI1 Hhere Hneed. rinv_open RI1. rewrite code_at_cat in Hhere. cbn [is_codes] in Hhere.
    pose proof (tab_root_entry DISTS _ _ _ (BITSv ho1 f_distbits) TD (BITSv_root ho1 f_distbits ltac:(lia))) as RE.
    cbv beta in RE. rewrite <- Hhere in RE. destruct RE as (HB & _ & _ & CASES).
    destruct CASES as [[NL TM] | (L' & BB & V & X & SUB)]; [| assert (L : 1 <= code_op here <= 15) by liaq].
    -
      destruct (term_ok_DISTS _ _ TM) as (_ & CL).
      assert (E240 : (Z.land (code_op here) 240 =? 0) = false).
      { apply Z.eqb_neq. destruct CL as [(Oe & _) | (Ie & _)]; [destruct (op_base_tests _ Oe) as (_ & _ & _ & -> & _); lia | apply land64_240; exact Ie]. }
      rewrite E240. wred.
      pose proof (dist_rep _ SIr eq_refl) as DREP. cbn [is_codes is_distcode is_distbits] in DREP.
      rewrite code_at_cat in Hdmin. cbn [is_codes] in Hdmin.
      fin_apply2 DIST_fin here f_distbits TM; [pinv0_auto | cbn; liaq | cbn [w_r ir_bits]].
      destruct (dec1_exit _ _ DREP ltac:(lia) r_hold r_bits ho1 b1 here ltac:(lia) ltac:(lia) Hdpre Hhere NL ltac:(lia) Hdmin) as [DX | [Eb Eh]]; [exact DX|].
      subst ho1. binv_use. destruct BI as [B8 | BP]; [liaq|].
      match type of BP with _ < dcons ?S0 ?hh =>
        rewrite (dcons_term S0 hh here ltac:(liaq) ltac:(cbn; liaq)) in BP; [liaq | rewrite code_at_cat; cbn [is_codes is_distcode is_distbits]; exact Hhere | exact NL] end.
    -
      destruct (op_link_tests _ L) as (_ & _ & E240 & _). rewrite E240. wred.
      assert (HN2 : forall h, 0 <= h -> (fun here2 => wrap32 (code_bits here + code_bits here2)) (code_at
              (mkIS DIST f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
              f_distcode (code_val here + Z.shiftr (BITSv h (code_bits here + code_op here)) (code_bits here))) <= 30).
      { intros h Hh. rewrite code_at_cat. cbn [is_codes]. apply (need2_bound DISTS _ _ extD here h TD Hh L' BB). intros j Hj. apply (proj2 (SUB j Hj)). }
      decode_run RI1 HN2 NI32 NO32 ClNI Cinb.
      2:{ decode_aleave DC r2 RI2. cbn [apost w_s]. leave_post. rinv_open RI2.
          assert (LK : is_linkop (code_op here) = true) by (apply is_linkop_true; lia).
          right. cbv beta in Hdlt.
          rewrite wrap32_id in Hdlt by (match goal with |- context [code_bits here + code_bits ?e2] => pose proof (code_bits_bound e2) end; liaq).
          match goal with |- _ < dcons ?S0 ?hh =>
            rewrite (dcons_link S0 hh here ltac:(liaq) ltac:(cbn; liaq));
              [exact Hdlt | | exact LK | liaq | liaq | cbn; liaq];
            rewrite code_at_cat; cbn [is_codes is_distcode is_distbits]; rewrite (BITSv_hpre hh ho1 b1 f_distbits Hdpre0) by liaq; exact Hhere
          end. }
      decode_arun DC r2 RI2 Hhere2 Hneed2. rinv_open RI2. rewrite code_at_cat in Hhere2. cbn [is_codes] in Hhere2.
      set (j := Z.shiftr (BITSv ho0 (code_bits here + code_op here)) (code_bits here)) in Hhere2.
      pose proof (shiftr_BITSv_sub ho0 (code_bits here) (code_op here) ltac:(lia) ltac:(lia)) as Hj.
      destruct (SUB j Hj) as [NL2 TM2]. rewrite <- Hhere2 in TM2.
      pose proof (term_ok_bits _ _ _ TM2) as B2. rewrite (wrap32_id (code_bits here + code_bits here0)) in Hneed2 by liaq.
      wred. dropbits (code_bits here) RI2 RI3 NI32 NO32. rinv_open RI3. auxstep.
      pose proof (dist_rep _ SIr eq_refl) as DREP. cbn [is_codes is_distcode is_distbits] in DREP.
      rewrite code_at_cat in Hdmin. cbn [is_codes] in Hdmin. cbv beta in Hdmin0. rewrite code_at_cat in Hdmin0. cbn [is_codes] in Hdmin0.
      fin_apply2 DIST_fin here0 (15 - f_distbits) TM2; [pinv0_auto | cbn; liaq | cbn [w_r ir_bits]].
      subst j.
      assert (LK : is_linkop (code_op here) = true) by (apply is_linkop_true; lia).
      pose proof (code_bits_bound here0) as CB0.
      assert (D2 : b0 = b1 \/ (b1 + 8 <= b0 /\ b0 - 8 < f_distbits + code_bits (cat f_codes f_distcode
                     (code_val here + Z.shiftr (BITSv (htrunc ho0 (b0 - 8)) (f_distbits + code_op here)) f_distbits)))).
      { destruct Hdmin0 as [DX | [DX DY]]; [left; exact DX | right; split; [exact DX|]].
        rewrite BB in DY. rewrite wrap32_id in DY by (pose proof (code_bits_bound (cat f_codes f_distcode
            (code_val here + Z.shiftr (BITSv (htrunc ho0 (b0 - 8)) (f_distbits + code_op here)) f_distbits))); liaq). exact DY. }
      rewrite BB in Hhere2.
      destruct (dec2_exit _ _ DREP ltac:(liaq) ho1 b1 ho0 b0 here here0 Hhere LK ltac:(liaq) ltac:(liaq) BB ltac:(liaq) ltac:(liaq) ltac:(liaq) Hdpre0 Hhere2 ltac:(liaq) D2)
        as [DX | [Eb Eh]]; [rewrite BB; exact DX|].
      subst ho0.
      destruct (dec1_exit_link _ f_distbits ltac:(liaq) r_hold r_bits ho1 b1 here ltac:(liaq) ltac:(liaq) Hdpre Hhere BB Hdmin) as [DX | [Eb1 Eh1]]; [liaq|].
      subst ho1. binv_use. destruct BI as [B8 | BP]; [liaq|].
      match type of BP with _ < dcons ?S0 ?hh =>
        rewrite (dcons_link S0 hh here ltac:(liaq) ltac:(cbn; liaq)) in BP;
          [| rewrite code_at_cat; cbn [is_codes is_distcode is_distbits]; exact Hhere | exact LK | liaq | liaq | cbn; liaq] end.
      rewrite code_at_cat in BP. cbn [is_codes is_distcode] in BP. rewrite BB, <- Hhere2 in BP. liaq.
  Qed.

End Arms.
