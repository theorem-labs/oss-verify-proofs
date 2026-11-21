(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb
  InftreesCoverage ItCovIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit InflateInvCov InflateInvArms1 InflateInvArms3 InflateInvArms4.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.


Lemma order_cover : forall s, 0 <= s < 19 -> exists i, 0 <= i < 19 /\ arr_get order_a i = s.
Proof.
  intros s Hs.
  assert (C : forallb (fun s => existsb (fun i => arr_get order_a i =? s) (zupto 19)) (zupto 19) = true) by (vm_compute; reflexivity).
  pose proof (forallb_zupto _ _ C s Hs) as E. cbv beta in E.
  apply existsb_exists in E. destruct E as (i & Hi & Ei). apply zupto_spec in Hi. apply Z.eqb_eq in Ei. exists i. split; assumption.
Qed.

Lemma order_range : forall i, 0 <= i < 19 -> 0 <= arr_get order_a i < 19.
Proof.
  intros i Hi.
  assert (C : forallb (fun i => (0 <=? arr_get order_a i) && (arr_get order_a i <? 19)) (zupto 19) = true) by (vm_compute; reflexivity).
  pose proof (forallb_zupto _ _ C i Hi) as E. cbv beta in E. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.


Lemma lens_repeat_loop : forall n lens have copy lens' have' c' B,
  Z.of_nat n = copy -> 0 <= have -> 0 <= copy -> have + copy <= arr_len lens -> arr_len lens < 2 ^ 31 -> 0 <= B <= 15 ->
  loopZ copy (fun st : arr * Z * Z => let '(lens, have, copy) := st in
     if negb (copy =? 0) then (true, (arr_set lens have (wrap16 B), wrap32 (have + 1), wrap32 (copy - 1)))
     else (false, (lens, have, copy))) (lens, have, copy) = (lens', have', c') ->
  have' = have + copy /\ arr_len lens' = arr_len lens
  /\ (forall i, 0 <= arr_get lens i <= 15 \/ have <= i < have + copy -> 0 <= arr_get lens' i <= 15)
  /\ (forall i, ~ (have <= i < have + copy) -> arr_get lens' i = arr_get lens i).
Proof.
  induction n as [|n IH]; intros lens have copy lens' have' c' B Hn Hh Hc Hhc HL HB E.
  - rewrite loopZ_le0 in E by lia. injection E; intros <- <- <-. split; [lia|]. split; [reflexivity|].
    split; [intros i [Hi|Hi]; [exact Hi | lia] | intros; reflexivity].
  - rewrite loopZ_step in E by lia. cbv beta iota zeta in E.
    destruct (Z.eqb_spec copy 0) as [C0|C0]; [lia|]. cbn [negb] in E.
    rewrite (wrap32_id (have + 1)), (wrap32_id (copy - 1)) in E by lia.
    pose proof (IH (arr_set lens have (wrap16 B)) (have + 1) (copy - 1) lens' have' c' B
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite arr_len_set; lia) ltac:(rewrite arr_len_set; lia) HB E) as (A1 & A2 & A3 & A4).
    split; [lia|]. split; [rewrite A2; apply arr_len_set|].
    assert (W16 : wrap16 B = B) by (apply wrap16_id; lia).
    split.
    + intros i Hi. apply A3. rewrite arr_get_set. unfold arr_inb. destruct (Z.eqb_spec have i).
      * subst i. replace ((0 <=? have) && (have <? arr_len lens)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        cbn [andb]. rewrite W16. left. lia.
      * cbn [andb]. destruct Hi as [Hi|Hi]; [left; exact Hi | right; lia].
    + intros i Hi. rewrite A4 by lia. rewrite arr_get_set. destruct (Z.eqb_spec have i); [lia|]. reflexivity.
Qed.

Lemma lens_repeat_run : forall copy len s c r,
  0 <= is_have s -> 0 <= copy -> is_have s + copy <= arr_len (is_lens s) -> arr_len (is_lens s) < 2 ^ 31 -> 0 <= len <= 15 ->
  exists lens', lens_repeat copy len (mkW s c r) = ARun tt (mkW (iset_have (iset_lens s lens') (is_have s + copy)) c r)
    /\ arr_len lens' = arr_len (is_lens s)
    /\ (forall i, 0 <= arr_get (is_lens s) i <= 15 \/ is_have s <= i < is_have s + copy -> 0 <= arr_get lens' i <= 15)
    /\ (forall i, ~ (is_have s <= i < is_have s + copy) -> arr_get lens' i = arr_get (is_lens s) i).
Proof.
  intros copy len s c r Hh Hc Hhc HL Hlen. unfold lens_repeat, us. cbn [w_s wset_s].
  destruct (loopZ copy _ (is_lens s, is_have s, copy)) as [[lens' have'] c'] eqn:E.
  destruct (lens_repeat_loop (Z.to_nat copy) (is_lens s) (is_have s) copy lens' have' c' len ltac:(lia) Hh Hc Hhc HL Hlen E) as (A1 & A2 & A3 & A4).
  exists lens'. subst have'. split; [reflexivity|]. split; [exact A2|]. split; [exact A3 | exact A4].
Qed.

Section Arms.
  Variables (NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation pinv := (pinv NI NO WN TOT0).
  Local Notation apost := (apost NI NO WN TOT0).


  Lemma LL1 : forall k w, pinv w -> is_mode (w_s w) = LENLENS ->
    match lenlens_while1 k w with
    | ARun _ w' => pinv w' /\ is_mode (w_s w') = LENLENS /\ wle w w'
    | ALeave w' => LRNGq NI NO WN TOT0 w' /\ sinv (w_s w') /\ binv w' /\ cks (w_s w') /\ xinv w' /\ cinv w'
    | ARet _ _ => False
    end.
  Proof.
    induction k as [|k IH]; intros w PI Hm.
    { cbn. split; [assumption|]. split; [assumption | apply wle_refl]. }
    cbn [lenlens_while1]. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    destruct Qlenlens as (QN & QD & QC & QH & QL).
    wred. destruct (Z.ltb_spec f_have f_ncode) as [LT|GE]; wred.
    2:{ split; [| split; [reflexivity | apply wle_refl]]. pinv_auto. }
    needbits_run 3 RIr NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. rinv_open RI1. leave_post5. }
    needbits_arun NB r1 RI1. wred. rinv_open RI1.
    pose proof (BITSv_bound ho1 3 ltac:(lia)) as B3. change (2 ^ 3) with 8 in B3.
    rewrite (wrap32_id (f_have + 1)) by glia.
    dropbits 3%Z RI1 RI2 NI32 NO32. rinv_open RI2.
    pose proof (order_range f_have ltac:(liaq)) as OR.
    match goal with |- match lenlens_while1 k ?W with _ => _ end => enough (PW : pinv W);
      [pose proof (IH W PW eq_refl) as IHW; destruct (lenlens_while1 k W) as [? ?|?|? ?];
       [destruct IHW as (P1 & P2 & P3); split; [exact P1 | split; [exact P2 | eapply wle_trans; [| exact P3]; unfold wle; cbn [w_r ir_left ir_bits ir_have]; lia]]
       | exact IHW | exact IHW] |] end.
    pinv_auto.
    - rewrite arr_len_set. exact Alens.
    - intros _. split; [lia|]. split; [lia|]. split; [lia|]. split; [glia|]. intros i Hi. rewrite arr_get_set. unfold arr_inb. rewrite Alens.
      destruct (Z.eqb_spec (arr_get order_a f_have) (arr_get order_a i)).
      + replace ((0 <=? arr_get order_a f_have) && (arr_get order_a f_have <? 320)) with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        cbn [andb]. rewrite wrap16_id by lia. lia.
      + cbn [andb]. destruct (Z.eq_dec i f_have); [subst; congruence|]. apply QL. lia.
  Qed.

  Lemma LL2 : forall k w, pinv w -> is_mode (w_s w) = LENLENS -> 19 - is_have (w_s w) <= Z.of_nat k ->
    exists w', lenlens_while2 k w = ARun tt w' /\ pinv w' /\ is_mode (w_s w') = LENLENS /\ is_have (w_s w') = 19
      /\ w_r w' = w_r w /\ w_c w' = w_c w.
  Proof.
    induction k as [|k IH]; intros w PI Hm Hk.
    { cbn. exists w. split; [reflexivity|]. split; [exact PI|]. split; [exact Hm|].
      dworld w. cbn [w_s is_mode is_have] in Hm, Hk |- *. pinv_open PI. subst f_mode. sinv_triage.
      destruct Qlenlens as (QN & QD & QC & QH & QL). split; [lia|]. split; reflexivity. }
    cbn [lenlens_while2]. pose proof PI as PI0. dworld w. cbn [w_s is_mode is_have] in Hm, Hk. pinv_open PI. subst f_mode. sinv_triage.
    destruct Qlenlens as (QN & QD & QC & QH & QL).
    wred. destruct (Z.ltb_spec f_have 19) as [LT|GE]; wred.
    2:{ eexists. split; [reflexivity|]. cbn [w_s w_r w_c is_mode is_have]. split; [exact PI0|]. repeat split; try reflexivity. lia. }
    rewrite (wrap32_id (f_have + 1)) by glia. change (wrap16 0) with 0.
    pose proof (order_range f_have ltac:(lia)) as OR.
    match goal with |- exists w', lenlens_while2 k ?W = _ /\ _ => destruct (IH W) as (w' & E & P & M & H19 & Er & Ec) end.
    - pinv_auto.
      + rewrite arr_len_set. exact Alens.
      + intros _. split; [lia|]. split; [lia|]. split; [lia|]. split; [glia|]. intros i Hi. rewrite arr_get_set. unfold arr_inb. rewrite Alens.
        destruct (Z.eqb_spec (arr_get order_a f_have) (arr_get order_a i)).
        * replace ((0 <=? arr_get order_a f_have) && (arr_get order_a f_have <? 320)) with true
            by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
          cbn [andb]. lia.
        * cbn [andb]. destruct (Z.eq_dec i f_have); [subst; congruence|]. apply QL. lia.
    - reflexivity.
    - cbn [w_s is_have]. lia.
    - exists w'. split; [exact E|]. split; [exact P|]. split; [exact M|]. split; [exact H19|]. cbn [w_r w_c] in Er, Ec. split; assumption.
  Qed.


  Lemma code_tab : forall s, sinv s -> is_mode s = CODELENS ->
    is_lencode s = CDyn 0 /\ is_next s <= 1444 /\ tab_ok CODES (fun i => cat (is_codes s) (CDyn 0) i) (is_lenbits s) (is_next s) = true.
  Proof.
    intros s SI M. destruct SI as (_ & _ & _ & _ & _ & QC & _). destruct (QC M) as (_ & _ & _ & CT & _).
    unfold ctab_ok in CT. destruct (ctab_ok_cases _ _ _ _ CT) as (A & B & C). split; [exact A|]. split; [exact B | exact C].
  Qed.

  Lemma CB : forall w, pinv w -> is_mode (w_s w) = CODELENS -> is_have (w_s w) < is_nlen (w_s w) + is_ndist (w_s w) ->
    match codelens_body w with
    | ARun c w' => pinv w' /\ is_nlen (w_s w') = is_nlen (w_s w) /\ is_ndist (w_s w') = is_ndist (w_s w)
                   /\ (c = true -> is_mode (w_s w') = CODELENS /\ is_have (w_s w) + 1 <= is_have (w_s w') /\ ir_bits (w_r w') < 8)
                   /\ (c = false -> is_mode (w_s w') = BAD)
                   /\ wle w w'
    | ALeave w' => LRNGq NI NO WN TOT0 w' /\ sinv (w_s w') /\ binv w' /\ cks (w_s w') /\ xinv w' /\ cinv w'
    | ARet _ _ => False
    end.
  Proof.
    intros w PI Hm Hhv. dworld w. cbn [w_s is_mode is_have is_nlen is_ndist] in Hm, Hhv |- *. pinv_open PI. subst f_mode. sinv_triage.
    destruct Qcodelens as (QN & QD & QH & QCT & QL15).
    destruct (code_tab _ SIr eq_refl) as (ELC & NX & TC). cbn [is_lencode is_next is_codes is_lenbits] in ELC, NX, TC. subst f_lencode.
    pose proof (code_rep _ SIr eq_refl) as CREP. cbn [is_codes is_lencode is_lenbits] in CREP.
    destruct (tab_ok_root _ _ _ _ TC) as (Rc1 & Rc2 & Rc3).
    unfold codelens_body. wred.
    assert (HN1 : forall h, 0 <= h -> code_bits (code_at
              (mkIS CODELENS f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra (CDyn 0) f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
              (CDyn 0) (BITSv h f_lenbits)) <= 15).
    { intros h Hh. rewrite code_at_cat. cbn [is_codes]. apply (need1_bound CODES _ _ _ h TC Hh). }
    decode_run RIr HN1 NI32 NO32 ClNI Cinb.
    2:{ decode_aleave DC r1 RI1. rinv_open RI1. leave_post5. right. split; [| lia].
        match goal with |- _ < ccons ?S0 ?hh =>
          rewrite (ccons_eq S0 hh _ ltac:(lia) ltac:(cbn; lia) eq_refl); pose proof (clx_range (code_val (code_at S0 (is_lencode S0) (BITSv hh (is_lenbits S0))))) end.
        cbn [is_lencode is_lenbits] in *. lia. }
    decode_arun DC r1 RI1 Hhere Hneed. rinv_open RI1. rewrite code_at_cat in Hhere. cbn [is_codes] in Hhere.
    rewrite code_at_cat in Hdmin. cbn [is_codes] in Hdmin.
    pose proof (tab_root_entry CODES _ _ _ (BITSv ho1 f_lenbits) TC (BITSv_root ho1 f_lenbits ltac:(lia))) as RT. cbv beta in RT. rewrite <- Hhere in RT.
    destruct RT as (HB & _ & _ & RCASE).
    pose proof (code_val_bound here) as VB.
    assert (STABLE : forall h', hpre h' b1 ho1 -> 0 <= h' -> code_at
              (mkIS CODELENS f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra (CDyn 0) f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
              (CDyn 0) (BITSv h' f_lenbits) = here).
    { intros h' P Hh'. rewrite code_at_cat. cbn [is_codes]. rewrite Hhere. rewrite !BITSv_idx by lia.
      destruct RCASE as [[NL TM] | (OP & BB & _)].
      - apply (root_stable _ _ CREP ltac:(liaq) ho1 h' b1 ltac:(liaq)); try (rewrite <- BITSv_idx by liaq; rewrite <- Hhere).
        + unfold hpre, htrunc in P. rewrite P. symmetry. apply Z.mod_small. lia.
        + exact NL. + lia. + lia.
      - apply (root_same _ f_lenbits ltac:(lia) ho1 h' b1 ltac:(lia)).
        + unfold hpre, htrunc in P. rewrite P. symmetry. apply Z.mod_small. lia.
        + liaq. }
    assert (EX1 : b1 - code_bits here < 8 \/ (b1 = r_bits /\ ho1 = r_hold)).
    { destruct RCASE as [[NL TM] | (OP & BB & _)].
      - exact (dec1_exit _ _ CREP ltac:(lia) r_hold r_bits ho1 b1 here ltac:(lia) ltac:(lia) Hdpre Hhere NL ltac:(lia) Hdmin).
      - pose proof (dec1_exit_link _ f_lenbits ltac:(lia) r_hold r_bits ho1 b1 here ltac:(lia) ltac:(lia) Hdpre Hhere BB Hdmin). liaq. }
    assert (EX0 : b1 = r_bits -> ho1 = r_hold -> r_bits < 8 \/ r_bits < code_bits here + clx (code_val here)).
    { intros -> ->. binv_use. destruct BI as [B8 | [BP _]]; [left; exact B8 | right].
      match type of BP with _ < ccons ?S0 ?hh => rewrite (ccons_eq S0 hh here ltac:(lia) ltac:(cbn; lia)) in BP end.
      - exact BP.
      - rewrite code_at_cat. cbn [is_codes is_lencode is_lenbits]. exact Hhere. }
    destruct (Z.ltb_spec (code_val here) 16) as [V16|V16]; wred.
    -
      dropbits (code_bits here) RI1 RI2 NI32 NO32. rinv_open RI2.
      rewrite (wrap32_id (f_have + 1)) by glia. rewrite (wrap16_id (code_val here)) by lia.
      assert (B8' : b1 - code_bits here < 8).
      { destruct EX1 as [X | [Eb Eh]]; [exact X|]. destruct (EX0 Eb Eh) as [X|X]; [liaq|].
        unfold clx in X. replace (code_val here <? 16) with true in X by (symmetry; apply Z.ltb_lt; lia). liaq. }
      split; [| split; [reflexivity | split; [reflexivity | split; [intros _; split; [reflexivity | split; [liaq | cbn [w_r ir_bits]; liaq]] | split; [intros X; discriminate X | unfold wle; cbn [w_r ir_left ir_bits ir_have]; liaq]]]]].
      pinv_auto.
      + rewrite arr_len_set. exact Alens.
      + intros _. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact QCT|].
        intros i Hi. rewrite arr_get_set. unfold arr_inb. rewrite Alens.
        destruct (Z.eqb_spec f_have i).
        * subst i. replace ((0 <=? f_have) && (f_have <? 320)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; liaq). cbn. lia.
        * cbn [andb]. apply QL15. liaq.
    -
      assert (REP : forall len copy n2 h2 ho2 b2,
        0 <= len <= 15 -> 3 <= copy <= 138 ->
        RINV NI NO (mkIR n2 h2 r_put r_left ho2 b2 r_in r_out r_ret) -> b2 < 8 -> b2 + 8 * h2 <= r_bits + 8 * r_have -> h2 <= r_have ->
        match (do s <- gs (fun s => s) ;
               if is_nlen s + is_ndist s <? is_have s + copy then go_bad MSG_invalid_bit_length_repeat ;; aret false
               else lens_repeat copy len ;; aret true)%am
              (mkW (mkIS CODELENS f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra (CDyn 0) f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
                   (mkIC c_input c_next_in c_avail_in c_outbuf c_next_out c_avail_out c_total_in c_total_out c_adler c_data_type c_msg)
                   (mkIR n2 h2 r_put r_left ho2 b2 r_in r_out r_ret)) with
        | ARun c w' => pinv w' /\ is_nlen (w_s w') = f_nlen /\ is_ndist (w_s w') = f_ndist
                       /\ (c = true -> is_mode (w_s w') = CODELENS /\ f_have + 1 <= is_have (w_s w') /\ ir_bits (w_r w') < 8)
                       /\ (c = false -> is_mode (w_s w') = BAD)
                       /\ wle (mkW (mkIS CODELENS f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra (CDyn 0) f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
                   (mkIC c_input c_next_in c_avail_in c_outbuf c_next_out c_avail_out c_total_in c_total_out c_adler c_data_type c_msg)
                   (mkIR r_next r_have r_put r_left r_hold r_bits r_in r_out r_ret)) w'
        | ALeave w' => LRNGq NI NO WN TOT0 w' /\ sinv (w_s w') /\ binv w' /\ cks (w_s w') /\ xinv w' /\ cinv w'
        | ARet _ _ => False
        end).
      { intros len copy n2 h2 ho2 b2 Hlen Hcopy RI5 B28 TLE HLE. rinv_open RI5. wred.
        destruct (Z.ltb_spec (f_nlen + f_ndist) (f_have + copy)) as [OV|OV]; wred.
        - cbn [w_s w_r is_nlen is_ndist is_mode ir_bits].
          split; [pinv_auto | split; [reflexivity | split; [reflexivity | split; [intros X; discriminate X | split; [intros _; reflexivity | unfold wle; cbn [w_r ir_left ir_bits ir_have]; lia]]]]].
        - destruct (lens_repeat_run copy len
                     (mkIS CODELENS f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                        f_window f_window_blk f_hold f_bits f_length f_offset f_extra (CDyn 0) f_distcode f_lenbits f_distbits
                        f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
                     (mkIC c_input c_next_in c_avail_in c_outbuf c_next_out c_avail_out c_total_in c_total_out c_adler c_data_type c_msg)
                     (mkIR n2 h2 r_put r_left ho2 b2 r_in r_out r_ret)
                     ltac:(cbn; liaq) ltac:(liaq) ltac:(cbn; liaq) ltac:(cbn; liaq) Hlen) as (lens' & E & L1 & L2 & L3).
          cbn [is_have is_lens] in E, L1, L2, L3. rewrite E. wred. cbn [w_s w_r is_nlen is_ndist is_mode is_have ir_bits].
          split; [| split; [reflexivity | split; [reflexivity | split; [intros _; split; [reflexivity | split; [lia | exact B28]] | split; [intros X; discriminate X | unfold wle; cbn [w_r ir_left ir_bits ir_have]; lia]]]]].
          pinv_auto.
          {
            destruct Sarrb as (AL & AW & AC). split; [| split; [exact AW | exact AC]].
            intros i Hi. destruct (Z_lt_le_dec i f_have) as [Hlt|Hge]; [| destruct (Z_lt_le_dec i (f_have + copy)) as [Hlt2|Hge2]].
            - pose proof (L2 i (or_introl (QL15 i (conj (proj1 Hi) Hlt)))). liaq.
            - pose proof (L2 i (or_intror (conj Hge Hlt2))). liaq.
            - rewrite (L3 i ltac:(liaq)). apply AL. exact Hi. }
          intros _. split; [lia|]. split; [lia|]. split; [liaq|]. split; [exact QCT|].
          intros i Hi. apply L2. destruct (Z_lt_le_dec i f_have); [left; apply QL15; liaq | right; liaq]. }
      assert (NLV : forall n7 h7 ho7 b7 k, k = clx (code_val here) ->
        RINV NI NO (mkIR n7 h7 r_put r_left ho7 b7 r_in r_out r_ret) -> h7 = 0 -> b7 < code_bits here + k -> hpre ho7 b1 ho1 ->
        LRNGq NI NO WN TOT0 (mkW (mkIS CODELENS f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra (CDyn 0) f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
                 (mkIC c_input c_next_in c_avail_in c_outbuf c_next_out c_avail_out c_total_in c_total_out c_adler c_data_type c_msg)
                 (mkIR n7 h7 r_put r_left ho7 b7 r_in r_out r_ret))
        /\ sinv (mkIS CODELENS f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra (CDyn 0) f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
        /\ binv (mkW (mkIS CODELENS f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra (CDyn 0) f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
                 (mkIC c_input c_next_in c_avail_in c_outbuf c_next_out c_avail_out c_total_in c_total_out c_adler c_data_type c_msg)
                 (mkIR n7 h7 r_put r_left ho7 b7 r_in r_out r_ret))
        /\ cks (mkIS CODELENS f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra (CDyn 0) f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
        /\ xinv (mkW (mkIS CODELENS f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra (CDyn 0) f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
                 (mkIC c_input c_next_in c_avail_in c_outbuf c_next_out c_avail_out c_total_in c_total_out c_adler c_data_type c_msg)
                 (mkIR n7 h7 r_put r_left ho7 b7 r_in r_out r_ret))
        /\ cinv (mkW (mkIS CODELENS f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                    f_window f_window_blk f_hold f_bits f_length f_offset f_extra (CDyn 0) f_distcode f_lenbits f_distbits
                    f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)
                 (mkIC c_input c_next_in c_avail_in c_outbuf c_next_out c_avail_out c_total_in c_total_out c_adler c_data_type c_msg)
                 (mkIR n7 h7 r_put r_left ho7 b7 r_in r_out r_ret))).
      { intros n7 h7 ho7 b7 k Hk RI7 Hz Hlt P. rinv_open RI7. split; [lrng_auto|]. split; [exact SIr|]. split; [| split; [cks_close | split; [xinv_auto | kinv_close; kinv_auto]]]. binv_close. right. split; [| lia].
        match goal with |- _ < ccons ?S0 ?hh => rewrite (ccons_eq S0 hh here ltac:(liaq) ltac:(cbn; liaq)); [liaq|] end.
        symmetry. apply (STABLE ho7 P). lia. }
      destruct (Z.eqb_spec (code_val here) 16) as [E16|N16]; wred.
      + needbits_run (code_bits here + 2) RI1 NI32 NO32 ClNI Cinb.
        2:{ needbits_aleave NB r2 RI2. apply (NLV _ _ _ _ 2); [unfold clx; rewrite E16; reflexivity | exact RI2 | assumption | assumption | assumption]. }
        needbits_arun NB r2 RI2. wred. rinv_open RI2.
        dropbits (code_bits here) RI2 RI3 NI32 NO32. rinv_open RI3.
        destruct (Z.eqb_spec f_have 0) as [H0|H0]; wred.
        { cbn [w_s w_r is_nlen is_ndist is_mode ir_bits].
          split; [pinv_auto | split; [reflexivity | split; [reflexivity | split; [intros X; discriminate X | split; [intros _; reflexivity | unfold wle; cbn [w_r ir_left ir_bits ir_have]; liaq]]]]]. }
        pose proof (BITSv_bound (Z.shiftr ho0 (code_bits here)) 2 ltac:(lia)) as B2. change (2 ^ 2) with 4 in B2.
        dropbits 2%Z RI3 RI4 NI32 NO32.
        apply REP; [apply QL15; glia | glia | exact RI4 | | glia | glia].
        destruct EX1 as [X | [Eb Eh]]; [glia|]. destruct (EX0 Eb Eh) as [X|X]; [glia|]. unfold clx in X. rewrite E16 in X. cbn in X. glia.
      + destruct (Z.eqb_spec (code_val here) 17) as [E17|N17]; wred.
        * needbits_run (code_bits here + 3) RI1 NI32 NO32 ClNI Cinb.
          2:{ needbits_aleave NB r2 RI2. apply (NLV _ _ _ _ 3); [unfold clx; rewrite E17; reflexivity | exact RI2 | assumption | assumption | assumption]. }
          needbits_arun NB r2 RI2. wred. rinv_open RI2.
          dropbits (code_bits here) RI2 RI3 NI32 NO32. rinv_open RI3.
          pose proof (BITSv_bound (Z.shiftr ho0 (code_bits here)) 3 ltac:(lia)) as B3. change (2 ^ 3) with 8 in B3.
          dropbits 3%Z RI3 RI4 NI32 NO32.
          apply REP; [glia | glia | exact RI4 | | glia | glia].
          destruct EX1 as [X | [Eb Eh]]; [glia|]. destruct (EX0 Eb Eh) as [X|X]; [glia|]. unfold clx in X. rewrite E17 in X.
          replace (code_val here <? 16) with false in X by (symmetry; apply Z.ltb_ge; lia). replace (code_val here =? 16) with false in X by (symmetry; apply Z.eqb_neq; lia). cbn in X. liaq.
        * needbits_run (code_bits here + 7) RI1 NI32 NO32 ClNI Cinb.
          2:{ needbits_aleave NB r2 RI2. apply (NLV _ _ _ _ 7); [| exact RI2 | assumption | assumption | assumption].
              unfold clx. replace (code_val here <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
              replace (code_val here =? 16) with false by (symmetry; apply Z.eqb_neq; lia). replace (code_val here =? 17) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
          needbits_arun NB r2 RI2. wred. rinv_open RI2.
          dropbits (code_bits here) RI2 RI3 NI32 NO32. rinv_open RI3.
          pose proof (BITSv_bound (Z.shiftr ho0 (code_bits here)) 7 ltac:(lia)) as B7. change (2 ^ 7) with 128 in B7.
          dropbits 7%Z RI3 RI4 NI32 NO32.
          apply REP; [glia | glia | exact RI4 | | glia | glia].
          destruct EX1 as [X | [Eb Eh]]; [glia|]. destruct (EX0 Eb Eh) as [X|X]; [glia|]. unfold clx in X.
          replace (code_val here <? 16) with false in X by (symmetry; apply Z.ltb_ge; lia).
          replace (code_val here =? 16) with false in X by (symmetry; apply Z.eqb_neq; lia). replace (code_val here =? 17) with false in X by (symmetry; apply Z.eqb_neq; lia). cbn in X. glia.
  Qed.
End Arms.
