(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel TreeModel CompressModel FlushBlockModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel RefDeflSafeZ RefDeflSafeT RefDeflSafeG RefDeflSafeFBT RefDeflSafeFB RefDeflSafeW RefDeflSafeLW RefDeflSafeF RefDeflSafeLF.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM RefDeflFast1 RefDeflFast6 RefDeflSlow2 RefDeflSlow6 RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI4 RefDeflSafeL2 RefDeflSafeL5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BoundArith BoundDefs BoundCost BoundFw BoundTfb BoundMc DeflateRc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section SlowB.
  Variable c0 : cstrm.
  Variable s0 : deflate_state.
  Variable flush : Z.
  Variable IN0 : Z.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis HFB : FB_CALL.
  Hypothesis HLBS : ds_lit_bufsize s0 = 16384.
  Hypothesis HWS : ds_w_size s0 = 32768.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.

  Definition Apos (s : deflate_state) : Z :=
    IN0 + cs_next_in (ds_strm s) - ds_lookahead s - (ds_strstart s - ds_block_start s).
  Definition Psi (s : deflate_state) : Z := phi0 (Apos s) - Mc s.
  Definition BT (s : deflate_state) : Prop := COV s /\ 0 <= Apos s.

  Lemma COV_same : forall s s',
    ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s -> ds_sym_next s' = ds_sym_next s ->
    ds_strstart s' - ds_block_start s' = ds_strstart s - ds_block_start s -> ds_match_available s' = ds_match_available s ->
    nbP s' -> ds_match_length s' = ds_match_length s ->
    wrap32 (ds_strstart s' - ds_match_start s') = wrap32 (ds_strstart s - ds_match_start s) ->
    COV s -> COV s'.
  Proof.
    intros s s' EP EL EN ED EM NB EML EW [C1 C2 C3 C4 C5]. constructor.
    - rewrite (cov_same s s' EP EL EN), ED, EM. exact C1.
    - exact (near_same s s' EP EL EN C2).
    - exact NB.
    - rewrite EML, EW. exact C4.
    - rewrite EML, EM. exact C5.
  Qed.

  Lemma bfill : forall s, STI c0 s0 s -> BT s ->
    BT (fst (st_fill s flush)) /\ Psi (fst (st_fill s flush)) = Psi s.
  Proof.
    intros s HF [HC HA]. unfold st_fill.
    destruct (ds_lookahead s <? MIN_LOOKAHEAD); [| cbn [fst]; split; [split; assumption | reflexivity]].
    assert (E : fst (if (ds_lookahead (fill_window s) <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH) then (fill_window s, Some (LRet need_more))
                     else if ds_lookahead (fill_window s) =? 0 then (fill_window s, Some LBreak) else (fill_window s, None)) = fill_window s)
      by (destruct (_ && _); [reflexivity | destruct (_ =? 0); reflexivity]).
    rewrite E. clear E.
    pose proof (fill_window_keep s) as K. pose proof (fwG_fields _ _ (fwG_fill_window s)) as (_ & ED & EI & _ & EW).
    destruct K as (Kp & _ & Kbv & _ & Kpb & Klbs & _ & Ksn & _ & _ & _ & Kml & _ & Kma & _ & _ & _ & Kor & _ & _ & Kla).
    assert (EA : Apos (fill_window s) = Apos s) by (unfold Apos; lia).
    split.
    - split; [| rewrite EA; exact HA].
      apply (COV_same s); try assumption. apply nbP_fill_window. exact (cv_nb _ HC).
    - unfold Psi. rewrite EA. f_equal. unfold Mc, olen, Mloc. rewrite Kor, Kp, Kbv. reflexivity.
  Qed.

  Definition FLP (x : deflate_state) : Prop :=
    dwf x /\ SV c0 x /\ DXX x /\ fb_entry x 0 /\ ds_status x <> FINISH_STATE /\ dmode x <> 0 /\ KV x = KV s0
    /\ cov x = ds_strstart x - ds_block_start x /\ (forall j, 0 <= j < nsym x -> near3 x j) /\ nbP x /\ 0 <= Apos x.

  Lemma fb_len_eq : forall x last, fb_entry x last -> fb_len x = ds_strstart x - ds_block_start x.
  Proof. intros x last FE. pose proof (fe_diff _ _ FE). unfold fb_len. apply wrap64_id. lia. Qed.

  Lemma FLP_sizes : forall x, FLP x -> ds_lit_bufsize x = 16384 /\ ds_w_size x = 32768.
  Proof. intros x (_ & _ & _ & _ & _ & _ & K & _). pose proof (KV_fields _ _ K) as (A & _ & B & _). rewrite A, B. auto. Qed.

  Lemma FLP_nobuf : forall x last, FLP x -> fb_entry x last -> fb_buf x = None ->
    zsum (scost x) 0 (Z.to_nat (nsym x)) <= 8 * fb_len x + 30.
  Proof.
    intros x last P FE EB. pose proof (FLP_sizes x P) as [Elbs Ews].
    destruct P as (_ & _ & _ & _ & _ & _ & _ & CV & NR & NB & _).
    rewrite (fb_len_eq x last FE).
    pose proof (fe_nsym _ _ FE) as Hn. pose proof (scost_sum_cov x (proj1 Hn) (fe_syms _ _ FE) NR) as (S1 & S2 & S3).
    assert (Hbs : ds_block_start x < 0) by (unfold fb_buf in EB; destruct (Z.leb_spec 0 (ds_block_start x)); [discriminate EB | assumption]).
    specialize (NB Hbs). rewrite Ews in NB. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in NB. rewrite Elbs in Hn. rewrite CV in *.
    lia.
  Qed.

  Lemma bflush_gen : forall x last, FLP x -> fb_entry x last -> 0 <= last <= 1 ->
    let x' := flush_block_only x last in
    Mc x' <= Mc x + (ds_strstart x - ds_block_start x) + 5
    /\ Apos x' = Apos x + (ds_strstart x - ds_block_start x)
    /\ ds_sym_next x' = 0 /\ ds_block_start x' = ds_strstart x /\ ds_strstart x' = ds_strstart x
    /\ ds_match_length x' = ds_match_length x /\ PF x' = PF x /\ ds_lookahead x' = ds_lookahead x.
  Proof.
    intros x last P FE Hlast x'. pose proof P as (D & V & XX & _ & Hst & Hm & K & CV & NR & NB & HA).
    pose proof (flush_block_only_factsW c0 x last HFB HC0w D V XX FE Hst Hm) as F. cbv zeta in F. fold x' in F.
    destruct F as (_ & _ & _ & _ & EPF & Estr & Elook & Ebs & Eml & _ & Esn & _ & _ & Enin).
    destruct (HFB x last FE) as [_ FP].
    pose proof (tfb_bound x last FE (FLP_nobuf x last P FE)) as TB. pose proof (fb_len_eq x last FE) as EL.
    pose proof (Mc_flush_block_only x last _ eq_refl FP (proj1 (fe_aout _ _ FE)) (fe_lbs _ _ FE)) as EM. fold x' in EM.
    split; [| split; [| repeat split; assumption]].
    - rewrite EM. unfold Mc, Mloc at 2. rewrite (fe_pending _ _ FE). lia.
    - unfold Apos. rewrite Enin, Elook, Ebs, Estr. lia.
  Qed.

  Definition symview (s : deflate_state) := (ds_pending_buf s, ds_lit_bufsize s, ds_sym_next s).

  Lemma symview_fields : forall s s', symview s' = symview s ->
    ds_pending_buf s' = ds_pending_buf s /\ ds_lit_bufsize s' = ds_lit_bufsize s /\ ds_sym_next s' = ds_sym_next s.
  Proof. intros s s' E. unfold symview in E. injection E as E1 E2 E3. auto. Qed.

  Lemma slow_insert_symview : forall n s mi, symview (deflate_slow_insert n s mi) = symview s.
  Proof.
    induction n as [|n IH]; intros s mi; [reflexivity|].
    cbn [deflate_slow_insert]. unfold insert_string.
    destruct (ds_strstart (set_strstart s (ds_strstart s + 1)) <=? mi); dsred;
      (destruct (negb _); [rewrite IH|]; unfold symview; dsred; reflexivity).
  Qed.

  Lemma sdist_symview : forall s4,
    symview (fst (st_sdist s4)) = symview (fst (tr_tally_dist s4 (wrap32 (ds_strstart s4 - 1 - ds_prev_match s4)) (ds_prev_length s4 - 3))).
  Proof.
    intros s4. unfold st_sdist. destruct (tr_tally_dist s4 _ _) as [t b]. cbn [fst].
    unfold symview at 1. dsred.
    pose proof (symview_fields _ _ (slow_insert_symview (Z.to_nat (ds_prev_length (set_prev_length (set_lookahead t (wrap32 (ds_lookahead t - (ds_prev_length t - 1)))) (ds_prev_length (set_lookahead t (wrap32 (ds_lookahead t - (ds_prev_length t - 1)))) - 2))))
                  (set_prev_length (set_lookahead t (wrap32 (ds_lookahead t - (ds_prev_length t - 1)))) (ds_prev_length (set_lookahead t (wrap32 (ds_lookahead t - (ds_prev_length t - 1)))) - 2))
                  (wrap32 (ds_strstart s4 + ds_lookahead s4 - 3)))) as (E1 & E2 & E3).
    dsred in E1. dsred in E2. dsred in E3. rewrite E1, E2, E3. reflexivity.
  Qed.

  Lemma s4_block : forall s1 s2 s4, STI c0 s0 s1 -> SMREL s1 s2 s4 ->
    BQ s4 /\ nsym s4 = nsym s1 /\ cov s4 = cov s1 /\ (forall j, 0 <= j < nsym s1 -> near3 s1 j -> near3 s4 j)
    /\ ds_lit_bufsize s4 + ds_sym_next s4 + 3 <= arr_len (ds_pending_buf s4) /\ 0 <= ds_lit_bufsize s4 /\ nsym s4 + 2 < 65536
    /\ L_CODES <= arr_len (ds_dyn_ltree_fc s4) /\ D_CODES <= arr_len (ds_dyn_dtree_fc s4)
    /\ ds_block_start s4 = ds_block_start s1 /\ ds_w_size s4 = ds_w_size s1 /\ ds_strm s4 = ds_strm s1
    /\ ds_pending s4 = ds_pending s1 /\ ds_bi_valid s4 = ds_bi_valid s1.
  Proof.
    intros s1 s2 s4 HF MR.
    pose proof (STI_facts c0 s0 s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & _).
    destruct MR as (T4 & Estr4 & Elook4 & Esn4 & Epb4 & Elfc4 & Edfc4 & _).
    pose proof (TS_fields _ _ T4) as (_ & (_ & Ews4 & _) & (Ebs4 & _ & _ & Elbs4 & Ebl4 & _) & _ & (Estrm4 & Epd4 & _ & Ebv4 & _) & _).
    assert (BQ4 : BQ s4).
    { apply (BQ_same s1); [rewrite Epb4 | rewrite Elbs4 | rewrite Esn4 | rewrite Elfc4 | rewrite Edfc4 | rewrite Ebl4 |]; try reflexivity. exact (DX_BQ s1 X). }
    assert (N4 : nsym s4 = nsym s1) by (unfold nsym; rewrite Esn4; reflexivity).
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL.
    split; [exact BQ4|]. split; [exact N4|]. split; [apply cov_same; assumption|].
    split. { intros j Hj NJ. destruct (sym_view_same s1 s4 Epb4 Elbs4 (3 * j)) as [Ed Ec]. exact (near3_same s1 s4 j Ed Ec NJ). }
    split; [rewrite Elbs4, Esn4, Epb4, (df_bl _ D); lia|]. split; [rewrite Elbs4; lia|]. split; [rewrite N4; lia|].
    split; [rewrite Elfc4; unfold L_CODES; lia|]. split; [rewrite Edfc4; unfold D_CODES; lia|].
    repeat split; assumption.
  Qed.

  Lemma bdist : forall s1 s2 s4, STI c0 s0 s1 -> 1 <= ds_lookahead s1 -> SHREL s1 s2 -> SMREL s1 s2 s4 -> dist_cond s4 = true -> BT s1 ->
    let s7 := fst (st_sdist s4) in
    BT s7 /\ Psi s7 = Psi s1 /\ cov s7 = ds_strstart s7 - ds_block_start s7
    /\ (forall j, 0 <= j < nsym s7 -> near3 s7 j) /\ nbP s7 /\ 0 <= Apos s7.
  Proof.
    intros s1 s2 s4 HF Hl1 HR MR Hdc [HC HA] s7.
    pose proof (STI_facts c0 s0 s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & Hma11 & H31).
    pose proof (sdist_stage c0 s0 s1 s2 s4 HF Hl1 HR MR Hdc) as SD. cbv zeta in SD. fold s7 in SD.
    destruct SD as (R & _ & Hml3 & Hmll & Hstr3 & _).
    destruct (s4_block s1 s2 s4 HF MR) as (BQ4 & N4 & C4 & NR4 & Room & Lb0 & Nn & TLl & TLd & Ebs4 & Ews4 & Estrm4 & Epd4 & Ebv4).
    pose proof MR as (_ & Estr4 & _ & _ & _ & _ & _ & _ & _ & _ & Epl4 & Epm4 & _).
    destruct (H31 ltac:(unfold MIN_MATCH; lia)) as (_ & _ & Hw).

    set (d := wrap32 (ds_strstart s4 - 1 - ds_prev_match s4)).
    assert (Ed : d = wrap32 (ds_strstart s1 - ds_match_start s1) - 1).
    { subst d. rewrite Estr4, Epm4. replace (ds_strstart s1 - 1 - ds_match_start s1) with (ds_strstart s1 - ds_match_start s1 - 1) by lia.
      apply wrap32_pred. lia. }
    assert (Hd : 1 <= d <= 32768) by (unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hw; lia).
    destruct (BQ_tally_dist s4 BQ4 Room Lb0 Nn TLl TLd d (ds_prev_length s4 - 3) Hd) as (_ & N5 & Dn & Ln & OLD). cbv zeta in N5, Dn, Ln, OLD.
    set (r := fst (tr_tally_dist s4 d (ds_prev_length s4 - 3))) in *.
    pose proof (symview_fields _ _ (sdist_symview s4)) as (Vp & Vl & Vn). fold d r s7 in Vp, Vl, Vn.
    assert (Elc : sym_lc r (3 * nsym s4) = ds_match_length s1 - 3) by (rewrite Ln, Epl4; apply wrap8_id; lia).
    assert (SL : symlen r (nsym s4) = ds_match_length s1) by (rewrite symlen_match by (rewrite Dn; lia); rewrite Elc; lia).
    assert (Cr : cov r = cov s1 + ds_match_length s1).
    { rewrite (cov_snoc s4 r (proj1 (proj2 BQ4)) N5 OLD), C4, SL. reflexivity. }
    assert (NRr : forall j, 0 <= j < nsym r -> near3 r j).
    { apply (near_snoc s4 r (proj1 (proj2 BQ4)) N5 OLD).
      - intros j Hj. apply NR4; [lia|]. apply (cv_near _ HC). lia.
      - unfold near3. intros _ Z0. rewrite Dn. rewrite Elc in Z0. pose proof (cv_pm _ HC ltac:(lia)). lia. }
    destruct R as (T7 & Estr7 & Elook7 & Eml7 & Ema7 & _).
    pose proof (TS_fields _ _ T7) as (_ & (_ & Ews7 & _) & (Ebs7 & _) & _ & (Estrm7 & Epd7 & _ & Ebv7 & _) & _).
    pose proof (cv_cov _ HC) as CC. pose proof (cv_ma _ HC ltac:(lia)) as MA1.
    assert (C7 : cov s7 = ds_strstart s7 - ds_block_start s7) by (rewrite (cov_same r s7 Vp Vl Vn), Cr, CC, Estr7, Ebs7, MA1; lia).
    assert (NR7 : forall j, 0 <= j < nsym s7 -> near3 s7 j) by (exact (near_same r s7 Vp Vl Vn NRr)).
    assert (NB7 : nbP s7).
    { unfold nbP. rewrite Ebs7, Ews7, Estr7. intros Hb. pose proof (cv_nb _ HC Hb). lia. }
    assert (EA : Apos s7 = Apos s1) by (unfold Apos; rewrite Estrm7, Elook7, Estr7, Ebs7; lia).
    split; [| split; [| split; [exact C7 | split; [exact NR7 | split; [exact NB7 | rewrite EA; exact HA]]]]].
    - split; [| rewrite EA; exact HA]. constructor.
      + rewrite C7, Ema7. lia.
      + exact NR7.
      + exact NB7.
      + rewrite Eml7. intros HH; discriminate HH.
      + rewrite Eml7. intros HH; lia.
    - unfold Psi. rewrite EA. f_equal. unfold Mc, olen, Mloc. rewrite Estrm7, Epd7, Ebv7. reflexivity.
  Qed.

  Lemma cov_nil : forall x, ds_sym_next x = 0 -> cov x = 0 /\ nsym x = 0.
  Proof. intros x E. unfold cov, nsym. rewrite E. split; reflexivity. Qed.

  Lemma bflush_full : forall x, FLP x -> ds_sym_next x = ds_sym_end x ->
    let x' := flush_block_only x 0 in
    Psi x <= Psi x' /\ 0 <= Apos x'
    /\ ds_sym_next x' = 0 /\ ds_block_start x' = ds_strstart x /\ ds_strstart x' = ds_strstart x
    /\ ds_match_length x' = ds_match_length x /\ PF x' = PF x /\ ds_lookahead x' = ds_lookahead x.
  Proof.
    intros x P Efull x'. pose proof (FLP_sizes x P) as [Elbs _].
    pose proof P as (_ & _ & _ & FE & _ & _ & _ & CV & NR & _ & HA).
    destruct (bflush_gen x 0 P FE ltac:(lia)) as (HM & EA & R). fold x' in HM, EA, R.
    pose proof (fe_nsym _ _ FE) as Hn. pose proof (scost_sum_cov x (proj1 Hn) (fe_syms _ _ FE) NR) as (_ & S2 & S3).
    assert (HN : nsym x = 16383).
    { pose proof (fe_sn _ _ FE) as Esn. pose proof (fe_symend _ _ FE) as Ese. rewrite Elbs in Ese. lia. }
    assert (HL : KBLK <= ds_strstart x - ds_block_start x) by (unfold KBLK; rewrite <- CV; lia).
    pose proof (phi0_step (Apos x) (ds_strstart x - ds_block_start x) HA HL) as PS.
    split; [unfold Psi; rewrite EA; lia|]. split; [rewrite EA; unfold KBLK in HL; lia | exact R].
  Qed.

  Lemma st_lm_near : forall s3 hh, ds_match_length s3 = 2 ->
    ds_match_length (st_lm s3 hh) = 3 -> wrap32 (ds_strstart (st_lm s3 hh) - ds_match_start (st_lm s3 hh)) <= 4096.
  Proof.
    intros s3 hh E2. unfold st_lm. destruct (sl_lm_cond s3 hh); [| rewrite E2; intros HH; discriminate HH].
    set (s1 := set_match_length (fst (longest_match s3 hh)) (snd (longest_match s3 hh))).
    destruct (sl_filter s1) eqn:EF; [dsred; intros HH; discriminate HH|].
    intros E3. unfold sl_filter in EF. rewrite E3 in EF. cbn [Z.leb Z.compare Pos.compare Pos.compare_cont Z.eqb Pos.eqb andb] in EF.
    apply orb_false_iff in EF as [_ EF]. apply Z.ltb_ge in EF. exact EF.
  Qed.

  Lemma pm_next : forall str ms, wrap32 (str - ms) <= 4096 -> wrap32 (str + 1 - ms) <= 4097.
  Proof.
    intros str ms H. replace (str + 1 - ms) with (str - ms + 1) by lia. rewrite wrap32_succ; [lia|]. pose proof (wrap32_range (str - ms)). lia.
  Qed.

  Lemma bavail : forall s1 s2 s4, STI c0 s0 s1 -> SMREL s1 s2 s4 -> ds_match_available s4 = 0 ->
    (ds_match_length s4 = 3 -> wrap32 (ds_strstart s4 - ds_match_start s4) <= 4096) -> BT s1 ->
    let s7 := fst (st_avail s4) in BT s7 /\ Psi s7 = Psi s1.
  Proof.
    intros s1 s2 s4 HF MR Hma0 HPM [HC HA] s7.
    destruct (s4_block s1 s2 s4 HF MR) as (_ & N4 & C4 & NR4 & _ & _ & _ & _ & _ & Ebs4 & Ews4 & Estrm4 & Epd4 & Ebv4).
    pose proof MR as (_ & Estr4 & Elook4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ema4 & _).
    subst s7. unfold st_avail. cbn [fst].
    assert (EA : Apos (set_lookahead (set_strstart (set_match_available s4 1) (ds_strstart s4 + 1)) (ds_lookahead s4 - 1)) = Apos s1)
      by (unfold Apos; dsred; rewrite Estrm4, Elook4, Estr4, Ebs4; lia).
    split; [split; [| rewrite EA; exact HA] | unfold Psi; rewrite EA; f_equal; unfold Mc, olen, Mloc; dsred; rewrite Estrm4, Epd4, Ebv4; reflexivity].
    pose proof (cv_cov _ HC) as CC. rewrite <- Ema4, Hma0 in CC.
    set (s7 := set_lookahead (set_strstart (set_match_available s4 1) (ds_strstart s4 + 1)) (ds_lookahead s4 - 1)).
    assert (V7 : ds_pending_buf s7 = ds_pending_buf s4 /\ ds_lit_bufsize s7 = ds_lit_bufsize s4 /\ ds_sym_next s7 = ds_sym_next s4) by (subst s7; dsred; auto).
    destruct V7 as (Vp & Vl & Vn).
    constructor.
    - rewrite (cov_same s4 s7 Vp Vl Vn), C4, CC. subst s7; dsred. rewrite Estr4, Ebs4. lia.
    - apply (near_same s4 s7 Vp Vl Vn). intros k Hk. apply NR4; [lia|]. apply (cv_near _ HC). lia.
    - subst s7; dsred. rewrite Ebs4, Ews4, Estr4. intros Hb. pose proof (cv_nb _ HC Hb). lia.
    - subst s7; dsred. intros E3. apply pm_next. exact (HPM E3).
    - subst s7; dsred. intros _. reflexivity.
  Qed.

  Definition adv1 (x : deflate_state) : deflate_state := set_lookahead (set_strstart x (ds_strstart x + 1)) (ds_lookahead x - 1).

  Lemma adv1_BT : forall x, ds_match_available x = 1 ->
    cov x = ds_strstart x - ds_block_start x -> (forall j, 0 <= j < nsym x -> near3 x j) -> nbP x ->
    (ds_match_length x = 3 -> wrap32 (ds_strstart x - ds_match_start x) <= 4096) -> 0 <= Apos x ->
    BT (adv1 x) /\ Psi (adv1 x) = Psi x.
  Proof.
    intros x Hma C NR NB HPM HA. unfold adv1.
    set (y := set_lookahead (set_strstart x (ds_strstart x + 1)) (ds_lookahead x - 1)).
    assert (V : ds_pending_buf y = ds_pending_buf x /\ ds_lit_bufsize y = ds_lit_bufsize x /\ ds_sym_next y = ds_sym_next x) by (subst y; dsred; auto).
    destruct V as (Vp & Vl & Vn).
    assert (EA : Apos y = Apos x) by (subst y; unfold Apos; dsred; lia).
    split; [split; [| rewrite EA; exact HA] | unfold Psi; rewrite EA; f_equal].
    constructor.
    - rewrite (cov_same x y Vp Vl Vn), C. subst y; dsred. lia.
    - exact (near_same x y Vp Vl Vn NR).
    - subst y; unfold nbP in *; dsred. intros Hb. specialize (NB Hb). lia.
    - subst y; dsred. intros E3. apply pm_next. exact (HPM E3).
    - subst y; dsred. intros _. exact Hma.
  Qed.

  Lemma blit : forall s1 s2 s4, STI c0 s0 s1 -> 1 <= ds_lookahead s1 -> SHREL s1 s2 -> SMREL s1 s2 s4 ->
    dist_cond s4 = false -> ds_match_available s4 = 1 ->
    (ds_match_length s4 = 3 -> wrap32 (ds_strstart s4 - ds_match_start s4) <= 4096) -> BT s1 ->
    let s7 := fst (st_slit s4) in BT s7 /\ Psi s1 <= Psi s7.
  Proof.
    intros s1 s2 s4 HF Hl1 HR MR Hdc Hma4 HPM [HC HA] s7.
    destruct (s4_block s1 s2 s4 HF MR) as (BQ4 & N4 & C4 & NR4 & Room & Lb0 & Nn & TLl & _ & Ebs4 & Ews4 & Estrm4 & Epd4 & Ebv4).
    pose proof MR as (_ & Estr4 & Elook4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ema4 & _).
    pose proof (STI_facts c0 s0 s1 HF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsn1 & Hse1 & Hstr1 & _).
    pose proof (smid_facts c0 s0 HC0 s1 s2 s4 HF Hl1 HR MR Hdc Hma4) as SM. cbv zeta in SM.
    set (c := arr_get (ds_window s4) (ds_strstart s4 - 1)) in *.
    destruct (BQ_tally_lit s4 BQ4 Room Lb0 Nn TLl c) as (_ & N5 & Dn & _ & OLD). cbv zeta in N5, Dn, OLD.
    pose proof (tally_lit_facts s4 c) as (TK & _). cbv zeta in TK.
    subst s7. unfold st_slit. fold c.
    destruct (tr_tally_lit s4 c) as [s5 b]. cbn [fst snd] in SM, N5, Dn, OLD, TK |- *.
    destruct SM as (Ebf & D5 & V5 & XX5 & FE5 & HK5 & _ & Hst5 & Hm5 & Estrm5 & Estr5 & Elook5 & _ & _ & Hma5 & _ & _ & _ & N5' & Elbs5).
    destruct TK as (_ & _ & _ & _ & _ & _ & Kbs & Kml & Kms & _ & _ & _ & Kpd & _ & Kbv & _ & _ & _ & _ & Kws & _).
    pose proof (cv_cov _ HC) as CC. rewrite <- Ema4, Hma4 in CC.
    assert (C5 : cov s5 = ds_strstart s5 - ds_block_start s5).
    { rewrite (cov_snoc s4 s5 (proj1 (proj2 BQ4)) N5 OLD), C4, (symlen_lit s5 _ Dn), CC, Estr5, Kbs, Ebs4. lia. }
    assert (NR5 : forall j, 0 <= j < nsym s5 -> near3 s5 j).
    { apply (near_snoc s4 s5 (proj1 (proj2 BQ4)) N5 OLD); [| exact (near3_lit s5 _ Dn)].
      intros j Hj. apply NR4; [lia|]. apply (cv_near _ HC). lia. }
    assert (NB5 : nbP s5) by (unfold nbP; rewrite Kbs, Kws, Ebs4, Ews4, Estr5; exact (cv_nb _ HC)).
    assert (EA5 : Apos s5 = Apos s1) by (unfold Apos; rewrite Estrm5, Elook5, Estr5, Kbs, Ebs4; lia).
    assert (EM5 : Mc s5 = Mc s1) by (unfold Mc, olen, Mloc; rewrite Estrm5, Kpd, Kbv, Epd4, Ebv4; reflexivity).
    assert (HPM5 : ds_match_length s5 = 3 -> wrap32 (ds_strstart s5 - ds_match_start s5) <= 4096)
      by (rewrite Kml, Kms, Estr5, <- Estr4; exact HPM).
    assert (EP5 : Psi s5 = Psi s1) by (unfold Psi; rewrite EA5, EM5; reflexivity).
    fold (adv1 (if b then flush_block_only s5 0 else s5)).
    destruct b.
    -
      assert (P5 : FLP s5).
      { split; [exact D5|]. split; [exact V5|]. split; [exact XX5|]. split; [exact FE5|]. split; [exact Hst5|]. split; [rewrite Hm5; lia|].
        split; [exact HK5|]. split; [exact C5|]. split; [exact NR5|]. split; [exact NB5 | rewrite EA5; exact HA]. }
      assert (Efull : ds_sym_next s5 = ds_sym_end s5).
      { symmetry in Ebf. apply Z.eqb_eq in Ebf. pose proof (fe_sn _ _ FE5) as E1. pose proof (fe_symend _ _ FE5) as E2. rewrite E1, E2, N5', Elbs5. lia. }
      destruct (bflush_full s5 P5 Efull) as (HP & HA6 & Esn6 & Ebs6 & Estr6 & Eml6 & EPF6 & _).
      set (s6 := flush_block_only s5 0) in *.
      pose proof (PF_fields _ _ EPF6) as (_ & (_ & _ & _ & Ema6 & _) & _ & (_ & _ & _ & _ & _ & _ & _ & Ems6 & _)).
      destruct (cov_nil s6 Esn6) as [C6 N6].
      destruct (adv1_BT s6) as [B7 E7].
      + rewrite Ema6. exact Hma5.
      + rewrite C6, Ebs6, Estr6. lia.
      + intros j Hj. rewrite N6 in Hj. lia.
      + unfold nbP. rewrite Ebs6. pose proof (fe_str _ _ FE5). lia.
      + rewrite Eml6, Estr6, Ems6. exact HPM5.
      + exact HA6.
      + split; [exact B7 | rewrite E7, <- EP5; exact HP].
    - destruct (adv1_BT s5 Hma5 C5 NR5 NB5 HPM5 ltac:(rewrite EA5; exact HA)) as [B7 E7].
      split; [exact B7 | rewrite E7, EP5; lia].
  Qed.

  Lemma fst_st_bflush : forall x b, fst (st_bflush x b) = if b then flush_block_only x 0 else x.
  Proof.
    intros x b. unfold st_bflush. destruct b; [| reflexivity]. rewrite flush_block_eq'.
    destruct (cs_avail_out (ds_strm (flush_block_only x 0)) =? 0); reflexivity.
  Qed.

  Lemma bdistf : forall s1 s2 s4, STI c0 s0 s1 -> 1 <= ds_lookahead s1 -> SHREL s1 s2 -> SMREL s1 s2 s4 -> dist_cond s4 = true -> BT s1 ->
    let r := st_bflush (fst (st_sdist s4)) (snd (st_sdist s4)) in BT (fst r) /\ Psi s1 <= Psi (fst r).
  Proof.
    intros s1 s2 s4 HF Hl1 HR MR Hdc HB.
    destruct (bdist s1 s2 s4 HF Hl1 HR MR Hdc HB) as (B7 & E7 & C7 & NR7 & NB7 & HA7).
    pose proof (sdist_stage c0 s0 s1 s2 s4 HF Hl1 HR MR Hdc) as SD. cbv zeta in SD. destruct SD as (R & Ebf & Hml3 & Hmll & _).
    pose proof (sdist_send c0 s0 s1 _ HF R Hml3 Hmll) as SE.
    pose proof (send_facts c0 s0 HC0 s1 _ _ 1 HF SE) as SF.
    destruct SF as (D7 & V7 & HK7 & _ & Hm7 & Hst7 & _ & _ & _ & _ & N7 & _ & Elbs7 & _ & FE7 & XX7 & _).
    pose proof (STI_facts c0 s0 s1 HF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsn1 & Hse1 & _).
    set (s7 := fst (st_sdist s4)) in *. cbv zeta. rewrite fst_st_bflush.
    destruct (snd (st_sdist s4)); [| split; [exact B7 | rewrite E7; lia]].
    assert (P7 : FLP s7).
    { split; [exact D7|]. split; [exact V7|]. split; [exact XX7|]. split; [exact FE7|]. split; [exact Hst7|]. split; [rewrite Hm7; lia|].
      split; [exact HK7|]. split; [exact C7|]. split; [exact NR7|]. split; [exact NB7 | exact HA7]. }
    assert (Efull : ds_sym_next s7 = ds_sym_end s7).
    { symmetry in Ebf. apply Z.eqb_eq in Ebf. pose proof (fe_sn _ _ FE7) as E1. pose proof (fe_symend _ _ FE7) as E2. rewrite E1, E2, N7, Elbs7. lia. }
    destruct (bflush_full s7 P7 Efull) as (HP & HA8 & Esn8 & Ebs8 & Estr8 & Eml8 & EPF8 & _).
    set (s8 := flush_block_only s7 0) in *.
    pose proof (PF_fields _ _ EPF8) as (_ & (_ & _ & _ & Ema8 & _) & _).
    destruct (cov_nil s8 Esn8) as [C8 N8]. destruct R as (_ & _ & _ & Eml7 & Ema7 & _).
    split; [| rewrite <- E7; exact HP].
    split; [| exact HA8]. constructor.
    - rewrite C8, Ebs8, Estr8, Ema8, Ema7. lia.
    - intros j Hj. rewrite N8 in Hj. lia.
    - rewrite Ebs8. pose proof (fe_str _ _ FE7). lia.
    - rewrite Eml8, Eml7. intros HH; discriminate HH.
    - rewrite Eml8, Eml7. intros HH; lia.
  Qed.

  Lemma bdecide : forall s1 s2 s4, STI c0 s0 s1 -> 1 <= ds_lookahead s1 -> SHREL s1 s2 -> SMREL s1 s2 s4 ->
    (ds_match_length s4 = 3 -> wrap32 (ds_strstart s4 - ds_match_start s4) <= 4096) -> BT s1 ->
    BT (fst (st_decide s4)) /\ Psi s1 <= Psi (fst (st_decide s4)).
  Proof.
    intros s1 s2 s4 HF Hl1 HR MR HPM HB. unfold st_decide.
    destruct (dist_cond s4) eqn:Hdc; [exact (bdistf s1 s2 s4 HF Hl1 HR MR Hdc HB)|].
    pose proof (STI_facts c0 s0 s1 HF) as (_ & _ & _ & _ & _ & _ & Hma1 & _).
    pose proof MR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ema4 & _).
    destruct (Z.eqb_spec (ds_match_available s4) 0) as [Hma0|Hma0]; cbn [negb].
    - destruct (bavail s1 s2 s4 HF MR Hma0 HPM HB) as [B E]. split; [exact B | rewrite E; lia].
    - apply (blit s1 s2 s4 HF Hl1 HR MR Hdc); [rewrite Ema4 in *; lia | exact HPM | exact HB].
  Qed.

  Lemma bstep : forall s, STI c0 s0 s -> BT s ->
    BT (fst (st_sbody s flush)) /\ Psi s <= Psi (fst (st_sbody s flush)).
  Proof.
    intros s HF HB. unfold st_sbody.
    destruct (bfill s HF HB) as [B1 E1].
    pose proof (sfill_stage c0 s0 flush HC0 s HF) as FS. cbv zeta in FS.
    destruct FS as (HF1 & _ & _ & _ & _ & Ews1 & Hnone & _ & _ & Hss1 & _).
    set (s1 := fst (st_fill s flush)) in *.
    destruct (snd (st_fill s flush)) as [o|] eqn:Eo; [cbn [fst]; split; [exact B1 | rewrite E1; lia]|].
    pose proof (Hnone eq_refl) as Hl1.
    pose proof (shash_stage c0 s0 s1 HF1 Hl1) as HS. cbv zeta in HS. destruct HS as [HR Hlm].
    rewrite <- Ews1 in Hss1.
    pose proof (slm_stage c0 s0 s1 (fst (st_hash s1)) (snd (st_hash s1)) HF1 Hl1 Hss1 HR Hlm) as LM. cbv zeta in LM. destruct LM as [MR _].
    unfold st_srest.
    destruct (bdecide s1 (fst (st_hash s1)) (st_lm (prev_st (fst (st_hash s1))) (snd (st_hash s1))) HF1 Hl1 HR MR) as [B E].
    - apply st_lm_near. reflexivity.
    - exact B1.
    - split; [exact B | rewrite <- E1; exact E].
  Qed.

  Lemma bloop : forall fuel s, STI c0 s0 s -> lz_meas s < Z.of_nat fuel -> BT s ->
    BT (fst (deflate_slow_loop fuel s flush)) /\ Psi s <= Psi (fst (deflate_slow_loop fuel s flush)).
  Proof.
    induction fuel as [|f IH]; intros s HF Hm HB; [cbn [deflate_slow_loop fst]; split; [exact HB | lia]|].
    cbn [deflate_slow_loop]. rewrite st_sbody_eq.
    destruct (bstep s HF HB) as [B1 E1]. destruct (sstep c0 s0 flush HC0 HFB s HF) as [_ OUT].
    destruct (st_sbody s flush) as [s1 o]. cbn [fst snd] in B1, E1, OUT |- *.
    destruct o as [| |bs]; cbn [fst]; try (split; [exact B1 | exact E1]).
    destruct OUT as [HF1 Hm1]. destruct (IH s1 HF1 ltac:(lia) B1) as [B2 E2]. split; [exact B2 | lia].
  Qed.

  Lemma st_decide_nobreak : forall x, snd (st_decide x) <> LBreak.
  Proof.
    intros x. unfold st_decide. destruct (dist_cond x).
    - unfold st_bflush. destruct (snd (st_sdist x)); [| cbn; discriminate].
      rewrite flush_block_eq'. destruct (cs_avail_out (ds_strm (flush_block_only (fst (st_sdist x)) 0)) =? 0); cbn; discriminate.
    - destruct (negb _); [| cbn; discriminate].
      unfold st_slit. destruct (tr_tally_lit x _) as [x1 b]. cbn [snd]. destruct (_ =? 0); discriminate.
  Qed.

  Lemma sbody_nobreak : forall s, flush = Z_NO_FLUSH -> snd (st_sbody s flush) <> LBreak.
  Proof.
    intros s F0. unfold st_sbody, st_fill. rewrite F0. change (Z_NO_FLUSH =? Z_NO_FLUSH) with true. rewrite andb_true_r.
    destruct (ds_lookahead s <? MIN_LOOKAHEAD); cbn [fst snd]; [| unfold st_srest; apply st_decide_nobreak].
    destruct (Z.ltb_spec (ds_lookahead (fill_window s)) MIN_LOOKAHEAD) as [L|L]; cbn [fst snd]; [discriminate|].
    destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [E|E]; cbn [fst snd]; [unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in L; lia|].
    unfold st_srest. apply st_decide_nobreak.
  Qed.

  Lemma loop_noflush_some : forall fuel s, flush = Z_NO_FLUSH -> STI c0 s0 s -> lz_meas s < Z.of_nat fuel ->
    snd (deflate_slow_loop fuel s flush) <> None.
  Proof.
    induction fuel as [|f IH]; intros s F0 HF Hm.
    - exfalso. pose proof (STI_facts c0 s0 s HF) as (_ & _ & V & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & _).
      pose proof (sv_ain _ _ V). unfold lz_meas in Hm. cbn in Hm. lia.
    - cbn [deflate_slow_loop]. rewrite st_sbody_eq.
      pose proof (sbody_nobreak s F0) as NBk. destruct (sstep c0 s0 flush HC0 HFB s HF) as [_ OUT].
      destruct (st_sbody s flush) as [s1 o]. cbn [fst snd] in NBk, OUT |- *.
      destruct o as [| |bs]; [| contradiction | cbn; discriminate].
      destruct OUT as [HF1 Hm1]. apply IH; [exact F0 | exact HF1 | lia].
  Qed.

  Lemma phi0_add : forall a L, 0 <= a -> 0 <= L -> phi0 a + L <= phi0 (a + L).
  Proof. intros a L Ha HL. pose proof (phi0_mono a (a + L) ltac:(lia)). unfold phi0 in *. pose proof (Z.div_le_mono a (a + L) KBLK ltac:(unfold KBLK; lia) ltac:(lia)). lia. Qed.

  Lemma btail_flush : forall u, TAILOK c0 s0 u ->
    cov u = ds_strstart u - ds_block_start u -> (forall j, 0 <= j < nsym u -> near3 u j) -> nbP u -> 0 <= Apos u ->
    let x' := flush_block_only (tail_st u) 1 in Psi u <= Psi x' + 5 /\ 0 <= Apos x'.
  Proof.
    intros u (D & V & XX & B & HK & Ho & Hst & Hm & Hp & Hl0 & Hma0 & Hsn & Hstr & FE & XD & TI) CV NR NB HA x'.
    pose proof (dwf_sizes u D) as (Sw & _).
    assert (Hv : 0 <= (if ds_strstart u <? MIN_MATCH - 1 then ds_strstart u else MIN_MATCH - 1) <= ds_strstart u
                 /\ (if ds_strstart u <? MIN_MATCH - 1 then ds_strstart u else MIN_MATCH - 1) <= ds_w_size u).
    { destruct (Z.ltb_spec (ds_strstart u) (MIN_MATCH - 1)); unfold MIN_MATCH in *; lia. }
    destruct (tail_insert_facts u _ (proj1 Hv) (proj2 Hv) D XX B FE XD) as (Dst & XXst & _ & FEst & _).
    change (set_insert u (if ds_strstart u <? MIN_MATCH - 1 then ds_strstart u else MIN_MATCH - 1)) with (tail_st u) in Dst, XXst, FEst.
    set (u2 := tail_st u) in *.
    assert (Efs : forall A (g : deflate_state -> A), (forall x v, g (set_insert x v) = g x) -> g u2 = g u) by (intros A g Hg; subst u2; unfold tail_st; apply Hg).
    assert (Estrm : ds_strm u2 = ds_strm u) by (apply Efs; reflexivity).
    assert (P2 : FLP u2).
    { split; [exact Dst|]. split; [exact (SV_strm c0 u u2 Estrm V)|]. split; [exact XXst|]. split; [exact (FEst 0 ltac:(lia))|].
      split; [rewrite (Efs _ ds_status) by reflexivity; exact Hst|]. split; [rewrite (Efs _ dmode) by reflexivity; rewrite Hm; lia|].
      split; [rewrite (Efs _ KV) by reflexivity; exact HK|].
      split; [rewrite (Efs _ cov), (Efs _ ds_strstart), (Efs _ ds_block_start) by reflexivity; exact CV|].
      split; [intros j Hj; rewrite (Efs _ nsym) in Hj by reflexivity; exact (near_same u u2 eq_refl eq_refl eq_refl NR j Hj)|].
      split; [rewrite (Efs _ nbP) by reflexivity; exact NB | rewrite (Efs _ Apos) by reflexivity; exact HA]. }
    destruct (bflush_gen u2 1 P2 (FEst 1 ltac:(lia)) ltac:(lia)) as (HM & EA & _). fold x' in HM, EA.
    assert (EP : Psi u2 = Psi u) by (apply Efs; reflexivity).
    assert (EA2 : Apos u2 = Apos u) by (apply Efs; reflexivity).
    pose proof (fe_diff _ _ (FEst 1 ltac:(lia))) as Fd.
    pose proof (phi0_add (Apos u2) (ds_strstart u2 - ds_block_start u2) ltac:(lia) ltac:(lia)) as PA.
    split; [rewrite <- EP; unfold Psi; rewrite EA; lia | rewrite EA; lia].
  Qed.

  Lemma btail_lit_aux : forall s1 s5, COV s1 -> 0 <= Apos s1 -> ds_match_available s1 = 1 -> 0 <= nsym s1 ->
    tally_keep s1 s5 -> nsym s5 = nsym s1 + 1 -> sym_dist s5 (3 * nsym s1) = 0 ->
    (forall j, 0 <= j < nsym s1 -> sym_dist s5 (3 * j) = sym_dist s1 (3 * j) /\ sym_lc s5 (3 * j) = sym_lc s1 (3 * j)) ->
    let u := set_match_available s5 0 in
    cov u = ds_strstart u - ds_block_start u /\ (forall j, 0 <= j < nsym u -> near3 u j) /\ nbP u
    /\ 0 <= Apos u /\ Psi u = Psi s1.
  Proof.
    intros s1 s5 HC HA M1 N0 TK N5 Dn OLD u.
    destruct TK as (Kstrm & _ & _ & _ & Klook & Kstr & Kbs & _ & _ & _ & _ & _ & Kpd & _ & Kbv & _ & _ & _ & _ & Kws & _).
    assert (Vp : ds_pending_buf u = ds_pending_buf s5) by reflexivity.
    assert (Vl : ds_lit_bufsize u = ds_lit_bufsize s5) by reflexivity.
    assert (Vn : ds_sym_next u = ds_sym_next s5) by reflexivity.
    assert (Ustr : ds_strstart u = ds_strstart s5) by reflexivity.
    assert (Ubs : ds_block_start u = ds_block_start s5) by reflexivity.
    assert (Uws : ds_w_size u = ds_w_size s5) by reflexivity.
    assert (Ustrm : ds_strm u = ds_strm s5) by reflexivity.
    assert (Ulook : ds_lookahead u = ds_lookahead s5) by reflexivity.
    assert (Upd : ds_pending u = ds_pending s5) by reflexivity.
    assert (Ubv : ds_bi_valid u = ds_bi_valid s5) by reflexivity.
    clearbody u.
    pose proof (cv_cov _ HC) as CC. rewrite M1 in CC.
    assert (C5 : cov s5 = ds_strstart s1 - ds_block_start s1).
    { rewrite (cov_snoc s1 s5 N0 N5 OLD), (symlen_lit s5 _ Dn), CC. lia. }
    assert (EA : Apos u = Apos s1) by (unfold Apos; rewrite Ustrm, Ulook, Ustr, Ubs, Kstrm, Klook, Kstr, Kbs; reflexivity).
    split; [rewrite (cov_same s5 u Vp Vl Vn), C5, Ustr, Ubs, Kstr, Kbs; reflexivity|].
    split. { apply (near_same s5 u Vp Vl Vn). apply (near_snoc s1 s5 N0 N5 OLD); [exact (cv_near _ HC) | exact (near3_lit s5 _ Dn)]. }
    split; [unfold nbP; rewrite Ubs, Uws, Ustr, Kbs, Kws, Kstr; exact (cv_nb _ HC)|].
    split; [rewrite EA; exact HA|].
    unfold Psi. rewrite EA. f_equal. unfold Mc, olen, Mloc. rewrite Ustrm, Upd, Ubv, Kstrm, Kpd, Kbv. reflexivity.
  Qed.

  Lemma btail_state : forall s1, STI c0 s0 s1 -> ds_lookahead s1 = 0 -> BT s1 ->
    let u := if negb (ds_match_available s1 =? 0) then break1_st s1 else s1 in
    TAILOK c0 s0 u /\ cov u = ds_strstart u - ds_block_start u /\ (forall j, 0 <= j < nsym u -> near3 u j) /\ nbP u
    /\ 0 <= Apos u /\ Psi u = Psi s1.
  Proof.
    intros s1 HF Hl0 [HC HA] u.
    pose proof (STI_facts c0 s0 s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & Hma11 & H31).
    subst u. destruct (Z.eqb_spec (ds_match_available s1) 0) as [M0|M0]; cbn [negb].
    - split; [exact (TAILOK_STI c0 s0 HC0 s1 HF Hl0 M0)|]. pose proof (cv_cov _ HC) as CC. rewrite M0 in CC.
      split; [lia|]. split; [exact (cv_near _ HC)|]. split; [exact (cv_nb _ HC)|]. split; [exact HA | reflexivity].
    - assert (M1 : ds_match_available s1 = 1) by lia.
      assert (EB : break1_st s1 = set_match_available (fst (tr_tally_lit s1 (arr_get (ds_window s1) (ds_strstart s1 - 1)))) 0)
        by (unfold break1_st; rewrite (proj1 (slit_tally_eq s1)); reflexivity).
      rewrite EB.
      split; [exact (TAILOK_lit c0 s0 HC0 s1 HF Hl0 M1)|].
      pose proof (DX_BQ s1 X) as BQ1. pose proof (df_tl _ D) as TL. unfold tree_lens in TL.
      destruct (BQ_tally_lit s1 BQ1 ltac:(rewrite Hsn, (df_bl _ D); lia) ltac:(lia) ltac:(lia) ltac:(unfold L_CODES; lia)
                  (arr_get (ds_window s1) (ds_strstart s1 - 1))) as (_ & N5 & Dn & _ & OLD).
      pose proof (tally_lit_facts s1 (arr_get (ds_window s1) (ds_strstart s1 - 1))) as (TK & _).
      exact (btail_lit_aux s1 _ HC HA M1 (proj1 (proj2 BQ1)) TK N5 Dn OLD).
  Qed.

  Lemma keeps_CF : keeps CF true true.
  Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

  Lemma CF_TS : forall a b, TS b = TS a -> CF b = CF a.
  Proof.
    intros a b E. pose proof (TS_fields _ _ E) as ((_ & _ & _ & _ & El & Es) & _ & (_ & Ew & Est & _) & _ & (Estrm & _) & _).
    unfold CF, fwT. rewrite El, Es, Ew, Est, Estrm. reflexivity.
  Qed.

  Lemma CF_tally_keep : forall a b, tally_keep a b -> CF b = CF a.
  Proof.
    intros a b K. unfold tally_keep in K.
    destruct K as (Estrm & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & El & Es & _ & _ & _ & _ & Est & Ew & _).
    unfold CF, fwT. rewrite El, Es, Ew, Est, Estrm. reflexivity.
  Qed.

  Lemma CF_set_match_available : forall u v, CF (set_match_available u v) = CF u. Proof. reflexivity. Qed.
  Lemma CF_set_match_length : forall u v, CF (set_match_length u v) = CF u. Proof. reflexivity. Qed.
  Lemma CF_set_strstart : forall u v, CF (set_strstart u v) = CF u. Proof. reflexivity. Qed.
  Lemma CF_set_lookahead : forall u v, CF (set_lookahead u v) = CF u. Proof. reflexivity. Qed.
  Lemma CF_set_prev_length : forall u v, CF (set_prev_length u v) = CF u. Proof. reflexivity. Qed.
  Lemma CF_set_block_start : forall u v, CF (set_block_start u v) = CF u. Proof. reflexivity. Qed.
  Lemma CF_set_insert : forall u v, CF (set_insert u v) = CF u. Proof. reflexivity. Qed.

  Lemma CF_tr_flush_bits : forall u, CF (tr_flush_bits u) = CF u.
  Proof. intros u. destruct (tr_flush_bits_cases u) as [E|[E|E]]; rewrite E; reflexivity. Qed.
  Lemma CF_fp_tail : forall u len, CF (fp_tail u len) = CF u.
  Proof. intros u len. unfold fp_tail. destruct (_ =? 0); reflexivity. Qed.
  Lemma CF_flush_pending : forall u, CF (flush_pending u) = CF u.
  Proof. intros u. rewrite flush_pending_eq. cbv zeta. destruct (_ =? 0); rewrite ?CF_fp_tail; apply CF_tr_flush_bits. Qed.
  Lemma CF_tfb : forall u buf len last, CF (tr_flush_block u buf len last) = CF u.
  Proof. intros. rewrite (k_tr_flush_block CF keeps_CF). unfold tfb_X0. destruct (_ && _); [destruct u|]; reflexivity. Qed.

  Lemma CF_flush_block_only : forall x last, CF (flush_block_only x last) = CF x.
  Proof. intros x last. rewrite flush_block_only_eq'. rewrite CF_flush_pending, CF_set_block_start, CF_tfb. reflexivity. Qed.

  Lemma CF_bflush : forall x b, CF (fst (st_bflush x b)) = CF x.
  Proof. intros x b. rewrite fst_st_bflush. destruct b; [apply CF_flush_block_only | reflexivity]. Qed.

  Lemma CF_slow_insert : forall n s mi, CF (deflate_slow_insert n s mi) = CF s.
  Proof.
    induction n as [|n IH]; intros s mi; [reflexivity|].
    cbn [deflate_slow_insert]. unfold insert_string.
    destruct (ds_strstart (set_strstart s (ds_strstart s + 1)) <=? mi); dsred;
      (destruct (negb _); [rewrite IH|]; unfold CF, fwT; dsred; reflexivity).
  Qed.

  Lemma CF_sdist : forall x, CF (fst (st_sdist x)) = CF x.
  Proof.
    intros x. unfold st_sdist.
    pose proof (tally_dist_facts x (wrap32 (ds_strstart x - 1 - ds_prev_match x)) (ds_prev_length x - 3)) as (TK & _). cbv zeta in TK.
    pose proof (CF_tally_keep _ _ TK) as E.
    destruct (tr_tally_dist x _ _) as [t b]. cbn [fst] in E |- *. rewrite <- E.
    rewrite CF_set_strstart, CF_set_match_length, CF_set_match_available, CF_slow_insert, CF_set_prev_length, CF_set_lookahead. reflexivity.
  Qed.

  Lemma CF_slit : forall x, CF (fst (st_slit x)) = CF x.
  Proof.
    intros x. unfold st_slit.
    pose proof (tally_lit_facts x (arr_get (ds_window x) (ds_strstart x - 1))) as (TK & _). cbv zeta in TK.
    pose proof (CF_tally_keep _ _ TK) as E.
    destruct (tr_tally_lit x _) as [t b]. cbn [fst] in E |- *. rewrite <- E.
    rewrite CF_set_lookahead, CF_set_strstart. destruct b; [apply CF_flush_block_only | reflexivity].
  Qed.

  Lemma CF_decide : forall x, CF (fst (st_decide x)) = CF x.
  Proof.
    intros x. unfold st_decide. destruct (dist_cond x); [rewrite CF_bflush; apply CF_sdist|].
    destruct (negb _); [apply CF_slit|]. unfold st_avail. cbn [fst].
    rewrite CF_set_lookahead, CF_set_strstart, CF_set_match_available. reflexivity.
  Qed.

  Lemma CF_fill : forall s, CF (fst (st_fill s flush)) = CF s.
  Proof.
    intros s. unfold st_fill. destruct (ds_lookahead s <? MIN_LOOKAHEAD); [| reflexivity].
    destruct (_ && _); [apply CF_fill_window|]. destruct (_ =? 0); apply CF_fill_window.
  Qed.

  Lemma cfstep : forall s, STI c0 s0 s -> CF (fst (st_sbody s flush)) = CF s.
  Proof.
    intros s HF. unfold st_sbody.
    pose proof (CF_fill s) as E1.
    pose proof (sfill_stage c0 s0 flush HC0 s HF) as FS. cbv zeta in FS.
    destruct FS as (HF1 & _ & _ & _ & _ & Ews1 & Hnone & _ & _ & Hss1 & _).
    set (s1 := fst (st_fill s flush)) in *.
    destruct (snd (st_fill s flush)) as [o|] eqn:Eo; [cbn [fst]; exact E1|].
    pose proof (Hnone eq_refl) as Hl1.
    pose proof (shash_stage c0 s0 s1 HF1 Hl1) as HS. cbv zeta in HS. destruct HS as [HR Hlm].
    rewrite <- Ews1 in Hss1.
    pose proof (slm_stage c0 s0 s1 (fst (st_hash s1)) (snd (st_hash s1)) HF1 Hl1 Hss1 HR Hlm) as LM. cbv zeta in LM. destruct LM as [MR _].
    unfold st_srest. rewrite CF_decide. rewrite <- E1. apply CF_TS. exact (proj1 MR).
  Qed.

  Lemma cfloop : forall fuel s, STI c0 s0 s -> lz_meas s < Z.of_nat fuel -> CF (fst (deflate_slow_loop fuel s flush)) = CF s.
  Proof.
    induction fuel as [|f IH]; intros s HF Hm; [reflexivity|].
    cbn [deflate_slow_loop]. rewrite st_sbody_eq.
    pose proof (cfstep s HF) as E1. destruct (sstep c0 s0 flush HC0 HFB s HF) as [_ OUT].
    destruct (st_sbody s flush) as [s1 o]. cbn [fst snd] in E1, OUT |- *.
    destruct o as [| |bs]; cbn [fst]; try exact E1.
    destruct OUT as [HF1 Hm1]. rewrite (IH s1 HF1 ltac:(lia)). exact E1.
  Qed.

  Lemma CF_break1 : forall x, CF (break1_st x) = CF x.
  Proof.
    intros x. unfold break1_st. rewrite CF_set_match_available. rewrite <- (proj1 (slit_tally_eq x)).
    pose proof (tally_lit_facts x (arr_get (ds_window x) (ds_strstart x - 1))) as (TK & _). cbv zeta in TK.
    exact (CF_tally_keep _ _ TK).
  Qed.

  Lemma CF_tail_st : forall u, CF (tail_st u) = CF u.
  Proof. intros u. unfold tail_st. apply CF_set_insert. Qed.

  Lemma sbody_break_ain : forall s, STI c0 s0 s -> snd (st_sbody s flush) = LBreak ->
    cs_avail_in (ds_strm (fst (st_sbody s flush))) = 0.
  Proof.
    intros s HF. unfold st_sbody, st_fill.
    pose proof HF as (HDC & _ & _ & Hm & Hst & _).
    destruct (Z.ltb_spec (ds_lookahead s) MIN_LOOKAHEAD) as [Hlt|Hge]; cbn [fst snd].
    2:{ unfold st_srest. intros E. exfalso. exact (st_decide_nobreak _ E). }
    pose proof (DC_fill_window c0 s HC0w HDC ltac:(rewrite Hm; lia) Hst Hlt) as FW. cbv zeta in FW.
    destruct FW as (_ & _ & _ & _ & _ & _ & HX & _).
    destruct (Z.ltb_spec (ds_lookahead (fill_window s)) MIN_LOOKAHEAD) as [L1|L1]; cbn [andb].
    - destruct (flush =? Z_NO_FLUSH); cbn [fst snd]; [intros E; discriminate E|].
      destruct (ds_lookahead (fill_window s) =? 0); cbn [fst snd]; [intros _; exact (proj1 (HX L1))|].
      unfold st_srest. intros E. exfalso. exact (st_decide_nobreak _ E).
    - destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [E0|E0]; cbn [fst snd]; [intros _|].
      + exfalso. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in L1. lia.
      + unfold st_srest. intros E. exfalso. exact (st_decide_nobreak _ E).
  Qed.
  Lemma loop_none_ain : forall fuel s, STI c0 s0 s -> lz_meas s < Z.of_nat fuel ->
    snd (deflate_slow_loop fuel s flush) = None -> cs_avail_in (ds_strm (fst (deflate_slow_loop fuel s flush))) = 0.
  Proof.
    induction fuel as [|f IH]; intros s HF Hm.
    - exfalso. pose proof (STI_facts c0 s0 s HF) as (D & _ & V & _). pose proof (sv_ain _ _ V). pose proof (df_look _ D).
      unfold lz_meas in Hm. cbn [Z.of_nat] in Hm. lia.
    - cbn [deflate_slow_loop]. rewrite st_sbody_eq.
      pose proof (sbody_break_ain s HF) as BA. destruct (sstep c0 s0 flush HC0 HFB s HF) as [_ OUT].
      destruct (st_sbody s flush) as [s1 o]. cbn [fst snd] in BA, OUT |- *.
      destruct o as [| |bs]; cbn [fst snd].
      + destruct OUT as [HF1 Hm1]. apply IH; [exact HF1 | lia].
      + intros _. exact (BA eq_refl).
      + intros E; discriminate E.
  Qed.

  Definition AIN (s : deflate_state) : Z := cs_avail_in (ds_strm s).
  Lemma AIN_def : forall s, AIN s = cs_avail_in (ds_strm s). Proof. reflexivity. Qed.
  Lemma keeps_AIN : keeps AIN true true.
  Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.
  Lemma AIN_tr_flush_bits : forall u, AIN (tr_flush_bits u) = AIN u.
  Proof. intros u. destruct (tr_flush_bits_cases u) as [E|[E|E]]; rewrite E; reflexivity. Qed.
  Lemma AIN_fp_tail : forall u len, AIN (fp_tail u len) = AIN u.
  Proof. intros u len. unfold fp_tail. destruct (_ =? 0); reflexivity. Qed.
  Lemma AIN_flush_pending : forall u, AIN (flush_pending u) = AIN u.
  Proof. intros u. rewrite flush_pending_eq. cbv zeta. destruct (_ =? 0); rewrite ?AIN_fp_tail; apply AIN_tr_flush_bits. Qed.
  Lemma AIN_tfb : forall u buf len last, AIN (tr_flush_block u buf len last) = AIN u.
  Proof. intros. rewrite (k_tr_flush_block AIN keeps_AIN). unfold tfb_X0. destruct (_ && _); [destruct u|]; reflexivity. Qed.
  Lemma AIN_set_block_start : forall u v, AIN (set_block_start u v) = AIN u. Proof. reflexivity. Qed.
  Lemma AIN_flush_block_only : forall x last, AIN (flush_block_only x last) = AIN x.
  Proof. intros x last. rewrite flush_block_only_eq'. rewrite AIN_flush_pending, AIN_set_block_start, AIN_tfb. reflexivity. Qed.
  Lemma AIN_set_match_available : forall u v, AIN (set_match_available u v) = AIN u. Proof. reflexivity. Qed.
  Lemma AIN_set_insert : forall u v, AIN (set_insert u v) = AIN u. Proof. reflexivity. Qed.
  Lemma AIN_break1 : forall x, AIN (break1_st x) = AIN x.
  Proof.
    intros x. unfold break1_st. rewrite AIN_set_match_available. rewrite <- (proj1 (slit_tally_eq x)).
    pose proof (tally_lit_facts x (arr_get (ds_window x) (ds_strstart x - 1))) as (TK & _). cbv zeta in TK.
    unfold AIN. rewrite (proj1 TK). reflexivity.
  Qed.
  Lemma AIN_tail_st : forall u, AIN (tail_st u) = AIN u.
  Proof. intros u. unfold tail_st. apply AIN_set_insert. Qed.

  Definition GI (s : deflate_state) := (ds_gzhead s, ds_insert s).
  Lemma GI_fields : forall a b, GI b = GI a -> GZ b = GZ a /\ INS b = INS a.
  Proof. intros a b E. unfold GI in E. injection E as E1 E2. split; assumption. Qed.

  Lemma GI_TS : forall a b, TS b = TS a -> GI b = GI a.
  Proof.
    intros a b E. pose proof (TS_fields _ _ E) as (_ & (Ei & _) & _ & _ & _ & (_ & _ & _ & Eg & _)).
    unfold GI. rewrite Ei, Eg. reflexivity.
  Qed.
  Lemma GI_PF : forall a b, PF b = PF a -> GI b = GI a.
  Proof.
    intros a b E. pose proof (PF_fields _ _ E) as (_ & (_ & Ei & _) & _ & (_ & _ & _ & Eg & _)).
    unfold GI. rewrite Ei, Eg. reflexivity.
  Qed.
  Lemma GI_flush_block_only : forall x last, GI (flush_block_only x last) = GI x.
  Proof. intros x last. apply GI_PF. rewrite flush_block_only_eq'. rewrite PF_flush_pending, PF_set_block_start, PF_tfb. reflexivity. Qed.
  Lemma GI_bflush : forall x b, GI (fst (st_bflush x b)) = GI x.
  Proof. intros x b. rewrite fst_st_bflush. destruct b; [apply GI_flush_block_only | reflexivity]. Qed.

  Lemma GI_tally_lit : forall x c, GI (fst (tr_tally_lit x c)) = GI x.
  Proof. intros x c. unfold tr_tally_lit, sym_buf_set, set_Freq, Freq, tree_fc, set_tree_fc. dsred. reflexivity. Qed.
  Lemma GI_tally_dist : forall x d l, GI (fst (tr_tally_dist x d l)) = GI x.
  Proof. intros x d l. unfold tr_tally_dist, sym_buf_set, set_Freq, Freq, tree_fc, set_tree_fc. dsred. reflexivity. Qed.

  Lemma GI_set_match_available : forall u v, GI (set_match_available u v) = GI u. Proof. reflexivity. Qed.
  Lemma GI_set_match_length : forall u v, GI (set_match_length u v) = GI u. Proof. reflexivity. Qed.
  Lemma GI_set_strstart : forall u v, GI (set_strstart u v) = GI u. Proof. reflexivity. Qed.
  Lemma GI_set_lookahead : forall u v, GI (set_lookahead u v) = GI u. Proof. reflexivity. Qed.
  Lemma GI_set_prev_length : forall u v, GI (set_prev_length u v) = GI u. Proof. reflexivity. Qed.

  Lemma GI_slow_insert : forall n s mi, GI (deflate_slow_insert n s mi) = GI s.
  Proof.
    induction n as [|n IH]; intros s mi; [reflexivity|].
    cbn [deflate_slow_insert]. unfold insert_string.
    destruct (ds_strstart (set_strstart s (ds_strstart s + 1)) <=? mi); dsred;
      (destruct (negb _); [rewrite IH|]; unfold GI; dsred; reflexivity).
  Qed.

  Lemma GI_sdist : forall x, GI (fst (st_sdist x)) = GI x.
  Proof.
    intros x. unfold st_sdist.
    pose proof (GI_tally_dist x (wrap32 (ds_strstart x - 1 - ds_prev_match x)) (ds_prev_length x - 3)) as E.
    destruct (tr_tally_dist x _ _) as [t b]. cbn [fst] in E |- *. rewrite <- E.
    rewrite GI_set_strstart, GI_set_match_length, GI_set_match_available, GI_slow_insert, GI_set_prev_length, GI_set_lookahead. reflexivity.
  Qed.
  Lemma GI_slit : forall x, GI (fst (st_slit x)) = GI x.
  Proof.
    intros x. unfold st_slit.
    pose proof (GI_tally_lit x (arr_get (ds_window x) (ds_strstart x - 1))) as E.
    destruct (tr_tally_lit x _) as [t b]. cbn [fst] in E |- *. rewrite <- E.
    rewrite GI_set_lookahead, GI_set_strstart. destruct b; [apply GI_flush_block_only | reflexivity].
  Qed.
  Lemma GI_decide : forall x, GI (fst (st_decide x)) = GI x.
  Proof.
    intros x. unfold st_decide. destruct (dist_cond x); [rewrite GI_bflush; apply GI_sdist|].
    destruct (negb _); [apply GI_slit|]. unfold st_avail. cbn [fst].
    rewrite GI_set_lookahead, GI_set_strstart, GI_set_match_available. reflexivity.
  Qed.

  Lemma GZINS_fill : forall s, STI c0 s0 s -> GZ (fst (st_fill s flush)) = GZ s /\ (INS s = 0 -> INS (fst (st_fill s flush)) = 0).
  Proof.
    intros s HF. pose proof HF as (_ & HK & _). pose proof (KV_fields _ _ HK) as (Ews & _).
    assert (Hw : MIN_LOOKAHEAD <= ds_w_size s) by (rewrite Ews, HWS; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; lia).
    destruct (GZINS_fill_window s) as [G I].
    unfold st_fill. destruct (ds_lookahead s <? MIN_LOOKAHEAD); [| cbn [fst]; split; [reflexivity | intros H; exact H]].
    destruct (_ && _); [cbn [fst]; split; [exact G | intros H; exact (I H Hw)]|].
    destruct (_ =? 0); cbn [fst]; (split; [exact G | intros H; exact (I H Hw)]).
  Qed.

  Lemma gistep : forall s, STI c0 s0 s -> GZ (fst (st_sbody s flush)) = GZ s /\ (INS s = 0 -> INS (fst (st_sbody s flush)) = 0).
  Proof.
    intros s HF. unfold st_sbody.
    destruct (GZINS_fill s HF) as [G1 I1].
    pose proof (sfill_stage c0 s0 flush HC0 s HF) as FS. cbv zeta in FS.
    destruct FS as (HF1 & _ & _ & _ & _ & Ews1 & Hnone & _ & _ & Hss1 & _).
    set (s1 := fst (st_fill s flush)) in *.
    destruct (snd (st_fill s flush)) as [o|] eqn:Eo; [cbn [fst]; split; assumption|].
    pose proof (Hnone eq_refl) as Hl1.
    pose proof (shash_stage c0 s0 s1 HF1 Hl1) as HS. cbv zeta in HS. destruct HS as [HR Hlm].
    rewrite <- Ews1 in Hss1.
    pose proof (slm_stage c0 s0 s1 (fst (st_hash s1)) (snd (st_hash s1)) HF1 Hl1 Hss1 HR Hlm) as LM. cbv zeta in LM. destruct LM as [MR _].
    unfold st_srest.
    destruct (GI_fields _ _ (GI_decide (st_lm (prev_st (fst (st_hash s1))) (snd (st_hash s1))))) as [G2 I2].
    destruct (GI_fields _ _ (GI_TS _ _ (proj1 MR))) as [G3 I3].
    split; [rewrite G2, G3; exact G1 | intros H; rewrite I2, I3; exact (I1 H)].
  Qed.

  Lemma giloop : forall fuel s, STI c0 s0 s -> lz_meas s < Z.of_nat fuel ->
    GZ (fst (deflate_slow_loop fuel s flush)) = GZ s /\ (INS s = 0 -> INS (fst (deflate_slow_loop fuel s flush)) = 0).
  Proof.
    induction fuel as [|f IH]; intros s HF Hm; [cbn [deflate_slow_loop fst]; split; [reflexivity | intros H; exact H]|].
    cbn [deflate_slow_loop]. rewrite st_sbody_eq.
    destruct (gistep s HF) as [G1 I1]. destruct (sstep c0 s0 flush HC0 HFB s HF) as [_ OUT].
    destruct (st_sbody s flush) as [s1 o]. cbn [fst snd] in G1, I1, OUT |- *.
    destruct o as [| |bs]; cbn [fst]; try (split; assumption).
    destruct OUT as [HF1 Hm1]. destruct (IH s1 HF1 ltac:(lia)) as [G2 I2].
    split; [rewrite G2; exact G1 | intros H; exact (I2 (I1 H))].
  Qed.

  Lemma GZ_set_match_available : forall u v, GZ (set_match_available u v) = GZ u. Proof. reflexivity. Qed.
  Lemma GZ_break1 : forall x, GZ (break1_st x) = GZ x.
  Proof.
    intros x. unfold break1_st. rewrite GZ_set_match_available. rewrite <- (proj1 (slit_tally_eq x)).
    exact (proj1 (GI_fields _ _ (GI_tally_lit x (arr_get (ds_window x) (ds_strstart x - 1))))).
  Qed.
  Lemma GZ_set_insert : forall u v, GZ (set_insert u v) = GZ u. Proof. reflexivity. Qed.
End SlowB.

Lemma deflate_tail_finish : forall x,
  fst (deflate_tail x Z_FINISH) = flush_block_only x 1 /\ snd (deflate_tail x Z_FINISH) <> need_more
  /\ (snd (deflate_tail x Z_FINISH) = finish_started \/ snd (deflate_tail x Z_FINISH) = finish_done).
Proof.
  intros x. unfold deflate_tail. change (Z_FINISH =? Z_FINISH) with true. cbv iota. rewrite flush_block_eq'.
  destruct (cs_avail_out (ds_strm (flush_block_only x 1)) =? 0); cbn; (split; [reflexivity|]); (split; [discriminate|]); [left | right]; reflexivity.
Qed.

Theorem bslow : forall c0 s flush IN0, FB_CALL -> BFPRE c0 s flush -> dmode s = 4 ->
  ds_lit_bufsize s = 16384 -> ds_w_size s = 32768 -> flush = Z_NO_FLUSH \/ flush = Z_FINISH -> BT IN0 s ->
  let r := deflate_slow s flush in
  (snd r = need_more -> BT IN0 (fst r) /\ Psi IN0 s <= Psi IN0 (fst r))
  /\ (snd r <> need_more -> flush = Z_FINISH /\ 0 <= Apos IN0 (fst r) /\ Psi IN0 s <= Psi IN0 (fst r) + 5
                            /\ (snd r = finish_started \/ snd r = finish_done) /\ cs_avail_in (ds_strm (fst r)) = 0)
  /\ CF (fst r) = CF s
  /\ GZ (fst r) = GZ s /\ (snd r = need_more -> INS s = 0 -> INS (fst r) = 0).
Proof.
  intros c0 s flush IN0 HFB (HC0 & HDC & Hp & Hst & Hfl) Hm HL HW HFL HB.
  assert (HF : STI c0 s s).
  { split; [exact HDC|]. split; [reflexivity|]. split; [exact Hp|]. split; [exact Hm|]. split; [exact Hst | apply OUTLE_refl]. }
  pose proof HDC as [[D X] V].
  assert (Hmz : 0 <= lz_meas s) by (unfold lz_meas; pose proof (df_look _ D); pose proof (sv_ain _ _ V); lia).
  destruct (bloop c0 s flush IN0 HC0 HFB HL HW (lz_fuel s) s HF (lz_fuel_meas s Hmz) HB) as [BL EL].
  destruct (sloop c0 s flush HC0 HFB (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as [_ HR].
  pose proof (loop_noflush_some c0 s flush HC0 HFB (lz_fuel s) s) as NS.
  pose proof (cfloop c0 s flush HC0 HFB (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as CL.
  pose proof (loop_none_ain c0 s flush HC0 HFB (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as AL.
  destruct (giloop c0 s flush HC0 HFB HW (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as [GL IL].
  cbv zeta. rewrite deflate_slow_eq.
  set (lp := deflate_slow_loop (lz_fuel s) s flush) in *. clearbody lp. destruct lp as [s1 o]. cbn [fst snd] in *.
  destruct o as [bs|].
  - cbn [fst snd]. destruct HR as (_ & _ & _ & ->).
    split; [intros _; split; [exact BL | exact EL]|]. split; [intros HH; contradiction|]. split; [exact CL|].
    split; [exact GL | intros _ H0; exact (IL H0)].
  - destruct HFL as [F0|F4]; [exfalso; exact (NS F0 HF (lz_fuel_meas s Hmz) eq_refl)|].
    destruct HR as [HF1 Hl1]. specialize (AL eq_refl).
    destruct (btail_state c0 s IN0 HC0 s1 HF1 Hl1 BL) as (TU & CU & NRU & NBU & HAU & EPU).
    assert (CU' : CF (if negb (ds_match_available s1 =? 0) then break1_st s1 else s1) = CF s)
      by (destruct (negb _); [rewrite CF_break1|]; exact CL).
    assert (AU : AIN (if negb (ds_match_available s1 =? 0) then break1_st s1 else s1) = 0)
      by (destruct (negb _); [rewrite AIN_break1|]; exact AL).
    assert (GU : GZ (if negb (ds_match_available s1 =? 0) then break1_st s1 else s1) = GZ s)
      by (destruct (negb _); [rewrite GZ_break1|]; exact GL).
    cbv zeta in *.
    set (u := if negb (ds_match_available s1 =? 0) then break1_st s1 else s1) in *. clearbody u.
    destruct (btail_flush c0 s IN0 HC0 HFB HL HW u TU CU NRU NBU HAU) as [HP HA'].
    subst flush. destruct (deflate_tail_finish (tail_st u)) as (E1 & E2 & E3).
    split; [intros HH; exfalso; exact (E2 HH)|].
    split.
    + intros _. rewrite E1. split; [reflexivity|]. split; [exact HA'|]. split; [lia|]. split; [exact E3|].
      rewrite <- (AIN_def (flush_block_only (tail_st u) 1)). rewrite AIN_flush_block_only, AIN_tail_st. exact AU.
    + rewrite E1. split; [rewrite CF_flush_block_only, CF_tail_st; exact CU'|].
      split; [| intros HH; exfalso; exact (E2 HH)].
      rewrite (proj1 (GI_fields _ _ (GI_flush_block_only (tail_st u) 1))). unfold tail_st. rewrite GZ_set_insert. exact GU.
Qed.

