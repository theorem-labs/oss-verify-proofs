(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import DeflM.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel DeflFastModel DeflSlowModel
  DeflateInvHash DeflateInvKeep OverlayFBS DeflRoom RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflSlowOk
  RefDeflateRel RefDeflateEnd1 RefDeflateHdrKit RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3 RefDeflateHdr4 RefDeflateHdr5 RefDeflateTrl1 RefDeflatePost
  DeflateInv DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep DeflInvFbo DeflInvFw DeflInvFast DeflInvSlow DeflInvSlow2 DeflInvCore DeflInvMain DeflInvWk FB6
  BoundArith BoundTfb BoundInv BoundSlow BoundCore BoundCall HarnessKit HarnessFacts HarnessSmallStages HarnessSmallFacts HarnessSmallBound HarnessFlush HarnessFlushFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import DeflSlow6_1 DeflSlow6_M DeflSlow6_Bridge Defl6_1 Defl6_3 Defl6_5 Defl6_6 Defl6_M DeflInst6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ExFlushIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec Require Import FlushStages FlushM BoundFlush FlushBound.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma DWF_of_dcfg : forall s, dcfg s -> 0 <= cs_avail_out (ds_strm s) < 2 ^ 32 -> DWF s.
Proof.
  intros s C AO. pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
  constructor; [exact (cf_wl _ C) | exact (cf_pl _ C) | exact (cf_hl _ C) | exact (cf_bl _ C) | lia | lia | lia | exact AO].
Qed.


Lemma set_last_flush_fields : forall s v,
  ds_status (set_last_flush s v) = ds_status s /\ ds_pending (set_last_flush s v) = ds_pending s
  /\ ds_pending_out (set_last_flush s v) = ds_pending_out s /\ ds_wrap (set_last_flush s v) = ds_wrap s
  /\ ds_level (set_last_flush s v) = ds_level s /\ ds_strategy (set_last_flush s v) = ds_strategy s
  /\ ds_strm (set_last_flush s v) = ds_strm s /\ ds_lookahead (set_last_flush s v) = ds_lookahead s
  /\ ds_strstart (set_last_flush s v) = ds_strstart s /\ ds_w_bits (set_last_flush s v) = ds_w_bits s
  /\ ds_sym_next (set_last_flush s v) = ds_sym_next s /\ ds_lit_bufsize (set_last_flush s v) = ds_lit_bufsize s.
Proof. intros s v. destruct s; repeat split; reflexivity. Qed.

Lemma level_set_last_flush : forall s v, ds_level (set_last_flush s v) = ds_level s.
Proof. intros s v. destruct s; reflexivity. Qed.

Lemma hdr_st_fields : forall X,
  ds_level (hdr_st X) = ds_level X /\ ds_strategy (hdr_st X) = ds_strategy X /\ ds_wrap (hdr_st X) = ds_wrap X
  /\ ds_lookahead (hdr_st X) = ds_lookahead X /\ cs_avail_in (ds_strm (hdr_st X)) = cs_avail_in (ds_strm X)
  /\ ds_status (hdr_st X) = 113.
Proof. intros X. unfold hdr_st. destruct X; cbn. destruct ds_strm; cbn. repeat split; reflexivity. Qed.

Lemma set_status_fields : forall s v,
  ds_pending (set_status s v) = ds_pending s /\ ds_pending_out (set_status s v) = ds_pending_out s
  /\ ds_wrap (set_status s v) = ds_wrap s /\ ds_level (set_status s v) = ds_level s /\ ds_strm (set_status s v) = ds_strm s
  /\ ds_sym_next (set_status s v) = ds_sym_next s /\ ds_bi_valid (set_status s v) = ds_bi_valid s /\ ds_status (set_status s v) = v
  /\ ds_lookahead (set_status s v) = ds_lookahead s.
Proof. intros s v. destruct s; repeat split; reflexivity. Qed.

Lemma ta_post_fold : forall X,
  ta_post X = fold_left put_byte [cs_adler (ds_strm X) / 2 ^ 24; cs_adler (ds_strm X) / 2 ^ 16; cs_adler (ds_strm X) / 2 ^ 8; cs_adler (ds_strm X)] X.
Proof. intros X. reflexivity. Qed.

Lemma level_t2_st : forall X, ds_level (t2_st X) = ds_level X.
Proof. intros X. unfold t2_st. destruct (0 <? ds_wrap X); [destruct X|]; reflexivity. Qed.

Lemma level_bst_st : forall X bs, ds_level (bst_st X bs) = ds_level X.
Proof. intros X bs. unfold bst_st. destruct bs; try reflexivity; destruct X; reflexivity. Qed.

Lemma level_trl_st : forall X, ds_level (trl_st X) = ds_level X.
Proof. intros X. unfold trl_st. cbv zeta. destruct X; reflexivity. Qed.

Lemma level_live_tail : forall f X, ds_level (fst (live_tail f X)) = ds_level X.
Proof.
  intros f X. unfold live_tail. destruct (negb (f =? 4)); [reflexivity|]. destruct (ds_wrap X <=? 0); [reflexivity|].
  cbv zeta. cbn [fst]. rewrite level_t2_st.
  pose proof (flush_pending_keeps (trl_st X)) as (_ & _ & _ & _ & L & _). rewrite L. apply level_trl_st.
Qed.




Lemma HPBL6 : 2048 <= 65536. Proof. lia. Qed.



Lemma bi_buf_put_byte : forall s b, ds_bi_buf (put_byte s b) = ds_bi_buf s. Proof. intros s b. destruct s; reflexivity. Qed.
Lemma bi_buf_put_short : forall s w, ds_bi_buf (put_short s w) = ds_bi_buf s. Proof. intros s w. unfold put_short. rewrite !bi_buf_put_byte. reflexivity. Qed.
Lemma bi_buf_bi_windup : forall s, ds_bi_buf (bi_windup s) = 0.
Proof. intros s. unfold bi_windup. destruct (8 <? ds_bi_valid s); [| destruct (0 <? ds_bi_valid s)]; destruct s; reflexivity. Qed.
Lemma tsb0_emit : forall s, ds_bi_buf (tr_stored_block s None 0 0) = 0 /\ ds_pending_out (tr_stored_block s None 0 0) = ds_pending_out s.
Proof.
  intros s. split; [| exact (ep_pending_out _ _ (ep_tr_stored_block s None 0 0))].
  unfold tr_stored_block. cbn [negb Z.eqb].
  assert (E : forall x v, ds_bi_buf (set_pending x v) = ds_bi_buf x) by (intros x v; destruct x; reflexivity).
  rewrite E, !bi_buf_put_short. apply bi_buf_bi_windup.
Qed.
Lemma level_bd_st : forall X, 0 <= ds_bi_valid X <= 16 -> ds_level (bd_st X) = ds_level X.
Proof.
  intros X BV. unfold bd_st. cbv zeta.
  pose proof (tsb00_fields X BV) as F. cbv zeta in F. destruct F as (_ & _ & _ & _ & _ & _ & Lv1 & _).
  remember (tr_stored_block X None 0 0) as t eqn:Et. clear Et.
  pose proof (reset_fields t) as R. cbv zeta in R. destruct R as (_ & _ & _ & _ & _ & Lv3 & _).
  assert (LC : ds_level (clear_hash t) = ds_level t) by (destruct t; reflexivity).
  destruct (ds_lookahead (clear_hash t) =? 0); [rewrite Lv3; exact Lv1 | rewrite LC; exact Lv1].
Qed.

Section GEN.
  Variables (IN OCAP TOT : Z) (ds : deflate_state) (f : Z).
  Let DC := dcore 32768 32768 65536 IN OCAP TOT.
  Let ZBc := ZB 32768 32768 65536 IN OCAP TOT.
  Hypothesis D0 : DC ds.
  Hypothesis Hf : f = 3 \/ f = 4.
  Hypothesis HIN : 0 < IN < 2 ^ 31.
  Hypothesis HOCAP : 0 < OCAP < 2 ^ 31.
  Hypothesis Fai : cs_avail_in (ds_strm ds) = IN.
  Hypothesis Fao : cs_avail_out (ds_strm ds) = OCAP.
  Hypothesis Fni : cs_next_in (ds_strm ds) = 0.
  Hypothesis Sst : ds_status ds = 42 \/ ds_status ds = 113.
  Hypothesis S42 : ds_status ds = 42 -> ds_pending ds = 0 /\ ds_strstart ds = 0.
  Hypothesis Swr : ds_wrap ds = 1.
  Hypothesis Flv : ds_level ds = 6.
  Hypothesis Fsg : ds_strategy ds = 0.
  Hypothesis Fwb : ds_w_bits ds = 15.
  Variable SSAFE : deflate_state -> Z -> Prop.
  Hypothesis HSS : forall X, drun 32768 32768 65536 IN OCAP TOT X -> 4 <= ds_level X <= 9 -> lz_strat X -> ds_wrap X = 1 ->
    ds_w_size X = 32768 -> ds_hash_size X = 32768 -> SSAFE X f.

  Lemma Hf5 : -2 <= f <= 5. Proof. clear -Hf; lia. Qed.
  Lemma Hf0 : f <> 0. Proof. clear -Hf; lia. Qed.
  Lemma EPBL : ds_lit_bufsize ds * 4 = 65536. Proof. destruct D0 as [C I CL Ews Ehs Epbl]. exact Epbl. Qed.

  Theorem gen_dsafe6 : dsafe6 SSAFE ds f /\ ds_level (fst (deflate_core ds f)) = 6.
  Proof.
    pose proof D0 as DC0. pose proof (dcore_basics _ _ _ _ _ _ HPBL6 ds DC0) as BB0.
    pose proof Hf5 as Hf5'. pose proof Hf0 as Hf0'. pose proof EPBL as EPBL'.
    assert (N666 : ds_status ds <> 666) by (clear -Sst; lia).
    pose proof (dcore_set_last_flush _ _ _ _ _ _ ds f DC0 Hf5') as DC1.
    pose proof (set_last_flush_fields ds f) as (K1s & K1p & K1po & K1w & K1lv & K1sg & K1st & K1lk & K1ss & K1wb & K1sn & K1lbs).
    change (set_last_flush ds f) with (X1 ds f) in DC1, K1s, K1p, K1po, K1w, K1lv, K1sg, K1st, K1lk, K1ss, K1wb, K1sn, K1lbs.
    pose proof (dcore_basics _ _ _ _ _ _ HPBL6 _ DC1) as BB1.
    assert (PO1 : ds_pending ds = 0 -> ds_pending_out (X1 ds f) = 0).
    { intros P0. rewrite K1po. destruct DC0 as [C0 I0 CL0 W0 H0 PB0]. apply (di_po0 _ _ _ _ I0). exact P0. }
    assert (ST2 : ds_pending ds <> 0 ->
      DC (X2 ds f) /\ (cs_avail_out (ds_strm (X2 ds f)) <> 0 -> ZBc (X2 ds f))
      /\ ds_status (X2 ds f) = ds_status ds /\ ds_lookahead (X2 ds f) = ds_lookahead ds /\ ds_wrap (X2 ds f) = ds_wrap ds
      /\ ds_level (X2 ds f) = 6 /\ ds_strategy (X2 ds f) = 0 /\ cs_avail_in (ds_strm (X2 ds f)) = IN
      /\ fp_ok 65536 OCAP (X1 ds f)).
    { intros P.
      destruct DC1 as [C1 I1 CL1 W1 H1 PB1] eqn:EDC1. clear EDC1.
      assert (SN1 : ds_sym_next (X1 ds f) = 0) by (apply (di_pendsym _ _ _ _ I1); rewrite K1p; exact P).
      assert (NI : ds_status (X1 ds f) <> INIT_STATE /\ ds_status (X1 ds f) <> GZIP_STATE).
      { rewrite K1s. unfold INIT_STATE, GZIP_STATE. split; intros E; [destruct (S42 E) as (P0 & _); exact (P P0) | clear -E Sst; lia]. }
      destruct (dcore_fp _ _ _ _ _ _ HPBL6 (X1 ds f) DC1 SN1 (proj1 NI) (proj2 NI)) as (D2 & FL2 & PO2 & St2 & Lk2 & Sn2 & W2 & Lv2 & Sg2 & Ma2 & Ai2 & Ao2 & Bv2).
      change (flush_pending (X1 ds f)) with (X2 ds f) in D2, FL2, PO2, St2, Lk2, Sn2, W2, Lv2, Sg2, Ai2, Ao2.
      split; [exact D2|]. split; [intros AO; split; [exact D2 | exact (FL2 AO)]|].
      split; [rewrite St2, K1s; reflexivity|]. split; [rewrite Lk2, K1lk; reflexivity|]. split; [rewrite W2, K1w; reflexivity|].
      split; [rewrite Lv2, K1lv; exact Flv|]. split; [rewrite Sg2, K1sg; exact Fsg|]. split; [rewrite Ai2, K1st; exact Fai|].
      exact (dcore_fp_ok _ _ _ _ _ _ HPBL6 _ DC1). }
    assert (ST3 : DC (X3 ds f) /\ (G3 ds f -> ZBc (X3 ds f))
      /\ ds_status (X3 ds f) = ds_status ds /\ ds_lookahead (X3 ds f) = ds_lookahead ds /\ ds_wrap (X3 ds f) = ds_wrap ds
      /\ ds_level (X3 ds f) = 6 /\ ds_strategy (X3 ds f) = 0 /\ cs_avail_in (ds_strm (X3 ds f)) = IN
      /\ (ds_pending ds = 0 -> X3 ds f = X1 ds f)).
    { unfold G3. unfold X3.
      destruct (Z.eqb_spec (ds_pending ds) 0) as [P0|P0].
      - split; [exact DC1|]. split.
        { intros _. split; [exact DC1|]. rewrite K1p. split; [exact P0 | exact (PO1 P0)]. }
        split; [exact K1s|]. split; [exact K1lk|]. split; [exact K1w|].
        split; [rewrite K1lv; exact Flv|]. split; [rewrite K1sg; exact Fsg|]. split; [rewrite K1st; exact Fai|]. intros _; reflexivity.
      - destruct (ST2 P0) as (D2 & Z2 & St2 & Lk2 & W2 & Lv2 & Sg2 & Ai2 & _).
        split; [exact D2|]. split; [intros G; apply Z2; apply G; exact P0|].
        split; [exact St2|]. split; [exact Lk2|]. split; [exact W2|]. split; [exact Lv2|]. split; [exact Sg2|]. split; [exact Ai2|].
        intros X; exfalso; exact (P0 X). }
    destruct ST3 as (DC3 & Z3 & S3s & S3lk & S3w & S3lv & S3sg & S3ai & E31).
    pose proof (dcore_basics _ _ _ _ _ _ HPBL6 _ DC3) as BB3.
    assert (ST4h : ds_status ds = 42 ->
      fp_ok 65536 OCAP (hdr_st (X3 ds f))
      /\ DC (X4h ds f) /\ ds_status (X4h ds f) = 113 /\ (ds_pending (X4h ds f) = 0 -> ZBc (X4h ds f)) /\ 0 <= ds_pending (X4h ds f) < 2 ^ 63
      /\ ds_level (X4h ds f) = 6 /\ ds_strategy (X4h ds f) = 0 /\ ds_wrap (X4h ds f) = ds_wrap ds
      /\ ds_lookahead (X4h ds f) = ds_lookahead ds /\ cs_avail_in (ds_strm (X4h ds f)) = IN).
    { intros E42. destruct (S42 E42) as (P0 & SS0). pose proof (E31 P0) as E3.
      assert (Z3' : ZBc (X3 ds f)).
      { split; [exact DC3|]. rewrite E3, K1p. split; [exact P0 | exact (PO1 P0)]. }
      destruct (zlib_inv _ _ _ _ _ _ HPBL6 (X3 ds f) Z3' ltac:(rewrite S3s; exact E42) ltac:(rewrite S3w, Swr; lia)) as (ZOK & D4 & St4 & PO4 & FL4 & _).
      assert (EH : zlib_s3_spec (X3 ds f) = hdr_st (X3 ds f)).
      { apply hdr_st_eq; [rewrite E3, K1p; exact P0 | rewrite E3, K1ss; exact SS0 | rewrite E3, K1wb; exact Fwb | exact S3lv
                        | exact S3sg | rewrite E3, K1st; clear -BB0; lia]. }
      rewrite EH in D4, St4, PO4, FL4. change (flush_pending (hdr_st (X3 ds f))) with (X4h ds f) in D4, St4, PO4, FL4.
      destruct ZOK as [_ ZE]. unfold zlib_emit in ZE. cbv zeta in ZE. rewrite EH in ZE. destruct ZE as (FP3 & Pd4 & _).
      change (flush_pending (hdr_st (X3 ds f))) with (X4h ds f) in Pd4.
      pose proof (flush_pending_keeps (hdr_st (X3 ds f))) as (_ & Qai & Qlk & Qw & Qlv & Qsg & _).
      change (flush_pending (hdr_st (X3 ds f))) with (X4h ds f) in Qai, Qlk, Qw, Qlv, Qsg.
      pose proof (hdr_st_fields (X3 ds f)) as (Rlv & Rsg & Rw & Rlk & Rai & _).
      split; [exact FP3|]. split; [exact D4|]. split; [exact St4|].
      split; [intros Pq; split; [exact D4 | split; [exact Pq | exact (PO4 Pq)]]|]. split; [exact Pd4|].
      split; [rewrite Qlv, Rlv; exact S3lv|]. split; [rewrite Qsg, Rsg; exact S3sg|]. split; [rewrite Qw, Rw; exact S3w|].
      split; [rewrite Qlk, Rlk; exact S3lk | rewrite Qai, Rai; exact S3ai]. }
    assert (ST4 : DC (X4 ds f) /\ (G4 ds f -> blocks_cond (X4 ds f) f = true -> ZBc (X4 ds f) /\ ds_status (X4 ds f) = 113)
      /\ (G4 ds f -> blocks_cond (X4 ds f) f = false -> False)
      /\ ds_level (X4 ds f) = 6 /\ ds_strategy (X4 ds f) = 0 /\ ds_wrap (X4 ds f) = ds_wrap ds
      /\ ds_lookahead (X4 ds f) = ds_lookahead ds /\ cs_avail_in (ds_strm (X4 ds f)) = IN
      /\ ds_status (X4 ds f) = 113).
    { unfold G4. unfold X4.
      destruct (Z.eqb_spec (ds_status ds) 42) as [E42|E42].
      - destruct (ST4h E42) as (_ & D4 & St4 & Z4 & _ & Lv4 & Sg4 & W4 & Lk4 & Ai4).
        split; [exact D4|]. split; [intros [_ Pq] _; split; [exact (Z4 (Pq E42)) | exact St4]|].
        split.
        { intros _ BC. rewrite (blocks_cond_true_of (X4h ds f) f ltac:(rewrite St4; discriminate) Hf0') in BC. discriminate BC. }
        split; [exact Lv4|]. split; [exact Sg4|]. split; [exact W4|]. split; [exact Lk4|]. split; [exact Ai4 | exact St4].
      - assert (E113 : ds_status ds = 113) by (clear -Sst E42; lia).
        split; [exact DC3|].
        split.
        { intros [G _] BC. split; [exact (Z3 G) | rewrite S3s; exact E113]. }
        split.
        { intros _ BC. rewrite (blocks_cond_true_of (X3 ds f) f ltac:(rewrite S3s, E113; discriminate) Hf0') in BC. discriminate BC. }
        split; [exact S3lv|]. split; [exact S3sg|]. split; [exact S3w|]. split; [exact S3lk|]. split; [exact S3ai|]. rewrite S3s; exact E113. }
    destruct ST4 as (DC4 & Z4r & Z4i & S4lv & S4sg & S4w & S4lk & S4ai & S4st).
    pose proof (dcore_basics _ _ _ _ _ _ HPBL6 _ DC4) as BB4.
    assert (ST5 : G4 ds f -> blocks_cond (X4 ds f) f = true ->
      drun 32768 32768 65536 IN OCAP TOT (X4 ds f) /\ ds_wrap (X4 ds f) = 1
      /\ SSAFE (X4 ds f) f
      /\ BPOST 32768 32768 65536 IN OCAP TOT f (X4 ds f) (X5 ds f) (BS ds f)).
    { intros G BC. destruct (Z4r G BC) as [Z4 St4]. destruct Z4 as (D4 & P4 & PO4).
      pose proof (dcore_drun _ _ _ _ _ _ (X4 ds f) D4 P4 PO4 St4 ltac:(rewrite S4lv; discriminate)) as DR.
      assert (W1 : ds_wrap (X4 ds f) = 1) by (rewrite S4w; exact Swr).
      assert (LZ : lz_strat (X4 ds f)) by (unfold lz_strat, Z_HUFFMAN_ONLY, Z_RLE; rewrite S4sg; split; discriminate).
      pose proof (HSS (X4 ds f) DR ltac:(rewrite S4lv; clear -Hf; lia) LZ W1 (co_ws _ _ _ _ _ _ _ D4) (co_hs _ _ _ _ _ _ _ D4)) as SAFE.
      pose proof (slow_run 32768 32768 65536 IN OCAP TOT tfb_safe_holds tfb_room_holds HPBL6 f (X4 ds f) DR ltac:(rewrite S4lv; clear -Hf; lia) LZ) as [_ BP].
      rewrite (surjective_pairing (deflate_slow (X4 ds f) f)) in BP. cbv beta iota in BP.
      change (fst (deflate_slow (X4 ds f) f)) with (X5 ds f) in BP. change (snd (deflate_slow (X4 ds f) f)) with (BS ds f) in BP.
      split; [exact DR|]. split; [exact W1|]. split; [exact SAFE | exact BP]. }
    assert (HS : dsafe6 SSAFE ds f).
    { unfold dsafe6. cbv zeta. rewrite EPBL'.
    split.
    {
      unfold dlive, dstat_live. rewrite Fao, Fai, Swr, Flv, Fsg, Fwb, Fni.
      split; [clear -Hf; lia|]. split; [clear -Sst; lia|]. split; [clear -HOCAP; lia|]. split; [clear -HIN; lia|].
      split; [intros A0; exfalso; clear -A0 HIN; lia|].
      split; [intros E6; exfalso; exact (N666 E6)|].
      split; [intros E42; destruct (S42 E42) as (P0 & SS0); split; [reflexivity | split; [exact P0 | exact SS0]]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; reflexivity|].
      split; [clear -BB0; lia|]. split; [reflexivity|]. clear -BB0; lia. }
    split.
    {
      intros P. destruct (ST2 P) as (D2 & _ & St2 & _ & _ & _ & _ & Ai2 & FP1).
      pose proof (dcore_basics _ _ _ _ _ _ HPBL6 _ D2) as BB2. pose proof (dcore_status_range _ _ _ _ _ _ _ D2) as SR2.
      unfold fp_ok in FP1. cbv zeta in FP1. destruct FP1 as (B1 & Pd1 & Po1 & Pop1 & Ao1 & Out1 & To1 & _).
      pose proof (Zle_0_nat (length (cs_out_rev (ds_strm (tr_flush_bits (X1 ds f)))))) as OL.
      split; [unfold fp_pre6; cbv zeta; split; [exact B1 | repeat split; clear -Pd1 Po1 Pop1 Ao1 Out1 To1 OL HOCAP; lia]|].
      rewrite St2, Ai2, Fai. split; [clear -BB2 HOCAP; lia|]. split; [clear -Sst; lia|]. split; reflexivity. }
    split.
    {
      intros E42. destruct (ST4h E42) as (FP3 & D4 & St4 & _ & Pd4 & _).
      unfold fp_ok in FP3. cbv zeta in FP3. destruct FP3 as (B3 & Pd3 & Po3 & Pop3 & Ao3 & Out3 & To3 & _).
      pose proof (Zle_0_nat (length (cs_out_rev (ds_strm (tr_flush_bits (hdr_st (X3 ds f))))))) as OL.
      split; [clear -Hf; lia|]. split; [unfold fp_pre6; cbv zeta; split; [exact B3 | repeat split; clear -Pd3 Po3 Pop3 Ao3 Out3 To3 OL HOCAP; lia]|]. split; [exact Pd4 | exact St4]. }
    split; [rewrite S4ai; clear -HIN; lia|].
    split; [rewrite S4lk; clear -BB0; lia|].
    split; [pose proof (dcore_status_range _ _ _ _ _ _ _ DC4) as T; clear -T; lia|]. split; [exact S4lv|]. split; [exact S4sg|].
    split; [intros E6; exfalso; exact (N666 E6)|].
    split; [rewrite S3w, Swr; lia|]. split; [rewrite S3w, Swr; lia|].
    split.
    {
      intros G BC. destruct (ST5 G BC) as (DR & W1 & SAFE & BP).
      destruct BP as (DP5 & Lv5 & Sg5 & R5). pose proof (dpost_dcore _ _ _ _ _ _ _ DP5) as D5. pose proof (dcore_basics _ _ _ _ _ _ HPBL6 _ D5) as BB5.
      split; [exact SAFE|]. split; [clear -BB5 HOCAP; lia|].
      intros EBD. rewrite EBD in R5. destruct R5 as (DR5 & SN5 & LK5 & NF4 & MA5 & _).
      pose proof (dr_pend _ _ _ _ _ _ _ _ _ _ DR5) as P5. pose proof (dr_pout _ _ _ _ _ _ _ _ _ _ DR5) as PO5.
      pose proof (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ DR5)) as I5.
      pose proof (dp_hs _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ DR5)) as HS5.
      pose proof (di_bv _ _ _ _ I5) as BV5. pose proof (di_pop _ _ _ _ I5) as POP5.
      pose proof (dcore_BINV _ _ _ _ _ _ HPBL6 _ D5) as BI5.
      split; [clear -Hf NF4; unfold Z_FINISH in NF4; lia|].
      split; [exact BI5|].
      pose proof (tsb00_fields (X5 ds f) BV5) as F1. cbv zeta in F1.
      destruct F1 as (P1 & V1 & Sm1 & Sn1 & St1 & Wr1 & Lv1 & Sg1 & Lk1 & Str1 & Bs1 & Ma1 & Ml1 & Ms1 & Ws1 & Fq1 & Ol1 & Sl1).
      pose proof (cdiv8_le (ds_bi_valid (X5 ds f) + 3) ltac:(clear -BV5; lia)) as C8.
      split; [rewrite P1, P5; clear -C8 BV5; lia|].
      remember (tr_stored_block (X5 ds f) None 0 0) as t eqn:Et.
      destruct (tsb0_emit (X5 ds f)) as [Bbt Pot]. rewrite <- Et in Bbt, Pot.
      pose proof (reset_fields t) as F3. cbv zeta in F3.
      destruct F3 as (LKC & Sm3 & Sn3 & St3 & Wr3 & Lv3 & Sg3 & Lk3 & Str3 & Bs3 & Ma3 & Ml3 & Ms3 & Ws3 & P3 & V3 & Fq3 & Ol3 & Sl3).
      assert (E6 : X6d ds f = set_insert (set_block_start (set_strstart (clear_hash t) 0) 0) 0).
      { unfold X6d, bd_st. cbv zeta. rewrite <- Et, LKC, Lk1, LK5. reflexivity. }
      remember (set_insert (set_block_start (set_strstart (clear_hash t) 0) 0) 0) as s6 eqn:Es6.
      assert (R6 : ds_bi_buf s6 = ds_bi_buf t /\ ds_pending_out s6 = ds_pending_out t) by (subst s6; destruct t; split; reflexivity).
      destruct R6 as [Bb6 Po6].
      pose proof (dp_call _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ DR5)) as CL5.
      pose proof (dc_ao _ _ _ _ CL5) as AO5. pose proof (dc_out _ _ _ _ CL5) as OUT5. pose proof (dc_to _ _ _ _ CL5) as TO5. pose proof (dc_tot0 _ _ _ _ CL5) as T05.
      pose proof (Zle_0_nat (length (cs_out_rev (ds_strm (X5 ds f))))) as OL5. unfold zlength in OUT5.
      assert (PB6 : 0 <= ds_pending s6 <= 7) by (rewrite P3, P1, P5; clear -C8 BV5; lia).
      assert (BVZ : ds_bi_valid s6 = 0) by (rewrite V3; exact V1).
      assert (TF : tr_flush_bits s6 = s6) by (unfold tr_flush_bits, bi_flush; rewrite BVZ; reflexivity).
      assert (AO6 : 0 <= cs_avail_out (ds_strm s6) < 2 ^ 31) by (rewrite Sm3, Sm1; clear -AO5 OUT5 OL5 HOCAP; lia).
      split.
      { rewrite E6. unfold fp_pre6. cbv zeta. rewrite TF. unfold BINV. rewrite BVZ, Bb6, Bbt, Po6, Pot, PO5, Sm3, Sm1, TO5.
        pose proof (wrap64_range (TOT + zlength (cs_out_rev (ds_strm (X5 ds f))))) as WR.
        repeat split; try (clear -PB6; lia); try (clear -AO5 OUT5 OL5 HOCAP; lia); try (clear -WR; lia). }
      split.
      { unfold X6f. rewrite E6. rewrite (flush_pending_eqm s6) by (rewrite TF; clear -PB6; lia). rewrite TF. cbv zeta.
        destruct (fpm_len s6 =? 0) eqn:EL; [exact AO6|].
        pose proof (fpm_post_fields s6 (fpm_len s6)) as FF. cbv zeta in FF. destruct FF as (_ & _ & _ & AOF & _). rewrite AOF.
        unfold fpm_len in *. destruct (Z.ltb_spec (cs_avail_out (ds_strm s6)) (ds_pending s6)); clear -AO6 PB6 H; lia. }
      split; [rewrite LK5; clear; lia|]. split; [exact HS5|].
      pose proof D5 as [_ _ _ Ews5 _ _]. exact Ews5. }
    split.
    {
      intros [G CASE].
      assert (BC : blocks_cond (X4 ds f) f = true) by (apply blocks_cond_true_of; [rewrite S4st; discriminate | exact Hf0']).
      destruct CASE as [[BCf _]|[_ EBS]]; [rewrite BC in BCf; discriminate BCf|].
      destruct (ST5 G BC) as (DR & W1 & SAFE & BP). destruct BP as (DP5 & Lv5 & Sg5 & R5). rewrite EBS in R5.
      destruct R5 as ([DP5' P5 PO5] & SN5 & LK5 & F4 & MA5). pose proof (dpost_dcore _ _ _ _ _ _ _ DP5) as D5.
      assert (T7 : ZBc (X7 ds f) /\ ds_status (X7 ds f) = 666 /\ ds_sym_next (X7 ds f) = 0 /\ ds_wrap (X7 ds f) = 1 /\ ds_level (X7 ds f) = 6).
      { unfold X7. rewrite BC. unfold X6. rewrite EBS. change (bst_st (X5 ds f) finish_done) with (set_status (X5 ds f) 666).
        pose proof (set_status_fields (X5 ds f) 666) as (Qp & Qpo & Qw & Qlv & Qst & Qsn & Qbv & Qs & Qlk).
        split.
        { split; [apply dcore_set_status; [exact D5 | right; split; [reflexivity | split; [exact LK5 | exact SN5]]]|].
          rewrite Qp, Qpo. split; [exact P5 | exact PO5]. }
        split; [exact Qs|]. split; [rewrite Qsn; exact SN5|]. split; [| rewrite Qlv, Lv5; exact S4lv].
        rewrite Qw. pose proof (wk_deflate_slow (X4 ds f) f) as WK. unfold wk in WK.
        change (fst (deflate_slow (X4 ds f) f)) with (X5 ds f) in WK. rewrite WK. exact W1. }
      destruct T7 as ((D7 & P7 & PO7) & St7 & SN7 & W7 & Lv7). pose proof (dcore_basics _ _ _ _ _ _ HPBL6 _ D7) as BB7.
      split; [rewrite W7; left; reflexivity|]. split; [clear -P7; lia|]. split; [clear -P7; lia|]. split; [clear -BB7 HOCAP; lia|].
      intros _ WP.
      assert (NI7 : ds_status (X7 ds f) <> INIT_STATE /\ ds_status (X7 ds f) <> GZIP_STATE) by (rewrite St7; split; discriminate).
      destruct (dcore_put_bytes _ _ _ _ _ _ HPBL6
                  [cs_adler (ds_strm (X7 ds f)) / 2 ^ 24; cs_adler (ds_strm (X7 ds f)) / 2 ^ 16; cs_adler (ds_strm (X7 ds f)) / 2 ^ 8; cs_adler (ds_strm (X7 ds f))]
                  (X7 ds f) D7 SN7 (proj1 NI7) (proj2 NI7) ltac:(unfold zlength; cbn [length]; change (Z.of_nat 4) with 4; clear -P7 PO7 BB7; lia))
        as (D8a & P8a & V8a & PO8a & SN8a & St8a & Sm8a & W8a).
      rewrite <- ta_post_fold, trl_st_eq in D8a, P8a, V8a, PO8a, SN8a, St8a, Sm8a, W8a.
      pose proof (dcore_fp_ok _ _ _ _ _ _ HPBL6 _ D8a) as FP7. unfold fp_ok in FP7. cbv zeta in FP7. destruct FP7 as (B7 & Pd7 & Po7 & Pop7 & Ao7 & Out7 & To7 & _).
      pose proof (Zle_0_nat (length (cs_out_rev (ds_strm (tr_flush_bits (trl_st (X7 ds f))))))) as OL.
      split; [unfold fp_pre6; cbv zeta; split; [exact B7 | repeat split; clear -Pd7 Po7 Pop7 Ao7 Out7 To7 OL HOCAP; lia]|].
      destruct (dcore_fp _ _ _ _ _ _ HPBL6 (trl_st (X7 ds f)) D8a SN8a ltac:(rewrite St8a; exact (proj1 NI7)) ltac:(rewrite St8a; exact (proj2 NI7)))
        as (D8 & _ & _ & _ & _ & _ & W8 & _).
      change (flush_pending (trl_st (X7 ds f))) with (X8 ds f) in D8, W8. pose proof (dcore_basics _ _ _ _ _ _ HPBL6 _ D8) as BB8.
      split; [rewrite W8, W8a, W7; left; reflexivity|]. split; [clear -BB8 HOCAP; lia | clear -BB7 HOCAP; lia]. }
    destruct D0 as [C I CL Ews Ehs Epbl]. pose proof (dc_ilen _ _ _ _ CL) as IL. rewrite IL. clear -HIN; lia.
    }
    split; [exact HS|].
    rewrite (core_live SSAFE ds f HS). unfold live_core.
    assert (LV6f : G4 ds f -> blocks_cond (X4 ds f) f = true -> BS ds f = block_done -> ds_level (X6f ds f) = 6).
    { intros G BC EBD. destruct (ST5 G BC) as (_ & _ & _ & BP). destruct BP as (DP5 & Lv5 & _ & R5). rewrite EBD in R5. destruct R5 as (DR5 & _).
      pose proof (di_bv _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ DR5))) as BV5.
      unfold X6f. pose proof (flush_pending_keeps (X6d ds f)) as (_ & _ & _ & _ & L & _). rewrite L. unfold X6d. rewrite (level_bd_st _ BV5), Lv5. exact S4lv. }
    assert (BLK : G4 ds f ->
      ds_level (fst (if blocks_cond (X4 ds f) f then
                      match BS ds f with
                      | finish_done => live_tail f (X6 ds f)
                      | block_done => (if cs_avail_out (ds_strm (X6f ds f)) =? 0 then set_last_flush (X6f ds f) (-1) else X6f ds f, Z_OK)
                      | _ => (if cs_avail_out (ds_strm (X6 ds f)) =? 0 then set_last_flush (X6 ds f) (-1) else X6 ds f, Z_OK)
                      end
                    else if f =? 0 then (X4 ds f, Z_OK) else live_tail f (X4 ds f))) = 6).
    { intros G. destruct (blocks_cond (X4 ds f) f) eqn:BC.
      - destruct (ST5 G eq_refl) as (_ & _ & _ & BP). destruct BP as (DP5 & Lv5 & _ & _). unfold X6.
        destruct (BS ds f) eqn:EBS; cbn [fst];
          first [ rewrite level_live_tail, level_bst_st, Lv5; exact S4lv
                | lazymatch goal with |- context [if ?cnd then _ else _] => destruct cnd end; cbn [fst];
                  rewrite ?level_set_last_flush; first [rewrite level_bst_st, Lv5; exact S4lv | exact (LV6f G eq_refl eq_refl)] ].
      - destruct (f =? 0); cbn [fst]; [exact S4lv | rewrite level_live_tail; exact S4lv]. }
    destruct (Z.eqb_spec (ds_pending ds) 0) as [P0|P0]; cbn [negb andb].
    - destruct (Z.eqb_spec (ds_status ds) 42) as [E42|E42]; cbn [andb].
      + destruct (Z.eqb_spec (ds_pending (X4h ds f)) 0) as [Pq|Pq]; cbn [negb].
        * apply BLK. split; [intros P; exfalso; exact (P P0) | intros _; exact Pq].
        * cbn [fst]. rewrite level_set_last_flush. destruct (ST4h E42) as (_ & _ & _ & _ & _ & Lv4 & _). exact Lv4.
      + apply BLK. split; [intros P; exfalso; exact (P P0) | intros E; exfalso; exact (E42 E)].
    - destruct (Z.eqb_spec (cs_avail_out (ds_strm (X2 ds f))) 0) as [A0|A0].
      + cbn [fst]. rewrite level_set_last_flush. destruct (ST2 P0) as (_ & _ & _ & _ & _ & Lv2 & _). exact Lv2.
      + replace (ds_status ds =? 42) with false by (symmetry; apply Z.eqb_neq; intros E; destruct (S42 E) as (X & _); exact (P0 X)). cbn [andb].
        apply BLK. split; [intros _; unfold X3; rewrite (proj2 (Z.eqb_neq _ _) P0); exact A0 | intros E; exfalso; destruct (S42 E) as (X & _); exact (P0 X)].
  Qed.
End GEN.



Lemma HSS6 : forall IN OCAP TOT f X, 0 < OCAP < 2 ^ 31 -> 0 <= f <= 5 ->
  drun 32768 32768 65536 IN OCAP TOT X -> 4 <= ds_level X <= 9 -> lz_strat X -> ds_wrap X = 1 ->
  ds_w_size X = 32768 -> ds_hash_size X = 32768 -> SSAFE6 X f.
Proof.
  intros IN OCAP TOT f X HO Hf DR Hlv LZ W1 Ews Ehs. unfold SSAFE6. split.
  - pose proof (dr_post _ _ _ _ _ _ _ _ _ _ DR) as P. apply DWF_of_dcfg; [exact (dp_cfg _ _ _ _ _ _ _ _ _ _ P)|].
    pose proof (dp_call _ _ _ _ _ _ _ _ _ _ P) as CL. pose proof (dc_ao _ _ _ _ CL). pose proof (dc_out _ _ _ _ CL).
    pose proof (Zle_0_nat (length (cs_out_rev (ds_strm X)))). unfold zlength in *. lia.
  - exact (slow_safe6_of_drun 32768 32768 65536 IN OCAP TOT HPBL6 f Hf X DR (proj1 Hlv) LZ W1 Ews Ehs).
Qed.

Lemma w_bits_of_dcfg : forall s, dcfg s -> ds_w_size s = 32768 -> ds_w_bits s = 15.
Proof.
  intros s C Ews. pose proof (cf_wbits _ C) as R. pose proof (cf_wsize _ C) as E. rewrite Ews in E.
  assert (L : Z.log2 32768 = Z.log2 (2 ^ ds_w_bits s)) by (rewrite <- E; reflexivity). rewrite Z.log2_pow2 in L by lia. cbn in L. lia.
Qed.

Section FL.
  Variable d : list Z.
  Hypothesis Hn : 4 <= zlength d <= 2 ^ 20.
  Hypothesis Hb : Forall (fun b => 0 <= b < 256) d.

  Lemma fl_ds1_dcore : dcore 32768 32768 65536 (zlength (zc_input (fl_zc1 d))) (zc_avail_out (fl_zc1 d)) (zs_total_out (zc_strm (fl_zc1 d))) (fl_ds1 d)
    /\ zlength (zc_input (fl_zc1 d)) = 3 /\ zc_avail_out (fl_zc1 d) = fl_clen (zlength d) /\ CFGX (fl_ds1 d).
  Proof.
    pose proof DB_ds0 as [DI0 AD ZS B C SZ T0 I0 TIN TOUT PHI].
    assert (HCL : wrap32 (fl_clen (zlength d)) = fl_clen (zlength d)) by (apply wrap32_fl_clen; lia).
    pose proof (fl_clen_range (zlength d) ltac:(lia)) as CR.
    assert (L3 : zlength (zc_input (fl_zc1 d)) = 3) by (rewrite fl_zc1_eq; cbn [zc_input]; rewrite arr_slice_length; reflexivity).
    assert (ZC : zcall_ok (fl_zc1 d)).
    { rewrite fl_zc1_eq. unfold zcall_ok, zs_ok in *. cbn [zc_strm zc_avail_out zc_input]. rewrite HCL, arr_slice_length.
      repeat split; try lia; try (cbn; lia). apply Forall_arr_slice_of_list. exact Hb. }
    split; [| split; [exact L3 | split; [rewrite fl_zc1_eq; cbn [zc_avail_out]; exact HCL | exact (CFGX_set_strm _ _ C)]]].
    unfold fl_ds1. destruct SZ as [Sw Sl].
    apply (dcore_entry 32768 32768 65536 _ _ _ ds0 (fl_zc1 d) DI0 ZC); try reflexivity.
    all: try (rewrite fl_zc1_eq; cbn [zc_strm]; exact AD). all: try exact Sw. all: rewrite Sl; reflexivity.
  Qed.

  Theorem dfl1_facts : DSAFE6 (fl_ds1 d) 3 /\ ds_level (fl_s1 d) = 6.
  Proof.
    destruct fl_ds1_dcore as (D0 & L3 & AO & CFG). pose proof (fl_clen_range (zlength d) ltac:(lia)) as CR.
    pose proof (fl_ds1_scalars d) as (ST & P0 & LF & WR & LV & SG & AI & AOe & NI & OUT).
    destruct CFG as (CL & CS & CW & CI).
    pose proof (gen_dsafe6 (zlength (zc_input (fl_zc1 d))) (zc_avail_out (fl_zc1 d)) (zs_total_out (zc_strm (fl_zc1 d))) (fl_ds1 d) 3 D0
                  ltac:(left; reflexivity) ltac:(rewrite L3; lia) ltac:(rewrite AO; lia)
                  ltac:(rewrite L3; exact AI) ltac:(rewrite AO, <- (wrap32_fl_clen (zlength d)) by lia; exact AOe) NI
                  ltac:(left; exact ST) ltac:(intros E; split; [exact P0 | exact (proj1 (CI E))]) WR LV SG
                  (w_bits_of_dcfg _ (co_cfg _ _ _ _ _ _ _ D0) (co_ws _ _ _ _ _ _ _ D0))
                  SSAFE6 (fun X DR Hlv LZ W1 Ews Ehs => HSS6 (zlength (zc_input (fl_zc1 d))) (zc_avail_out (fl_zc1 d)) (zs_total_out (zc_strm (fl_zc1 d))) 3 X ltac:(rewrite AO; lia) ltac:(lia) DR Hlv LZ W1 Ews Ehs)) as [HS LV1].
    split.
    - split; [| exact HS]. apply DWF_of_dcfg; [exact (co_cfg _ _ _ _ _ _ _ D0)|]. rewrite AOe, (wrap32_fl_clen (zlength d)) by lia. lia.
    - unfold fl_s1. rewrite fl_call1_core. change Z_FULL_FLUSH with 3. destruct (deflate_core (fl_ds1 d) 3) as [s rc]. exact LV1.
  Qed.
  Corollary dfl1_safe : DSAFE6 (fl_ds1 d) 3.
  Proof. exact (proj1 dfl1_facts). Qed.

  Theorem dfl2_safe : DSAFE6 (fl_ds2 d) 4.
  Proof.
    destruct (flush2_dcore d Hn Hb) as (D2 & B2 & C2 & SB2 & AO2 & ZC2 & P2 & AI2 & OUT2).
    destruct (flush2_entry d Hn Hb) as (_ & _ & _ & EAO2 & LO1). destruct (flush1_post d Hn Hb) as (DI1 & _).
    pose proof (fl_clen_range (zlength d) ltac:(lia)) as CR. pose proof (zlength_nonneg (cs_out_rev (ds_strm (fl_s1 d)))) as OL.
    destruct C2 as (CL & CS & CW & CI). destruct dfl1_facts as [_ LV1].
    assert (LIN : zlength (zc_input (fl_zc2 d)) = zlength d - 3).
    { rewrite fl_zc2_eq. cbn [zc_input]. rewrite arr_slice_length. rewrite (wrap32_id (zlength d)) by lia. rewrite (wrap32_id (zlength d - 3)) by lia. lia. }
    assert (EAI : cs_avail_in (ds_strm (fl_ds2 d)) = zlength (zc_input (fl_zc2 d))) by (unfold fl_ds2; destruct (fl_s1 d); reflexivity).
    assert (EAO : cs_avail_out (ds_strm (fl_ds2 d)) = zc_avail_out (fl_zc2 d)) by (unfold fl_ds2; destruct (fl_s1 d); reflexivity).
    assert (ENI : cs_next_in (ds_strm (fl_ds2 d)) = 0) by (unfold fl_ds2; destruct (fl_s1 d); reflexivity).
    assert (WR2 : ds_wrap (fl_ds2 d) = 1).
    { destruct CW as [W|W]; [exact W|]. exfalso.
      assert (WR1 : ds_wrap (fl_s1 d) = -1) by (revert W; unfold fl_ds2; destruct (fl_s1 d); intros W; exact W).
      destruct DI1 as [_ I1]. pose proof (di_negwrap _ _ _ _ I1) as NW.
      assert (E1 : ds_wrap (zin (fl_s1 d)) = ds_wrap (fl_s1 d) /\ ds_status (zin (fl_s1 d)) = ds_status (fl_s1 d)) by (destruct (fl_s1 d); split; reflexivity).
      destruct E1 as [Ew Es]. rewrite Ew, Es, WR1 in NW. destruct (NW eq_refl) as [S6 _].
      assert (SB1 : ds_status (fl_s1 d) = BUSY_STATE) by (revert SB2; unfold fl_ds2; destruct (fl_s1 d); intros X; exact X).
      rewrite SB1 in S6. discriminate S6. }
    assert (LV2 : ds_level (fl_ds2 d) = 6) by (revert LV1; unfold fl_ds2; destruct (fl_s1 d); intros X; exact X).
    pose proof (gen_dsafe6 (zlength (zc_input (fl_zc2 d))) (zc_avail_out (fl_zc2 d)) (zs_total_out (zc_strm (fl_zc2 d))) (fl_ds2 d) 4 D2
                  ltac:(right; reflexivity) ltac:(rewrite LIN; lia) ltac:(rewrite <- EAO, EAO2; lia)
                  EAI EAO ENI
                  ltac:(right; exact SB2) ltac:(intros E; rewrite SB2 in E; discriminate E) WR2 LV2 CS
                  (w_bits_of_dcfg _ (co_cfg _ _ _ _ _ _ _ D2) (co_ws _ _ _ _ _ _ _ D2))
                  SSAFE6 (fun X DR Hlv LZ W1 Ews Ehs => HSS6 (zlength (zc_input (fl_zc2 d))) (zc_avail_out (fl_zc2 d)) (zs_total_out (zc_strm (fl_zc2 d))) 4 X ltac:(rewrite <- EAO, EAO2; lia) ltac:(lia) DR Hlv LZ W1 Ews Ehs)) as [HS _].
    split; [| exact HS]. apply DWF_of_dcfg; [exact (co_cfg _ _ _ _ _ _ _ D2)|]. rewrite EAO2. lia.
  Qed.
End FL.
