(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  DeflateInvHash DeflateInvKeep OverlayFBS OverlayRace OverlayFlush DeflRoom SendModel
  LmatchModel FillWinModel DeflFastModel DeflSlowModel TreesTab
  RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflSlowOk
  DeflateInv DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep DeflInvFbo DeflInvFw DeflInvFast DeflInvSlow DeflInvSlow2
  BoundArith BoundTfb.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition Mloc (s : deflate_state) : Z :=
  zlength (cs_out_rev (ds_strm s)) + ds_pending s + cdiv8 (ds_bi_valid s).

Definition Aof (IN0 : Z) (s : deflate_state) : Z :=
  IN0 + cs_next_in (ds_strm s) - ds_lookahead s - (ds_strstart s - ds_block_start s).

Definition KBLK : Z := 16383.
Definition Phi (IN0 : Z) (s : deflate_state) : Z :=
  Aof IN0 s + 5 * (Aof IN0 s / KBLK)
  + (if ds_status s =? INIT_STATE then 0 else 2)
  + (if ds_status s =? FINISH_STATE then 5 else 0)
  + (if ds_wrap s <=? 0 then 4 else 0).



Record BI (s : deflate_state) : Prop := MkBI {
  bi_cov : forall syms, dsyms syms s -> zcov syms + ds_match_available s = ds_strstart s - ds_block_start s;
  bi_tf : forall syms, dsyms syms s -> Forall too_far_ok syms;
  bi_tfc : ds_match_length s = MIN_MATCH -> wrap32 (ds_strstart s - 1 - ds_match_start s) <= TOO_FAR;
  bi_mla : MIN_MATCH <= ds_match_length s -> ds_match_available s = 1;
  bi_nb : ds_block_start s < 0 -> ds_w_size s - MIN_LOOKAHEAD <= ds_strstart s }.

Record BIfin (s : deflate_state) : Prop := MkBIF {
  bf_cov : forall syms, dsyms syms s -> zcov syms + ds_match_available s = ds_strstart s - ds_block_start s
           \/ ds_status s = FINISH_STATE;
  bf_bi : ds_status s <> FINISH_STATE -> BI s }.



Lemma bi_flush_M : forall s, 0 <= ds_bi_valid s <= 16 ->
  ds_pending (bi_flush s) + cdiv8 (ds_bi_valid (bi_flush s)) = ds_pending s + cdiv8 (ds_bi_valid s)
  /\ ds_strm (bi_flush s) = ds_strm s /\ 0 <= ds_bi_valid (bi_flush s) <= 16 /\ ds_pending s <= ds_pending (bi_flush s).
Proof.
  intros s Hb. unfold bi_flush.
  destruct (Z.eqb_spec (ds_bi_valid s) 16) as [E|E].
  - destruct (put_short_acct s (ds_bi_buf s)) as (A & B & C). dsred. rewrite A, E. unfold put_short, put_byte. dsred.
    change (cdiv8 16) with 2. change (cdiv8 0) with 0. repeat split; lia.
  - destruct (Z.leb_spec 8 (ds_bi_valid s)).
    + destruct (put_byte_acct s (ds_bi_buf s)) as (A & B & C). dsred. rewrite A. unfold put_byte. dsred.
      replace (ds_bi_valid s) with (8 * 1 + (ds_bi_valid s - 8)) at 2 by lia. rewrite cdiv8_mul. repeat split; lia.
    + repeat split; lia.
Qed.

Lemma flush_pending_M : forall s, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_pending (bi_flush s) < 2 ^ 32 ->
  0 <= cs_avail_out (ds_strm s) ->
  let s' := flush_pending s in
  Mloc s' = Mloc s /\ cs_next_in (ds_strm s') = cs_next_in (ds_strm s) /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s)
  /\ 0 <= ds_bi_valid s' <= 16.
Proof.
  intros s Hb Hp Hao. destruct (bi_flush_M s Hb) as (M1 & S1 & B1 & _).
  rewrite (flush_pending_eqm s Hp). change (tr_flush_bits s) with (bi_flush s). cbv zeta.
  set (s1 := bi_flush s) in *. unfold Mloc.
  destruct (Z.eqb_spec (fpm_len s1) 0) as [E|E].
  - rewrite S1. repeat split; lia.
  - pose proof (fpm_post_fields s1 (fpm_len s1)) as F. cbv zeta in F.
    destruct F as (P1 & _ & O1 & _ & _ & N1 & A1 & _ & _ & _ & _ & _ & _ & V1 & _).
    rewrite P1, O1, N1, A1, V1, S1, zlength_rev_append, arr_slice_length.
    assert (L0 : 0 <= fpm_len s1).
    { unfold fpm_len. rewrite S1. destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) (ds_pending s1)); lia. }
    repeat split; lia.
Qed.


Lemma set_match_start_idem : forall s a b, set_match_start (set_match_start s a) b = set_match_start s b.
Proof. intros s a b. destruct s; reflexivity. Qed.
Lemma set_match_start_self : forall s, set_match_start s (ds_match_start s) = s.
Proof. intros s. destruct s; reflexivity. Qed.

Lemma longest_match_loop_shape : forall f s cur ch bl nice limit se1 se,
  exists v bl', longest_match_loop f s cur ch bl nice limit se1 se = (set_match_start s v, bl').
Proof.
  induction f as [|f IH]; intros s cur ch bl nice limit se1 se.
  - exists (ds_match_start s), bl. cbn. rewrite set_match_start_self. reflexivity.
  - cbn [longest_match_loop].
    assert (B : exists v bl1 a b c d cont, longest_match_body s cur ch bl nice limit se1 se = (set_match_start s v, bl1, a, b, c, d, cont)).
    { unfold longest_match_body.
      repeat match goal with |- context [if ?c then _ else _] => let b := fresh "b" in destruct c eqn:b; clear b end;
        first [ do 7 eexists; rewrite set_match_start_self; reflexivity
              | do 7 eexists; reflexivity ]. }
    destruct B as (v & bl1 & a & b & c & d & cont & E). rewrite E.
    destruct cont.
    + destruct (IH (set_match_start s v) c d bl1 nice limit a b) as (v' & bl' & E'). rewrite E', set_match_start_idem. eauto.
    + eauto.
Qed.

Lemma longest_match_shape : forall s cur, exists v, fst (longest_match s cur) = set_match_start s v.
Proof.
  intros s cur. unfold longest_match.
  match goal with |- context [longest_match_loop ?f s cur ?ch ?bl ?nm ?lim ?e1 ?e2] =>
    destruct (longest_match_loop_shape f s cur ch bl nm lim e1 e2) as (v & bl' & E); rewrite E end.
  destruct (bl' <=? ds_lookahead (set_match_start s v)); exists v; reflexivity.
Qed.


Lemma dsyms_iff : forall s s', 
  ds_sym_next s' = ds_sym_next s -> ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s ->
  ds_w_size s' = ds_w_size s -> ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s -> ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s ->
  ds_bl_tree_fc s' = ds_bl_tree_fc s -> ds_opt_len s' = ds_opt_len s -> ds_static_len s' = ds_static_len s ->
  forall syms, dsyms syms s' <-> dsyms syms s.
Proof.
  intros s s' E1 E2 E3 E4 E5 E6 E7 E8 E9 syms. split; intros D.
  - eapply dsyms_keep; [exact D | symmetry; assumption ..].
  - eapply dsyms_keep; [exact D | assumption ..].
Qed.

Section FW.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).

  Lemma fw_BI : forall rm fz s IN0, drunR rm 0 fz ws hs PBL ILEN OCAP tot0 s -> ds_lookahead s < MIN_LOOKAHEAD -> BI s ->
    let s' := fill_window s in
    BI s' /\ Mloc s' = Mloc s /\ Aof IN0 s' = Aof IN0 s
    /\ ds_status s' = ds_status s /\ ds_wrap s' = ds_wrap s /\ ds_match_length s' = ds_match_length s
    /\ ds_match_available s' = ds_match_available s
    /\ drunR rm 0 fz ws hs PBL ILEN OCAP tot0 s' /\ ds_strstart s' + MIN_LOOKAHEAD < 2 * ws
    /\ (cs_avail_in (ds_strm s') = 0 \/ MIN_LOOKAHEAD <= ds_lookahead s')
    /\ ds_lookahead s <= ds_lookahead s' /\ ds_lookahead s' + cs_avail_in (ds_strm s') = ds_lookahead s + cs_avail_in (ds_strm s).
  Proof.
    intros rm fz s IN0 D Hl B. pose proof (drun_dwin _ _ _ _ _ _ _ _ _ D) as W.
    destruct (fw_run _ _ _ _ _ _ W Hl) as (W1 & Z1 & L1 & CONS & EX & ST1 & BS1 & MS1 & NI1 & NB1). cbv zeta.
    set (s' := fill_window s) in *.
    pose proof (fw_match_available _ _ Z1) as Ema. pose proof (fw_match_length _ _ Z1) as Eml.
    assert (SY : forall syms, dsyms syms s' <-> dsyms syms s).
    { apply dsyms_iff; [exact (fw_sym_next _ _ Z1) | exact (fw_pending_buf _ _ Z1) | exact (fw_lit_bufsize _ _ Z1) | | exact (fw_dyn_ltree_fc _ _ Z1)
        | exact (fw_dyn_dtree_fc _ _ Z1) | exact (fw_bl_tree_fc _ _ Z1) | exact (fw_opt_len _ _ Z1) | exact (fw_static_len _ _ Z1)].
      rewrite (dw_ws _ _ _ _ _ _ W1), (dw_ws _ _ _ _ _ _ W). reflexivity. }
    split.
    - constructor.
      + intros syms Dy. rewrite Ema, BS1. apply (bi_cov _ B). apply SY. exact Dy.
      + intros syms Dy. apply (bi_tf _ B). apply SY. exact Dy.
      + rewrite Eml, MS1. exact (bi_tfc _ B).
      + rewrite Eml, Ema. exact (bi_mla _ B).
      + intros Hb. apply NB1; [exact (bi_nb _ B) | exact Hb].
    - split; [unfold Mloc; rewrite (fw_cs_out_rev _ _ Z1), (fw_pending _ _ Z1), (fw_bi_valid _ _ Z1); reflexivity|].
      split; [unfold Aof; rewrite <- BS1; pose proof (dw_in _ _ _ _ _ _ W); pose proof (dw_in _ _ _ _ _ _ W1); lia|].
      split; [exact (fw_status _ _ Z1)|]. split; [exact (fw_wrap _ _ Z1)|]. split; [exact Eml|]. split; [exact Ema|].
      split; [exact (dwin_drun _ _ _ _ _ _ _ _ _ _ D W1 Z1)|]. split; [exact ST1|]. split; [exact EX|]. split; [exact L1 | exact CONS].
  Qed.
End FW.

Lemma set_match_length_idem : forall s a b, set_match_length (set_match_length s a) b = set_match_length s b.
Proof. intros s a b; destruct s; reflexivity. Qed.

Definition sf_norm (s : deflate_state) (ms ml : Z) : deflate_state :=
  set_match_length (set_match_start (set_match_length (set_prev_match (set_prev_length s (ds_match_length s)) (ds_match_start s)) (MIN_MATCH - 1)) ms) ml.

Lemma slow_front2_norm : forall s hh, exists ms ml,
  slow_front2 s hh = sf_norm s ms ml /\ (ml = MIN_MATCH -> wrap32 (ds_strstart s - ms) <= TOO_FAR).
Proof.
  intros s hh. unfold slow_front2, sf_norm. rewrite match_start_set_prev_length.
  set (s3 := set_match_length (set_prev_match (set_prev_length s (ds_match_length s)) (ds_match_start s)) (MIN_MATCH - 1)).
  match goal with |- context [if ?c then _ else s3] => destruct c end.
  - destruct (longest_match_shape s3 hh) as [v Ev]. destruct (longest_match s3 hh) as [s4 ml0]. cbn [fst] in Ev. subst s4.
    match goal with |- context [if ?c then _ else _] => destruct c eqn:FILT end.
    + exists v, (MIN_MATCH - 1). rewrite set_match_length_idem. split; [reflexivity | unfold MIN_MATCH; lia].
    + exists v, ml0. split; [reflexivity|]. intros E3. subst ml0.
      revert FILT. subst s3. dsr. unfold MIN_MATCH. cbn [Z.sub Z.leb Z.eqb Pos.compare Pos.compare_cont andb].
      destruct (ds_strategy s =? Z_FILTERED); cbn [orb]; [intros X; discriminate X|].
      destruct (Z.ltb_spec TOO_FAR (wrap32 (ds_strstart s - v))); [intros X; discriminate X | intros _; lia].
  - exists (ds_match_start s), (MIN_MATCH - 1). split; [| unfold MIN_MATCH; lia].
    subst s3. destruct s; reflexivity.
Qed.

Lemma sf_norm_fields : forall s ms ml, let s6 := sf_norm s ms ml in
  ds_prev_length s6 = ds_match_length s /\ ds_prev_match s6 = ds_match_start s
  /\ ds_match_available s6 = ds_match_available s /\ ds_block_start s6 = ds_block_start s
  /\ ds_strstart s6 = ds_strstart s /\ ds_lookahead s6 = ds_lookahead s
  /\ ds_strm s6 = ds_strm s /\ ds_pending s6 = ds_pending s /\ ds_bi_valid s6 = ds_bi_valid s
  /\ ds_status s6 = ds_status s /\ ds_wrap s6 = ds_wrap s /\ ds_w_size s6 = ds_w_size s
  /\ ds_match_length s6 = ml /\ ds_match_start s6 = ms
  /\ (forall syms, dsyms syms s6 <-> dsyms syms s).
Proof.
  intros s ms ml. cbv zeta. unfold sf_norm. dsr. repeat (split; [reflexivity|]). apply dsyms_iff; dsr; reflexivity.
Qed.

Lemma insert_string_norm : forall s str, exists h pv hd,
  fst (insert_string s str) = set_head (set_prev (set_ins_h s h) pv) hd.
Proof. intros s str. unfold insert_string. cbn [fst]. do 3 eexists. reflexivity. Qed.

Record sff (s s6 : deflate_state) : Prop := MkSFF {
  sf_pl : ds_prev_length s6 = ds_match_length s;
  sf_pm : ds_prev_match s6 = ds_match_start s;
  sf_ma : ds_match_available s6 = ds_match_available s;
  sf_bs : ds_block_start s6 = ds_block_start s;
  sf_str : ds_strstart s6 = ds_strstart s;
  sf_look : ds_lookahead s6 = ds_lookahead s;
  sf_strm : ds_strm s6 = ds_strm s;
  sf_pend : ds_pending s6 = ds_pending s;
  sf_bv : ds_bi_valid s6 = ds_bi_valid s;
  sf_status : ds_status s6 = ds_status s;
  sf_wrap : ds_wrap s6 = ds_wrap s;
  sf_ws : ds_w_size s6 = ds_w_size s;
  sf_syms : forall syms, dsyms syms s6 <-> dsyms syms s;
  sf_tf : ds_match_length s6 = MIN_MATCH -> wrap32 (ds_strstart s6 - ds_match_start s6) <= TOO_FAR }.

Lemma slow_front_sff : forall s, sff s (slow_front s).
Proof.
  intros s. unfold slow_front.
  assert (G : forall s1, ds_match_length s1 = ds_match_length s -> ds_match_start s1 = ds_match_start s ->
              ds_match_available s1 = ds_match_available s -> ds_block_start s1 = ds_block_start s ->
              ds_strstart s1 = ds_strstart s -> ds_lookahead s1 = ds_lookahead s -> ds_strm s1 = ds_strm s ->
              ds_pending s1 = ds_pending s -> ds_bi_valid s1 = ds_bi_valid s -> ds_status s1 = ds_status s ->
              ds_wrap s1 = ds_wrap s -> ds_w_size s1 = ds_w_size s -> (forall syms, dsyms syms s1 <-> dsyms syms s) ->
              forall hh, sff s (slow_front2 s1 hh)).
  { intros s1 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 SY hh.
    destruct (slow_front2_norm s1 hh) as (ms & ml & E & TF). rewrite E.
    pose proof (sf_norm_fields s1 ms ml) as F. cbv zeta in F.
    destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
    constructor; try congruence.
    - intros syms. rewrite F15. apply SY.
    - rewrite F13, F14, F5, E5. intros H. rewrite <- E5. exact (TF H). }
  destruct (Z.leb_spec MIN_MATCH (ds_lookahead s)).
  - destruct (insert_string_norm s (ds_strstart s)) as (h & pv & hd & E).
    destruct (insert_string s (ds_strstart s)) as [s2 hh]. cbn [fst] in E. subst s2.
    apply G; dsr; try reflexivity. apply dsyms_iff; dsr; reflexivity.
  - cbn [fst snd]. apply G; try reflexivity.
Qed.


Lemma fbs_dsyms_same : forall a b s buf len last, FBS a s buf len last -> dsyms b s -> a = b.
Proof.
  intros a b s buf len last Fa Db.
  pose proof (fbs_sym_next _ _ _ _ _ Fa) as Na. unfold fbs_n in Na. pose proof (sy_next _ _ Db) as Nb.
  assert (L : length a = length b) by lia.
  pose proof (fbs_sym_bytes _ _ _ _ _ Fa) as Ba. unfold fbs_L in Ba. pose proof (sy_bytes _ _ Db) as Bb.
  pose proof (fbs_syms_valid _ _ _ _ _ Fa) as Va. pose proof (sy_valid _ _ Db) as Vb.
  apply nth_error_ext. intros i.
  destruct (nth_error a i) as [[d lc]|] eqn:Ea; destruct (nth_error b i) as [[d' lc']|] eqn:Eb.
  - destruct (Ba i d lc Ea) as (A1 & A2 & A3). destruct (Bb i d' lc' Eb) as (B1 & B2 & B3).
    pose proof (Forall_nth_error' _ _ _ _ Va Ea) as X. pose proof (Forall_nth_error' _ _ _ _ Vb Eb) as Y.
    unfold sym_valid in X, Y. cbn in X, Y.
    f_equal. f_equal; [| congruence].
    rewrite (Z.div_mod d 256) by lia. rewrite (Z.div_mod d' 256) by lia. congruence.
  - exfalso. assert (Hi : (i < length a)%nat) by (apply nth_error_Some; rewrite Ea; discriminate).
    apply nth_error_None in Eb. lia.
  - exfalso. assert (Hi : (i < length b)%nat) by (apply nth_error_Some; rewrite Eb; discriminate).
    apply nth_error_None in Ea. lia.
  - reflexivity.
Qed.

Section FBO.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.
  Hypothesis HWS : ws = 32768.
  Hypothesis HLBS : PBL = 4 * 16384.

  Lemma fbo_cb : forall rm hb fz s last IN0, 0 <= rm -> drunR rm hb fz ws hs PBL ILEN OCAP tot0 s -> (last = 0 \/ last = 1) ->
    (forall syms, dsyms syms s -> zcov syms = ds_strstart s - ds_block_start s /\ Forall too_far_ok syms) ->
    (ds_block_start s < 0 -> ds_w_size s - MIN_LOOKAHEAD <= ds_strstart s) ->
    let s' := flush_block_only s last in
    Mloc s' <= Mloc s + (ds_strstart s - ds_block_start s) + 5
    /\ Aof IN0 s' = Aof IN0 s + (ds_strstart s - ds_block_start s)
    /\ (forall syms, dsyms syms s' -> syms = [])
    /\ dpostR 3 hb fz ws hs PBL ILEN OCAP tot0 s' /\ ds_sym_next s' = 0 /\ ds_block_start s' = ds_strstart s' /\ fbo_frame s s'.
  Proof.
    intros rm hb fz s last IN0 Hrm D Hl COV NB.
    destruct (fbo_run ws hs PBL ILEN OCAP tot0 TS TR HPBL rm hb fz s last Hrm D Hl) as (_ & P' & SN' & BS' & FR).
    cbv zeta in P'. cbv zeta in SN'. cbv zeta in BS'. cbv zeta in FR.
    destruct (drun_FBS _ _ _ _ _ _ _ _ _ s last Hrm D Hl) as [syms F].
    pose proof D as [P P0 PO0]. pose proof (drun_span _ _ _ _ _ _ _ _ _ _ Hrm P) as (R & RS & EL & EB).
    pose proof P as [C I CL Ews Ehs Epbl Sst Swr Slz Sfl].
    destruct (di_syms _ _ _ _ I) as (sy & Dy & _). pose proof (fbs_dsyms_same _ _ _ _ _ _ F Dy) as ->.
    destruct (COV sy Dy) as [ZC TF].
    assert (HL512 : 512 <= ds_lit_bufsize s) by lia.
    assert (CB : cdiv8 (vsize (tr_flush_block s (fbo_buf s) (fbo_len s) last)) <= cdiv8 (ds_bi_valid s) + fbo_len s + 5).
    { apply (tfb_cb sy s (fbo_buf s) (fbo_len s) last F HL512).
      intros NONE. unfold fbo_buf in NONE. destruct (Z.leb_spec 0 (ds_block_start s)) as [|NEG]; [discriminate NONE|].
      pose proof (fbs_n_range _ _ _ _ _ F) as NR. unfold fbs_n, fbs_L in NR.
      apply (Sstat_big_block sy (fbo_len s) (fbs_syms_valid _ _ _ _ _ F) TF); rewrite ?EL; try lia.
      specialize (NB NEG). rewrite Ews, HWS in NB. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in NB. lia. }
    pose proof (TR sy s _ _ _ F HL512) as ROOM. cbv zeta in ROOM. destruct ROOM as (RV & RB1 & RB2 & RB3).
    unfold vsize in RV. rewrite (cf_bl _ C) in RV.
    pose proof (tfb_fields s (fbo_buf s) (fbo_len s) last) as TF0.
    remember (tr_flush_block s (fbo_buf s) (fbo_len s) last) as s1 eqn:Es1.
    destruct TF0 as (F1 & F2 & F3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F25 & _ & F27 & F28 & _).
    assert (E' : flush_block_only s last = flush_pending (set_block_start s1 (ds_strstart s1))).
    { unfold flush_block_only. fold (fbo_buf s) (fbo_len s). rewrite <- Es1. reflexivity. }
    cbv zeta. rewrite E' in *.
    set (s2 := set_block_start s1 (ds_strstart s1)) in *.
    assert (M2 : Mloc s2 = Mloc s1 /\ ds_bi_valid s2 = ds_bi_valid s1 /\ ds_pending s2 = ds_pending s1 /\ ds_strm s2 = ds_strm s1
                 /\ ds_lookahead s2 = ds_lookahead s1 /\ ds_strstart s2 = ds_strstart s1 /\ ds_block_start s2 = ds_strstart s1)
      by (subst s2; unfold Mloc; dsr; repeat split; reflexivity).
    destruct M2 as (M2 & B2 & Pd2 & St2 & L2 & S2 & Bs2).
    assert (AO : 0 <= cs_avail_out (ds_strm s2)) by (rewrite St2, F27; dsr; exact (dc_ao _ _ _ _ CL)).
    destruct (bi_flush_M s2 ltac:(rewrite B2; lia)) as (X & _ & Xb & Xp).
    pose proof (cdiv8_le (ds_bi_valid (bi_flush s2)) ltac:(lia)) as C1. pose proof (cdiv8_le (ds_bi_valid s2) ltac:(rewrite B2; lia)) as C2.
    rewrite Pd2 in X, Xp. rewrite B2 in X, C2.
    destruct (flush_pending_M s2 ltac:(rewrite B2; lia) ltac:(lia) AO) as (M3 & N3 & A3 & B3).
    split; [| split; [| split; [| split; [exact P' | split; [exact SN' | split; [exact BS' | exact FR]]]]]].
    - rewrite M3, M2. unfold Mloc. rewrite F27. dsr. rewrite P0. unfold vsize in CB.
      rewrite cdiv8_mul in CB. change (cdiv8 0) with 0. lia.
    - unfold Aof. rewrite (ff_next_in _ _ FR), (ff_lookahead _ _ FR), (ff_strstart _ _ FR), (ff_block_start _ _ FR). lia.
    - intros syms' D'. pose proof (sy_next _ _ D') as Y. rewrite SN' in Y. destruct syms'; [reflexivity | cbn in Y; lia].
  Qed.
End FBO.


Lemma Mloc_frame : forall s s', ds_strm s' = ds_strm s -> ds_pending s' = ds_pending s -> ds_bi_valid s' = ds_bi_valid s ->
  Mloc s' = Mloc s.
Proof. intros s s' A B C. unfold Mloc. rewrite A, B, C. reflexivity. Qed.

Lemma Aof_shift : forall IN0 s s', cs_next_in (ds_strm s') = cs_next_in (ds_strm s) ->
  Aof IN0 s' = Aof IN0 s + (ds_lookahead s - ds_lookahead s')
               - ((ds_strstart s' - ds_block_start s') - (ds_strstart s - ds_block_start s)).
Proof. intros IN0 s s' A. unfold Aof. rewrite A. lia. Qed.

Lemma Aof_frame : forall IN0 s s', cs_next_in (ds_strm s') = cs_next_in (ds_strm s) ->
  ds_lookahead s' = ds_lookahead s -> ds_strstart s' - ds_block_start s' = ds_strstart s - ds_block_start s ->
  Aof IN0 s' = Aof IN0 s.
Proof. intros IN0 s s' A B C. rewrite (Aof_shift IN0 s s' A), B, C. lia. Qed.
