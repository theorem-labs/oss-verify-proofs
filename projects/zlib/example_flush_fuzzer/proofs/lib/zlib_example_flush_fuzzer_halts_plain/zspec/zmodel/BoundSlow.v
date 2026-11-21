(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  DeflateInvHash DeflateInvKeep OverlayFBS OverlayRace OverlayFlush DeflRoom SendModel
  LmatchModel FillWinModel DeflFastModel DeflSlowModel TreesTab
  RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflSlowOk
  DeflateInv DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep DeflInvFbo DeflInvFw DeflInvFast DeflInvSlow DeflInvSlow2
  BoundArith BoundTfb BoundInv.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Record sik (s s' : deflate_state) : Prop := MkSIK {
  ik_look : ds_lookahead s' = ds_lookahead s;
  ik_ml : ds_match_length s' = ds_match_length s;
  ik_ms : ds_match_start s' = ds_match_start s;
  ik_ma : ds_match_available s' = ds_match_available s;
  ik_bs : ds_block_start s' = ds_block_start s;
  ik_strm : ds_strm s' = ds_strm s;
  ik_pend : ds_pending s' = ds_pending s;
  ik_bv : ds_bi_valid s' = ds_bi_valid s;
  ik_status : ds_status s' = ds_status s;
  ik_wrap : ds_wrap s' = ds_wrap s;
  ik_ws : ds_w_size s' = ds_w_size s;
  ik_syms : forall syms, dsyms syms s' <-> dsyms syms s }.

Lemma sik_refl : forall s, sik s s.
Proof. intros s; constructor; reflexivity. Qed.
Lemma sik_trans : forall a b c, sik a b -> sik b c -> sik a c.
Proof.
  intros a b c [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12]; constructor; try congruence.
  intros syms. rewrite B12. apply A12.
Qed.

Lemma slow_insert_fields : forall f s mi, Z.of_nat f = ds_prev_length s ->
  let s' := deflate_slow_insert f s mi in
  ds_strstart s' = ds_strstart s + ds_prev_length s /\ (f <> 0%nat -> ds_prev_length s' = 0) /\ sik s s'.
Proof.
  induction f as [|f IH]; intros s mi Hf; cbv zeta.
  - cbn. split; [lia|]. split; [intros X; exfalso; exact (X eq_refl) | apply sik_refl].
  - cbn [deflate_slow_insert].
    set (s1 := set_strstart s (ds_strstart s + 1)).
    set (s2 := if ds_strstart s1 <=? mi then fst (insert_string s1 (ds_strstart s1)) else s1).
    assert (F2 : ds_strstart s2 = ds_strstart s + 1 /\ ds_prev_length s2 = ds_prev_length s /\ sik s s2).
    { subst s2. destruct (ds_strstart s1 <=? mi).
      - destruct (insert_string_norm s1 (ds_strstart s1)) as (h & pv & hd & E). rewrite E. subst s1. dsr.
        split; [reflexivity|]. split; [reflexivity|]. constructor; dsr; try reflexivity. apply dsyms_iff; dsr; reflexivity.
      - subst s1. dsr. split; [reflexivity|]. split; [reflexivity|]. constructor; dsr; try reflexivity. apply dsyms_iff; dsr; reflexivity. }
    destruct F2 as (S2 & P2 & K2).
    set (s3 := set_prev_length s2 (ds_prev_length s2 - 1)).
    assert (F3 : ds_strstart s3 = ds_strstart s + 1 /\ ds_prev_length s3 = ds_prev_length s - 1 /\ sik s s3).
    { subst s3. dsr. split; [exact S2|]. split; [rewrite P2; reflexivity|].
      eapply sik_trans; [exact K2|]. constructor; dsr; try reflexivity. apply dsyms_iff; dsr; reflexivity. }
    destruct F3 as (S3 & P3 & K3).
    destruct (Z.eqb_spec (ds_prev_length s3) 0) as [Z0|Z0]; cbn [negb].
    + split; [lia|]. split; [intros _; exact Z0 | exact K3].
    + pose proof (IH s3 mi ltac:(lia)) as X. cbv zeta in X. destruct X as (X1 & X2 & X3).
      split; [lia|]. split; [intros _; apply X2; lia | exact (sik_trans _ _ _ K3 X3)].
Qed.


Lemma div_step : forall A L K, 0 < K -> K <= L -> A / K + 1 <= (A + L) / K.
Proof.
  intros A L K HK HL. replace (A / K + 1) with ((A + 1 * K) / K) by (rewrite Z.div_add by lia; lia).
  apply Z.div_le_mono; lia.
Qed.

Lemma div_mono : forall A B K, 0 < K -> A <= B -> A / K <= B / K.
Proof. intros. apply Z.div_le_mono; lia. Qed.

Lemma zcov_ge_len : forall l, Forall sym_valid l -> Z.of_nat (length l) <= zcov l.
Proof.
  intros l H. rewrite zcov_csum. induction H as [|[d lc] l Hx H IH]; cbn [csum length]; [lia|].
  rewrite Nat2Z.inj_succ. unfold scov at 1. unfold sym_valid in Hx. destruct (Z.eqb_spec d 0); unfold MIN_MATCH; lia.
Qed.

Definition ACC (IN0 : Z) (s s' : deflate_state) : Prop :=
  Mloc s' - Mloc s <= (Aof IN0 s' - Aof IN0 s) + 5 * (Aof IN0 s' / KBLK - Aof IN0 s / KBLK)
  /\ Aof IN0 s <= Aof IN0 s'.

Lemma ACC_refl' : forall IN0 s s', Mloc s' = Mloc s -> Aof IN0 s' = Aof IN0 s -> ACC IN0 s s'.
Proof. intros IN0 s s' M A. unfold ACC. rewrite M, A. generalize (Aof IN0 s / KBLK). intros; lia. Qed.

Lemma ACC_trans : forall IN0 a b c, ACC IN0 a b -> ACC IN0 b c -> ACC IN0 a c.
Proof.
  intros IN0 a b c [A1 A2] [B1 B2]. unfold ACC in *.
  generalize dependent (Aof IN0 a / KBLK); generalize dependent (Aof IN0 b / KBLK); generalize dependent (Aof IN0 c / KBLK). intros; lia.
Qed.

Lemma ACC_flush : forall IN0 s s' L, Mloc s' <= Mloc s + L + 5 -> Aof IN0 s' = Aof IN0 s + L -> KBLK <= L -> ACC IN0 s s'.
Proof.
  intros IN0 s s' L M A HL. unfold ACC. rewrite A.
  pose proof (div_step (Aof IN0 s) L KBLK ltac:(unfold KBLK; lia) HL). unfold KBLK in *. lia.
Qed.


Section TRIP.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.
  Hypothesis HWS : ws = 32768.
  Hypothesis HLBS : PBL = 4 * 16384.
  Variable IN0 : Z.

  Let DRUN rm hb fz := drunR rm hb fz ws hs PBL ILEN OCAP tot0.
  Let DPOST := dpost ws hs PBL ILEN OCAP tot0.
  Local Notation ACC := (ACC IN0).

  Let KML : MIN_LOOKAHEAD = 262 := eq_refl.
  Let KMM : MIN_MATCH = 3 := eq_refl.

  Record BI6 (t s6 : deflate_state) : Prop := MkBI6 {
    b6_cov : forall syms, dsyms syms s6 -> zcov syms + ds_match_available t = ds_strstart t - ds_block_start t;
    b6_tf : forall syms, dsyms syms s6 -> Forall too_far_ok syms;
    b6_tfc : ds_prev_length s6 = MIN_MATCH -> wrap32 (ds_strstart s6 - 1 - ds_prev_match s6) <= TOO_FAR;
    b6_mla : MIN_MATCH <= ds_prev_length s6 -> ds_match_available s6 = 1;
    b6_nb : ds_block_start s6 < 0 -> ds_w_size s6 - MIN_LOOKAHEAD <= ds_strstart s6;
    b6_tf6 : ds_match_length s6 = MIN_MATCH -> wrap32 (ds_strstart s6 - ds_match_start s6) <= TOO_FAR }.

  Lemma BI6_intro : forall t, BI t -> BI6 t (slow_front t).
  Proof.
    intros t B. pose proof (slow_front_sff t) as F.
    constructor.
    - intros syms D. apply (bi_cov _ B). apply (sf_syms _ _ F). exact D.
    - intros syms D. apply (bi_tf _ B). apply (sf_syms _ _ F). exact D.
    - rewrite (sf_pl _ _ F), (sf_pm _ _ F), (sf_str _ _ F). exact (bi_tfc _ B).
    - rewrite (sf_pl _ _ F), (sf_ma _ _ F). exact (bi_mla _ B).
    - rewrite (sf_bs _ _ F), (sf_ws _ _ F), (sf_str _ _ F). exact (bi_nb _ B).
    - exact (sf_tf _ _ F).
  Qed.

  Lemma kp_tally_fields : forall s s' v, kproj s' = kproj (set_sym_next s v) ->
    ds_strstart s' = ds_strstart s /\ ds_block_start s' = ds_block_start s /\ ds_lookahead s' = ds_lookahead s
    /\ ds_match_available s' = ds_match_available s /\ ds_match_length s' = ds_match_length s
    /\ ds_match_start s' = ds_match_start s /\ ds_prev_length s' = ds_prev_length s /\ ds_prev_match s' = ds_prev_match s
    /\ ds_status s' = ds_status s /\ ds_wrap s' = ds_wrap s /\ ds_w_size s' = ds_w_size s /\ ds_strm s' = ds_strm s
    /\ ds_lit_bufsize s' = ds_lit_bufsize s.
  Proof.
    intros s s' v K.
    pose proof (kp_strstart _ _ K) as E1. pose proof (kp_block_start _ _ K) as E2. pose proof (kp_lookahead _ _ K) as E3.
    pose proof (kp_match_available _ _ K) as E4. pose proof (kp_match_length _ _ K) as E5. pose proof (kp_match_start _ _ K) as E6.
    pose proof (kp_prev_length _ _ K) as E7. pose proof (kp_prev_match _ _ K) as E8. pose proof (kp_status _ _ K) as E9.
    pose proof (kp_wrap _ _ K) as E10. pose proof (kp_w_size _ _ K) as E11. pose proof (kp_strm _ _ K) as E12.
    pose proof (kp_lit_bufsize _ _ K) as E13.
    revert E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13. dsr. intros. repeat split; assumption.
  Qed.

  Lemma bnone : forall t s6, DRUN 3 1 false s6 -> BI6 t s6 ->
    ds_match_available s6 = ds_match_available t -> ds_strstart s6 = ds_strstart t -> ds_block_start s6 = ds_block_start t ->
    ds_match_available s6 = 0 ->
    let s' := set_lookahead (set_strstart (set_match_available s6 1) (ds_strstart (set_match_available s6 1) + 1))
                           (ds_lookahead (set_strstart (set_match_available s6 1) (ds_strstart (set_match_available s6 1) + 1)) - 1) in
    ACC s6 s' /\ BI s' /\ ds_status s' = ds_status s6 /\ ds_wrap s' = ds_wrap s6.
  Proof.
    intros t s6 D6 B6 Ema Estr Ebs Hma. cbv zeta.
    match goal with |- ACC s6 ?X /\ _ => set (s' := X) end.
    assert (F : ds_strm s' = ds_strm s6 /\ ds_pending s' = ds_pending s6 /\ ds_bi_valid s' = ds_bi_valid s6
                /\ ds_lookahead s' = ds_lookahead s6 - 1 /\ ds_strstart s' = ds_strstart s6 + 1 /\ ds_block_start s' = ds_block_start s6
                /\ ds_match_available s' = 1 /\ ds_match_length s' = ds_match_length s6 /\ ds_match_start s' = ds_match_start s6
                /\ ds_w_size s' = ds_w_size s6 /\ ds_status s' = ds_status s6 /\ ds_wrap s' = ds_wrap s6).
    { subst s'. dsr. repeat split; reflexivity. }
    destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
    assert (SY : forall syms, dsyms syms s' <-> dsyms syms s6) by (subst s'; apply dsyms_iff; dsr; reflexivity).
    clearbody s'.
    split; [apply ACC_refl'; [apply (Mloc_frame _ _ F1 F2 F3) | rewrite (Aof_shift IN0 s6 s') by (rewrite F1; reflexivity); rewrite F4, F5, F6; lia]|].
    split; [| split; assumption].
    constructor.
    - intros syms D. apply SY in D. pose proof (b6_cov _ _ B6 syms D). rewrite F7, F5, F6. lia.
    - intros syms D. apply SY in D. exact (b6_tf _ _ B6 syms D).
    - rewrite F8, F5, F9. intros M. replace (ds_strstart s6 + 1 - 1) with (ds_strstart s6) by lia. exact (b6_tf6 _ _ B6 M).
    - intros _. exact F7.
    - rewrite F6, F10, F5. intros NB. pose proof (b6_nb _ _ B6 NB). lia.
  Qed.

  Lemma blit_mid : forall t s6, DRUN 3 1 false s6 -> BI6 t s6 ->
    ds_match_available s6 = ds_match_available t -> ds_strstart s6 = ds_strstart t -> ds_block_start s6 = ds_block_start t ->
    (MIN_MATCH <= ds_prev_length s6 -> ds_match_length s6 <= ds_prev_length s6 -> False) ->
    ds_match_available s6 <> 0 -> 1 <= ds_lookahead s6 -> 4 <= ds_level s6 -> lz_strat s6 ->
    (MIN_MATCH <= ds_match_length s6 -> ds_match_length s6 <= ds_prev_length s6
       \/ (1 <= ds_strstart s6 - ds_match_start s6 <= ds_w_size s6 - MIN_LOOKAHEAD /\ ds_match_length s6 <= ds_lookahead s6)) ->
    let '(s0, bflush) := tr_tally_lit s6 (arr_get (ds_window s6) (ds_strstart s6 - 1)) in
    let s1 := if bflush then flush_block_only s0 0 else s0 in
    ACC s6 s1 /\ ds_status s1 = ds_status s6 /\ ds_wrap s1 = ds_wrap s6 /\ ds_w_size s1 = ds_w_size s6
    /\ ds_strstart s1 = ds_strstart s6 /\ ds_match_available s1 = 1 /\ ds_match_length s1 = ds_match_length s6
    /\ ds_match_start s1 = ds_match_start s6 /\ (ds_block_start s1 = ds_block_start s6 \/ 0 <= ds_block_start s1)
    /\ (forall sy, dsyms sy s1 -> zcov sy + 1 = ds_strstart s6 + 1 - ds_block_start s1 /\ Forall too_far_ok sy).
  Proof.
    intros t s6 D6 B6 Ema Estr Ebs NM Hma Hlook Hlv Hst SF.
    pose proof D6 as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s6 C) as (Sw & Sh & Sl & Shl).
    pose proof (di_ma _ _ _ _ I) as Ima. assert (Hma1 : ds_match_available s6 = 1) by lia.
    pose proof (di_ma1 _ _ _ _ I Hma1 Slz) as Hstr1. pose proof (di_str _ _ _ _ I) as Istr.
    set (c := arr_get (ds_window s6) (ds_strstart s6 - 1)) in *.
    assert (Hc : 0 <= c < 256) by (subst c; apply (ct_win _ (di_cty _ _ _ _ I)); rewrite (cf_wl _ C); pose proof (di_sl _ _ _ _ I); pose proof (di_look _ _ _ _ I); lia).
    pose proof (slit_mid_run ws hs PBL ILEN OCAP tot0 1 s6 ltac:(lia) D6 NM Hma Hlook Hlv Hst SF) as MID. fold c in MID.
    pose proof (dinv_tally_lit 1 false s6 C I Slz P0 Sst c Hc) as TL.
    destruct (tr_tally_lit s6 c) as [s0 bflush]. cbn [fst snd] in MID, TL |- *.
    destruct MID as [D0 LF0]. destruct TL as (I0 & (syms & Dy6 & Dy0) & Hb & P1 & P2 & P3 & K0).
    pose proof (kp_tally_fields _ _ _ K0) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
    pose proof (b6_cov _ _ B6 syms Dy6) as COV. rewrite <- Ema, Hma1, <- Estr, <- Ebs in COV.
    pose proof (b6_tf _ _ B6 syms Dy6) as TF.
    assert (TF' : Forall too_far_ok (syms ++ [(0, c)])).
    { apply Forall_app. split; [exact TF|]. constructor; [| constructor]. intros X. exfalso. exact (X eq_refl). }
    assert (ZC : zcov (syms ++ [(0, c)]) = zcov syms + 1) by (rewrite zcov_app1; reflexivity).
    assert (LEN : bflush = true -> zcov (syms ++ [(0, c)]) >= KBLK).
    { intros Hbt. rewrite Hbt in Hb. symmetry in Hb. apply Z.eqb_eq in Hb.
      pose proof (sy_next _ _ Dy0) as SN. pose proof D0 as [[C0 _ _ _ _ Epbl0 _ _ _ _] _ _].
      rewrite (cf_symend _ C0) in Hb.
      pose proof (zcov_ge_len (syms ++ [(0, c)]) (sy_valid _ _ Dy0)) as GL. unfold KBLK. clear - Hb SN GL Epbl0 HLBS. lia. }
    assert (EM : Mloc s0 = Mloc s6) by exact (Mloc_frame _ _ F12 P1 P2).
    assert (EA : Aof IN0 s0 = Aof IN0 s6) by (apply Aof_frame; [rewrite F12; reflexivity | exact F3 | rewrite F1, F2; reflexivity]).
    destruct bflush; cbv zeta.
    - destruct (fbo_cb ws hs PBL ILEN OCAP tot0 TS TR HPBL HWS HLBS 0 1 false s0 0 IN0 ltac:(lia) D0 ltac:(left; reflexivity))
        as (M1 & A1 & SY1 & P1' & SN1 & BS1 & FR1).
      { intros sy Dsy. rewrite (dsyms_unique _ _ _ Dsy Dy0). rewrite F1, F2. split; [clear - ZC COV; lia | exact TF']. }
      { rewrite F2, F11, F1. exact (b6_nb _ _ B6). }
      remember (flush_block_only s0 0) as sF eqn:EsF. cbv zeta in M1, A1, SY1.
      split.
      { apply (ACC_flush IN0 s6 _ (ds_strstart s0 - ds_block_start s0)).
        - rewrite <- EM. exact M1.
        - rewrite <- EA. exact A1.
        - rewrite F1, F2. pose proof (LEN eq_refl) as X. clear - X ZC COV. lia. }
      rewrite BS1, (ff_status _ _ FR1), (ff_wrap _ _ FR1), (ff_w_size _ _ FR1), (ff_strstart _ _ FR1), (ff_match_available _ _ FR1),
              (ff_match_length _ _ FR1), (ff_match_start _ _ FR1), F9, F10, F11, F1, F4, F5, F6.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hma1|].
      split; [reflexivity|]. split; [reflexivity|]. split; [right; exact Istr|].
      intros sy Dsy; rewrite (SY1 sy Dsy), zcov_nil; split; [clear; lia | constructor].
    - split; [apply ACC_refl'; [exact EM | exact EA]|].
      rewrite F9, F10, F11, F1, F4, F5, F6, F2.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hma1|].
      split; [reflexivity|]. split; [reflexivity|]. split; [left; reflexivity|].
      intros sy Dsy; rewrite (dsyms_unique _ _ _ Dsy Dy0); split; [clear -ZC COV; lia | exact TF'].
  Qed.

  Lemma blit : forall t s6, DRUN 3 1 false s6 -> BI6 t s6 ->
    ds_match_available s6 = ds_match_available t -> ds_strstart s6 = ds_strstart t -> ds_block_start s6 = ds_block_start t ->
    (MIN_MATCH <= ds_prev_length s6 -> ds_match_length s6 <= ds_prev_length s6 -> False) ->
    ds_match_available s6 <> 0 -> 1 <= ds_lookahead s6 -> 4 <= ds_level s6 -> lz_strat s6 ->
    (MIN_MATCH <= ds_match_length s6 -> ds_match_length s6 <= ds_prev_length s6
       \/ (1 <= ds_strstart s6 - ds_match_start s6 <= ds_w_size s6 - MIN_LOOKAHEAD /\ ds_match_length s6 <= ds_lookahead s6)) ->
    let '(s0, bflush) := tr_tally_lit s6 (arr_get (ds_window s6) (ds_strstart s6 - 1)) in
    let s1 := if bflush then flush_block_only s0 0 else s0 in
    let s2 := set_strstart s1 (ds_strstart s1 + 1) in
    let s3 := set_lookahead s2 (ds_lookahead s2 - 1) in
    ACC s6 s3 /\ BI s3 /\ ds_status s3 = ds_status s6 /\ ds_wrap s3 = ds_wrap s6.
  Proof.
    intros t s6 D6 B6 Ema Estr Ebs NM Hma Hlook Hlv Hst SF.
    pose proof (blit_mid t s6 D6 B6 Ema Estr Ebs NM Hma Hlook Hlv Hst SF) as MID.
    destruct (tr_tally_lit s6 (arr_get (ds_window s6) (ds_strstart s6 - 1))) as [s0 bflush]. cbv zeta in MID |- *.
    remember (if bflush then flush_block_only s0 0 else s0) as s1 eqn:Es1. clear Es1.
    destruct MID as (ACC1 & St1 & Wr1 & Ws1 & Str1 & Ma1 & Ml1 & Ms1 & Sp1 & SY1).
    match goal with |- ACC s6 ?X /\ _ => set (s3 := X) end.
    assert (F : ds_strm s3 = ds_strm s1 /\ ds_pending s3 = ds_pending s1 /\ ds_bi_valid s3 = ds_bi_valid s1
                /\ ds_lookahead s3 = ds_lookahead s1 - 1 /\ ds_strstart s3 = ds_strstart s1 + 1 /\ ds_block_start s3 = ds_block_start s1
                /\ ds_match_available s3 = ds_match_available s1 /\ ds_match_length s3 = ds_match_length s1 /\ ds_match_start s3 = ds_match_start s1
                /\ ds_w_size s3 = ds_w_size s1 /\ ds_status s3 = ds_status s1 /\ ds_wrap s3 = ds_wrap s1).
    { subst s3. dsr. repeat split; reflexivity. }
    destruct F as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
    assert (SY3 : forall sy, dsyms sy s3 <-> dsyms sy s1) by (subst s3; apply dsyms_iff; dsr; reflexivity).
    clearbody s3.
    split.
    { eapply ACC_trans; [exact ACC1|]. apply ACC_refl'; [apply (Mloc_frame _ _ G1 G2 G3) | rewrite (Aof_shift IN0 s1 s3) by (rewrite G1; reflexivity); rewrite G4, G5, G6; lia]. }
    split; [| rewrite G11, G12; split; assumption].
    constructor.
    - intros sy Dsy. apply SY3 in Dsy. destruct (SY1 sy Dsy) as [X _]. rewrite G7, G5, G6, Ma1. clear - X Str1. lia.
    - intros sy Dsy. apply SY3 in Dsy. exact (proj2 (SY1 sy Dsy)).
    - rewrite G8, G9, G5, Ml1, Ms1, Str1. intros M. replace (ds_strstart s6 + 1 - 1) with (ds_strstart s6) by lia. exact (b6_tf6 _ _ B6 M).
    - intros _. rewrite G7. exact Ma1.
    - rewrite G6, G10, G5, Ws1, Str1. intros NB. destruct Sp1 as [E|E]; [| exfalso; clear - NB E; lia]. rewrite E in NB. pose proof (b6_nb _ _ B6 NB) as X.
      clear - X. lia.
  Qed.


  Lemma bmatch : forall t s6, DRUN 3 1 false s6 -> BI6 t s6 ->
    ds_match_available s6 = ds_match_available t -> ds_strstart s6 = ds_strstart t -> ds_block_start s6 = ds_block_start t ->
    MIN_MATCH <= ds_prev_length s6 -> ds_match_length s6 <= ds_prev_length s6 ->
    1 <= ds_strstart s6 -> 1 <= wrap32 (ds_strstart s6 - 1 - ds_prev_match s6) <= ds_w_size s6 - MIN_LOOKAHEAD ->
    ds_prev_length s6 <= ds_lookahead s6 + 1 -> 4 <= ds_level s6 -> lz_strat s6 ->
    let max_insert := wrap32 (ds_strstart s6 + ds_lookahead s6 - MIN_MATCH) in
    let '(s5, bflush) := tr_tally_dist s6 (wrap32 (ds_strstart s6 - 1 - ds_prev_match s6)) (ds_prev_length s6 - MIN_MATCH) in
    let sa := set_lookahead s5 (wrap32 (ds_lookahead s5 - (ds_prev_length s5 - 1))) in
    let sb := set_prev_length sa (ds_prev_length sa - 2) in
    let sc := deflate_slow_insert (Z.to_nat (ds_prev_length sb)) sb max_insert in
    let sd := set_match_available sc 0 in let se := set_match_length sd (MIN_MATCH - 1) in
    let s11 := set_strstart se (ds_strstart se + 1) in
    let s' := (if bflush then fst (flush_block s11 0) else s11) in
    ACC s6 s' /\ BI s' /\ ds_status s' = ds_status s6 /\ ds_wrap s' = ds_wrap s6.
  Proof.
    intros t s6 D6 B6 Ema Estr Ebs Hpl Hmlpl Hstr1 HD Hpll Hlv Hst.
    pose proof D6 as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s6 C) as (Sw & Sh & Sl & Shl).
    pose proof (di_pl _ _ _ _ I) as Ipl. pose proof (di_str _ _ _ _ I) as Istr.
    cbv zeta. rewrite (wrap32_id (ds_strstart s6 + ds_lookahead s6 - MIN_MATCH)) by (pose proof (di_sl _ _ _ _ I); lia).
    set (DD := wrap32 (ds_strstart s6 - 1 - ds_prev_match s6)) in *.
    pose proof (smatch_mid_run ws hs PBL ILEN OCAP tot0 s6 D6 Hpl Hmlpl Hstr1 HD Hpll Hlv Hst) as MID.
    cbv zeta in MID. fold DD in MID. rewrite (wrap32_id (ds_strstart s6 + ds_lookahead s6 - MIN_MATCH)) in MID by (pose proof (di_sl _ _ _ _ I); lia).
    pose proof (dinv_tally_dist 1 false s6 C I Slz P0 Sst DD (ds_prev_length s6 - MIN_MATCH) HD ltac:(unfold MAX_MATCH in Ipl; lia)) as TD.
    destruct (tr_tally_dist s6 DD (ds_prev_length s6 - MIN_MATCH)) as [s5 bflush]. cbn [fst snd] in MID, TD |- *.
    destruct MID as (D11 & L11 & Sm11 & _ & _). destruct TD as (I5 & (syms & Dy6 & Dy5) & Hb & P1 & P2 & P3 & K5).
    pose proof (kp_tally_fields _ _ _ K5) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
    pose proof (b6_mla _ _ B6 Hpl) as MA1.
    pose proof (b6_cov _ _ B6 syms Dy6) as COV. rewrite <- Ema, MA1, <- Estr, <- Ebs in COV.
    pose proof (b6_tf _ _ B6 syms Dy6) as TF.
    assert (TF' : Forall too_far_ok (syms ++ [(DD, ds_prev_length s6 - MIN_MATCH)])).
    { apply Forall_app. split; [exact TF|]. constructor; [| constructor].
      unfold too_far_ok. cbn [fst snd]. intros _ L0. apply (b6_tfc _ _ B6). lia. }
    assert (ZC : zcov (syms ++ [(DD, ds_prev_length s6 - MIN_MATCH)]) = zcov syms + ds_prev_length s6).
    { rewrite zcov_app1. replace (DD =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
    match goal with |- ACC s6 (if bflush then fst (flush_block ?X 0) else _) /\ _ => set (s11 := X) in * end.
    assert (F : ds_strm s11 = ds_strm s6 /\ ds_pending s11 = ds_pending s6 /\ ds_bi_valid s11 = ds_bi_valid s6
                /\ ds_lookahead s11 = ds_lookahead s6 - (ds_prev_length s6 - 1)
                /\ ds_strstart s11 = ds_strstart s6 + ds_prev_length s6 - 1 /\ ds_block_start s11 = ds_block_start s6
                /\ ds_match_available s11 = 0 /\ ds_match_length s11 = MIN_MATCH - 1
                /\ ds_w_size s11 = ds_w_size s6 /\ ds_status s11 = ds_status s6 /\ ds_wrap s11 = ds_wrap s6
                /\ (forall sy, dsyms sy s11 <-> dsyms sy s5)).
    { subst s11.
      set (sb := set_prev_length (set_lookahead s5 (wrap32 (ds_lookahead s5 - (ds_prev_length s5 - 1)))) (ds_prev_length (set_lookahead s5 (wrap32 (ds_lookahead s5 - (ds_prev_length s5 - 1)))) - 2)).
      assert (Fb : ds_strm sb = ds_strm s6 /\ ds_pending sb = ds_pending s6 /\ ds_bi_valid sb = ds_bi_valid s6
                   /\ ds_prev_length sb = ds_prev_length s6 - 2 /\ ds_strstart sb = ds_strstart s6 /\ ds_block_start sb = ds_block_start s6
                   /\ ds_w_size sb = ds_w_size s6 /\ ds_status sb = ds_status s6 /\ ds_wrap sb = ds_wrap s6
                   /\ (forall sy, dsyms sy sb <-> dsyms sy s5) /\ ds_lookahead sb = ds_lookahead s6 - (ds_prev_length s6 - 1)).
      { subst sb. dsr. rewrite F12, P1, P2, F7, F1, F2, F11, F9, F10, F3. repeat (split; [reflexivity|]). split; [apply dsyms_iff; dsr; reflexivity|].
        apply wrap32_id. unfold MAX_MATCH in Ipl. pose proof (di_look _ _ _ _ I). pose proof (di_sl _ _ _ _ I). clear - Ipl H H0 Hpll Hpl Sw Istr KMM. lia. }
      destruct Fb as (B1 & B2 & B3 & B4 & B5 & B6' & B7 & B8 & B9 & B10 & B11).
      pose proof (slow_insert_fields (Z.to_nat (ds_prev_length sb)) sb (ds_strstart s6 + ds_lookahead s6 - MIN_MATCH) ltac:(rewrite B4; lia)) as INS.
      cbv zeta in INS. destruct INS as (IS & IP & IK).
      remember (deflate_slow_insert (Z.to_nat (ds_prev_length sb)) sb (ds_strstart s6 + ds_lookahead s6 - MIN_MATCH)) as sc eqn:Esc. clear Esc.
      dsr. rewrite (ik_strm _ _ IK), (ik_pend _ _ IK), (ik_bv _ _ IK), (ik_look _ _ IK), IS, (ik_bs _ _ IK), (ik_ws _ _ IK), (ik_status _ _ IK), (ik_wrap _ _ IK),
              B1, B2, B3, B4, B5, B6', B7, B8, B9, B11.
      repeat (split; [first [reflexivity | lia] |]).
      intros sy. rewrite <- B10, <- (ik_syms _ _ IK). apply dsyms_iff; dsr; reflexivity. }
    destruct F as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
    clearbody s11.
    assert (Dy11 : dsyms (syms ++ [(DD, ds_prev_length s6 - MIN_MATCH)]) s11) by (apply G12; exact Dy5).
    assert (EM : Mloc s11 = Mloc s6) by exact (Mloc_frame _ _ G1 G2 G3).
    assert (EA : Aof IN0 s11 = Aof IN0 s6) by (rewrite (Aof_shift IN0 s6 s11) by (rewrite G1; reflexivity); rewrite G4, G5, G6; lia).
    assert (COV11 : forall sy, dsyms sy s11 -> zcov sy = ds_strstart s11 - ds_block_start s11 /\ Forall too_far_ok sy).
    { intros sy Dsy. rewrite (dsyms_unique _ _ _ Dsy Dy11). rewrite G5, G6. split; [clear - ZC COV; lia | exact TF']. }
    assert (NB11 : ds_block_start s11 < 0 -> ds_w_size s11 - MIN_LOOKAHEAD <= ds_strstart s11).
    { rewrite G6, G9, G5. intros NB. pose proof (b6_nb _ _ B6 NB). lia. }
    assert (LEN : bflush = true -> KBLK <= ds_strstart s11 - ds_block_start s11).
    { intros Hbt. rewrite Hbt in Hb. symmetry in Hb. apply Z.eqb_eq in Hb.
      pose proof (sy_next _ _ Dy5) as SN. pose proof (cf_symend _ (dcfg_kproj _ _ K5 (dcfg_set_sym_next _ _ C))) as SE.
      pose proof (kp_lit_bufsize _ _ K5) as LB. revert LB. dsr. intros LB. rewrite SE, LB in Hb.
      pose proof (zcov_ge_len _ (sy_valid _ _ Dy5)) as GL. rewrite G5, G6. unfold KBLK. clear - Hb SN GL Epbl HLBS ZC COV. lia. }
    destruct bflush.
    -
      destruct (fbo_cb ws hs PBL ILEN OCAP tot0 TS TR HPBL HWS HLBS 0 0 true s11 0 IN0 ltac:(lia) D11 ltac:(left; reflexivity) COV11 NB11)
        as (M1 & A1 & SY1 & P1' & SN1 & BS1 & FR1).
      assert (EF : fst (flush_block s11 0) = flush_block_only s11 0).
      { unfold flush_block. destruct (cs_avail_out _ =? 0); reflexivity. }
      rewrite EF. remember (flush_block_only s11 0) as sF eqn:EsF. cbv zeta in M1, A1, SY1.
      split.
      { apply (ACC_flush IN0 s6 _ (ds_strstart s11 - ds_block_start s11)).
        - rewrite <- EM. exact M1.
        - rewrite <- EA. exact A1.
        - exact (LEN eq_refl). }
      rewrite (ff_status _ _ FR1), (ff_wrap _ _ FR1), G10, G11. split; [| split; reflexivity].
      pose proof (di_str _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ P1')) as Sstr.
      constructor.
      + intros sy Dsy. rewrite (SY1 sy Dsy), zcov_nil, (ff_match_available _ _ FR1), BS1, G7. lia.
      + intros sy Dsy. rewrite (SY1 sy Dsy). constructor.
      + rewrite (ff_match_length _ _ FR1), G8. unfold MIN_MATCH. intros X; exfalso; lia.
      + rewrite (ff_match_length _ _ FR1), G8. unfold MIN_MATCH. intros X; exfalso; lia.
      + rewrite BS1. intros X; exfalso; lia.
    - split; [apply ACC_refl'; [exact EM | exact EA]|].
      rewrite G10, G11. split; [| split; reflexivity].
      constructor.
      + intros sy Dsy. destruct (COV11 sy Dsy) as [X _]. rewrite G7. lia.
      + intros sy Dsy. exact (proj2 (COV11 sy Dsy)).
      + rewrite G8. unfold MIN_MATCH. intros X; exfalso; lia.
      + rewrite G8. unfold MIN_MATCH. intros X; exfalso; lia.
      + exact NB11.
  Qed.

  Definition TPOST (t s' : deflate_state) : Prop :=
    ACC t s' /\ BI s' /\ ds_status s' = ds_status t /\ ds_wrap s' = ds_wrap t.

  Lemma bdisp : forall t, DRUN 3 0 true t -> BI t -> 1 <= ds_lookahead t ->
    ds_strstart t + MIN_LOOKAHEAD <= 2 * ds_w_size t -> 4 <= ds_level t -> lz_strat t ->
    TPOST t (fst (sdispatch (slow_front t))).
  Proof.
    intros t D B Hlook Hstr Hlv Hst.
    destruct (slow_front_run ws hs PBL ILEN OCAP tot0 t D Hlook Hstr Hlv Hst) as (D6 & El & Es & Ew & Elv & Esg & Esm & PREV & CUR).
    pose proof (slow_front_sff t) as SFF. pose proof (BI6_intro t B) as B6.
    remember (slow_front t) as s6 eqn:Es6. clear Es6.
    assert (A06 : ACC t s6).
    { apply ACC_refl'; [apply (Mloc_frame _ _ (sf_strm _ _ SFF) (sf_pend _ _ SFF) (sf_bv _ _ SFF))
                        | apply Aof_frame; [rewrite (sf_strm _ _ SFF); reflexivity | exact (sf_look _ _ SFF) | rewrite (sf_str _ _ SFF), (sf_bs _ _ SFF); reflexivity]]. }
    assert (LIFT : forall s', TPOST s6 s' -> TPOST t s').
    { intros s' (A & B' & St & Wr). split; [exact (ACC_trans _ _ _ _ A06 A)|]. split; [exact B'|].
      rewrite St, Wr, (sf_status _ _ SFF), (sf_wrap _ _ SFF). split; reflexivity. }
    pose proof (sf_ma _ _ SFF) as Ema. pose proof (sf_str _ _ SFF) as Estr. pose proof (sf_bs _ _ SFF) as Ebs.
    pose proof D6 as [[C6 I6 _ _ _ _ _ _ _ _] _ _].
    unfold sdispatch.
    destruct (Z.leb_spec MIN_MATCH (ds_prev_length s6)) as [Hpl|Hpl]; destruct (Z.leb_spec (ds_match_length s6) (ds_prev_length s6)) as [Hml|Hml]; cbn [andb].
    -
      destruct (PREV Hpl) as (Hstr1 & HD & Hpll).
      pose proof (bmatch t s6 D6 B6 Ema Estr Ebs Hpl Hml Hstr1 HD Hpll ltac:(rewrite Elv; exact Hlv) ltac:(unfold lz_strat; rewrite Esg; exact Hst)) as BM.
      assert (W32 : 0 <= ds_strstart s6 + ds_lookahead s6 - MIN_MATCH < 2 ^ 32).
      { pose proof (di_sl _ _ _ _ I6). pose proof (dcfg_sizes s6 C6). unfold MIN_MATCH in *. clear - H H0 Hstr1 Hpll Hpl. lia. }
      cbv zeta in BM. rewrite (wrap32_id (ds_strstart s6 + ds_lookahead s6 - MIN_MATCH)) by exact W32.
      rewrite (wrap32_id (ds_strstart s6 + ds_lookahead s6 - MIN_MATCH)) in BM by exact W32.
      destruct (tr_tally_dist s6 _ _) as [s5 bflush]. cbv zeta in BM |- *.
      apply LIFT. destruct bflush; [| exact BM].
      match goal with |- TPOST s6 (fst (let '(s7, r) := flush_block ?X 0 in _)) => destruct (flush_block X 0) as [s7 [bs|]]; exact BM end.
    -
      assert (NM : MIN_MATCH <= ds_prev_length s6 -> ds_match_length s6 <= ds_prev_length s6 -> False) by lia.
      destruct (Z.eqb_spec (ds_match_available s6) 0) as [Hma|Hma]; cbn [negb].
      + apply LIFT. exact (bnone t s6 D6 B6 Ema Estr Ebs Hma).
      + pose proof (blit t s6 D6 B6 Ema Estr Ebs NM Hma ltac:(rewrite El; exact Hlook) ltac:(rewrite Elv; exact Hlv) ltac:(unfold lz_strat; rewrite Esg; exact Hst) CUR) as BL.
        destruct (tr_tally_lit s6 _) as [s0 bflush]. cbv zeta in BL |- *.
        apply LIFT. destruct (cs_avail_out _ =? 0); exact BL.
    - assert (NM : MIN_MATCH <= ds_prev_length s6 -> ds_match_length s6 <= ds_prev_length s6 -> False) by lia.
      destruct (Z.eqb_spec (ds_match_available s6) 0) as [Hma|Hma]; cbn [negb].
      + apply LIFT. exact (bnone t s6 D6 B6 Ema Estr Ebs Hma).
      + pose proof (blit t s6 D6 B6 Ema Estr Ebs NM Hma ltac:(rewrite El; exact Hlook) ltac:(rewrite Elv; exact Hlv) ltac:(unfold lz_strat; rewrite Esg; exact Hst) CUR) as BL.
        destruct (tr_tally_lit s6 _) as [s0 bflush]. cbv zeta in BL |- *.
        apply LIFT. destruct (cs_avail_out _ =? 0); exact BL.
    - assert (NM : MIN_MATCH <= ds_prev_length s6 -> ds_match_length s6 <= ds_prev_length s6 -> False) by lia.
      destruct (Z.eqb_spec (ds_match_available s6) 0) as [Hma|Hma]; cbn [negb].
      + apply LIFT. exact (bnone t s6 D6 B6 Ema Estr Ebs Hma).
      + pose proof (blit t s6 D6 B6 Ema Estr Ebs NM Hma ltac:(rewrite El; exact Hlook) ltac:(rewrite Elv; exact Hlv) ltac:(unfold lz_strat; rewrite Esg; exact Hst) CUR) as BL.
        destruct (tr_tally_lit s6 _) as [s0 bflush]. cbv zeta in BL |- *.
        apply LIFT. destruct (cs_avail_out _ =? 0); exact BL.
  Qed.

  Variable flush : Z.

  Theorem btrip : forall s, DRUN 3 0 true s -> BI s -> 4 <= ds_level s -> lz_strat s ->
    TPOST s (fst (deflate_slow_body s flush)).
  Proof.
    intros s D B Hlv Hst. pose proof D as [[C I _ Ews _ _ _ _ _ _] _ _].
    rewrite deflate_slow_body_eq.
    destruct (Z.ltb_spec (ds_lookahead s) MIN_LOOKAHEAD) as [Hl|Hl].
    - pose proof (fw_BI ws hs PBL ILEN OCAP tot0 3 true s IN0 D Hl B) as FW. cbv zeta in FW.
      destruct FW as (B1 & M1 & A1 & St1 & Wr1 & Ml1 & Ma1 & D1 & ST1 & EX1 & L1 & CONS1).
      pose proof (fw_level _ _ (fwz_fill_window s)) as Lv1. pose proof (fw_strategy _ _ (fwz_fill_window s)) as Sg1.
      remember (fill_window s) as s1 eqn:Es1. clear Es1.
      assert (T1 : TPOST s s1) by (split; [apply ACC_refl'; assumption | split; [exact B1 | split; assumption]]).
      cbv zeta. destruct ((ds_lookahead s1 <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)); [exact T1|].
      destruct (Z.eqb_spec (ds_lookahead s1) 0) as [L0|L0]; [exact T1|].
      rewrite slow_p1_front. pose proof D1 as [[C1 I1 _ Ews1 _ _ _ _ _ _] _ _].
      pose proof (bdisp s1 D1 B1 ltac:(pose proof (di_look _ _ _ _ I1); lia) ltac:(rewrite Ews1; lia)
                    ltac:(rewrite Lv1; exact Hlv) ltac:(unfold lz_strat; rewrite Sg1; exact Hst)) as (A2 & B2 & St2 & Wr2).
      destruct T1 as (A1' & _ & St1' & Wr1').
      split; [exact (ACC_trans _ _ _ _ A1' A2)|]. split; [exact B2|]. rewrite St2, Wr2. split; assumption.
    - cbv zeta. rewrite slow_p1_front.
      apply (bdisp s D B); [lia | | exact Hlv | exact Hst].
      pose proof (di_sl _ _ _ _ I). rewrite Ews in *. lia.
  Qed.

  Lemma bloop : forall n s, DRUN 3 0 true s -> BI s -> 4 <= ds_level s -> lz_strat s -> lzm s < Z.of_nat n ->
    let '(s', r) := deflate_slow_loop n s flush in
    TPOST s s' /\ ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s
    /\ match r with None => DRUN 3 0 true s' /\ ds_lookahead s' = 0 /\ flush <> Z_NO_FLUSH
                    | Some bs => bs = need_more /\ DPOST s' /\ NMPROG flush s' end.
  Proof.
    induction n as [|n IH]; intros s D B Hlv Hst HM.
    { exfalso. unfold DeflInvFast.lzm in HM. pose proof (di_look _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))).
      pose proof (dc_ai _ _ _ _ (dp_call _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))). cbn in HM. lia. }
    rewrite deflate_slow_loop_step.
    destruct (strip_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush s D Hlv Hst) as [_ TP].
    pose proof (btrip s D B Hlv Hst) as T1.
    destruct (deflate_slow_body s flush) as [s1 o]. cbn [fst] in T1. destruct TP as [[EL ES] TP].
    destruct T1 as (A1 & B1 & St1 & Wr1).
    destruct o as [| |bs].
    - destruct TP as [D1 M1].
      specialize (IH s1 D1 B1 ltac:(rewrite EL; exact Hlv) ltac:(unfold lz_strat; rewrite ES; exact Hst) ltac:(rewrite Nat2Z.inj_succ in HM; lia)).
      destruct (deflate_slow_loop n s1 flush) as [s' r]. destruct IH as ((A2 & B2 & St2 & Wr2) & EL2 & ES2 & R2).
      split; [split; [exact (ACC_trans _ _ _ _ A1 A2) | split; [exact B2 | split; congruence]]|].
      split; [congruence|]. split; [congruence | exact R2].
    - split; [split; [exact A1 | split; [exact B1 | split; assumption]]|]. split; [exact EL|]. split; [exact ES | exact TP].
    - split; [split; [exact A1 | split; [exact B1 | split; assumption]]|]. split; [exact EL|]. split; [exact ES | exact TP].
  Qed.

  Definition ACCF (s s' : deflate_state) : Prop :=
    Mloc s' - Mloc s <= (Aof IN0 s' - Aof IN0 s) + 5 * (Aof IN0 s' / KBLK - Aof IN0 s / KBLK) + 5
    /\ Aof IN0 s <= Aof IN0 s'.

  Lemma ACC_ACCF : forall s s', ACC s s' -> ACCF s s'.
  Proof. intros s s' [A B]. unfold ACCF. split; [| exact B]. generalize dependent (Aof IN0 s' / KBLK). generalize dependent (Aof IN0 s / KBLK). intros; lia. Qed.

  Lemma ACC_ACCF_trans : forall a b c, ACC a b -> ACCF b c -> ACCF a c.
  Proof.
    intros a b c [A1 A2] [B1 B2]. unfold ACCF.
    generalize dependent (Aof IN0 a / KBLK); generalize dependent (Aof IN0 b / KBLK); generalize dependent (Aof IN0 c / KBLK). intros; lia.
  Qed.

  Lemma ACCF_flush : forall s s' L, Mloc s' <= Mloc s + L + 5 -> Aof IN0 s' = Aof IN0 s + L -> 0 <= L -> ACCF s s'.
  Proof.
    intros s s' L M A HL. unfold ACCF. rewrite A.
    pose proof (div_mono (Aof IN0 s) (Aof IN0 s + L) KBLK ltac:(unfold KBLK; lia) ltac:(lia)).
    generalize dependent (Aof IN0 s / KBLK); generalize dependent ((Aof IN0 s + L) / KBLK). intros; lia.
  Qed.

  Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

  Lemma btail : forall s, DRUN 3 0 true s -> BI s -> ds_lookahead s = 0 -> 4 <= ds_level s -> lz_strat s -> flush = Z_FINISH ->
    let '(s', bs) :=
      (let s1 := if negb (Z.eqb (ds_match_available s) 0) then
                   let '(s1, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in set_match_available s1 0
                 else s in
       let s2 := set_insert s1 (if Z.ltb (ds_strstart s1) (MIN_MATCH - 1) then ds_strstart s1 else MIN_MATCH - 1) in
       deflate_tail s2 flush) in
    ACCF s s' /\ BI s' /\ ds_status s' = ds_status s /\ ds_wrap s' = ds_wrap s /\ (bs = finish_started \/ bs = finish_done)
    /\ (forall syms, dsyms syms s' -> syms = []) /\ ds_match_available s' = 0 /\ ds_block_start s' = ds_strstart s' /\ ds_lookahead s' = 0.
  Proof.
    intros s D B Hlook Hlv Hst HF. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl). pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_ma _ _ _ _ I) as Ima.
    destruct (stail_mid_run ws hs PBL ILEN OCAP tot0 s D Hlook Hlv Hst) as (rm & Hrm & MID). cbv zeta in MID.
    assert (S1 : let s1 := (if negb (ds_match_available s =? 0) then
                             let '(s1, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in set_match_available s1 0
                           else s) in
                 Mloc s1 = Mloc s /\ Aof IN0 s1 = Aof IN0 s /\ ds_status s1 = ds_status s /\ ds_wrap s1 = ds_wrap s /\ ds_w_size s1 = ds_w_size s
                 /\ ds_strstart s1 = ds_strstart s /\ ds_block_start s1 = ds_block_start s
                 /\ (forall sy, dsyms sy s1 -> zcov sy = ds_strstart s1 - ds_block_start s1 /\ Forall too_far_ok sy)).
    { destruct (Z.eqb_spec (ds_match_available s) 0) as [M0|M0]; cbn [negb].
      - repeat (split; [reflexivity|]). intros sy Dsy. pose proof (bi_cov _ B sy Dsy) as X. rewrite M0 in X. split; [lia | exact (bi_tf _ B sy Dsy)].
      - assert (Hma1 : ds_match_available s = 1) by lia.
        set (c := arr_get (ds_window s) (ds_strstart s - 1)) in *.
        assert (Hc : 0 <= c < 256).
        { subst c; apply (ct_win _ (di_cty _ _ _ _ I)); rewrite (cf_wl _ C). pose proof (di_ma1 _ _ _ _ I Hma1 Slz). pose proof (di_sl _ _ _ _ I). lia. }
        pose proof (dinv_tally_lit 0 true s C I Slz P0 Sst c Hc) as TL.
        destruct (tr_tally_lit s c) as [s0 bf]. cbn [fst snd] in TL |- *.
        destruct TL as (I0 & (syms & Dy & Dy0) & Hb & P1 & P2 & P3 & K0).
        pose proof (kp_tally_fields _ _ _ K0) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
        cbv zeta. dsr. rewrite F9, F10, F11, F1, F2.
        split; [apply Mloc_frame; dsr; [exact F12 | exact P1 | exact P2]|].
        split; [apply Aof_frame; dsr; [rewrite F12; reflexivity | exact F3 | rewrite F1, F2; reflexivity]|].
        repeat (split; [reflexivity|]).
        intros sy Dsy. assert (Dsy' : dsyms sy s0) by (revert Dsy; apply dsyms_iff; dsr; reflexivity).
        rewrite (dsyms_unique _ _ _ Dsy' Dy0). pose proof (bi_cov _ B syms Dy) as X. rewrite Hma1 in X.
        rewrite zcov_app1. cbn [Z.eqb]. split; [lia|].
        apply Forall_app. split; [exact (bi_tf _ B syms Dy)|]. constructor; [| constructor]. intros X'. exfalso. exact (X' eq_refl). }
    cbv zeta in S1.
    remember (if negb (ds_match_available s =? 0) then let '(s1, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in set_match_available s1 0 else s)
      as s1 eqn:Es1. clear Es1.
    destruct MID as (D1 & L1 & MA1 & EL1 & ES1). destruct S1 as (M1 & A1 & St1 & Wr1 & Ws1 & Str1 & Bs1 & COV1).
    cbv zeta.
    remember (set_insert s1 (if ds_strstart s1 <? MIN_MATCH - 1 then ds_strstart s1 else MIN_MATCH - 1)) as s2 eqn:Es2.
    assert (D2 : DRUN rm 0 true s2).
    { subst s2. pose proof D1 as [[C1 I1 CL1 _ _ _ _ _ _ _] _ _].
      eapply drun_relift; [exact D1 | | apply dcfg_set_insert; exact C1 | dsr; reflexivity ..].
      apply dinv_set_insert; [exact I1 |]. dsr. pose proof (di_str _ _ _ _ I1). unfold MIN_MATCH. destruct (Z.ltb_spec (ds_strstart s1) (3 - 1)); lia. }
    assert (F2 : Mloc s2 = Mloc s1 /\ Aof IN0 s2 = Aof IN0 s1 /\ ds_status s2 = ds_status s1 /\ ds_wrap s2 = ds_wrap s1 /\ ds_w_size s2 = ds_w_size s1
                 /\ ds_strstart s2 = ds_strstart s1 /\ ds_block_start s2 = ds_block_start s1 /\ ds_match_available s2 = ds_match_available s1
                 /\ (forall sy, dsyms sy s2 <-> dsyms sy s1)
                 /\ ds_lookahead s2 = ds_lookahead s1 /\ ds_match_length s2 = ds_match_length s1 /\ ds_level s2 = ds_level s1 /\ ds_strategy s2 = ds_strategy s1).
    { subst s2. split; [apply Mloc_frame; dsr; reflexivity|]. split; [apply Aof_frame; dsr; reflexivity|]. dsr. repeat (split; [reflexivity|]).
      split; [apply dsyms_iff; dsr; reflexivity|]. repeat split; reflexivity. }
    clear Es2. destruct F2 as (M2 & A2 & St2 & Wr2 & Ws2 & Str2 & Bs2 & Ma2 & SY2 & Lk2 & Ml2 & Lv2 & Sg2).
    unfold deflate_tail. rewrite HF. cbn [Z.eqb Z_FINISH Pos.eqb].
    destruct (fbo_cb ws hs PBL ILEN OCAP tot0 TS TR HPBL HWS HLBS rm 0 true s2 1 IN0 Hrm D2 ltac:(right; reflexivity)) as (M3 & A3 & SY3 & P3 & SN3 & BS3 & FR3).
    { intros sy Dsy. apply SY2 in Dsy. rewrite Str2, Bs2. exact (COV1 sy Dsy). }
    { rewrite Bs2, Ws2, Str2, Bs1, Ws1, Str1. exact (bi_nb _ B). }
    cbv zeta in M3, A3, SY3.
    unfold flush_block. cbv zeta. remember (flush_block_only s2 1) as sF eqn:EsF. clear EsF.
    pose proof (di_str _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D2))) as Str2'.
    pose proof (di_bs _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D2))) as Bs2'.
    assert (ML : ds_match_length sF < MIN_MATCH).
    { rewrite (ff_match_length _ _ FR3).
      pose proof (di_slow _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D2)) eq_refl) as SL.
      destruct (Z.lt_ge_cases (ds_match_length s2) MIN_MATCH) as [X|X]; [exact X|]. exfalso.
      destruct (SL ltac:(rewrite Lv2, EL1; exact Hlv) ltac:(unfold lz_strat; rewrite Sg2, ES1; exact Hst) ltac:(lia)) as (_ & _ & Y).
      rewrite Lk2, L1 in Y. unfold MIN_MATCH in X. lia. }
    assert (POST : forall bs, (bs = finish_started \/ bs = finish_done) ->
      ACCF s sF /\ BI sF /\ ds_status sF = ds_status s /\ ds_wrap sF = ds_wrap s /\ (bs = finish_started \/ bs = finish_done)
      /\ (forall syms, dsyms syms sF -> syms = []) /\ ds_match_available sF = 0 /\ ds_block_start sF = ds_strstart sF /\ ds_lookahead sF = 0).
    { intros bs Hbs. split.
      { apply (ACCF_flush s sF (ds_strstart s2 - ds_block_start s2)).
        - rewrite <- M1, <- M2. exact M3.
        - rewrite <- A1, <- A2. exact A3.
        - lia. }
      split.
      { constructor.
        - intros sy Dsy. rewrite (SY3 sy Dsy), zcov_nil, (ff_match_available _ _ FR3), BS3, Ma2, MA1. lia.
        - intros sy Dsy. rewrite (SY3 sy Dsy). constructor.
        - intros X. exfalso. unfold MIN_MATCH in *. lia.
        - intros X. exfalso. unfold MIN_MATCH in *. lia.
        - rewrite BS3. intros X. exfalso. pose proof (ff_strstart _ _ FR3). lia. }
      rewrite (ff_status _ _ FR3), (ff_wrap _ _ FR3), St2, Wr2, St1, Wr1, (ff_match_available _ _ FR3), Ma2, MA1.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Hbs|]. split; [exact SY3|]. split; [reflexivity|]. split; [exact BS3|].
      rewrite (ff_lookahead _ _ FR3), Lk2. exact L1. }
    destruct (cs_avail_out (ds_strm sF) =? 0); cbn [negb Z.eqb]; apply POST; auto.
  Qed.

  Theorem bslow : forall s, DRUN 3 0 true s -> BI s -> 4 <= ds_level s -> lz_strat s ->
    let '(s', bs) := deflate_slow s flush in
    BI s' /\ ds_status s' = ds_status s /\ ds_wrap s' = ds_wrap s
    /\ ((bs = need_more /\ ACC s s')
        \/ ((bs = finish_started \/ bs = finish_done) /\ ACCF s s' /\ flush = Z_FINISH /\ ds_lookahead s' = 0
            /\ (forall syms, dsyms syms s' -> syms = []) /\ ds_match_available s' = 0 /\ ds_block_start s' = ds_strstart s')).
  Proof.
    intros s D B Hlv Hst. unfold deflate_slow. pose proof D as [[C I CL _ _ _ _ _ _ _] _ _].
    pose proof (bloop (lz_fuel s) s D B Hlv Hst) as LP.
    assert (FU : lzm s < Z.of_nat (lz_fuel s)).
    { unfold lz_fuel, DeflInvFast.lzm. pose proof (di_look _ _ _ _ I). pose proof (dc_ai _ _ _ _ CL). rewrite Z2Nat.id by lia. lia. }
    specialize (LP FU). destruct (deflate_slow_loop (lz_fuel s) s flush) as [s1 r]. destruct LP as ((A1 & B1 & St1 & Wr1) & EL & ES & R).
    destruct r as [bs|].
    - destruct R as (-> & P1 & _). split; [exact B1|]. split; [exact St1|]. split; [exact Wr1|]. left. split; [reflexivity | exact A1].
    - destruct R as (D1 & L1 & NF). assert (HF : flush = Z_FINISH) by (destruct HFL as [X|X]; [exfalso; exact (NF X) | exact X]).
      pose proof (btail s1 D1 B1 L1 ltac:(rewrite EL; exact Hlv) ltac:(unfold lz_strat; rewrite ES; exact Hst) HF) as TL.
      match goal with |- let '(s', bs) := ?X in _ => destruct X as [s' bs] end.
      destruct TL as (A2 & B2 & St2 & Wr2 & Hbs & SY & MA & BS & LK).
      split; [exact B2|]. split; [congruence|]. split; [congruence|].
      right. split; [exact Hbs|]. split; [exact (ACC_ACCF_trans _ _ _ A1 A2)|]. split; [exact HF|]. split; [exact LK | split; [exact SY | split; [exact MA | exact BS]]].
  Qed.
End TRIP.
