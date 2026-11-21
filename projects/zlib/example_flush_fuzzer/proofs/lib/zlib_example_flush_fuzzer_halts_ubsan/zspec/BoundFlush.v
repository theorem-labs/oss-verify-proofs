(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  DeflateInvHash DeflateInvKeep OverlayFBS OverlayRace OverlayFlush DeflRoom SendModel
  LmatchModel FillWinModel DeflFastModel DeflSlowModel TreesTab
  RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflSlowOk RefDeflateHdrKit RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3 RefDeflateHdr4 RefDeflateHdr5
  DeflateInv DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep DeflInvFbo DeflInvFw DeflInvFast DeflInvSlow DeflInvSlow2 DeflInvCore
  BoundArith BoundTfb BoundInv BoundSlow BoundCore BoundRc.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section TRIP3.
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
  Local Notation ACCF := (ACCF IN0).

  Let KML : MIN_LOOKAHEAD = 262 := eq_refl.
  Let KMM : MIN_MATCH = 3 := eq_refl.

  Definition TAILPOST (s s' : deflate_state) : Prop :=
    ACCF s s' /\ BI s' /\ ds_status s' = ds_status s /\ ds_wrap s' = ds_wrap s
    /\ (forall syms, dsyms syms s' -> syms = []) /\ ds_match_available s' = 0 /\ ds_block_start s' = ds_strstart s' /\ ds_lookahead s' = 0
    /\ ds_match_length s' < MIN_MATCH /\ ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s /\ ds_w_size s' = ds_w_size s.

  Lemma btail3 : forall s, DRUN 3 0 true s -> BI s -> ds_lookahead s = 0 -> 4 <= ds_level s -> lz_strat s ->
    let '(s', bs) :=
      (let s1 := if negb (Z.eqb (ds_match_available s) 0) then
                   let '(s1, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in set_match_available s1 0
                 else s in
       let s2 := set_insert s1 (if Z.ltb (ds_strstart s1) (MIN_MATCH - 1) then ds_strstart s1 else MIN_MATCH - 1) in
       deflate_tail s2 Z_FULL_FLUSH) in
    TAILPOST s s' /\ (bs = need_more \/ bs = block_done).
  Proof.
    intros s D B Hlook Hlv Hst. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl). pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_ma _ _ _ _ I) as Ima.
    destruct (stail_mid_run ws hs PBL ILEN OCAP tot0 s D Hlook Hlv Hst) as (rm & Hrm & MID). cbv zeta in MID.
    assert (S1 : let s1 := (if negb (ds_match_available s =? 0) then
                             let '(s1, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in set_match_available s1 0
                           else s) in
                 Mloc s1 = Mloc s /\ Aof IN0 s1 = Aof IN0 s /\ ds_status s1 = ds_status s /\ ds_wrap s1 = ds_wrap s /\ ds_w_size s1 = ds_w_size s
                 /\ ds_strstart s1 = ds_strstart s /\ ds_block_start s1 = ds_block_start s
                 /\ (forall sy, dsyms sy s1 -> zcov sy = ds_strstart s1 - ds_block_start s1 /\ Forall too_far_ok sy)
                 /\ (ds_match_available s = 0 -> s1 = s)).
    { destruct (Z.eqb_spec (ds_match_available s) 0) as [M0|M0]; cbn [negb].
      - repeat (split; [reflexivity|]). split; [| intros _; reflexivity]. intros sy Dsy. pose proof (bi_cov _ B sy Dsy) as X. rewrite M0 in X. split; [lia | exact (bi_tf _ B sy Dsy)].
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
        repeat (split; [reflexivity|]). split; [| intros X; exfalso; lia].
        intros sy Dsy. assert (Dsy' : dsyms sy s0) by (revert Dsy; apply dsyms_iff; dsr; reflexivity).
        rewrite (dsyms_unique _ _ _ Dsy' Dy0). pose proof (bi_cov _ B syms Dy) as X. rewrite Hma1 in X.
        rewrite zcov_app1. cbn [Z.eqb]. split; [lia|].
        apply Forall_app. split; [exact (bi_tf _ B syms Dy)|]. constructor; [| constructor]. intros X'. exfalso. exact (X' eq_refl). }
    cbv zeta in S1.
    remember (if negb (ds_match_available s =? 0) then let '(s1, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in set_match_available s1 0 else s)
      as s1 eqn:Es1.
    destruct MID as (D1 & L1 & MA1 & EL1 & ES1). destruct S1 as (M1 & A1 & St1 & Wr1 & Ws1 & Str1 & Bs1 & COV1 & ID1).
    cbv zeta.
    remember (set_insert s1 (if ds_strstart s1 <? MIN_MATCH - 1 then ds_strstart s1 else MIN_MATCH - 1)) as s2 eqn:Es2.
    assert (D2 : DRUN rm 0 true s2).
    { subst s2. pose proof D1 as [[C1 I1 CL1 _ _ _ _ _ _ _] _ _].
      eapply drun_relift; [exact D1 | | apply dcfg_set_insert; exact C1 | dsr; reflexivity ..].
      apply dinv_set_insert; [exact I1 |]. dsr. pose proof (di_str _ _ _ _ I1). unfold MIN_MATCH. destruct (Z.ltb_spec (ds_strstart s1) (3 - 1)); lia. }
    assert (F2 : Mloc s2 = Mloc s1 /\ Aof IN0 s2 = Aof IN0 s1 /\ ds_status s2 = ds_status s1 /\ ds_wrap s2 = ds_wrap s1 /\ ds_w_size s2 = ds_w_size s1
                 /\ ds_strstart s2 = ds_strstart s1 /\ ds_block_start s2 = ds_block_start s1 /\ ds_match_available s2 = ds_match_available s1
                 /\ (forall sy, dsyms sy s2 <-> dsyms sy s1)
                 /\ ds_lookahead s2 = ds_lookahead s1 /\ ds_match_length s2 = ds_match_length s1 /\ ds_level s2 = ds_level s1 /\ ds_strategy s2 = ds_strategy s1
                 /\ ds_sym_next s2 = ds_sym_next s1 /\ ds_match_start s2 = ds_match_start s1).
    { subst s2. split; [apply Mloc_frame; dsr; reflexivity|]. split; [apply Aof_frame; dsr; reflexivity|]. dsr. repeat (split; [reflexivity|]).
      split; [apply dsyms_iff; dsr; reflexivity|]. repeat split; reflexivity. }
    destruct F2 as (M2 & A2 & St2 & Wr2 & Ws2 & Str2 & Bs2 & Ma2 & SY2 & Lk2 & Ml2 & Lv2 & Sg2 & Sn2 & Ms2).
    unfold deflate_tail. replace (Z_FULL_FLUSH =? Z_FINISH) with false by reflexivity. cbv iota beta.
    pose proof (di_str _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D2))) as Str2'.
    pose proof (di_bs _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D2))) as Bs2'.
    assert (ML2 : ds_match_length s2 < MIN_MATCH).
    { pose proof (di_slow _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D2)) eq_refl) as SL.
      destruct (Z.lt_ge_cases (ds_match_length s2) MIN_MATCH) as [X|X]; [exact X|]. exfalso.
      destruct (SL ltac:(rewrite Lv2, EL1; exact Hlv) ltac:(unfold lz_strat; rewrite Sg2, ES1; exact Hst) ltac:(lia)) as (_ & _ & Y).
      rewrite Lk2, L1 in Y. unfold MIN_MATCH in X. lia. }
    destruct (Z.eqb_spec (ds_sym_next s2) 0) as [SN0|SN0]; cbn [negb].
    -
      destruct (di_syms _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D2))) as (sy2 & Dy2 & _).
      pose proof (dsyms_nil_of _ _ Dy2 SN0) as D20.
      assert (MA0 : ds_match_available s = 0).
      { destruct (Z.eq_dec (ds_match_available s) 0) as [X|X]; [exact X|]. exfalso.
        assert (D10 : dsyms [] s1) by (apply (proj1 (SY2 [])); exact D20).
        destruct (COV1 [] D10) as [Z0 _]. rewrite zcov_nil in Z0.
        destruct (Z.eqb_spec (ds_match_available s) 0) as [|_]; [lia|]. cbn [negb] in Es1.
        destruct (tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1))) as [s0 bf] eqn:ET.
        pose proof (bi_cov _ B) as CV. destruct (di_syms _ _ _ _ I) as (sy0 & Dy0 & _).
        pose proof (CV sy0 Dy0) as X0. pose proof (zcov_nonneg sy0 (sy_valid _ _ Dy0)). rewrite Str1, Bs1 in Z0. lia. }
      pose proof (ID1 MA0) as ->.
      split; [| right; reflexivity].
      split. { apply (ACC_ACCF ws hs PBL ILEN OCAP tot0 IN0). apply ACC_refl'; [rewrite M2; reflexivity | rewrite A2; reflexivity]. }
      split. { apply (BI_transfer s). 2: exact B. subst s2. constructor; dsr; try reflexivity. apply dsyms_iff; dsr; reflexivity. }
      split; [exact St2|]. split; [exact Wr2|]. split.
      { intros syms Dsy. exact (dsyms_unique _ _ _ Dsy D20). }
      split; [rewrite Ma2; exact MA0|]. split.
      { destruct (COV1 [] ltac:(apply (proj1 (SY2 [])); exact D20)) as [Z0 _]. rewrite zcov_nil in Z0. rewrite Bs2, Str2. lia. }
      split; [rewrite Lk2; exact L1|]. split; [exact ML2|]. split; [exact Lv2|]. split; [exact Sg2 | exact Ws2].
    -
      unfold flush_block. cbv zeta.
      destruct (fbo_cb ws hs PBL ILEN OCAP tot0 TS TR HPBL HWS HLBS rm 0 true s2 0 IN0 Hrm D2 ltac:(left; reflexivity)) as (M3 & A3 & SY3 & P3 & SN3 & BS3 & FR3).
      { intros sy Dsy. apply SY2 in Dsy. rewrite Str2, Bs2. exact (COV1 sy Dsy). }
      { rewrite Bs2, Ws2, Str2, Bs1, Ws1, Str1. exact (bi_nb _ B). }
      cbv zeta in M3, A3, SY3.
      remember (flush_block_only s2 0) as sF eqn:EsF. clear EsF.
      assert (ML : ds_match_length sF < MIN_MATCH) by (rewrite (ff_match_length _ _ FR3); exact ML2).
      assert (POST : TAILPOST s sF).
      { split.
        { apply (ACCF_flush ws hs PBL ILEN OCAP tot0 IN0 s sF (ds_strstart s2 - ds_block_start s2)).
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
        split; [reflexivity|]. split; [reflexivity|]. split; [exact SY3|]. split; [reflexivity|]. split; [exact BS3|].
        rewrite (ff_lookahead _ _ FR3), Lk2, L1. split; [reflexivity|]. split; [exact ML|].
        rewrite (ff_level _ _ FR3), (ff_strategy _ _ FR3), (ff_w_size _ _ FR3), Lv2, Sg2, Ws2, EL1, ES1, Ws1. repeat split; reflexivity. }
      destruct (cs_avail_out (ds_strm sF) =? 0); cbn [negb]; (split; [exact POST|]); [left | right]; reflexivity.
  Qed.

  Theorem bslow3 : forall s, DRUN 3 0 true s -> BI s -> 4 <= ds_level s -> lz_strat s ->
    let '(s', bs) := deflate_slow s Z_FULL_FLUSH in
    ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s /\
    ((bs = need_more /\ ACC s s' /\ BI s' /\ ds_status s' = ds_status s /\ ds_wrap s' = ds_wrap s /\ DPOST s')
     \/ ((bs = need_more \/ bs = block_done) /\ TAILPOST s s')).
  Proof.
    intros s D B Hlv Hst. unfold deflate_slow. pose proof D as [[C I CL Ews _ _ _ _ _ _] _ _].
    pose proof (bloop ws hs PBL ILEN OCAP tot0 TS TR HPBL HWS HLBS IN0 Z_FULL_FLUSH (lz_fuel s) s D B Hlv Hst) as LP.
    assert (FU : lzm s < Z.of_nat (lz_fuel s)).
    { unfold lz_fuel, DeflInvFast.lzm. pose proof (di_look _ _ _ _ I). pose proof (dc_ai _ _ _ _ CL). rewrite Z2Nat.id by lia. lia. }
    specialize (LP FU). destruct (deflate_slow_loop (lz_fuel s) s Z_FULL_FLUSH) as [s1 r]. destruct LP as ((A1 & B1 & St1 & Wr1) & EL & ES & R).
    destruct r as [bs|].
    - destruct R as (-> & P1 & _). split; [exact EL|]. split; [exact ES|]. left.
      split; [reflexivity|]. split; [exact A1|]. split; [exact B1|]. split; [exact St1|]. split; [exact Wr1 | exact P1].
    - destruct R as (D1 & L1 & NF).
      pose proof (btail3 s1 D1 B1 L1 ltac:(rewrite EL; exact Hlv) ltac:(unfold lz_strat; rewrite ES; exact Hst)) as TL.
      match goal with |- let '(s', bs) := ?X in _ => destruct X as [s' bs] end.
      destruct TL as ((A2 & B2 & St2 & Wr2 & SY & MA & BS & LK & ML & Lv2 & Sg2 & Ws2) & Hbs).
      split; [rewrite Lv2; exact EL|]. split; [rewrite Sg2; exact ES|]. right. split; [exact Hbs|].
      split; [exact (ACC_ACCF_trans ws hs PBL ILEN OCAP tot0 _ _ _ _ A1 A2)|]. split; [exact B2|].
      split; [rewrite St2; exact St1|]. split; [rewrite Wr2; exact Wr1|].
      split; [exact SY|]. split; [exact MA|]. split; [exact BS|]. split; [exact LK|]. split; [exact ML|].
      split; [rewrite Lv2; exact EL|]. split; [rewrite Sg2; exact ES|].
      pose proof D1 as [[_ _ _ Ews1 _ _ _ _ _ _] _ _]. rewrite Ws2, Ews1, Ews. reflexivity.
  Qed.
End TRIP3.

Section CORE3.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.
  Hypothesis HWS : ws = 32768.
  Hypothesis HLBS : PBL = 4 * 16384.
  Variable IN0 : Z.

  Let DCORE := dcore ws hs PBL ILEN OCAP tot0.
  Local Notation Phi := (Phi IN0).
  Local Notation Aof := (Aof IN0).
  Local Notation TAILPOST := (TAILPOST IN0).

  Lemma HF16_3 : 0 <= Z_FULL_FLUSH < 16. Proof. unfold Z_FULL_FLUSH; lia. Qed.
  Lemma HF5_3 : Z_FULL_FLUSH <= 5. Proof. unfold Z_FULL_FLUSH; lia. Qed.

  Definition CPOSTK (k : Z) (s s' : deflate_state) : Prop :=
    BI s' /\ CFGX s' /\ Mloc s' - Mloc s <= Phi s' - Phi s + k.
  Lemma CPOSTK_of_SAME : forall s s', SAME IN0 s s' -> CPOSTK 0 s s'.
  Proof. intros s s' (B & C & M & P). split; [exact B | split; [exact C | rewrite M, P; lia]]. Qed.
  Lemma CPOSTK_trans : forall a b x y z, CPOSTK a x y -> CPOSTK b y z -> CPOSTK (a + b) x z.
  Proof. intros a b x y z (_ & _ & M1) (B & C & M2). split; [exact B | split; [exact C | lia]]. Qed.
  Lemma CPOSTK_le : forall a b x y, a <= b -> CPOSTK a x y -> CPOSTK b x y.
  Proof. intros a b x y L (B & C & M). split; [exact B | split; [exact C | lia]]. Qed.

  Lemma dsyms_nil_keep : forall s s', dsyms [] s -> ds_sym_next s' = ds_sym_next s ->
    (forall c, Freq s' TL c = Freq s TL c) -> (forall c, Freq s' TD c = Freq s TD c) -> (forall c, Freq s' TB c = Freq s TB c) ->
    ds_opt_len s' = ds_opt_len s -> ds_static_len s' = ds_static_len s -> dsyms [] s'.
  Proof.
    intros s s' D SN FL FD FB OL SL. destruct D as [N V Di By QL QD QB O St]. constructor.
    - rewrite SN. exact N. - constructor. - constructor.
    - intros i d lc H. destruct i; discriminate H.
    - intros c Hc. rewrite FL. exact (QL c Hc). - intros j Hj. rewrite FD. exact (QD j Hj). - intros j Hj. rewrite FB. exact (QB j Hj).
    - rewrite OL. exact O. - rewrite SL. exact St.
  Qed.

  Lemma tsb00_fields : forall s, 0 <= ds_bi_valid s <= 16 ->
    let s1 := tr_stored_block s None 0 0 in
    ds_pending s1 = ds_pending s + cdiv8 (ds_bi_valid s + 3) + 4 + 0 /\ ds_bi_valid s1 = 0
    /\ ds_strm s1 = ds_strm s /\ ds_sym_next s1 = ds_sym_next s /\ ds_status s1 = ds_status s /\ ds_wrap s1 = ds_wrap s /\ ds_level s1 = ds_level s
    /\ ds_strategy s1 = ds_strategy s /\ ds_lookahead s1 = ds_lookahead s /\ ds_strstart s1 = ds_strstart s /\ ds_block_start s1 = ds_block_start s
    /\ ds_match_available s1 = ds_match_available s /\ ds_match_length s1 = ds_match_length s /\ ds_match_start s1 = ds_match_start s
    /\ ds_w_size s1 = ds_w_size s
    /\ (forall t c, Freq s1 t c = Freq s t c) /\ ds_opt_len s1 = ds_opt_len s /\ ds_static_len s1 = ds_static_len s.
  Proof.
    intros s Hbv. cbv zeta. pose proof (ep_tr_stored_block s None 0 0) as E1.
    destruct (tr_stored_block_acct s None 0 0 Hbv ltac:(left; reflexivity)) as [P1 V1].
    split; [exact P1|]. split; [exact V1|].
    split; [exact (ep_strm _ _ E1)|]. split; [exact (ep_sym_next _ _ E1)|]. split; [exact (ep_status _ _ E1)|]. split; [exact (ep_wrap _ _ E1)|].
    split; [exact (ep_level _ _ E1)|]. split; [exact (ep_strategy _ _ E1)|]. split; [exact (ep_lookahead _ _ E1)|]. split; [exact (ep_strstart _ _ E1)|].
    split; [exact (ep_block_start _ _ E1)|]. split; [exact (ep_match_available _ _ E1)|]. split; [exact (ep_match_length _ _ E1)|].
    split; [exact (ep_match_start _ _ E1)|]. split; [exact (ep_w_size _ _ E1)|].
    split; [intros t c; exact (ep_Freq _ _ t c E1)|]. split; [exact (ep_opt_len _ _ E1) | exact (ep_static_len _ _ E1)].
  Qed.

  Lemma reset_fields : forall s1,
    let s3 := set_insert (set_block_start (set_strstart (clear_hash s1) 0) 0) 0 in
    ds_lookahead (clear_hash s1) = ds_lookahead s1
    /\ ds_strm s3 = ds_strm s1 /\ ds_sym_next s3 = ds_sym_next s1 /\ ds_status s3 = ds_status s1 /\ ds_wrap s3 = ds_wrap s1 /\ ds_level s3 = ds_level s1
    /\ ds_strategy s3 = ds_strategy s1 /\ ds_lookahead s3 = ds_lookahead s1 /\ ds_strstart s3 = 0 /\ ds_block_start s3 = 0
    /\ ds_match_available s3 = ds_match_available s1 /\ ds_match_length s3 = ds_match_length s1 /\ ds_match_start s3 = ds_match_start s1
    /\ ds_w_size s3 = ds_w_size s1 /\ ds_pending s3 = ds_pending s1 /\ ds_bi_valid s3 = ds_bi_valid s1
    /\ (forall t c, Freq s3 t c = Freq s1 t c) /\ ds_opt_len s3 = ds_opt_len s1 /\ ds_static_len s3 = ds_static_len s1.
  Proof. intros s1. destruct s1. cbv zeta. unfold clear_hash, Freq. cbn. repeat split; reflexivity. Qed.

  Lemma bd_pre3_facts : forall s0 s t s6, DCORE s0 -> TAILPOST s0 s -> dcore ws hs PBL ILEN OCAP tot0 s ->
    t = tr_stored_block s None 0 0 -> s6 = set_insert (set_block_start (set_strstart (clear_hash t) 0) 0) 0 ->
    ds_lookahead (clear_hash t) = 0
    /\ BI s6 /\ ds_status s6 = ds_status s /\ ds_wrap s6 = ds_wrap s /\ ds_level s6 = ds_level s /\ ds_strategy s6 = ds_strategy s
    /\ Mloc s6 <= Mloc s + 5 /\ Aof s6 = Aof s /\ ds_strm s6 = ds_strm s /\ ds_sym_next s6 = ds_sym_next s /\ ds_lookahead s6 = 0
    /\ ds_strstart s6 = 0 /\ ds_block_start s6 = 0 /\ 0 <= ds_bi_valid s6 <= 16 /\ 0 <= ds_pending s6 /\ dsyms [] s6.
  Proof.
    intros s0 s t s6 D0 TP D Et Es6. destruct TP as (A & B & St & Wr & SY & MA & BS & LK & ML & Lv & Sg & Ws). pose proof D as [Cf I CL Ews Ehs Epbl].
    pose proof (di_bv _ _ _ _ I) as Hbv. pose proof (di_pend _ _ _ _ I) as Hp.
    destruct (di_syms _ _ _ _ I) as (sy & Dy & _). pose proof (SY sy Dy) as Esy. subst sy.
    pose proof (tsb00_fields s Hbv) as F1. cbv zeta in F1. rewrite <- Et in F1.
    destruct F1 as (P1 & V1 & Sm1 & Sn1 & St1 & Wr1 & Lv1 & Sg1 & Lk1 & Str1 & Bs1 & Ma1 & Ml1 & Ms1 & Ws1 & Fq1 & Ol1 & Sl1).
    assert (D1 : dsyms [] t) by (apply (dsyms_nil_keep s); [exact Dy | exact Sn1 | intros c; apply Fq1 .. | exact Ol1 | exact Sl1]).
    pose proof (reset_fields t) as F3. cbv zeta in F3. rewrite <- Es6 in F3.
    destruct F3 as (LKC & Sm3 & Sn3 & St3 & Wr3 & Lv3 & Sg3 & Lk3 & Str3 & Bs3 & Ma3 & Ml3 & Ms3 & Ws3 & P3 & V3 & Fq3 & Ol3 & Sl3).
    assert (D3 : dsyms [] s6) by (apply (dsyms_nil_keep t); [exact D1 | exact Sn3 | intros c; apply Fq3 .. | exact Ol3 | exact Sl3]).
    split; [rewrite LKC, Lk1; exact LK|].
    split.
    { constructor.
      - intros sy' Dsy. rewrite (dsyms_unique _ _ _ Dsy D3), zcov_nil, Ma3, Ma1, MA, Str3, Bs3. reflexivity.
      - intros sy' Dsy. rewrite (dsyms_unique _ _ _ Dsy D3). constructor.
      - intros X. exfalso. rewrite Ml3, Ml1 in X. lia.
      - intros X. exfalso. rewrite Ml3, Ml1 in X. lia.
      - intros X. exfalso. rewrite Bs3 in X. lia. }
    split; [rewrite St3; exact St1|]. split; [rewrite Wr3; exact Wr1|]. split; [rewrite Lv3; exact Lv1|]. split; [rewrite Sg3; exact Sg1|].
    split. { unfold Mloc. rewrite Sm3, Sm1, P3, P1, V3, V1, cdiv8_0. pose proof (cdiv8_3 (ds_bi_valid s) ltac:(lia)). pose proof (cdiv8_le (ds_bi_valid s) ltac:(lia)). lia. }
    split. { unfold BoundInv.Aof. rewrite Sm3, Sm1, Lk3, Lk1, LK, Str3, Bs3, BS. lia. }
    split; [rewrite Sm3; exact Sm1|]. split; [rewrite Sn3; exact Sn1|]. split; [rewrite Lk3, Lk1; exact LK|]. split; [exact Str3|]. split; [exact Bs3|].
    pose proof (cdiv8_le (ds_bi_valid s + 3) ltac:(lia)). rewrite V3, V1, P3, P1. split; [lia|]. split; [lia | exact D3].
  Qed.

  Lemma dcore_of_drun : forall s, drunR 3 0 true ws hs PBL ILEN OCAP tot0 s -> DCORE s.
  Proof. intros s D. pose proof (dr_post _ _ _ _ _ _ _ _ _ _ D) as P. exact (MkDCORE _ _ _ _ _ _ s (dp_cfg _ _ _ _ _ _ _ _ _ _ P) (dp_inv _ _ _ _ _ _ _ _ _ _ P) (dp_call _ _ _ _ _ _ _ _ _ _ P) (dp_ws _ _ _ _ _ _ _ _ _ _ P) (dp_hs _ _ _ _ _ _ _ _ _ _ P) (dp_pbl _ _ _ _ _ _ _ _ _ _ P)). Qed.

  Lemma blocks_cb3 : forall s, DCORE s -> ds_pending s = 0 -> ds_pending_out s = 0 -> BI s -> CFGX s -> ds_status s = BUSY_STATE ->
    let '(s2, r) := blocks_body s Z_FULL_FLUSH in CPOSTK 10 s s2 /\ ds_status s2 = BUSY_STATE.
  Proof.
    intros s D P0 PO0 B C SB. pose proof D as [Cf I CL Ews Ehs Epbl].
    destruct C as (CL1 & CS & CW & CI).
    assert (LZS : lz_strat s) by (unfold lz_strat, Z_HUFFMAN_ONLY, Z_RLE; rewrite CS; lia).
    pose proof (dcore_drun _ _ _ _ _ _ s D P0 PO0 SB ltac:(lia)) as DR.
    unfold blocks_body, run_compress_func.
    replace (ds_level s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite CS. replace (0 =? Z_HUFFMAN_ONLY) with false by reflexivity. replace (0 =? Z_RLE) with false by reflexivity. cbv iota.
    replace (ds_level s <=? 3) with false by (symmetry; apply Z.leb_gt; lia).
    pose proof (bslow3 ws hs PBL ILEN OCAP tot0 TS TR HPBL HWS HLBS IN0 s DR B ltac:(lia) LZS) as BS.
    destruct (slow_run ws hs PBL ILEN OCAP tot0 TS TR HPBL Z_FULL_FLUSH s DR ltac:(lia) LZS) as [_ BP].
    destruct (deflate_slow s Z_FULL_FLUSH) as [s1 bs]. destruct BS as (EL1 & ES1 & CASES). destruct BP as (P1 & _ & _ & BPC).
    assert (CFG1 : forall s2, ds_level s2 = ds_level s1 -> ds_strategy s2 = ds_strategy s1 -> ds_wrap s2 = ds_wrap s -> ds_status s2 = BUSY_STATE -> CFGX s2).
    { intros s2 Lv Sg W St. unfold CFGX. rewrite Lv, Sg, W, EL1, ES1, St. split; [exact CL1|]. split; [exact CS|]. split; [exact CW | intros X; discriminate X]. }
    assert (X : BI s1 /\ ds_status s1 = ds_status s /\ ds_wrap s1 = ds_wrap s /\ Mloc s1 - Mloc s <= Phi s1 - Phi s + 5).
    { destruct CASES as [(_ & AC & B1 & St1 & Wr1 & _) | (_ & (AC & B1 & St1 & Wr1 & _))].
      - split; [exact B1|]. split; [exact St1|]. split; [exact Wr1|]. destruct AC as [AC _]. unfold Phi. rewrite St1, Wr1.
        generalize dependent (Aof s1 / KBLK); generalize dependent (Aof s / KBLK). intros; lia.
      - split; [exact B1|]. split; [exact St1|]. split; [exact Wr1|]. destruct AC as [AC _]. unfold Phi. rewrite St1, Wr1.
        generalize dependent (Aof s1 / KBLK); generalize dependent (Aof s / KBLK). intros; lia. }
    destruct X as (B1 & St1 & Wr1 & M1).
    destruct bs; cbn [block_state_eqb orb andb].
    -
      destruct (cs_avail_out (ds_strm s1) =? 0).
      + split; [| dsr; rewrite St1; exact SB]. split.
        { apply (BI_transfer s1); [| exact B1]. constructor; dsr; try reflexivity. apply dsyms_iff; dsr; reflexivity. }
        split; [apply CFG1; dsr; [reflexivity | reflexivity | exact Wr1 | rewrite St1; exact SB]|].
        rewrite (Mloc_frame s1 (set_last_flush s1 (-1))) by (dsr; reflexivity). unfold Phi in *. rewrite (Aof_frame IN0 s1 (set_last_flush s1 (-1))) by (dsr; reflexivity).
        dsr. lia.
      + split; [| rewrite St1; exact SB]. split; [exact B1|]. split; [apply CFG1; [reflexivity | reflexivity | exact Wr1 | rewrite St1; exact SB] | lia].
    -
      destruct CASES as [(X & _) | (_ & TP)]; [discriminate X|].
      destruct BPC as (DR1 & SN1 & LK1 & _ & MA1 & _).
      pose proof (dcore_of_drun s1 DR1) as D1.
      replace (Z_FULL_FLUSH =? Z_PARTIAL_FLUSH) with false by reflexivity. replace (negb (Z_FULL_FLUSH =? Z_BLOCK)) with true by reflexivity. replace (Z_FULL_FLUSH =? Z_FULL_FLUSH) with true by reflexivity. cbn iota.
      cbv zeta. remember (tr_stored_block s1 None 0 0) as t eqn:Et.
      remember (set_insert (set_block_start (set_strstart (clear_hash t) 0) 0) 0) as s6 eqn:Es6.
      pose proof (bd_pre3_facts s s1 t s6 D TP D1 Et Es6) as F. clear Et Es6.
      destruct F as [LKC F]. rewrite LKC. cbn [Z.eqb].
      destruct F as (B6 & St6 & Wr6 & Lv6 & Sg6 & M6 & A6 & Sm6 & Sn6 & Lk6 & Str6 & Bs6 & Bv6 & P6 & D6).
      pose proof (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ DR1)) as I1.
      pose proof (di_pop _ _ _ _ I1) as POP1. pose proof (di_pout _ _ _ _ I1) as PO1. pose proof (di_bv _ _ _ _ I1) as BV1.
      pose proof (dc_ao _ _ _ _ (dp_call _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ DR1))) as AO1.
      destruct (bi_flush_M s6 Bv6) as (Y1 & _ & Y2 & Y3).
      pose proof (cdiv8_le (ds_bi_valid s6) ltac:(lia)) as C1. pose proof (cdiv8_le (ds_bi_valid (bi_flush s6)) ltac:(lia)) as C2.
      assert (PB6 : ds_pending s6 <= ds_pending s1 + 7).
      { pose proof M6 as M6'. unfold Mloc in M6'. rewrite Sm6 in M6'. pose proof (cdiv8_le (ds_bi_valid s1) ltac:(lia)). lia. }
      pose proof D1 as [_ _ _ _ _ Epbl1].
      destruct (fp_frame s6 Bv6 ltac:(rewrite Epbl1 in POP1; lia) ltac:(rewrite Sm6; exact AO1)) as (M7 & N7 & A7 & EP7 & Bv7).
      remember (flush_pending s6) as s7 eqn:Es7. clear Es7.
      destruct (ep_spo_fields _ _ _ _ EP7) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13).
      pose proof (ep_spo_bif _ _ _ _ EP7 D6) as F7.
      assert (POST7 : CPOSTK 10 s s7 /\ ds_status s7 = BUSY_STATE).
      { split; [| rewrite R8, St6, St1; exact SB]. split; [exact (BI_transfer _ _ F7 B6)|].
        split; [apply CFG1; [rewrite R10, Lv6; reflexivity | rewrite R11, Sg6; reflexivity | rewrite R9, Wr6; exact Wr1 | rewrite R8, St6, St1; exact SB]|].
        rewrite M7. unfold Phi in *. rewrite (Aof_frame IN0 s6 s7); [| exact N7 | exact R3 | rewrite R1, R2; reflexivity]. rewrite A6, R8, R9, St6, Wr6.
        clear - M1 M6. generalize dependent (Aof s1 / KBLK); generalize dependent (Aof s / KBLK). intros; lia. }
      destruct (cs_avail_out (ds_strm s7) =? 0); [| exact POST7].
      destruct POST7 as ((B7 & C7 & M7') & St7). split; [| dsr; exact St7]. split.
      { apply (BI_transfer s7); [| exact B7]. constructor; dsr; try reflexivity. apply dsyms_iff; dsr; reflexivity. }
      split.
      { destruct C7 as (C71 & C72 & C73 & C74). unfold CFGX. dsr. split; [exact C71|]. split; [exact C72|]. split; [exact C73 | exact C74]. }
      rewrite (Mloc_frame s7 (set_last_flush s7 (-1))) by (dsr; reflexivity). unfold Phi in *. rewrite (Aof_frame IN0 s7 (set_last_flush s7 (-1))) by (dsr; reflexivity).
      dsr. exact M7'.
    - exfalso. destruct CASES as [(X & _) | ([X|X] & _)]; discriminate X.
    - exfalso. destruct CASES as [(X & _) | ([X|X] & _)]; discriminate X.
  Qed.

  Lemma core3_f12 : forall s, DCORE s -> ds_status s = INIT_STATE -> ds_pending s = 0 -> cs_avail_in (ds_strm s) <> 0 -> cs_avail_out (ds_strm s) <> 0 ->
    f1_spec s Z_FULL_FLUSH = None /\ f2_spec s Z_FULL_FLUSH = F2Hdr (set_last_flush s Z_FULL_FLUSH).
  Proof.
    intros s D SI P0 AI AO. split.
    - rewrite (f1_spec_eq Z_FULL_FLUSH s (dcore_status_ok _ _ _ _ _ _ s D) ltac:(unfold Z_FULL_FLUSH; lia)).
      replace (5 <? Z_FULL_FLUSH) with false by reflexivity. rewrite SI. replace ((INIT_STATE =? FINISH_STATE) && negb (Z_FULL_FLUSH =? Z_FINISH)) with false by reflexivity.
      replace (cs_avail_out (ds_strm s) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AO). reflexivity.
    - unfold f2_spec. cbv zeta.
      assert (Ep : ds_pending (set_last_flush s Z_FULL_FLUSH) = 0) by (destruct s; exact P0). rewrite Ep. cbn [Z.eqb negb].
      assert (Ea : cs_avail_in (ds_strm (set_last_flush s Z_FULL_FLUSH)) = cs_avail_in (ds_strm s)) by (destruct s; reflexivity). rewrite Ea.
      replace (cs_avail_in (ds_strm s) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AI). cbn [andb].
      assert (Es : ds_status (set_last_flush s Z_FULL_FLUSH) = INIT_STATE) by (destruct s; exact SI). rewrite Es.
      replace (INIT_STATE =? FINISH_STATE) with false by reflexivity. reflexivity.
  Qed.

  Lemma core3_f3 : forall s1, ds_status s1 = INIT_STATE -> ds_wrap s1 = 1 -> ds_status (flush_pending (zlib_s3_spec s1)) = BUSY_STATE ->
    f3_spec s1 = (let s4 := flush_pending (zlib_s3_spec s1) in
                  if negb (ds_pending s4 =? 0) then (set_last_flush s4 (-1), Some Z_OK) else (s4, None)).
  Proof.
    intros s1 SI1 W11 SB4. unfold f3_spec. rewrite !SI1, !W11. replace ((INIT_STATE =? INIT_STATE) && (1 =? 0)) with false by reflexivity. cbv iota.
    rewrite !SI1. replace (INIT_STATE =? INIT_STATE) with true by reflexivity. cbv iota.
    rewrite deflate_zlib_header_spec. cbv zeta.
    destruct (negb (ds_pending (flush_pending (zlib_s3_spec s1)) =? 0)) eqn:PZ; [reflexivity|].
    rewrite SB4. replace (BUSY_STATE =? GZIP_STATE) with false by reflexivity. reflexivity.
  Qed.
  Theorem core3 : forall s, DCORE s -> BI s -> CFGX s -> ds_status s = INIT_STATE -> ds_pending s = 0 -> ds_pending_out s = 0 ->
    cs_avail_in (ds_strm s) <> 0 -> cs_avail_out (ds_strm s) <> 0 ->
    let s' := fst (deflate_core s Z_FULL_FLUSH) in CPOSTK 10 s s' /\ ds_status s' = BUSY_STATE.
  Proof.
    intros s D B C SI P0 PO0 AI AO. pose proof D as [Cf I CL Ews Ehs Epbl]. pose proof C as (CL1 & CS & CW & CI).
    destruct (core3_f12 s D SI P0 AI AO) as [E1 E2].
    pose proof (f2_inv ws hs PBL ILEN OCAP tot0 HPBL Z_FULL_FLUSH HF16_3 s D HF5_3 AO) as [_ F2]. rewrite E2 in F2. destruct F2 as (Z1 & NF1 & AO1 & _).
    pose proof (SAME_last_flush IN0 s Z_FULL_FLUSH B C) as S1.
    assert (SI1 : ds_status (set_last_flush s Z_FULL_FLUSH) = INIT_STATE) by (destruct s; exact SI).
    rewrite deflate_core_front. unfold front_spec. rewrite E1, E2.
    remember (set_last_flush s Z_FULL_FLUSH) as s1 eqn:Es1. clear Es1.
    destruct S1 as (B1 & C1 & M1 & Ph1). destruct Z1 as (D1 & P1 & PO1).
    pose proof C1 as (_ & _ & _ & CI1). destruct (CI1 SI1) as (_ & W11 & _ & _).
    destruct (zhdr_cb ws hs PBL ILEN OCAP tot0 IN0 s1 D1 B1 C1 P1 SI1) as (B4 & C4 & M4 & Ph4 & St4).
    pose proof (f3_inv ws hs PBL ILEN OCAP tot0 HPBL s1 (conj D1 (conj P1 PO1)) NF1) as (_ & _ & F3).
    rewrite (core3_f3 s1 SI1 W11 St4) in F3 |- *. cbv zeta in F3 |- *.
    remember (flush_pending (zlib_s3_spec s1)) as s4 eqn:Es4. clear Es4.
    assert (K4 : CPOSTK 0 s s4) by (split; [exact B4 | split; [exact C4 | rewrite M4, Ph4, M1, Ph1; lia]]).
    destruct (negb (ds_pending s4 =? 0)) eqn:PZ in F3 |- *; cbn [fst] in F3 |- *.
    -
      pose proof (SAME_last_flush IN0 s4 (-1) B4 C4) as S5. split; [| destruct s4; exact St4].
      apply (CPOSTK_le 0 10); [lia|]. apply (CPOSTK_trans 0 0 s s4); [exact K4 | exact (CPOSTK_of_SAME _ _ S5)].
    -
      destruct F3 as (Z4 & SB4 & _). destruct Z4 as (D4 & P4 & PO4).
      unfold blocks_or_idle.
      replace (blocks_cond s4 Z_FULL_FLUSH) with true
        by (unfold blocks_cond; rewrite SB4; replace (negb (Z_FULL_FLUSH =? Z_NO_FLUSH) && negb (BUSY_STATE =? FINISH_STATE)) with true by reflexivity; rewrite Bool.orb_true_r; reflexivity).
      cbv iota.
      pose proof (blocks_cb3 s4 D4 P4 PO4 B4 C4 SB4) as BB.
      destruct (blocks_body s4 Z_FULL_FLUSH) as [s5 [rc5|]]; cbn [fst]; destruct BB as [K5 St5].
      + split; [| exact St5]. apply (CPOSTK_trans 0 10 s s4 s5 K4 K5).
      + unfold core_tail. replace (negb (Z_FULL_FLUSH =? Z_FINISH)) with true by reflexivity. cbn [fst].
        split; [| exact St5]. apply (CPOSTK_trans 0 10 s s4 s5 K4 K5).
  Qed.
End CORE3.

Section S4.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.

  Lemma HF16_4 : 0 <= Z_FINISH < 16. Proof. unfold Z_FINISH; lia. Qed.
  Lemma HF5_4 : Z_FINISH <= 5. Proof. unfold Z_FINISH; lia. Qed.

  Lemma f3_spec_busy : forall s, ds_status s = BUSY_STATE -> f3_spec s = (s, None).
  Proof.
    intros s SB. unfold f3_spec. rewrite SB. replace ((BUSY_STATE =? INIT_STATE) && (ds_wrap s =? 0)) with false by reflexivity. cbv iota.
    rewrite SB. replace (BUSY_STATE =? INIT_STATE) with false by reflexivity. cbv iota.
    rewrite SB. replace (BUSY_STATE =? GZIP_STATE) with false by reflexivity. reflexivity.
  Qed.

  Theorem core4_status : forall s, dcore ws hs PBL ILEN OCAP tot0 s -> ds_status s = BUSY_STATE -> cs_avail_out (ds_strm s) <> 0 ->
    let s' := fst (deflate_core s Z_FINISH) in ds_status s' = BUSY_STATE \/ ds_status s' = FINISH_STATE.
  Proof.
    intros s D SB AO. cbv zeta.
    rewrite deflate_core_front. unfold front_spec.
    rewrite (f1_spec_eq Z_FINISH s (dcore_status_ok _ _ _ _ _ _ s D) ltac:(unfold Z_FINISH; lia)).
    replace (5 <? Z_FINISH) with false by reflexivity. rewrite SB.
    replace ((BUSY_STATE =? FINISH_STATE) && negb (Z_FINISH =? Z_FINISH)) with false by reflexivity.
    replace (cs_avail_out (ds_strm s) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AO). cbv iota.
    pose proof (f2_inv ws hs PBL ILEN OCAP tot0 HPBL Z_FINISH HF16_4 s D HF5_4 AO) as [_ P2].
    pose proof (f2_rc ws hs PBL ILEN OCAP tot0 Z_FINISH ltac:(right; reflexivity) s D AO
                  ltac:(rewrite SB; intros X; discriminate X) ltac:(intros X; discriminate X)) as R2.
    destruct (f2_spec s Z_FINISH) as [s2 rc2 | s2 | s2].
    - cbn [fst]. destruct R2 as [_ ST2]. left. rewrite ST2. exact SB.
    - destruct P2 as (Z2 & NF2 & AO2 & _). rewrite SB in R2.
      rewrite (f3_spec_busy s2 R2). cbv iota.
      unfold blocks_or_idle. destruct (blocks_cond s2 Z_FINISH); cbv iota.
      + pose proof (cfunc_inv ws hs PBL ILEN OCAP tot0 TS TR HPBL Z_FINISH HF16_4 s2 Z2 R2 HF5_4) as [_ CP].
        unfold blocks_body. destruct (run_compress_func s2 Z_FINISH) as [s1 bs]. destruct CP as (_ & SB1 & _).
        assert (TL : forall x, ds_status x = BUSY_STATE \/ ds_status x = FINISH_STATE ->
                     ds_status (fst (core_tail x Z_FINISH)) = BUSY_STATE \/ ds_status (fst (core_tail x Z_FINISH)) = FINISH_STATE).
        { intros x Hx. unfold core_tail. replace (negb (Z_FINISH =? Z_FINISH)) with false by reflexivity. cbv iota.
          destruct (ds_wrap x <=? 0); cbn [fst]; [exact Hx|]. rewrite trailer_status. exact Hx. }
        destruct bs; cbn [block_state_eqb orb andb].
        * destruct (cs_avail_out (ds_strm s1) =? 0); cbn [fst]; left; rewrite ?status_set_last_flush; exact SB1.
        * replace (Z_FINISH =? Z_PARTIAL_FLUSH) with false by reflexivity. replace (negb (Z_FINISH =? Z_BLOCK)) with true by reflexivity.
          replace (Z_FINISH =? Z_FULL_FLUSH) with false by reflexivity. cbv iota.
          assert (SBt : ds_status (flush_pending (tr_stored_block s1 None 0 0)) = BUSY_STATE).
          { rewrite (proj1 (flush_pending_keeps _)), (ep_status _ _ (ep_tr_stored_block s1 None 0 0)). exact SB1. }
          remember (flush_pending (tr_stored_block s1 None 0 0)) as s6 eqn:E6. clear E6.
          destruct (cs_avail_out (ds_strm s6) =? 0); cbn [fst]; [left; rewrite status_set_last_flush; exact SBt | apply TL; left; exact SBt].
        * destruct (cs_avail_out (ds_strm (set_status s1 FINISH_STATE)) =? 0); cbn [fst]; right; rewrite ?status_set_last_flush; destruct s1; reflexivity.
        * apply TL. right. destruct s1; reflexivity.
      + replace (Z_FINISH =? Z_NO_FLUSH) with false by reflexivity. cbv iota.
        cbv iota. unfold core_tail. replace (negb (Z_FINISH =? Z_FINISH)) with false by reflexivity. cbv iota.
        destruct (ds_wrap s2 <=? 0); cbn [fst]; [left; exact R2|]. rewrite trailer_status. left; exact R2.
    - destruct P2 as (Z2 & SF2 & _). rewrite SB in R2. rewrite R2 in SF2. discriminate SF2.
  Qed.
End S4.

Section S4O.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.
  Hypothesis HWS : ws = 32768.
  Hypothesis HLBS : PBL = 4 * 16384.

  Lemma core4_f12 : forall s, dcore ws hs PBL ILEN OCAP tot0 s -> ds_status s = BUSY_STATE -> ds_pending s = 0 -> cs_avail_in (ds_strm s) <> 0 -> cs_avail_out (ds_strm s) <> 0 ->
    f1_spec s Z_FINISH = None /\ f2_spec s Z_FINISH = F2Hdr (set_last_flush s Z_FINISH).
  Proof.
    intros s D SB P0 AI AO. split.
    - rewrite (f1_spec_eq Z_FINISH s (dcore_status_ok _ _ _ _ _ _ s D) ltac:(unfold Z_FINISH; lia)).
      replace (5 <? Z_FINISH) with false by reflexivity. rewrite SB. replace ((BUSY_STATE =? FINISH_STATE) && negb (Z_FINISH =? Z_FINISH)) with false by reflexivity.
      replace (cs_avail_out (ds_strm s) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AO). reflexivity.
    - unfold f2_spec. cbv zeta.
      assert (Ep : ds_pending (set_last_flush s Z_FINISH) = 0) by (destruct s; exact P0). rewrite Ep. cbn [Z.eqb negb].
      assert (Ea : cs_avail_in (ds_strm (set_last_flush s Z_FINISH)) = cs_avail_in (ds_strm s)) by (destruct s; reflexivity). rewrite Ea.
      replace (cs_avail_in (ds_strm s) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AI). cbn [andb].
      assert (Es : ds_status (set_last_flush s Z_FINISH) = BUSY_STATE) by (destruct s; exact SB). rewrite Es.
      replace (BUSY_STATE =? FINISH_STATE) with false by reflexivity. reflexivity.
  Qed.

  Lemma trailer_out : forall s, ds_wrap s = 1 -> 0 <= ds_bi_valid s <= 16 -> 0 <= ds_pending s -> ds_pending s + 6 < 2 ^ 32 -> 0 <= cs_avail_out (ds_strm s) -> dsyms [] s ->
    let s' := fst (deflate_trailer s) in
    (snd (deflate_trailer s) = Z_STREAM_END -> zlength (cs_out_rev (ds_strm s')) >= zlength (cs_out_rev (ds_strm s)) + 3)
    /\ (snd (deflate_trailer s) = Z_OK -> cs_avail_out (ds_strm s') = 0).
  Proof.
    intros s W1 Hbv Hp HpB Hao D0. unfold deflate_trailer. rewrite W1. replace (1 =? 2) with false by reflexivity. cbv iota beta zeta.
    pose proof (psm_facts ws hs PBL ILEN OCAP tot0 s (wrap32 (Z.shiftr (cs_adler (ds_strm s)) 16)) D0) as X1. cbv zeta in X1.
    remember (putShortMSB s (wrap32 (Z.shiftr (cs_adler (ds_strm s)) 16))) as s1 eqn:Es1. clear Es1.
    destruct X1 as (P1 & V1 & Sm1 & _ & _ & _ & _ & _ & _ & _ & _ & Wr1 & _ & _ & _ & _ & D1 & _).
    pose proof (psm_facts ws hs PBL ILEN OCAP tot0 s1 (Z.land (cs_adler (ds_strm s)) 65535) D1) as X2. cbv zeta in X2.
    remember (putShortMSB s1 (Z.land (cs_adler (ds_strm s)) 65535)) as s2 eqn:Es2. clear Es2.
    destruct X2 as (P2 & V2 & Sm2 & _ & _ & _ & _ & _ & _ & _ & _ & Wr2 & _ & _ & _ & _ & D2 & _).
    destruct (bi_flush_M s2 ltac:(rewrite V2, V1; exact Hbv)) as (Y1 & Y2 & Y3 & Y4).
    pose proof (cdiv8_le (ds_bi_valid s2) ltac:(rewrite V2, V1; lia)) as C1. pose proof (cdiv8_le (ds_bi_valid (bi_flush s2)) ltac:(lia)) as C2.
    assert (PT : ds_pending s + 4 <= ds_pending (bi_flush s2) <= ds_pending s + 6) by (rewrite P2, P1 in Y1, Y4; pose proof (cdiv8_small (ds_bi_valid (bi_flush s2))); lia).
    pose proof (flush_pending_keeps s2) as (_ & _ & _ & WFP & _). rewrite Wr2, Wr1, W1 in WFP.
    rewrite WFP. replace (0 <? 1) with true by reflexivity. cbv iota. cbn [fst snd].
    assert (PW : forall x, ds_pending (set_wrap x (- (1))) = ds_pending x) by (intros x; destruct x; reflexivity).
    assert (SW : forall x, ds_strm (set_wrap x (- (1))) = ds_strm x) by (intros x; destruct x; reflexivity).
    rewrite PW, SW.
    rewrite (flush_pending_eqm s2) by (change (tr_flush_bits s2) with (bi_flush s2); lia).
    change (tr_flush_bits s2) with (bi_flush s2). cbv zeta.
    remember (bi_flush s2) as t eqn:Et. clear Et.
    assert (AOt : cs_avail_out (ds_strm t) = cs_avail_out (ds_strm s)) by (rewrite Y2, Sm2, Sm1; reflexivity).
    assert (ORt : cs_out_rev (ds_strm t) = cs_out_rev (ds_strm s)) by (rewrite Y2, Sm2, Sm1; reflexivity).
    unfold fpm_len. rewrite AOt.
    destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) (ds_pending t)) as [LT|GE].
    -
      destruct (Z.eq_dec (cs_avail_out (ds_strm s)) 0) as [A0|A0].
      + rewrite A0. replace (0 =? 0) with true by reflexivity. cbv iota.
        split; [intros X; exfalso; destruct (Z.eqb_spec (ds_pending t) 0); [lia | discriminate X] | intros _; rewrite AOt; exact A0].
      + replace (cs_avail_out (ds_strm s) =? 0) with false by (symmetry; apply Z.eqb_neq; exact A0). cbv iota.
        pose proof (fpm_post_fields t (cs_avail_out (ds_strm s))) as F. cbv zeta in F. destruct F as (Fp & _ & Fo & Fa & _).
        remember (fpm_post t (cs_avail_out (ds_strm s))) as u eqn:Eu. clear Eu.
        split; [intros X; exfalso; destruct (Z.eqb_spec (ds_pending u) 0); [lia | discriminate X] | intros _; rewrite Fa, AOt; lia].
    -
      destruct (Z.eqb_spec (ds_pending t) 0) as [Pt0|Pt0]; [lia|]. cbv iota.
      pose proof (fpm_post_fields t (ds_pending t)) as F. cbv zeta in F. destruct F as (Fp & _ & Fo & Fa & _).
      remember (fpm_post t (ds_pending t)) as u eqn:Eu. clear Eu.
      split; [| intros X; exfalso; rewrite Fp in X; replace (ds_pending t - ds_pending t =? 0) with true in X by (symmetry; apply Z.eqb_eq; lia); discriminate X].
      intros _. rewrite Fo, zlength_rev_append, arr_slice_length, ORt. lia.
  Qed.

  Lemma HF16_4' : 0 <= Z_FINISH < 16. Proof. unfold Z_FINISH; lia. Qed.
  Lemma HF5_4' : Z_FINISH <= 5. Proof. unfold Z_FINISH; lia. Qed.
  Lemma blocks_cond_true_of : forall X f, ds_status X <> FINISH_STATE -> f <> Z_NO_FLUSH -> blocks_cond X f = true.
  Proof.
    intros X f NS NF. unfold blocks_cond.
    replace (negb (f =? Z_NO_FLUSH)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NF).
    replace (negb (ds_status X =? FINISH_STATE)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NS).
    rewrite Bool.orb_true_r. reflexivity.
  Qed.

  Theorem core4_fin_out : forall s, dcore ws hs PBL ILEN OCAP tot0 s -> BI s -> CFGX s -> ds_status s = BUSY_STATE ->
    ds_pending s = 0 -> cs_avail_in (ds_strm s) <> 0 -> cs_avail_out (ds_strm s) <> 0 -> cs_out_rev (ds_strm s) = [] ->
    let s' := fst (deflate_core s Z_FINISH) in
    ds_status s' = FINISH_STATE -> cs_avail_out (ds_strm s') = 0 \/ 3 <= zlength (cs_out_rev (ds_strm s')).
  Proof.
    intros s D B C SB P0 AI AO OUT0. cbv zeta. pose proof D as [Cf I CL Ews Ehs Epbl]. pose proof C as (CL1 & CS & CW & CI).
    assert (W1 : ds_wrap s = 1).
    { destruct CW as [X|X]; [exact X|]. exfalso.
      pose proof (di_negwrap _ _ _ _ I) as NW. rewrite X, SB in NW. destruct (NW ltac:(lia)) as [Y _]. discriminate Y. }
    destruct (core4_f12 s D SB P0 AI AO) as [E1 E2].
    pose proof (f2_inv ws hs PBL ILEN OCAP tot0 HPBL Z_FINISH HF16_4' s D HF5_4' AO) as [_ F2]. rewrite E2 in F2. destruct F2 as (Z1 & _ & AO1 & _).
    rewrite deflate_core_front. unfold front_spec. rewrite E1, E2.
    assert (SB1 : ds_status (set_last_flush s Z_FINISH) = BUSY_STATE) by (destruct s; exact SB).
    assert (WR1 : ds_wrap (set_last_flush s Z_FINISH) = ds_wrap s) by (destruct s; reflexivity).
    assert (LV1 : ds_level (set_last_flush s Z_FINISH) = ds_level s /\ ds_strategy (set_last_flush s Z_FINISH) = ds_strategy s
                  /\ cs_out_rev (ds_strm (set_last_flush s Z_FINISH)) = cs_out_rev (ds_strm s)) by (destruct s; repeat split; reflexivity).
    destruct LV1 as (LV1 & SG1 & OR1). rewrite OUT0 in OR1. rewrite W1 in WR1.
    assert (B1 : BI (set_last_flush s Z_FINISH)) by (apply (BI_transfer s); [| exact B]; constructor; dsr; try reflexivity; apply dsyms_iff; dsr; reflexivity).
    remember (set_last_flush s Z_FINISH) as s1 eqn:Es1. clear Es1.
    rewrite (f3_spec_busy s1 SB1). cbv iota.
    unfold blocks_or_idle. rewrite (blocks_cond_true_of s1 Z_FINISH ltac:(rewrite SB1; discriminate) ltac:(discriminate)). cbv iota.
    destruct Z1 as (D1 & P1 & PO1).
    pose proof (dcore_drun _ _ _ _ _ _ s1 D1 P1 PO1 SB1 ltac:(rewrite LV1; lia)) as DR1.
    assert (LZ1 : lz_strat s1) by (unfold lz_strat, Z_HUFFMAN_ONLY, Z_RLE; rewrite SG1, CS; lia).
    unfold blocks_body, run_compress_func.
    replace (ds_level s1 =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite LV1; lia).
    rewrite SG1, CS. replace (0 =? Z_HUFFMAN_ONLY) with false by reflexivity. replace (0 =? Z_RLE) with false by reflexivity. cbv iota.
    replace (ds_level s1 <=? 3) with false by (symmetry; apply Z.leb_gt; rewrite LV1; lia).
    destruct (slow_run ws hs PBL ILEN OCAP tot0 TS TR HPBL Z_FINISH s1 DR1 ltac:(rewrite LV1; lia) LZ1) as [_ BP].
    pose proof (bslow ws hs PBL ILEN OCAP tot0 TS TR HPBL HWS HLBS 0 Z_FINISH ltac:(right; reflexivity) s1 DR1 B1 ltac:(rewrite LV1; lia) LZ1) as BS.
    destruct (deflate_slow s1 Z_FINISH) as [s2 bs]. destruct BP as (P2 & EL2 & ES2 & BPC). destruct BS as (_ & _ & Wr2 & _). rewrite WR1 in Wr2.
    pose proof (dp_status _ _ _ _ _ _ _ _ _ _ P2) as SB2.
    destruct bs; cbn [block_state_eqb orb andb].
    -
      destruct (cs_avail_out (ds_strm s2) =? 0); cbn [fst]; rewrite ?status_set_last_flush; rewrite SB2; intros X; discriminate X.
    -
      exfalso. destruct BPC as (_ & _ & _ & NF & _). exact (NF eq_refl).
    -
      destruct BPC as (_ & _ & _ & AO2).
      destruct (cs_avail_out (ds_strm (set_status s2 FINISH_STATE)) =? 0); cbn [fst]; intros _; left.
      + destruct s2; exact AO2.
      + destruct s2; exact AO2.
    -
      unfold core_tail. replace (negb (Z_FINISH =? Z_FINISH)) with false by reflexivity. cbv iota.
      destruct BPC as (DR2 & SN2 & LK2 & _ & MA2).
      pose proof (dp_inv _ _ _ _ _ _ _ _ _ _ P2) as I2. pose proof (dr_pend _ _ _ _ _ _ _ _ _ _ DR2) as Pd2.
      pose proof (di_bv _ _ _ _ I2) as BV2. pose proof (dc_ao _ _ _ _ (dp_call _ _ _ _ _ _ _ _ _ _ P2)) as AO2.
      destruct (di_syms _ _ _ _ I2) as (sy2 & Dy2 & _). pose proof (dsyms_nil_of _ _ Dy2 SN2) as D20.
      assert (F3 : ds_wrap (set_status s2 FINISH_STATE) = ds_wrap s2 /\ ds_bi_valid (set_status s2 FINISH_STATE) = ds_bi_valid s2
                   /\ ds_pending (set_status s2 FINISH_STATE) = ds_pending s2 /\ ds_strm (set_status s2 FINISH_STATE) = ds_strm s2).
      { dsr. repeat split; reflexivity. }
      assert (D3 : dsyms [] (set_status s2 FINISH_STATE)).
      { apply (proj2 (dsyms_iff s2 (set_status s2 FINISH_STATE) ltac:(dsr; reflexivity) ltac:(dsr; reflexivity) ltac:(dsr; reflexivity) ltac:(dsr; reflexivity)
                 ltac:(dsr; reflexivity) ltac:(dsr; reflexivity) ltac:(dsr; reflexivity) ltac:(dsr; reflexivity) ltac:(dsr; reflexivity) [])). exact D20. }
      remember (set_status s2 FINISH_STATE) as s3 eqn:Es3. clear Es3.
      destruct F3 as (W3 & BV3 & P3 & Sm3). rewrite Wr2 in W3. rewrite Pd2 in P3.
      replace (ds_wrap s3 <=? 0) with false by (rewrite W3; reflexivity).
      destruct (trailer_out s3 W3 ltac:(rewrite BV3; exact BV2) ltac:(lia) ltac:(lia) ltac:(rewrite Sm3; exact AO2) D3) as [T1 T2].
      intros _. destruct (trailer_rc s3) as [RO|RE].
      + left. exact (T2 RO).
      + right. pose proof (T1 RE) as X. rewrite Sm3 in X. pose proof (zlength_nonneg (cs_out_rev (ds_strm s2))). lia.
  Qed.
End S4O.

Section P3.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.
  Hypothesis HWS : ws = 32768.
  Hypothesis HLBS : PBL = 4 * 16384.
  Variable IN0 : Z.

  Theorem core3_pend : forall s, dcore ws hs PBL ILEN OCAP tot0 s -> BI s -> CFGX s -> ds_status s = INIT_STATE -> ds_pending s = 0 -> ds_pending_out s = 0 ->
    cs_avail_in (ds_strm s) <> 0 -> cs_avail_out (ds_strm s) <> 0 ->
    let s' := fst (deflate_core s Z_FULL_FLUSH) in
    cs_avail_out (ds_strm s') <> 0 -> ds_pending s' = 0 /\ ds_pending_out s' = 0.
  Proof.
    intros s D B C SI P0 PO0 AI AO. cbv zeta. pose proof D as [Cf I CL Ews Ehs Epbl]. pose proof C as (CL1 & CS & CW & CI).
    destruct (core3_f12 ws hs PBL ILEN OCAP tot0 s D SI P0 AI AO) as [E1 E2].
    pose proof (f2_inv ws hs PBL ILEN OCAP tot0 HPBL Z_FULL_FLUSH HF16_3 s D HF5_3 AO) as [_ F2].
    rewrite E2 in F2. destruct F2 as (Z1 & NF1 & AO1 & _).
    pose proof (SAME_last_flush IN0 s Z_FULL_FLUSH B C) as S1.
    assert (SI1 : ds_status (set_last_flush s Z_FULL_FLUSH) = INIT_STATE) by (destruct s; exact SI).
    rewrite deflate_core_front. unfold front_spec. rewrite E1, E2.
    remember (set_last_flush s Z_FULL_FLUSH) as s1 eqn:Es1. clear Es1.
    destruct S1 as (B1 & C1 & M1 & Ph1). destruct Z1 as (D1 & P1 & PO1).
    pose proof C1 as (_ & _ & _ & CI1). destruct (CI1 SI1) as (_ & W11 & _ & _).
    destruct (zhdr_cb ws hs PBL ILEN OCAP tot0 IN0 s1 D1 B1 C1 P1 SI1) as (B4 & C4 & M4 & Ph4 & St4).
    pose proof (f3_inv ws hs PBL ILEN OCAP tot0 HPBL s1 (conj D1 (conj P1 PO1)) NF1) as (_ & _ & F3).
    rewrite (core3_f3 s1 SI1 W11 St4) in F3 |- *. cbv zeta in F3 |- *.
    remember (flush_pending (zlib_s3_spec s1)) as s4 eqn:Es4. clear Es4.
    destruct (negb (ds_pending s4 =? 0)) eqn:PZ in F3 |- *; cbn [fst] in F3 |- *.
    - destruct F3 as (_ & _ & A4). intros X. exfalso. apply X. destruct s4; exact A4.
    - destruct F3 as (Z4 & SB4 & _). pose proof Z4 as (D4 & P4 & PO4).
      unfold blocks_or_idle.
      replace (blocks_cond s4 Z_FULL_FLUSH) with true
        by (unfold blocks_cond; rewrite SB4; replace (negb (Z_FULL_FLUSH =? Z_NO_FLUSH) && negb (BUSY_STATE =? FINISH_STATE)) with true by reflexivity; rewrite Bool.orb_true_r; reflexivity).
      cbv iota.
      destruct (blocks_inv ws hs PBL ILEN OCAP tot0 TS TR HPBL Z_FULL_FLUSH HF16_3 s4 Z4 SB4 HF5_3) as [_ BP].
      destruct (cfunc_inv ws hs PBL ILEN OCAP tot0 TS TR HPBL Z_FULL_FLUSH HF16_3 s4 Z4 SB4 HF5_3) as [_ CP].
      revert BP. unfold blocks_body. destruct (run_compress_func s4 Z_FULL_FLUSH) as [s5 bs]. destruct CP as (_ & SB5 & PF5 & R5).
      destruct bs; cbn [block_state_eqb orb andb].
      + destruct (Z.eqb_spec (cs_avail_out (ds_strm s5)) 0) as [A0|A0]; cbn [fst].
        * intros _ X. exfalso. apply X. destruct s5; exact A0.
        * intros _ _. exact (PF5 A0).
      + replace (Z_FULL_FLUSH =? Z_PARTIAL_FLUSH) with false by reflexivity. replace (negb (Z_FULL_FLUSH =? Z_BLOCK)) with true by reflexivity.
        replace (Z_FULL_FLUSH =? Z_FULL_FLUSH) with true by reflexivity. cbv iota. cbv zeta.
        match goal with |- context [flush_pending ?X] => remember (flush_pending X) as s7 eqn:Es7; clear Es7 end.
        destruct (Z.eqb_spec (cs_avail_out (ds_strm s7)) 0) as [A0|A0]; cbn [fst].
        * intros _ X. exfalso. apply X. destruct s7; exact A0.
        * intros [_ BP]. unfold core_tail. replace (negb (Z_FULL_FLUSH =? Z_FINISH)) with true by reflexivity. cbn [fst].
          intros _. destruct BP as (P7 & PO7 & _). split; [exact P7 | exact PO7].
      + exfalso. destruct R5 as (_ & _ & F & _). cbv in F. discriminate F.
      + exfalso. destruct R5 as (_ & _ & _ & _ & F). cbv in F. discriminate F.
  Qed.
End P3.
