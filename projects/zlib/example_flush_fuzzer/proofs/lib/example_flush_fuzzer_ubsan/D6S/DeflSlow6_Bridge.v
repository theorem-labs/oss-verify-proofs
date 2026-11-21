(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel DeflFastModel DeflSlowModel
  DeflateInvHash DeflateInvKeep OverlayFBS DeflRoom RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflSlowOk
  DeflateInv DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep DeflInvFbo DeflInvFw DeflInvFast DeflInvSlow DeflInvSlow2 DeflInvMain DeflInvWk FB6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import DeflSlow6_2 DeflSlow6_3 DeflSlow6_5 DeflSlow6_7 DeflSlow6_M.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma strip_inv_of_dpost : forall rm hb fz ws hs PBL ILEN OCAP tot0 s, 0 <= rm ->
  dpostR rm hb fz ws hs PBL ILEN OCAP tot0 s -> strip_inv s.
Proof.
  intros rm hb fz ws hs PBL ILEN OCAP tot0 s Hrm P. pose proof P as [C I CL Ews Ehs Epbl _ _ _ _].
  pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl). pose proof (dinv_lzw rm hb fz s Hrm C I) as LZ.
  pose proof (di_cty _ _ _ _ I) as CT.
  constructor.
  - exact (di_str _ _ _ _ I).
  - exact (di_sl _ _ _ _ I).
  - exact (di_look _ _ _ _ I).
  - pose proof (di_ih _ _ _ _ I). lia.
  - exact (cf_hmask _ C).
  - exact (cf_wmask _ C).
  - exact (lz_hsh _ LZ).
  - pose proof (di_ml _ _ _ _ I) as X. unfold MAX_MATCH in X. lia.
  - exact (di_ms _ _ _ _ I).
  - pose proof (di_pl _ _ _ _ I) as X. unfold MAX_MATCH in X. lia.
  - exact (di_pm _ _ _ _ I).
  - pose proof (di_ma _ _ _ _ I). lia.
  - exact (cf_strategy _ C).
  - exact (lz_mlz _ LZ).
  - pose proof (lz_sn _ LZ) as X. rewrite (cf_symend _ C) in X. lia.
  - rewrite (cf_symend _ C). lia.
  - intros j Hj. apply (ct_win _ CT). rewrite (cf_wl _ C). exact Hj.
  - intros j Hj. apply (ct_head _ CT). rewrite (cf_hl _ C). exact Hj.
  - intros j Hj. apply (ct_prev _ CT). rewrite (cf_pl _ C). exact Hj.
  - exact (cf_hl _ C).
  - intros i Hi. apply (ct_lfc _ CT). destruct (cf_tl _ C) as (L1 & _). rewrite L1. exact Hi.
  - intros i Hi. apply (ct_dfc _ CT). destruct (cf_tl _ C) as (_ & _ & L3 & _). rewrite L3. exact Hi.
Qed.


Lemma strstart_tfb : forall s buf len last, ds_strstart (tr_flush_block s buf len last) = ds_strstart s.
Proof.
  intros. pose proof (kp_strstart _ _ (kp_tr_flush_block s buf len last)) as E. rewrite E. destruct s; reflexivity.
Qed.

Section FOK.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis HPBL : 2048 <= PBL.

  Lemma flush_ok6_of_drun : forall rm hb fz s last, 0 <= rm ->
    drunR rm hb fz ws hs PBL ILEN OCAP tot0 s -> (last = 0 \/ last = 1) -> flush_ok6 FB6 s last.
  Proof.
    intros rm hb fz s last Hrm D Hl.
    pose proof (FB6_of_drun rm hb fz ws hs PBL ILEN OCAP tot0 s last Hrm HPBL D Hl) as F6.
    pose proof (fbo_run ws hs PBL ILEN OCAP tot0 tfb_safe_holds tfb_room_holds HPBL rm hb fz s last Hrm D Hl) as [OK _].
    pose proof D as [P P0 PO0]. pose proof (drun_span _ _ _ _ _ _ _ _ _ s Hrm P) as (SP & STR & EL & EB).
    pose proof P as [C I CL Ews Ehs Epbl _ _ _ _]. pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    destruct OK as (LZ & BS & TFB & POST). destruct TFB as (B & FS & K & L32 & BUF). cbv zeta in POST. destruct POST as (STR1 & FP & AO).
    unfold flush_ok6. cbv zeta. fold (fbo_buf s). fold (fbo_len s). rewrite Epbl.
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_look _ _ _ _ I) as Ilk.
    split; [exact F6|]. split; [exact B|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [intros j Hj; apply (ct_win _ (di_cty _ _ _ _ I)); rewrite (cf_wl _ C); exact Hj|].
    split; [rewrite strstart_tfb; lia|].
    unfold fp_ok in FP. cbv zeta in FP. fold (fbo_buf s) in FP. fold (fbo_len s) in FP.
    destruct FP as (B2 & PD & PO & POP & AOR & OUT & TOT & PBB).
    split; [exact B2|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [| exact TOT].
    unfold DeflM.fp_len. rewrite wrap32_id by lia. match goal with |- context [cs_avail_out ?st <? ds_pending ?x] => destruct (Z.ltb_spec (cs_avail_out st) (ds_pending x)); lia end.
  Qed.
End FOK.


Lemma prev_st_a3 : forall s2,
  prev_st s2 = set_match_length (set_prev_match (set_prev_length s2 (ds_match_length s2)) (ds_match_start (set_prev_length s2 (ds_match_length s2)))) (MIN_MATCH - 1).
Proof. intros s2. symmetry. apply prev_st_eq. Qed.

Lemma slow_front_kit : forall s1, slow_front s1 = st_lm (prev_st (fst (st_hash s1))) (snd (st_hash s1)).
Proof.
  intros s1. unfold slow_front, st_hash. destruct (if MIN_MATCH <=? ds_lookahead s1 then _ else _) as [s2 hh]. cbn [fst snd].
  unfold slow_front2. cbv zeta. rewrite <- prev_st_a3. generalize (prev_st s2); intros s3.
  unfold st_lm, sl_lm_cond, sl_filter, NIL, Z_FILTERED, TOO_FAR, MIN_MATCH. rewrite MIN_LOOKAHEAD_eq.
  destruct (negb (hh =? 0) && _ && _); [| reflexivity].
  destruct (longest_match s3 hh) as [s4 ml]. cbn [fst snd]. reflexivity.
Qed.

Lemma st_sdist_a3 : forall s,
  st_sdist s
  = (let max_insert := wrap32 (ds_strstart s + ds_lookahead s - MIN_MATCH) in
     let '(s5, bflush) := tr_tally_dist s (wrap32 (ds_strstart s - 1 - ds_prev_match s)) (ds_prev_length s - MIN_MATCH) in
     let s6 := set_lookahead s5 (wrap32 (ds_lookahead s5 - (ds_prev_length s5 - 1))) in
     let s7 := set_prev_length s6 (ds_prev_length s6 - 2) in
     let s8 := deflate_slow_insert (Z.to_nat (ds_prev_length s7)) s7 max_insert in
     let s9 := set_match_available s8 0 in let s10 := set_match_length s9 (MIN_MATCH - 1) in
     let s11 := set_strstart s10 (ds_strstart s10 + 1) in
     (s11, bflush)).
Proof. intros s. unfold st_sdist, MIN_MATCH. reflexivity. Qed.


Section TRIP.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis HPBL : 2048 <= PBL.
  Variable flush : Z.
  Hypothesis Hflush : 0 <= flush <= 5.

  Let DRUN rm hb fz := drunR rm hb fz ws hs PBL ILEN OCAP tot0.
  Let KML : MIN_LOOKAHEAD = 262 := eq_refl.
  Let KMM : MIN_MATCH = 3 := eq_refl.

  Local Notation flush_ok := (flush_ok6 FB6).

  Lemma lm_ok6_of : forall s3 hh, dcfg s3 -> lzw s3 -> lm_pre s3 hh -> 0 <= hh < 65536 ->
    (let '(s4, ml) := longest_match s3 hh in lzw (set_match_length s4 ml)) -> lm_ok6 s3 hh.
  Proof.
    intros s3 hh C LZ PRE Hhh ML. pose proof (dcfg_sizes s3 C) as (Sw & _).
    destruct PRE as (Hcur & Hch & VIS & (Sstr & S258 & _) & (Wm & _) & Ppl & Pnice & Plook & Pgood & Pchain & Pws).
    rewrite (cf_wl _ C) in S258.
    unfold lm_ok6. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    - intros i Hi. apply (lz_wb _ LZ). rewrite (cf_wl _ C). exact Hi.
    - intros i Hi. apply (lz_pb _ LZ). rewrite (cf_pl _ C). exact Hi.
    - exact (cf_wmask _ C).
    - destruct (longest_match s3 hh) as [s4 ml]. cbn [snd]. pose proof (lz_ml _ ML) as X. revert X. destruct s4; cbn. unfold MAX_MATCH. lia.
    - destruct (longest_match s3 hh) as [s4 ml]. cbn [snd]. pose proof (lz_ml _ ML) as X. revert X. destruct s4; cbn. unfold MAX_MATCH. lia.
  Qed.

  Lemma sdec_ok_of : forall s4, DRUN 3 1 false s4 -> 1 <= ds_lookahead s4 ->
    (MIN_MATCH <= ds_prev_length s4 ->
       1 <= ds_strstart s4 /\ 1 <= wrap32 (ds_strstart s4 - 1 - ds_prev_match s4) <= ds_w_size s4 - MIN_LOOKAHEAD
       /\ ds_prev_length s4 <= ds_lookahead s4 + 1) ->
    (MIN_MATCH <= ds_match_length s4 -> ds_match_length s4 <= ds_prev_length s4
       \/ (1 <= ds_strstart s4 - ds_match_start s4 <= ds_w_size s4 - MIN_LOOKAHEAD /\ ds_match_length s4 <= ds_lookahead s4)) ->
    4 <= ds_level s4 -> lz_strat s4 ->
    sdec_ok FB6 ws s4.
  Proof.
    intros s4 D4 Hlook T1 SF Hlv Hst. pose proof D4 as [P4 _ _]. pose proof P4 as [C I CL Ews Ehs Epbl _ _ _ _].
    pose proof (dcfg_sizes s4 C) as (Sw & Sh & Sl & Shl).
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_ma _ _ _ _ I) as Ima.
    unfold sdec_ok. split; [exact (strip_inv_of_dpost 3 1 false ws hs PBL ILEN OCAP tot0 s4 ltac:(lia) P4)|].
    split; [rewrite <- Ews; lia|].
    unfold dist_cond. destruct (Z.leb_spec 3 (ds_prev_length s4)) as [Hpl|Hpl]; [destruct (Z.leb_spec (ds_match_length s4) (ds_prev_length s4)) as [Hml|Hml]|]; cbn [andb].
    -
      destruct (T1 ltac:(rewrite KMM; exact Hpl)) as (Hs1 & HD & Hpll). rewrite KML in HD.
      unfold sdist_ok. split; [lia|]. split; [lia|]. split.
      { unfold sdist_D. replace (ds_strstart s4 - ds_prev_match s4 + -2) with (ds_strstart s4 - 1 - ds_prev_match s4 - 1) by lia.
        change (2 ^ 16) with 65536. rewrite dist1_mod16 by lia. lia. }
      rewrite st_sdist_a3.
      pose proof (smatch_mid_run ws hs PBL ILEN OCAP tot0 s4 D4
                    ltac:(rewrite KMM; exact Hpl) Hml Hs1 ltac:(rewrite KML; exact HD) Hpll Hlv Hst) as MR.
      cbv zeta in MR |- *. destruct (tr_tally_dist s4 _ _) as [s5 b]. cbn [fst snd]. intros Hb. subst b.
      destruct MR as (D11 & _). exact (flush_ok6_of_drun ws hs PBL ILEN OCAP tot0 HPBL 0 0 true _ 0 ltac:(lia) D11 (or_introl eq_refl)).
    -
      destruct (Z.eqb_spec (ds_match_available s4) 0) as [Ma|Ma]; cbn [negb]; [exact Logic.I|].
      assert (Ma1 : ds_match_available s4 = 1) by lia.
      unfold slit_ok6. split; [exact (di_ma1 _ _ _ _ I Ma1 ltac:(lia))|].
      destruct (slit_tally_eq s4) as [E1 E2].
      pose proof (slit_mid_run ws hs PBL ILEN OCAP tot0 1 s4 ltac:(lia) D4
                    ltac:(intros A B; rewrite KMM in A; lia) Ma Hlook Hlv Hst SF) as MR.
      destruct (tr_tally_lit s4 _) as [s1 b]. cbn [fst snd] in E1, E2. subst s1 b. destruct MR as [D1 LF].
      split.
      { intros Hb. rewrite Hb in D1. exact (flush_ok6_of_drun ws hs PBL ILEN OCAP tot0 HPBL 0 1 false _ 0 ltac:(lia) D1 (or_introl eq_refl)). }
      pose proof (kp_tr_tally_lit s4 (arr_get (ds_window s4) (ds_strstart s4 - 1))) as K1.
      destruct (slit_tally_eq s4) as [E1' _]. rewrite E1' in K1.
      pose proof (kp_strstart _ _ K1) as Kstr. pose proof (kp_lookahead _ _ K1) as Klk. cbn [ds_strstart ds_lookahead set_sym_next] in Kstr, Klk.
      cbv zeta. destruct (ds_sym_next s4 + 3 =? ds_sym_end s4).
      + pose proof (fbo_run ws hs PBL ILEN OCAP tot0 tfb_safe_holds tfb_room_holds HPBL 0 1 false (slit1 s4) 0 ltac:(lia) D1 (or_introl eq_refl)) as [_ X].
        cbv zeta in X. destruct X as (_ & _ & _ & FF). rewrite (ff_strstart _ _ FF), (ff_lookahead _ _ FF), Kstr, Klk, <- Ews. lia.
      + rewrite Kstr, Klk, <- Ews. lia.
    - destruct (Z.eqb_spec (ds_match_available s4) 0) as [Ma|Ma]; cbn [negb]; [exact Logic.I|].
      assert (Ma1 : ds_match_available s4 = 1) by lia.
      unfold slit_ok6. split; [exact (di_ma1 _ _ _ _ I Ma1 ltac:(lia))|].
      destruct (slit_tally_eq s4) as [E1 E2].
      pose proof (slit_mid_run ws hs PBL ILEN OCAP tot0 1 s4 ltac:(lia) D4
                    ltac:(intros A B; rewrite KMM in A; lia) Ma Hlook Hlv Hst SF) as MR.
      destruct (tr_tally_lit s4 _) as [s1 b]. cbn [fst snd] in E1, E2. subst s1 b. destruct MR as [D1 LF].
      split.
      { intros Hb. rewrite Hb in D1. exact (flush_ok6_of_drun ws hs PBL ILEN OCAP tot0 HPBL 0 1 false _ 0 ltac:(lia) D1 (or_introl eq_refl)). }
      pose proof (kp_tr_tally_lit s4 (arr_get (ds_window s4) (ds_strstart s4 - 1))) as K1.
      destruct (slit_tally_eq s4) as [E1' _]. rewrite E1' in K1.
      pose proof (kp_strstart _ _ K1) as Kstr. pose proof (kp_lookahead _ _ K1) as Klk. cbn [ds_strstart ds_lookahead set_sym_next] in Kstr, Klk.
      cbv zeta. destruct (ds_sym_next s4 + 3 =? ds_sym_end s4).
      + pose proof (fbo_run ws hs PBL ILEN OCAP tot0 tfb_safe_holds tfb_room_holds HPBL 0 1 false (slit1 s4) 0 ltac:(lia) D1 (or_introl eq_refl)) as [_ X].
        cbv zeta in X. destruct X as (_ & _ & _ & FF). rewrite (ff_strstart _ _ FF), (ff_lookahead _ _ FF), Kstr, Klk, <- Ews. lia.
      + rewrite Kstr, Klk, <- Ews. lia.
  Qed.

  Lemma shash_ok_of : forall s1, DRUN 3 0 true s1 -> 1 <= ds_lookahead s1 -> ds_strstart s1 + MIN_LOOKAHEAD <= 2 * ds_w_size s1 ->
    4 <= ds_level s1 -> lz_strat s1 -> shash_ok FB6 ws s1.
  Proof.
    intros s1 D1 Hlook Hstr Hlv Hst. pose proof D1 as [P1 _ _]. pose proof P1 as [C I CL Ews Ehs Epbl _ _ _ _].
    pose proof (dcfg_sizes s1 C) as (Sw & Sh & Sl & Shl). pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_str _ _ _ _ I) as Istr.
    unfold shash_ok. split; [exact (strip_inv_of_dpost 3 0 true ws hs PBL ILEN OCAP tot0 s1 ltac:(lia) P1)|].
    split; [rewrite <- Ews; lia|].
    rewrite <- slow_front_kit.
    split.
    -
      destruct (sp1_run ws hs PBL ILEN OCAP tot0 tfb_safe_holds tfb_room_holds HPBL flush (DeflInvFast.lzm s1) s1 D1 Hlook Hstr Hlv Hst ltac:(lia)) as [SP1 _].
      unfold sp1_ok in SP1. destruct SP1 as (LZ1 & _ & SP2).
      unfold st_hash.
      assert (H2 : let '(s2, hh) := (if MIN_MATCH <=? ds_lookahead s1 then insert_string s1 (ds_strstart s1) else (s1, NIL)) in
                   dcfg s2 /\ 0 <= hh < 65536).
      { destruct (Z.leb_spec MIN_MATCH (ds_lookahead s1)) as [L3|L3]; [| split; [exact C | unfold NIL; lia]].
        pose proof (dinv_insert_string 3 true s1 C I L3) as INS. pose proof (dcfg_insert_string s1 (ds_strstart s1) C) as C2.
        destruct (insert_string s1 (ds_strstart s1)) as [s2 hh]. cbn [fst] in C2. destruct INS as (_ & Hhh & _). split; [exact C2 | exact Hhh]. }
      destruct (if MIN_MATCH <=? ds_lookahead s1 then _ else _) as [s2 hh]. cbn [fst snd]. destruct H2 as [C2 Hhh].
      destruct SP2 as [LZ2 SP2]. unfold sp2_ok in SP2. cbv zeta in SP2. rewrite <- prev_st_a3 in SP2.
      destruct SP2 as (LZ3 & PL3 & _ & BR).
      assert (C3 : dcfg (prev_st s2)) by (rewrite prev_st_a3; apply dcfg_set_match_length, dcfg_set_prev_match, dcfg_set_prev_length; exact C2).
      intros CND. unfold sl_lm_cond in CND. unfold NIL in BR. rewrite KML in BR. rewrite CND in BR.
      destruct BR as (PRE & BR).
      apply (lm_ok6_of (prev_st s2) hh C3 LZ3 PRE Hhh).
      destruct (longest_match (prev_st s2) hh) as [s4 ml]. destruct BR as (_ & _ & LZ5 & _). exact LZ5.
    -
      pose proof (slow_front_run ws hs PBL ILEN OCAP tot0 s1 D1 Hlook Hstr Hlv Hst) as X. cbv zeta in X.
      destruct X as (D4 & Elk & Estr & Ews4 & Elv & Esg & Esm & T1 & SF).
      apply sdec_ok_of; [exact D4 | rewrite Elk; exact Hlook | exact T1 | exact SF | rewrite Elv; exact Hlv | unfold lz_strat; rewrite Esg; exact Hst].
  Qed.

  Theorem strip_ok_of_drun : forall s, DRUN 3 0 true s -> 4 <= ds_level s -> lz_strat s -> ds_wrap s = 1 ->
    strip_ok FB6 ws hs s flush.
  Proof.
    intros s D Hlv Hst Hw. pose proof D as [P _ _]. pose proof P as [C I CL Ews Ehs Epbl _ _ _ _].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl). pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_look _ _ _ _ I) as Ilk.
    unfold strip_ok. split; [rewrite <- Ews; lia|].
    split.
    { intros Hl. split; [| exact Hw]. exact (dwin_fw_wf _ _ _ _ _ _ (drun_dwin _ _ _ _ _ _ _ _ _ D)). }
    destruct (Z.ltb_spec (ds_lookahead s) 262) as [Hl|Hl].
    - rewrite (st_fill_lo s flush Hl). cbn [fst snd].
      pose proof (drun_dwin _ _ _ _ _ _ _ _ _ D) as W.
      destruct (fw_run _ _ _ _ _ _ W ltac:(rewrite KML; exact Hl)) as (W1 & Z1 & L1 & CONS & EX & ST1 & _).
      pose proof (dwin_drun _ _ _ _ _ _ _ _ _ _ D W1 Z1) as D1. pose proof D1 as [[C1 I1 _ Ews1 _ _ _ _ _ _] _ _].
      pose proof (di_sl _ _ _ _ I1) as Isl1. pose proof (di_str _ _ _ _ I1) as Istr1. pose proof (di_look _ _ _ _ I1) as Ilk1.
      split; [rewrite <- Ews1; lia|].
      unfold fill_out, Z_NO_FLUSH.
      destruct (Z.ltb_spec (ds_lookahead (fill_window s)) 262) as [Hl1|Hl1]; destruct (Z.eqb_spec flush 0) as [F0|F0]; cbn [andb];
        [intros X; discriminate X | ..];
        destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [E0|E0]; intros X; try discriminate X;
        (apply shash_ok_of; [exact D1 | lia | rewrite Ews1; rewrite KML; lia | rewrite (fw_level _ _ Z1); exact Hlv | unfold lz_strat; rewrite (fw_strategy _ _ Z1); exact Hst]).
    - rewrite (st_fill_hi s flush Hl). cbn [fst snd]. split; [rewrite <- Ews; lia|]. intros _.
      apply shash_ok_of; [exact D | lia | rewrite KML; lia | exact Hlv | exact Hst].
  Qed.

  Lemma sloop_ok_of : forall n s, DRUN 3 0 true s -> 4 <= ds_level s -> lz_strat s -> ds_wrap s = 1 ->
    DeflInvFast.lzm s < Z.of_nat n -> sloop_ok FB6 ws hs n s flush.
  Proof.
    induction n as [|n IH]; intros s D Hlv Hst Hw HM.
    - exfalso. pose proof D as [[C I CL _ _ _ _ _ _ _] _ _]. pose proof (di_look _ _ _ _ I). pose proof (dc_ai _ _ _ _ CL).
      unfold DeflInvFast.lzm in HM. cbn [Z.of_nat] in HM. lia.
    - rewrite sloop_ok_S. split; [exact (strip_ok_of_drun s D Hlv Hst Hw)|].
      rewrite <- st_sbody_eq. pose proof (wk_deflate_slow_body s flush) as WK. unfold wk in WK.
      destruct (strip_run ws hs PBL ILEN OCAP tot0 tfb_safe_holds tfb_room_holds HPBL flush s D Hlv Hst) as [_ PQ].
      destruct (deflate_slow_body s flush) as [s' o]. cbn [fst snd] in WK |- *. unfold DeflInvFast.LZPOST in PQ.
      destruct PQ as [[EL ES] PQ]. destruct o; [| exact Logic.I | exact Logic.I].
      destruct PQ as [D' M']. apply IH; [exact D' | rewrite EL; exact Hlv | unfold lz_strat; rewrite ES; exact Hst | rewrite WK; exact Hw | lia].
  Qed.

  Lemma stail_ok_of : forall s, DRUN 3 0 true s -> ds_lookahead s = 0 -> 4 <= ds_level s -> lz_strat s ->
    stail_ok FB6 ws s flush.
  Proof.
    intros s D Hlook Hlv Hst. pose proof D as [P _ _]. pose proof P as [C I CL Ews Ehs Epbl _ _ _ _].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl). pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_ma _ _ _ _ I) as Ima.
    unfold stail_ok. split; [exact (strip_inv_of_dpost 3 0 true ws hs PBL ILEN OCAP tot0 s ltac:(lia) P)|].
    split; [rewrite <- Ews; lia|].
    split; [intros Ma; apply (di_ma1 _ _ _ _ I); lia|].
    pose proof (stail_mid_run ws hs PBL ILEN OCAP tot0 s D Hlook Hlv Hst) as (rm & Hrm & MID).
    assert (EB : break1_st s = (let '(s1, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in set_match_available s1 0)).
    { unfold break1_st. destruct (slit_tally_eq s) as [E1 _]. destruct (tr_tally_lit s _) as [s1 b]. cbn [fst] in E1. rewrite E1. reflexivity. }
    rewrite EB. cbv zeta in MID |- *.
    match goal with |- context [if negb (ds_match_available s =? 0) then ?A else s] => set (s2 := if negb (ds_match_available s =? 0) then A else s) in * end.
    clearbody s2. destruct MID as (D2 & L2 & M2 & EL2 & ES2).
    pose proof D2 as [P2 _ _]. pose proof P2 as [C2 I2 CL2 Ews2 Ehs2 Epbl2 _ _ _ _].
    pose proof (drun_span _ _ _ _ _ _ _ _ _ s2 Hrm P2) as (SP & STR & _).
    pose proof (dinv_lzw rm 0 true s2 Hrm C2 I2) as LZ2. pose proof (lz_sn _ LZ2) as SN. rewrite (cf_symend _ C2) in SN. pose proof (dcfg_sizes s2 C2) as (Sw2 & _ & Sl2 & _).
    split; [lia|]. split; [lia|]. split; [lia|].
    assert (DT : DRUN rm 0 true (tail_st s2)).
    { unfold tail_st. pose proof (di_str _ _ _ _ I2) as Istr2.
      set (v := if ds_strstart s2 <? MIN_MATCH - 1 then ds_strstart s2 else MIN_MATCH - 1).
      assert (Hv : 0 <= v <= ds_strstart s2) by (subst v; rewrite KMM; destruct (Z.ltb_spec (ds_strstart s2) (3 - 1)); lia).
      exact (drun_lzf ws hs PBL ILEN OCAP tot0 _ _ _ _ _ _ _ _ D2 (dinv_set_insert _ _ _ _ _ I2 Hv) (dcfg_set_insert _ _ C2) ltac:(constructor; reflexivity)). }
    split; [intros _; exact (flush_ok6_of_drun ws hs PBL ILEN OCAP tot0 HPBL rm 0 true _ 1 Hrm DT (or_intror eq_refl))|].
    intros _ _. exact (flush_ok6_of_drun ws hs PBL ILEN OCAP tot0 HPBL rm 0 true _ 0 Hrm DT (or_introl eq_refl)).
  Qed.

  Theorem slow_safe6_of_drun : forall s, DRUN 3 0 true s -> 4 <= ds_level s -> lz_strat s -> ds_wrap s = 1 ->
    ds_w_size s = ws -> ds_hash_size s = hs ->
    slow_safe6 FB6 s flush.
  Proof.
    intros s D Hlv Hst Hw Ews Ehs. pose proof D as [[C I CL _ _ _ _ _ _ _] _ _].
    unfold slow_safe6. rewrite Ews, Ehs.
    assert (HM : DeflInvFast.lzm s < Z.of_nat (lz_fuel s)).
    { unfold lz_fuel, DeflInvFast.lzm. pose proof (di_look _ _ _ _ I). pose proof (dc_ai _ _ _ _ CL). rewrite Z2Nat.id by lia. lia. }
    split; [exact (sloop_ok_of (lz_fuel s) s D Hlv Hst Hw HM)|].
    destruct (sloop_run ws hs PBL ILEN OCAP tot0 tfb_safe_holds tfb_room_holds HPBL flush (lz_fuel s) s D Hlv Hst HM) as [_ LP].
    destruct (deflate_slow_loop (lz_fuel s) s flush) as [s1 [bs|]]; cbn [fst snd]; [exact Logic.I|].
    destruct LP as (EL & ES & D1 & L1 & NF).
    exact (stail_ok_of s1 D1 L1 ltac:(rewrite EL; exact Hlv) ltac:(unfold lz_strat; rewrite ES; exact Hst)).
  Qed.
End TRIP.
End FXG.
