(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateInvHash DeflateInvKeep OverlayFBS DeflRoom.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import LmatchModel FillWinModel SendModel DeflFastModel DeflSlowModel TreesTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflSlowOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep DeflInvFbo DeflInvFw DeflInvFast DeflInvSlow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac dsr := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd].
Tactic Notation "dsr" "in" hyp(H) := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd] in H.

Section SLOW2.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.
  Variable flush : Z.
  Hypothesis Hflush : 0 <= flush <= 5.

  Let DRUN rm hb fz := drunR rm hb fz ws hs PBL ILEN OCAP tot0.
  Let DPOST := dpost ws hs PBL ILEN OCAP tot0.
  Local Notation LZPOST := (LZPOST ws hs PBL ILEN OCAP tot0 flush).
  Local Notation BPOST := (BPOST ws hs PBL ILEN OCAP tot0).
  Local Notation lzm := DeflInvFast.lzm.

  Let KML : MIN_LOOKAHEAD = 262 := eq_refl.
  Let KMM : MIN_MATCH = 3 := eq_refl.
  Let KXM : MAX_MATCH = 258 := eq_refl.


  Lemma smatch_run : forall M0 s0 s, DRUN 3 1 false s ->
    MIN_MATCH <= ds_prev_length s -> ds_match_length s <= ds_prev_length s ->
    1 <= ds_strstart s -> 1 <= wrap32 (ds_strstart s - 1 - ds_prev_match s) <= ds_w_size s - MIN_LOOKAHEAD ->
    ds_prev_length s <= ds_lookahead s + 1 ->
    4 <= ds_level s -> lz_strat s -> lzm s <= M0 -> ds_level s = ds_level s0 -> ds_strategy s = ds_strategy s0 ->
    smatch_ok ws PBL OCAP s /\ LZPOST M0 s0 (sdispatch s).
  Proof.
    intros M0 s0 s D Hpl Hmlpl Hstr1 HD Hpll Hlv Hst HM EL ES. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_pl _ _ _ _ I) as Ipl.
    pose proof (di_look _ _ _ _ I) as Ilook. pose proof (di_pm _ _ _ _ I) as Ipm. pose proof (di_ma _ _ _ _ I) as Ima.
    pose proof (dc_ai _ _ _ _ CL) as AI0.
    unfold smatch_ok, sdispatch. rewrite (proj2 (Z.leb_le _ _) Hpl), (proj2 (Z.leb_le _ _) Hmlpl). cbn [andb]. cbv zeta.
    set (DD := wrap32 (ds_strstart s - 1 - ds_prev_match s)) in *.
    rewrite (wrap32_id (ds_strstart s + ds_lookahead s - MIN_MATCH)) by lia.
    pose proof (dinv_tally_dist 1 false s C I Slz P0 Sst DD (ds_prev_length s - MIN_MATCH) HD ltac:(lia)) as TD.
    pose proof (dcfg_tally_dist s DD (ds_prev_length s - MIN_MATCH) C) as C5.
    destruct (tr_tally_dist s DD (ds_prev_length s - MIN_MATCH)) as [s5 bflush]. cbn [fst snd] in *.
    destruct TD as (I5 & (syms & D0 & D5) & Hb & P1 & P2 & P3 & K5).
    pose proof (kp_sn_fields _ _ _ K5) as SF. destruct SF.
    pose proof (di_syms _ _ _ _ I) as (sy0 & Dy0 & COV0). rewrite (dsyms_unique _ _ _ Dy0 D0) in COV0. specialize (COV0 Slz).
    assert (ZC : zcov (syms ++ [(DD, ds_prev_length s - MIN_MATCH)]) = zcov syms + ds_prev_length s).
    { rewrite zcov_app1. replace (DD =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
    assert (Hrm : 0 <= (if bflush then 0 else 3)) by (destruct bflush; lia).
    assert (LZ0 : lzw s) by exact (dinv_lzw 3 1 false s ltac:(lia) C I).
    assert (LZ5 : lzw s5) by exact (dinv_lzw _ 1 false s5 Hrm C5 I5).
    rewrite sn_lookahead, sn_prev_length. rewrite (wrap32_id (ds_lookahead s - (ds_prev_length s - 1))) by lia.
    assert (I6 : dinvR (if bflush then 0 else 3) 1 false (set_lookahead s5 (ds_lookahead s - (ds_prev_length s - 1)))).
    { apply dinv_set_lookahead; try exact I5; rewrite ?sn_strstart, ?sn_w_size, ?sn_wrap, ?sn_level; [lia | lia | intros X; discriminate X | intros W; exfalso; lia | intros L0; exfalso; exact (Slz L0) | rewrite sn_lookahead; lia]. }
    set (s6 := set_lookahead s5 (ds_lookahead s - (ds_prev_length s - 1))) in *.
    assert (C6 : dcfg s6) by (subst s6; apply dcfg_set_lookahead; exact C5).
    replace (ds_prev_length s6) with (ds_prev_length s) by (subst s6; dsr; symmetry; exact sn_prev_length).
    assert (I7 : dinvR (if bflush then 0 else 3) 1 false (set_prev_length s6 (ds_prev_length s - 2))).
    { apply dinv_set_prev_length; [exact I6 | lia | subst s6; dsr; rewrite sn_level; intros A; lia]. }
    set (s7 := set_prev_length s6 (ds_prev_length s - 2)) in *.
    assert (C7 : dcfg s7) by (subst s7 s6; apply dcfg_set_prev_length, dcfg_set_lookahead; exact C5).
    assert (LF7 : lzf s s7).
    { subst s7 s6. constructor; dsr; try assumption. }
    assert (D7 : DRUN (if bflush then 0 else 3) 1 false s7) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D I7 C7 LF7).
    assert (DS7 : dsyms (syms ++ [(DD, ds_prev_length s - MIN_MATCH)]) s7) by (subst s7 s6; eapply dsyms_keep; [exact D5 | dsr; reflexivity ..]).
    assert (E7pl : ds_prev_length s7 = ds_prev_length s - 2) by (subst s7; dsr; reflexivity).
    assert (E7str : ds_strstart s7 = ds_strstart s) by (subst s7 s6; dsr; exact sn_strstart).
    assert (E7look : ds_lookahead s7 = ds_lookahead s - (ds_prev_length s - 1)) by (subst s7 s6; dsr; reflexivity).
    assert (E7ws : ds_w_size s7 = ds_w_size s) by (subst s7 s6; dsr; exact sn_w_size).
    assert (E7bs : ds_block_start s7 = ds_block_start s) by (subst s7 s6; dsr; exact sn_block_start).
    assert (E7ma : ds_match_available s7 = ds_match_available s) by (subst s7 s6; dsr; exact sn_match_available).
    assert (E7lv : ds_level s7 = ds_level s) by (subst s7 s6; dsr; exact sn_level).
    assert (E7sg : ds_strategy s7 = ds_strategy s) by (subst s7 s6; dsr; exact sn_strategy).
    assert (E7sm : ds_strm s7 = ds_strm s) by (subst s7 s6; dsr; exact sn_strm).
    rewrite E7pl.
    assert (X1 : Z.of_nat (Z.to_nat (ds_prev_length s - 2)) = ds_prev_length s7) by (rewrite E7pl; lia).
    destruct (slow_insert_run ws hs PBL ILEN OCAP tot0 (Z.to_nat (ds_prev_length s - 2)) _ 1 s7 _ (ds_strstart s + ds_lookahead s - MIN_MATCH)
                Hrm ltac:(lia) D7 X1 ltac:(rewrite E7pl; lia) ltac:(rewrite E7ws; lia) ltac:(rewrite E7str, E7pl, E7look, E7ws; lia)
                ltac:(rewrite E7lv; exact Hlv) DS7 ltac:(rewrite E7str, E7pl, E7bs, E7ma, ZC; lia)) as (IL & D8 & SF8 & DS8 & S8 & PL8).
    remember (deflate_slow_insert (Z.to_nat (ds_prev_length s - 2)) s7 (ds_strstart s + ds_lookahead s - MIN_MATCH)) as s8 eqn:Es8.
    pose proof SF8 as [[G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15] Glook Gml Gms Gpm Gsn Gse].
    pose proof (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D8)) as I8. pose proof (dp_cfg _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D8)) as C8.
    rewrite E7str, E7pl in S8.
    assert (I9 : dinvR (if bflush then 0 else 3) 1 false (set_match_available s8 0)).
    { apply dinv_set_match_available; [exact I8 | left; reflexivity | intros X; discriminate X | | intros X; exfalso; exact (X eq_refl)].
      intros _. eexists. split; [exact DS8|]. rewrite ZC, S8, G14, E7bs. lia. }
    assert (I10 : dinvR (if bflush then 0 else 3) 1 true (set_match_length (set_match_available s8 0) (MIN_MATCH - 1))).
    { apply (dinv_set_match_length _ 1 false true _ _ I9); dsr; rewrite ?G9, ?E7lv; [lia | intros _ A; lia | intros _ _ _ A; lia | intros _ _; lia]. }
    assert (I11 : dinvR (if bflush then 0 else 3) 0 true
                    (set_strstart (set_match_length (set_match_available s8 0) (MIN_MATCH - 1)) (ds_strstart (set_match_length (set_match_available s8 0) (MIN_MATCH - 1)) + 1))).
    { apply (dinv_set_strstart _ 1 true 0 _ _ I10); dsr; rewrite ?S8, ?Glook, ?E7look, ?G4, ?E7ws, ?G14, ?E7bs, ?G9, ?E7lv; try lia.
      all: try (intros _ _ _ A; lia).
      intros _. eexists. split; [eapply dsyms_keep; [exact DS8 | dsr; reflexivity ..]|]. dsr. rewrite ZC. lia. }
    remember (set_strstart (set_match_length (set_match_available s8 0) (MIN_MATCH - 1)) (ds_strstart (set_match_length (set_match_available s8 0) (MIN_MATCH - 1)) + 1)) as s11 eqn:Es11.
    assert (C11 : dcfg s11) by (subst s11; apply dcfg_set_strstart, dcfg_set_match_length, dcfg_set_match_available; exact C8).
    assert (D11 : DRUN (if bflush then 0 else 3) 0 true s11).
    { eapply drun_relift; [exact D8 | exact I11 | exact C11 | subst s11; dsr; reflexivity ..]. }
    assert (E11 : ds_lookahead s11 = ds_lookahead s - (ds_prev_length s - 1) /\ ds_strm s11 = ds_strm s
                  /\ ds_level s11 = ds_level s0 /\ ds_strategy s11 = ds_strategy s0).
    { subst s11. dsr. rewrite Glook, E7look, G1, E7sm, G9, E7lv, G10, E7sg. repeat split; try reflexivity; assumption. }
    destruct E11 as (E11look & E11sm & E11lv & E11sg).
    destruct (after_tally_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush M0 s0 s11 bflush D11 ltac:(unfold DeflInvFast.lzm in *; rewrite E11look, E11sm; lia) E11lv E11sg) as [FOK PQ].
    split.
    - split; [exact LZ0|]. split; [exact (di_room _ _ _ _ I)|]. split; [lia|].
      split; [subst DD; rewrite dist1_mod16 by lia; lia|].
      split; [exact Hpll|]. split; [lia|]. split; [exact Ipm|].
      split; [exact LZ5|]. split; [exact IL|]. split; [exact (dinv_lzw _ _ _ _ Hrm C8 I8)|].
      split; [exact (dinv_lzw _ _ _ _ Hrm C11 (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D11)))|].
      intros Hbf. split; [exact (FOK Hbf)|]. rewrite Hbf in D11.
      destruct (fbo_run ws hs PBL ILEN OCAP tot0 TS TR HPBL 0 0 true s11 0 ltac:(lia) D11 ltac:(left; reflexivity)) as (_ & P' & _). cbv zeta in P'.
      exact (drun_lzw 3 0 true _ _ _ _ _ _ _ ltac:(lia) P').
    - unfold after_tally in PQ. exact PQ.
  Qed.


  Lemma set_str_look_comm : forall s a b, set_lookahead (set_strstart s a) b = set_strstart (set_lookahead s b) a.
  Proof. intros s a b. destruct s; reflexivity. Qed.

  Lemma slit_tail : forall hb s2, 0 <= hb <= 1 -> dpostR 3 hb false ws hs PBL ILEN OCAP tot0 s2 ->
    1 <= ds_lookahead s2 -> ds_match_available s2 = 1 -> 4 <= ds_level s2 -> lz_strat s2 ->
    (exists syms2, dsyms syms2 s2 /\ ds_strstart s2 + 1 - ds_block_start s2 <= zcov syms2 + 1) ->
    (MIN_MATCH <= ds_match_length s2 -> 1 <= ds_strstart s2 - ds_match_start s2 <= ds_w_size s2 - MIN_LOOKAHEAD /\ ds_match_length s2 <= ds_lookahead s2) ->
    let s4 := set_lookahead (set_strstart s2 (ds_strstart s2 + 1)) (ds_lookahead (set_strstart s2 (ds_strstart s2 + 1)) - 1) in
    DPOST s4 /\ (cs_avail_out (ds_strm s4) <> 0 -> DRUN 3 0 true s4)
    /\ ds_lookahead s4 = ds_lookahead s2 - 1 /\ ds_strm s4 = ds_strm s2 /\ ds_level s4 = ds_level s2 /\ ds_strategy s4 = ds_strategy s2.
  Proof.
    intros hb s2 Hhb P2 Hlook Hma Hlv Hst (syms2 & DS2 & COV2) SF. pose proof P2 as [C I CL Ews Ehs Epbl Sst Swr Slz Sfl].
    cbv zeta. dsr. rewrite set_str_look_comm. pose proof (dcfg_sizes s2 C) as (Sw & Sh & Sl & Shl).
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl.
    assert (I3 : dinvR 3 hb false (set_lookahead s2 (ds_lookahead s2 - 1))).
    { apply dinv_set_lookahead; [exact I | lia | lia | intros X; discriminate X | intros W; exfalso; lia | intros L0; exfalso; exact (Slz L0) | lia]. }
    assert (I4 : dinvR 3 0 true (set_strstart (set_lookahead s2 (ds_lookahead s2 - 1)) (ds_strstart s2 + 1))).
    { apply (dinv_fz_true _ _ false).
      - apply (dinv_set_strstart 3 hb false 0 _ _ I3); dsr; try lia. all: try (intros X; discriminate X).
        intros _. exists syms2. split; [eapply dsyms_keep; [exact DS2 | dsr; reflexivity ..] | dsr; rewrite Hma; exact COV2].
      - dsr. intros A. lia.
      - dsr. intros _ _ M. destruct (SF M) as [X Y]. rewrite Z.add_simpl_r, wrap32_id by lia. lia. }
    assert (C4 : dcfg (set_strstart (set_lookahead s2 (ds_lookahead s2 - 1)) (ds_strstart s2 + 1))) by (apply dcfg_set_strstart, dcfg_set_lookahead; exact C).
    assert (P4 : DPOST (set_strstart (set_lookahead s2 (ds_lookahead s2 - 1)) (ds_strstart s2 + 1))).
    { constructor; dsr; try assumption. destruct CL; constructor; dsr; assumption. }
    split; [exact P4|]. split; [| repeat split; reflexivity].
    intros A. split; [exact P4 | ..]; dsr; apply (dp_flush _ _ _ _ _ _ _ _ _ _ P2); exact A.
  Qed.

  Lemma slit_run : forall M0 s0 hb s, 0 <= hb <= 1 -> DRUN 3 hb false s ->
    (MIN_MATCH <= ds_prev_length s -> ds_match_length s <= ds_prev_length s -> False) ->
    ds_match_available s <> 0 -> 1 <= ds_lookahead s ->
    4 <= ds_level s -> lz_strat s ->
    (MIN_MATCH <= ds_match_length s -> ds_match_length s <= ds_prev_length s
       \/ (1 <= ds_strstart s - ds_match_start s <= ds_w_size s - MIN_LOOKAHEAD /\ ds_match_length s <= ds_lookahead s)) ->
    lzm s <= M0 -> ds_level s = ds_level s0 -> ds_strategy s = ds_strategy s0 ->
    slit_ok ws PBL OCAP s /\ LZPOST M0 s0 (sdispatch s).
  Proof.
    intros M0 s0 hb s Hhb D NM Hma Hlook Hlv Hst SF HM EL ES. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_ma _ _ _ _ I) as Ima.
    pose proof (dc_ai _ _ _ _ CL) as AI0.
    assert (Hma1 : ds_match_available s = 1) by lia. pose proof (di_ma1 _ _ _ _ I Hma1 Slz) as Hstr1.
    assert (SF' : MIN_MATCH <= ds_match_length s -> 1 <= ds_strstart s - ds_match_start s <= ds_w_size s - MIN_LOOKAHEAD /\ ds_match_length s <= ds_lookahead s).
    { intros M. destruct (SF M) as [X|X]; [exfalso; exact (NM ltac:(lia) X) | exact X]. }
    unfold slit_ok, sdispatch.
    assert (EC : (MIN_MATCH <=? ds_prev_length s) && (ds_match_length s <=? ds_prev_length s) = false).
    { destruct (Z.leb_spec MIN_MATCH (ds_prev_length s)); destruct (Z.leb_spec (ds_match_length s) (ds_prev_length s)); cbn; try reflexivity. exfalso; auto. }
    rewrite EC. replace (negb (ds_match_available s =? 0)) with true by (rewrite Hma1; reflexivity). cbv zeta.
    set (c := arr_get (ds_window s) (ds_strstart s - 1)) in *.
    assert (Hc : 0 <= c < 256) by (subst c; apply (ct_win _ (di_cty _ _ _ _ I)); rewrite (cf_wl _ C); lia).
    pose proof (dinv_tally_lit hb false s C I Slz P0 Sst c Hc) as TL.
    pose proof (dcfg_tally_lit s c C) as C1.
    destruct (tr_tally_lit s c) as [s1 bflush]. cbn [fst snd] in *.
    destruct TL as (I1 & (syms & D0 & D1) & Hb & P1 & P2 & P3 & K1).
    pose proof (kp_sn_fields _ _ _ K1) as SN. destruct SN.
    pose proof (di_syms _ _ _ _ I) as (sy0 & Dy0 & COV0). rewrite (dsyms_unique _ _ _ Dy0 D0) in COV0. specialize (COV0 Slz).
    assert (Hrm : 0 <= (if bflush then 0 else 3)) by (destruct bflush; lia).
    assert (LF1 : lzf s s1) by (constructor; try assumption).
    assert (Dr1 : DRUN (if bflush then 0 else 3) hb false s1) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D I1 C1 LF1).
    assert (LZ0 : lzw s) by exact (dinv_lzw 3 hb false s ltac:(lia) C I).
    assert (LZ1 : lzw s1) by exact (dinv_lzw _ hb false s1 Hrm C1 I1).
    assert (MID : (bflush = true -> fbo_ok ws PBL OCAP s1 0)
                  /\ let s2 := (if bflush then flush_block_only s1 0 else s1) in
                     dpostR 3 hb false ws hs PBL ILEN OCAP tot0 s2
                     /\ ds_lookahead s2 = ds_lookahead s /\ ds_strstart s2 = ds_strstart s /\ ds_match_available s2 = 1
                     /\ ds_match_length s2 = ds_match_length s /\ ds_match_start s2 = ds_match_start s /\ ds_w_size s2 = ds_w_size s
                     /\ ds_level s2 = ds_level s /\ ds_strategy s2 = ds_strategy s /\ cs_avail_in (ds_strm s2) = cs_avail_in (ds_strm s)
                     /\ (exists syms2, dsyms syms2 s2 /\ ds_strstart s + 1 - ds_block_start s2 <= zcov syms2 + 1)).
    { destruct bflush.
      - destruct (fbo_run ws hs PBL ILEN OCAP tot0 TS TR HPBL 0 hb false s1 0 ltac:(lia) Dr1 ltac:(left; reflexivity)) as (FOK & P' & SN' & BS' & FR). cbv zeta in P'. cbv zeta in FR. cbv zeta in SN'. cbv zeta in BS'.
        split; [intros _; exact FOK|]. cbv zeta. split; [exact P'|].
        rewrite (ff_lookahead _ _ FR), (ff_strstart _ _ FR), (ff_match_available _ _ FR), (ff_match_length _ _ FR), (ff_match_start _ _ FR),
                (ff_w_size _ _ FR), (ff_level _ _ FR), (ff_strategy _ _ FR), (ff_avail_in _ _ FR), BS', (ff_strstart _ _ FR).
        repeat (split; [first [assumption | congruence] |]).
        destruct (di_syms _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ P')) as (syms2 & DS2 & _). exists syms2. split; [exact DS2|].
        pose proof (sy_next _ _ DS2) as SN2. rewrite SN' in SN2. destruct syms2; [| cbn in SN2; lia]. rewrite zcov_nil, sn_strstart. lia.
      - split; [intros X; discriminate X|]. cbv zeta. split; [exact (dr_post _ _ _ _ _ _ _ _ _ _ Dr1)|].
        repeat (split; [first [assumption | congruence] |]).
        exists (syms ++ [(0, c)]). split; [exact D1|]. rewrite zcov_app1, sn_block_start. cbn [Z.eqb]. lia. }
    destruct MID as [FOK MID]. cbv zeta in MID.
    remember (if bflush then flush_block_only s1 0 else s1) as s2 eqn:Es2.
    destruct MID as (P2' & E2look & E2str & E2ma & E2ml & E2ms & E2ws & E2lv & E2sg & E2ai & COV2).
    destruct (slit_tail hb s2 Hhb P2' ltac:(lia) E2ma ltac:(lia) ltac:(unfold lz_strat; rewrite E2sg; exact Hst)
                ltac:(rewrite E2str; exact COV2) ltac:(rewrite E2ml, E2str, E2ms, E2ws, E2look; exact SF')) as (P4 & D4 & E4look & E4sm & E4lv & E4sg).
    remember (set_lookahead (set_strstart s2 (ds_strstart s2 + 1)) (ds_lookahead (set_strstart s2 (ds_strstart s2 + 1)) - 1)) as s4 eqn:Es4.
    pose proof (dp_call _ _ _ _ _ _ _ _ _ _ P2') as CL2.
    split.
    - split; [exact LZ0|]. split; [exact (di_room _ _ _ _ I)|]. split; [exact Hstr1|]. split; [lia|].
      split; [exact LZ1|]. split; [exact FOK|].
      split; [exact (drun_lzw 3 hb false _ _ _ _ _ _ _ ltac:(lia) P2')|]. split; [lia|].
      pose proof (dc_ao _ _ _ _ CL2). pose proof (dc_out _ _ _ _ CL2). pose proof (dc_ocap32 _ _ _ _ CL2).
      pose proof (Zle_0_nat (length (cs_out_rev (ds_strm s2)))). unfold zlength in *. lia.
    - cbv beta. destruct (Z.eqb_spec (cs_avail_out (ds_strm s4)) 0) as [A|A]; unfold DeflInvFast.LZPOST.
      + split; [rewrite E4lv, E4sg; split; congruence|]. split; [reflexivity|]. split; [exact P4 | left; exact A].
      + split; [rewrite E4lv, E4sg; split; congruence|]. split; [exact (D4 A)|].
        unfold DeflInvFast.lzm in *. rewrite E4look, E4sm, E2ai, E2look. pose proof (dc_ai _ _ _ _ CL2). lia.
  Qed.

  Lemma snone_run' : forall M0 s0 hb s, 0 <= hb <= 1 -> DRUN 3 hb false s ->
    (MIN_MATCH <= ds_prev_length s -> ds_match_length s <= ds_prev_length s -> False) ->
    ds_match_available s = 0 -> 1 <= ds_lookahead s ->
    4 <= ds_level s -> lz_strat s ->
    (MIN_MATCH <= ds_match_length s -> ds_match_length s <= ds_prev_length s
       \/ (1 <= ds_strstart s - ds_match_start s <= ds_w_size s - MIN_LOOKAHEAD /\ ds_match_length s <= ds_lookahead s)) ->
    lzm s <= M0 -> ds_level s = ds_level s0 -> ds_strategy s = ds_strategy s0 ->
    snone_ok s /\ LZPOST M0 s0 (sdispatch s).
  Proof.
    intros M0 s0 hb s Hhb D NM Hma Hlook Hlv Hst SF HM EL ES. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    assert (SF' : MIN_MATCH <= ds_match_length s -> 1 <= ds_strstart s - ds_match_start s <= ds_w_size s - MIN_LOOKAHEAD /\ ds_match_length s <= ds_lookahead s).
    { intros M. destruct (SF M) as [X|X]; [exfalso; exact (NM ltac:(lia) X) | exact X]. }
    destruct (snone_run ws hs PBL ILEN OCAP tot0 hb s Hhb D Hlook Hma Hlv Hst SF') as (OK & D' & E1 & E2 & E3 & E4 & E5).
    split; [exact OK|].
    unfold sdispatch.
    assert (EC : (MIN_MATCH <=? ds_prev_length s) && (ds_match_length s <=? ds_prev_length s) = false).
    { destruct (Z.leb_spec MIN_MATCH (ds_prev_length s)); destruct (Z.leb_spec (ds_match_length s) (ds_prev_length s)); cbn; try reflexivity. exfalso; auto. }
    rewrite EC, Hma. cbn [Z.eqb negb]. cbv zeta. dsr.
    cbv zeta in D'. dsr in E3.
    unfold DeflInvFast.LZPOST. split; [dsr; split; assumption|]. split; [exact D'|].
    unfold DeflInvFast.lzm in *. dsr. pose proof (dc_ai _ _ _ _ CL). pose proof (di_look _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))). lia.
  Qed.

  Lemma dinv_hb_le : forall rm hb hb' fz s, dinvR rm hb fz s -> hb <= hb' -> dinvR rm hb' fz s.
  Proof.
    intros rm hb hb' fz s I H. destruct I; constructor; try assumption.
    intros L. destruct (di_hash L) as [Ins HC]. exists Ins. apply (hc_inv_str_le _ _ _ _ _ _ _ HC). lia.
  Qed.

  Lemma sdispatch_run : forall M0 s0 hb s, 0 <= hb <= 1 -> DRUN 3 hb false s -> 1 <= ds_lookahead s ->
    (MIN_MATCH <= ds_prev_length s ->
       1 <= ds_strstart s /\ 1 <= wrap32 (ds_strstart s - 1 - ds_prev_match s) <= ds_w_size s - MIN_LOOKAHEAD
       /\ ds_prev_length s <= ds_lookahead s + 1) ->
    (MIN_MATCH <= ds_match_length s -> ds_match_length s <= ds_prev_length s
       \/ (1 <= ds_strstart s - ds_match_start s <= ds_w_size s - MIN_LOOKAHEAD /\ ds_match_length s <= ds_lookahead s)) ->
    4 <= ds_level s -> lz_strat s -> lzm s <= M0 -> ds_level s = ds_level s0 -> ds_strategy s = ds_strategy s0 ->
    sdisp_ok ws PBL OCAP s /\ LZPOST M0 s0 (sdispatch s).
  Proof.
    intros M0 s0 hb s Hhb D Hlook T1 SF Hlv Hst HM EL ES. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    unfold sdisp_ok.
    destruct (Z.leb_spec MIN_MATCH (ds_prev_length s)) as [A|A]; destruct (Z.leb_spec (ds_match_length s) (ds_prev_length s)) as [B|B]; cbn [andb].
    - destruct (T1 A) as (X & Y & W).
      assert (D' : DRUN 3 1 false s) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D (dinv_hb_le _ _ 1 _ _ I ltac:(lia)) C (lzf_refl s)).
      exact (smatch_run M0 s0 s D' A B X Y W Hlv Hst HM EL ES).
    - destruct (Z.eqb_spec (ds_match_available s) 0) as [M|M]; cbn [negb].
      + exact (snone_run' M0 s0 hb s Hhb D ltac:(intros A' B'; lia) M Hlook Hlv Hst SF HM EL ES).
      + exact (slit_run M0 s0 hb s Hhb D ltac:(intros A' B'; lia) M Hlook Hlv Hst SF HM EL ES).
    - destruct (Z.eqb_spec (ds_match_available s) 0) as [M|M]; cbn [negb].
      + exact (snone_run' M0 s0 hb s Hhb D ltac:(intros A' B'; lia) M Hlook Hlv Hst SF HM EL ES).
      + exact (slit_run M0 s0 hb s Hhb D ltac:(intros A' B'; lia) M Hlook Hlv Hst SF HM EL ES).
    - destruct (Z.eqb_spec (ds_match_available s) 0) as [M|M]; cbn [negb].
      + exact (snone_run' M0 s0 hb s Hhb D ltac:(intros A' B'; lia) M Hlook Hlv Hst SF HM EL ES).
      + exact (slit_run M0 s0 hb s Hhb D ltac:(intros A' B'; lia) M Hlook Hlv Hst SF HM EL ES).
  Qed.


  Lemma sp2_run : forall M0 s0 s2 hh (Ins : Z -> Prop),
    DRUN 3 1 true s2 -> 1 <= ds_lookahead s2 ->
    ds_strstart s2 + MIN_LOOKAHEAD <= 2 * ds_w_size s2 ->
    0 <= hh < 65536 ->
    (hh <> 0 -> Ins hh /\ chain_inv Ins (ds_strstart s2) (ds_w_size s2) (ds_prev s2)) ->
    4 <= ds_level s2 -> lz_strat s2 -> lzm s2 <= M0 -> ds_level s2 = ds_level s0 -> ds_strategy s2 = ds_strategy s0 ->
    sp2_ok ws PBL OCAP s2 hh /\ LZPOST M0 s0 (slow_p2 s2 hh).
  Proof.
    intros M0 s0 s2 hh Ins D Hlook Hstr Hhh HH Hlv Hst HM EL ES. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s2 C) as (Sw & Sh & Sl & Shl).
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_ml _ _ _ _ I) as Iml.
    pose proof (di_ms _ _ _ _ I) as Ims. pose proof (di_slow1 _ _ _ _ I Hlv Hst) as Iml1.
    pose proof (di_slow _ _ _ _ I eq_refl Hlv Hst) as T1.
    unfold sp2_ok, slow_p2. cbv zeta. dsr.
    assert (I3 : dinvR 3 1 false (set_match_length (set_prev_match (set_prev_length s2 (ds_match_length s2)) (ds_match_start s2)) (MIN_MATCH - 1))).
    { apply (dinv_set_match_length 3 1 true false); dsr; [| lia | intros X; discriminate X | intros X; discriminate X | intros _ _; lia].
      apply dinv_set_prev_match; dsr; [| exact Ims].
      apply dinv_set_prev_length; [exact I | lia | intros A; lia]. }
    assert (C3 : dcfg (set_match_length (set_prev_match (set_prev_length s2 (ds_match_length s2)) (ds_match_start s2)) (MIN_MATCH - 1))).
    { apply dcfg_set_match_length, dcfg_set_prev_match, dcfg_set_prev_length. exact C. }
    assert (D3 : DRUN 3 1 false (set_match_length (set_prev_match (set_prev_length s2 (ds_match_length s2)) (ds_match_start s2)) (MIN_MATCH - 1))).
    { exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D I3 C3 ltac:(constructor; dsr; reflexivity)). }
    remember (set_match_length (set_prev_match (set_prev_length s2 (ds_match_length s2)) (ds_match_start s2)) (MIN_MATCH - 1)) as s3 eqn:Es3.
    assert (E3 : ds_prev_length s3 = ds_match_length s2 /\ ds_prev_match s3 = ds_match_start s2 /\ ds_match_length s3 = MIN_MATCH - 1
                 /\ ds_strstart s3 = ds_strstart s2 /\ ds_lookahead s3 = ds_lookahead s2 /\ ds_w_size s3 = ds_w_size s2
                 /\ ds_level s3 = ds_level s2 /\ ds_strategy s3 = ds_strategy s2 /\ ds_prev s3 = ds_prev s2 /\ ds_strm s3 = ds_strm s2
                 /\ ds_match_available s3 = ds_match_available s2).
    { subst s3. dsr. repeat split; reflexivity. }
    destruct E3 as (E3pl & E3pm & E3ml & E3str & E3look & E3ws & E3lv & E3sg & E3pv & E3sm & E3ma).
    assert (LZ3 : lzw s3) by exact (dinv_lzw 3 1 false s3 ltac:(lia) C3 I3).
    assert (T1' : MIN_MATCH <= ds_prev_length s3 ->
                  1 <= ds_strstart s3 /\ 1 <= wrap32 (ds_strstart s3 - 1 - ds_prev_match s3) <= ds_w_size s3 - MIN_LOOKAHEAD
                  /\ ds_prev_length s3 <= ds_lookahead s3 + 1).
    { rewrite E3pl, E3str, E3pm, E3ws, E3look. exact T1. }
    assert (Y1 : 1 <= ds_lookahead s3) by (rewrite E3look; exact Hlook).
    assert (Y4 : 4 <= ds_level s3) by (rewrite E3lv; exact Hlv).
    assert (Y5 : lz_strat s3) by (unfold lz_strat; rewrite E3sg; exact Hst).
    assert (Y6 : lzm s3 <= M0) by (unfold DeflInvFast.lzm in *; rewrite E3look, E3sm; exact HM).
    assert (Y7 : ds_level s3 = ds_level s0) by congruence. assert (Y8 : ds_strategy s3 = ds_strategy s0) by congruence.
    destruct (negb (hh =? NIL) && (ds_match_length s2 <? ds_max_lazy_match s2) && (wrap32 (ds_strstart s2 - hh) <=? ds_w_size s2 - MIN_LOOKAHEAD)) eqn:EC.
    - apply Bool.andb_true_iff in EC as [EC EC3]. apply Bool.andb_true_iff in EC as [EC1 EC2].
      apply Bool.negb_true_iff in EC1. apply Z.eqb_neq in EC1. unfold NIL in EC1. apply Z.leb_le in EC3.
      destruct (HH EC1) as [Ihh CH]. pose proof (proj1 CH hh Ihh) as Rhh.
      rewrite <- E3str in Rhh. rewrite wrap32_id in EC3 by lia.
      destruct (lm_run 3 1 false s3 hh Ins C3 I3 ltac:(rewrite E3lv; lia) Ihh EC1 ltac:(rewrite E3str, E3ws, E3pv; exact CH) ltac:(rewrite E3str, E3ws; exact EC3) Hhh
                  ltac:(rewrite E3str, E3ws; exact Hstr) ltac:(rewrite E3pl; exact Iml1)) as [PRE POST].
      destruct (longest_match s3 hh) as [s4 ml]. destruct POST as (v & Es4 & Hv & M1 & M2 & M3 & Alt).
      assert (I4 : dinvR 3 1 false s4).
      { rewrite Es4. apply dinv_set_match_start; [exact I3 | exact Hv | intros X; discriminate X]. }
      assert (C4 : dcfg s4) by (rewrite Es4; apply dcfg_set_match_start; exact C3).
      assert (Hml : 1 <= ml <= 258).
      { rewrite E3pl, E3look in M3. rewrite E3pl in M2. unfold MAX_MATCH in M2. lia. }
      assert (I5 : dinvR 3 1 false (set_match_length s4 ml)).
      { apply (dinv_set_match_length 3 1 false false s4 _ I4); [lia | intros X; discriminate X | intros X; discriminate X | intros _ _; lia]. }
      assert (C5 : dcfg (set_match_length s4 ml)) by (apply dcfg_set_match_length; exact C4).
      assert (LF5 : lzf s3 (set_match_length s4 ml)) by (rewrite Es4; constructor; dsr; reflexivity).
      assert (D5 : DRUN 3 1 false (set_match_length s4 ml)) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D3 I5 C5 LF5).
      remember (set_match_length s4 ml) as s5 eqn:Es5.
      assert (E5 : ds_prev_length s5 = ds_prev_length s3 /\ ds_prev_match s5 = ds_prev_match s3 /\ ds_match_length s5 = ml /\ ds_match_start s5 = v
                   /\ ds_strstart s5 = ds_strstart s3 /\ ds_lookahead s5 = ds_lookahead s3 /\ ds_w_size s5 = ds_w_size s3
                   /\ ds_level s5 = ds_level s3 /\ ds_strategy s5 = ds_strategy s3 /\ ds_strm s5 = ds_strm s3).
      { subst s5 s4. dsr. repeat split; reflexivity. }
      destruct E5 as (E5pl & E5pm & E5ml & E5ms & E5str & E5look & E5ws & E5lv & E5sg & E5sm).
      assert (LZ5 : lzw s5) by exact (dinv_lzw 3 1 false s5 ltac:(lia) C5 I5).
      match goal with |- context [if ?c then set_match_length s5 (MIN_MATCH - 1) else s5] => set (cnd := c) in * end.
      assert (DEM : exists s6, (if cnd then set_match_length s5 (MIN_MATCH - 1) else s5) = s6
                /\ DRUN 3 1 false s6 /\ lzw s6
                /\ ds_prev_length s6 = ds_prev_length s3 /\ ds_prev_match s6 = ds_prev_match s3 /\ ds_strstart s6 = ds_strstart s3
                /\ ds_lookahead s6 = ds_lookahead s3 /\ ds_w_size s6 = ds_w_size s3 /\ ds_level s6 = ds_level s3 /\ ds_strategy s6 = ds_strategy s3
                /\ ds_strm s6 = ds_strm s3
                /\ (MIN_MATCH <= ds_match_length s6 -> ds_match_length s6 = ml /\ ds_match_start s6 = v)).
      { destruct cnd.
        - eexists. split; [reflexivity|].
          assert (I6 : dinvR 3 1 false (set_match_length s5 (MIN_MATCH - 1)))
            by (apply (dinv_set_match_length 3 1 false false s5 _ I5); [lia | intros X; discriminate X | intros X; discriminate X | intros _ _; lia]).
          assert (C6 : dcfg (set_match_length s5 (MIN_MATCH - 1))) by (apply dcfg_set_match_length; exact C5).
          split; [exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D5 I6 C6 ltac:(constructor; dsr; reflexivity))|].
          split; [exact (dinv_lzw 3 1 false _ ltac:(lia) C6 I6)|]. dsr.
          repeat match goal with |- (_ = _) /\ _ => split; [assumption|] end. intros X. exfalso. clear -X KMM. lia.
        - exists s5. split; [reflexivity|]. split; [exact D5|]. split; [exact LZ5|].
          repeat match goal with |- (_ = _) /\ _ => split; [assumption|] end. intros _. split; assumption. }
      destruct DEM as (s6 & -> & D6 & LZ6 & E6pl & E6pm & E6str & E6look & E6ws & E6lv & E6sg & E6sm & E6m).
      destruct (sdispatch_run M0 s0 1 s6 ltac:(lia) D6 ltac:(rewrite E6look; exact Y1)
                  ltac:(rewrite E6pl, E6str, E6pm, E6ws, E6look; exact T1')
                  ltac:(intros M; destruct (E6m M) as [A B]; rewrite A, B, E6pl, E6str, E6ws, E6look;
                        destruct Alt as [[_ X]|[X Y]]; [left; exact X | right; lia])
                  ltac:(rewrite E6lv; exact Y4) ltac:(unfold lz_strat; rewrite E6sg; exact Y5)
                  ltac:(unfold DeflInvFast.lzm in *; rewrite E6look, E6sm; exact Y6) ltac:(congruence) ltac:(congruence)) as [DOK DQ].
      split; [| exact DQ].
      split; [exact LZ3|]. split; [lia|]. split; [lia|]. split; [exact PRE|].
      split; [exact (dinv_lzw 3 1 false s4 ltac:(lia) C4 I4)|].
      split; [lia|]. split; [exact LZ5|].
      split; [rewrite Es4; dsr; rewrite E3sg; pose proof (cf_strategy _ C); lia|].
      split; [rewrite Es4; dsr; rewrite E3pl; lia|].
      split; [exact LZ6 | exact DOK].
    - destruct (sdispatch_run M0 s0 1 s3 ltac:(lia) D3 Y1 T1' ltac:(rewrite E3ml; intros X; exfalso; clear -X KMM; lia) Y4 Y5 Y6 Y7 Y8) as [DOK DQ].
      split; [| exact DQ].
      split; [exact LZ3|]. split; [lia|]. split; [lia|]. exact DOK.
  Qed.

  Lemma sp1_run : forall M0 s, DRUN 3 0 true s -> 1 <= ds_lookahead s ->
    ds_strstart s + MIN_LOOKAHEAD <= 2 * ds_w_size s ->
    4 <= ds_level s -> lz_strat s -> lzm s <= M0 ->
    sp1_ok ws PBL OCAP s /\ LZPOST M0 s (slow_p1 s).
  Proof.
    intros M0 s D Hlook Hstr Hlv Hst HM. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    unfold sp1_ok, slow_p1.
    assert (LZ0 : lzw s) by exact (dinv_lzw 3 0 true s ltac:(lia) C I).
    destruct (Z.leb_spec MIN_MATCH (ds_lookahead s)) as [L3|L3].
    - pose proof (dinv_insert_string 3 true s C I L3) as INS. pose proof (dcfg_insert_string s (ds_strstart s) C) as C2.
      destruct (insert_string s (ds_strstart s)) as [s2 hh]. cbn [fst snd] in *.
      destruct INS as (I2 & Hhh & K2 & Q1 & Q2 & Q3 & HASH).
      assert (F : forall (f : deflate_state -> Z), (forall b a, kproj a = kproj b -> f a = f b) ->
                 (forall x a, f (set_head x a) = f x) -> (forall x a, f (set_prev x a) = f x) -> (forall x a, f (set_ins_h x a) = f x) -> f s2 = f s).
      { intros f E1 E2 E3 E4. rewrite <- (E1 _ _ K2), E2, E3, E4. reflexivity. }
      pose proof (F ds_strstart kp_strstart strstart_set_head strstart_set_prev strstart_set_ins_h) as Fstr.
      pose proof (F ds_lookahead kp_lookahead lookahead_set_head lookahead_set_prev lookahead_set_ins_h) as Flook.
      pose proof (F ds_w_size kp_w_size w_size_set_head w_size_set_prev w_size_set_ins_h) as Fws.
      pose proof (F ds_hash_size kp_hash_size hash_size_set_head hash_size_set_prev hash_size_set_ins_h) as Fhs.
      pose proof (F ds_lit_bufsize kp_lit_bufsize lit_bufsize_set_head lit_bufsize_set_prev lit_bufsize_set_ins_h) as Flb.
      pose proof (F ds_status kp_status status_set_head status_set_prev status_set_ins_h) as Fst.
      pose proof (F ds_wrap kp_wrap wrap_set_head wrap_set_prev wrap_set_ins_h) as Fwr.
      pose proof (F ds_level kp_level level_set_head level_set_prev level_set_ins_h) as Flv.
      pose proof (F ds_strategy kp_strategy strategy_set_head strategy_set_prev strategy_set_ins_h) as Fsg.
      pose proof (F ds_pending_out kp_pending_out pending_out_set_head pending_out_set_prev pending_out_set_ins_h) as Fpo.
      pose proof (F ds_max_lazy_match kp_max_lazy_match max_lazy_match_set_head max_lazy_match_set_prev max_lazy_match_set_ins_h) as Flz.
      pose proof (F ds_block_start kp_block_start block_start_set_head block_start_set_prev block_start_set_ins_h) as Fbs.
      pose proof (F ds_match_available kp_match_available match_available_set_head match_available_set_prev match_available_set_ins_h) as Fma.
      assert (Fsm : ds_strm s2 = ds_strm s).
      { pose proof (kp_strm _ _ K2) as X. rewrite strm_set_head, strm_set_prev, strm_set_ins_h in X. exact X. }
      assert (LF2 : lzf s s2) by (constructor; try assumption).
      assert (D2 : DRUN 3 1 true s2) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D I2 C2 LF2).
      destruct (HASH Slz) as (Ins & IH & CH).
      destruct (sp2_run M0 s s2 hh Ins D2 ltac:(rewrite Flook; exact Hlook) ltac:(rewrite Fstr, Fws; exact Hstr) Hhh
                  ltac:(intros NZ; split; [exact (IH NZ) | rewrite Fstr, Fws; exact CH]) ltac:(rewrite Flv; exact Hlv)
                  ltac:(unfold lz_strat; rewrite Fsg; exact Hst) ltac:(unfold DeflInvFast.lzm in *; rewrite Flook, Fsm; exact HM) Flv Fsg) as [OK PQ].
      split; [| exact PQ]. split; [exact LZ0|]. split; [exact Hlook|]. split; [exact (dinv_lzw 3 1 true s2 ltac:(lia) C2 I2) | exact OK].
    - cbn [fst snd].
      assert (D' : DRUN 3 1 true s) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D (dinv_hb01 _ _ _ I) C (lzf_refl s)).
      destruct (sp2_run M0 s s NIL (fun _ => False) D' Hlook Hstr ltac:(unfold NIL; lia) ltac:(intros X; exfalso; exact (X eq_refl)) Hlv Hst HM eq_refl eq_refl) as [OK PQ].
      split; [| exact PQ]. split; [exact LZ0|]. split; [exact Hlook|]. split; [exact LZ0 | exact OK].
  Qed.


  Lemma strip_run : forall s, DRUN 3 0 true s -> 4 <= ds_level s -> lz_strat s ->
    slow_trip_ok ws hs PBL OCAP s flush /\ LZPOST (lzm s) s (deflate_slow_body s flush).
  Proof.
    intros s D Hlv Hst. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dinv_lzw 3 0 true s ltac:(lia) C I) as LZ0.
    pose proof (di_look _ _ _ _ I) as L0. pose proof (di_sl _ _ _ _ I) as SL0. pose proof (dcfg_sizes s C) as (Sw & _).
    unfold slow_trip_ok. rewrite deflate_slow_body_eq.
    destruct (Z.ltb_spec (ds_lookahead s) MIN_LOOKAHEAD) as [Hl|Hl].
    - pose proof (drun_dwin _ _ _ _ _ _ _ _ _ D) as W.
      pose proof (dwin_fw_wf _ _ _ _ _ _ W) as WF.
      destruct (fw_run _ _ _ _ _ _ W Hl) as (W1 & Z1 & L1 & CONS & EX & ST1 & BS1 & MS1 & NI1 & NB1).
      remember (fill_window s) as s1 eqn:Es1.
      pose proof (dwin_drun _ _ _ _ _ _ _ _ _ _ D W1 Z1) as D1. pose proof D1 as [[C1 I1 _ _ _ _ _ _ _ _] _ _].
      pose proof (dinv_lzw 3 0 true s1 ltac:(lia) C1 I1) as LZ1.
      pose proof (dw_ws _ _ _ _ _ _ W1) as Ews1. pose proof (di_look _ _ _ _ I1) as L1'.
      assert (P1 : ds_lookahead s1 <> 0 -> sp1_ok ws PBL OCAP s1 /\ LZPOST (lzm s) s1 (slow_p1 s1)).
      { intros E0. apply (sp1_run (lzm s) s1 D1); try lia.
        - rewrite (fw_level _ _ Z1). exact Hlv.
        - unfold lz_strat. rewrite (fw_strategy _ _ Z1). exact Hst.
        - unfold DeflInvFast.lzm in *. lia. }
      split.
      + split; [exact LZ0|]. split; [exact WF|]. split; [exact LZ1|].
        destruct ((ds_lookahead s1 <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)); [exact Logic.I|].
        destruct (Z.eqb_spec (ds_lookahead s1) 0) as [E0|E0]; [exact Logic.I|]. exact (proj1 (P1 E0)).
      + assert (LS1 : ds_level s1 = ds_level s /\ ds_strategy s1 = ds_strategy s) by (split; [exact (fw_level _ _ Z1) | exact (fw_strategy _ _ Z1)]).
        cbv zeta. destruct (Z.ltb_spec (ds_lookahead s1) MIN_LOOKAHEAD) as [Hl1|Hl1]; destruct (Z.eqb_spec flush Z_NO_FLUSH) as [F0|F0]; cbn [andb].
        1: { unfold DeflInvFast.LZPOST; cbv beta iota. split; [exact LS1|]. split; [reflexivity|]. split; [exact (drun_dpost _ _ _ _ _ _ _ D1)|].
             right; split; [destruct EX as [X|X]; [exact X | exfalso; clear -X Hl1 KML; lia] | exact F0]. }
        all: destruct (Z.eqb_spec (ds_lookahead s1) 0) as [E0|E0]; [unfold DeflInvFast.LZPOST; cbv beta iota; split; [exact LS1|]; split; [exact D1|]; split; [exact E0 | first [exact F0 | exfalso; clear -E0 Hl1 KML; lia]]|].
        all: pose proof (proj2 (P1 E0)) as X; revert X; unfold DeflInvFast.LZPOST; destruct (slow_p1 s1) as [sx ox]; rewrite (proj1 LS1), (proj2 LS1); intros X; exact X.
    - destruct (sp1_run (lzm s) s D ltac:(lia) ltac:(lia) Hlv Hst ltac:(lia)) as [OK PQ].
      split; [| exact PQ]. split; [exact LZ0 | exact OK].
  Qed.

  Lemma sloop_run : forall n s, DRUN 3 0 true s -> 4 <= ds_level s -> lz_strat s -> lzm s < Z.of_nat n ->
    slow_loop_ok ws hs PBL OCAP n s flush
    /\ let '(s', r) := deflate_slow_loop n s flush in
       ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s
       /\ match r with None => DRUN 3 0 true s' /\ ds_lookahead s' = 0 /\ flush <> Z_NO_FLUSH | Some bs => bs = need_more /\ DPOST s' /\ NMPROG flush s' end.
  Proof.
    induction n as [|n IH]; intros s D Hlv Hst HM.
    { exfalso. unfold DeflInvFast.lzm in HM. pose proof (di_look _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))).
      pose proof (dc_ai _ _ _ _ (dp_call _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))). cbn in HM. lia. }
    cbn [slow_loop_ok]. rewrite deflate_slow_loop_step.
    destruct (strip_run s D Hlv Hst) as [TOK TP].
    destruct (deflate_slow_body s flush) as [s1 o]. destruct TP as [[EL ES] TP].
    destruct o as [| |bs].
    - destruct TP as [D1 M1].
      destruct (IH s1 D1 ltac:(rewrite EL; exact Hlv) ltac:(unfold lz_strat; rewrite ES; exact Hst) ltac:(rewrite Nat2Z.inj_succ in HM; lia)) as [LOK LP].
      split; [split; [exact TOK | exact LOK]|].
      destruct (deflate_slow_loop n s1 flush) as [s' r]. destruct LP as (EL' & ES' & LP). split; [congruence|]. split; [congruence|]. exact LP.
    - split; [split; [exact TOK | exact Logic.I]|]. split; [exact EL|]. split; [exact ES|]. exact TP.
    - split; [split; [exact TOK | exact Logic.I]|]. split; [exact EL|]. split; [exact ES|]. exact TP.
  Qed.

  Lemma stail_run : forall s, DRUN 3 0 true s -> ds_lookahead s = 0 -> 4 <= ds_level s -> lz_strat s -> flush <> Z_NO_FLUSH ->
    slow_tail_ok ws PBL OCAP s flush
    /\ let '(s', bs) :=
         (let s1 := if negb (Z.eqb (ds_match_available s) 0) then
                      let '(s1, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in set_match_available s1 0
                    else s in
          let s2 := set_insert s1 (if Z.ltb (ds_strstart s1) (MIN_MATCH - 1) then ds_strstart s1 else MIN_MATCH - 1) in
          deflate_tail s2 flush) in
       BPOST flush s s' bs.
  Proof.
    intros s D Hlook Hlv Hst HNF. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    pose proof (di_ma _ _ _ _ I) as Ima. pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl.
    assert (LZ0 : lzw s) by exact (dinv_lzw 3 0 true s ltac:(lia) C I).
    unfold slow_tail_ok.
    assert (MID : exists rm s1,
              (if negb (ds_match_available s =? 0) then
                 let '(s1, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in set_match_available s1 0
               else s) = s1
              /\ 0 <= rm /\ DRUN rm 0 true s1 /\ ds_lookahead s1 = 0 /\ ds_level s1 = ds_level s /\ ds_strategy s1 = ds_strategy s
              /\ ds_match_available s1 = 0).
    { destruct (Z.eqb_spec (ds_match_available s) 0) as [M|M]; cbn [negb].
      - exists 3, s. split; [reflexivity|]. split; [lia|]. split; [exact D|]. split; [exact Hlook|]. split; [reflexivity|]. split; [reflexivity | exact M].
      - assert (Hma1 : ds_match_available s = 1) by lia. pose proof (di_ma1 _ _ _ _ I Hma1 Slz) as Hstr1.
        set (c := arr_get (ds_window s) (ds_strstart s - 1)) in *.
        assert (Hc : 0 <= c < 256) by (subst c; apply (ct_win _ (di_cty _ _ _ _ I)); rewrite (cf_wl _ C); lia).
        pose proof (dinv_tally_lit 0 true s C I Slz P0 Sst c Hc) as TL. pose proof (dcfg_tally_lit s c C) as C1.
        destruct (tr_tally_lit s c) as [s1 bflush]. cbn [fst snd] in *.
        destruct TL as (I1 & (syms & D0 & D1) & Hb & P1 & P2 & P3 & K1).
        pose proof (kp_sn_fields _ _ _ K1) as SN. destruct SN.
        pose proof (di_syms _ _ _ _ I) as (sy0 & Dy0 & COV0). rewrite (dsyms_unique _ _ _ Dy0 D0) in COV0. specialize (COV0 Slz).
        exists (if bflush then 0 else 3), (set_match_available s1 0). split; [reflexivity|].
        split; [destruct bflush; lia|].
        assert (I2 : dinvR (if bflush then 0 else 3) 0 true (set_match_available s1 0)).
        { apply dinv_set_match_available; [exact I1 | left; reflexivity | intros X; discriminate X | | intros X; exfalso; exact (X eq_refl)].
          intros _. exists (syms ++ [(0, c)]). split; [exact D1|]. rewrite zcov_app1, sn_strstart, sn_block_start. cbn [Z.eqb]. lia. }
        assert (C2 : dcfg (set_match_available s1 0)) by (apply dcfg_set_match_available; exact C1).
        split; [| dsr; split; [rewrite sn_lookahead; exact Hlook | split; [assumption | split; [assumption | reflexivity]]]].
        eapply drun_relift; [exact D | exact I2 | exact C2 | dsr; first [assumption | symmetry; assumption] ..]. }
    destruct MID as (rm & s1 & E1 & Hrm & D1 & L1 & EL1 & ES1 & MA1). rewrite E1.
    destruct (tail_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush rm s1 Hrm D1 L1 MA1 HNF) as [TOK TP].
    split.
    - split; [exact LZ0|]. split; [lia|].
      split; [intros M; split; [pose proof (di_room _ _ _ _ I); lia | exact (di_ma1 _ _ _ _ I ltac:(lia) Slz)]|].
      exact TOK.
    - cbv zeta in TP. cbv zeta.
      match goal with |- let '(s', bs) := ?X in _ => destruct X as [s' bs] end.
      unfold DeflInvFast.BPOST in *. rewrite <- EL1, <- ES1. exact TP.
  Qed.

  Theorem slow_run : forall s, DRUN 3 0 true s -> 4 <= ds_level s -> lz_strat s ->
    slow_ok ws hs PBL OCAP s flush
    /\ let '(s', bs) := deflate_slow s flush in BPOST flush s s' bs.
  Proof.
    intros s D Hlv Hst. unfold slow_ok, deflate_slow.
    pose proof D as [[C I CL _ _ _ _ _ _ _] _ _].
    destruct (sloop_run (lz_fuel s) s D Hlv Hst) as [LOK LP].
    { unfold lz_fuel, DeflInvFast.lzm. pose proof (di_look _ _ _ _ I). pose proof (dc_ai _ _ _ _ CL). rewrite Z2Nat.id by lia. lia. }
    split; [split; [exact LOK|]|]; destruct (deflate_slow_loop (lz_fuel s) s flush) as [s1 r]; destruct LP as (EL & ES & LP).
    - destruct r as [bs|]; [exact Logic.I|]. destruct LP as (D1 & L1 & NF).
      exact (proj1 (stail_run s1 D1 L1 ltac:(rewrite EL; exact Hlv) ltac:(unfold lz_strat; rewrite ES; exact Hst) NF)).
    - destruct r as [bs|].
      + destruct LP as (-> & P & NM). unfold DeflInvFast.BPOST. split; [exact P|]. split; [exact EL|]. split; [exact ES | exact NM].
      + destruct LP as (D1 & L1 & NF). pose proof (proj2 (stail_run s1 D1 L1 ltac:(rewrite EL; exact Hlv) ltac:(unfold lz_strat; rewrite ES; exact Hst) NF)) as TP. cbv zeta in TP.
        match goal with |- let '(s', bs) := ?X in _ => destruct X as [s' bs] end.
        unfold DeflInvFast.BPOST in *. destruct TP as (P & EL' & ES' & R). split; [exact P|]. split; [congruence|]. split; [congruence | exact R].
  Qed.



  Lemma smatch_mid_run : forall s, DRUN 3 1 false s -> MIN_MATCH <= ds_prev_length s -> ds_match_length s <= ds_prev_length s ->
    1 <= ds_strstart s -> 1 <= wrap32 (ds_strstart s - 1 - ds_prev_match s) <= ds_w_size s - MIN_LOOKAHEAD ->
    ds_prev_length s <= ds_lookahead s + 1 -> 4 <= ds_level s -> lz_strat s ->
    let max_insert := wrap32 (ds_strstart s + ds_lookahead s - MIN_MATCH) in
    let '(s5, bflush) := tr_tally_dist s (wrap32 (ds_strstart s - 1 - ds_prev_match s)) (ds_prev_length s - MIN_MATCH) in
    let s6 := set_lookahead s5 (wrap32 (ds_lookahead s5 - (ds_prev_length s5 - 1))) in
    let s7 := set_prev_length s6 (ds_prev_length s6 - 2) in
    let s8 := deflate_slow_insert (Z.to_nat (ds_prev_length s7)) s7 max_insert in
    let s9 := set_match_available s8 0 in let s10 := set_match_length s9 (MIN_MATCH - 1) in
    let s11 := set_strstart s10 (ds_strstart s10 + 1) in
    DRUN (if bflush then 0 else 3) 0 true s11 /\ ds_lookahead s11 = ds_lookahead s - (ds_prev_length s - 1) /\ ds_strm s11 = ds_strm s
    /\ ds_level s11 = ds_level s /\ ds_strategy s11 = ds_strategy s.
  Proof.
    intros s D Hpl Hmlpl Hstr1 HD Hpll Hlv Hst. pose (s0 := s). pose (M0 := lzm s).
    assert (HM : lzm s <= M0) by (unfold M0; lia). assert (EL : ds_level s = ds_level s0) by reflexivity. assert (ES : ds_strategy s = ds_strategy s0) by reflexivity.
    pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].

    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_pl _ _ _ _ I) as Ipl.
    pose proof (di_look _ _ _ _ I) as Ilook. pose proof (di_pm _ _ _ _ I) as Ipm. pose proof (di_ma _ _ _ _ I) as Ima.
    pose proof (dc_ai _ _ _ _ CL) as AI0.
    cbv zeta.
    set (DD := wrap32 (ds_strstart s - 1 - ds_prev_match s)) in *.
    rewrite (wrap32_id (ds_strstart s + ds_lookahead s - MIN_MATCH)) by lia.
    pose proof (dinv_tally_dist 1 false s C I Slz P0 Sst DD (ds_prev_length s - MIN_MATCH) HD ltac:(lia)) as TD.
    pose proof (dcfg_tally_dist s DD (ds_prev_length s - MIN_MATCH) C) as C5.
    destruct (tr_tally_dist s DD (ds_prev_length s - MIN_MATCH)) as [s5 bflush]. cbn [fst snd] in *.
    destruct TD as (I5 & (syms & D0 & D5) & Hb & P1 & P2 & P3 & K5).
    pose proof (kp_sn_fields _ _ _ K5) as SF. destruct SF.
    pose proof (di_syms _ _ _ _ I) as (sy0 & Dy0 & COV0). rewrite (dsyms_unique _ _ _ Dy0 D0) in COV0. specialize (COV0 Slz).
    assert (ZC : zcov (syms ++ [(DD, ds_prev_length s - MIN_MATCH)]) = zcov syms + ds_prev_length s).
    { rewrite zcov_app1. replace (DD =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
    assert (Hrm : 0 <= (if bflush then 0 else 3)) by (destruct bflush; lia).
    assert (LZ0 : lzw s) by exact (dinv_lzw 3 1 false s ltac:(lia) C I).
    assert (LZ5 : lzw s5) by exact (dinv_lzw _ 1 false s5 Hrm C5 I5).
    rewrite sn_lookahead, sn_prev_length. rewrite (wrap32_id (ds_lookahead s - (ds_prev_length s - 1))) by lia.
    assert (I6 : dinvR (if bflush then 0 else 3) 1 false (set_lookahead s5 (ds_lookahead s - (ds_prev_length s - 1)))).
    { apply dinv_set_lookahead; try exact I5; rewrite ?sn_strstart, ?sn_w_size, ?sn_wrap, ?sn_level; [lia | lia | intros X; discriminate X | intros W; exfalso; lia | intros L0; exfalso; exact (Slz L0) | rewrite sn_lookahead; lia]. }
    set (s6 := set_lookahead s5 (ds_lookahead s - (ds_prev_length s - 1))) in *.
    assert (C6 : dcfg s6) by (subst s6; apply dcfg_set_lookahead; exact C5).
    replace (ds_prev_length s6) with (ds_prev_length s) by (subst s6; dsr; symmetry; exact sn_prev_length).
    assert (I7 : dinvR (if bflush then 0 else 3) 1 false (set_prev_length s6 (ds_prev_length s - 2))).
    { apply dinv_set_prev_length; [exact I6 | lia | subst s6; dsr; rewrite sn_level; intros A; lia]. }
    set (s7 := set_prev_length s6 (ds_prev_length s - 2)) in *.
    assert (C7 : dcfg s7) by (subst s7 s6; apply dcfg_set_prev_length, dcfg_set_lookahead; exact C5).
    assert (LF7 : lzf s s7).
    { subst s7 s6. constructor; dsr; try assumption. }
    assert (D7 : DRUN (if bflush then 0 else 3) 1 false s7) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D I7 C7 LF7).
    assert (DS7 : dsyms (syms ++ [(DD, ds_prev_length s - MIN_MATCH)]) s7) by (subst s7 s6; eapply dsyms_keep; [exact D5 | dsr; reflexivity ..]).
    assert (E7pl : ds_prev_length s7 = ds_prev_length s - 2) by (subst s7; dsr; reflexivity).
    assert (E7str : ds_strstart s7 = ds_strstart s) by (subst s7 s6; dsr; exact sn_strstart).
    assert (E7look : ds_lookahead s7 = ds_lookahead s - (ds_prev_length s - 1)) by (subst s7 s6; dsr; reflexivity).
    assert (E7ws : ds_w_size s7 = ds_w_size s) by (subst s7 s6; dsr; exact sn_w_size).
    assert (E7bs : ds_block_start s7 = ds_block_start s) by (subst s7 s6; dsr; exact sn_block_start).
    assert (E7ma : ds_match_available s7 = ds_match_available s) by (subst s7 s6; dsr; exact sn_match_available).
    assert (E7lv : ds_level s7 = ds_level s) by (subst s7 s6; dsr; exact sn_level).
    assert (E7sg : ds_strategy s7 = ds_strategy s) by (subst s7 s6; dsr; exact sn_strategy).
    assert (E7sm : ds_strm s7 = ds_strm s) by (subst s7 s6; dsr; exact sn_strm).
    rewrite E7pl.
    assert (X1 : Z.of_nat (Z.to_nat (ds_prev_length s - 2)) = ds_prev_length s7) by (rewrite E7pl; lia).
    destruct (slow_insert_run ws hs PBL ILEN OCAP tot0 (Z.to_nat (ds_prev_length s - 2)) _ 1 s7 _ (ds_strstart s + ds_lookahead s - MIN_MATCH)
                Hrm ltac:(lia) D7 X1 ltac:(rewrite E7pl; lia) ltac:(rewrite E7ws; lia) ltac:(rewrite E7str, E7pl, E7look, E7ws; lia)
                ltac:(rewrite E7lv; exact Hlv) DS7 ltac:(rewrite E7str, E7pl, E7bs, E7ma, ZC; lia)) as (IL & D8 & SF8 & DS8 & S8 & PL8).
    remember (deflate_slow_insert (Z.to_nat (ds_prev_length s - 2)) s7 (ds_strstart s + ds_lookahead s - MIN_MATCH)) as s8 eqn:Es8.
    pose proof SF8 as [[G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15] Glook Gml Gms Gpm Gsn Gse].
    pose proof (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D8)) as I8. pose proof (dp_cfg _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D8)) as C8.
    rewrite E7str, E7pl in S8.
    assert (I9 : dinvR (if bflush then 0 else 3) 1 false (set_match_available s8 0)).
    { apply dinv_set_match_available; [exact I8 | left; reflexivity | intros X; discriminate X | | intros X; exfalso; exact (X eq_refl)].
      intros _. eexists. split; [exact DS8|]. rewrite ZC, S8, G14, E7bs. lia. }
    assert (I10 : dinvR (if bflush then 0 else 3) 1 true (set_match_length (set_match_available s8 0) (MIN_MATCH - 1))).
    { apply (dinv_set_match_length _ 1 false true _ _ I9); dsr; rewrite ?G9, ?E7lv; [lia | intros _ A; lia | intros _ _ _ A; lia | intros _ _; lia]. }
    assert (I11 : dinvR (if bflush then 0 else 3) 0 true
                    (set_strstart (set_match_length (set_match_available s8 0) (MIN_MATCH - 1)) (ds_strstart (set_match_length (set_match_available s8 0) (MIN_MATCH - 1)) + 1))).
    { apply (dinv_set_strstart _ 1 true 0 _ _ I10); dsr; rewrite ?S8, ?Glook, ?E7look, ?G4, ?E7ws, ?G14, ?E7bs, ?G9, ?E7lv; try lia.
      all: try (intros _ _ _ A; lia).
      intros _. eexists. split; [eapply dsyms_keep; [exact DS8 | dsr; reflexivity ..]|]. dsr. rewrite ZC. lia. }
    remember (set_strstart (set_match_length (set_match_available s8 0) (MIN_MATCH - 1)) (ds_strstart (set_match_length (set_match_available s8 0) (MIN_MATCH - 1)) + 1)) as s11 eqn:Es11.
    assert (C11 : dcfg s11) by (subst s11; apply dcfg_set_strstart, dcfg_set_match_length, dcfg_set_match_available; exact C8).
    assert (D11 : DRUN (if bflush then 0 else 3) 0 true s11).
    { eapply drun_relift; [exact D8 | exact I11 | exact C11 | subst s11; dsr; reflexivity ..]. }
    assert (E11 : ds_lookahead s11 = ds_lookahead s - (ds_prev_length s - 1) /\ ds_strm s11 = ds_strm s
                  /\ ds_level s11 = ds_level s0 /\ ds_strategy s11 = ds_strategy s0).
    { subst s11. dsr. rewrite Glook, E7look, G1, E7sm, G9, E7lv, G10, E7sg. repeat split; try reflexivity; assumption. }
    destruct E11 as (E11look & E11sm & E11lv & E11sg).
    split; [exact D11|]. split; [exact E11look|]. split; [exact E11sm|]. split; [exact E11lv | exact E11sg].
  Qed.

  Lemma slit_mid_run : forall hb s, 0 <= hb <= 1 -> DRUN 3 hb false s ->
    (MIN_MATCH <= ds_prev_length s -> ds_match_length s <= ds_prev_length s -> False) ->
    ds_match_available s <> 0 -> 1 <= ds_lookahead s -> 4 <= ds_level s -> lz_strat s ->
    (MIN_MATCH <= ds_match_length s -> ds_match_length s <= ds_prev_length s
       \/ (1 <= ds_strstart s - ds_match_start s <= ds_w_size s - MIN_LOOKAHEAD /\ ds_match_length s <= ds_lookahead s)) ->
    let '(s1, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in
    DRUN (if bflush then 0 else 3) hb false s1 /\ lzf s s1.
  Proof.
    intros hb s Hhb D NM Hma Hlook Hlv Hst SF. pose (s0 := s). pose (M0 := lzm s).
    assert (HM : lzm s <= M0) by (unfold M0; lia). assert (EL : ds_level s = ds_level s0) by reflexivity. assert (ES : ds_strategy s = ds_strategy s0) by reflexivity.
    pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].

    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_ma _ _ _ _ I) as Ima.
    pose proof (dc_ai _ _ _ _ CL) as AI0.
    assert (Hma1 : ds_match_available s = 1) by lia. pose proof (di_ma1 _ _ _ _ I Hma1 Slz) as Hstr1.
    assert (SF' : MIN_MATCH <= ds_match_length s -> 1 <= ds_strstart s - ds_match_start s <= ds_w_size s - MIN_LOOKAHEAD /\ ds_match_length s <= ds_lookahead s).
    { intros M. destruct (SF M) as [X|X]; [exfalso; exact (NM ltac:(lia) X) | exact X]. }
    set (c := arr_get (ds_window s) (ds_strstart s - 1)) in *.
    assert (Hc : 0 <= c < 256) by (subst c; apply (ct_win _ (di_cty _ _ _ _ I)); rewrite (cf_wl _ C); lia).
    pose proof (dinv_tally_lit hb false s C I Slz P0 Sst c Hc) as TL.
    pose proof (dcfg_tally_lit s c C) as C1.
    destruct (tr_tally_lit s c) as [s1 bflush]. cbn [fst snd] in *.
    destruct TL as (I1 & (syms & D0 & D1) & Hb & P1 & P2 & P3 & K1).
    pose proof (kp_sn_fields _ _ _ K1) as SN. destruct SN.
    pose proof (di_syms _ _ _ _ I) as (sy0 & Dy0 & COV0). rewrite (dsyms_unique _ _ _ Dy0 D0) in COV0. specialize (COV0 Slz).
    assert (Hrm : 0 <= (if bflush then 0 else 3)) by (destruct bflush; lia).
    assert (LF1 : lzf s s1) by (constructor; try assumption).
    assert (Dr1 : DRUN (if bflush then 0 else 3) hb false s1) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D I1 C1 LF1).
    split; [exact Dr1 | exact LF1].
  Qed.

  Lemma stail_mid_run : forall s, DRUN 3 0 true s -> ds_lookahead s = 0 -> 4 <= ds_level s -> lz_strat s ->
    exists rm, 0 <= rm /\
      let s1 := (if negb (ds_match_available s =? 0) then
                   let '(s1, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in set_match_available s1 0
                 else s) in
      DRUN rm 0 true s1 /\ ds_lookahead s1 = 0 /\ ds_match_available s1 = 0 /\ ds_level s1 = ds_level s /\ ds_strategy s1 = ds_strategy s.
  Proof.
    intros s D Hlook Hlv Hst. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].

    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    pose proof (di_ma _ _ _ _ I) as Ima. pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl.
    assert (LZ0 : lzw s) by exact (dinv_lzw 3 0 true s ltac:(lia) C I).
    assert (MID : exists rm s1,
              (if negb (ds_match_available s =? 0) then
                 let '(s1, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in set_match_available s1 0
               else s) = s1
              /\ 0 <= rm /\ DRUN rm 0 true s1 /\ ds_lookahead s1 = 0 /\ ds_level s1 = ds_level s /\ ds_strategy s1 = ds_strategy s
              /\ ds_match_available s1 = 0).
    { destruct (Z.eqb_spec (ds_match_available s) 0) as [M|M]; cbn [negb].
      - exists 3, s. split; [reflexivity|]. split; [lia|]. split; [exact D|]. split; [exact Hlook|]. split; [reflexivity|]. split; [reflexivity | exact M].
      - assert (Hma1 : ds_match_available s = 1) by lia. pose proof (di_ma1 _ _ _ _ I Hma1 Slz) as Hstr1.
        set (c := arr_get (ds_window s) (ds_strstart s - 1)) in *.
        assert (Hc : 0 <= c < 256) by (subst c; apply (ct_win _ (di_cty _ _ _ _ I)); rewrite (cf_wl _ C); lia).
        pose proof (dinv_tally_lit 0 true s C I Slz P0 Sst c Hc) as TL. pose proof (dcfg_tally_lit s c C) as C1.
        destruct (tr_tally_lit s c) as [s1 bflush]. cbn [fst snd] in *.
        destruct TL as (I1 & (syms & D0 & D1) & Hb & P1 & P2 & P3 & K1).
        pose proof (kp_sn_fields _ _ _ K1) as SN. destruct SN.
        pose proof (di_syms _ _ _ _ I) as (sy0 & Dy0 & COV0). rewrite (dsyms_unique _ _ _ Dy0 D0) in COV0. specialize (COV0 Slz).
        exists (if bflush then 0 else 3), (set_match_available s1 0). split; [reflexivity|].
        split; [destruct bflush; lia|].
        assert (I2 : dinvR (if bflush then 0 else 3) 0 true (set_match_available s1 0)).
        { apply dinv_set_match_available; [exact I1 | left; reflexivity | intros X; discriminate X | | intros X; exfalso; exact (X eq_refl)].
          intros _. exists (syms ++ [(0, c)]). split; [exact D1|]. rewrite zcov_app1, sn_strstart, sn_block_start. cbn [Z.eqb]. lia. }
        assert (C2 : dcfg (set_match_available s1 0)) by (apply dcfg_set_match_available; exact C1).
        split; [| dsr; split; [rewrite sn_lookahead; exact Hlook | split; [assumption | split; [assumption | reflexivity]]]].
        eapply drun_relift; [exact D | exact I2 | exact C2 | dsr; first [assumption | symmetry; assumption] ..]. }
    destruct MID as (rm & s1 & E1 & Hrm & D1 & L1 & EL1 & ES1 & MA1).
    exists rm. split; [exact Hrm|]. cbv zeta. rewrite E1. split; [exact D1|]. split; [exact L1|]. split; [exact MA1|]. split; [exact EL1 | exact ES1].
  Qed.


  Definition slow_front2 (s : deflate_state) (hash_head : Z) : deflate_state :=
    let s := set_prev_length s (ds_match_length s) in
    let s := set_prev_match s (ds_match_start s) in
    let s := set_match_length s (MIN_MATCH - 1) in
    if negb (Z.eqb hash_head NIL) && Z.ltb (ds_prev_length s) (ds_max_lazy_match s)
       && Z.leb (wrap32 (ds_strstart s - hash_head)) (ds_w_size s - MIN_LOOKAHEAD)
    then
      let '(s, ml) := longest_match s hash_head in
      let s := set_match_length s ml in
      if Z.leb (ds_match_length s) 5
         && (Z.eqb (ds_strategy s) Z_FILTERED
             || (Z.eqb (ds_match_length s) MIN_MATCH
                 && Z.ltb TOO_FAR (wrap32 (ds_strstart s - ds_match_start s))))
      then set_match_length s (MIN_MATCH - 1)
      else s
    else s.
  Definition slow_front (s : deflate_state) : deflate_state :=
    let '(s, hash_head) :=
      if Z.leb MIN_MATCH (ds_lookahead s) then insert_string s (ds_strstart s) else (s, NIL) in
    slow_front2 s hash_head.

  Lemma slow_p2_front : forall s hh, slow_p2 s hh = sdispatch (slow_front2 s hh).
  Proof.
    intros s hh. unfold slow_p2, slow_front2.
    destruct (negb (hh =? NIL) && _ && _); [| reflexivity].
    destruct (longest_match _ hh) as [s4 ml]. destruct (_ && _); reflexivity.
  Qed.
  Lemma slow_p1_front : forall s, slow_p1 s = sdispatch (slow_front s).
  Proof.
    intros s. unfold slow_p1, slow_front.
    destruct (if Z.leb MIN_MATCH (ds_lookahead s) then insert_string s (ds_strstart s) else (s, NIL)) as [s2 hh]. apply slow_p2_front.
  Qed.

  Lemma slow_front2_run : forall s2 hh (Ins : Z -> Prop),
    DRUN 3 1 true s2 -> 1 <= ds_lookahead s2 ->
    ds_strstart s2 + MIN_LOOKAHEAD <= 2 * ds_w_size s2 ->
    0 <= hh < 65536 ->
    (hh <> 0 -> Ins hh /\ chain_inv Ins (ds_strstart s2) (ds_w_size s2) (ds_prev s2)) ->
    4 <= ds_level s2 -> lz_strat s2 ->
    let s6 := slow_front2 s2 hh in
    DRUN 3 1 false s6
    /\ ds_lookahead s6 = ds_lookahead s2 /\ ds_strstart s6 = ds_strstart s2 /\ ds_w_size s6 = ds_w_size s2
    /\ ds_level s6 = ds_level s2 /\ ds_strategy s6 = ds_strategy s2 /\ ds_strm s6 = ds_strm s2
    /\ (MIN_MATCH <= ds_prev_length s6 ->
        1 <= ds_strstart s6 /\ 1 <= wrap32 (ds_strstart s6 - 1 - ds_prev_match s6) <= ds_w_size s6 - MIN_LOOKAHEAD
        /\ ds_prev_length s6 <= ds_lookahead s6 + 1)
    /\ (MIN_MATCH <= ds_match_length s6 -> ds_match_length s6 <= ds_prev_length s6
        \/ (1 <= ds_strstart s6 - ds_match_start s6 <= ds_w_size s6 - MIN_LOOKAHEAD /\ ds_match_length s6 <= ds_lookahead s6)).
  Proof.
    intros s2 hh Ins D Hlook Hstr Hhh HH Hlv Hst. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s2 C) as (Sw & Sh & Sl & Shl).
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_ml _ _ _ _ I) as Iml.
    pose proof (di_ms _ _ _ _ I) as Ims. pose proof (di_slow1 _ _ _ _ I Hlv Hst) as Iml1.
    pose proof (di_slow _ _ _ _ I eq_refl Hlv Hst) as T1.
    unfold slow_front2. cbv zeta. dsr.
    assert (I3 : dinvR 3 1 false (set_match_length (set_prev_match (set_prev_length s2 (ds_match_length s2)) (ds_match_start s2)) (MIN_MATCH - 1))).
    { apply (dinv_set_match_length 3 1 true false); dsr; [| lia | intros X; discriminate X | intros X; discriminate X | intros _ _; lia].
      apply dinv_set_prev_match; dsr; [| exact Ims].
      apply dinv_set_prev_length; [exact I | lia | intros A; lia]. }
    assert (C3 : dcfg (set_match_length (set_prev_match (set_prev_length s2 (ds_match_length s2)) (ds_match_start s2)) (MIN_MATCH - 1))).
    { apply dcfg_set_match_length, dcfg_set_prev_match, dcfg_set_prev_length. exact C. }
    assert (D3 : DRUN 3 1 false (set_match_length (set_prev_match (set_prev_length s2 (ds_match_length s2)) (ds_match_start s2)) (MIN_MATCH - 1))).
    { exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D I3 C3 ltac:(constructor; dsr; reflexivity)). }
    remember (set_match_length (set_prev_match (set_prev_length s2 (ds_match_length s2)) (ds_match_start s2)) (MIN_MATCH - 1)) as s3 eqn:Es3.
    assert (E3 : ds_prev_length s3 = ds_match_length s2 /\ ds_prev_match s3 = ds_match_start s2 /\ ds_match_length s3 = MIN_MATCH - 1
                 /\ ds_strstart s3 = ds_strstart s2 /\ ds_lookahead s3 = ds_lookahead s2 /\ ds_w_size s3 = ds_w_size s2
                 /\ ds_level s3 = ds_level s2 /\ ds_strategy s3 = ds_strategy s2 /\ ds_prev s3 = ds_prev s2 /\ ds_strm s3 = ds_strm s2
                 /\ ds_match_available s3 = ds_match_available s2).
    { subst s3. dsr. repeat split; reflexivity. }
    destruct E3 as (E3pl & E3pm & E3ml & E3str & E3look & E3ws & E3lv & E3sg & E3pv & E3sm & E3ma).
    assert (T1' : MIN_MATCH <= ds_prev_length s3 ->
                  1 <= ds_strstart s3 /\ 1 <= wrap32 (ds_strstart s3 - 1 - ds_prev_match s3) <= ds_w_size s3 - MIN_LOOKAHEAD
                  /\ ds_prev_length s3 <= ds_lookahead s3 + 1).
    { rewrite E3pl, E3str, E3pm, E3ws, E3look. exact T1. }
    destruct (negb (hh =? NIL) && (ds_match_length s2 <? ds_max_lazy_match s2) && (wrap32 (ds_strstart s2 - hh) <=? ds_w_size s2 - MIN_LOOKAHEAD)) eqn:EC.
    - apply Bool.andb_true_iff in EC as [EC EC3]. apply Bool.andb_true_iff in EC as [EC1 EC2].
      apply Bool.negb_true_iff in EC1. apply Z.eqb_neq in EC1. unfold NIL in EC1. apply Z.leb_le in EC3.
      destruct (HH EC1) as [Ihh CH]. pose proof (proj1 CH hh Ihh) as Rhh.
      rewrite <- E3str in Rhh. rewrite wrap32_id in EC3 by lia.
      destruct (lm_run 3 1 false s3 hh Ins C3 I3 ltac:(rewrite E3lv; lia) Ihh EC1 ltac:(rewrite E3str, E3ws, E3pv; exact CH) ltac:(rewrite E3str, E3ws; exact EC3) Hhh
                  ltac:(rewrite E3str, E3ws; exact Hstr) ltac:(rewrite E3pl; exact Iml1)) as [PRE POST].
      destruct (longest_match s3 hh) as [s4 ml]. destruct POST as (v & Es4 & Hv & M1 & M2 & M3 & Alt).
      assert (I4 : dinvR 3 1 false s4).
      { rewrite Es4. apply dinv_set_match_start; [exact I3 | exact Hv | intros X; discriminate X]. }
      assert (C4 : dcfg s4) by (rewrite Es4; apply dcfg_set_match_start; exact C3).
      assert (Hml : 1 <= ml <= 258).
      { rewrite E3pl, E3look in M3. rewrite E3pl in M2. unfold MAX_MATCH in M2. lia. }
      assert (I5 : dinvR 3 1 false (set_match_length s4 ml)).
      { apply (dinv_set_match_length 3 1 false false s4 _ I4); [lia | intros X; discriminate X | intros X; discriminate X | intros _ _; lia]. }
      assert (C5 : dcfg (set_match_length s4 ml)) by (apply dcfg_set_match_length; exact C4).
      assert (LF5 : lzf s3 (set_match_length s4 ml)) by (rewrite Es4; constructor; dsr; reflexivity).
      assert (D5 : DRUN 3 1 false (set_match_length s4 ml)) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D3 I5 C5 LF5).
      remember (set_match_length s4 ml) as s5 eqn:Es5.
      assert (E5 : ds_prev_length s5 = ds_prev_length s3 /\ ds_prev_match s5 = ds_prev_match s3 /\ ds_match_length s5 = ml /\ ds_match_start s5 = v
                   /\ ds_strstart s5 = ds_strstart s3 /\ ds_lookahead s5 = ds_lookahead s3 /\ ds_w_size s5 = ds_w_size s3
                   /\ ds_level s5 = ds_level s3 /\ ds_strategy s5 = ds_strategy s3 /\ ds_strm s5 = ds_strm s3).
      { subst s5 s4. dsr. repeat split; reflexivity. }
      destruct E5 as (E5pl & E5pm & E5ml & E5ms & E5str & E5look & E5ws & E5lv & E5sg & E5sm).
      match goal with |- context [if ?c then set_match_length s5 (MIN_MATCH - 1) else s5] => set (cnd := c) in * end.
      assert (DEM : exists s6, (if cnd then set_match_length s5 (MIN_MATCH - 1) else s5) = s6
                /\ DRUN 3 1 false s6
                /\ ds_prev_length s6 = ds_prev_length s3 /\ ds_prev_match s6 = ds_prev_match s3 /\ ds_strstart s6 = ds_strstart s3
                /\ ds_lookahead s6 = ds_lookahead s3 /\ ds_w_size s6 = ds_w_size s3 /\ ds_level s6 = ds_level s3 /\ ds_strategy s6 = ds_strategy s3
                /\ ds_strm s6 = ds_strm s3
                /\ (MIN_MATCH <= ds_match_length s6 -> ds_match_length s6 = ml /\ ds_match_start s6 = v)).
      { destruct cnd.
        - eexists. split; [reflexivity|].
          assert (I6 : dinvR 3 1 false (set_match_length s5 (MIN_MATCH - 1)))
            by (apply (dinv_set_match_length 3 1 false false s5 _ I5); [lia | intros X; discriminate X | intros X; discriminate X | intros _ _; lia]).
          assert (C6 : dcfg (set_match_length s5 (MIN_MATCH - 1))) by (apply dcfg_set_match_length; exact C5).
          split; [exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D5 I6 C6 ltac:(constructor; dsr; reflexivity))|].
          dsr. repeat match goal with |- (_ = _) /\ _ => split; [assumption|] end. intros X. exfalso. clear -X KMM. lia.
        - exists s5. split; [reflexivity|]. split; [exact D5|].
          repeat match goal with |- (_ = _) /\ _ => split; [assumption|] end. intros _. split; assumption. }
      destruct DEM as (s6 & -> & D6 & E6pl & E6pm & E6str & E6look & E6ws & E6lv & E6sg & E6sm & E6m).
      split; [exact D6|].
      rewrite E6look, E6str, E6ws, E6lv, E6sg, E6sm, E6pl, E6pm, E3look, E3str, E3ws, E3lv, E3sg, E3sm.
      repeat (split; [reflexivity|]).
      split; [rewrite <- E3str, <- E3ws, <- E3look; exact T1'|].
      intros M. destruct (E6m M) as [A B]. rewrite A, B. rewrite E3pl.
      rewrite ?E3pl, ?E3str, ?E3ws, ?E3look in Alt. destruct Alt as [[_ X]|[X Y]]; [left; exact X | right; lia].
    - split; [exact D3|]. rewrite E3look, E3str, E3ws, E3lv, E3sg, E3sm.
      repeat (split; [reflexivity|]).
      split; [rewrite <- E3str, <- E3ws, <- E3look; exact T1'|].
      rewrite E3ml. intros X. exfalso. clear -X KMM. lia.
  Qed.

  Lemma slow_front_run : forall s, DRUN 3 0 true s -> 1 <= ds_lookahead s ->
    ds_strstart s + MIN_LOOKAHEAD <= 2 * ds_w_size s ->
    4 <= ds_level s -> lz_strat s ->
    let s6 := slow_front s in
    DRUN 3 1 false s6
    /\ ds_lookahead s6 = ds_lookahead s /\ ds_strstart s6 = ds_strstart s /\ ds_w_size s6 = ds_w_size s
    /\ ds_level s6 = ds_level s /\ ds_strategy s6 = ds_strategy s /\ ds_strm s6 = ds_strm s
    /\ (MIN_MATCH <= ds_prev_length s6 ->
        1 <= ds_strstart s6 /\ 1 <= wrap32 (ds_strstart s6 - 1 - ds_prev_match s6) <= ds_w_size s6 - MIN_LOOKAHEAD
        /\ ds_prev_length s6 <= ds_lookahead s6 + 1)
    /\ (MIN_MATCH <= ds_match_length s6 -> ds_match_length s6 <= ds_prev_length s6
        \/ (1 <= ds_strstart s6 - ds_match_start s6 <= ds_w_size s6 - MIN_LOOKAHEAD /\ ds_match_length s6 <= ds_lookahead s6)).
  Proof.
    intros s D Hlook Hstr Hlv Hst. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    unfold slow_front.
    destruct (Z.leb_spec MIN_MATCH (ds_lookahead s)) as [L3|L3].
    - pose proof (dinv_insert_string 3 true s C I L3) as INS. pose proof (dcfg_insert_string s (ds_strstart s) C) as C2.
      destruct (insert_string s (ds_strstart s)) as [s2 hh]. cbn [fst snd] in *.
      destruct INS as (I2 & Hhh & K2 & Q1 & Q2 & Q3 & HASH).
      assert (F : forall (f : deflate_state -> Z), (forall b a, kproj a = kproj b -> f a = f b) ->
                 (forall x a, f (set_head x a) = f x) -> (forall x a, f (set_prev x a) = f x) -> (forall x a, f (set_ins_h x a) = f x) -> f s2 = f s).
      { intros f E1 E2 E3 E4. rewrite <- (E1 _ _ K2), E2, E3, E4. reflexivity. }
      pose proof (F ds_strstart kp_strstart strstart_set_head strstart_set_prev strstart_set_ins_h) as Fstr.
      pose proof (F ds_lookahead kp_lookahead lookahead_set_head lookahead_set_prev lookahead_set_ins_h) as Flook.
      pose proof (F ds_w_size kp_w_size w_size_set_head w_size_set_prev w_size_set_ins_h) as Fws.
      pose proof (F ds_hash_size kp_hash_size hash_size_set_head hash_size_set_prev hash_size_set_ins_h) as Fhs.
      pose proof (F ds_lit_bufsize kp_lit_bufsize lit_bufsize_set_head lit_bufsize_set_prev lit_bufsize_set_ins_h) as Flb.
      pose proof (F ds_status kp_status status_set_head status_set_prev status_set_ins_h) as Fst.
      pose proof (F ds_wrap kp_wrap wrap_set_head wrap_set_prev wrap_set_ins_h) as Fwr.
      pose proof (F ds_level kp_level level_set_head level_set_prev level_set_ins_h) as Flv.
      pose proof (F ds_strategy kp_strategy strategy_set_head strategy_set_prev strategy_set_ins_h) as Fsg.
      pose proof (F ds_pending_out kp_pending_out pending_out_set_head pending_out_set_prev pending_out_set_ins_h) as Fpo.
      pose proof (F ds_max_lazy_match kp_max_lazy_match max_lazy_match_set_head max_lazy_match_set_prev max_lazy_match_set_ins_h) as Flz.
      pose proof (F ds_block_start kp_block_start block_start_set_head block_start_set_prev block_start_set_ins_h) as Fbs.
      pose proof (F ds_match_available kp_match_available match_available_set_head match_available_set_prev match_available_set_ins_h) as Fma.
      assert (Fsm : ds_strm s2 = ds_strm s).
      { pose proof (kp_strm _ _ K2) as X. rewrite strm_set_head, strm_set_prev, strm_set_ins_h in X. exact X. }
      assert (LF2 : lzf s s2) by (constructor; try assumption).
      assert (D2 : DRUN 3 1 true s2) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D I2 C2 LF2).
      destruct (HASH Slz) as (Ins & IH & CH).
      pose proof (slow_front2_run s2 hh Ins D2 ltac:(rewrite Flook; exact Hlook) ltac:(rewrite Fstr, Fws; exact Hstr) Hhh
                  ltac:(intros NZ; split; [exact (IH NZ) | rewrite Fstr, Fws; exact CH]) ltac:(rewrite Flv; exact Hlv)
                  ltac:(unfold lz_strat; rewrite Fsg; exact Hst)) as X.
      cbv zeta in X. rewrite Flook, Fstr, Fws, Flv, Fsg, Fsm in X. exact X.
    - cbn [fst snd].
      assert (D' : DRUN 3 1 true s) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D (dinv_hb01 _ _ _ I) C (lzf_refl s)).
      exact (slow_front2_run s NIL (fun _ => False) D' Hlook Hstr ltac:(unfold NIL; lia) ltac:(intros X; exfalso; exact (X eq_refl)) Hlv Hst).
  Qed.
End SLOW2.
