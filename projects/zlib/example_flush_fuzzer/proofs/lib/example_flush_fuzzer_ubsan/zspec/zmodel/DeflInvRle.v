(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateInvHash DeflateInvKeep OverlayFBS DeflRoom.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import LmatchModel FillWinModel SendModel DeflFastModel DeflRleModel TreesTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflHuffOk RefDeflRleOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep DeflInvFbo DeflInvFw DeflInvFast DeflInvHuff.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac dsr := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd].
Tactic Notation "dsr" "in" hyp(H) := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd] in H.


Lemma set_ml_ml : forall s a b, set_match_length (set_match_length s a) b = set_match_length s b.
Proof. intros s a b. destruct s; reflexivity. Qed.

Lemma rscan_shape : forall s, 0 <= ds_lookahead s -> exists v,
  rscan (set_match_length s 0) = set_match_length s v
  /\ 0 <= v <= MAX_MATCH /\ v <= ds_lookahead s /\ (MIN_MATCH <= v -> 1 <= ds_strstart s).
Proof.
  intros s Hl. unfold rscan. dsr.
  destruct (Z.leb_spec MIN_MATCH (ds_lookahead s)) as [A|A]; destruct (Z.ltb_spec 0 (ds_strstart s)) as [B|B]; cbn [andb];
    try (exists 0; split; [reflexivity|]; unfold MAX_MATCH, MIN_MATCH in *; lia).
  destruct (rle_cmpk 3 (ds_window s) (arr_get (ds_window s) (ds_strstart s - 1)) (ds_strstart s - 1)) as [sc ok] eqn:E.
  pose proof (rle_cmpk_ok_fst 3 (ds_window s) (arr_get (ds_window s) (ds_strstart s - 1)) (ds_strstart s - 1)) as F. rewrite E in F. cbn [fst snd] in F.
  destruct ok; [| exists 0; split; [reflexivity|]; unfold MAX_MATCH, MIN_MATCH in *; lia].
  specialize (F eq_refl). assert (F' : sc = ds_strstart s + 2) by lia.
  pose proof (rle_cmp_loop_le 33 (ds_window s) (arr_get (ds_window s) (ds_strstart s - 1)) sc (ds_strstart s + MAX_MATCH)
                ltac:(unfold MAX_MATCH; lia) ltac:(rewrite F'; unfold MAX_MATCH; replace (ds_strstart s + 258 - (ds_strstart s + 2)) with (32 * 8) by lia; apply Z_mod_mult)) as R.
  rewrite !set_ml_ml. dsr.
  destruct (Z.ltb_spec (ds_lookahead s) (MAX_MATCH - (ds_strstart s + MAX_MATCH - rle_cmp_loop 33 (ds_window s) (arr_get (ds_window s) (ds_strstart s - 1)) sc (ds_strstart s + MAX_MATCH))));
    rewrite ?set_ml_ml; eexists; (split; [reflexivity|]); unfold MAX_MATCH, MIN_MATCH in *; lia.
Qed.

Section RLE.
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

  Lemma rbody_ok_eq : forall s, rbody_ok ws PBL OCAP s =
    (lzw s /\ 1 <= ds_lookahead s /\ ds_sym_next s + 3 <= ds_sym_end s
     /\ (MIN_MATCH <= ds_lookahead s -> 0 < ds_strstart s -> ds_strstart s + MAX_MATCH < arr_len (ds_window s))
     /\ let s2 := rscan (set_match_length s 0) in
        lzw s2
        /\ if Z.leb MIN_MATCH (ds_match_length s2) then
             let '(s3, bflush) := tr_tally_dist s2 1 (ds_match_length s2 - MIN_MATCH) in
             let s4 := set_lookahead s3 (ds_lookahead s3 - ds_match_length s3) in
             let s5 := set_strstart s4 (ds_strstart s4 + ds_match_length s4) in
             let s6 := set_match_length s5 0 in
             lzw s6 /\ (bflush = true -> fbo_ok ws PBL OCAP s6 0)
           else
             let '(s3, bflush) := tr_tally_lit s2 (arr_get (ds_window s2) (ds_strstart s2)) in
             let s4 := set_lookahead s3 (ds_lookahead s3 - 1) in
             let s5 := set_strstart s4 (ds_strstart s4 + 1) in
             lzw s5 /\ (bflush = true -> fbo_ok ws PBL OCAP s5 0)).
  Proof. reflexivity. Qed.

  Lemma rtally_run : forall M0 s0 s2, DRUN 3 0 true s2 -> MIN_MATCH <= ds_match_length s2 -> ds_match_length s2 <= ds_lookahead s2 ->
    ~ lz_strat s2 -> lzm s2 <= M0 -> ds_level s2 = ds_level s0 -> ds_strategy s2 = ds_strategy s0 ->
    (let '(s3, bflush) := tr_tally_dist s2 1 (ds_match_length s2 - MIN_MATCH) in
     let s4 := set_lookahead s3 (ds_lookahead s3 - ds_match_length s3) in
     let s5 := set_strstart s4 (ds_strstart s4 + ds_match_length s4) in
     let s6 := set_match_length s5 0 in
     lzw s6 /\ (bflush = true -> fbo_ok ws PBL OCAP s6 0))
    /\ LZPOST M0 s0 (after_tally (rtally_out s2) (snd (rtally_core s2))).
  Proof.
    intros M0 s0 s2 D Hml Hmll NLZ HM EL ES. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s2 C) as (Sw & Sh & Sl & Shl).
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_ml _ _ _ _ I) as Iml. pose proof (di_ma _ _ _ _ I) as Ima.
    pose proof (dc_ai _ _ _ _ CL) as AI0.
    assert (KML : MIN_LOOKAHEAD = 262) by reflexivity. assert (KMM : MIN_MATCH = 3) by reflexivity. assert (KXM : MAX_MATCH = 258) by reflexivity.
    unfold rtally_out, rtally_core.
    pose proof (dinv_tally_dist 0 true s2 C I Slz P0 Sst 1 (ds_match_length s2 - MIN_MATCH) ltac:(lia) ltac:(lia)) as TD.
    pose proof (dcfg_tally_dist s2 1 (ds_match_length s2 - MIN_MATCH) C) as C3.
    destruct (tr_tally_dist s2 1 (ds_match_length s2 - MIN_MATCH)) as [s3 bflush]. cbn [fst snd] in *.
    destruct TD as (I3 & (syms & D0 & D3) & Hb & P1 & P2 & P3 & K3).
    pose proof (kp_sn_fields _ _ _ K3) as SF. destruct SF.
    pose proof (di_syms _ _ _ _ I) as (sy0 & Dy0 & COV0). rewrite (dsyms_unique _ _ _ Dy0 D0) in COV0. specialize (COV0 Slz).
    assert (ZC : zcov (syms ++ [(1, ds_match_length s2 - MIN_MATCH)]) = zcov syms + ds_match_length s2) by (rewrite zcov_app1; cbn [Z.eqb]; lia).
    assert (Hrm : 0 <= (if bflush then 0 else 3)) by (destruct bflush; lia).
    dsr. rewrite sn_lookahead, sn_match_length, sn_strstart.
    assert (I6 : dinvR (if bflush then 0 else 3) 0 true
                   (set_match_length (set_strstart (set_lookahead s3 (ds_lookahead s2 - ds_match_length s2)) (ds_strstart s2 + ds_match_length s2)) 0)).
    { apply (dinv_set_match_length _ 0 true true); dsr; [| lia | intros _ _ B; exfalso; exact (NLZ ltac:(unfold lz_strat; rewrite <- sn_strategy; exact B)) | intros _ _ B; exfalso; exact (NLZ ltac:(unfold lz_strat; rewrite <- sn_strategy; exact B)) | intros _ B; exfalso; exact (NLZ ltac:(unfold lz_strat; rewrite <- sn_strategy; exact B))].
      apply (dinv_set_strstart _ 0 true 0); dsr; rewrite ?sn_strstart, ?sn_w_size, ?sn_block_start, ?sn_match_available, ?sn_level, ?sn_strategy; try lia.
      - apply dinv_set_lookahead; [exact I3 | lia | rewrite sn_strstart, sn_w_size; lia | rewrite sn_level; intros _ _ B; exfalso; exact (NLZ ltac:(unfold lz_strat; rewrite <- sn_strategy; exact B)) | rewrite sn_wrap; intros W; exfalso; lia | rewrite sn_level; intros L0; exfalso; exact (Slz L0) | rewrite sn_lookahead; lia].
      - intros _. eexists. split; [eapply dsyms_keep; [exact D3 | dsr; reflexivity ..]|]. rewrite ZC. lia.
      - intros _ _ B. exfalso. exact (NLZ ltac:(unfold lz_strat; rewrite <- sn_strategy; exact B)). }
    assert (C6 : dcfg (set_match_length (set_strstart (set_lookahead s3 (ds_lookahead s2 - ds_match_length s2)) (ds_strstart s2 + ds_match_length s2)) 0)).
    { apply dcfg_set_match_length, dcfg_set_strstart, dcfg_set_lookahead. exact C3. }
    assert (D6 : DRUN (if bflush then 0 else 3) 0 true (set_match_length (set_strstart (set_lookahead s3 (ds_lookahead s2 - ds_match_length s2)) (ds_strstart s2 + ds_match_length s2)) 0)).
    { eapply drun_relift; [exact D | exact I6 | exact C6 | dsr; assumption ..]. }
    destruct (after_tally_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush M0 s0 _ bflush D6
                ltac:(unfold DeflInvFast.lzm in *; dsr; rewrite sn_strm; lia) ltac:(dsr; congruence) ltac:(dsr; congruence)) as [FOK PQ].
    split.
    - split; [exact (dinv_lzw _ _ _ _ Hrm C6 I6) | exact FOK].
    - replace (ds_sym_next s2 + 3 =? ds_sym_end s2) with bflush; [exact PQ|].
      rewrite Hb, (sy_next _ _ D3), (sy_next _ _ D0), length_app1, <- sn_sym_end. lia.
  Qed.

  Lemma rbody_run : forall M0 s, DRUN 3 0 true s -> 1 <= ds_lookahead s -> ds_strstart s + MAX_MATCH < 2 * ds_w_size s ->
    ~ lz_strat s -> lzm s <= M0 ->
    rbody_ok ws PBL OCAP s /\ LZPOST M0 s (rbody_spec s).
  Proof.
    intros M0 s D Hlook Hstr NLZ HM. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (di_look _ _ _ _ I) as Ilook.
    destruct (rscan_shape s ltac:(lia)) as (v & E & Hv & Hvl & Hvs).
    assert (I2 : dinvR 3 0 true (set_match_length s v)).
    { apply (dinv_set_match_length 3 0 true true s v I); [exact Hv | intros _ _ B; exfalso; exact (NLZ B) | intros _ _ B; exfalso; exact (NLZ B) | intros _ B; exfalso; exact (NLZ B)]. }
    assert (C2 : dcfg (set_match_length s v)) by (apply dcfg_set_match_length; exact C).
    assert (D2 : DRUN 3 0 true (set_match_length s v)) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D I2 C2 ltac:(constructor; dsr; reflexivity)).
    rewrite rbody_ok_eq. unfold rbody_spec, rdispatch. rewrite E. cbv zeta.
    assert (LZ0 : lzw s) by exact (dinv_lzw 3 0 true s ltac:(lia) C I).
    assert (LZ2 : lzw (set_match_length s v)) by exact (dinv_lzw 3 0 true _ ltac:(lia) C2 I2).
    assert (HD : lzw s /\ 1 <= ds_lookahead s /\ ds_sym_next s + 3 <= ds_sym_end s
                 /\ (MIN_MATCH <= ds_lookahead s -> 0 < ds_strstart s -> ds_strstart s + MAX_MATCH < arr_len (ds_window s))).
    { split; [exact LZ0|]. split; [exact Hlook|]. split; [exact (di_room _ _ _ _ I)|]. intros _ _. rewrite (cf_wl _ C). exact Hstr. }
    destruct (Z.leb_spec MIN_MATCH (ds_match_length (set_match_length s v))) as [M|M].
    - destruct (rtally_run M0 s (set_match_length s v) D2 M ltac:(dsr; dsr in M; lia) ltac:(unfold lz_strat; dsr; exact NLZ)
                  ltac:(unfold DeflInvFast.lzm in *; dsr; exact HM) eq_refl eq_refl) as [A B].
      split; [| exact B]. destruct HD as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
      split; [exact LZ2 | exact A].
    - destruct (lit_run ws hs PBL ILEN OCAP tot0 TS TR HPBL 0 true (set_match_length s v) ltac:(lia) D2 ltac:(dsr; exact Hlook)
                  ltac:(intros B; exfalso; exact (NLZ B))) as [LOK LP].
      destruct HD as (H1 & H2 & H3 & H4).
      split.
      + split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact LZ2|].
        unfold lit_ok in LOK. destruct LOK as (_ & _ & _ & REST). exact REST.
      + destruct (lit_core (set_match_length s v)) as [s' b] eqn:ELC. cbn [fst snd]. destruct LP as (D' & LF & L' & S' & Hb).
        pose proof (zf_level _ _ LF) as EL. pose proof (zf_strategy _ _ LF) as ES. dsr in EL. dsr in ES.
        destruct (after_tally_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush M0 s s' b D'
                    ltac:(unfold DeflInvFast.lzm in *; rewrite L', (zf_strm _ _ LF); dsr; pose proof (dc_ai _ _ _ _ CL); lia) EL ES) as [_ PQ].
        exact PQ.
  Qed.


  Lemma rtrip_run : forall s, DRUN 3 0 true s -> ~ lz_strat s ->
    rle_trip_ok ws hs PBL OCAP s flush /\ LZPOST (lzm s) s (deflate_rle_body s flush).
  Proof.
    intros s D NLZ. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dinv_lzw 3 0 true s ltac:(lia) C I) as LZ0.
    pose proof (di_look _ _ _ _ I) as L0. pose proof (di_sl _ _ _ _ I) as SL0.
    assert (KML : MIN_LOOKAHEAD = 262) by reflexivity. assert (KXM : MAX_MATCH = 258) by reflexivity.
    unfold rle_trip_ok. rewrite deflate_rle_body_eq.
    destruct (Z.leb_spec (ds_lookahead s) MAX_MATCH) as [Hl|Hl].
    - pose proof (drun_dwin _ _ _ _ _ _ _ _ _ D) as W.
      pose proof (dwin_fw_wf _ _ _ _ _ _ W) as WF.
      destruct (fw_run _ _ _ _ _ _ W ltac:(lia)) as (W1 & Z1 & L1 & CONS & EX & ST1 & BS1 & MS1 & NI1 & NB1).
      remember (fill_window s) as s1 eqn:Es1.
      pose proof (dwin_drun _ _ _ _ _ _ _ _ _ _ D W1 Z1) as D1. pose proof D1 as [[C1 I1 _ _ _ _ _ _ _ _] _ _].
      pose proof (dinv_lzw 3 0 true s1 ltac:(lia) C1 I1) as LZ1. pose proof (di_look _ _ _ _ I1) as L1'.
      pose proof (dw_ws _ _ _ _ _ _ W1) as Ews1.
      assert (LS1 : ds_level s1 = ds_level s /\ ds_strategy s1 = ds_strategy s) by (split; [exact (fw_level _ _ Z1) | exact (fw_strategy _ _ Z1)]).
      assert (P1 : ds_lookahead s1 <> 0 -> rbody_ok ws PBL OCAP s1 /\ LZPOST (lzm s) s1 (rbody_spec s1)).
      { intros E0. apply (rbody_run (lzm s) s1 D1); try lia.
        - unfold lz_strat. rewrite (proj2 LS1). exact NLZ.
        - unfold DeflInvFast.lzm in *. lia. }
      split.
      + split; [exact LZ0|]. split; [exact WF|]. split; [exact LZ1|].
        destruct ((ds_lookahead s1 <=? MAX_MATCH) && (flush =? Z_NO_FLUSH)); [exact Logic.I|].
        destruct (Z.eqb_spec (ds_lookahead s1) 0) as [E0|E0]; [exact Logic.I|]. exact (proj1 (P1 E0)).
      + cbv zeta. destruct (Z.leb_spec (ds_lookahead s1) MAX_MATCH) as [Hl1|Hl1]; destruct (Z.eqb_spec flush Z_NO_FLUSH) as [F0|F0]; cbn [andb].
        1: { unfold DeflInvFast.LZPOST; cbv beta iota. split; [exact LS1|]. split; [reflexivity|]. split; [exact (drun_dpost _ _ _ _ _ _ _ D1)|].
             right; split; [destruct EX as [X|X]; [exact X | exfalso; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; clear -X Hl1; lia] | exact F0]. }
        all: destruct (Z.eqb_spec (ds_lookahead s1) 0) as [E0|E0]; [unfold DeflInvFast.LZPOST; cbv beta iota; split; [exact LS1|]; split; [exact D1|]; split; [exact E0 | first [exact F0 | exfalso; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; clear -E0 Hl1; lia]]|].
        all: pose proof (proj2 (P1 E0)) as X; revert X; unfold DeflInvFast.LZPOST; destruct (rbody_spec s1) as [sx ox]; rewrite (proj1 LS1), (proj2 LS1); intros X; exact X.
    - destruct (rbody_run (lzm s) s D ltac:(lia) ltac:(lia) NLZ ltac:(lia)) as [OK PQ].
      split; [| exact PQ]. split; [exact LZ0 | exact OK].
  Qed.

  Lemma rloop_run : forall n s, DRUN 3 0 true s -> ~ lz_strat s -> lzm s < Z.of_nat n ->
    rle_loop_ok ws hs PBL OCAP n s flush
    /\ let '(s', r) := deflate_rle_loop n s flush in
       ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s
       /\ match r with None => DRUN 3 0 true s' /\ ds_lookahead s' = 0 /\ flush <> Z_NO_FLUSH | Some bs => bs = need_more /\ DPOST s' /\ NMPROG flush s' end.
  Proof.
    induction n as [|n IH]; intros s D NLZ HM.
    { exfalso. unfold DeflInvFast.lzm in HM. pose proof (di_look _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))).
      pose proof (dc_ai _ _ _ _ (dp_call _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))). cbn in HM. lia. }
    cbn [rle_loop_ok]. rewrite deflate_rle_loop_step.
    destruct (rtrip_run s D NLZ) as [TOK TP].
    destruct (deflate_rle_body s flush) as [s1 o]. destruct TP as [[EL ES] TP].
    destruct o as [| |bs].
    - destruct TP as [D1 M1].
      destruct (IH s1 D1 ltac:(unfold lz_strat; rewrite ES; exact NLZ) ltac:(rewrite Nat2Z.inj_succ in HM; lia)) as [LOK LP].
      split; [split; [exact TOK | exact LOK]|].
      destruct (deflate_rle_loop n s1 flush) as [s' r]. destruct LP as (EL' & ES' & LP). split; [congruence|]. split; [congruence|]. exact LP.
    - split; [split; [exact TOK | exact Logic.I]|]. split; [exact EL|]. split; [exact ES|]. exact TP.
    - split; [split; [exact TOK | exact Logic.I]|]. split; [exact EL|]. split; [exact ES|]. exact TP.
  Qed.

  Theorem rle_run : forall s, DRUN 3 0 true s -> ds_strategy s = Z_RLE ->
    rle_ok ws hs PBL OCAP s flush
    /\ let '(s', bs) := deflate_rle s flush in BPOST flush s s' bs.
  Proof.
    intros s D Hsg. unfold rle_ok, deflate_rle.
    assert (NLZ : ~ lz_strat s) by (unfold lz_strat; rewrite Hsg; intros [_ A]; exact (A eq_refl)).
    pose proof D as [[C I CL _ _ _ _ _ _ _] _ _].
    destruct (rloop_run (lz_fuel s) s D NLZ) as [LOK LP].
    { unfold lz_fuel, DeflInvFast.lzm. pose proof (di_look _ _ _ _ I). pose proof (dc_ai _ _ _ _ CL). rewrite Z2Nat.id by lia. lia. }
    split; [split; [exact LOK|]|]; destruct (deflate_rle_loop (lz_fuel s) s flush) as [s1 r]; destruct LP as (EL & ES & LP).
    - destruct r as [bs|]; [exact Logic.I|]. destruct LP as (D1 & L1 & NF). exact (proj1 (tail0_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush s1 D1 L1 (or_intror (eq_trans ES Hsg)) NF)).
    - destruct r as [bs|].
      + destruct LP as (-> & P & NM). unfold DeflInvFast.BPOST. split; [exact P|]. split; [exact EL|]. split; [exact ES | exact NM].
      + destruct LP as (D1 & L1 & NF). pose proof (proj2 (tail0_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush s1 D1 L1 (or_intror (eq_trans ES Hsg)) NF)) as TP. cbv zeta in TP.
        match goal with |- let '(s', bs) := ?X in _ => destruct X as [s' bs] end.
        unfold DeflInvFast.BPOST in *. destruct TP as (P & EL' & ES' & R). split; [exact P|]. split; [congruence|]. split; [congruence | exact R].
  Qed.
End RLE.
