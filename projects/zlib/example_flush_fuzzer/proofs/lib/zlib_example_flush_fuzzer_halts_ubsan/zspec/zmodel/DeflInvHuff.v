(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateInvHash DeflateInvKeep OverlayFBS DeflRoom.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import LmatchModel FillWinModel SendModel DeflFastModel TreesTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflHuffOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep DeflInvFbo DeflInvFw DeflInvFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac dsr := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd].
Tactic Notation "dsr" "in" hyp(H) := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd] in H.


Definition hbody (s : deflate_state) : deflate_state * loop_out :=
  let '(s1, b) := lit_core (set_match_length s 0) in after_tally s1 b.

Lemma deflate_huff_body_eq : forall s flush,
  deflate_huff_body s flush =
    if ds_lookahead s =? 0 then
      let s1 := fill_window s in
      if ds_lookahead s1 =? 0 then (if flush =? Z_NO_FLUSH then (s1, LRet need_more) else (s1, LBreak))
      else hbody s1
    else hbody s.
Proof.
  intros s flush. unfold deflate_huff_body, hbody, lit_core, after_tally.
  destruct (ds_lookahead s =? 0).
  - cbv zeta. destruct (ds_lookahead (fill_window s) =? 0); [destruct (flush =? Z_NO_FLUSH); reflexivity|].
    destruct (tr_tally_lit (set_match_length (fill_window s) 0) _) as [x y]. reflexivity.
  - destruct (tr_tally_lit (set_match_length s 0) _) as [x y]. reflexivity.
Qed.

Lemma deflate_huff_loop_step : forall f s flush,
  deflate_huff_loop (S f) s flush =
    (let '(s', o) := deflate_huff_body s flush in
     match o with LCont => deflate_huff_loop f s' flush | LBreak => (s', None) | LRet bs => (s', Some bs) end).
Proof. intros; reflexivity. Qed.

Section HUFF.
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

  Lemma hlit_run : forall M0 s, DRUN 3 0 true s -> 1 <= ds_lookahead s -> ~ lz_strat s -> lzm s <= M0 ->
    hlit_ok ws PBL OCAP s /\ LZPOST M0 s (hbody s).
  Proof.
    intros M0 s D Hlook NLZ HM. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    assert (I0 : dinvR 3 0 true (set_match_length s 0)).
    { apply (dinv_set_match_length 3 0 true true s 0 I); [unfold MAX_MATCH; lia | intros _ _ _; unfold MIN_MATCH; lia | intros _ _ B; exfalso; exact (NLZ B) | intros _ B; exfalso; exact (NLZ B)]. }
    assert (C0 : dcfg (set_match_length s 0)) by (apply dcfg_set_match_length; exact C).
    assert (D0 : DRUN 3 0 true (set_match_length s 0)) by exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D I0 C0 ltac:(constructor; dsr; reflexivity)).
    destruct (lit_run ws hs PBL ILEN OCAP tot0 TS TR HPBL 0 true (set_match_length s 0) ltac:(lia) D0 ltac:(dsr; exact Hlook)
                ltac:(intros B; exfalso; exact (NLZ B))) as [LOK LP].
    unfold hlit_ok, hbody. split.
    - split; [exact (dinv_lzw 3 0 true s ltac:(lia) C I)|]. split; [exact (di_room _ _ _ _ I)|]. split; [exact Hlook|].
      unfold lit_ok in LOK. destruct LOK as (_ & _ & _ & REST). exact REST.
    - destruct (lit_core (set_match_length s 0)) as [s' b]. destruct LP as (D' & LF & L' & S' & Hb).
      pose proof (zf_level _ _ LF) as EL. pose proof (zf_strategy _ _ LF) as ES. dsr in EL. dsr in ES.
      destruct (after_tally_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush M0 s s' b D'
                  ltac:(unfold DeflInvFast.lzm in *; rewrite L', (zf_strm _ _ LF); dsr; pose proof (dc_ai _ _ _ _ CL); lia) EL ES) as [_ PQ].
      exact PQ.
  Qed.


  Lemma htrip_run : forall s, DRUN 3 0 true s -> ~ lz_strat s ->
    huff_trip_ok ws hs PBL OCAP s flush /\ LZPOST (lzm s) s (deflate_huff_body s flush).
  Proof.
    intros s D NLZ. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dinv_lzw 3 0 true s ltac:(lia) C I) as LZ0.
    pose proof (di_look _ _ _ _ I) as L0. assert (KML : MIN_LOOKAHEAD = 262) by reflexivity.
    unfold huff_trip_ok. rewrite deflate_huff_body_eq.
    destruct (Z.eqb_spec (ds_lookahead s) 0) as [Hl|Hl].
    - pose proof (drun_dwin _ _ _ _ _ _ _ _ _ D) as W.
      pose proof (dwin_fw_wf _ _ _ _ _ _ W) as WF.
      destruct (fw_run _ _ _ _ _ _ W ltac:(lia)) as (W1 & Z1 & L1 & CONS & EX & ST1 & BS1 & MS1 & NI1 & NB1).
      remember (fill_window s) as s1 eqn:Es1.
      pose proof (dwin_drun _ _ _ _ _ _ _ _ _ _ D W1 Z1) as D1. pose proof D1 as [[C1 I1 _ _ _ _ _ _ _ _] _ _].
      pose proof (dinv_lzw 3 0 true s1 ltac:(lia) C1 I1) as LZ1. pose proof (di_look _ _ _ _ I1) as L1'.
      assert (LS1 : ds_level s1 = ds_level s /\ ds_strategy s1 = ds_strategy s) by (split; [exact (fw_level _ _ Z1) | exact (fw_strategy _ _ Z1)]).
      split.
      + split; [exact LZ0|]. split; [exact WF|]. split; [exact LZ1|].
        destruct (Z.eqb_spec (ds_lookahead s1) 0) as [E0|E0]; [exact Logic.I|].
        exact (proj1 (hlit_run (lzm s) s1 D1 ltac:(lia) ltac:(unfold lz_strat; rewrite (proj2 LS1); exact NLZ) ltac:(unfold DeflInvFast.lzm in *; lia))).
      + cbv zeta. destruct (Z.eqb_spec (ds_lookahead s1) 0) as [E0|E0].
        * destruct (Z.eqb_spec flush Z_NO_FLUSH) as [F0|F0]; unfold DeflInvFast.LZPOST; (split; [exact LS1|]).
          -- split; [reflexivity|]. split; [exact (drun_dpost _ _ _ _ _ _ _ D1)|].
             right. split; [destruct EX as [X|X]; [exact X | exfalso; rewrite E0 in X; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in X; clear -X; lia] | exact F0].
          -- split; [exact D1|]. split; [exact E0 | exact F0].
        * pose proof (proj2 (hlit_run (lzm s) s1 D1 ltac:(lia) ltac:(unfold lz_strat; rewrite (proj2 LS1); exact NLZ) ltac:(unfold DeflInvFast.lzm in *; lia))) as X.
          revert X. unfold DeflInvFast.LZPOST. destruct (hbody s1) as [sx ox]. rewrite (proj1 LS1), (proj2 LS1). intros X; exact X.
    - destruct (hlit_run (lzm s) s D ltac:(lia) NLZ ltac:(lia)) as [OK PQ].
      split; [| exact PQ]. split; [exact LZ0 | exact OK].
  Qed.

  Lemma hloop_run : forall n s, DRUN 3 0 true s -> ~ lz_strat s -> lzm s < Z.of_nat n ->
    huff_loop_ok ws hs PBL OCAP n s flush
    /\ let '(s', r) := deflate_huff_loop n s flush in
       ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s
       /\ match r with None => DRUN 3 0 true s' /\ ds_lookahead s' = 0 /\ flush <> Z_NO_FLUSH | Some bs => bs = need_more /\ DPOST s' /\ NMPROG flush s' end.
  Proof.
    induction n as [|n IH]; intros s D NLZ HM.
    { exfalso. unfold DeflInvFast.lzm in HM. pose proof (di_look _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))).
      pose proof (dc_ai _ _ _ _ (dp_call _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))). cbn in HM. lia. }
    cbn [huff_loop_ok]. rewrite deflate_huff_loop_step.
    destruct (htrip_run s D NLZ) as [TOK TP].
    destruct (deflate_huff_body s flush) as [s1 o]. destruct TP as [[EL ES] TP].
    destruct o as [| |bs].
    - destruct TP as [D1 M1].
      destruct (IH s1 D1 ltac:(unfold lz_strat; rewrite ES; exact NLZ) ltac:(rewrite Nat2Z.inj_succ in HM; lia)) as [LOK LP].
      split; [split; [exact TOK | exact LOK]|].
      destruct (deflate_huff_loop n s1 flush) as [s' r]. destruct LP as (EL' & ES' & LP). split; [congruence|]. split; [congruence|]. exact LP.
    - split; [split; [exact TOK | exact Logic.I]|]. split; [exact EL|]. split; [exact ES|]. exact TP.
    - split; [split; [exact TOK | exact Logic.I]|]. split; [exact EL|]. split; [exact ES|]. exact TP.
  Qed.

  Lemma tail0_run : forall s, DRUN 3 0 true s -> ds_lookahead s = 0 -> (ds_strategy s = Z_HUFFMAN_ONLY \/ ds_strategy s = Z_RLE) -> flush <> Z_NO_FLUSH ->
    tail0_ok ws PBL OCAP s flush
    /\ let '(s', bs) := (let s1 := set_insert s 0 in deflate_tail s1 flush) in BPOST flush s s' bs.
  Proof.
    intros s D Hlook Hsg HNF. unfold tail0_ok.
    apply (tailv_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush 3 s 0 ltac:(lia) D Hlook); [| | exact HNF].
    - pose proof (di_str _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))). lia.
    - pose proof (di_maslow _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))) as X.
      destruct (Z.eq_dec (ds_match_available s) 0) as [E|E]; [exact E | exfalso].
      destruct (X E) as [_ [Y1 Y2]]. destruct Hsg as [H|H]; [exact (Y1 H) | exact (Y2 H)].
  Qed.

  Theorem huff_run : forall s, DRUN 3 0 true s -> ds_strategy s = Z_HUFFMAN_ONLY ->
    huff_ok ws hs PBL OCAP s flush
    /\ let '(s', bs) := deflate_huff s flush in BPOST flush s s' bs.
  Proof.
    intros s D Hsg. unfold huff_ok, deflate_huff.
    assert (NLZ : ~ lz_strat s) by (unfold lz_strat; rewrite Hsg; intros [A _]; exact (A eq_refl)).
    pose proof D as [[C I CL _ _ _ _ _ _ _] _ _].
    destruct (hloop_run (lz_fuel s) s D NLZ) as [LOK LP].
    { unfold lz_fuel, DeflInvFast.lzm. pose proof (di_look _ _ _ _ I). pose proof (dc_ai _ _ _ _ CL). rewrite Z2Nat.id by lia. lia. }
    split; [split; [exact LOK|]|]; destruct (deflate_huff_loop (lz_fuel s) s flush) as [s1 r]; destruct LP as (EL & ES & LP).
    - destruct r as [bs|]; [exact Logic.I|]. destruct LP as (D1 & L1 & NF). exact (proj1 (tail0_run s1 D1 L1 (or_introl (eq_trans ES Hsg)) NF)).
    - destruct r as [bs|].
      + destruct LP as (-> & P & NM). unfold DeflInvFast.BPOST. split; [exact P|]. split; [exact EL|]. split; [exact ES | exact NM].
      + destruct LP as (D1 & L1 & NF). pose proof (proj2 (tail0_run s1 D1 L1 (or_introl (eq_trans ES Hsg)) NF)) as TP. cbv zeta in TP.
        match goal with |- let '(s', bs) := ?X in _ => destruct X as [s' bs] end.
        unfold DeflInvFast.BPOST in *. destruct TP as (P & EL' & ES' & R). split; [exact P|]. split; [congruence|]. split; [congruence | exact R].
  Qed.
End HUFF.
