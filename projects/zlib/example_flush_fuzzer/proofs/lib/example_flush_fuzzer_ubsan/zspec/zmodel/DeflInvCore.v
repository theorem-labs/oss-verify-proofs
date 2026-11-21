(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateInvHash DeflateInvKeep OverlayFBS DeflRoom.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import LmatchModel FillWinModel SendModel AdlerModel DeflFastModel TreesTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflSlowOk RefDeflStoredOk RefDeflHuffOk RefDeflRleOk RefDeflMidOk RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3 RefDeflateHdr4 RefDeflateHdr5 RefDeflateTrl1 RefDeflateCore_run RefDeflateEnd1 RefDeflateRel RefDeflatePost RefDeflateSafe.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflInvTally DeflInvBits DeflInvStep DeflInvFbo DeflInvFw DeflInvFast DeflInvSlow2 DeflInvHuff DeflInvRle DeflInvStored DeflInvBk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac dsr := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd].
Tactic Notation "dsr" "in" hyp(H) := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd] in H.
Ltac drop_impl := repeat match goal with H : _ -> _ |- _ => clear H end.


Section Preds.
  Variables (ws hs PBL ILEN OCAP flush : Z).

  Definition front_okG (s : deflate_state) : Prop :=
    (dstatus_ok (ds_status s) /\ 0 <= cs_avail_in (ds_strm s) < 2 ^ 32 /\ 0 <= cs_avail_out (ds_strm s) < 2 ^ 32
     /\ 0 <= cs_next_in (ds_strm s) <= ILEN)
    /\ (f1_spec s flush = None ->
        f2_ok PBL OCAP flush s
        /\ match f2_spec s flush with
           | F2Ret _ _ => True
           | F2Fin s' => b4_ok s'
           | F2Hdr s' => f3_ok PBL OCAP s' /\ b4_ok (fst (f3_spec s'))
           end).


  Definition core_okG (s : deflate_state) : Prop :=
    front_okG s
    /\ match front_spec s flush with
       | FrontRet _ _ => True
       | FrontBlocks s' => blocks_ok ws hs PBL ILEN OCAP s' flush
                         /\ (let '(s2, r) := blocks_body s' flush in r = None -> trl_ok PBL OCAP flush s2)
       | FrontIdle s' => trl_ok PBL OCAP flush s'
       end.
End Preds.

Definition DADLER2 (wrap a : Z) : Prop := 0 <= a < 2 ^ 32 /\ (wrap = 1 -> adler_canon a).

Lemma arr_get_of_list_In : forall l i, 0 <= i < zlength l -> In (arr_get (arr_of_list l) i) l.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb, arr_make. rewrite arr_len_init.
  replace ((0 <=? i) && (i <? 0 + zlength l) && ((0 <=? i) && (i <? zlength l))) with true
    by (symmetry; rewrite !andb_true_iff; rewrite !Z.leb_le, !Z.ltb_lt; lia).
  rewrite Z.sub_0_r. apply nth_In. unfold zlength in Hi. lia.
Qed.
Lemma u8a_of_list : forall l, Forall (fun b => 0 <= b < 256) l -> u8a (arr_of_list l).
Proof. intros l H i Hi. rewrite arr_len_of_list in Hi. apply (proj1 (Forall_forall _ l) H). apply arr_get_of_list_In. exact Hi. Qed.

Lemma ep_shape : forall s s', eproj s' = eproj s ->
  s' = set_bi_valid (set_bi_buf (set_pending (set_pending_buf s (ds_pending_buf s')) (ds_pending s')) (ds_bi_buf s')) (ds_bi_valid s').
Proof.
  intros s s' E. unfold eproj, ezap in E. destruct s, s'. cbn in E. cbn.
  injection E. intros. subst. reflexivity.
Qed.

Lemma spo_self : forall x st po,
  set_pending_out (set_strm (set_pending_out (set_strm x st) po) (ds_strm x)) (ds_pending_out x) = x.
Proof. intros x st po. destruct x. reflexivity. Qed.

Lemma put_byte_set_status : forall s v c, put_byte (set_status s v) c = set_status (put_byte s c) v.
Proof. intros s v c. destruct s. reflexivity. Qed.
Lemma putShortMSB_set_status : forall s v b, putShortMSB (set_status s v) b = set_status (putShortMSB s b) v.
Proof. intros s v b. unfold putShortMSB. rewrite !put_byte_set_status. reflexivity. Qed.
Lemma set_strm_set_status : forall s v st, set_strm (set_status s v) st = set_status (set_strm s st) v.
Proof. intros s v st. destruct s. reflexivity. Qed.
Lemma strm_putShortMSB : forall s b, ds_strm (putShortMSB s b) = ds_strm s.
Proof. intros s b. unfold putShortMSB, put_byte. dsr. reflexivity. Qed.
Lemma strm_put_byte : forall s c, ds_strm (put_byte s c) = ds_strm s.
Proof. intros s c. unfold put_byte. dsr. reflexivity. Qed.
Lemma status_put_byte : forall s c, ds_status (put_byte s c) = ds_status s.
Proof. intros s c. unfold put_byte. dsr. reflexivity. Qed.
Lemma level_put_byte : forall s c, ds_level (put_byte s c) = ds_level s.
Proof. intros s c. unfold put_byte. dsr. reflexivity. Qed.
Lemma strategy_put_byte : forall s c, ds_strategy (put_byte s c) = ds_strategy s.
Proof. intros s c. unfold put_byte. dsr. reflexivity. Qed.

Lemma clear_hash_head0 : forall s h, arr_len (ds_head s) = ds_hash_size s -> 0 <= h < ds_hash_size s ->
  arr_get (ds_head (clear_hash s)) h = 0.
Proof.
  intros s h L Hh. unfold clear_hash. dsr. rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_set, L.
  destruct (Z.eq_dec h (ds_hash_size s - 1)) as [E|E].
  - replace ((0 <=? h) && (h <? 0 + Z.max 0 (ds_hash_size s - 1)) && ((0 <=? h) && (h <? ds_hash_size s))) with false
      by (symmetry; rewrite !Bool.andb_false_iff, Z.ltb_ge; left; right; lia).
    rewrite E. unfold NIL. apply arr_get_set_same. rewrite L. lia.
  - replace ((0 <=? h) && (h <? 0 + Z.max 0 (ds_hash_size s - 1)) && ((0 <=? h) && (h <? ds_hash_size s))) with true
      by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
    reflexivity.
Qed.

Lemma if_set_status : forall (b : bool) x y v, set_status (if b then x else y) v = if b then set_status x v else set_status y v.
Proof. intros [] x y v; reflexivity. Qed.
Lemma adler_ok_init : adler_ok adler32_init.
Proof. unfold adler_ok, adler32_init. vm_compute. repeat split; try discriminate; try reflexivity. Qed.
Lemma zlength_cons' : forall {A} (x : A) l, zlength (x :: l) = zlength l + 1.
Proof. intros A x l. unfold zlength. cbn [length]. lia. Qed.

Lemma clear_hash_fields : forall s,
  ds_pending (clear_hash s) = ds_pending s /\ ds_sym_next (clear_hash s) = ds_sym_next s /\ ds_status (clear_hash s) = ds_status s
  /\ ds_lookahead (clear_hash s) = ds_lookahead s /\ ds_match_available (clear_hash s) = ds_match_available s
  /\ ds_pending_out (clear_hash s) = ds_pending_out s /\ ds_hash_size (clear_hash s) = ds_hash_size s.
Proof. intros s. destruct s. repeat split; reflexivity. Qed.
Lemma reset0_fields : forall s, let sr := set_insert (set_block_start (set_strstart s 0) 0) 0 in
  ds_pending sr = ds_pending s /\ ds_sym_next sr = ds_sym_next s /\ ds_status sr = ds_status s /\ ds_pending_out sr = ds_pending_out s.
Proof. intros s. destruct s. repeat split; reflexivity. Qed.


Section CORE.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.

  Record dcore (s : deflate_state) : Prop := MkDCORE {
    co_cfg : dcfg s;
    co_inv : dinv s;
    co_call : dcall ILEN OCAP tot0 s;
    co_ws : ds_w_size s = ws;
    co_hs : ds_hash_size s = hs;
    co_pbl : ds_lit_bufsize s * 4 = PBL }.

  Lemma dcore_basics : forall s, dcore s ->
    512 <= ws <= 32768 /\ 512 <= PBL <= 2 ^ 17 /\ ds_pending_buf_size s = PBL /\ arr_len (ds_pending_buf s) = PBL
    /\ 0 <= ds_pending s /\ 0 <= ds_pending_out s /\ 8 * (ds_pending_out s + ds_pending s) + ds_bi_valid s <= 8 * PBL
    /\ 0 <= ds_bi_valid s <= 16 /\ 0 <= ds_bi_buf s < 2 ^ 16
    /\ 0 <= cs_avail_in (ds_strm s) /\ 0 <= cs_next_in (ds_strm s) /\ cs_next_in (ds_strm s) + cs_avail_in (ds_strm s) = ILEN /\ ILEN < 2 ^ 32
    /\ 0 <= cs_avail_out (ds_strm s) /\ cs_avail_out (ds_strm s) + zlength (cs_out_rev (ds_strm s)) = OCAP /\ OCAP < 2 ^ 32
    /\ 0 <= zlength (cs_out_rev (ds_strm s))
    /\ 0 <= cs_total_in (ds_strm s) < 2 ^ 64 /\ 0 <= cs_adler (ds_strm s) < 2 ^ 32 /\ -2 <= ds_wrap s <= 2
    /\ -2 <= ds_last_flush s <= 5 /\ 0 <= ds_strstart s <= 65536 /\ 0 <= ds_lookahead s <= 65536 /\ 0 <= ds_level s <= 9 /\ 0 <= ds_strategy s <= 4.
  Proof.
    intros s [C I CL Ews Ehs Epbl]. pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    pose proof I as [T Istr Ilook Isl Iins Ibs Ibs0 Ihw Iih Ims Ipm Iml Ipl Ima Ima1 Imt Ifast Ifastpl Islow Islow1 Ihash Isyms Iroom Ibv Ibb Ipend Ipout Ipop Ipo0 Ipobv Ilf Ilive Iinit Igz Ineg Ilk0 Isn0 Iinw Ifl Imas Ips].
    assert (OL : 0 <= zlength (cs_out_rev (ds_strm s))) by apply Zle_0_nat.
    destruct CL. pose proof (cf_pbs _ C). pose proof (cf_bl _ C). pose proof (cf_wrap _ C). pose proof (cf_level _ C). pose proof (cf_strategy _ C).
    drop_impl. clear T C I Isyms. repeat split; lia.
  Qed.

  Lemma dcore_status_ok : forall s, dcore s -> dstatus_ok (ds_status s).
  Proof. intros s D. apply (proj1 (deflateStateCheck_ok s)). exact (cf_check _ (co_cfg _ D)). Qed.

  Lemma dcore_status_range : forall s, dcore s -> 0 <= ds_status s < 2 ^ 10.
  Proof. intros s D. pose proof (dcore_status_ok s D) as X. unfold dstatus_ok in X. lia. Qed.

  Local Ltac dinv_xfer I :=
    let sy := fresh "sy" in let D := fresh "D" in let Cv := fresh "Cv" in
    pose proof (di_syms _ _ _ _ I) as (sy & D & Cv);
    destruct I; constructor; dsr; try assumption;
    try (exists sy; split; [eapply dsyms_keep; [exact D | dsr; reflexivity ..] | dsr; exact Cv]).

  Lemma dcore_msg : forall s m, dcore s -> dcore (set_strm s (cset_msg (ds_strm s) m)).
  Proof.
    intros s m [C I CL Ews Ehs Epbl]. constructor; dsr; try assumption.
    - apply dcfg_set_strm. exact C.
    - dinv_xfer I. apply cty_set_strm_in; [assumption | reflexivity].
    - destruct CL; constructor; dsr; assumption.
  Qed.

  Lemma dcore_set_last_flush : forall s v, dcore s -> -2 <= v <= 5 -> dcore (set_last_flush s v).
  Proof.
    intros s v [C I CL Ews Ehs Epbl] Hv. constructor; dsr; try assumption.
    - destruct C; constructor; dsr; assumption.
    - dinv_xfer I. apply cty_set_last_flush. assumption.
    - destruct CL; constructor; dsr; assumption.
  Qed.

  Lemma dcore_set_status : forall s v, dcore s ->
    ((v = BUSY_STATE /\ 0 <= ds_wrap s) \/ (v = FINISH_STATE /\ ds_lookahead s = 0 /\ ds_sym_next s = 0)) -> dcore (set_status s v).
  Proof.
    intros s v [C I CL Ews Ehs Epbl] Hv.
    assert (Hv' : v = BUSY_STATE \/ v = FINISH_STATE) by (destruct Hv as [[X _]|[X _]]; [left|right]; exact X).
    constructor; dsr; try assumption.
    - destruct C; constructor; dsr; try assumption. unfold deflateStateCheck in *. dsr.
      destruct Hv' as [-> | ->]; reflexivity.
    - dinv_xfer I.
      + apply cty_set_status. assumption.
      + unfold BUSY_STATE, FINISH_STATE in Hv'. clear -Hv'. lia.
      + intros [X|X]; exfalso; unfold BUSY_STATE, FINISH_STATE, INIT_STATE, GZIP_STATE in *; clear -Hv' X; lia.
      + intros X; exfalso; unfold BUSY_STATE, FINISH_STATE, INIT_STATE, GZIP_STATE in *; clear -Hv' X; lia.
      + intros W. destruct Hv as [[_ P]|[-> [L _]]]; [exfalso; clear -W P; lia | split; [reflexivity | exact L]].
      + intros X; exfalso; unfold BUSY_STATE, FINISH_STATE, INIT_STATE, GZIP_STATE in *; clear -Hv' X; lia.
      + intros X. destruct Hv as [[Hb _] | [_ L]]; [exfalso; rewrite Hb in X; discriminate X | exact L].
    - destruct CL; constructor; dsr; assumption.
  Qed.

  Lemma dcore_entry0 : forall s0 zc, dcfg s0 -> dinv s0 -> zcall_ok zc -> DADLER2 (ds_wrap s0) (zs_adler (zc_strm zc)) ->
    ds_w_size s0 = ws -> ds_hash_size s0 = hs -> ds_lit_bufsize s0 * 4 = PBL ->
    zlength (zc_input zc) = ILEN -> zc_avail_out zc = OCAP -> zs_total_out (zc_strm zc) = tot0 ->
    dcore (set_strm s0 (cstrm_of_call zc)).
  Proof.
    intros s0 zc C I ((Zti & Zto & Zad & Zdt) & Zao & Zil & Zib) [A2 A1] Ews Ehs Epbl Eil Eoc Etot.
    assert (OL : 0 <= zlength (zc_input zc)) by apply Zle_0_nat.
    constructor; dsr; try assumption.
    - apply dcfg_set_strm. exact C.
    - pose proof (di_syms _ _ _ _ I) as (sy & D & Cv).
      destruct I; constructor; dsr; try assumption.
      + destruct di_cty; constructor; dsr; try assumption. unfold cstrm_of_call. cbn [cs_input]. apply u8a_of_list. exact Zib.
      + exists sy. split; [eapply dsyms_keep; [exact D | dsr; reflexivity ..] | dsr; exact Cv].
    - unfold cstrm_of_call. constructor; dsr; rewrite ?arr_len_of_list; change (zlength (@nil Z)) with 0; try lia.
      all: try (intros W; apply adler_ok_canon; exact (A1 W)).
      all: try exact A2.
      all: try (intros _; exact A2).
      all: try constructor.
      rewrite <- Etot, Z.add_0_r. symmetry. apply wrap64_id. lia.
  Qed.

  Lemma dcore_entry : forall s0 zc, DI s0 -> zcall_ok zc -> DADLER2 (ds_wrap s0) (zs_adler (zc_strm zc)) ->
    ds_w_size s0 = ws -> ds_hash_size s0 = hs -> ds_lit_bufsize s0 * 4 = PBL ->
    zlength (zc_input zc) = ILEN -> zc_avail_out zc = OCAP -> zs_total_out (zc_strm zc) = tot0 ->
    dcore (set_strm s0 (cstrm_of_call zc)).
  Proof.
    intros s0 zc [C I] ZC AD Ews Ehs Epbl Eil Eoc Etot. rewrite <- set_strm_zin.
    exact (dcore_entry0 (zin s0) zc (dcfg_zin s0 C) I ZC AD Ews Ehs Epbl Eil Eoc Etot).
  Qed.


  Lemma dcore_bits : forall s, dcore s -> bits_ok s.
  Proof. intros s D. pose proof (dcore_basics s D) as BB. split; lia. Qed.

  Lemma dcore_fp_inv : forall s, dcore s -> fp_inv PBL s.
  Proof.
    intros s D. pose proof (dcore_basics s D) as BB. pose proof D as [C I CL Ews Ehs Epbl].
    constructor; unfold bvol; try (clear -BB; lia). 2: exact (di_po0 _ _ _ _ I).
    split; clear -BB; lia.
  Qed.

  Lemma dcore_fp_ok : forall s, dcore s -> fp_ok PBL OCAP s.
  Proof. intros s D. pose proof D as [C I CL Ews Ehs Epbl]. exact (fp_ok_intro ILEN OCAP tot0 PBL s (dcore_fp_inv s D) CL (di_cty _ _ _ _ I)). Qed.

  Lemma dcore_BINV : forall s, dcore s -> BINV PBL s.
  Proof. intros s D. pose proof (dcore_basics s D) as BB. unfold BINV. lia. Qed.

  Lemma dcore_b4 : forall s, dcore s -> b4_ok s.
  Proof. intros s D. pose proof (dcore_basics s D) as BB. pose proof (dcore_status_range s D). unfold b4_ok. lia. Qed.

  Lemma dcore_lzw : forall s, dcore s -> lzw s.
  Proof. intros s [C I CL _ _ _]. exact (dinv_lzw 3 0 true s ltac:(lia) C I). Qed.

  Lemma dcore_status4 : forall s, dcore s ->
    ds_status s = INIT_STATE \/ ds_status s = GZIP_STATE \/ ds_status s = BUSY_STATE \/ ds_status s = FINISH_STATE.
  Proof.
    intros s D. pose proof (dcore_status_ok s D) as X. pose proof (di_live _ _ _ _ (co_inv _ D)) as (L1 & L2 & L3 & L4).
    unfold dstatus_ok, INIT_STATE, GZIP_STATE, BUSY_STATE, FINISH_STATE in *. lia.
  Qed.


  Lemma dcore_ep0 : forall s s', dcore s -> ds_sym_next s = 0 -> eproj s' = eproj s -> cty s' ->
    0 <= ds_bi_valid s' <= 16 -> 0 <= ds_bi_buf s' < 2 ^ 16 -> 0 <= ds_pending s' ->
    8 * (ds_pending_out s + ds_pending s') + ds_bi_valid s' <= 8 * PBL -> (ds_pending s' = 0 -> ds_pending_out s = 0) ->
    (ds_pending_out s <> 0 -> ds_bi_valid s' < 8) ->
    (ds_status s = INIT_STATE \/ ds_status s = GZIP_STATE -> ds_pending s' = 0) ->
    dcore s'.
  Proof.
    intros s s' D SN E T' Hbv Hbb Hp Hpop Hpo0 Hpobv Hinit. pose proof D as [C I CL Ews Ehs Epbl].
    pose proof (ep_kp _ _ E) as K. pose proof (ep_shape s s' E) as SH.
    remember (ds_pending_buf s') as pb' eqn:E1. remember (ds_pending s') as p' eqn:E2.
    remember (ds_bi_buf s') as bb' eqn:E3. remember (ds_bi_valid s') as bv' eqn:E4. clear E1 E2 E3 E4.
    subst s'.
    pose proof (di_syms _ _ _ _ I) as (sy & Dy & Cv).
    assert (sy = []) as -> by (pose proof (sy_next _ _ Dy) as X; rewrite SN in X; destruct sy; [reflexivity | cbn in X; lia]).
    pose proof (dsyms_nil_ep _ _ Dy E) as Dy'.
    constructor; dsr; try assumption.
    - exact (dcfg_kproj _ _ K C).
    - destruct I; constructor; dsr; try assumption.
      all: try (exists (@nil (Z * Z)); split; [exact Dy' | dsr; exact Cv]).
      all: try (rewrite Epbl; exact Hpop).
      all: try (intros X; split; [exact (Hinit X) | split; [exact (proj1 (proj2 (di_init X))) | exact SN]]).
      all: try (intros _; exact SN).
    - destruct CL; constructor; dsr; assumption.
  Qed.

  Lemma dcore_put_byte : forall s c, dcore s -> ds_sym_next s = 0 ->
    ds_status s <> INIT_STATE -> ds_status s <> GZIP_STATE ->
    8 * (ds_pending_out s + ds_pending s + 1) + ds_bi_valid s <= 8 * PBL ->
    dcore (put_byte s c) /\ ds_pending (put_byte s c) = ds_pending s + 1 /\ ds_bi_valid (put_byte s c) = ds_bi_valid s
    /\ ds_pending_out (put_byte s c) = ds_pending_out s /\ ds_sym_next (put_byte s c) = 0
    /\ ds_status (put_byte s c) = ds_status s /\ ds_strm (put_byte s c) = ds_strm s /\ ds_wrap (put_byte s c) = ds_wrap s.
  Proof.
    intros s c D SN NI NG R. pose proof (dcore_basics s D) as BB.
    destruct (put_byte_bits s c (dcore_bits s D)) as (B1 & V1 & P1 & BV1 & BB1).
    pose proof (ep_put_byte s c) as E.
    split.
    - apply (dcore_ep0 s (put_byte s c) D SN E).
      + apply cty_put_byte. exact (di_cty _ _ _ _ (co_inv _ D)).
      + rewrite BV1. lia.
      + rewrite BB1. lia.
      + rewrite P1. lia.
      + rewrite P1, BV1. lia.
      + rewrite P1. intros X. exfalso. lia.
      + rewrite BV1. exact (di_pobv _ _ _ _ (co_inv _ D)).
      + intros [X|X]; exfalso; [exact (NI X) | exact (NG X)].
    - rewrite P1, BV1, (ep_pending_out _ _ E), (ep_sym_next _ _ E), (ep_status _ _ E), (ep_strm _ _ E), (ep_wrap _ _ E), SN.
      repeat split; reflexivity.
  Qed.

  Lemma dcore_putShortMSB : forall s b, dcore s -> ds_sym_next s = 0 ->
    ds_status s <> INIT_STATE -> ds_status s <> GZIP_STATE ->
    8 * (ds_pending_out s + ds_pending s + 2) + ds_bi_valid s <= 8 * PBL ->
    dcore (putShortMSB s b) /\ ds_pending (putShortMSB s b) = ds_pending s + 2 /\ ds_bi_valid (putShortMSB s b) = ds_bi_valid s
    /\ ds_pending_out (putShortMSB s b) = ds_pending_out s /\ ds_sym_next (putShortMSB s b) = 0
    /\ ds_status (putShortMSB s b) = ds_status s /\ ds_strm (putShortMSB s b) = ds_strm s /\ ds_wrap (putShortMSB s b) = ds_wrap s.
  Proof.
    intros s b D SN NI NG R. unfold putShortMSB.
    destruct (dcore_put_byte s (Z.shiftr b 8) D SN NI NG ltac:(lia)) as (D1 & P1 & V1 & PO1 & SN1 & ST1 & SM1 & W1).
    destruct (dcore_put_byte (put_byte s (Z.shiftr b 8)) (Z.land b 255) D1 SN1 ltac:(rewrite ST1; exact NI) ltac:(rewrite ST1; exact NG)
                ltac:(rewrite PO1, P1, V1; lia)) as (D2 & P2 & V2 & PO2 & SN2 & ST2 & SM2 & W2).
    rewrite P2, V2, PO2, ST2, SM2, W2, P1, V1, PO1, ST1, SM1, W1. split; [exact D2|]. repeat split; try reflexivity; try lia.
  Qed.

  Lemma dcore_fp : forall s, dcore s -> ds_sym_next s = 0 -> ds_status s <> INIT_STATE -> ds_status s <> GZIP_STATE ->
    let s' := flush_pending s in
    dcore s'
    /\ (cs_avail_out (ds_strm s') <> 0 -> ds_pending s' = 0 /\ ds_pending_out s' = 0)
    /\ (ds_pending s' = 0 -> ds_pending_out s' = 0)
    /\ ds_status s' = ds_status s /\ ds_lookahead s' = ds_lookahead s /\ ds_sym_next s' = 0 /\ ds_wrap s' = ds_wrap s
    /\ ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s /\ ds_match_available s' = ds_match_available s
    /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s)
    /\ cs_avail_out (ds_strm s') <= cs_avail_out (ds_strm s)
    /\ 0 <= ds_bi_valid s' <= 7.
  Proof.
    intros s D SN NI NG. pose proof (dcore_basics s D) as BB. pose proof D as [C I CL Ews Ehs Epbl].
    pose proof (dcore_fp_inv s D) as FP.
    destruct (flush_pending_inv ILEN OCAP tot0 PBL s FP CL (di_cty _ _ _ _ I))
      as (FP3 & CL3 & T3 & B3 & V3 & FL3 & KP3 & N3a & N3b & N3c & N3d & N3e & N3f & N3g & N3h & N3i & EP3).
    cbv zeta.
    generalize FP3 CL3 T3 B3 V3 FL3 KP3 N3a N3b N3c N3d N3e N3f N3g N3h N3i EP3. generalize (flush_pending s).
    clear FP3 CL3 T3 B3 V3 FL3 KP3 N3a N3b N3c N3d N3e N3f N3g N3h N3i EP3.
    intros s3 FP3 CL3 T3 B3 V3 FL3 KP3 N3a N3b N3c N3d N3e N3f N3g N3h N3i EP3.
    pose proof (ep_shape _ _ EP3) as SH. dsr in SH.
    assert (SH3 : s3 = set_pending_out (set_strm
              (set_bi_valid (set_bi_buf (set_pending (set_pending_buf s (ds_pending_buf s3)) (ds_pending s3)) (ds_bi_buf s3)) (ds_bi_valid s3))
              (ds_strm s3)) (ds_pending_out s3)).
    { rewrite <- SH. symmetry. apply spo_self. }
    pose proof (di_syms _ _ _ _ I) as (sy & Dy & Cv).
    assert (sy = []) as -> by (pose proof (sy_next _ _ Dy) as X; rewrite SN in X; destruct sy; [reflexivity | cbn in X; lia]).
    pose proof (dsyms_nil_ep _ _ Dy EP3) as Dy'.
    remember (ds_pending_buf s3) as pb3 eqn:Q1. remember (ds_pending s3) as p3 eqn:Q2. remember (ds_bi_buf s3) as bb3 eqn:Q3.
    remember (ds_bi_valid s3) as bv3 eqn:Q4. remember (ds_strm s3) as st3 eqn:Q5. remember (ds_pending_out s3) as po3 eqn:Q6.
    clear Q1 Q2 Q3 Q4 Q5 Q6. subst s3.
    dsr in FL3. dsr in N3a. dsr in N3b. dsr in N3i. dsr in B3. dsr in KP3.
    destruct FP3 as [[A3 Bb3 C3] Hpo3 HV3 HPBL3 Hpo03 _]. unfold bvol in HV3.
    dsr in A3. dsr in Bb3. dsr in C3. dsr in Hpo3. dsr in HV3. dsr in Hpo03.
    split.
    { constructor; dsr; try assumption.
      - apply (dcfg_kproj _ _ KP3). apply dcfg_set_pending_out, dcfg_set_strm. exact C.
      - destruct I; constructor; dsr; try assumption.
        all: try (exists (@nil (Z * Z)); split; [eapply dsyms_keep; [exact Dy' | dsr; reflexivity ..] | dsr; exact Cv]).
        all: try (rewrite Epbl; clear -HV3; lia).
        all: try (intros X; exfalso; destruct X as [X|X]; [exact (NI X) | exact (NG X)]).
        all: try (intros _; exact SN).
        all: try (intros _; clear -B3; lia). }
    split; [exact FL3|]. split; [exact Hpo03|].
    repeat (split; [first [reflexivity | exact SN | exact N3b | exact N3i] |]).
    exact B3.
  Qed.

  Lemma dcore_set_adler : forall s a, dcore s -> 0 <= a < 2 ^ 32 ->
    (ds_wrap s = 1 -> adler_ok a) -> (ds_wrap s = 2 -> 0 <= a < 2 ^ 32) ->
    dcore (set_strm s (cset_adler (ds_strm s) a)).
  Proof.
    intros s a [C I CL Ews Ehs Epbl] Ha A1 A2. constructor; dsr; try assumption.
    - apply dcfg_set_strm. exact C.
    - dinv_xfer I. apply cty_set_strm_in; [assumption | reflexivity].
    - destruct CL; constructor; dsr; assumption.
  Qed.

  Lemma dcore_negwrap : forall s, dcore s -> ds_status s = FINISH_STATE -> 0 < ds_wrap s -> dcore (set_wrap s (- ds_wrap s)).
  Proof.
    intros s [C I CL Ews Ehs Epbl] SF W. pose proof (di_finlook _ _ _ _ I SF) as [L0 SN0].
    constructor; dsr; try assumption.
    - destruct C; constructor; dsr; try assumption. lia.
    - dinv_xfer I.
      + apply cty_set_wrap. assumption.
      + rewrite SF. intros [X|X]; discriminate X.
      + rewrite SF. intros X; discriminate X.
      + intros _. split; [exact SF | exact L0].
      + rewrite SF. intros X; discriminate X.
    - destruct CL; constructor; dsr; try assumption; intros X; exfalso; lia.
  Qed.

  Lemma dcore_clear_hash : forall s, dcore s ->
    dcore (clear_hash s) /\ (forall h, 0 <= h < ds_hash_size s -> arr_get (ds_head (clear_hash s)) h = 0).
  Proof.
    intros s D. pose proof D as [C I CL Ews Ehs Epbl].
    assert (HZ : forall h, 0 <= h < ds_hash_size s -> arr_get (ds_head (clear_hash s)) h = 0).
    { intros h Hh. apply clear_hash_head0; [exact (cf_hl _ C) | exact Hh]. }
    split; [| exact HZ].
    pose proof (cty_clear_hash s (di_cty _ _ _ _ I)) as T'.
    generalize HZ T'. unfold clear_hash. dsr. intros HZ' T''.
    constructor; dsr; try assumption.
    - destruct C; constructor; dsr; try assumption. rewrite arr_len_fill, arr_len_set. assumption.
    - dinv_xfer I. intros Lz. exists (fun _ : Z => False). rewrite Z.add_0_r. apply hc_inv_empty. exact HZ'.
    - destruct CL; constructor; dsr; assumption.
  Qed.

  Lemma dcore_reset0 : forall s, dcore s -> ds_lookahead s = 0 -> ds_match_available s = 0 ->
    (forall h, 0 <= h < ds_hash_size s -> arr_get (ds_head s) h = 0) ->
    dcore (set_insert (set_block_start (set_strstart s 0) 0) 0).
  Proof.
    intros s [C I CL Ews Ehs Epbl] L0 MA HZ. pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    constructor; dsr; try assumption.
    - apply dcfg_set_insert, dcfg_set_block_start, dcfg_set_strstart. exact C.
    - pose proof (di_syms _ _ _ _ I) as (sy & Dy & Cv). pose proof (zcov_nonneg sy (sy_valid _ _ Dy)) as ZC.
      destruct I; constructor; dsr; try assumption.
      all: try (clear; lia).
      all: try (rewrite MA; intros X; discriminate X).
      all: try (intros Lz; exists (fun _ : Z => False); rewrite Z.add_0_r; apply hc_inv_empty; exact HZ).
      all: try (exists sy; split; [eapply dsyms_keep; [exact Dy | dsr; reflexivity ..] | dsr]; intros _; rewrite MA; clear -ZC; lia).
      all: try (apply cty_set_insert; apply cty_set_block_start; apply cty_set_strstart; assumption).
      all: try (rewrite L0; clear -Sw; lia).
      all: try (intros _; clear; lia).
      all: intros Fz A B M; exfalso; destruct (di_slow Fz A B M) as (_ & _ & X); rewrite L0 in X; unfold MIN_MATCH in M; clear -X M; lia.
    - destruct CL; constructor; dsr; assumption.
  Qed.

  Lemma dcore_drun : forall s, dcore s -> ds_pending s = 0 -> ds_pending_out s = 0 -> ds_status s = BUSY_STATE -> ds_level s <> 0 ->
    drunR 3 0 true ws hs PBL ILEN OCAP tot0 s.
  Proof.
    intros s [C I CL Ews Ehs Epbl] P0 PO0 SB LZ. split; [| exact P0 | exact PO0].
    constructor; try assumption.
    - destruct (Z.lt_ge_cases (ds_wrap s) 0) as [W|W]; [| lia]. exfalso. pose proof (di_negwrap _ _ _ _ I W) as [X _]. rewrite SB in X. discriminate X.
    - intros _. split; assumption.
  Qed.

  Lemma dcore_dsr0 : forall s, dcore s -> ds_pending s = 0 -> ds_pending_out s = 0 -> ds_status s = BUSY_STATE -> ds_level s = 0 ->
    dsr0 ws hs PBL ILEN OCAP tot0 s.
  Proof.
    intros s [C I CL Ews Ehs Epbl] P0 PO0 SB LZ. split; [| exact P0 | exact PO0].
    constructor; try assumption.
    destruct (Z.lt_ge_cases (ds_wrap s) 0) as [W|W]; [| lia]. exfalso. pose proof (di_negwrap _ _ _ _ I W) as [X _]. rewrite SB in X. discriminate X.
  Qed.

  Lemma dpost_dcore : forall s, dpostR 3 0 true ws hs PBL ILEN OCAP tot0 s -> dcore s.
  Proof. intros s [C I CL Ews Ehs Epbl _ _ _ _]. constructor; assumption. Qed.

  Lemma dst_dcore : forall s, dst ws hs PBL ILEN OCAP tot0 s -> dcore s.
  Proof. intros s [C I CL Ews Ehs Epbl _ _ _]. constructor; assumption. Qed.


  Variable flush : Z.
  Hypothesis Hflush : 0 <= flush < 16.

  Definition ZB (s : deflate_state) : Prop := dcore s /\ ds_pending s = 0 /\ ds_pending_out s = 0.

  Lemma f1_inv : forall s, dcore s ->
    match f1_spec s flush with
    | Some (s', rc) => dcore s' /\ (rc = Z_STREAM_ERROR \/ rc = Z_BUF_ERROR)
    | None => flush <= 5 /\ cs_avail_out (ds_strm s) <> 0 /\ (ds_status s = FINISH_STATE -> flush = Z_FINISH)
    end.
  Proof.
    intros s D. rewrite (f1_spec_eq flush s (dcore_status_ok s D) ltac:(lia)).
    destruct (Z.ltb_spec 5 flush) as [F5|F5]; [split; [exact D | left; reflexivity]|].
    destruct (Z.eqb_spec (ds_status s) FINISH_STATE) as [SF|SF]; destruct (Z.eqb_spec flush Z_FINISH) as [FF|FF]; cbn [andb negb].
    2: { split; [apply dcore_msg; exact D | left; reflexivity]. }
    all: destruct (Z.eqb_spec (cs_avail_out (ds_strm s)) 0) as [A0|A0]; [split; [apply dcore_msg; exact D | right; reflexivity]|].
    all: split; [lia|]; split; [exact A0|]; intros X; first [exact FF | exfalso; exact (SF X)].
  Qed.

  Definition F2K (s s' : deflate_state) : Prop :=
    cs_avail_out (ds_strm s') <= cs_avail_out (ds_strm s) /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s).

  Lemma f2_inv : forall s, dcore s -> flush <= 5 -> cs_avail_out (ds_strm s) <> 0 ->
    f2_ok PBL OCAP flush s
    /\ match f2_spec s flush with
       | F2Ret s' rc => dcore s' /\ (rc = Z_OK \/ rc = Z_BUF_ERROR) /\ (rc = Z_OK -> cs_avail_out (ds_strm s') = 0)
       | F2Hdr s' => ZB s' /\ ds_status s' <> FINISH_STATE /\ cs_avail_out (ds_strm s') <> 0 /\ F2K s s'
       | F2Fin s' => ZB s' /\ ds_status s' = FINISH_STATE /\ cs_avail_in (ds_strm s') = 0 /\ cs_avail_out (ds_strm s') <> 0 /\ F2K s s'
       end.
  Proof.
    intros s D F5 A0. pose proof (dcore_basics s D) as BB. pose proof D as [C I CL Ews Ehs Epbl].
    pose proof (dcore_set_last_flush s flush D ltac:(lia)) as D1.
    remember (set_last_flush s flush) as s1 eqn:Es1.
    assert (E1 : ds_pending s1 = ds_pending s /\ ds_status s1 = ds_status s /\ ds_strm s1 = ds_strm s /\ ds_sym_next s1 = ds_sym_next s
                 /\ ds_pending_out s1 = ds_pending_out s) by (subst s1; dsr; repeat split; reflexivity).
    destruct E1 as (E1p & E1s & E1m & E1n & E1o).
    assert (FL : ds_pending s <> 0 ->
      let s2 := flush_pending s1 in
      fp_ok PBL OCAP s1 /\ dcore s2 /\ (cs_avail_out (ds_strm s2) <> 0 -> ds_pending s2 = 0 /\ ds_pending_out s2 = 0)
      /\ ds_status s2 = ds_status s /\ cs_avail_in (ds_strm s2) = cs_avail_in (ds_strm s)
      /\ cs_avail_out (ds_strm s2) <= cs_avail_out (ds_strm s)).
    { intros P. pose proof (di_pendsym _ _ _ _ I P) as SN.
      assert (NIG : ds_status s <> INIT_STATE /\ ds_status s <> GZIP_STATE).
      { split; intros X; apply P; exact (proj1 (di_init _ _ _ _ I ltac:(first [left; exact X | right; exact X]))). }
      destruct NIG as [NI NG].
      destruct (dcore_fp s1 D1 ltac:(rewrite E1n; exact SN) ltac:(rewrite E1s; exact NI) ltac:(rewrite E1s; exact NG))
        as (D2 & FL2 & PO2 & ST2 & _ & _ & _ & _ & _ & _ & AI2 & AO2 & _).
      cbv zeta. split; [exact (dcore_fp_ok s1 D1)|]. split; [exact D2|]. split; [exact FL2|]. rewrite ST2, AI2, E1s, E1m. rewrite E1m in AO2.
      split; [reflexivity|]. split; [reflexivity | exact AO2]. }
    split.
    {
      unfold f2_ok. rewrite <- Es1. pose proof (dcore_status_range s D).
      repeat (split; [clear FL; lia|]). intros P. destruct (FL P) as (OK & D2 & _ & ST2 & AI2 & _). cbv zeta in ST2, AI2.
      pose proof (dcore_basics _ D2) as BB2. pose proof (dcore_status_range _ D2).
      split; [exact OK|]. clear FL. repeat split; lia. }
    unfold f2_spec. rewrite <- Es1. rewrite E1p.
    destruct (Z.eqb_spec (ds_pending s) 0) as [P0|P0]; cbn [negb].
    -
      assert (Z1 : ZB s1) by (split; [exact D1|]; rewrite E1p, E1o; split; [exact P0 | exact (di_po0 _ _ _ _ I P0)]).
      assert (K1 : F2K s s1) by (unfold F2K; rewrite E1m; split; [lia | reflexivity]).
      assert (NOK : Z_BUF_ERROR = Z_OK -> forall st, cs_avail_out st = 0) by (intros X; discriminate X).
      destruct ((cs_avail_in (ds_strm s1) =? 0) && (RANK flush <=? RANK (ds_last_flush s)) && negb (flush =? Z_FINISH)).
      + unfold err_return. split; [apply dcore_msg; exact D1 | split; [right; reflexivity | intros X; exact (NOK X _)]].
      + rewrite E1s, E1m.
        destruct (Z.eqb_spec (ds_status s) FINISH_STATE) as [SF|SF]; destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [AI|AI]; cbn [andb negb].
        * split; [exact Z1|]. rewrite E1s, E1m. split; [exact SF|]. split; [exact AI|]. split; [exact A0 | exact K1].
        * unfold err_return. split; [apply dcore_msg; exact D1 | split; [right; reflexivity | intros X; exact (NOK X _)]].
        * split; [exact Z1|]. rewrite E1s, E1m. split; [exact SF|]. split; [exact A0 | exact K1].
        * split; [exact Z1|]. rewrite E1s, E1m. split; [exact SF|]. split; [exact A0 | exact K1].
    -
      destruct (FL P0) as (_ & D2 & FL2 & ST2 & AI2 & AO2). cbv zeta in D2, FL2, ST2, AI2, AO2.
      remember (flush_pending s1) as s2 eqn:Es2.
      assert (K2 : F2K s s2) by (unfold F2K; split; [exact AO2 | exact AI2]).
      assert (NOK : Z_BUF_ERROR = Z_OK -> forall st, cs_avail_out st = 0) by (intros X; discriminate X).
      destruct (Z.eqb_spec (cs_avail_out (ds_strm s2)) 0) as [A2|A2].
      + split; [apply dcore_set_last_flush; [exact D2 | lia] | split; [left; reflexivity | intros _; dsr; exact A2]].
      + destruct (FL2 A2) as [P2 PO2].
        assert (Z2 : ZB s2) by (split; [exact D2 | split; assumption]).
        rewrite ST2, AI2.
        destruct (Z.eqb_spec (ds_status s) FINISH_STATE) as [SF|SF]; destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [AI|AI]; cbn [andb negb].
        * split; [exact Z2|]. rewrite ST2, AI2. split; [exact SF|]. split; [exact AI|]. split; [exact A2 | exact K2].
        * unfold err_return. split; [apply dcore_msg; exact D2 | split; [right; reflexivity | intros X; exact (NOK X _)]].
        * split; [exact Z2|]. rewrite ST2. split; [exact SF|]. split; [exact A2 | exact K2].
        * split; [exact Z2|]. rewrite ST2. split; [exact SF|]. split; [exact A2 | exact K2].
  Qed.

  Lemma dcore_put_bytes : forall cs s, dcore s -> ds_sym_next s = 0 ->
    ds_status s <> INIT_STATE -> ds_status s <> GZIP_STATE ->
    8 * (ds_pending_out s + ds_pending s + zlength cs) + ds_bi_valid s <= 8 * PBL ->
    let x := fold_left put_byte cs s in
    dcore x /\ ds_pending x = ds_pending s + zlength cs /\ ds_bi_valid x = ds_bi_valid s
    /\ ds_pending_out x = ds_pending_out s /\ ds_sym_next x = 0
    /\ ds_status x = ds_status s /\ ds_strm x = ds_strm s /\ ds_wrap x = ds_wrap s.
  Proof.
    induction cs as [|c cs IH]; intros s D SN NI NG R; cbv zeta.
    - cbn [fold_left]. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r. split; [exact D|]. repeat split; try reflexivity. exact SN.
    - cbn [fold_left]. rewrite zlength_cons' in *.
      assert (L0 : 0 <= zlength cs) by apply Zle_0_nat.
      destruct (dcore_put_byte s c D SN NI NG ltac:(lia)) as (D1 & P1 & V1 & PO1 & SN1 & ST1 & SM1 & W1).
      destruct (IH (put_byte s c) D1 SN1 ltac:(rewrite ST1; exact NI) ltac:(rewrite ST1; exact NG) ltac:(rewrite PO1, P1, V1; lia))
        as (D2 & P2 & V2 & PO2 & SN2 & ST2 & SM2 & W2).
      cbv zeta in *. rewrite P2, V2, PO2, ST2, SM2, W2, P1, V1, PO1, ST1, SM1, W1.
      split; [exact D2|]. repeat split; try reflexivity; try lia.
  Qed.

  Lemma dcore_set_adler' : forall s st a, dcore s -> st = ds_strm s -> 0 <= a < 2 ^ 32 ->
    (ds_wrap s = 1 -> adler_ok a) -> (ds_wrap s = 2 -> 0 <= a < 2 ^ 32) ->
    dcore (set_strm s (cset_adler st a)).
  Proof. intros s st a D -> Ha A1 A2. exact (dcore_set_adler s a D Ha A1 A2). Qed.

  Lemma zlib_inv : forall s, ZB s -> ds_status s = INIT_STATE -> ds_wrap s <> 0 ->
    zlib_ok PBL OCAP s
    /\ let s' := flush_pending (zlib_s3_spec s) in
       dcore s' /\ ds_status s' = BUSY_STATE /\ (ds_pending s' = 0 -> ds_pending_out s' = 0)
       /\ (cs_avail_out (ds_strm s') <> 0 -> ds_pending s' = 0 /\ ds_pending_out s' = 0) /\ F2K s s'.
  Proof.
    intros s (D & P0 & PO0) SI W. pose proof D as [C I CL Ews Ehs Epbl]. pose proof (dcore_basics s D) as BB.
    destruct (di_init _ _ _ _ I (or_introl SI)) as (_ & W0 & SN). pose proof (di_initw _ _ _ _ I SI) as W1.
    assert (WR : ds_wrap s = 1) by lia. pose proof (dc_ad1 _ _ _ _ CL WR) as AD. pose proof AD as [AD1 _].
    unfold zlib_ok, zlib_emit. change (zlib_s3_spec s) with (zl_s3_raw s (zhdr s)). set (h := zhdr s).
    unfold zl_s3_raw. cbv zeta. rewrite (ep_strstart _ _ (ep_putShortMSB s h)), !strm_putShortMSB.
    match goal with |- context [cset_adler (ds_strm ?X) adler32_init] =>
      replace (ds_strm X) with (ds_strm s) by (destruct (negb (ds_strstart s =? 0)); rewrite ?strm_putShortMSB; reflexivity) end.
    rewrite <- !set_strm_set_status, !if_set_status, <- !putShortMSB_set_status.
    pose proof (dcore_set_status s BUSY_STATE D (or_introl (conj eq_refl W0))) as D0.
    remember (set_status s BUSY_STATE) as s0 eqn:Es0.
    assert (F0 : ds_pending s0 = 0 /\ ds_pending_out s0 = 0 /\ ds_sym_next s0 = 0 /\ ds_status s0 = BUSY_STATE /\ ds_strm s0 = ds_strm s
                 /\ ds_wrap s0 = 1 /\ ds_bi_valid s0 = ds_bi_valid s)
      by (subst s0; dsr; repeat split; first [assumption | reflexivity]).
    destruct F0 as (P0' & PO0' & SN0 & ST0 & SM0 & W0' & BV0).
    assert (NI0 : ds_status s0 <> INIT_STATE) by (rewrite ST0; discriminate).
    assert (NG0 : ds_status s0 <> GZIP_STATE) by (rewrite ST0; discriminate).
    lazymatch goal with |- context [flush_pending (set_strm ?X (cset_adler _ adler32_init))] =>
      assert (F2 : dcore X /\ ds_pending X <= 6 /\ ds_bi_valid X = ds_bi_valid s /\ ds_pending_out X = 0 /\ ds_sym_next X = 0
                   /\ ds_status X = BUSY_STATE /\ ds_strm X = ds_strm s /\ ds_wrap X = 1 /\ 0 <= ds_pending X);
      [| remember X as s2 eqn:Es2; clear Es2 ] end.
    { destruct (dcore_putShortMSB s0 h D0 SN0 NI0 NG0 ltac:(rewrite PO0', P0', BV0; clear -BB; lia)) as (D1 & P1 & V1 & PO1 & SN1 & ST1 & SM1 & WW1).
      destruct (negb (ds_strstart s =? 0)).
      - destruct (dcore_putShortMSB _ (wrap32 (Z.shiftr (cs_adler (ds_strm s)) 16)) D1 SN1 ltac:(rewrite ST1; exact NI0) ltac:(rewrite ST1; exact NG0)
                   ltac:(rewrite PO1, P1, V1, PO0', P0', BV0; clear -BB; lia)) as (D2 & P2 & V2 & PO2 & SN2 & ST2 & SM2 & WW2).
        destruct (dcore_putShortMSB _ (Z.land (cs_adler (ds_strm s)) 65535) D2 SN2 ltac:(rewrite ST2, ST1; exact NI0) ltac:(rewrite ST2, ST1; exact NG0)
                   ltac:(rewrite PO2, P2, V2, PO1, P1, V1, PO0', P0', BV0; clear -BB; lia)) as (D3 & P3 & V3 & PO3 & SN3 & ST3 & SM3 & WW3).
        rewrite P3, V3, PO3, ST3, SM3, WW3, P2, V2, PO2, ST2, SM2, WW2, P1, V1, PO1, ST1, SM1, WW1, P0', PO0', BV0, ST0, SM0, W0'.
        split; [exact D3|]. repeat split; try reflexivity; try (clear; lia); try exact SN3.
      - rewrite P1, V1, PO1, ST1, SM1, WW1, P0', PO0', BV0, ST0, SM0, W0'.
        split; [exact D1|]. repeat split; try reflexivity; try (clear; lia); try exact SN1. }
    destruct F2 as (D2 & P2 & V2 & PO2 & SN2 & ST2 & SM2 & WW2 & Pge2).
    pose proof (dcore_set_adler' s2 (ds_strm s) adler32_init D2 (eq_sym SM2) ltac:(unfold adler32_init; lia)
                  ltac:(intros _; exact adler_ok_init) ltac:(intros _; unfold adler32_init; lia)) as D3.
    remember (set_strm s2 (cset_adler (ds_strm s) adler32_init)) as s3 eqn:Es3.
    assert (F3 : ds_pending s3 = ds_pending s2 /\ ds_pending_out s3 = 0 /\ ds_sym_next s3 = 0 /\ ds_status s3 = BUSY_STATE
                 /\ ds_bi_valid s3 = ds_bi_valid s
                 /\ cs_avail_in (ds_strm s3) = cs_avail_in (ds_strm s) /\ cs_avail_out (ds_strm s3) = cs_avail_out (ds_strm s))
      by (subst s3; dsr; repeat split; first [assumption | reflexivity]).
    destruct F3 as (P3 & PO3 & SN3 & ST3 & BV3 & AI3 & AO3).
    destruct (dcore_fp s3 D3 SN3 ltac:(rewrite ST3; discriminate) ltac:(rewrite ST3; discriminate))
      as (D4 & FL4 & PO4 & ST4 & _ & _ & _ & _ & _ & _ & AI4 & AO4 & _).
    cbv zeta in *. pose proof (dcore_basics _ D4) as BB4. pose proof (dcore_status_range _ D4) as SR4.
    split.
    - split.
      + unfold zlib_pre. pose proof (cf_wbits _ C). rewrite P0. clear -BB H AD1. lia.
      + split; [exact (dcore_fp_ok s3 D3)|]. clear -BB4 SR4. lia.
    - split; [exact D4|]. split; [rewrite ST4; exact ST3|]. split; [exact PO4|]. split; [exact FL4|].
      unfold F2K. clear -AI3 AO3 AI4 AO4. split; lia.
  Qed.

  Lemma gzip_inv : forall s, ZB s -> ds_status s = GZIP_STATE ->
    gzip_ok PBL OCAP s
    /\ let s' := flush_pending (gzip_s3_spec s) in
       dcore s' /\ ds_status s' = BUSY_STATE /\ (ds_pending s' = 0 -> ds_pending_out s' = 0)
       /\ (cs_avail_out (ds_strm s') <> 0 -> ds_pending s' = 0 /\ ds_pending_out s' = 0) /\ F2K s s'.
  Proof.
    intros s (D & P0 & PO0) SG. pose proof D as [C I CL Ews Ehs Epbl]. pose proof (dcore_basics s D) as BB.
    destruct (di_init _ _ _ _ I (or_intror SG)) as (_ & W0 & SN). pose proof (di_gz _ _ _ _ I SG) as W2.
    unfold gzip_ok, gzip_emit. rewrite gzip_s3_spec_eq. unfold gz_s3, gz_s2, gz_s1.
    rewrite <- !put_byte_set_status, <- set_strm_set_status.
    pose proof (dcore_set_status s BUSY_STATE D (or_introl (conj eq_refl W0))) as D0.
    remember (set_status s BUSY_STATE) as s0 eqn:Es0.
    assert (F0 : ds_pending s0 = 0 /\ ds_pending_out s0 = 0 /\ ds_sym_next s0 = 0 /\ ds_status s0 = BUSY_STATE /\ ds_strm s0 = ds_strm s
                 /\ ds_wrap s0 = 2 /\ ds_bi_valid s0 = ds_bi_valid s)
      by (subst s0; dsr; repeat split; first [assumption | reflexivity]).
    destruct F0 as (P0' & PO0' & SN0 & ST0 & SM0 & W0' & BV0).
    pose proof (dcore_set_adler' s0 (ds_strm s) crc32_init D0 (eq_sym SM0) ltac:(unfold crc32_init; lia)
                  ltac:(intros X; exfalso; clear -X W0'; lia) ltac:(intros _; unfold crc32_init; lia)) as D1.
    remember (set_strm s0 (cset_adler (ds_strm s) crc32_init)) as s1 eqn:Es1.
    assert (F1 : ds_pending s1 = 0 /\ ds_pending_out s1 = 0 /\ ds_sym_next s1 = 0 /\ ds_status s1 = BUSY_STATE /\ ds_bi_valid s1 = ds_bi_valid s
                 /\ cs_avail_in (ds_strm s1) = cs_avail_in (ds_strm s) /\ cs_avail_out (ds_strm s1) = cs_avail_out (ds_strm s))
      by (subst s1; dsr; repeat split; first [assumption | reflexivity]).
    destruct F1 as (P1 & PO1 & SN1 & ST1 & BV1 & AI1 & AO1).
    lazymatch goal with |- context [flush_pending ?X] =>
      change X with (fold_left put_byte [31; 139; 8; 0; 0; 0; 0; 0; gz_xfl s; OS_CODE] s1) end.
    destruct (dcore_put_bytes [31; 139; 8; 0; 0; 0; 0; 0; gz_xfl s; OS_CODE] s1 D1 SN1 ltac:(rewrite ST1; discriminate) ltac:(rewrite ST1; discriminate)
                ltac:(rewrite PO1, P1, BV1; change (zlength _) with 10; clear -BB; lia)) as (D2 & P2 & V2 & PO2 & SN2 & ST2 & SM2 & WW2).
    cbv zeta in *. change (zlength _) with 10 in P2.
    remember (fold_left put_byte [31; 139; 8; 0; 0; 0; 0; 0; gz_xfl s; OS_CODE] s1) as s2 eqn:Es2. clear Es2.
    destruct (dcore_fp s2 D2 SN2 ltac:(rewrite ST2, ST1; discriminate) ltac:(rewrite ST2, ST1; discriminate))
      as (D4 & FL4 & PO4 & ST4 & _ & _ & _ & _ & _ & _ & AI4 & AO4 & _).
    cbv zeta in *. pose proof (dcore_basics _ D4) as BB4.
    split.
    - split.
      + unfold gzip_pre. pose proof (cf_gzhead _ C). rewrite P0. clear -BB H. lia.
      + split; [exact (dcore_fp_ok s2 D2)|]. clear -BB4. lia.
    - split; [exact D4|]. split; [rewrite ST4, ST2; exact ST1|]. split; [exact PO4|]. split; [exact FL4|].
      unfold F2K. rewrite SM2 in AI4, AO4. clear -AI1 AO1 AI4 AO4. split; lia.
  Qed.

  Lemma f3_inv : forall s, ZB s -> ds_status s <> FINISH_STATE ->
    f3_ok PBL OCAP s /\ b4_ok (fst (f3_spec s))
    /\ let '(s', r) := f3_spec s in
       match r with
       | Some rc => dcore s' /\ rc = Z_OK /\ cs_avail_out (ds_strm s') = 0
       | None => ZB s' /\ ds_status s' = BUSY_STATE /\ F2K s s'
       end.
  Proof.
    intros s Z NF. pose proof Z as (D & P0 & PO0). pose proof D as [C I CL Ews Ehs Epbl]. pose proof (dcore_basics s D) as BB.
    pose proof (dcore_status_range s D) as SR. pose proof (di_live _ _ _ _ I) as LV.
    split.
    { unfold f3_ok. split; [exact SR|]. split; [clear -BB; lia|]. split; [clear -BB; lia|]. split; [exact LV|].
      split; [intros SI W; exact (proj1 (zlib_inv s Z SI W)) | intros SG; exact (proj1 (gzip_inv s Z SG))]. }
    assert (NXT : forall s4 : deflate_state, (cs_avail_out (ds_strm s4) <> 0 -> ds_pending s4 = 0 /\ ds_pending_out s4 = 0) ->
                  ds_pending s4 <> 0 -> cs_avail_out (ds_strm (set_last_flush s4 (-1))) = 0).
    { intros s4 FL4 P4. dsr. destruct (Z.eq_dec (cs_avail_out (ds_strm s4)) 0) as [A|A]; [exact A | exfalso; exact (P4 (proj1 (FL4 A)))]. }
    assert (KS : F2K s s) by (unfold F2K; split; [lia | reflexivity]).
    assert (POST : let '(s', r) := f3_spec s in
                   match r with Some rc => dcore s' /\ rc = Z_OK /\ cs_avail_out (ds_strm s') = 0 | None => ZB s' /\ ds_status s' = BUSY_STATE /\ F2K s s' end).
    { unfold f3_spec.
      destruct (dcore_status4 s D) as [SI | [SG | [SB | SF]]].
      - rewrite SI, Z.eqb_refl. destruct (Z.eqb_spec (ds_wrap s) 0) as [W|W]; cbn [andb].
        + assert (W0 : 0 <= ds_wrap s) by (rewrite W; lia).
          pose proof (dcore_set_status s BUSY_STATE D (or_introl (conj eq_refl W0))) as D1.
          remember (set_status s BUSY_STATE) as s1 eqn:Es1.
          assert (F1 : ds_status s1 = BUSY_STATE /\ ds_pending s1 = 0 /\ ds_pending_out s1 = 0 /\ ds_strm s1 = ds_strm s) by (subst s1; dsr; repeat split; assumption || reflexivity).
          destruct F1 as (ST1 & P1 & PO1 & SM1). rewrite ST1.
          replace (BUSY_STATE =? INIT_STATE) with false by reflexivity. cbv beta iota.
          rewrite ST1. replace (BUSY_STATE =? GZIP_STATE) with false by reflexivity. cbv beta iota.
          split; [split; [exact D1 | split; assumption] | split; [exact ST1 | unfold F2K; rewrite SM1; exact KS]].
        + rewrite SI, Z.eqb_refl. rewrite deflate_zlib_header_spec.
          destruct (zlib_inv s Z SI W) as (_ & D4 & ST4 & PO4 & FL4 & K4). cbv zeta in D4, ST4, PO4, FL4, K4. cbv zeta.
          remember (flush_pending (zlib_s3_spec s)) as s4 eqn:Es4.
          destruct (Z.eqb_spec (ds_pending s4) 0) as [P4|P4]; cbn [negb].
          * rewrite ST4. replace (BUSY_STATE =? GZIP_STATE) with false by reflexivity. cbv beta iota.
            split; [split; [exact D4 | split; [exact P4 | exact (PO4 P4)]] | split; [exact ST4 | exact K4]].
          * split; [apply dcore_set_last_flush; [exact D4 | lia] | split; [reflexivity | exact (NXT s4 FL4 P4)]].
      - rewrite SG. replace (GZIP_STATE =? INIT_STATE) with false by reflexivity. cbn [andb]. cbv beta iota.
        rewrite SG. replace (GZIP_STATE =? INIT_STATE) with false by reflexivity. cbv beta iota.
        rewrite SG, Z.eqb_refl. rewrite deflate_gzip_header_spec.
        destruct (gzip_inv s Z SG) as (_ & D4 & ST4 & PO4 & FL4 & K4). cbv zeta in D4, ST4, PO4, FL4, K4. cbv zeta.
        remember (flush_pending (gzip_s3_spec s)) as s4 eqn:Es4.
        destruct (Z.eqb_spec (ds_pending s4) 0) as [P4|P4]; cbn [negb].
        + split; [split; [exact D4 | split; [exact P4 | exact (PO4 P4)]] | split; [exact ST4 | exact K4]].
        + split; [apply dcore_set_last_flush; [exact D4 | lia] | split; [reflexivity | exact (NXT s4 FL4 P4)]].
      - rewrite SB. replace (BUSY_STATE =? INIT_STATE) with false by reflexivity. cbn [andb]. cbv beta iota.
        rewrite SB. replace (BUSY_STATE =? INIT_STATE) with false by reflexivity. cbv beta iota.
        rewrite SB. replace (BUSY_STATE =? GZIP_STATE) with false by reflexivity. cbv beta iota.
        split; [exact Z | split; [exact SB | exact KS]].
      - exfalso. exact (NF SF). }
    split; [| exact POST].
    destruct (f3_spec s) as [s' r]. destruct r; apply dcore_b4; [exact (proj1 POST) | exact (proj1 (proj1 POST))].
  Qed.

  Lemma bd_inv : forall s, ZB s -> ds_status s = BUSY_STATE -> ds_sym_next s = 0 -> ds_lookahead s = 0 -> ds_match_available s = 0 ->
    bd_ok PBL OCAP s flush
    /\ let s1 :=
         if Z.eqb flush Z_PARTIAL_FLUSH then tr_align s
         else if negb (Z.eqb flush Z_BLOCK) then
           let s := tr_stored_block s None 0 0 in
           if Z.eqb flush Z_FULL_FLUSH then
             let s := clear_hash s in
             if Z.eqb (ds_lookahead s) 0 then set_insert (set_block_start (set_strstart s 0) 0) 0 else s
           else s
         else s in
       let s2 := flush_pending s1 in
       dcore s2 /\ (cs_avail_out (ds_strm s2) <> 0 -> ds_pending s2 = 0 /\ ds_pending_out s2 = 0)
       /\ ds_sym_next s2 = 0 /\ ds_status s2 = BUSY_STATE.
  Proof.
    intros s Z SB SN L0 MA. pose proof Z as (D & P0 & PO0). pose proof D as [C I CL Ews Ehs Epbl]. pose proof (dcore_basics s D) as BB.
    pose proof (dcore_bits s D) as BI. pose proof (di_cty _ _ _ _ I) as T.
    unfold bd_ok. cbv zeta.
    assert (AL : forall P : deflate_state -> Prop,
              (forall a, dcore a -> ds_pending a <= PBL -> ds_sym_next a = 0 -> ds_status a = BUSY_STATE -> P a) -> P (tr_align s)).
    { intros P HP. destruct (tr_align_bits s BI) as (B1 & V1 & BV1 & P1). unfold bvol in V1. destruct B1 as [A1 Bb1 C1].
      pose proof (ep_tr_align s) as E. pose proof (cty_tr_align s T) as T1.
      revert E T1 A1 Bb1 C1 V1 BV1 P1. generalize (tr_align s) as a. intros a E T1 A1 Bb1 C1 V1 BV1 P1.
      apply HP.
      - apply (dcore_ep0 s a D SN E T1); try assumption.
        + rewrite PO0. clear -V1 BV1 P0 BB. lia.
        + intros X. exact PO0.
        + rewrite PO0. intros X. exfalso. exact (X eq_refl).
        + rewrite SB. intros [X|X]; discriminate X.
      - clear -P1 BB P0; lia.
      - rewrite (ep_sym_next _ _ E). exact SN.
      - rewrite (ep_status _ _ E). exact SB. }
    pattern (tr_align s). apply AL. intros sa Da Pa SNa STa.
    destruct (tsb0_facts s 0 T ltac:(clear -BB; lia) ltac:(clear -BB; lia) ltac:(clear -BB; lia) ltac:(lia)) as (T1 & E & BV1 & Bb1 & P1 & V1).
    revert T1 E BV1 Bb1 P1 V1. generalize (tr_stored_block s None 0 0) as st. intros st T1 E BV1 Bb1 P1 V1.
    assert (Dt : dcore st).
    { apply (dcore_ep0 s st D SN E T1); try assumption.
      - rewrite BV1. clear; lia.
      - clear -P1 P0; lia.
      - rewrite PO0, BV1. clear -V1 P0 BB. lia.
      - intros _. exact PO0.
      - rewrite PO0. intros X. exfalso. exact (X eq_refl).
      - rewrite SB. intros [X|X]; discriminate X. }
    pose proof (ep_sym_next _ _ E) as SNt. pose proof (ep_status _ _ E) as STt. pose proof (ep_lookahead _ _ E) as Lt.
    pose proof (ep_match_available _ _ E) as MAt. pose proof (ep_pending_out _ _ E) as POt. pose proof (ep_hash_size _ _ E) as HSt.
    rewrite SN in SNt. rewrite SB in STt. rewrite L0 in Lt. rewrite MA in MAt. rewrite PO0 in POt.
    assert (Pt : ds_pending st <= PBL) by (clear -P1 P0 BB; lia).
    clear T1 E BV1 Bb1 P1 V1.
    destruct (dcore_clear_hash st Dt) as [Dc HZ].
    pose proof (clear_hash_fields st) as (Pc & SNc & STc & Lc & MAc & POc & HSc).
    rewrite SNt in SNc. rewrite STt in STc. rewrite Lt in Lc. rewrite MAt in MAc. rewrite POt in POc.
    revert Dc HZ Pc SNc STc Lc MAc POc HSc. generalize (clear_hash st) as sc. intros sc Dc HZ Pc SNc STc Lc MAc POc HSc.
    rewrite Lc, Z.eqb_refl.
    pose proof (dcore_reset0 sc Dc Lc MAc ltac:(rewrite HSc; exact HZ)) as Dr.
    pose proof (reset0_fields sc) as (Pr & SNr & STr & POr). rewrite SNc in SNr. rewrite STc in STr. rewrite POc in POr.
    revert Dr Pr SNr STr POr. generalize (set_insert (set_block_start (set_strstart sc 0) 0) 0) as sr. intros sr Dr Pr SNr STr POr.
    lazymatch goal with |- (_ /\ _ /\ _ /\ fp_ok _ _ ?X /\ _) /\ _ =>
      assert (F1 : forall P : deflate_state -> Prop,
                (forall a, dcore a -> ds_sym_next a = 0 -> ds_status a = BUSY_STATE -> P a) -> P X) end.
    { intros P HP.
      destruct (Z.eqb_spec flush Z_PARTIAL_FLUSH) as [F1|F1]; [exact (HP sa Da SNa STa)|].
      destruct (negb (flush =? Z_BLOCK)); [| exact (HP s D SN SB)].
      destruct (Z.eqb_spec flush Z_FULL_FLUSH) as [F3|F3]; [exact (HP sr Dr SNr STr) | exact (HP st Dt SNt STt)]. }
    lazymatch goal with |- (_ /\ _ /\ _ /\ fp_ok _ _ ?X /\ _) /\ _ => pattern X end.
    apply F1. intros s1 D1 SN1 ST1.
    destruct (dcore_fp s1 D1 SN1 ltac:(rewrite ST1; discriminate) ltac:(rewrite ST1; discriminate)) as (D2 & FL2 & PO2 & ST2 & _ & SN2 & _).
    revert D2 FL2 PO2 ST2 SN2. generalize (flush_pending s1) as s2. intros s2 D2 FL2 PO2 ST2 SN2.
    split.
    - split; [intros _; split; [exact (dcore_BINV s D) | exact Pa]|].
      split; [intros _ _; split; [exact (dcore_BINV s D) | exact Pt]|].
      split; [intros _; exact (dcore_lzw sc Dc)|].
      split; [exact (dcore_fp_ok s1 D1)|]. pose proof (dcore_basics _ D2) as BB2. clear -BB2. lia.
    - split; [exact D2|]. split; [exact FL2|]. split; [exact SN2 | rewrite ST2; exact ST1].
  Qed.

  Definition CPROG (s s1 : deflate_state) : Prop :=
    cs_avail_out (ds_strm s1) = 0
    \/ (cs_avail_in (ds_strm s1) = 0 /\ flush = Z_NO_FLUSH)
    \/ (cs_avail_out (ds_strm s1) <= cs_avail_out (ds_strm s) /\ cs_avail_in (ds_strm s1) <= cs_avail_in (ds_strm s)
        /\ (0 < cs_avail_out (ds_strm s) -> (flush = Z_NO_FLUSH -> 0 < cs_avail_in (ds_strm s)) ->
            cs_avail_out (ds_strm s1) < cs_avail_out (ds_strm s) \/ cs_avail_in (ds_strm s1) < cs_avail_in (ds_strm s))).

  Definition CPOST (s s1 : deflate_state) (bs : block_state) : Prop :=
    dcore s1 /\ ds_status s1 = BUSY_STATE
    /\ (cs_avail_out (ds_strm s1) <> 0 -> ds_pending s1 = 0 /\ ds_pending_out s1 = 0)
    /\ match bs with
       | need_more => CPROG s s1
       | block_done => ds_pending s1 = 0 /\ ds_pending_out s1 = 0 /\ ds_sym_next s1 = 0 /\ ds_lookahead s1 = 0
                       /\ ds_match_available s1 = 0 /\ flush <> Z_FINISH /\ flush <> Z_NO_FLUSH
       | finish_started => ds_lookahead s1 = 0 /\ ds_sym_next s1 = 0 /\ flush = Z_FINISH /\ CPROG s s1
       | finish_done => ds_pending s1 = 0 /\ ds_pending_out s1 = 0 /\ ds_sym_next s1 = 0 /\ ds_lookahead s1 = 0 /\ flush = Z_FINISH
       end.

  Lemma bpost_cpost : forall s0 s1 bs, DeflInvFast.BPOST ws hs PBL ILEN OCAP tot0 flush s0 s1 bs -> CPOST s0 s1 bs.
  Proof.
    intros s0 s1 bs (P & _ & _ & R). unfold CPOST.
    split; [exact (dpost_dcore s1 P)|]. split; [exact (dp_status _ _ _ _ _ _ _ _ _ _ P)|]. split; [exact (dp_flush _ _ _ _ _ _ _ _ _ _ P)|].
    destruct bs.
    - unfold CPROG. destruct R as [A | [A F0]]; [left; exact A | right; left; split; [exact A | exact F0]].
    - destruct R as ([_ P1 PO1] & SN & L & NF & MA & NNF). repeat split; assumption.
    - destruct R as (L & F4 & SN & A). split; [exact L|]. split; [exact SN|]. split; [exact F4|]. unfold CPROG. left; exact A.
    - destruct R as ([_ P1 PO1] & SN & L & F4 & _). repeat split; assumption.
  Qed.

  Lemma cfunc_inv : forall s, ZB s -> ds_status s = BUSY_STATE -> flush <= 5 ->
    cfunc_ok ws hs PBL ILEN OCAP s flush /\ let '(s1, bs) := run_compress_func s flush in CPOST s s1 bs.
  Proof.
    intros s Z SB F5. pose proof Z as (D & P0 & PO0). pose proof D as [C I CL Ews Ehs Epbl].
    assert (HF : 0 <= flush <= 5) by lia.
    unfold cfunc_ok, run_compress_func.
    destruct (Z.eqb_spec (ds_level s) 0) as [L0|L0].
    - pose proof (dcore_dsr0 s D P0 PO0 SB L0) as DR.
      destruct (stored_run ws hs PBL ILEN OCAP tot0 flush s DR HF) as (OK & SP & SG).
      split; [exact OK|]. destruct (deflate_stored s flush) as [s1 bs].
      destruct SP as (ST1 & FL1 & R). pose proof ST1 as [C1 I1 CL1 Ews1 Ehs1 Epbl1 SB1 W1 L1].
      pose proof (di_sn0 _ _ _ _ I1 L1) as SN1. pose proof (di_look0 _ _ _ _ I1 L1) as LK1.
      assert (PG : bs = need_more \/ bs = finish_started -> CPROG s s1).
      { intros Hbs. destruct SG as (G1 & G2 & G3). unfold CPROG. right; right. split; [exact G1|]. split; [exact G2|]. exact (G3 Hbs). }
      unfold CPOST. split; [exact (dst_dcore s1 ST1)|]. split; [exact SB1|]. split; [exact FL1|].
      destruct bs.
      + exact (PG (or_introl eq_refl)).
      + destruct R as ([_ P1 PO1] & NF0 & NF4).
        assert (MA1 : ds_match_available s1 = 0).
        { destruct (Z.eq_dec (ds_match_available s1) 0) as [E|E]; [exact E|]. exfalso. pose proof (di_maslow _ _ _ _ I1 E) as [X _]. rewrite L1 in X. lia. }
        repeat split; assumption.
      + split; [exact LK1 | split; [exact SN1 | split; [exact R | exact (PG (or_intror eq_refl))]]].
      + destruct R as ([_ P1 PO1] & F4). repeat split; assumption.
    - pose proof (dcore_drun s D P0 PO0 SB L0) as DR. pose proof (cf_level _ C) as LV.
      destruct (Z.eqb_spec (ds_strategy s) Z_HUFFMAN_ONLY) as [SG2|SG2].
      { destruct (huff_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush s DR SG2) as [OK BP].
        split; [exact OK|]. destruct (deflate_huff s flush) as [s1 bs]. exact (bpost_cpost s s1 bs BP). }
      destruct (Z.eqb_spec (ds_strategy s) Z_RLE) as [SG3|SG3].
      { destruct (rle_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush s DR SG3) as [OK BP].
        split; [exact OK|]. destruct (deflate_rle s flush) as [s1 bs]. exact (bpost_cpost s s1 bs BP). }
      assert (LZS : lz_strat s) by (split; assumption).
      destruct (Z.leb_spec (ds_level s) 3) as [L3|L3].
      { destruct (fast_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush s DR ltac:(lia) LZS) as [OK BP].
        split; [exact OK|]. destruct (deflate_fast s flush) as [s1 bs]. exact (bpost_cpost s s1 bs BP). }
      { destruct (slow_run ws hs PBL ILEN OCAP tot0 TS TR HPBL flush s DR ltac:(lia) LZS) as [OK BP].
        split; [exact OK|]. destruct (deflate_slow s flush) as [s1 bs]. exact (bpost_cpost s s1 bs BP). }
  Qed.

  Lemma blocks_inv : forall s, ZB s -> ds_status s = BUSY_STATE -> flush <= 5 ->
    blocks_ok ws hs PBL ILEN OCAP s flush
    /\ let '(s2, r) := blocks_body s flush in
       dcore s2 /\ match r with
                   | Some rc => rc = Z_OK /\ CPROG s s2
                   | None => ds_pending s2 = 0 /\ ds_pending_out s2 = 0 /\ ds_sym_next s2 = 0
                             /\ (flush = Z_FINISH -> ds_status s2 = FINISH_STATE) /\ (flush <> Z_FINISH -> ds_status s2 = BUSY_STATE)
                             /\ flush <> Z_NO_FLUSH
                   end.
  Proof.
    intros s Z SB F5. pose proof Z as (D & P0 & PO0). pose proof (dcore_basics s D) as BB.
    destruct (cfunc_inv s Z SB F5) as [CF CP].
    unfold blocks_ok, blocks_body.
    destruct (run_compress_func s flush) as [s1 bs].
    destruct CP as (D1 & SB1 & FL1 & R). pose proof (dcore_basics s1 D1) as BB1.
    destruct bs; cbn [block_state_eqb orb]; cbv zeta.
    -
      split; [split; [clear -BB; lia|]; split; [clear -BB; lia|]; split; [exact CF|]; split; [intros _; clear -BB1; lia | intros X; discriminate X]|].
      split; [destruct (cs_avail_out (ds_strm s1) =? 0); [apply dcore_set_last_flush; [exact D1 | lia] | exact D1]|].
      split; [reflexivity|].
      lazymatch goal with |- CPROG _ ?x => replace (CPROG s x) with (CPROG s s1) by (unfold CPROG; destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity) end.
      exact R.
    -
      destruct R as (P1 & PO1 & SN1 & L1 & MA1 & NF & NNF).
      assert (Z1 : ZB s1) by (split; [exact D1 | split; assumption]).
      destruct (bd_inv s1 Z1 SB1 SN1 L1 MA1) as [BOK BP]. cbv zeta in BP. destruct BP as (D2 & FL2 & SN2 & ST2).
      split; [split; [clear -BB; lia|]; split; [clear -BB; lia|]; split; [exact CF|]; split; [intros X; discriminate X | intros _; exact BOK]|].
      lazymatch type of D2 with dcore (flush_pending ?X) =>
        revert D2 FL2 SN2 ST2; generalize (flush_pending X) as s2; intros s2 D2 FL2 SN2 ST2 end.
      destruct (Z.eqb_spec (cs_avail_out (ds_strm s2)) 0) as [A|A].
      + split; [apply dcore_set_last_flush; [exact D2 | lia] |]. split; [reflexivity|]. unfold CPROG. left. exact A.
      + destruct (FL2 A) as [P2 PO2]. split; [exact D2|]. split; [exact P2|]. split; [exact PO2|]. split; [exact SN2|].
        split; [intros F; exfalso; exact (NF F)|]. split; [intros _; exact ST2 | exact NNF].
    -
      destruct R as (L1 & SN1 & F4 & PG).
      pose proof (dcore_set_status s1 FINISH_STATE D1 (or_intror (conj eq_refl (conj L1 SN1)))) as D2.
      assert (BB2 : 0 <= cs_avail_out (ds_strm (set_status s1 FINISH_STATE)) < 2 ^ 32) by (dsr; clear -BB1; lia).
      split; [split; [clear -BB; lia|]; split; [clear -BB; lia|]; split; [exact CF|]; split; [intros _; exact BB2 | intros X; discriminate X]|].
      split; [destruct (cs_avail_out (ds_strm (set_status s1 FINISH_STATE)) =? 0); [apply dcore_set_last_flush; [exact D2 | lia] | exact D2]|].
      split; [reflexivity|].
      lazymatch goal with |- CPROG _ ?x => replace (CPROG s x) with (CPROG s s1) by (unfold CPROG; destruct (cs_avail_out (ds_strm (set_status s1 FINISH_STATE)) =? 0); reflexivity) end.
      exact PG.
    -
      destruct R as (P1 & PO1 & SN1 & L1 & F4).
      pose proof (dcore_set_status s1 FINISH_STATE D1 (or_intror (conj eq_refl (conj L1 SN1)))) as D2.
      split; [split; [clear -BB; lia|]; split; [clear -BB; lia|]; split; [exact CF|]; split; [intros X; discriminate X | intros X; discriminate X]|].
      split; [exact D2|]. dsr. split; [exact P1|]. split; [exact PO1|]. split; [exact SN1|].
      split; [intros _; reflexivity|]. split; [intros X; exfalso; exact (X F4)|]. intros X. rewrite X in F4. discriminate F4.
  Qed.

  Lemma trl_inv : forall s, ZB s -> ds_sym_next s = 0 -> ds_status s = FINISH_STATE -> 0 < ds_wrap s ->
    trl_emit PBL OCAP s
    /\ let '(s', rc) := deflate_trailer s in dcore s' /\ (rc = Z_OK \/ rc = Z_STREAM_END) /\ (rc = Z_OK -> cs_avail_out (ds_strm s') = 0).
  Proof.
    intros s Z SN SF W. pose proof Z as (D & P0 & PO0). pose proof D as [C I CL Ews Ehs Epbl]. pose proof (dcore_basics s D) as BB.
    assert (AD32 : 0 <= cs_adler (ds_strm s) < 2 ^ 32) by exact (dc_ad _ _ _ _ CL).
    assert (NI : ds_status s <> INIT_STATE) by (rewrite SF; discriminate).
    assert (NG : ds_status s <> GZIP_STATE) by (rewrite SF; discriminate).
    unfold trl_emit, deflate_trailer. cbv zeta.
    split.
    all: destruct (Z.eqb_spec (ds_wrap s) 2) as [W2|W2].
    all: lazymatch goal with |- context [flush_pending ?X] =>
      assert (F1 : forall P : deflate_state -> Prop,
        (forall a, dcore a -> ds_sym_next a = 0 -> ds_status a = FINISH_STATE -> ds_wrap a = ds_wrap s -> P a) -> P X);
      [ intros P HP
      | pattern X; apply F1; intros a Da SNa STa Wa;
        destruct (dcore_fp a Da SNa ltac:(rewrite STa; discriminate) ltac:(rewrite STa; discriminate)) as (D2 & FL2 & PO2 & ST2 & _ & SN2 & W2' & _);
        revert D2 FL2 PO2 ST2 SN2 W2'; generalize (flush_pending a) as s2; intros s2 D2 FL2 PO2 ST2 SN2 W2';
        pose proof (dcore_basics s2 D2) as BB2 ] end.
    - set (cs := [Z.land (cs_adler (ds_strm s)) 255; Z.land (Z.shiftr (cs_adler (ds_strm s)) 8) 255;
                  Z.land (Z.shiftr (cs_adler (ds_strm s)) 16) 255; Z.land (Z.shiftr (cs_adler (ds_strm s)) 24) 255;
                  Z.land (cs_total_in (ds_strm s)) 255; Z.land (Z.shiftr (cs_total_in (ds_strm s)) 8) 255;
                  Z.land (Z.shiftr (cs_total_in (ds_strm s)) 16) 255; Z.land (Z.shiftr (cs_total_in (ds_strm s)) 24) 255]).
      lazymatch goal with |- P ?X => change X with (fold_left put_byte cs s) end.
      destruct (dcore_put_bytes cs s D SN NI NG ltac:(rewrite P0, PO0; subst cs; change (zlength _) with 8; clear -BB; lia)) as (D1 & P1 & V1 & PO1 & SN1 & ST1 & SM1 & WW1).
      apply HP; [exact D1 | exact SN1 | rewrite ST1; exact SF | exact WW1].
    - split; [rewrite P0; clear -BB; lia|]. split; [exact (dcore_fp_ok a Da)|]. clear -BB2. lia.
    - destruct (dcore_putShortMSB s (wrap32 (Z.shiftr (cs_adler (ds_strm s)) 16)) D SN NI NG ltac:(rewrite P0, PO0; clear -BB; lia)) as (D1 & P1 & V1 & PO1 & SN1 & ST1 & SM1 & WW1).
      destruct (dcore_putShortMSB _ (Z.land (cs_adler (ds_strm s)) 65535) D1 SN1 ltac:(rewrite ST1; exact NI) ltac:(rewrite ST1; exact NG)
                  ltac:(rewrite P1, PO1, V1, P0, PO0; clear -BB; lia)) as (D2 & P2 & V2 & PO2 & SN2 & ST2 & SM2 & WW2).
      apply HP; [exact D2 | exact SN2 | rewrite ST2, ST1; exact SF | rewrite WW2; exact WW1].
    - split; [rewrite P0; clear -BB; lia|]. split; [exact (dcore_fp_ok a Da)|]. clear -BB2. lia.
    - set (cs := [Z.land (cs_adler (ds_strm s)) 255; Z.land (Z.shiftr (cs_adler (ds_strm s)) 8) 255;
                  Z.land (Z.shiftr (cs_adler (ds_strm s)) 16) 255; Z.land (Z.shiftr (cs_adler (ds_strm s)) 24) 255;
                  Z.land (cs_total_in (ds_strm s)) 255; Z.land (Z.shiftr (cs_total_in (ds_strm s)) 8) 255;
                  Z.land (Z.shiftr (cs_total_in (ds_strm s)) 16) 255; Z.land (Z.shiftr (cs_total_in (ds_strm s)) 24) 255]).
      lazymatch goal with |- P ?X => change X with (fold_left put_byte cs s) end.
      destruct (dcore_put_bytes cs s D SN NI NG ltac:(rewrite P0, PO0; subst cs; change (zlength _) with 8; clear -BB; lia)) as (D1 & P1 & V1 & PO1 & SN1 & ST1 & SM1 & WW1).
      apply HP; [exact D1 | exact SN1 | rewrite ST1; exact SF | exact WW1].
    - replace (0 <? ds_wrap s2) with true by (symmetry; apply Z.ltb_lt; rewrite W2', Wa; exact W).
      split; [apply dcore_negwrap; [exact D2 | rewrite ST2; exact STa | rewrite W2', Wa; exact W]|].
      replace (ds_pending (set_wrap s2 (- ds_wrap s2))) with (ds_pending s2) by reflexivity.
      replace (ds_strm (set_wrap s2 (- ds_wrap s2))) with (ds_strm s2) by reflexivity.
      destruct (Z.eqb_spec (ds_pending s2) 0) as [PZ|PZ]; cbn [negb].
      { split; [right; reflexivity | intros X; discriminate X]. }
      split; [left; reflexivity | intros _].
      destruct (Z.eq_dec (cs_avail_out (ds_strm s2)) 0) as [A|A]; [exact A | exfalso; exact (PZ (proj1 (FL2 A)))].
    - destruct (dcore_putShortMSB s (wrap32 (Z.shiftr (cs_adler (ds_strm s)) 16)) D SN NI NG ltac:(rewrite P0, PO0; clear -BB; lia)) as (D1 & P1 & V1 & PO1 & SN1 & ST1 & SM1 & WW1).
      destruct (dcore_putShortMSB _ (Z.land (cs_adler (ds_strm s)) 65535) D1 SN1 ltac:(rewrite ST1; exact NI) ltac:(rewrite ST1; exact NG)
                  ltac:(rewrite P1, PO1, V1, P0, PO0; clear -BB; lia)) as (D2 & P2 & V2 & PO2 & SN2 & ST2 & SM2 & WW2).
      apply HP; [exact D2 | exact SN2 | rewrite ST2, ST1; exact SF | rewrite WW2; exact WW1].
    - replace (0 <? ds_wrap s2) with true by (symmetry; apply Z.ltb_lt; rewrite W2', Wa; exact W).
      split; [apply dcore_negwrap; [exact D2 | rewrite ST2; exact STa | rewrite W2', Wa; exact W]|].
      replace (ds_pending (set_wrap s2 (- ds_wrap s2))) with (ds_pending s2) by reflexivity.
      replace (ds_strm (set_wrap s2 (- ds_wrap s2))) with (ds_strm s2) by reflexivity.
      destruct (Z.eqb_spec (ds_pending s2) 0) as [PZ|PZ]; cbn [negb].
      { split; [right; reflexivity | intros X; discriminate X]. }
      split; [left; reflexivity | intros _].
      destruct (Z.eq_dec (cs_avail_out (ds_strm s2)) 0) as [A|A]; [exact A | exfalso; exact (PZ (proj1 (FL2 A)))].
  Qed.

  Lemma dcore_trl_pre : forall s, dcore s -> trl_pre PBL s.
  Proof. intros s D. pose proof (dcore_basics s D) as BB. unfold trl_pre. lia. Qed.

  Lemma tail_inv : forall s, ZB s -> ds_sym_next s = 0 -> (flush = Z_FINISH -> ds_status s = FINISH_STATE) ->
    trl_ok PBL OCAP flush s
    /\ dcore (fst (core_tail s flush))
    /\ (let rc := snd (core_tail s flush) in rc = Z_OK \/ rc = Z_STREAM_END \/ rc = Z_BUF_ERROR \/ rc = Z_STREAM_ERROR)
    /\ (snd (core_tail s flush) = Z_OK -> flush = Z_FINISH -> cs_avail_out (ds_strm (fst (core_tail s flush))) = 0).
  Proof.
    intros s Z SN SF. pose proof Z as (D & P0 & PO0). unfold trl_ok, core_tail.
    destruct (Z.eqb_spec flush Z_FINISH) as [FF|FF]; cbn [negb].
    - destruct (Z.leb_spec (ds_wrap s) 0) as [W|W]; cbn [fst snd].
      + split; [split; [exact (dcore_trl_pre s D) | intros _ X; exfalso; lia]|]. split; [exact D|]. split; [right; left; reflexivity | intros X; discriminate X].
      + destruct (trl_inv s Z SN (SF FF) ltac:(lia)) as [EM TP].
        split; [split; [exact (dcore_trl_pre s D) | intros _ _; exact EM]|].
        destruct (deflate_trailer s) as [s' rc]. cbn [fst snd]. destruct TP as (D' & R & A). split; [exact D'|]. split; [clear -R; tauto | intros X _; exact (A X)].
    - cbn [fst snd]. split; [split; [exact (dcore_trl_pre s D) | intros X; exfalso; exact (FF X)]|]. split; [exact D|]. split; [left; reflexivity | intros _ X; exfalso; exact (FF X)].
  Qed.

  Lemma dcore_front1 : forall s, dcore s ->
    dstatus_ok (ds_status s) /\ 0 <= cs_avail_in (ds_strm s) < 2 ^ 32 /\ 0 <= cs_avail_out (ds_strm s) < 2 ^ 32
    /\ 0 <= cs_next_in (ds_strm s) <= ILEN.
  Proof. intros s D. pose proof (dcore_basics s D) as BB. split; [exact (dcore_status_ok s D) | lia]. Qed.

  Theorem core_inv : forall s, dcore s ->
    core_okG ws hs PBL ILEN OCAP flush s
    /\ dcore (fst (deflate_core s flush))
    /\ (let rc := snd (deflate_core s flush) in rc = Z_OK \/ rc = Z_STREAM_END \/ rc = Z_BUF_ERROR \/ rc = Z_STREAM_ERROR).
  Proof.
    intros s D. pose proof (dcore_front1 s D) as FR1.
    assert (FOK : front_okG PBL ILEN OCAP flush s).
    { split; [exact FR1|]. intros EF1. pose proof (f1_inv s D) as F1. rewrite EF1 in F1. destruct F1 as (F5 & A0 & _).
      destruct (f2_inv s D F5 A0) as [OK2 P2]. split; [exact OK2|].
      destruct (f2_spec s flush) as [s2 rc2 | s2 | s2]; [exact Logic.I | | apply dcore_b4; exact (proj1 (proj1 P2))].
      destruct P2 as (Z2 & NF2 & _). destruct (f3_inv s2 Z2 NF2) as (OK3 & B4 & _). split; [exact OK3 | exact B4]. }
    rewrite deflate_core_front. unfold core_okG.
    match goal with |- (_ /\ ?M) /\ ?R => enough (H : M /\ R) by (split; [split; [exact FOK | exact (proj1 H)] | exact (proj2 H)]) end.
    unfold front_spec.
    pose proof (f1_inv s D) as F1.
    destruct (f1_spec s flush) as [[s1 rc1]|].
    { destruct F1 as [D1 R1]. cbn [fst snd]. split; [exact Logic.I|]. split; [exact D1 | clear -R1; tauto]. }
    destruct F1 as (F5 & A0 & SFF).
    destruct (f2_inv s D F5 A0) as [OK2 P2].
    destruct (f2_spec s flush) as [s2 rc2 | s2 | s2].
    - destruct P2 as (D2 & R2 & _). cbn [fst snd]. split; [exact Logic.I|]. split; [exact D2 | clear -R2; tauto].
    - destruct P2 as (Z2 & NF2 & A2 & _).
      destruct (f3_inv s2 Z2 NF2) as (OK3 & B4 & P3).
      destruct (f3_spec s2) as [s3 [rc3|]].
      + destruct P3 as (D3 & -> & _). cbn [fst snd]. split; [exact Logic.I|]. split; [exact D3 | left; reflexivity].
      + destruct P3 as (Z3 & SB3 & _). unfold blocks_or_idle.
        destruct (blocks_cond s3 flush) eqn:BC.
        * destruct (blocks_inv s3 Z3 SB3 F5) as [BOK BP].
          destruct (blocks_body s3 flush) as [s4 [rc4|]].
          -- destruct BP as (D4 & -> & _). cbn [fst snd]. split; [split; [exact BOK | intros X; discriminate X]|]. split; [exact D4 | left; reflexivity].
          -- destruct BP as (D4 & P4 & PO4 & SN4 & SF4 & SB4 & _).
             destruct (tail_inv s4 (conj D4 (conj P4 PO4)) SN4 SF4) as (TOK & TD & TR' & _).
             split; [split; [exact BOK | intros _; exact TOK]|]. split; [exact TD | exact TR'].
        * destruct (Z.eqb_spec flush Z_NO_FLUSH) as [F0|F0]; cbn [fst snd].
          -- split; [exact Logic.I|]. split; [exact (proj1 Z3) | left; reflexivity].
          -- exfalso. unfold blocks_cond in BC. rewrite SB3 in BC.
             replace (negb (flush =? Z_NO_FLUSH)) with true in BC by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact F0).
             replace (negb (BUSY_STATE =? FINISH_STATE)) with true in BC by reflexivity.
             rewrite !Bool.orb_true_r in BC. discriminate BC.
    - destruct P2 as (Z2 & SF2 & AI2 & A2 & _). pose proof (proj1 Z2) as D2.
      pose proof (di_finlook _ _ _ _ (co_inv _ D2) SF2) as [L2 SN2].
      unfold blocks_or_idle.
      replace (blocks_cond s2 flush) with false
        by (unfold blocks_cond; rewrite AI2, L2, SF2, !Z.eqb_refl; cbn [negb orb andb]; rewrite Bool.andb_false_r; reflexivity).
      destruct (Z.eqb_spec flush Z_NO_FLUSH) as [F0|F0]; cbn [fst snd].
      + split; [exact Logic.I|]. split; [exact D2 | left; reflexivity].
      + destruct (tail_inv s2 Z2 SN2 ltac:(intros _; exact SF2)) as (TOK & TD & TR' & _).
        split; [exact TOK|]. split; [exact TD | exact TR'].
  Qed.


  Theorem deflate_inv_call : forall s0 zc, DI s0 -> zcall_ok zc -> DADLER2 (ds_wrap s0) (zs_adler (zc_strm zc)) ->
    ds_w_size s0 = ws -> ds_hash_size s0 = hs -> ds_lit_bufsize s0 * 4 = PBL ->
    zlength (zc_input zc) = ILEN -> zc_avail_out zc = OCAP -> zs_total_out (zc_strm zc) = tot0 ->
    let s := set_strm s0 (cstrm_of_call zc) in
    core_okG ws hs PBL ILEN OCAP flush s
    /\ dcore (fst (deflate_core s flush))
    /\ (let rc := snd (deflate_core s flush) in rc = Z_OK \/ rc = Z_STREAM_END \/ rc = Z_BUF_ERROR \/ rc = Z_STREAM_ERROR).
  Proof.
    intros s0 zc DI0 ZC AD Ews Ehs Epbl Eil Eoc Etot. cbv zeta.
    exact (core_inv _ (dcore_entry s0 zc DI0 ZC AD Ews Ehs Epbl Eil Eoc Etot)).
  Qed.
End CORE.


Lemma DI_dwf0 : forall s, dcfg s -> dinv s -> dwf s.
Proof.
  intros s C I. pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
  pose proof I as [T Istr Ilook Isl Iins Ibs Ibs0 Ihw Iih Ims Ipm Iml Ipl Ima Ima1 Imt Ifast Ifastpl Islow Islow1 Ihash Isyms Iroom Ibv Ibb Ipend Ipout Ipop Ipo0 Ipobv Ilf Ilive Iinit Igz Ineg Ilk0 Isn0 Iinw Ifl Imas Ips].
  assert (BS : - 2 ^ 63 <= ds_block_start s < 2 ^ 63).
  { destruct (Z.eq_dec (ds_level s) 0) as [L0|L0].
    - pose proof (Ibs0 L0) as X. clear -X Ibs Istr Isl Ilook Sw. lia.
    - destruct Isyms as (sy & Dy & Cv). specialize (Cv L0).
      pose proof (zcov_le sy (sy_valid _ _ Dy)) as ZC. pose proof (sy_next _ _ Dy) as SN. pose proof (cf_symend _ C) as SE.
      assert (MA : ds_match_available s <= 1) by (clear -Ima; lia).
      clear -Cv ZC SN SE MA Iroom Ibs Istr Isl Ilook Sw Sl. lia. }
  pose proof T as [_ _ _ _ _ _ _ _ _ Tw Tp Th _].
  destruct C; constructor; try assumption.
  - clear -Istr Isl Ilook Sw. lia.
  - clear -Iih. lia.
  - clear -Ihw Sw. lia.
  - intros i Hi. apply Tw. rewrite cf_wl. exact Hi.
  - intros i Hi. apply Tp. rewrite cf_pl. exact Hi.
  - intros i Hi. apply Th. rewrite cf_hl. exact Hi.
Qed.

Lemma DI_dwf : forall s, DI s -> dwf s.
Proof.
  intros s [C I]. pose proof (DI_dwf0 (zin s) (dcfg_zin s C) I) as W.
  destruct W; constructor; assumption.
Qed.

Definition deflate_okG (s0 : deflate_state) (zc : ZCall) (flush : Z) : Prop :=
  let s := set_strm s0 (cstrm_of_call zc) in
  let s1 := fst (deflate_core s flush) in
  let rc := snd (deflate_core s flush) in
  core_okG (ds_w_size s0) (ds_hash_size s0) (ds_lit_bufsize s0 * 4) (zlength (zc_input zc)) (zc_avail_out zc) flush s
  /\ dwf s1 /\ (DADLER2 (ds_wrap s1) (cs_adler (ds_strm s1)) /\ DI s1) /\ dkeep s0 s1 /\ zpost_ok zc (ds_strm s1) rc.

Definition deflate_safe_stmtG : Prop :=
  forall s0 zc flush, 2048 <= ds_lit_bufsize s0 * 4 ->
    dwf s0 -> DI s0 -> zcall_ok zc -> 0 <= flush < 16 -> DADLER2 (ds_wrap s0) (zs_adler (zc_strm zc)) ->
    deflate_okG s0 zc flush
    /\ (let s1 := fst (deflate_core (set_strm s0 (cstrm_of_call zc)) flush) in DI s1 /\ DADLER2 (ds_wrap s1) (cs_adler (ds_strm s1))).

Theorem deflate_safeG : tfb_safe_stmt -> tfb_room_stmt -> deflate_safe_stmtG.
Proof.
  intros TS TR s0 zc flush HPBL _ DI0 ZC HF AD.
  destruct (deflate_inv_call (ds_w_size s0) (ds_hash_size s0) (ds_lit_bufsize s0 * 4) (zlength (zc_input zc)) (zc_avail_out zc)
              (zs_total_out (zc_strm zc)) TS TR HPBL flush HF s0 zc DI0 ZC AD eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as (OK & D1 & RC).
  cbv zeta in RC.
  revert D1 RC. unfold deflate_okG, DADLER, zpost_ok. cbv zeta.
  pose proof (dkeep_deflate_core s0 (cstrm_of_call zc) flush) as DK. revert DK.
  generalize (deflate_core (set_strm s0 (cstrm_of_call zc)) flush) as r. intros [s1 rc] DK D1 RC. cbn [fst snd] in *.
  pose proof D1 as [C1 I1 CL1 _ _ _]. pose proof CL1 as [Eil _ Hni Hai Hin _ Hao Hout Hob _ Hto Hti Had Had1 Had2 Hdt].
  pose proof (wrap64_range (zs_total_out (zc_strm zc) + zlength (cs_out_rev (ds_strm s1)))) as W64.
  assert (ADL : DADLER2 (ds_wrap s1) (cs_adler (ds_strm s1))).
  { split; [exact Had | intros W; apply adler_ok_canon; exact (Had1 W)]. }
  split; [| split; [exact (DI_of s1 C1 I1) | exact ADL]].
  split; [exact OK|]. split; [exact (DI_dwf0 s1 C1 I1)|]. split; [exact (conj ADL (DI_of s1 C1 I1))|]. split; [exact DK|].
  rewrite Hto. repeat split; try assumption; try lia.
  all: unfold Z_OK, Z_STREAM_END, Z_BUF_ERROR, Z_STREAM_ERROR in RC; lia.
Qed.




