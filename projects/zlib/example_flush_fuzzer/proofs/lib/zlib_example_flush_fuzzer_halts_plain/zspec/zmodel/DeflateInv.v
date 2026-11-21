(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateInvHash DeflateInvKeep DeflateSetters OverlayFBS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Export DeflateSetters.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac dsf := autorewrite with dsf.
Tactic Notation "dsf" "in" hyp(H) := autorewrite with dsf in H.
Tactic Notation "dsf" "in" "*" := autorewrite with dsf in *.

Ltac dsr := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd].
Tactic Notation "dsr" "in" hyp(H) := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd] in H.
Tactic Notation "dsr" "in" "*" := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd] in *.


Record dcfg (s : deflate_state) : Prop := MkDCFG {
  cf_check : deflateStateCheck s = false;
  cf_blkw : ds_window_blk s <> None;
  cf_blkp : ds_prev_blk s <> None;
  cf_blkh : ds_head_blk s <> None;
  cf_blkb : ds_pending_buf_blk s <> None;
  cf_wbits : 9 <= ds_w_bits s <= 15;
  cf_wsize : ds_w_size s = 2 ^ ds_w_bits s;
  cf_wmask : ds_w_mask s = ds_w_size s - 1;
  cf_wsz : ds_window_size s = 2 * ds_w_size s;
  cf_hbits : 8 <= ds_hash_bits s <= 16;
  cf_hsize : ds_hash_size s = 2 ^ ds_hash_bits s;
  cf_hmask : ds_hash_mask s = ds_hash_size s - 1;
  cf_hshift : ds_hash_shift s = (ds_hash_bits s + MIN_MATCH - 1) / MIN_MATCH;
  cf_lbs : ds_lit_bufsize s = 2 ^ (ds_hash_bits s - 1);
  cf_pbs : ds_pending_buf_size s = ds_lit_bufsize s * 4;
  cf_symend : ds_sym_end s = (ds_lit_bufsize s - 1) * 3;
  cf_wl : arr_len (ds_window s) = 2 * ds_w_size s;
  cf_pl : arr_len (ds_prev s) = ds_w_size s;
  cf_hl : arr_len (ds_head s) = ds_hash_size s;
  cf_bl : arr_len (ds_pending_buf s) = ds_lit_bufsize s * 4;
  cf_tl : fbs_tree_lens s;
  cf_gzhead : ds_gzhead s = 0;
  cf_method : ds_method s = Z_DEFLATED;
  cf_level : 0 <= ds_level s <= 9;
  cf_strategy : 0 <= ds_strategy s <= 4;
  cf_wrap : -2 <= ds_wrap s <= 2;
  cf_table : (ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s)
             = configuration_table (ds_level s) }.

Lemma dcfg_sizes : forall s, dcfg s ->
  512 <= ds_w_size s <= 32768 /\ 256 <= ds_hash_size s <= 65536 /\ 128 <= ds_lit_bufsize s <= 32768
  /\ ds_hash_size s = 2 * ds_lit_bufsize s.
Proof.
  intros s C. pose proof (cf_wbits _ C) as Wb. pose proof (cf_hbits _ C) as Hb.
  rewrite (cf_wsize _ C), (cf_hsize _ C), (cf_lbs _ C).
  assert (A : 2 ^ 9 <= 2 ^ ds_w_bits s <= 2 ^ 15) by (split; apply Z.pow_le_mono_r; lia).
  assert (B : 2 ^ 8 <= 2 ^ ds_hash_bits s <= 2 ^ 16) by (split; apply Z.pow_le_mono_r; lia).
  assert (C' : 2 ^ 7 <= 2 ^ (ds_hash_bits s - 1) <= 2 ^ 15) by (split; apply Z.pow_le_mono_r; lia).
  replace (2 ^ ds_hash_bits s) with (2 * 2 ^ (ds_hash_bits s - 1)) in * by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  cbn in A, B, C'. lia.
Qed.


Definition zcov (syms : list (Z * Z)) : Z :=
  fold_right (fun dl acc => (let '(d, lc) := dl in if d =? 0 then 1 else lc + MIN_MATCH) + acc) 0 syms.

Record dsyms (syms : list (Z * Z)) (s : deflate_state) : Prop := MkDSYMS {
  sy_next : ds_sym_next s = 3 * Z.of_nat (length syms);
  sy_valid : Forall sym_valid syms;
  sy_dist : Forall (fun dl => fst dl <= ds_w_size s - MIN_LOOKAHEAD) syms;
  sy_bytes : forall i d lc, nth_error syms i = Some (d, lc) ->
      arr_get (ds_pending_buf s) (ds_lit_bufsize s + 3 * Z.of_nat i) = d mod 256
      /\ arr_get (ds_pending_buf s) (ds_lit_bufsize s + 3 * Z.of_nat i + 1) = d / 256
      /\ arr_get (ds_pending_buf s) (ds_lit_bufsize s + 3 * Z.of_nat i + 2) = lc;
  sy_freq_l : forall c, 0 <= c < L_CODES ->
      Freq s TL c = zcount (fun dl => sym_lcode dl =? c) syms + (if c =? END_BLOCK then 1 else 0);
  sy_freq_d : forall j, 0 <= j < D_CODES ->
      Freq s TD j = zcount (fun dl => match sym_dcode dl with Some j' => j' =? j | None => false end) syms;
  sy_freq_b : forall j, 0 <= j < BL_CODES -> Freq s TB j = 0;
  sy_opt_len : ds_opt_len s = 0;
  sy_static_len : ds_static_len s = 0 }.


Definition dhash (s : deflate_state) : Prop :=
  exists Ins : Z -> Prop, hc_inv Ins (ds_strstart s) (ds_w_size s) (ds_head s) (ds_prev s) (ds_hash_size s).
Definition dhashb (hb : Z) (s : deflate_state) : Prop :=
  exists Ins : Z -> Prop, hc_inv Ins (ds_strstart s + hb) (ds_w_size s) (ds_head s) (ds_prev s) (ds_hash_size s).
Lemma dhashb0 : forall s, dhash s -> dhashb 0 s.
Proof. intros s [Ins H]. exists Ins. rewrite Z.add_0_r. exact H. Qed.
Lemma dhashb0' : forall s, dhashb 0 s -> dhash s.
Proof. intros s [Ins H]. exists Ins. rewrite Z.add_0_r in H. exact H. Qed.


Definition lz_strat (s : deflate_state) : Prop := ds_strategy s <> Z_HUFFMAN_ONLY /\ ds_strategy s <> Z_RLE.

Record dinvR (rm hb : Z) (fz : bool) (s : deflate_state) : Prop := MkDINV {
  di_cty : cty s;
  di_str : 0 <= ds_strstart s;
  di_look : 0 <= ds_lookahead s;
  di_sl : ds_strstart s + ds_lookahead s <= 2 * ds_w_size s;
  di_ins : 0 <= ds_insert s <= ds_strstart s;
  di_bs : ds_block_start s <= ds_strstart s;
  di_bs0 : ds_level s = 0 -> 0 <= ds_block_start s;
  di_hw : 0 <= ds_high_water s <= 2 * ds_w_size s;
  di_ih : 0 <= ds_ins_h s < 2 ^ 16;
  di_ms : 0 <= ds_match_start s < 2 ^ 32;
  di_pm : 0 <= ds_prev_match s < 2 ^ 32;
  di_ml : 0 <= ds_match_length s <= MAX_MATCH;
  di_pl : 0 <= ds_prev_length s <= MAX_MATCH;
  di_ma : ds_match_available s = 0 \/ ds_match_available s = 1;
  di_ma1 : ds_match_available s = 1 -> ds_level s <> 0 -> 1 <= ds_strstart s;
  di_matches : 0 <= ds_matches s <= 2;
  di_fast : fz = true -> 1 <= ds_level s <= 3 -> lz_strat s -> ds_match_length s < MIN_MATCH;
  di_fastpl : 1 <= ds_level s <= 3 -> lz_strat s -> ds_prev_length s = MIN_MATCH - 1;
  di_slow : fz = true -> 4 <= ds_level s -> lz_strat s -> MIN_MATCH <= ds_match_length s ->
            1 <= ds_strstart s
            /\ 1 <= wrap32 (ds_strstart s - 1 - ds_match_start s) <= ds_w_size s - MIN_LOOKAHEAD
            /\ ds_match_length s <= ds_lookahead s + 1;
  di_slow1 : 4 <= ds_level s -> lz_strat s -> 1 <= ds_match_length s;
  di_hash : ds_level s <> 0 -> dhashb hb s;
  di_syms : exists syms, dsyms syms s
            /\ (ds_level s <> 0 -> ds_strstart s - ds_block_start s <= zcov syms + ds_match_available s);
  di_room : ds_sym_next s + rm <= ds_sym_end s;
  di_bv : 0 <= ds_bi_valid s <= 16;
  di_bb : 0 <= ds_bi_buf s < 2 ^ 16;
  di_pend : 0 <= ds_pending s;
  di_pout : 0 <= ds_pending_out s;
  di_pop : 8 * (ds_pending_out s + ds_pending s) + ds_bi_valid s <= 8 * (ds_lit_bufsize s * 4);
  di_po0 : ds_pending s = 0 -> ds_pending_out s = 0;
  di_pobv : ds_pending_out s <> 0 -> ds_bi_valid s < 8;
  di_lf : -2 <= ds_last_flush s <= 5;
  di_live : ds_status s <> 69 /\ ds_status s <> 73 /\ ds_status s <> 91 /\ ds_status s <> 103;
  di_init : ds_status s = INIT_STATE \/ ds_status s = GZIP_STATE -> ds_pending s = 0 /\ 0 <= ds_wrap s /\ ds_sym_next s = 0;
  di_gz : ds_status s = GZIP_STATE -> ds_wrap s = 2;
  di_negwrap : ds_wrap s < 0 -> ds_status s = FINISH_STATE /\ ds_lookahead s = 0;
  di_look0 : ds_level s = 0 -> ds_lookahead s = 0;
  di_sn0 : ds_level s = 0 -> ds_sym_next s = 0;
  di_initw : ds_status s = INIT_STATE -> ds_wrap s <= 1;
  di_finlook : ds_status s = FINISH_STATE -> ds_lookahead s = 0 /\ ds_sym_next s = 0;
  di_maslow : ds_match_available s <> 0 -> 4 <= ds_level s /\ lz_strat s;
  di_pendsym : ds_pending s <> 0 -> ds_sym_next s = 0 }.
Notation dinv := (dinvR 3 0 true).



Definition adler_ok (a : Z) : Prop := 0 <= a < 2 ^ 32 /\ a mod 2 ^ 16 < 65521 /\ (a mod 2 ^ 32) / 2 ^ 16 < 65521.

Record dcall (ILEN OCAP tot0 : Z) (s : deflate_state) : Prop := MkDCALL {
  dc_ilen : arr_len (cs_input (ds_strm s)) = ILEN;
  dc_ilen32 : 0 <= ILEN < 2 ^ 32;
  dc_ni : 0 <= cs_next_in (ds_strm s);
  dc_ai : 0 <= cs_avail_in (ds_strm s);
  dc_in : cs_next_in (ds_strm s) + cs_avail_in (ds_strm s) = ILEN;
  dc_ocap32 : 0 <= OCAP < 2 ^ 32;
  dc_ao : 0 <= cs_avail_out (ds_strm s);
  dc_out : cs_avail_out (ds_strm s) + zlength (cs_out_rev (ds_strm s)) = OCAP;
  dc_ob : Forall (fun b => 0 <= b < 256) (cs_out_rev (ds_strm s));
  dc_tot0 : 0 <= tot0 < 2 ^ 64;
  dc_to : cs_total_out (ds_strm s) = wrap64 (tot0 + zlength (cs_out_rev (ds_strm s)));
  dc_ti : 0 <= cs_total_in (ds_strm s) < 2 ^ 64;
  dc_ad : 0 <= cs_adler (ds_strm s) < 2 ^ 32;
  dc_ad1 : ds_wrap s = 1 -> adler_ok (cs_adler (ds_strm s));
  dc_ad2 : ds_wrap s = 2 -> 0 <= cs_adler (ds_strm s) < 2 ^ 32;
  dc_dt : - 2 ^ 31 <= cs_data_type (ds_strm s) < 2 ^ 31 }.



Record dpostR (rm hb : Z) (fz : bool) (ws hs PBL ILEN OCAP tot0 : Z) (s : deflate_state) : Prop := MkDPOST {
  dp_cfg : dcfg s;
  dp_inv : dinvR rm hb fz s;
  dp_call : dcall ILEN OCAP tot0 s;
  dp_ws : ds_w_size s = ws;
  dp_hs : ds_hash_size s = hs;
  dp_pbl : ds_lit_bufsize s * 4 = PBL;
  dp_status : ds_status s = BUSY_STATE;
  dp_wrap : 0 <= ds_wrap s;
  dp_lz : ds_level s <> 0;
  dp_flush : cs_avail_out (ds_strm s) <> 0 -> ds_pending s = 0 /\ ds_pending_out s = 0 }.

Record drunR (rm hb : Z) (fz : bool) (ws hs PBL ILEN OCAP tot0 : Z) (s : deflate_state) : Prop := MkDRUN {
  dr_post : dpostR rm hb fz ws hs PBL ILEN OCAP tot0 s;
  dr_pend : ds_pending s = 0;
  dr_pout : ds_pending_out s = 0 }.
Notation dpost := (dpostR 3 0 true).
Notation drun := (drunR 3 0 true).


Definition zin (s : deflate_state) : deflate_state := set_strm s (cset_input (ds_strm s) arr0).
Definition DI (s : deflate_state) : Prop := dcfg s /\ dinv (zin s).

Lemma set_strm_zin : forall s st, set_strm (zin s) st = set_strm s st.
Proof. intros s st. destruct s; reflexivity. Qed.
Lemma u8a_arr0 : u8a arr0.
Proof. intros i Hi. unfold arr0, arr_make in Hi. rewrite arr_len_init in Hi. lia. Qed.
Lemma dcfg_zin : forall s, dcfg s -> dcfg (zin s).
Proof. intros s C. unfold zin. destruct C; constructor; dsr; assumption. Qed.
