(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateInvHash DeflateInvKeep OverlayFBS DeflRoom.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import LmatchModel FillWinModel SendModel DeflFastModel TreesTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import RefFlushBlk11 RefFlushPend1 RefDeflFastOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition tfb_safe_stmt : Prop :=
  forall syms s buf len last, FBS syms s buf len last -> 512 <= ds_lit_bufsize s -> fb_safe s buf len last.
Definition tfb_room_stmt : Prop :=
  forall syms s buf len last, FBS syms s buf len last -> 512 <= ds_lit_bufsize s ->
    let s' := tr_flush_block s buf len last in
    vsize s' + 80 <= 8 * arr_len (ds_pending_buf s) /\ 0 <= ds_bi_valid s' <= 16 /\ 0 <= ds_bi_buf s' < 2 ^ 16 /\ 0 <= ds_pending s'.




Lemma drun_lzw : forall rm hb fz ws hs PBL ILEN OCAP tot0 s, 0 <= rm -> dpostR rm hb fz ws hs PBL ILEN OCAP tot0 s -> lzw s.
Proof.
  intros rm hb fz ws hs PBL ILEN OCAP tot0 s Hrm P. destruct P as [C I CL Ews Ehs Epbl Sst Swr Slz Sfl].
  pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
  pose proof (cf_table _ C) as TB.
  assert (LZ : 0 <= ds_max_lazy_match s <= 258).
  { pose proof (cf_level _ C). assert (E : ds_max_lazy_match s = snd (fst (fst (configuration_table (ds_level s))))) by (rewrite <- TB; reflexivity).
    rewrite E. unfold configuration_table.
    destruct (ds_level s) as [|p|p]; try lia; cbn; try lia. do 4 (destruct p; cbn; try lia). }
  constructor.
  - symmetry. exact (cf_bl _ C).
  - exact (cf_symend _ C).
  - pose proof (di_room _ _ _ _ I). destruct (di_syms _ _ _ _ I) as (syms & D & _). pose proof (sy_next _ _ D). lia.
  - exact (cf_wmask _ C).
  - exact (cf_hmask _ C).
  - rewrite (cf_hshift _ C). pose proof (cf_hbits _ C). unfold MIN_MATCH. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  - exact (di_ih _ _ _ _ I).
  - exact (di_str _ _ _ _ I).
  - exact (di_look _ _ _ _ I).
  - rewrite (cf_wl _ C). exact (di_sl _ _ _ _ I).
  - pose proof (di_ml _ _ _ _ I). unfold MAX_MATCH in *. lia.
  - exact (di_ms _ _ _ _ I).
  - lia.
  - intros i Hi. exact (ct_win _ (di_cty _ _ _ _ I) i Hi).
  - intros i Hi. exact (ct_head _ (di_cty _ _ _ _ I) i Hi).
  - intros i Hi. exact (ct_prev _ (di_cty _ _ _ _ I) i Hi).
Qed.


Lemma zcov_le : forall l, Forall sym_valid l -> zcov l <= 258 * Z.of_nat (length l).
Proof.
  intros l H. unfold zcov. induction H as [|[d lc] l Hx H IH]; cbn [fold_right length]; [lia|].
  set (X := fold_right _ _ _) in *. rewrite Nat2Z.inj_succ.
  unfold sym_valid in Hx. cbn in Hx. pose proof (eq_refl : MIN_MATCH = 3). destruct (Z.eqb_spec d 0); lia.
Qed.

Definition fbo_buf (s : deflate_state) : option Z :=
  if 0 <=? ds_block_start s then Some (wrap32 (ds_block_start s)) else None.
Definition fbo_len (s : deflate_state) : Z := wrap64 (ds_strstart s - ds_block_start s).

Lemma drun_span : forall rm hb fz ws hs PBL ILEN OCAP tot0 s, 0 <= rm -> dpostR rm hb fz ws hs PBL ILEN OCAP tot0 s ->
  0 <= ds_strstart s - ds_block_start s < 2 ^ 24 /\ 0 <= ds_strstart s <= 65536
  /\ fbo_len s = ds_strstart s - ds_block_start s
  /\ (forall off, fbo_buf s = Some off -> off = ds_block_start s /\ 0 <= off).
Proof.
  intros rm hb fz ws hs PBL ILEN OCAP tot0 s Hrm P. destruct P as [C I CL Ews Ehs Epbl Sst Swr Slz Sfl].
  pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
  destruct (di_syms _ _ _ _ I) as (syms & D & COV). specialize (COV Slz).
  pose proof (zcov_le syms (sy_valid _ _ D)) as ZL. pose proof (sy_next _ _ D) as SN. pose proof (di_room _ _ _ _ I) as RM.
  rewrite (cf_symend _ C) in RM.
  pose proof (di_bs _ _ _ _ I). pose proof (di_str _ _ _ _ I). pose proof (di_sl _ _ _ _ I). pose proof (di_look _ _ _ _ I). pose proof (di_ma _ _ _ _ I).
  assert (R : 0 <= ds_strstart s - ds_block_start s < 2 ^ 24) by lia.
  split; [exact R|]. split; [lia|]. split.
  - unfold fbo_len. rewrite wrap64_mod. apply Z.mod_small. lia.
  - intros off Hb. unfold fbo_buf in Hb. destruct (Z.leb_spec 0 (ds_block_start s)); [| discriminate Hb].
    injection Hb as <-. rewrite wrap32_id by lia. lia.
Qed.

Lemma drun_FBS : forall rm hb fz ws hs PBL ILEN OCAP tot0 s last, 0 <= rm -> drunR rm hb fz ws hs PBL ILEN OCAP tot0 s -> (last = 0 \/ last = 1) ->
  exists syms, FBS syms s (fbo_buf s) (fbo_len s) last.
Proof.
  intros rm hb fz ws hs PBL ILEN OCAP tot0 s last Hrm [P P0 PO0] Hl.
  pose proof (drun_span _ _ _ _ _ _ _ _ _ _ Hrm P) as (R & RS & EL & EB).
  destruct P as [C I CL Ews Ehs Epbl Sst Swr Slz Sfl].
  pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
  destruct (di_syms _ _ _ _ I) as (syms & D & COV). specialize (COV Slz).
  pose proof (sy_next _ _ D) as SN. pose proof (di_room _ _ _ _ I) as RM. rewrite (cf_symend _ C) in RM.
  pose proof (di_cty _ _ _ _ I) as T.
  exists syms. constructor.
  - exact P0.
  - exact (di_bv _ _ _ _ I).
  - exact (di_bb _ _ _ _ I).
  - exists (ds_hash_bits s - 1). pose proof (cf_hbits _ C). split; [lia | exact (cf_lbs _ C)].
  - rewrite (cf_bl _ C). lia.
  - rewrite (cf_symend _ C). lia.
  - exact SN.
  - lia.
  - exact (sy_valid _ _ D).
  - exact (sy_bytes _ _ D).
  - exact (sy_freq_l _ _ D).
  - exact (sy_freq_d _ _ D).
  - exact (sy_freq_b _ _ D).
  - exact (cf_tl _ C).
  - exact T.
  - exact (sy_opt_len _ _ D).
  - exact (sy_static_len _ _ D).
  - pose proof (cf_level _ C). lia.
  - exact (cf_strategy _ C).
  - pose proof (dc_dt _ _ _ _ CL). lia.
  - exact Hl.
  - rewrite EL. lia.
  - intros off Hb. destruct (EB off Hb) as [-> Ho]. rewrite EL, (cf_wl _ C). pose proof (di_sl _ _ _ _ I). pose proof (di_look _ _ _ _ I).
    split; [exact Ho|]. split; [lia|]. rewrite <- (cf_wl _ C). exact (ct_win _ T).
Qed.


Lemma fp_ok_intro : forall ILEN OCAP tot0 PBL s,
  fp_inv PBL s -> dcall ILEN OCAP tot0 s -> cty s -> fp_ok PBL OCAP s.
Proof.
  intros ILEN OCAP tot0 PBL s F CL T. destruct F as [HB Hpo HV HPBL Hpo0 HPS].
  destruct (bi_flush_bits s HB) as (HB1 & V1 & B1 & P1).
  pose proof (ep_bi_flush s) as EP1. pose proof (cty_bi_flush _ T) as T1.
  unfold fp_ok. cbv zeta. change (tr_flush_bits s) with (bi_flush s).
  remember (bi_flush s) as s1 eqn:E1; clear E1.
  pose proof (ep_strm _ _ EP1) as S1. pose proof (ep_pending_out _ _ EP1) as PO1. rewrite S1, PO1.
  destruct HB as [A B Cp]. destruct HB1 as [A1 B1' C1]. unfold bvol in *.
  split; [split; [lia|]; split; [lia | lia]|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [pose proof (dc_ao _ _ _ _ CL); pose proof (dc_out _ _ _ _ CL); pose proof (dc_ocap32 _ _ _ _ CL); pose proof (Zle_0_nat (length (cs_out_rev (ds_strm s)))); unfold zlength in *; lia|].
  split; [pose proof (dc_out _ _ _ _ CL); unfold zlength in *; lia|].
  split; [rewrite (dc_to _ _ _ _ CL); rewrite wrap64_mod; apply Z.mod_pos_bound; lia|].
  intros i Hi. apply (ct_pb _ T1). rewrite (ep_len_pending_buf _ _ EP1), HPBL. exact Hi.
Qed.

Lemma detect_loop1_range : forall f s n m r, detect_loop1 f s n m = Some r -> r = Z_BINARY.
Proof.
  induction f as [|f IH]; intros s n m r H; cbn [detect_loop1] in H; [discriminate H|].
  destruct (n <=? 31); [| discriminate H]. destruct (_ && _); [injection H as <-; reflexivity | exact (IH _ _ _ _ H)].
Qed.
Lemma detect_loop2_range : forall f s n r, detect_loop2 f s n = Some r -> r = Z_TEXT.
Proof.
  induction f as [|f IH]; intros s n r H; cbn [detect_loop2] in H; [discriminate H|].
  destruct (n <? LITERALS); [| discriminate H]. destruct (negb _); [injection H as <-; reflexivity | exact (IH _ _ _ H)].
Qed.
Lemma detect_data_type_range : forall s, 0 <= detect_data_type s <= 1.
Proof.
  intros s. unfold detect_data_type.
  destruct (detect_loop1 32 s 0 4093624447) as [r|] eqn:E1; [rewrite (detect_loop1_range _ _ _ _ _ E1); unfold Z_BINARY; lia|].
  destruct (_ || _); [unfold Z_TEXT; lia|].
  destruct (detect_loop2 224 s 32) as [r|] eqn:E2; [rewrite (detect_loop2_range _ _ _ _ E2); unfold Z_TEXT; lia | unfold Z_BINARY; lia].
Qed.


Record fbo_frame (s s' : deflate_state) : Prop := MkFF {
  ff_status : ds_status s' = ds_status s;
  ff_pending_buf_size : ds_pending_buf_size s' = ds_pending_buf_size s;
  ff_wrap : ds_wrap s' = ds_wrap s;
  ff_gzhead : ds_gzhead s' = ds_gzhead s;
  ff_gzindex : ds_gzindex s' = ds_gzindex s;
  ff_method : ds_method s' = ds_method s;
  ff_last_flush : ds_last_flush s' = ds_last_flush s;
  ff_w_size : ds_w_size s' = ds_w_size s;
  ff_w_bits : ds_w_bits s' = ds_w_bits s;
  ff_w_mask : ds_w_mask s' = ds_w_mask s;
  ff_window : ds_window s' = ds_window s;
  ff_window_size : ds_window_size s' = ds_window_size s;
  ff_prev : ds_prev s' = ds_prev s;
  ff_head : ds_head s' = ds_head s;
  ff_ins_h : ds_ins_h s' = ds_ins_h s;
  ff_hash_size : ds_hash_size s' = ds_hash_size s;
  ff_hash_bits : ds_hash_bits s' = ds_hash_bits s;
  ff_hash_mask : ds_hash_mask s' = ds_hash_mask s;
  ff_hash_shift : ds_hash_shift s' = ds_hash_shift s;
  ff_match_length : ds_match_length s' = ds_match_length s;
  ff_prev_match : ds_prev_match s' = ds_prev_match s;
  ff_match_available : ds_match_available s' = ds_match_available s;
  ff_strstart : ds_strstart s' = ds_strstart s;
  ff_match_start : ds_match_start s' = ds_match_start s;
  ff_lookahead : ds_lookahead s' = ds_lookahead s;
  ff_prev_length : ds_prev_length s' = ds_prev_length s;
  ff_max_chain_length : ds_max_chain_length s' = ds_max_chain_length s;
  ff_max_lazy_match : ds_max_lazy_match s' = ds_max_lazy_match s;
  ff_level : ds_level s' = ds_level s;
  ff_strategy : ds_strategy s' = ds_strategy s;
  ff_good_match : ds_good_match s' = ds_good_match s;
  ff_nice_match : ds_nice_match s' = ds_nice_match s;
  ff_lit_bufsize : ds_lit_bufsize s' = ds_lit_bufsize s;
  ff_sym_end : ds_sym_end s' = ds_sym_end s;
  ff_insert : ds_insert s' = ds_insert s;
  ff_high_water : ds_high_water s' = ds_high_water s;
  ff_self_blk : ds_self_blk s' = ds_self_blk s;
  ff_window_blk : ds_window_blk s' = ds_window_blk s;
  ff_prev_blk : ds_prev_blk s' = ds_prev_blk s;
  ff_head_blk : ds_head_blk s' = ds_head_blk s;
  ff_pending_buf_blk : ds_pending_buf_blk s' = ds_pending_buf_blk s;
  ff_block_start : ds_block_start s' = ds_strstart s;
  ff_sym_next : ds_sym_next s' = 0;
  ff_matches : ds_matches s' = 0;
  ff_len : arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s);
  ff_next_in : cs_next_in (ds_strm s') = cs_next_in (ds_strm s);
  ff_avail_in : cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s);
  ff_total_in : cs_total_in (ds_strm s') = cs_total_in (ds_strm s);
  ff_adler : cs_adler (ds_strm s') = cs_adler (ds_strm s);
  ff_input : cs_input (ds_strm s') = cs_input (ds_strm s);
  ff_msg : cs_msg (ds_strm s') = cs_msg (ds_strm s);
  ff_out : zlength (cs_out_rev (ds_strm s)) <= zlength (cs_out_rev (ds_strm s'));
  ff_avail_out : cs_avail_out (ds_strm s') <= cs_avail_out (ds_strm s) }.

Lemma fbo_frame_intro : forall s s1 s3 dt st po,
  kproj s1 = kproj (set_strm (set_sym_next (set_matches s 0) 0) (cset_data_type (ds_strm s) dt)) ->
  let s2 := set_block_start s1 (ds_strstart s1) in
  kproj s3 = kproj (set_pending_out (set_strm s2 st) po) ->
  cs_next_in (ds_strm s3) = cs_next_in (ds_strm s2) -> cs_avail_in (ds_strm s3) = cs_avail_in (ds_strm s2) ->
  cs_total_in (ds_strm s3) = cs_total_in (ds_strm s2) -> cs_adler (ds_strm s3) = cs_adler (ds_strm s2) ->
  cs_input (ds_strm s3) = cs_input (ds_strm s2) -> cs_msg (ds_strm s3) = cs_msg (ds_strm s2) ->
  zlength (cs_out_rev (ds_strm s2)) <= zlength (cs_out_rev (ds_strm s3)) ->
  cs_avail_out (ds_strm s3) <= cs_avail_out (ds_strm s2) ->
  fbo_frame s s3.
Proof.
  intros s s1 s3 dt st po K1 s2 K3 N1 N2 N3 N4 N5 N6 N7 N8. subst s2.
  pose proof (kp_strm _ _ K1) as SS. rewrite strm_set_strm in SS.
  rewrite ?strm_set_block_start, ?SS in N1, N2, N3, N4, N5, N6, N7, N8.
  rewrite ?cs_next_in_cset_data_type, ?cs_avail_in_cset_data_type, ?cs_total_in_cset_data_type, ?cs_adler_cset_data_type,
          ?cs_input_cset_data_type, ?cs_msg_cset_data_type, ?cs_out_rev_cset_data_type, ?cs_avail_out_cset_data_type in *.
  constructor; try assumption.
  - pose proof (kp_status _ _ K1) as A. pose proof (kp_status _ _ K3) as B.
    rewrite ?status_set_strm, ?status_set_sym_next, ?status_set_matches in A. rewrite ?status_set_pending_out, ?status_set_strm, ?status_set_block_start in B. congruence.
  - pose proof (kp_pending_buf_size _ _ K1) as A. pose proof (kp_pending_buf_size _ _ K3) as B.
    rewrite ?pending_buf_size_set_strm, ?pending_buf_size_set_sym_next, ?pending_buf_size_set_matches in A. rewrite ?pending_buf_size_set_pending_out, ?pending_buf_size_set_strm, ?pending_buf_size_set_block_start in B. congruence.
  - pose proof (kp_wrap _ _ K1) as A. pose proof (kp_wrap _ _ K3) as B.
    rewrite ?wrap_set_strm, ?wrap_set_sym_next, ?wrap_set_matches in A. rewrite ?wrap_set_pending_out, ?wrap_set_strm, ?wrap_set_block_start in B. congruence.
  - pose proof (kp_gzhead _ _ K1) as A. pose proof (kp_gzhead _ _ K3) as B.
    rewrite ?gzhead_set_strm, ?gzhead_set_sym_next, ?gzhead_set_matches in A. rewrite ?gzhead_set_pending_out, ?gzhead_set_strm, ?gzhead_set_block_start in B. congruence.
  - pose proof (kp_gzindex _ _ K1) as A. pose proof (kp_gzindex _ _ K3) as B.
    rewrite ?gzindex_set_strm, ?gzindex_set_sym_next, ?gzindex_set_matches in A. rewrite ?gzindex_set_pending_out, ?gzindex_set_strm, ?gzindex_set_block_start in B. congruence.
  - pose proof (kp_method _ _ K1) as A. pose proof (kp_method _ _ K3) as B.
    rewrite ?method_set_strm, ?method_set_sym_next, ?method_set_matches in A. rewrite ?method_set_pending_out, ?method_set_strm, ?method_set_block_start in B. congruence.
  - pose proof (kp_last_flush _ _ K1) as A. pose proof (kp_last_flush _ _ K3) as B.
    rewrite ?last_flush_set_strm, ?last_flush_set_sym_next, ?last_flush_set_matches in A. rewrite ?last_flush_set_pending_out, ?last_flush_set_strm, ?last_flush_set_block_start in B. congruence.
  - pose proof (kp_w_size _ _ K1) as A. pose proof (kp_w_size _ _ K3) as B.
    rewrite ?w_size_set_strm, ?w_size_set_sym_next, ?w_size_set_matches in A. rewrite ?w_size_set_pending_out, ?w_size_set_strm, ?w_size_set_block_start in B. congruence.
  - pose proof (kp_w_bits _ _ K1) as A. pose proof (kp_w_bits _ _ K3) as B.
    rewrite ?w_bits_set_strm, ?w_bits_set_sym_next, ?w_bits_set_matches in A. rewrite ?w_bits_set_pending_out, ?w_bits_set_strm, ?w_bits_set_block_start in B. congruence.
  - pose proof (kp_w_mask _ _ K1) as A. pose proof (kp_w_mask _ _ K3) as B.
    rewrite ?w_mask_set_strm, ?w_mask_set_sym_next, ?w_mask_set_matches in A. rewrite ?w_mask_set_pending_out, ?w_mask_set_strm, ?w_mask_set_block_start in B. congruence.
  - pose proof (kp_window _ _ K1) as A. pose proof (kp_window _ _ K3) as B.
    rewrite ?window_set_strm, ?window_set_sym_next, ?window_set_matches in A. rewrite ?window_set_pending_out, ?window_set_strm, ?window_set_block_start in B. congruence.
  - pose proof (kp_window_size _ _ K1) as A. pose proof (kp_window_size _ _ K3) as B.
    rewrite ?window_size_set_strm, ?window_size_set_sym_next, ?window_size_set_matches in A. rewrite ?window_size_set_pending_out, ?window_size_set_strm, ?window_size_set_block_start in B. congruence.
  - pose proof (kp_prev _ _ K1) as A. pose proof (kp_prev _ _ K3) as B.
    rewrite ?prev_set_strm, ?prev_set_sym_next, ?prev_set_matches in A. rewrite ?prev_set_pending_out, ?prev_set_strm, ?prev_set_block_start in B. congruence.
  - pose proof (kp_head _ _ K1) as A. pose proof (kp_head _ _ K3) as B.
    rewrite ?head_set_strm, ?head_set_sym_next, ?head_set_matches in A. rewrite ?head_set_pending_out, ?head_set_strm, ?head_set_block_start in B. congruence.
  - pose proof (kp_ins_h _ _ K1) as A. pose proof (kp_ins_h _ _ K3) as B.
    rewrite ?ins_h_set_strm, ?ins_h_set_sym_next, ?ins_h_set_matches in A. rewrite ?ins_h_set_pending_out, ?ins_h_set_strm, ?ins_h_set_block_start in B. congruence.
  - pose proof (kp_hash_size _ _ K1) as A. pose proof (kp_hash_size _ _ K3) as B.
    rewrite ?hash_size_set_strm, ?hash_size_set_sym_next, ?hash_size_set_matches in A. rewrite ?hash_size_set_pending_out, ?hash_size_set_strm, ?hash_size_set_block_start in B. congruence.
  - pose proof (kp_hash_bits _ _ K1) as A. pose proof (kp_hash_bits _ _ K3) as B.
    rewrite ?hash_bits_set_strm, ?hash_bits_set_sym_next, ?hash_bits_set_matches in A. rewrite ?hash_bits_set_pending_out, ?hash_bits_set_strm, ?hash_bits_set_block_start in B. congruence.
  - pose proof (kp_hash_mask _ _ K1) as A. pose proof (kp_hash_mask _ _ K3) as B.
    rewrite ?hash_mask_set_strm, ?hash_mask_set_sym_next, ?hash_mask_set_matches in A. rewrite ?hash_mask_set_pending_out, ?hash_mask_set_strm, ?hash_mask_set_block_start in B. congruence.
  - pose proof (kp_hash_shift _ _ K1) as A. pose proof (kp_hash_shift _ _ K3) as B.
    rewrite ?hash_shift_set_strm, ?hash_shift_set_sym_next, ?hash_shift_set_matches in A. rewrite ?hash_shift_set_pending_out, ?hash_shift_set_strm, ?hash_shift_set_block_start in B. congruence.
  - pose proof (kp_match_length _ _ K1) as A. pose proof (kp_match_length _ _ K3) as B.
    rewrite ?match_length_set_strm, ?match_length_set_sym_next, ?match_length_set_matches in A. rewrite ?match_length_set_pending_out, ?match_length_set_strm, ?match_length_set_block_start in B. congruence.
  - pose proof (kp_prev_match _ _ K1) as A. pose proof (kp_prev_match _ _ K3) as B.
    rewrite ?prev_match_set_strm, ?prev_match_set_sym_next, ?prev_match_set_matches in A. rewrite ?prev_match_set_pending_out, ?prev_match_set_strm, ?prev_match_set_block_start in B. congruence.
  - pose proof (kp_match_available _ _ K1) as A. pose proof (kp_match_available _ _ K3) as B.
    rewrite ?match_available_set_strm, ?match_available_set_sym_next, ?match_available_set_matches in A. rewrite ?match_available_set_pending_out, ?match_available_set_strm, ?match_available_set_block_start in B. congruence.
  - pose proof (kp_strstart _ _ K1) as A. pose proof (kp_strstart _ _ K3) as B.
    rewrite ?strstart_set_strm, ?strstart_set_sym_next, ?strstart_set_matches in A. rewrite ?strstart_set_pending_out, ?strstart_set_strm, ?strstart_set_block_start in B. congruence.
  - pose proof (kp_match_start _ _ K1) as A. pose proof (kp_match_start _ _ K3) as B.
    rewrite ?match_start_set_strm, ?match_start_set_sym_next, ?match_start_set_matches in A. rewrite ?match_start_set_pending_out, ?match_start_set_strm, ?match_start_set_block_start in B. congruence.
  - pose proof (kp_lookahead _ _ K1) as A. pose proof (kp_lookahead _ _ K3) as B.
    rewrite ?lookahead_set_strm, ?lookahead_set_sym_next, ?lookahead_set_matches in A. rewrite ?lookahead_set_pending_out, ?lookahead_set_strm, ?lookahead_set_block_start in B. congruence.
  - pose proof (kp_prev_length _ _ K1) as A. pose proof (kp_prev_length _ _ K3) as B.
    rewrite ?prev_length_set_strm, ?prev_length_set_sym_next, ?prev_length_set_matches in A. rewrite ?prev_length_set_pending_out, ?prev_length_set_strm, ?prev_length_set_block_start in B. congruence.
  - pose proof (kp_max_chain_length _ _ K1) as A. pose proof (kp_max_chain_length _ _ K3) as B.
    rewrite ?max_chain_length_set_strm, ?max_chain_length_set_sym_next, ?max_chain_length_set_matches in A. rewrite ?max_chain_length_set_pending_out, ?max_chain_length_set_strm, ?max_chain_length_set_block_start in B. congruence.
  - pose proof (kp_max_lazy_match _ _ K1) as A. pose proof (kp_max_lazy_match _ _ K3) as B.
    rewrite ?max_lazy_match_set_strm, ?max_lazy_match_set_sym_next, ?max_lazy_match_set_matches in A. rewrite ?max_lazy_match_set_pending_out, ?max_lazy_match_set_strm, ?max_lazy_match_set_block_start in B. congruence.
  - pose proof (kp_level _ _ K1) as A. pose proof (kp_level _ _ K3) as B.
    rewrite ?level_set_strm, ?level_set_sym_next, ?level_set_matches in A. rewrite ?level_set_pending_out, ?level_set_strm, ?level_set_block_start in B. congruence.
  - pose proof (kp_strategy _ _ K1) as A. pose proof (kp_strategy _ _ K3) as B.
    rewrite ?strategy_set_strm, ?strategy_set_sym_next, ?strategy_set_matches in A. rewrite ?strategy_set_pending_out, ?strategy_set_strm, ?strategy_set_block_start in B. congruence.
  - pose proof (kp_good_match _ _ K1) as A. pose proof (kp_good_match _ _ K3) as B.
    rewrite ?good_match_set_strm, ?good_match_set_sym_next, ?good_match_set_matches in A. rewrite ?good_match_set_pending_out, ?good_match_set_strm, ?good_match_set_block_start in B. congruence.
  - pose proof (kp_nice_match _ _ K1) as A. pose proof (kp_nice_match _ _ K3) as B.
    rewrite ?nice_match_set_strm, ?nice_match_set_sym_next, ?nice_match_set_matches in A. rewrite ?nice_match_set_pending_out, ?nice_match_set_strm, ?nice_match_set_block_start in B. congruence.
  - pose proof (kp_lit_bufsize _ _ K1) as A. pose proof (kp_lit_bufsize _ _ K3) as B.
    rewrite ?lit_bufsize_set_strm, ?lit_bufsize_set_sym_next, ?lit_bufsize_set_matches in A. rewrite ?lit_bufsize_set_pending_out, ?lit_bufsize_set_strm, ?lit_bufsize_set_block_start in B. congruence.
  - pose proof (kp_sym_end _ _ K1) as A. pose proof (kp_sym_end _ _ K3) as B.
    rewrite ?sym_end_set_strm, ?sym_end_set_sym_next, ?sym_end_set_matches in A. rewrite ?sym_end_set_pending_out, ?sym_end_set_strm, ?sym_end_set_block_start in B. congruence.
  - pose proof (kp_insert _ _ K1) as A. pose proof (kp_insert _ _ K3) as B.
    rewrite ?insert_set_strm, ?insert_set_sym_next, ?insert_set_matches in A. rewrite ?insert_set_pending_out, ?insert_set_strm, ?insert_set_block_start in B. congruence.
  - pose proof (kp_high_water _ _ K1) as A. pose proof (kp_high_water _ _ K3) as B.
    rewrite ?high_water_set_strm, ?high_water_set_sym_next, ?high_water_set_matches in A. rewrite ?high_water_set_pending_out, ?high_water_set_strm, ?high_water_set_block_start in B. congruence.
  - pose proof (kp_self_blk _ _ K1) as A. pose proof (kp_self_blk _ _ K3) as B.
    rewrite ?self_blk_set_strm, ?self_blk_set_sym_next, ?self_blk_set_matches in A. rewrite ?self_blk_set_pending_out, ?self_blk_set_strm, ?self_blk_set_block_start in B. congruence.
  - pose proof (kp_window_blk _ _ K1) as A. pose proof (kp_window_blk _ _ K3) as B.
    rewrite ?window_blk_set_strm, ?window_blk_set_sym_next, ?window_blk_set_matches in A. rewrite ?window_blk_set_pending_out, ?window_blk_set_strm, ?window_blk_set_block_start in B. congruence.
  - pose proof (kp_prev_blk _ _ K1) as A. pose proof (kp_prev_blk _ _ K3) as B.
    rewrite ?prev_blk_set_strm, ?prev_blk_set_sym_next, ?prev_blk_set_matches in A. rewrite ?prev_blk_set_pending_out, ?prev_blk_set_strm, ?prev_blk_set_block_start in B. congruence.
  - pose proof (kp_head_blk _ _ K1) as A. pose proof (kp_head_blk _ _ K3) as B.
    rewrite ?head_blk_set_strm, ?head_blk_set_sym_next, ?head_blk_set_matches in A. rewrite ?head_blk_set_pending_out, ?head_blk_set_strm, ?head_blk_set_block_start in B. congruence.
  - pose proof (kp_pending_buf_blk _ _ K1) as A. pose proof (kp_pending_buf_blk _ _ K3) as B.
    rewrite ?pending_buf_blk_set_strm, ?pending_buf_blk_set_sym_next, ?pending_buf_blk_set_matches in A. rewrite ?pending_buf_blk_set_pending_out, ?pending_buf_blk_set_strm, ?pending_buf_blk_set_block_start in B. congruence.
  - pose proof (kp_strstart _ _ K1) as A. pose proof (kp_block_start _ _ K3) as B.
    rewrite ?strstart_set_strm, ?strstart_set_sym_next, ?strstart_set_matches in A. rewrite ?block_start_set_pending_out, ?block_start_set_strm, ?block_start_set_block_start in B. congruence.
  - pose proof (kp_sym_next _ _ K1) as A. pose proof (kp_sym_next _ _ K3) as B.
    rewrite ?sym_next_set_strm, ?sym_next_set_sym_next in A. rewrite ?sym_next_set_pending_out, ?sym_next_set_strm, ?sym_next_set_block_start in B. congruence.
  - pose proof (kp_matches _ _ K1) as A. pose proof (kp_matches _ _ K3) as B.
    rewrite ?matches_set_strm, ?matches_set_sym_next, ?matches_set_matches in A. rewrite ?matches_set_pending_out, ?matches_set_strm, ?matches_set_block_start in B. congruence.
  - pose proof (kp_len_pending_buf _ _ K1) as A. pose proof (kp_len_pending_buf _ _ K3) as B.
    rewrite ?pending_buf_set_strm, ?pending_buf_set_sym_next, ?pending_buf_set_matches in A. rewrite ?pending_buf_set_pending_out, ?pending_buf_set_strm, ?pending_buf_set_block_start in B. congruence.
Qed.

Lemma dsyms_nil_through : forall a b st po, dsyms [] a -> eproj (set_pending_out (set_strm b st) po) = eproj a -> dsyms [] b.
Proof.
  intros a b st po D E.
  pose proof (ep_sym_next _ _ E) as Q1. rewrite sym_next_set_pending_out, sym_next_set_strm in Q1.
  pose proof (ep_lit_bufsize _ _ E) as Q2. rewrite lit_bufsize_set_pending_out, lit_bufsize_set_strm in Q2.
  pose proof (ep_w_size _ _ E) as Q3. rewrite w_size_set_pending_out, w_size_set_strm in Q3.
  pose proof (ep_opt_len _ _ E) as Q4. rewrite opt_len_set_pending_out, opt_len_set_strm in Q4.
  pose proof (ep_static_len _ _ E) as Q5. rewrite static_len_set_pending_out, static_len_set_strm in Q5.
  pose proof (ep_dyn_ltree_fc _ _ E) as Q6. rewrite dyn_ltree_fc_set_pending_out, dyn_ltree_fc_set_strm in Q6.
  pose proof (ep_dyn_dtree_fc _ _ E) as Q7. rewrite dyn_dtree_fc_set_pending_out, dyn_dtree_fc_set_strm in Q7.
  pose proof (ep_bl_tree_fc _ _ E) as Q8. rewrite bl_tree_fc_set_pending_out, bl_tree_fc_set_strm in Q8.
  destruct D; constructor; unfold Freq in *; cbn [tree_fc] in *; rewrite ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; try assumption.
  intros i d lc Hi. destruct i; discriminate Hi.
Qed.

Section FBO.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.

  Let DPOST hb fz := dpostR 3 hb fz ws hs PBL ILEN OCAP tot0.

  Theorem fbo_run : forall rm hb fz s last, 0 <= rm -> drunR rm hb fz ws hs PBL ILEN OCAP tot0 s -> (last = 0 \/ last = 1) ->
    fbo_ok ws PBL OCAP s last
    /\ let s' := flush_block_only s last in
       DPOST hb fz s' /\ ds_sym_next s' = 0 /\ ds_block_start s' = ds_strstart s' /\ fbo_frame s s'.
  Proof.
    intros rm hb fz s last Hrm D Hl.
    destruct (drun_FBS _ _ _ _ _ _ _ _ _ s last Hrm D Hl) as [syms F].
    pose proof D as [P P0 PO0]. pose proof (drun_span _ _ _ _ _ _ _ _ _ _ Hrm P) as (R & RS & EL & EB).
    pose proof (drun_lzw _ _ _ _ _ _ _ _ _ _ Hrm P) as LZW.
    destruct P as [C I CL Ews Ehs Epbl Sst Swr Slz Sfl].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    pose proof (dc_dt _ _ _ _ CL) as DT.
    assert (HL512 : 512 <= ds_lit_bufsize s) by (clear -HPBL Epbl; lia).
    pose proof (TS syms s _ _ _ F HL512) as SAFE. pose proof (TR syms s _ _ _ F HL512) as ROOM. cbv zeta in ROOM.
    destruct ROOM as (RV & RB1 & RB2 & RB3). unfold vsize in RV.
    pose proof (tfb_fields s (fbo_buf s) (fbo_len s) last) as TF.
    pose proof (tfb_dsyms_nil s (fbo_buf s) (fbo_len s) last (cf_tl _ C)) as DS1.
    assert (BOK : buf_ok s (fbo_buf s) (fbo_len s)).
    { intros off Hb Hn. destruct (EB off Hb) as [-> Ho]. rewrite EL, (cf_wl _ C). pose proof (di_sl _ _ _ _ I). pose proof (di_look _ _ _ _ I). lia. }
    pose proof (cty_tr_flush_block s (fbo_buf s) (fbo_len s) last (di_cty _ _ _ _ I) BOK) as T1.
    assert (DT1 : - 2 ^ 31 <= cs_data_type (ds_strm (tr_flush_block s (fbo_buf s) (fbo_len s) last)) < 2 ^ 31).
    { destruct SAFE as (_ & _ & _ & Edt & _). rewrite Edt. pose proof (detect_data_type_range s).
      destruct ((0 <? ds_level s) && (cs_data_type (ds_strm s) =? Z_UNKNOWN)); lia. }
    remember (tr_flush_block s (fbo_buf s) (fbo_len s) last) as s1 eqn:Es1.
    destruct TF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20
                    & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & F32 & F33 & F34 & F35 & F36 & F37 & F38 & F39
                    & F40 & F41 & F42 & F43 & F44 & F45 & F46).
    remember (set_block_start s1 (ds_strstart s1)) as s2 eqn:Es2.
    assert (FP2 : fp_inv PBL s2).
    { subst s2. constructor; dsr; unfold bvol; dsr.
      - split; dsr; [exact RB1 | exact RB2 | exact RB3].
      - rewrite F19, PO0. lia.
      - rewrite F19, PO0, <- Epbl, <- (cf_bl _ C). lia.
      - rewrite F28, (cf_bl _ C). exact Epbl.
      - intros _. rewrite F19. exact PO0.
      - lia. }
    assert (CL2 : dcall ILEN OCAP tot0 s2).
    { subst s2. destruct CL; constructor; dsr; try rewrite F23; try rewrite F27; dsf; try assumption. }
    assert (T2 : cty s2) by (subst s2; apply cty_set_block_start; exact T1).
    destruct (flush_pending_inv ILEN OCAP tot0 PBL s2 FP2 CL2 T2)
      as (FP3 & CL3 & T3 & B3 & V3 & FL3 & KP3 & N3a & N3b & N3c & N3d & N3e & N3f & N3g & N3h & N3i & EP3).
    remember (flush_pending s2) as s3 eqn:Es3.
    pose proof (kp_tr_flush_block s (fbo_buf s) (fbo_len s) last) as K1. rewrite <- Es1 in K1.
    assert (FR : fbo_frame s s3).
    { subst s2. exact (fbo_frame_intro s s1 s3 _ _ _ K1 KP3 N3a N3b N3c N3d N3f N3g N3h N3i). }
    pose proof FP3 as [HB3 Hpo3 HV3 HPBL3 Hpo03 _]. unfold bvol in HV3. destruct HB3 as [A3 Bb3 C3].
    split.
    {
      unfold fbo_ok. cbv zeta. fold (fbo_buf s) (fbo_len s). rewrite <- Es1.
      split; [exact LZW|].
      split; [pose proof (di_bs _ _ _ _ I); lia|].
      split.
      { unfold tfb_ok. rewrite <- Es1. split; [| split; [exact SAFE | split; [| split; [rewrite EL; lia|]]]].
        - split; [exact (di_bv _ _ _ _ I)|]. split; [exact (di_bb _ _ _ _ I)|]. rewrite P0. pose proof (cf_bl _ C). lia.
        - unfold tfb_keeps. rewrite F12, F13, F14, F15, F16. repeat split; try reflexivity. exact F27.
        - unfold fbo_buf at 1. destruct (Z.leb_spec 0 (ds_block_start s)); [| exact Logic.I].
          intros _. destruct (EB (wrap32 (ds_block_start s)) ltac:(unfold fbo_buf; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity)) as [E _].
          rewrite E, EL, <- Ews. pose proof (di_sl _ _ _ _ I). pose proof (di_look _ _ _ _ I). lia. }
      split; [rewrite F1; lia|].
      rewrite <- Es2. split; [exact (fp_ok_intro _ _ _ _ _ FP2 CL2 T2)|].
      rewrite <- Es3. split; [exact (dc_ao _ _ _ _ CL3)|]. pose proof (dc_out _ _ _ _ CL3). pose proof (dc_ocap32 _ _ _ _ CL3).
      pose proof (Zle_0_nat (length (cs_out_rev (ds_strm s3)))). unfold zlength in *. lia. }
    assert (E3 : flush_block_only s last = s3).
    { unfold flush_block_only. fold (fbo_buf s) (fbo_len s). rewrite <- Es1, <- Es2. symmetry. exact Es3. }
    rewrite E3.
    destruct FR as [G_status G_pending_buf_size G_wrap G_gzhead G_gzindex G_method G_last_flush G_w_size G_w_bits G_w_mask G_window G_window_size G_prev G_head G_ins_h G_hash_size G_hash_bits G_hash_mask G_hash_shift G_match_length G_prev_match G_match_available G_strstart G_match_start G_lookahead G_prev_length G_max_chain_length G_max_lazy_match G_level G_strategy G_good_match G_nice_match G_lit_bufsize G_sym_end G_insert G_high_water G_self_blk G_window_blk G_prev_blk G_head_blk G_pending_buf_blk Gbs Gsn Gmt Glen Gni Gai Gti Gad Gin Gmsg Gout Gao] eqn:EFR. clear EFR.
    split; [| split; [exact Gsn | split; [rewrite Gbs, G_strstart; reflexivity | exact FR]]].
    assert (DS2 : dsyms [] s2) by (subst s2; eapply dsyms_keep; [exact DS1 | dsr; reflexivity ..]).
    assert (DS3 : dsyms [] s3) by exact (dsyms_nil_through _ _ _ _ DS2 EP3).
    pose proof (dcfg_sizes s C) as SZ.
    constructor.
    - apply (dcfg_kproj _ _ KP3). apply dcfg_set_pending_out, dcfg_set_strm. subst s2. apply dcfg_set_block_start.
      apply (dcfg_kproj _ _ K1). apply dcfg_set_strm, dcfg_set_sym_next, dcfg_set_matches. exact C.
    -
      pose proof I as [_ Istr Ilook Isl Iins Ibs Ibs0 Ihw Iih Ims Ipm Iml Ipl Ima Ima1 Imt Ifast Ifastpl Islow Islow1 Ihash Isyms Iroom Ibv Ibb Ipend Ipout Ipop Ipo0 Ipobv Ilf Ilive Iinit Igz Ineg Ilk0 Isn0 Iinw Ifl Imas Ips].
      pose proof (cf_symend _ C) as SE.
      constructor.
      + exact T3.
      + rewrite G_strstart. exact Istr.
      + rewrite G_lookahead. exact Ilook.
      + rewrite G_strstart, G_lookahead, G_w_size. exact Isl.
      + rewrite G_insert, G_strstart. exact Iins.
      + rewrite Gbs, G_strstart. clear. lia.
      + rewrite G_level. intros Hz. exfalso. exact (Slz Hz).
      + rewrite G_high_water, G_w_size. exact Ihw.
      + rewrite G_ins_h. exact Iih.
      + rewrite G_match_start. exact Ims.
      + rewrite G_prev_match. exact Ipm.
      + rewrite G_match_length. exact Iml.
      + rewrite G_prev_length. exact Ipl.
      + rewrite G_match_available. exact Ima.
      + rewrite G_match_available, G_strstart, G_level. exact Ima1.
      + rewrite Gmt. clear. lia.
      + unfold lz_strat. rewrite G_level, G_strategy, G_match_length. exact Ifast.
      + unfold lz_strat. rewrite G_level, G_strategy, G_prev_length. exact Ifastpl.
      + unfold lz_strat. rewrite G_level, G_strategy, G_match_length, G_strstart, G_match_start, G_w_size, G_lookahead. exact Islow.
      + unfold lz_strat. rewrite G_level, G_strategy, G_match_length. exact Islow1.
      + rewrite G_level. intros Hlv. destruct (Ihash Hlv) as [Ins HC]. exists Ins. rewrite G_strstart, G_w_size, G_head, G_prev, G_hash_size. exact HC.
      + exists []. split; [exact DS3|]. intros _. rewrite zcov_nil, Gbs, G_strstart, G_match_available. clear -Ima. lia.
      + rewrite Gsn, G_sym_end, SE. clear -SZ. lia.
      + exact A3.
      + exact Bb3.
      + exact C3.
      + exact Hpo3.
      + rewrite G_lit_bufsize. rewrite <- Epbl in HV3. clear -HV3. lia.
      + exact Hpo03.
      + intros _. clear -B3. lia.
      + rewrite G_last_flush. exact Ilf.
      + rewrite G_status. exact Ilive.
      + rewrite G_status, Sst. unfold BUSY_STATE, INIT_STATE, GZIP_STATE. intros [E|E]; discriminate E.
      + rewrite G_status, Sst. unfold BUSY_STATE, GZIP_STATE. intros E; discriminate E.
      + rewrite G_wrap, G_status. intros Hn. exfalso. clear -Hn Swr. lia.
      + rewrite G_level. intros L0. exfalso. exact (Slz L0).
      + rewrite G_level. intros L0. exfalso. exact (Slz L0).
      + rewrite G_status, Sst. unfold BUSY_STATE, INIT_STATE. intros E; discriminate E.
      + rewrite G_status, Sst. unfold BUSY_STATE, FINISH_STATE. intros E; discriminate E.
      + unfold lz_strat. rewrite G_match_available, G_level, G_strategy. exact Imas.
      + rewrite Gsn. intros _; reflexivity.
    - exact CL3.
    - rewrite G_w_size. exact Ews.
    - rewrite G_hash_size. exact Ehs.
    - rewrite G_lit_bufsize. exact Epbl.
    - rewrite G_status. exact Sst.
    - rewrite G_wrap. exact Swr.
    - rewrite G_level. exact Slz.
    - exact FL3.
  Qed.
End FBO.
