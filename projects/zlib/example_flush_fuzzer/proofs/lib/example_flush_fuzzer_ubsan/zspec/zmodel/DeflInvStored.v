(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateInvHash DeflateInvKeep OverlayFBS DeflRoom.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import LmatchModel FillWinModel SendModel AdlerModel DeflFastModel TreesTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import RefFlushPend1 RefDeflStored2 RefDeflStored3 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8 RefDeflStored9 RefDeflStoredOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflInvTally DeflInvBits DeflInvStep DeflInvFbo DeflInvFw DeflInvFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac dsr := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd].
Tactic Notation "dsr" "in" hyp(H) := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd] in H.

Ltac drop_impl := repeat match goal with H : _ -> _ |- _ => clear H end.


Record z0same (s s' : deflate_state) : Prop := MkZ0 {
  z0_level : ds_level s' = ds_level s; z0_strategy : ds_strategy s' = ds_strategy s; z0_w_size : ds_w_size s' = ds_w_size s;
  z0_hash_size : ds_hash_size s' = ds_hash_size s; z0_lit_bufsize : ds_lit_bufsize s' = ds_lit_bufsize s;
  z0_sym_end : ds_sym_end s' = ds_sym_end s; z0_sym_next : ds_sym_next s' = ds_sym_next s;
  z0_match_length : ds_match_length s' = ds_match_length s; z0_prev_length : ds_prev_length s' = ds_prev_length s;
  z0_match_start : ds_match_start s' = ds_match_start s; z0_prev_match : ds_prev_match s' = ds_prev_match s;
  z0_match_available : ds_match_available s' = ds_match_available s; z0_ins_h : ds_ins_h s' = ds_ins_h s;
  z0_lookahead : ds_lookahead s' = ds_lookahead s; z0_last_flush : ds_last_flush s' = ds_last_flush s;
  z0_status : ds_status s' = ds_status s; z0_wrap : ds_wrap s' = ds_wrap s;
  z0_lfc : ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s; z0_dfc : ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s; z0_bfc : ds_bl_tree_fc s' = ds_bl_tree_fc s;
  z0_opt_len : ds_opt_len s' = ds_opt_len s; z0_static_len : ds_static_len s' = ds_static_len s }.

Lemma dinv_level0 : forall rm hb fz s s',
  dinvR rm hb fz s -> ds_level s = 0 -> cty s' -> z0same s s' ->
  0 <= ds_strstart s' <= 2 * ds_w_size s -> 0 <= ds_insert s' <= ds_strstart s' -> 0 <= ds_block_start s' <= ds_strstart s' ->
  0 <= ds_high_water s' <= 2 * ds_w_size s -> 0 <= ds_matches s' <= 2 ->
  0 <= ds_bi_valid s' <= 16 -> 0 <= ds_bi_buf s' < 2 ^ 16 -> 0 <= ds_pending s' -> 0 <= ds_pending_out s' ->
  8 * (ds_pending_out s' + ds_pending s') + ds_bi_valid s' <= 8 * (ds_lit_bufsize s * 4) ->
  (ds_pending s' = 0 -> ds_pending_out s' = 0) -> (ds_pending_out s' <> 0 -> ds_bi_valid s' < 8) ->
  (ds_status s = INIT_STATE \/ ds_status s = GZIP_STATE -> ds_pending s' = 0) ->
  dinvR rm hb fz s'.
Proof.
  intros rm hb fz s s' I L0 T' Z Hstr Hins Hbs Hhw Hmt Hbv Hbb Hp Hpo Hpop Hpo0 Hpobv Hinit.
  pose proof Z as [E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 _ _ _ E21 E22].
  pose proof I as [T Istr Ilook Isl Iins Ibs Ibs0 Ihw Iih Ims Ipm Iml Ipl Ima Ima1 Imt Ifast Ifastpl Islow Islow1 Ihash Isyms Iroom Ibv Ibb Ipend Ipout Ipop Ipo0 Ipobv Ilf Ilive Iinit Igz Ineg Ilk0 Isn0 Iinw Ifl Imas Ips].
  pose proof (Ilk0 L0) as LK. pose proof (Isn0 L0) as SN.
  destruct Isyms as (syms & D & _).
  assert (syms = []) as ->.
  { pose proof (sy_next _ _ D) as X. rewrite SN in X. destruct syms; [reflexivity | cbn in X; clear -X; lia]. }
  assert (DS' : dsyms [] s').
  { destruct D; constructor; rewrite ?E3, ?E5, ?E7; try assumption.
    - intros i d lc Hi. destruct i; discriminate Hi.
    - intros c Hc. unfold Freq. cbn [tree_fc]. rewrite (z0_lfc _ _ Z). apply sy_freq_l. exact Hc.
    - intros j Hj. unfold Freq. cbn [tree_fc]. rewrite (z0_dfc _ _ Z). apply sy_freq_d. exact Hj.
    - intros j Hj. unfold Freq. cbn [tree_fc]. rewrite (z0_bfc _ _ Z). apply sy_freq_b. exact Hj.
    - rewrite E21. assumption.
    - rewrite E22. assumption. }
  clear Z D.
  constructor; unfold lz_strat in *; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9, ?E10, ?E11, ?E12, ?E13, ?E14, ?E15, ?E16, ?E17; try assumption.
  all: try (intros X; split; [exact (Hinit X) | split; [exact (proj1 (proj2 (Iinit X))) | first [exact SN | rewrite E7; exact SN]]]).
  all: try (exists (@nil (Z * Z)); split; [exact DS' | intros L; exfalso; clear -L L0; lia]).
  all: drop_impl; clear T T'.
  all: try lia.
  all: intros; exfalso; lia.
Qed.

Lemma dcall_emit : forall ILEN OCAP tot0 s l st',
  dcall ILEN OCAP tot0 s -> Forall (fun b => 0 <= b < 256) l -> zlength l <= cs_avail_out (ds_strm s) ->
  cs_out_rev st' = List.rev_append l (cs_out_rev (ds_strm s)) ->
  cs_avail_out st' = cs_avail_out (ds_strm s) - zlength l ->
  cs_total_out st' = wrap64 (cs_total_out (ds_strm s) + zlength l) ->
  cs_next_in st' = cs_next_in (ds_strm s) -> cs_avail_in st' = cs_avail_in (ds_strm s) -> cs_total_in st' = cs_total_in (ds_strm s) ->
  cs_input st' = cs_input (ds_strm s) -> cs_adler st' = cs_adler (ds_strm s) -> cs_data_type st' = cs_data_type (ds_strm s) ->
  ds_wrap (set_strm s st') = ds_wrap s ->
  dcall ILEN OCAP tot0 (set_strm s st').
Proof.
  intros ILEN OCAP tot0 s l st' CL Hl Hle Eo Eao Eto Eni Eai Eti Ein Ead Edt Ew.
  assert (L0 : 0 <= zlength l) by apply Zle_0_nat.
  destruct CL; constructor; dsr; rewrite ?Eo, ?Eao, ?Eto, ?Eni, ?Eai, ?Eti, ?Ein, ?Ead, ?Edt; try assumption; try lia.
  - rewrite zlength_rev_append. lia.
  - apply Forall_rev_append; assumption.
  - rewrite dc_to, zlength_rev_append, wrap64_add_l. f_equal. lia.
Qed.

Lemma dcall_move : forall ILEN OCAP tot0 s n st',
  dcall ILEN OCAP tot0 s -> cty s -> 0 < n <= cs_avail_in (ds_strm s) -> n <= cs_avail_out (ds_strm s) ->
  let st := ds_strm s in
  let l := arr_slice (cs_input st) (cs_next_in st) n in
  cs_out_rev st' = List.rev_append l (cs_out_rev st) ->
  cs_avail_out st' = cs_avail_out st - n ->
  cs_total_out st' = wrap64 (cs_total_out st + n) ->
  cs_next_in st' = cs_next_in st + n -> cs_avail_in st' = cs_avail_in st - n -> cs_total_in st' = wrap64 (cs_total_in st + n) ->
  cs_input st' = cs_input st -> cs_data_type st' = cs_data_type st ->
  cs_adler st' = (if ds_wrap s =? 1 then adler32_upd (cs_adler st) l else if ds_wrap s =? 2 then crc32_upd (cs_adler st) l else cs_adler st) ->
  dcall ILEN OCAP tot0 (set_strm s st').
Proof.
  intros ILEN OCAP tot0 s n st' CL T Hn Hno. cbv zeta. intros Eo Eao Eto Eni Eai Eti Ein Edt Ead.
  assert (BY : Forall (fun b => 0 <= b < 256) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n)).
  { apply u8a_slice; [exact (ct_in _ T)|]. intros _. pose proof (dc_ni _ _ _ _ CL). pose proof (dc_in _ _ _ _ CL). rewrite (dc_ilen _ _ _ _ CL). lia. }
  assert (LEN : zlength (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n) = n) by (rewrite arr_slice_length; lia).
  pose proof (wrap64_range (cs_total_in (ds_strm s) + n)) as W64.
  destruct CL; constructor; dsr; rewrite ?Eo, ?Eao, ?Eto, ?Eni, ?Eai, ?Eti, ?Ein, ?Ead, ?Edt; try assumption; try lia.
  - rewrite zlength_rev_append, LEN. lia.
  - apply Forall_rev_append; assumption.
  - rewrite dc_to, zlength_rev_append, wrap64_add_l, LEN. f_equal. lia.
  - destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)].
    + pose proof (adler32_model_canon (cs_adler (ds_strm s)) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n)) as [A _]. unfold adler32_upd. lia.
    + pose proof (crc32_upd_range (cs_adler (ds_strm s)) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n) ltac:(intros b Hb; exact (proj1 (List.Forall_forall _ _) BY b Hb))). lia.
    + assumption.
  - intros W. rewrite W. cbn. apply adler_ok_canon. unfold adler32_upd. apply adler32_model_canon.
  - intros W. rewrite W. cbn. apply crc32_upd_range. intros b Hb. exact (proj1 (List.Forall_forall _ _) BY b Hb).
Qed.



Section STEPS.
  Variables (ILEN OCAP tot0 : Z).

  Lemma fp_all : forall s, dcall ILEN OCAP tot0 s -> ds_bi_valid s = 0 -> 0 <= ds_pending s <= cs_avail_out (ds_strm s) ->
    (ds_pending s = 0 -> ds_pending_out s = 0) ->
    ds_pending (flush_pending s) = 0 /\ ds_pending_out (flush_pending s) = 0
    /\ cs_avail_out (ds_strm (flush_pending s)) = cs_avail_out (ds_strm s) - ds_pending s.
  Proof.
    intros s CL BV HP HPO.
    assert (FB : tr_flush_bits s = s) by (unfold tr_flush_bits, bi_flush; rewrite BV; reflexivity).
    pose proof (dc_ao _ _ _ _ CL) as A0. pose proof (dc_out _ _ _ _ CL) as A1. pose proof (dc_ocap32 _ _ _ _ CL) as A2.
    assert (A3 : 0 <= zlength (cs_out_rev (ds_strm s))) by apply Zle_0_nat. clear CL.
    rewrite (flush_pending_eqm s) by (rewrite FB; lia).
    cbv zeta. rewrite FB. unfold fpm_len.
    replace (if cs_avail_out (ds_strm s) <? ds_pending s then cs_avail_out (ds_strm s) else ds_pending s) with (ds_pending s)
      by (destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) (ds_pending s)); lia).
    destruct (Z.eqb_spec (ds_pending s) 0) as [Z0|Z0].
    - rewrite Z0, (HPO Z0). repeat split; lia.
    - pose proof (fpm_post_fields s (ds_pending s)) as F. cbv zeta in F.
      destruct F as (F1 & F2 & _ & F4 & _). rewrite F1, F2, F4. rewrite Z.sub_diag, Z.eqb_refl. repeat split; reflexivity.
  Qed.

  Lemma fp_acct : forall s, ds_bi_valid s = 0 -> 0 <= ds_pending s < 2 ^ 32 -> 0 <= cs_avail_out (ds_strm s) ->
    cs_avail_in (ds_strm (flush_pending s)) = cs_avail_in (ds_strm s)
    /\ cs_avail_out (ds_strm (flush_pending s)) <= cs_avail_out (ds_strm s)
    /\ (0 < ds_pending s -> 0 < cs_avail_out (ds_strm s) -> cs_avail_out (ds_strm (flush_pending s)) < cs_avail_out (ds_strm s)).
  Proof.
    intros s BV HP HA.
    assert (FB : tr_flush_bits s = s) by (unfold tr_flush_bits, bi_flush; rewrite BV; reflexivity).
    rewrite (flush_pending_eqm s) by (rewrite FB; lia).
    cbv zeta. rewrite FB. unfold fpm_len.
    destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) (ds_pending s)) as [L|L].
    - destruct (Z.eqb_spec (cs_avail_out (ds_strm s)) 0) as [Z0|Z0].
      + split; [reflexivity|]. split; [lia|]. intros _ X. exfalso. lia.
      + pose proof (fpm_post_fields s (cs_avail_out (ds_strm s))) as F. cbv zeta in F.
        destruct F as (_ & _ & _ & F4 & _ & _ & F7 & _). rewrite F4, F7. split; [reflexivity|]. split; [lia|]. intros _ _. lia.
    - destruct (Z.eqb_spec (ds_pending s) 0) as [Z0|Z0].
      + split; [reflexivity|]. split; [lia|]. intros X _. exfalso. lia.
      + pose proof (fpm_post_fields s (ds_pending s)) as F. cbv zeta in F.
        destruct F as (_ & _ & _ & F4 & _ & _ & F7 & _). rewrite F4, F7. split; [reflexivity|]. split; [lia|]. intros _ _. lia.
  Qed.

  Lemma tsb0_facts : forall s last, cty s -> 0 <= ds_bi_valid s <= 16 -> 0 <= ds_bi_buf s < 2 ^ 16 -> 0 <= ds_pending s -> 0 <= last <= 1 ->
    let s1 := tr_stored_block s None 0 last in
    cty s1 /\ eproj s1 = eproj s /\ ds_bi_valid s1 = 0 /\ 0 <= ds_bi_buf s1 < 2 ^ 16
    /\ ds_pending s + 4 <= ds_pending s1 <= ds_pending s + 7 /\ 8 * ds_pending s1 <= 8 * ds_pending s + ds_bi_valid s + 42.
  Proof.
    intros s last T BV BB P Hl. cbv zeta.
    generalize (cty_tr_stored_block s None 0 last T ltac:(intros off E; discriminate E)) (ep_tr_stored_block s None 0 last)
      (tr_stored_block_bits s None 0 last ltac:(split; assumption) Hl ltac:(lia)).
    generalize (tr_stored_block s None 0 last). intros s1 T1 EP1 (B1 & V1 & Z1 & P1).
    unfold bvol in V1. destruct B1 as [A B C].
    split; [exact T1|]. split; [exact EP1|]. split; [exact Z1|]. split; [exact B|]. split; [lia|]. lia.
  Qed.

  Lemma hdr4_facts : forall s1 len, cty s1 ->
    let s2 := hdr4 s1 len in
    cty s2 /\ eproj s2 = eproj s1 /\ ds_bi_valid s2 = ds_bi_valid s1 /\ ds_bi_buf s2 = ds_bi_buf s1 /\ ds_pending s2 = ds_pending s1
    /\ ds_strm s2 = ds_strm s1 /\ ds_pending_out s2 = ds_pending_out s1.
  Proof.
    intros s1 len T. cbv zeta. unfold hdr4. cbv zeta.
    split; [apply cty_set_pending_buf; [exact T|]; repeat apply u8a_set; try apply wrap8_range; exact (ct_pb _ T)|].
    split; [apply ep_set_pending_buf; rewrite !arr_len_set; reflexivity|].
    dsr. repeat split; reflexivity.
  Qed.

  Lemma rbpost_shape : forall s n, 0 < n <= cs_avail_in (ds_strm s) -> exists st',
    rbpost s n = set_strm s st'
    /\ let st := ds_strm s in
       let l := arr_slice (cs_input st) (cs_next_in st) n in
       cs_out_rev st' = List.rev_append l (cs_out_rev st)
       /\ cs_avail_out st' = cs_avail_out st - n
       /\ cs_total_out st' = wrap64 (cs_total_out st + n)
       /\ cs_next_in st' = cs_next_in st + n /\ cs_avail_in st' = cs_avail_in st - n /\ cs_total_in st' = wrap64 (cs_total_in st + n)
       /\ cs_input st' = cs_input st /\ cs_data_type st' = cs_data_type st /\ cs_msg st' = cs_msg st
       /\ cs_adler st' = (if ds_wrap s =? 1 then adler32_upd (cs_adler st) l else if ds_wrap s =? 2 then crc32_upd (cs_adler st) l else cs_adler st).
  Proof.
    intros s n Hn. unfold rbpost, read_buf.
    replace (if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)) with n by (destruct (Z.ltb_spec n (cs_avail_in (ds_strm s))); lia).
    replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct s; dsr. destruct ds_strm; dsr.
    destruct (Z.eqb_spec ds_wrap 1) as [W1|W1]; [| destruct (Z.eqb_spec ds_wrap 2) as [W2|W2]]; dsr;
      eexists; (split; [reflexivity|]); cbv zeta; dsr; repeat split; reflexivity.
  Qed.
End STEPS.


Lemma dcall_consume : forall ILEN OCAP tot0 s n st',
  dcall ILEN OCAP tot0 s -> cty s -> 0 < n <= cs_avail_in (ds_strm s) ->
  let st := ds_strm s in
  let l := arr_slice (cs_input st) (cs_next_in st) n in
  cs_out_rev st' = cs_out_rev st -> cs_avail_out st' = cs_avail_out st -> cs_total_out st' = cs_total_out st ->
  cs_next_in st' = cs_next_in st + n -> cs_avail_in st' = cs_avail_in st - n -> cs_total_in st' = wrap64 (cs_total_in st + n) ->
  cs_input st' = cs_input st -> cs_data_type st' = cs_data_type st ->
  cs_adler st' = (if ds_wrap s =? 1 then adler32_upd (cs_adler st) l else if ds_wrap s =? 2 then crc32_upd (cs_adler st) l else cs_adler st) ->
  dcall ILEN OCAP tot0 (set_strm s st').
Proof.
  intros ILEN OCAP tot0 s n st' CL T Hn. cbv zeta. intros Eo Eao Eto Eni Eai Eti Ein Edt Ead.
  assert (BY : Forall (fun b => 0 <= b < 256) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n)).
  { apply u8a_slice; [exact (ct_in _ T)|]. intros _. pose proof (dc_ni _ _ _ _ CL). pose proof (dc_in _ _ _ _ CL). rewrite (dc_ilen _ _ _ _ CL). lia. }
  pose proof (wrap64_range (cs_total_in (ds_strm s) + n)) as W64.
  destruct CL; constructor; dsr; rewrite ?Eo, ?Eao, ?Eto, ?Eni, ?Eai, ?Eti, ?Ein, ?Ead, ?Edt; try assumption; try lia.
  - destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)].
    + pose proof (adler32_model_canon (cs_adler (ds_strm s)) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n)) as [A _]. unfold adler32_upd. lia.
    + pose proof (crc32_upd_range (cs_adler (ds_strm s)) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n) ltac:(intros b Hb; exact (proj1 (List.Forall_forall _ _) BY b Hb))). lia.
    + assumption.
  - intros W. rewrite W. cbn. apply adler_ok_canon. unfold adler32_upd. apply adler32_model_canon.
  - intros W. rewrite W. cbn. apply crc32_upd_range. intros b Hb. exact (proj1 (List.Forall_forall _ _) BY b Hb).
Qed.

Lemma rbw_shape : forall s n, 0 < n <= cs_avail_in (ds_strm s) -> exists st',
  rbw s n = set_insert (set_strstart (set_window (set_strm s st') (arr_upd (ds_window s) (ds_strstart s) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n)))
                                     (ds_strstart s + n)) (ds_insert s + MIN n (wrap32 (ds_w_size s - ds_insert s)))
  /\ let st := ds_strm s in
     let l := arr_slice (cs_input st) (cs_next_in st) n in
     cs_out_rev st' = cs_out_rev st /\ cs_avail_out st' = cs_avail_out st /\ cs_total_out st' = cs_total_out st
     /\ cs_next_in st' = cs_next_in st + n /\ cs_avail_in st' = cs_avail_in st - n /\ cs_total_in st' = wrap64 (cs_total_in st + n)
     /\ cs_input st' = cs_input st /\ cs_data_type st' = cs_data_type st /\ cs_msg st' = cs_msg st
     /\ cs_adler st' = (if ds_wrap s =? 1 then adler32_upd (cs_adler st) l else if ds_wrap s =? 2 then crc32_upd (cs_adler st) l else cs_adler st).
Proof.
  intros s n Hn. unfold rbw, rbc3post, ckpost, ckv. cbv zeta.
  destruct s; dsr. destruct ds_strm; dsr.
  destruct (Z.eqb_spec ds_wrap 1) as [W1|W1]; [| destruct (Z.eqb_spec ds_wrap 2) as [W2|W2]]; dsr;
    eexists; (split; [reflexivity|]); cbv zeta; dsr; repeat split; reflexivity.
Qed.


Section STORED.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).

  Record dst (s : deflate_state) : Prop := MkDST {
    st_cfg : dcfg s;
    st_inv : dinvR 3 0 true s;
    st_call : dcall ILEN OCAP tot0 s;
    st_ws : ds_w_size s = ws;
    st_hs : ds_hash_size s = hs;
    st_pbl : ds_lit_bufsize s * 4 = PBL;
    st_status : ds_status s = BUSY_STATE;
    st_wrap : 0 <= ds_wrap s;
    st_lv : ds_level s = 0 }.

  Record dsr0 (s : deflate_state) : Prop := MkDSR0 {
    sr_dst : dst s;
    sr_pend : ds_pending s = 0;
    sr_pout : ds_pending_out s = 0 }.

  Lemma dst_basics : forall s, dst s ->
    512 <= ws <= 32768 /\ 512 <= PBL <= 2 ^ 17 /\ ds_pending_buf_size s = PBL /\ arr_len (ds_pending_buf s) = PBL
    /\ arr_len (ds_window s) = 2 * ws /\ ds_window_size s = 2 * ws
    /\ ds_lookahead s = 0 /\ ds_sym_next s = 0 /\ 0 <= ds_block_start s <= ds_strstart s /\ ds_strstart s <= 2 * ws
    /\ 0 <= ds_insert s <= ds_strstart s /\ 0 <= ds_high_water s <= 2 * ws /\ 0 <= ds_matches s <= 2
    /\ 0 <= ds_bi_valid s <= 16 /\ 0 <= ds_bi_buf s < 2 ^ 16 /\ 0 <= ds_pending s /\ 0 <= ds_pending_out s
    /\ 8 * (ds_pending_out s + ds_pending s) + ds_bi_valid s <= 8 * PBL
    /\ 0 <= cs_avail_in (ds_strm s) /\ 0 <= cs_next_in (ds_strm s) /\ cs_next_in (ds_strm s) + cs_avail_in (ds_strm s) = ILEN /\ ILEN < 2 ^ 32
    /\ 0 <= cs_avail_out (ds_strm s) /\ cs_avail_out (ds_strm s) + zlength (cs_out_rev (ds_strm s)) = OCAP /\ OCAP < 2 ^ 32
    /\ 0 <= cs_total_in (ds_strm s) < 2 ^ 64 /\ 0 <= cs_adler (ds_strm s) < 2 ^ 32 /\ -2 <= ds_wrap s <= 2.
  Proof.
    intros s [C I CL Ews Ehs Epbl Sst Swr L0].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    pose proof I as [T Istr Ilook Isl Iins Ibs Ibs0 Ihw Iih Ims Ipm Iml Ipl Ima Ima1 Imt Ifast Ifastpl Islow Islow1 Ihash Isyms Iroom Ibv Ibb Ipend Ipout Ipop Ipo0 Ipobv Ilf Ilive Iinit Igz Ineg Ilk0 Isn0 Iinw Ifl Imas Ips].
    pose proof (Ilk0 L0) as LK. pose proof (Isn0 L0) as SN. pose proof (Ibs0 L0) as BS0.
    destruct CL. pose proof (cf_pbs _ C). pose proof (cf_bl _ C). pose proof (cf_wl _ C). pose proof (cf_wsz _ C). pose proof (cf_wrap _ C).
    drop_impl. clear T C I Isyms. repeat split; lia.
  Qed.

  Lemma dst_ep : forall s s', dst s -> eproj s' = eproj s -> cty s' ->
    0 <= ds_bi_valid s' <= 16 -> 0 <= ds_bi_buf s' < 2 ^ 16 -> 0 <= ds_pending s' ->
    8 * (ds_pending_out s' + ds_pending s') + ds_bi_valid s' <= 8 * PBL -> (ds_pending s' = 0 -> ds_pending_out s' = 0) ->
    (ds_pending_out s' <> 0 -> ds_bi_valid s' < 8) ->
    dst s'.
  Proof.
    intros s s' D E T' Hbv Hbb Hp Hpop Hpo0 Hpobv. pose proof (dst_basics s D) as BB. pose proof D as [C I CL Ews Ehs Epbl Sst Swr L0].
    pose proof (ep_kp _ _ E) as K.
    pose proof (ep_strstart _ _ E) as Q1. pose proof (ep_insert _ _ E) as Q2. pose proof (ep_block_start _ _ E) as Q3.
    pose proof (ep_high_water _ _ E) as Q4. pose proof (ep_matches _ _ E) as Q5. pose proof (ep_pending_out _ _ E) as Q6.
    pose proof (ep_strm _ _ E) as Q7. pose proof (ep_w_size _ _ E) as Q8. pose proof (ep_hash_size _ _ E) as Q9.
    pose proof (ep_lit_bufsize _ _ E) as Q10. pose proof (ep_status _ _ E) as Q11. pose proof (ep_wrap _ _ E) as Q12. pose proof (ep_level _ _ E) as Q13.
    constructor; rewrite ?Q7, ?Q8, ?Q9, ?Q10, ?Q11, ?Q12, ?Q13; try assumption.
    - exact (dcfg_kproj _ _ K C).
    - rewrite Q6 in Hpo0. rewrite Q6 in Hpobv. apply (dinv_level0 3 0 true s s' I L0 T'); rewrite ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6; try assumption; try (clear -BB Ews; lia).
      all: try (constructor; first [ exact (ep_level _ _ E) | exact (ep_strategy _ _ E) | exact (ep_w_size _ _ E) | exact (ep_hash_size _ _ E)
          | exact (ep_lit_bufsize _ _ E) | exact (ep_sym_end _ _ E) | exact (ep_sym_next _ _ E) | exact (ep_match_length _ _ E)
          | exact (ep_prev_length _ _ E) | exact (ep_match_start _ _ E) | exact (ep_prev_match _ _ E) | exact (ep_match_available _ _ E)
          | exact (ep_ins_h _ _ E) | exact (ep_lookahead _ _ E) | exact (ep_last_flush _ _ E) | exact (ep_status _ _ E) | exact (ep_wrap _ _ E)
          | exact (ep_dyn_ltree_fc _ _ E) | exact (ep_dyn_dtree_fc _ _ E) | exact (ep_bl_tree_fc _ _ E) | exact (ep_opt_len _ _ E) | exact (ep_static_len _ _ E) ]).
      all: try (rewrite Epbl in *; rewrite ?Q6 in Hpop; clear -Hpop; lia).
      all: try (rewrite Sst; unfold BUSY_STATE, INIT_STATE, GZIP_STATE; intros [X|X]; discriminate X).
    - destruct CL; constructor; rewrite ?Q7, ?Q12; assumption.
  Qed.

  Lemma dst_strm : forall s st, dst s -> dcall ILEN OCAP tot0 (set_strm s st) -> cs_input st = cs_input (ds_strm s) -> dst (set_strm s st).
  Proof.
    intros s st D CL' Hin. pose proof (dst_basics s D) as BB. pose proof D as [C I CL Ews Ehs Epbl Sst Swr L0].
    constructor; dsr; try assumption.
    - apply dcfg_set_strm. exact C.
    - apply (dinv_level0 3 0 true s _ I L0); dsr; try (clear -BB Ews; lia).
      all: try (apply cty_set_strm_in; [exact (di_cty _ _ _ _ I) | exact Hin]).
      all: try (constructor; reflexivity).
      all: try (rewrite Epbl; clear -BB; lia).
      all: try (exact (di_po0 _ _ _ _ I)). all: try (exact (di_pobv _ _ _ _ I)).
      all: try (rewrite Sst; unfold BUSY_STATE, INIT_STATE, GZIP_STATE; intros [X|X]; discriminate X).
  Qed.

  Lemma dst_bs : forall s v, dst s -> 0 <= v <= ds_strstart s -> dst (set_block_start s v).
  Proof.
    intros s v D Hv. pose proof (dst_basics s D) as BB. pose proof D as [C I CL Ews Ehs Epbl Sst Swr L0].
    constructor; dsr; try assumption.
    - apply dcfg_set_block_start. exact C.
    - apply (dinv_level0 3 0 true s _ I L0); dsr; try (clear -BB Hv Ews; lia).
      all: try (apply cty_set_block_start; exact (di_cty _ _ _ _ I)).
      all: try (constructor; reflexivity).
      all: try (rewrite Epbl; clear -BB; lia).
      all: try (exact (di_po0 _ _ _ _ I)). all: try (exact (di_pobv _ _ _ _ I)).
      all: try (rewrite Sst; unfold BUSY_STATE, INIT_STATE, GZIP_STATE; intros [X|X]; discriminate X).
    - destruct CL; constructor; dsr; assumption.
  Qed.

  Lemma dst_fp : forall s, dst s -> 0 <= ds_bi_valid s <= 16 ->
    dst (flush_pending s)
    /\ dcall ILEN OCAP tot0 (flush_pending s)
    /\ (cs_avail_out (ds_strm (flush_pending s)) <> 0 -> ds_pending (flush_pending s) = 0 /\ ds_pending_out (flush_pending s) = 0)
    /\ cs_avail_in (ds_strm (flush_pending s)) = cs_avail_in (ds_strm s) /\ cs_next_in (ds_strm (flush_pending s)) = cs_next_in (ds_strm s)
    /\ ds_bi_valid (flush_pending s) <= 7
    /\ kproj (flush_pending s) = kproj (set_pending_out (set_strm s (ds_strm (flush_pending s))) (ds_pending_out (flush_pending s))).
  Proof.
    intros s D Hbv. pose proof (dst_basics s D) as BB. pose proof D as [C I CL Ews Ehs Epbl Sst Swr L0].
    assert (FP : fp_inv PBL s).
    { constructor; unfold bvol; try (clear -BB; lia). 2: pose proof (di_po0 _ _ _ _ I) as X; exact X.
      split; [exact Hbv | exact (di_bb _ _ _ _ I) | exact (di_pend _ _ _ _ I)]. }
    destruct (flush_pending_inv ILEN OCAP tot0 PBL s FP CL (di_cty _ _ _ _ I))
      as (FP3 & CL3 & T3 & B3 & V3 & FL3 & KP3 & N3a & N3b & N3c & N3d & N3e & N3f & N3g & N3h & N3i & EP3).
    generalize FP3 CL3 T3 B3 V3 FL3 KP3 N3a N3b N3c N3d N3e N3f N3g N3h N3i EP3. generalize (flush_pending s). clear FP3 CL3 T3 B3 V3 FL3 KP3 N3a N3b N3c N3d N3e N3f N3g N3h N3i EP3.
    intros s3 FP3 CL3 T3 B3 V3 FL3 KP3 N3a N3b N3c N3d N3e N3f N3g N3h N3i EP3.
    pose proof (kp_spo_fields _ _ _ _ KP3) as F.
    destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20
                 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & F32 & F33 & F34 & F35 & F36 & F37 & F38 & F39
                 & F40 & F41 & F42 & F43 & F44 & F45).
    destruct FP3 as [[A3 Bb3 C3] Hpo3 HV3 HPBL3 Hpo03 _]. unfold bvol in HV3.
    split; [| split; [exact CL3 | split; [exact FL3 | split; [exact N3b | split; [exact N3a | split; [clear -B3; lia | exact KP3]]]]]].
    constructor; rewrite ?F1, ?F3, ?F8, ?F16, ?F30, ?F34; try assumption.
    - apply (dcfg_kproj _ _ KP3). apply dcfg_set_pending_out, dcfg_set_strm. exact C.
    - pose proof (ep_dyn_ltree_fc _ _ EP3) as X1. rewrite dyn_ltree_fc_set_pending_out, dyn_ltree_fc_set_strm in X1.
      pose proof (ep_dyn_dtree_fc _ _ EP3) as X2. rewrite dyn_dtree_fc_set_pending_out, dyn_dtree_fc_set_strm in X2.
      pose proof (ep_bl_tree_fc _ _ EP3) as X3. rewrite bl_tree_fc_set_pending_out, bl_tree_fc_set_strm in X3.
      pose proof (ep_opt_len _ _ EP3) as X4. rewrite opt_len_set_pending_out, opt_len_set_strm in X4.
      pose proof (ep_static_len _ _ EP3) as X5. rewrite static_len_set_pending_out, static_len_set_strm in X5.
      assert (Z3 : z0same s s3) by (constructor; assumption).
      clear X1 X2 X3.
      apply (dinv_level0 3 0 true s s3 I L0 T3 Z3); rewrite ?F24, ?F38, ?F20, ?F39, ?F37; try (clear -BB Ews; lia).
      all: try (clear -A3; lia). all: try exact Bb3. all: try exact C3. all: try exact Hpo3. all: try exact Hpo03.
      all: try (rewrite Epbl; clear -HV3; lia). all: try (intros _; clear -B3; lia).
      all: try (rewrite Sst; unfold BUSY_STATE, INIT_STATE, GZIP_STATE; intros [X|X]; discriminate X).
  Qed.

  Definition stripG (s : deflate_state) (last : Z) : deflate_state :=
    let len := slen s in
    let left := sleft s in
    let s1 := tr_stored_block s None 0 last in
    let s2 := hdr4 s1 len in
    let s3 := flush_pending s2 in
    let '(s4, len') := if negb (left =? 0) then (awpost s3 (sL s), len - sL s) else (s3, len) in
    if negb (len' =? 0) then rbpost s4 len' else s4.

  Definition stripG_ok (last : Z) (s : deflate_state) : Prop :=
    let len := slen s in
    let left := sleft s in
    let s1 := tr_stored_block s None 0 last in
    let s2 := hdr4 s1 len in
    let s3 := flush_pending s2 in
    let L := sL s in
    let s4 := (if negb (left =? 0) then awpost s3 L else s3) in
    let len' := (if negb (left =? 0) then len - L else len) in
    tripA_wf s /\ BINV PBL s /\ 4 <= ds_pending s1 <= PBL /\ fp_ok PBL OCAP s2
    /\ (left <> 0 -> winA_ok ws OCAP s3 L) /\ rdA_ok ILEN OCAP s4 len'.

  Lemma tripA_eqG : forall s, tripA s = stripG s 0. Proof. reflexivity. Qed.
  Lemma tripB_eqG : forall s, tripB s = stripG s (slast s). Proof. reflexivity. Qed.
  Lemma tripA_ok_eqG : forall s, tripA_ok ws PBL ILEN OCAP s = stripG_ok 0 s. Proof. reflexivity. Qed.
  Lemma tripB_ok_eqG : forall s, tripB_ok ws PBL ILEN OCAP s = stripG_ok (slast s) s. Proof. reflexivity. Qed.

  Lemma strip_win : forall s3 L, dsr0 s3 -> 0 <= L -> ds_block_start s3 + L <= ds_strstart s3 -> L <= cs_avail_out (ds_strm s3) ->
    winA_ok ws OCAP s3 L
    /\ dsr0 (awpost s3 L)
    /\ cs_avail_out (ds_strm (awpost s3 L)) = cs_avail_out (ds_strm s3) - L
    /\ cs_avail_in (ds_strm (awpost s3 L)) = cs_avail_in (ds_strm s3)
    /\ ds_bi_valid (awpost s3 L) = ds_bi_valid s3.
  Proof.
    intros s3 L [D P0 PO0] HL Hbl Hao. pose proof (dst_basics s3 D) as BB. pose proof D as [C I CL Ews Ehs Epbl Sst Swr L0].
    destruct BB as (Wr & Pr & Epbs & Lpb & Lw & Wsz & LK & SN & Hbs & Hstr & Hins & Hhw & Hmt & Hbv & Hbb & Hp & Hpo & Hpop & Hai & Hni & Hin & Hil & Ha0 & Hout & Hoc & Hti & Had & Hwr).
    pose proof (ct_win _ (di_cty _ _ _ _ I)) as TW. unfold u8a in TW. rewrite Lw in TW.
    assert (TO : 0 <= cs_total_out (ds_strm s3) < 2 ^ 64) by (rewrite (dc_to _ _ _ _ CL); apply wrap64_range).
    assert (OL : 0 <= zlength (cs_out_rev (ds_strm s3))) by apply Zle_0_nat.
    split.
    { unfold winA_ok. rewrite <- zlength_of_nat. split; [lia|]. split; [lia|]. split; [exact TW|]. clear TW. lia. }
    assert (BY : Forall (fun b => 0 <= b < 256) (arr_slice (ds_window s3) (ds_block_start s3) L)).
    { apply u8a_slice; [exact (ct_win _ (di_cty _ _ _ _ I)) | intros; lia]. }
    assert (LEN : zlength (arr_slice (ds_window s3) (ds_block_start s3) L) = L) by (rewrite arr_slice_length; lia).
    unfold awpost. cbv zeta.
    match goal with |- context [set_strm s3 ?st] =>
      assert (CL4 : dcall ILEN OCAP tot0 (set_strm s3 st))
        by (apply (dcall_emit ILEN OCAP tot0 s3 (arr_slice (ds_window s3) (ds_block_start s3) L)); dsr; rewrite ?LEN; try reflexivity; try assumption; lia);
      pose proof (dst_strm s3 st D CL4 eq_refl) as D4
    end.
    split; [| dsr; repeat split; try reflexivity; lia].
    split; [| dsr; assumption ..]. apply dst_bs; [exact D4 | dsr; lia].
  Qed.

  Lemma strip_direct : forall s4 n, dsr0 s4 -> 0 <= ds_bi_valid s4 <= 16 -> 0 <= n <= cs_avail_in (ds_strm s4) -> n <= cs_avail_out (ds_strm s4) ->
    rdA_ok ILEN OCAP s4 n
    /\ dsr0 (if negb (n =? 0) then rbpost s4 n else s4)
    /\ cs_avail_out (ds_strm (if negb (n =? 0) then rbpost s4 n else s4)) = cs_avail_out (ds_strm s4) - n
    /\ cs_avail_in (ds_strm (if negb (n =? 0) then rbpost s4 n else s4)) = cs_avail_in (ds_strm s4) - n.
  Proof.
    intros s4 n DR Hbv Hn Hno. pose proof DR as [D P0 PO0]. pose proof (dst_basics s4 D) as BB. pose proof D as [C I CL Ews Ehs Epbl Sst Swr L0].
    destruct BB as (Wr & Pr & Epbs & Lpb & Lw & Wsz & LK & SN & Hbs & Hstr & Hins & Hhw & Hmt & _ & Hbb & Hp & Hpo & Hpop & Hai & Hni & Hin & Hil & Ha0 & Hout & Hoc & Hti & Had & Hwr).
    pose proof (ct_in _ (di_cty _ _ _ _ I)) as TI. unfold u8a in TI. rewrite (dc_ilen _ _ _ _ CL) in TI.
    assert (TO : 0 <= cs_total_out (ds_strm s4) < 2 ^ 64) by (rewrite (dc_to _ _ _ _ CL); apply wrap64_range).
    assert (OL : 0 <= zlength (cs_out_rev (ds_strm s4))) by apply Zle_0_nat.
    split.
    { unfold rdA_ok. rewrite <- zlength_of_nat. split; [lia|]. split; [lia|]. split; [lia|]. intros Hz.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact TI|]. split; [lia|].
      split; [intros W; apply adler_ok_canon; exact (dc_ad1 _ _ _ _ CL W)|]. clear TI. lia. }
    destruct (Z.eqb_spec n 0) as [Z0|Z0]; cbn [negb].
    - split; [exact DR | lia].
    - destruct (rbpost_shape s4 n ltac:(lia)) as (st' & E & F). cbv zeta in F. rewrite E.
      destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
      assert (CL5 : dcall ILEN OCAP tot0 (set_strm s4 st')).
      { apply (dcall_move ILEN OCAP tot0 s4 n st' CL (di_cty _ _ _ _ I) ltac:(lia) Hno); assumption. }
      split; [| dsr; split; [exact F2 | exact F5]].
      split; [exact (dst_strm s4 st' D CL5 F7) | dsr; exact P0 | dsr; exact PO0].
  Qed.
  Lemma strip_run : forall s last, dsr0 s -> hdrb s <= cs_avail_out (ds_strm s) -> 0 <= last <= 1 ->
    stripG_ok last s
    /\ dsr0 (stripG s last)
    /\ cs_avail_out (ds_strm (stripG s last)) <= cs_avail_out (ds_strm s) - 4
    /\ cs_avail_in (ds_strm (stripG s last)) <= cs_avail_in (ds_strm s).
  Proof.
    intros s last [D P0 PO0] Hh Hl. pose proof (dst_basics s D) as BB. pose proof D as [C I CL Ews Ehs Epbl Sst Swr L0].
    destruct BB as (Wr & Pr & Epbs & Lpb & Lw & Wsz & LK & SN & Hbs & Hstr & Hins & Hhw & Hmt & Hbv & Hbb & Hp & Hpo & Hpop & Hai & Hni & Hin & Hil & Hao & Hout & Hoc & Hti & Had & Hwr).
    pose proof (hdrb_range s Hbv) as HR.
    assert (Esl : sleft s = ds_strstart s - ds_block_start s) by reflexivity.
    pose proof (sL1_range s ltac:(rewrite Esl; lia) Hai) as (R1 & R1a & R1b).
    pose proof (slen_range s ltac:(rewrite Esl; lia) Hai Hh) as (R2 & R2a & R2b & R2c).
    assert (RL : 0 <= sL s <= slen s /\ sL s <= sleft s /\ slen s - sL s <= cs_avail_in (ds_strm s)
                 /\ (sleft s = 0 -> sL s = 0)).
    { unfold sL. unfold MAX_STORED in *. destruct (Z.ltb_spec (slen s) (sleft s)); lia. }
    assert (TO : 0 <= cs_total_out (ds_strm s) < 2 ^ 64) by (rewrite (dc_to _ _ _ _ CL); apply wrap64_range).
    assert (OL : 0 <= zlength (cs_out_rev (ds_strm s))) by apply Zle_0_nat.
    unfold stripG_ok, stripG. cbv zeta.
    generalize (tsb0_facts s last (di_cty _ _ _ _ I) Hbv Hbb Hp Hl).
    generalize (tr_stored_block s None 0 last). intros s1 (T1 & EP1 & BV1 & BB1 & P1 & P1b).
    rewrite P0 in P1, P1b.
    assert (Hp1 : ds_pending s1 <= hdrb s) by (unfold hdrb; apply Z.div_le_lower_bound; lia).
    pose proof (ep_pending_out _ _ EP1) as PO1. rewrite PO0 in PO1. pose proof (ep_strm _ _ EP1) as SM1.
    pose proof (ep_len_pending_buf _ _ EP1) as PL1.
    assert (D1 : dst s1) by (apply (dst_ep s s1 D EP1 T1); rewrite ?PO1; lia).
    generalize (hdr4_facts s1 (slen s) T1). generalize (hdr4 s1 (slen s)). intros s2 (T2 & EP2 & BV2 & BB2 & P2 & SM2 & PO2).
    assert (D2 : dst s2) by (apply (dst_ep s1 s2 D1 EP2 T2); rewrite ?BV2, ?BB2, ?P2, ?PO2, ?PO1; lia).
    pose proof (ep_len_pending_buf _ _ EP2) as PL2.
    pose proof (st_call _ D2) as CL2.
    destruct (fp_all ILEN OCAP tot0 s2 CL2 ltac:(rewrite BV2; exact BV1) ltac:(rewrite P2, SM2, SM1; lia) ltac:(rewrite P2; intros X; lia)) as (P3 & PO3 & AO3).
    destruct (dst_fp s2 D2 ltac:(rewrite BV2, BV1; lia)) as (D3 & CL3 & _ & AI3 & NI3 & BV3 & KP3).
    rewrite P2, SM2, SM1 in AO3. rewrite SM2, SM1 in AI3.
    pose proof (kp_block_start _ _ KP3) as BS3. rewrite block_start_set_pending_out, block_start_set_strm in BS3.
    pose proof (kp_strstart _ _ KP3) as ST3. rewrite strstart_set_pending_out, strstart_set_strm in ST3.
    rewrite (ep_block_start _ _ EP2), (ep_block_start _ _ EP1) in BS3. rewrite (ep_strstart _ _ EP2), (ep_strstart _ _ EP1) in ST3.
    pose proof (di_bv _ _ _ _ (st_inv _ D3)) as BV3'.
    generalize D3 CL3 AI3 BV3 P3 PO3 AO3 BS3 ST3 BV3'. generalize (flush_pending s2). clear D3 CL3 AI3 NI3 BV3 P3 PO3 AO3 BS3 ST3 BV3' KP3.
    intros s3 D3 CL3 AI3 BV3 P3 PO3 AO3 BS3 ST3 BV3'.
    assert (DR3 : dsr0 s3) by (split; assumption).
    assert (FB2 : tr_flush_bits s2 = s2) by (unfold tr_flush_bits, bi_flush; rewrite BV2, BV1; reflexivity).
    assert (FPOK : fp_ok PBL OCAP s2).
    { unfold fp_ok. rewrite FB2. cbv zeta. rewrite SM2, SM1, <- zlength_of_nat. unfold BINV. rewrite BV2, BV1, BB2, P2, PO2, PO1.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact TO|].
      pose proof (ct_pb _ T2) as TP. unfold u8a in TP. rewrite PL2, PL1, Lpb in TP. exact TP. }
    destruct (Z.eqb_spec (sleft s) 0) as [Z0|Z0]; cbn [negb].
    -
      destruct (strip_direct s3 (slen s) DR3 ltac:(lia) ltac:(rewrite AI3; lia) ltac:(rewrite AO3; lia)) as (RD & DR5 & AO5 & AI5).
      split; [| split; [exact DR5 | rewrite AO5, AO3, AI5, AI3; lia]].
      split; [unfold tripA_wf; lia|]. split; [unfold BINV; lia|]. split; [lia|]. split; [exact FPOK|].
      split; [intros X; exfalso; exact (X Z0) | exact RD].
    -
      destruct (strip_win s3 (sL s) DR3 ltac:(lia) ltac:(rewrite BS3, ST3, Esl in *; lia) ltac:(rewrite AO3; lia)) as (WOK & DR4 & AO4 & AI4 & BV4).
      destruct (strip_direct (awpost s3 (sL s)) (slen s - sL s) DR4 ltac:(rewrite BV4; lia) ltac:(rewrite AI4, AI3; lia) ltac:(rewrite AO4, AO3; lia)) as (RD & DR5 & AO5 & AI5).
      split; [| split; [exact DR5 | rewrite AO5, AO4, AO3, AI5, AI4, AI3; lia]].
      split; [unfold tripA_wf; lia|]. split; [unfold BINV; lia|]. split; [lia|]. split; [exact FPOK|].
      split; [intros _; exact WOK | exact RD].
  Qed.

  Lemma dsr0_wf : forall s, dsr0 s -> tripA_wf s /\ 0 <= ds_block_start s <= ds_strstart s /\ ds_strstart s < 2 ^ 32 /\ 0 <= cs_avail_out (ds_strm s).
  Proof.
    intros s [D P0 PO0]. pose proof (dst_basics s D) as BB. assert (OL : 0 <= zlength (cs_out_rev (ds_strm s))) by apply Zle_0_nat.
    unfold tripA_wf. repeat split; lia.
  Qed.

  Lemma sloopA_run : forall flush mb fuel s, dsr0 s -> flush <> Z_FINISH -> cs_avail_out (ds_strm s) < Z.of_nat fuel ->
    loopA_ok ws PBL ILEN OCAP flush mb fuel s
    /\ let '(s', last) := deflate_stored_loop fuel s flush mb in
       dsr0 s' /\ last = 0 /\ cs_avail_in (ds_strm s') <= cs_avail_in (ds_strm s)
       /\ cs_avail_out (ds_strm s') <= cs_avail_out (ds_strm s)
       /\ (ds_strm s' = ds_strm s \/ cs_avail_out (ds_strm s') < cs_avail_out (ds_strm s)).
  Proof.
    intros flush mb. induction fuel as [|fuel IH]; intros s DR Hf HM.
    { exfalso. pose proof (dsr0_wf s DR). cbn in HM. lia. }
    pose proof (dsr0_wf s DR) as (WF & Hbs & Hss & Hao).
    cbn [loopA_ok]. rewrite (loopA_model flush mb fuel s Hf Hbs Hss).
    destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) (hdrb s)) as [B|B].
    - split; [intros X; exfalso; lia|]. split; [exact DR|]. split; [reflexivity|]. split; [lia|]. split; [lia | left; reflexivity].
    - destruct (strip_run s 0 DR B ltac:(lia)) as (TOK & DR1 & AO1 & AI1). rewrite <- tripA_eqG in DR1, AO1, AI1.
      split.
      + intros _. split; [rewrite tripA_ok_eqG; exact TOK|]. intros _.
        exact (proj1 (IH (tripA s) DR1 Hf ltac:(rewrite Nat2Z.inj_succ in HM; lia))).
      + destruct (sbrk flush mb s); [split; [exact DR|]; split; [reflexivity|]; split; [lia|]; split; [lia | left; reflexivity]|].
        pose proof (proj2 (IH (tripA s) DR1 Hf ltac:(rewrite Nat2Z.inj_succ in HM; lia))) as X. cbv zeta in X.
        destruct (deflate_stored_loop fuel (tripA s) flush mb) as [s' last]. destruct X as (X1 & X2 & X3 & X4 & X5).
        split; [exact X1|]. split; [exact X2|]. split; [lia|]. split; [lia|]. right. lia.
  Qed.

  Lemma sloopB_run : forall mb fuel s, dsr0 s -> cs_avail_out (ds_strm s) < Z.of_nat fuel ->
    loopB_ok ws PBL ILEN OCAP mb fuel s
    /\ let '(s', last) := deflate_stored_loop fuel s Z_FINISH mb in
       dsr0 s' /\ (last = 0 \/ last = 1) /\ cs_avail_in (ds_strm s') <= cs_avail_in (ds_strm s)
       /\ cs_avail_out (ds_strm s') <= cs_avail_out (ds_strm s)
       /\ (ds_strm s' = ds_strm s \/ cs_avail_out (ds_strm s') < cs_avail_out (ds_strm s)).
  Proof.
    intros mb. induction fuel as [|fuel IH]; intros s DR HM.
    { exfalso. pose proof (dsr0_wf s DR). cbn in HM. lia. }
    pose proof (dsr0_wf s DR) as (WF & Hbs & Hss & Hao).
    cbn [loopB_ok]. rewrite (loopB_model mb fuel s Hbs Hss).
    pose proof (slast_range s) as SL.
    destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) (hdrb s)) as [B|B].
    - split; [split; [exact WF | intros X; exfalso; lia]|]. split; [exact DR|]. split; [left; reflexivity|]. split; [lia|]. split; [lia | left; reflexivity].
    - destruct (strip_run s (slast s) DR B ltac:(lia)) as (TOK & DR1 & AO1 & AI1). rewrite <- tripB_eqG in DR1, AO1, AI1.
      split.
      + split; [exact WF|]. intros _. split; [rewrite tripB_ok_eqG; exact TOK|]. intros _ _.
        exact (proj1 (IH (tripB s) DR1 ltac:(rewrite Nat2Z.inj_succ in HM; lia))).
      + destruct (sbrkB mb s); [split; [exact DR|]; split; [left; reflexivity|]; split; [lia|]; split; [lia | left; reflexivity]|].
        destruct (Z.eqb_spec (slast s) 0) as [E|E].
        * pose proof (proj2 (IH (tripB s) DR1 ltac:(rewrite Nat2Z.inj_succ in HM; lia))) as X. cbv zeta in X.
          destruct (deflate_stored_loop fuel (tripB s) Z_FINISH mb) as [s' last]. destruct X as (X1 & X2 & X3 & X4 & X5).
          split; [exact X1|]. split; [exact X2|]. split; [lia|]. split; [lia|]. right. lia.
        * split; [exact DR1|]. split; [exact SL|]. split; [exact AI1|]. split; [lia|]. right. lia.
  Qed.

  Lemma dst_geo : forall s s', dst s -> z0same s s' -> ds_strm s' = ds_strm s ->
    ds_pending s' = ds_pending s -> ds_pending_out s' = ds_pending_out s -> ds_bi_valid s' = ds_bi_valid s -> ds_bi_buf s' = ds_bi_buf s ->
    dcfg s' -> cty s' ->
    0 <= ds_strstart s' <= 2 * ws -> 0 <= ds_insert s' <= ds_strstart s' -> 0 <= ds_block_start s' <= ds_strstart s' ->
    0 <= ds_high_water s' <= 2 * ws -> 0 <= ds_matches s' <= 2 -> dst s'.
  Proof.
    intros s s' D Z SM P PO BV BBq C' T' Hstr Hins Hbs Hhw Hmt. pose proof (dst_basics s D) as BB. pose proof D as [C I CL Ews Ehs Epbl Sst Swr L0].
    constructor; rewrite ?SM, ?(z0_w_size _ _ Z), ?(z0_hash_size _ _ Z), ?(z0_lit_bufsize _ _ Z), ?(z0_status _ _ Z), ?(z0_wrap _ _ Z), ?(z0_level _ _ Z); try assumption.
    - apply (dinv_level0 3 0 true s s' I L0 T' Z); rewrite ?P, ?PO, ?BV, ?BBq; try (clear -BB Ews Hstr Hins Hbs Hhw Hmt; lia).
      all: try (exact (di_po0 _ _ _ _ I)). all: try (exact (di_pobv _ _ _ _ I)).
      all: try (rewrite Epbl; clear -BB; lia).
      all: try (rewrite Sst; unfold BUSY_STATE, INIT_STATE, GZIP_STATE; intros [X|X]; discriminate X).
    - destruct CL; constructor; rewrite ?SM, ?(z0_wrap _ _ Z); assumption.
  Qed.

  Lemma sused_run : forall ain0 s1, dsr0 s1 -> 0 <= ain0 < 2 ^ 32 -> cs_avail_in (ds_strm s1) <= ain0 ->
    ain0 - cs_avail_in (ds_strm s1) <= cs_next_in (ds_strm s1) ->
    used_ok ws ILEN ain0 s1 /\ dsr0 (used_post ain0 s1) /\ ds_strm (used_post ain0 s1) = ds_strm s1.
  Proof.
    intros ain0 s1 DR Ha0 Hle Hni. pose proof DR as [D P0 PO0]. pose proof (dst_basics s1 D) as BB. pose proof D as [C I CL Ews Ehs Epbl Sst Swr L0].
    destruct BB as (Wr & Pr & Epbs & Lpb & Lw & Wsz & LK & SN & Hbs & Hstr & Hins & Hhw & Hmt & Hbv & Hbb & Hp & Hpo & Hpop & Hai & Hni0 & Hin & Hil & Hao & Hout & Hoc & Hti & Had & Hwr).
    pose proof (di_cty _ _ _ _ I) as T. pose proof (ct_in _ T) as TI. pose proof (ct_win _ T) as TW.
    assert (TI' : forall j, 0 <= j < ILEN -> 0 <= arr_get (cs_input (ds_strm s1)) j < 256) by (intros j Hj; apply TI; rewrite (dc_ilen _ _ _ _ CL); exact Hj).
    assert (TW' : forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window s1) j < 256) by (intros j Hj; apply TW; rewrite Lw; exact Hj).
    assert (EU : sused ain0 s1 = ain0 - cs_avail_in (ds_strm s1)) by (unfold sused; apply wrap32_id; lia).
    assert (HW : forall u, dst u -> ds_w_size u = ws -> dst (hwpost u) /\ ds_strm (hwpost u) = ds_strm u /\ ds_pending (hwpost u) = ds_pending u /\ ds_pending_out (hwpost u) = ds_pending_out u
                           /\ ds_strstart (hwpost u) = ds_strstart u /\ 0 <= ds_high_water (hwpost u) <= 2 * ws).
    { intros u Du Eu. pose proof (dst_basics u Du) as BBu. unfold hwpost. destruct (Z.ltb_spec (ds_high_water u) (ds_strstart u)).
      - split; [| dsr; repeat split; try reflexivity; lia].
        apply (dst_geo u _ Du); dsr; try reflexivity; try lia.
        + constructor; reflexivity.
        + apply dcfg_set_high_water. exact (st_cfg _ Du).
        + apply cty_set_high_water. exact (di_cty _ _ _ _ (st_inv _ Du)).
      - split; [exact Du|]. repeat split; try reflexivity; lia. }
    unfold used_ok, used_post. cbv zeta. rewrite EU.
    destruct (Z.eqb_spec (ain0 - cs_avail_in (ds_strm s1)) 0) as [U0|U0]; cbn [negb].
    -
      destruct (HW s1 D Ews) as (Dh & SMh & Ph & POh & STh & HWh).
      split; [| split; [split; [exact Dh | rewrite Ph; exact P0 | rewrite POh; exact PO0] | exact SMh]].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros X; exfalso; exact (X U0)|]. lia.
    - set (u := ain0 - cs_avail_in (ds_strm s1)) in *.
      assert (Hu : 0 < u <= cs_next_in (ds_strm s1)) by lia.
      assert (UP : let s2 := set_block_start (upd_used s1 u) (ds_strstart (upd_used s1 u)) in
                   dst s2 /\ ds_strm s2 = ds_strm s1 /\ ds_pending s2 = ds_pending s1 /\ ds_pending_out s2 = ds_pending_out s1
                   /\ 0 <= ds_strstart s2 <= 2 * ws /\ ds_w_size s2 = ws
                   /\ (u < ws -> let s1' := (if ds_window_size s1 - ds_strstart s1 <=? u then upd_slide s1 else s1) in
                         ds_strm s1' = ds_strm s1 /\ 0 <= ds_strstart s1' /\ ds_strstart s1' + u <= 2 * ws /\ 0 <= ds_insert s1' <= 2 * ws)).
      { cbv zeta. unfold upd_used. destruct (Z.leb_spec (ds_w_size s1) u) as [BG|BG].
        -
          unfold upd_big. cbv zeta. dsr. rewrite Ews.
          assert (BY : Forall (fun b => 0 <= b < 256) (arr_slice (cs_input (ds_strm s1)) (cs_next_in (ds_strm s1) - ws) ws)).
          { apply u8a_slice; [exact TI | intros _; rewrite (dc_ilen _ _ _ _ CL); lia]. }
          split; [| repeat split; try reflexivity; try lia; intros X; exfalso; lia].
          apply (dst_geo s1 _ D); dsr; try reflexivity; try lia.
          + constructor; reflexivity.
          + apply dcfg_set_block_start, dcfg_set_insert, dcfg_set_strstart. apply dcfg_set_window; [apply dcfg_set_matches; exact C | rewrite arr_len_upd; reflexivity].
          + apply cty_set_block_start, cty_set_insert, cty_set_strstart. apply cty_set_window; [apply cty_set_matches; exact T | apply u8a_upd; [exact TW | exact BY]].
        -
          unfold upd_cp. cbv zeta.
          assert (SL : let s1' := (if ds_window_size s1 - ds_strstart s1 <=? u then upd_slide s1 else s1) in
                       (dcfg s1' /\ cty s1') /\ ds_strm s1' = ds_strm s1 /\ ds_pending s1' = ds_pending s1 /\ ds_pending_out s1' = ds_pending_out s1
                       /\ ds_w_size s1' = ws /\ 0 <= ds_strstart s1' /\ ds_strstart s1' + u <= 2 * ws /\ 0 <= ds_insert s1' <= ds_strstart s1'
                       /\ ds_bi_valid s1' = ds_bi_valid s1 /\ ds_bi_buf s1' = ds_bi_buf s1 /\ z0same s1 s1'
                       /\ arr_len (ds_window s1') = 2 * ws /\ u8a (ds_window s1') /\ cs_input (ds_strm s1') = cs_input (ds_strm s1)
                       /\ 0 <= ds_matches s1' <= 2 /\ 0 <= ds_high_water s1' <= 2 * ws).
          { cbv zeta. rewrite Wsz. destruct (Z.leb_spec (2 * ws - ds_strstart s1) u) as [SLc|SLc].
            - unfold upd_slide. cbv zeta. dsr. rewrite Ews.
              assert (WB : u8a (arr_blit (ds_window s1) 0 (ds_window s1) ws (ds_strstart s1 - ws))).
              { apply u8a_blit; [exact TW | intros _; rewrite Lw; lia | exact TW]. }
              match goal with |- context [dcfg ?x /\ cty _] =>
                assert (Ex : exists m i, x = set_insert (set_matches (set_window (set_strstart s1 (ds_strstart s1 - ws)) (arr_blit (ds_window s1) 0 (ds_window s1) ws (ds_strstart s1 - ws))) m) i
                               /\ 0 <= m <= 2 /\ 0 <= i <= ds_strstart s1 - ws)
              end.
              { destruct (Z.ltb_spec (ds_matches s1) 2); cbv iota; dsr; destruct (Z.ltb_spec (ds_strstart s1 - ws) (ds_insert s1)); cbv iota; dsr;
                  [ exists (ds_matches s1 + 1), (ds_strstart s1 - ws) | exists (ds_matches s1 + 1), (ds_insert s1)
                  | exists (ds_matches s1), (ds_strstart s1 - ws) | exists (ds_matches s1), (ds_insert s1) ];
                  (split; [destruct s1; reflexivity|]); lia. }
              destruct Ex as (m & i & -> & Hm & Hi). dsr.
              split; [| rewrite arr_len_blit, Lw; repeat match goal with |- _ /\ _ => split end; first [reflexivity | exact WB | (constructor; reflexivity) | lia]].
              split.
              + apply dcfg_set_insert, dcfg_set_matches. apply dcfg_set_window; [apply dcfg_set_strstart; exact C | rewrite arr_len_blit; reflexivity].
              + apply cty_set_insert, cty_set_matches. apply cty_set_window; [apply cty_set_strstart; exact T | exact WB].
            - rewrite Lw. split; [split; [exact C | exact T]|]. repeat match goal with |- _ /\ _ => split end; first [reflexivity | exact TW | (constructor; reflexivity) | lia]. }
          cbv zeta in SL.
          generalize SL. generalize (if ds_window_size s1 - ds_strstart s1 <=? u then upd_slide s1 else s1).
          intros s1' ([C' T'] & SM' & P' & PO' & WS' & ST' & STU & INS' & BV' & BBq' & Z' & LW' & TW1 & IN' & MT' & HW').
          dsr. rewrite SM', WS'.
          assert (BY : Forall (fun b => 0 <= b < 256) (arr_slice (cs_input (ds_strm s1)) (cs_next_in (ds_strm s1) - u) u)).
          { apply u8a_slice; [exact TI | intros _; rewrite (dc_ilen _ _ _ _ CL); lia]. }
          assert (HM : 0 <= MIN u (wrap32 (ws - ds_insert s1')) <= u).
          { unfold MIN. pose proof (wrap32_range (ws - ds_insert s1')). destruct (Z.ltb_spec (wrap32 (ws - ds_insert s1')) u); lia. }
          split; [| repeat split; try reflexivity; try lia; intros _; repeat split; lia].
          apply (dst_geo s1 _ D); dsr; rewrite ?SM'; try reflexivity; try lia.
          + destruct Z'; constructor; dsr; assumption.
          + apply dcfg_set_block_start, dcfg_set_insert, dcfg_set_strstart. apply dcfg_set_window; [exact C' | rewrite arr_len_upd; reflexivity].
          + apply cty_set_block_start, cty_set_insert, cty_set_strstart. apply cty_set_window; [exact T' | apply u8a_upd; [exact TW1 | rewrite ?IN'; exact BY]]. }
      cbv zeta in UP. destruct UP as (D2 & SM2 & P2 & PO2 & ST2 & WS2 & SL2).
      destruct (HW _ D2 WS2) as (Dh & SMh & Ph & POh & STh & HWh).
      split; [| split; [split; [exact Dh | rewrite Ph, P2; exact P0 | rewrite POh, PO2; exact PO0] | rewrite SMh; exact SM2]].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split.
      + intros _. split; [lia|]. split; [lia|]. split; [exact TI'|]. split.
        * intros U1 U2. split; [exact TW'|]. lia.
        * intros U1. destruct (SL2 U1) as (A1 & A2 & A3 & A4). rewrite A1. split; [lia|]. split; [lia|]. split; [exact TI'|]. lia.
      + pose proof (dst_basics _ D2) as BB2. clear -BB2 ST2. lia.
  Qed.

  Lemma smid_run : forall s, dsr0 s ->
    mid_ok ws ILEN s /\ dsr0 (mid_post s)
    /\ 0 <= mid_hv s < 2 ^ 32 /\ 0 <= mid_hv s + ds_w_size s < 2 ^ 32 /\ 0 <= cs_avail_in (ds_strm s)
    /\ (cs_avail_out (ds_strm (mid_post s)) = cs_avail_out (ds_strm s)
        /\ cs_avail_in (ds_strm (mid_post s)) = cs_avail_in (ds_strm s) - mid_n s /\ 0 <= mid_n s <= cs_avail_in (ds_strm s)
        /\ (mid_n s = 0 -> cs_avail_in (ds_strm s) = 0 \/ ws < ds_strstart (mid_post s) - ds_block_start (mid_post s))).
  Proof.
    intros s DR. pose proof DR as [D P0 PO0]. pose proof (dst_basics s D) as BB. pose proof D as [C I CL Ews Ehs Epbl Sst Swr L0].
    destruct BB as (Wr & Pr & Epbs & Lpb & Lw & Wsz & LK & SN & Hbs & Hstr & Hins & Hhw & Hmt & Hbv & Hbb & Hp & Hpo & Hpop & Hai & Hni0 & Hin & Hil & Hao & Hout & Hoc & Hti & Had & Hwr).
    pose proof (di_cty _ _ _ _ I) as T. pose proof (ct_in _ T) as TI. pose proof (ct_win _ T) as TW.
    assert (TW' : forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window s) j < 256) by (intros j Hj; apply TW; rewrite Lw; exact Hj).
    assert (EHV : mid_hv s = 2 * ws - ds_strstart s) by (unfold mid_hv; rewrite Wsz; reflexivity).
    assert (S2 : let s2 := mid_s2 s in
                 dsr0 s2 /\ ds_strm s2 = ds_strm s /\ ds_w_size s2 = ws /\ ds_wrap s2 = ds_wrap s
                 /\ 0 <= ds_block_start s2 <= ds_strstart s2 /\ ds_strstart s2 + mid_hv2 s = 2 * ws /\ 0 <= ds_insert s2 <= ds_strstart s2).
    { cbv zeta. unfold mid_s2, mid_hv2. destruct (mid_c s) eqn:MC.
      - unfold mid_c in MC. apply Bool.andb_true_iff in MC as [_ MC]. apply Z.leb_le in MC.
        unfold slide2. cbv zeta. dsr. rewrite Ews.
        assert (WB : u8a (arr_blit (ds_window s) 0 (ds_window s) ws (ds_strstart s - ws))).
        { apply u8a_blit; [exact TW | intros _; rewrite Lw; lia | exact TW]. }
        match goal with |- dsr0 ?x /\ _ =>
          assert (Ex : exists m i, x = set_insert (set_matches (set_window (set_strstart (set_block_start s (ds_block_start s - ws)) (ds_strstart s - ws)) (arr_blit (ds_window s) 0 (ds_window s) ws (ds_strstart s - ws))) m) i
                         /\ 0 <= m <= 2 /\ 0 <= i <= ds_strstart s - ws /\ ds_insert s - ws <= i)
        end.
        { destruct (Z.ltb_spec (ds_matches s) 2); cbv iota; dsr; destruct (Z.ltb_spec (ds_strstart s - ws) (ds_insert s)); cbv iota; dsr;
            [ exists (ds_matches s + 1), (ds_strstart s - ws) | exists (ds_matches s + 1), (ds_insert s)
            | exists (ds_matches s), (ds_strstart s - ws) | exists (ds_matches s), (ds_insert s) ];
            (split; [destruct s; reflexivity|]); lia. }
        destruct Ex as (m & i & -> & Hm & Hi & _). dsr.
        split; [| repeat split; try reflexivity; lia].
        split; [| dsr; assumption ..].
        apply (dst_geo s _ D); dsr; try reflexivity; try lia.
        + constructor; reflexivity.
        + apply dcfg_set_insert, dcfg_set_matches. apply dcfg_set_window; [apply dcfg_set_strstart, dcfg_set_block_start; exact C | rewrite arr_len_blit; reflexivity].
        + apply cty_set_insert, cty_set_matches. apply cty_set_window; [apply cty_set_strstart, cty_set_block_start; exact T | exact WB].
      - split; [exact DR|]. repeat split; try reflexivity; lia. }
    cbv zeta in S2. destruct S2 as (DR2 & SM2 & WS2 & WR2 & BS2 & ST2 & IN2).
    pose proof DR2 as [D2 P2 PO2]. pose proof (dst_basics _ D2) as BB2.
    pose proof (mid_n_range s ltac:(lia) ltac:(rewrite SM2; lia)) as NR. rewrite SM2 in NR.
    assert (TI2 : forall j, 0 <= j < ILEN -> 0 <= arr_get (cs_input (ds_strm (mid_s2 s))) j < 256) by (intros j Hj; rewrite SM2; apply TI; rewrite (dc_ilen _ _ _ _ CL); exact Hj).
    split.
    { unfold mid_ok. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
      { intros MC. unfold mid_c in MC. apply Bool.andb_true_iff in MC as [_ MC]. apply Z.leb_le in MC. split; [lia|]. split; [exact TW'|]. lia. }
      split; [lia|]. split; [lia|]. intros Hn. rewrite SM2, WR2.
      split; [lia|]. split; [lia|]. split; [intros j Hj; apply TI; rewrite (dc_ilen _ _ _ _ CL); exact Hj|]. split; [lia|].
      split; [intros W; apply adler_ok_canon; exact (dc_ad1 _ _ _ _ CL W)|]. split; [lia|]. split; [lia|]. lia. }
    assert (DICH : mid_n s = 0 -> cs_avail_in (ds_strm s) = 0 \/ ws < ds_strstart (mid_s2 s) - ds_block_start (mid_s2 s)).
    { intros N0. pose proof NR as NR'.
      assert (ALT : cs_avail_in (ds_strm s) = 0 \/ mid_hv2 s = 0).
      { unfold mid_n in N0. rewrite SM2 in N0. destruct (Z.ltb_spec (cs_avail_in (ds_strm s)) (mid_hv2 s)); lia. }
      destruct ALT as [A0|H0]; [left; exact A0|].
      unfold mid_hv2 in H0. unfold mid_s2. destruct (mid_c s) eqn:MC; [exfalso; lia|].
      unfold mid_c in MC. rewrite EHV, Ews in MC.
      destruct (Z.ltb_spec (2 * ws - ds_strstart s) (cs_avail_in (ds_strm s))); cbn [andb] in MC.
      - apply Z.leb_gt in MC. right. lia.
      - left. lia. }
    lazymatch goal with |- ?D /\ _ /\ _ /\ _ /\ ?R => enough (H : D /\ R) by (destruct H as [H1 H2]; split; [exact H1|]; split; [lia|]; split; [lia|]; split; [lia | exact H2]) end.
    unfold mid_post. destruct (Z.eqb_spec (mid_n s) 0) as [N0|N0]; cbn [negb].
    { split; [exact DR2|]. rewrite SM2, N0. split; [reflexivity|]. split; [lia|]. split; [lia|]. intros _. exact (DICH N0). }
    clear DICH.
    generalize DR2 D2 P2 PO2 SM2 WS2 WR2 BS2 ST2 IN2 BB2 NR TI2. generalize (mid_s2 s). clear DR2 D2 P2 PO2 SM2 WS2 WR2 BS2 ST2 IN2 BB2 NR TI2.
    intros s2 DR2 D2 P2 PO2 SM2 WS2 WR2 BS2 ST2 IN2 BB2 NR TI2.
    destruct (rbw_shape s2 (mid_n s) ltac:(rewrite SM2; lia)) as (st' & E & F). cbv zeta in F. rewrite E.
    destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (di_cty _ _ _ _ (st_inv _ D2)) as T2.
    assert (CL2' : dcall ILEN OCAP tot0 (set_strm s2 st')).
    { apply (dcall_consume ILEN OCAP tot0 s2 (mid_n s) st' (st_call _ D2) T2 ltac:(rewrite SM2; lia)); assumption. }
    pose proof (dst_strm s2 st' D2 CL2' F7) as D2a.
    assert (BY : Forall (fun b => 0 <= b < 256) (arr_slice (cs_input (ds_strm s2)) (cs_next_in (ds_strm s2)) (mid_n s))).
    { apply u8a_slice; [exact (ct_in _ T2)|]. intros _. pose proof (st_call _ D2) as CL2. pose proof (dc_ni _ _ _ _ CL2). pose proof (dc_in _ _ _ _ CL2). rewrite (dc_ilen _ _ _ _ CL2).
      pose proof NR as NR2. rewrite <- SM2 in NR2. lia. }
    assert (HM : 0 <= MIN (mid_n s) (wrap32 (ds_w_size s2 - ds_insert s2)) <= mid_n s).
    { unfold MIN. pose proof (wrap32_range (ds_w_size s2 - ds_insert s2)). destruct (Z.ltb_spec (wrap32 (ds_w_size s2 - ds_insert s2)) (mid_n s)); lia. }
    split; [| dsr; rewrite F2, F5, SM2; split; [reflexivity|]; split; [reflexivity|]; split; [lia | intros X; exfalso; exact (N0 X)]].
    split; [| dsr; assumption ..].
    apply (dst_geo (set_strm s2 st') _ D2a); dsr; try reflexivity; try lia.
    - constructor; reflexivity.
    - apply dcfg_set_insert, dcfg_set_strstart. apply dcfg_set_window; [exact (st_cfg _ D2a) | rewrite arr_len_upd; reflexivity].
    - apply cty_set_insert, cty_set_strstart. apply cty_set_window; [exact (di_cty _ _ _ _ (st_inv _ D2a)) | apply u8a_upd; [exact (ct_win _ T2) | exact BY]].
  Qed.


  Definition SPOST (flush : Z) (s' : deflate_state) (bs : block_state) : Prop :=
    dst s' /\ (cs_avail_out (ds_strm s') <> 0 -> ds_pending s' = 0 /\ ds_pending_out s' = 0)
    /\ match bs with
       | need_more => True
       | block_done => dsr0 s' /\ flush <> Z_NO_FLUSH /\ flush <> Z_FINISH
       | finish_started => flush = Z_FINISH
       | finish_done => dsr0 s' /\ flush = Z_FINISH
       end.

  Lemma dsr0_SPOST : forall flush s, dsr0 s -> SPOST flush s need_more.
  Proof. intros flush s [D P0 PO0]. split; [exact D|]. split; [intros _; split; assumption | exact Logic.I]. Qed.

  Definition FINPROG (flush : Z) (s : deflate_state) (r : deflate_state * block_state) : Prop :=
    let '(s', bs) := r in
    cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s) /\ cs_avail_out (ds_strm s') <= cs_avail_out (ds_strm s)
    /\ ((0 < cs_avail_out (ds_strm s) -> cs_avail_out (ds_strm s') < cs_avail_out (ds_strm s))
        \/ (bs = need_more /\ ds_strstart s - ds_block_start s < ws
            /\ (cs_avail_in (ds_strm s) = 0 -> flush <> Z_NO_FLUSH -> ds_strstart s = ds_block_start s /\ flush <> Z_FINISH))).

  Lemma sfin_run : forall flush s, dsr0 s -> 0 <= flush <= 5 ->
    fin_ok ws PBL OCAP flush s
    /\ (let '(s', bs) := deflate_stored_fin s flush in SPOST flush s' bs)
    /\ FINPROG flush s (deflate_stored_fin s flush).
  Proof.
    intros flush s DR Hfl. pose proof DR as [D P0 PO0]. pose proof (dst_basics s D) as BB. pose proof D as [C I CL Ews Ehs Epbl Sst Swr L0].
    destruct BB as (Wr & Pr & Epbs & Lpb & Lw & Wsz & LK & SN & Hbs & Hstr & Hins & Hhw & Hmt & Hbv & Hbb & Hp & Hpo & Hpop & Hai & Hni0 & Hin & Hil & Hao & Hout & Hoc & Hti & Had & Hwr).
    assert (HWP : exists v, hwpost s = set_high_water s v /\ 0 <= v <= 2 * ws).
    { unfold hwpost. destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s)); [exists (ds_strstart s) | exists (ds_high_water s)]; (split; [destruct s; reflexivity | lia]). }
    destruct HWP as (hv & EH & Hhv).
    assert (D1 : dst (hwpost s)).
    { rewrite EH. apply (dst_geo s _ D); dsr; try reflexivity; try lia.
      - constructor; reflexivity.
      - apply dcfg_set_high_water. exact C.
      - apply cty_set_high_water. exact (di_cty _ _ _ _ I). }
    assert (DR1 : dsr0 (hwpost s)) by (split; [exact D1 | rewrite EH; dsr; assumption ..]).
    rewrite (ds_fin_eq flush s) by (rewrite EH; dsr; lia).
    unfold fin_ok. cbv zeta.
    assert (E1 : ds_strstart (hwpost s) = ds_strstart s /\ ds_block_start (hwpost s) = ds_block_start s /\ ds_bi_valid (hwpost s) = ds_bi_valid s
                 /\ ds_pending_buf_size (hwpost s) = PBL /\ cs_avail_in (ds_strm (hwpost s)) = cs_avail_in (ds_strm s)
                 /\ ds_window (hwpost s) = ds_window s /\ ds_bi_buf (hwpost s) = ds_bi_buf s /\ ds_pending (hwpost s) = 0
                 /\ ds_pending_out (hwpost s) = 0 /\ ds_strm (hwpost s) = ds_strm s).
    { rewrite EH. dsr. repeat split; try reflexivity; assumption. }
    generalize D1 DR1 E1. generalize (hwpost s). clear D1 DR1 EH. intros s1 D1 DR1 (Es & Eb & Ev & Epb & Eai & Ew & Ebb & Ep1 & Epo1 & Esm).
    pose proof (hdrb_range s1 ltac:(rewrite Ev; lia)) as HR.
    assert (TL : 0 <= tlen s1 <= tleft s1 /\ tlen s1 <= PBL - hdrb s1 /\ tleft s1 = ds_strstart s - ds_block_start s).
    { unfold tlen, thave, tleft, MIN, MAX_STORED. rewrite Es, Eb, Epb.
      destruct (Z.ltb_spec 65535 (PBL - hdrb s1)); [destruct (Z.ltb_spec 65535 (ds_strstart s - ds_block_start s)) | destruct (Z.ltb_spec (PBL - hdrb s1) (ds_strstart s - ds_block_start s))]; lia. }
    destruct TL as (TL1 & TL2 & ETL).
    assert (LR : tlast flush s1 = 0 \/ (tlast flush s1 = 1 /\ flush = Z_FINISH)).
    { unfold tlast. destruct (Z.eqb_spec flush Z_FINISH); cbn [andb]; [| left; reflexivity].
      destruct ((cs_avail_in (ds_strm s1) =? 0) && (tlen s1 =? tleft s1)); [right; split; [reflexivity | assumption] | left; reflexivity]. }
    pose proof (ct_win _ (di_cty _ _ _ _ (st_inv _ D1))) as TW. unfold u8a in TW. rewrite Ew, Lw in TW.
    pose proof (dst_basics s1 D1) as BB1.
    assert (EMIT : let len := tlen s1 in let last := tlast flush s1 in
                   let s2 := tr_stored_block s1 (Some (ds_block_start s1)) len last in
                   let s3 := set_block_start s2 (ds_block_start s2 + len) in
                   (BINV PBL s1 /\ ds_pending s2 <= PBL /\ ds_block_start s1 + len <= 2 * ws
                    /\ (forall j, ds_block_start s1 <= j < ds_block_start s1 + len -> 0 <= arr_get (ds_window s1) j < 256)
                    /\ 0 <= ds_block_start s2 < 2 ^ 31 /\ fp_ok PBL OCAP s3)
                   /\ SPOST flush (flush_pending s3) (if negb (last =? 0) then finish_started else need_more)
                   /\ (cs_avail_in (ds_strm (flush_pending s3)) = cs_avail_in (ds_strm s)
                       /\ cs_avail_out (ds_strm (flush_pending s3)) <= cs_avail_out (ds_strm s)
                       /\ (0 < cs_avail_out (ds_strm s) -> cs_avail_out (ds_strm (flush_pending s3)) < cs_avail_out (ds_strm s)))).
    { cbv zeta.
      assert (Hl : 0 <= tlast flush s1 <= 1) by (destruct LR as [-> | [-> _]]; lia).
      generalize (cty_tr_stored_block s1 (Some (ds_block_start s1)) (tlen s1) (tlast flush s1) (di_cty _ _ _ _ (st_inv _ D1))
                    ltac:(intros off Eo Hn; injection Eo as <-; rewrite Ew, Lw; lia))
                 (ep_tr_stored_block s1 (Some (ds_block_start s1)) (tlen s1) (tlast flush s1))
                 (tr_stored_block_bits s1 (Some (ds_block_start s1)) (tlen s1) (tlast flush s1) ltac:(split; [rewrite Ev; exact Hbv | rewrite Ebb; exact Hbb | rewrite Ep1; lia]) Hl (proj1 TL1)).
      generalize (tr_stored_block s1 (Some (ds_block_start s1)) (tlen s1) (tlast flush s1)). intros s2 T2 EP2 (B2 & V2 & Z2 & P2).
      unfold bvol in V2. rewrite Ep1, Ev in V2. rewrite Ep1 in P2. destruct B2 as [A2 Bq2 C2].
      assert (Hp2 : ds_pending s2 - tlen s1 <= hdrb s1) by (unfold hdrb; apply Z.div_le_lower_bound; lia).
      pose proof (ep_block_start _ _ EP2) as BS2. pose proof (ep_pending_out _ _ EP2) as PO2. rewrite Epo1 in PO2.
      pose proof (ep_strm _ _ EP2) as SM2. pose proof (ep_len_pending_buf _ _ EP2) as PL2. pose proof (ep_strstart _ _ EP2) as ST2.
      assert (D2 : dst s2) by (apply (dst_ep s1 s2 D1 EP2 T2); rewrite ?PO2; lia).
      assert (D3 : dst (set_block_start s2 (ds_block_start s2 + tlen s1))) by (apply dst_bs; [exact D2 | rewrite BS2, ST2; lia]).
      destruct (dst_fp (set_block_start s2 (ds_block_start s2 + tlen s1)) D3 ltac:(dsr; lia)) as (D4 & CL4 & FL4 & _).
      assert (FB3 : tr_flush_bits (set_block_start s2 (ds_block_start s2 + tlen s1)) = set_block_start s2 (ds_block_start s2 + tlen s1)).
      { unfold tr_flush_bits, bi_flush. dsr. rewrite Z2. reflexivity. }
      assert (TO : 0 <= cs_total_out (ds_strm s) < 2 ^ 64) by (rewrite (dc_to _ _ _ _ CL); apply wrap64_range).
      assert (OL : 0 <= zlength (cs_out_rev (ds_strm s))) by apply Zle_0_nat.
      pose proof (ct_pb _ T2) as TP. unfold u8a in TP. rewrite PL2 in TP.
      split.
      - unfold BINV. rewrite Ev, Ebb, Ep1. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros j Hj; rewrite Ew; apply TW; lia|]. split; [rewrite BS2; lia|].
        unfold fp_ok. rewrite FB3. cbv zeta. dsr. rewrite SM2, Esm, PO2, <- zlength_of_nat. unfold BINV. dsr. rewrite Z2.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact TO|].
        intros i0 Hi0. apply TP. pose proof (proj1 (proj2 (proj2 (proj2 BB1)))) as PL1. lia.
      - split.
        + split; [exact D4|]. split; [exact FL4|].
          destruct LR as [EL0 | [EL1 HF]]; rewrite ?EL0, ?EL1; cbn; [exact Logic.I | exact HF].
        + destruct (fp_acct (set_block_start s2 (ds_block_start s2 + tlen s1)) ltac:(dsr; exact Z2) ltac:(dsr; lia) ltac:(dsr; rewrite SM2, Esm; lia)) as (Q1 & Q2 & Q3).
          replace (ds_strm (set_block_start s2 (ds_block_start s2 + tlen s1))) with (ds_strm s) in Q1, Q2, Q3 by (dsr; rewrite SM2, Esm; reflexivity).
          replace (ds_pending (set_block_start s2 (ds_block_start s2 + tlen s1))) with (ds_pending s2) in Q3 by reflexivity.
          split; [exact Q1|]. split; [exact Q2|]. intros A. apply Q3; [lia | exact A]. }
    cbv zeta in EMIT. destruct EMIT as (EOK & EPOST & EPROG).
    split.
    - split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros _. exact EOK.
    - pose proof (st_ws _ D1) as WS1.
      assert (TH : 0 <= thave s1).
      { unfold thave, MIN, MAX_STORED. rewrite Epb. destruct (Z.ltb_spec 65535 (PBL - hdrb s1)); lia. }
      destruct (tcond1 s1 || tcond2 flush s1) eqn:TC.
      + split; [exact EPOST|]. unfold FINPROG. destruct EPROG as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|]. left. exact Q3.
      + split; [exact (dsr0_SPOST flush s1 DR1)|]. unfold FINPROG. rewrite Esm. split; [reflexivity|]. split; [lia|].
        right. split; [reflexivity|].
        apply Bool.orb_false_iff in TC as [TC1 TC2]. unfold tcond1, tmb, tleft, MIN in TC1. unfold tcond2, tleft in TC2.
        rewrite Es, Eb, WS1 in TC1. rewrite Es, Eb, Esm in TC2. apply Z.leb_gt in TC1.
        assert (LT : ds_strstart s - ds_block_start s < ws /\ ds_strstart s - ds_block_start s < thave s1).
        { destruct (Z.ltb_spec ws (thave s1)); lia. }
        split; [exact (proj1 LT)|].
        intros AI0 NF. rewrite AI0, Z.eqb_refl in TC2.
        replace (negb (flush =? Z_NO_FLUSH)) with true in TC2 by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NF).
        replace (ds_strstart s - ds_block_start s <=? thave s1) with true in TC2 by (symmetry; apply Z.leb_le; lia).
        rewrite !Bool.andb_true_r in TC2. apply Bool.orb_false_iff in TC2 as [TA TB].
        apply Bool.negb_false_iff in TA. apply Z.eqb_eq in TA. apply Z.eqb_neq in TB. split; [lia | exact TB].
  Qed.

  Definition SPROG (flush : Z) (s s' : deflate_state) (bs : block_state) : Prop :=
    cs_avail_out (ds_strm s') <= cs_avail_out (ds_strm s) /\ cs_avail_in (ds_strm s') <= cs_avail_in (ds_strm s)
    /\ ((bs = need_more \/ bs = finish_started) -> 0 < cs_avail_out (ds_strm s) -> (flush = Z_NO_FLUSH -> 0 < cs_avail_in (ds_strm s)) ->
        cs_avail_out (ds_strm s') < cs_avail_out (ds_strm s) \/ cs_avail_in (ds_strm s') < cs_avail_in (ds_strm s)).

  Theorem stored_run : forall flush s, dsr0 s -> 0 <= flush <= 5 ->
    stored_ok ws PBL ILEN OCAP s flush
    /\ (let '(s', bs) := deflate_stored s flush in SPOST flush s' bs)
    /\ (let '(s', bs) := deflate_stored s flush in SPROG flush s s' bs).
  Proof.
    intros flush s DR Hfl. pose proof DR as [D P0 PO0]. pose proof (dst_basics s D) as BB. pose proof D as [C I CL Ews Ehs Epbl Sst Swr L0].
    destruct BB as (Wr & Pr & Epbs & Lpb & Lw & Wsz & LK & SN & Hbs & Hstr & Hins & Hhw & Hmt & Hbv & Hbb & Hp & Hpo & Hpop & Hai & Hni0 & Hin & Hil & Hao & Hout & Hoc & Hti & Had & Hwr).
    assert (OL : 0 <= zlength (cs_out_rev (ds_strm s))) by apply Zle_0_nat.
    unfold stored_ok, deflate_stored. cbv zeta. rewrite Ews.
    set (mb := MIN (ds_pending_buf_size s - 5) ws).
    assert (Hmb : 0 <= mb < 2 ^ 32) by (subst mb; unfold MIN; rewrite Epbs; destruct (Z.ltb_spec ws (PBL - 5)); lia).
    rewrite (wrap32_id mb) by exact Hmb.
    set (fuel := Z.to_nat (cs_avail_out (ds_strm s) + 1)).
    assert (HF : cs_avail_out (ds_strm s) < Z.of_nat fuel) by (subst fuel; rewrite Z2Nat.id; lia).
    assert (LOOP : (flush <> Z_FINISH -> loopA_ok ws PBL ILEN OCAP flush mb fuel s) /\ (flush = Z_FINISH -> loopB_ok ws PBL ILEN OCAP mb fuel s)
                   /\ let '(s1, last) := deflate_stored_loop fuel s flush mb in
                      dsr0 s1 /\ (last = 0 \/ (last = 1 /\ flush = Z_FINISH)) /\ cs_avail_in (ds_strm s1) <= cs_avail_in (ds_strm s)
                      /\ cs_avail_out (ds_strm s1) <= cs_avail_out (ds_strm s)
                      /\ (ds_strm s1 = ds_strm s \/ cs_avail_out (ds_strm s1) < cs_avail_out (ds_strm s))).
    { destruct (Z.eq_dec flush Z_FINISH) as [HF4|HF4].
      - destruct (sloopB_run mb fuel s DR HF) as [LOK LP]. rewrite HF4.
        split; [intros X; exfalso; exact (X eq_refl)|]. split; [intros _; exact LOK|].
        destruct (deflate_stored_loop fuel s Z_FINISH mb) as [s1 last]. destruct LP as (X1 & X2 & X3 & X4 & X5).
        split; [exact X1|]. split; [destruct X2; [left; assumption | right; split; [assumption | reflexivity]]|].
        split; [exact X3|]. split; [exact X4 | exact X5].
      - destruct (sloopA_run flush mb fuel s DR HF4 HF) as [LOK LP].
        split; [intros _; exact LOK|]. split; [intros X; exfalso; exact (HF4 X)|].
        destruct (deflate_stored_loop fuel s flush mb) as [s1 last]. destruct LP as (X1 & X2 & X3 & X4 & X5).
        split; [exact X1|]. split; [left; exact X2|]. split; [exact X3|]. split; [exact X4 | exact X5]. }
    destruct LOOP as (LA & LB & LP).
    destruct (deflate_stored_loop fuel s flush mb) as [s1 last]. cbn [fst snd]. destruct LP as (DR1 & HL & AI1 & AO1 & ALT1).
    pose proof (st_call _ (sr_dst _ DR1)) as CL1. pose proof (dc_in _ _ _ _ CL1) as IN1. pose proof (dc_ni _ _ _ _ CL1) as NI1.
    destruct (sused_run (cs_avail_in (ds_strm s)) s1 DR1 ltac:(lia) AI1 ltac:(lia)) as (UOK & DR3 & SM3).
    rewrite (ds_used_eq s1 (cs_avail_in (ds_strm s))).
    generalize UOK DR3 SM3. generalize (used_post (cs_avail_in (ds_strm s)) s1). clear UOK DR3 SM3. intros s3 UOK DR3 SM3.
    destruct (smid_run s3 DR3) as (MOK & DR4 & HV1 & HV2 & AI3 & MAO & MAI & MNR & MDICH).
    assert (MID0 : cs_avail_in (ds_strm s3) = 0 -> mid_post s3 = s3).
    { intros A0. pose proof (dst_basics _ (sr_dst _ DR3)) as BB3.
      unfold mid_post, mid_n, mid_hv2, mid_s2.
      replace (mid_c s3) with false by (unfold mid_c; rewrite A0; unfold mid_hv; destruct (Z.ltb_spec (ds_window_size s3 - ds_strstart s3) 0); [lia | reflexivity]).
      rewrite A0. unfold mid_hv. destruct (Z.ltb_spec 0 (ds_window_size s3 - ds_strstart s3)) as [X|X]; cbn [Z.eqb negb]; [reflexivity|].
      replace (ds_window_size s3 - ds_strstart s3) with 0 by lia. reflexivity. }
    split.
    - split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact LA|]. split; [exact LB|]. split; [exact UOK|]. split; [exact MOK|].
      intros Hlast Hc. exact (proj1 (sfin_run flush (mid_post s3) DR4 Hfl)).
    - destruct (Z.eqb_spec last 0) as [Z0|Z0]; cbn [negb].
      + match goal with |- context [if ?c then (s3, block_done) else _] => destruct c eqn:EC end.
        * split.
          -- split; [exact (sr_dst _ DR3)|]. split; [intros _; split; [exact (sr_pend _ DR3) | exact (sr_pout _ DR3)]|].
             split; [exact DR3|].
             apply Bool.andb_true_iff in EC as [EC _]. apply Bool.andb_true_iff in EC as [EC _]. apply Bool.andb_true_iff in EC as [E1 E2].
             apply Bool.negb_true_iff in E1. apply Bool.negb_true_iff in E2. apply Z.eqb_neq in E1. apply Z.eqb_neq in E2. split; assumption.
          -- unfold SPROG. rewrite SM3. split; [exact AO1|]. split; [exact AI1|]. intros [X|X]; discriminate X.
        * rewrite (mid_eq flush s3 HV1 HV2 AI3).
          pose proof (sfin_run flush (mid_post s3) DR4 Hfl) as (_ & FP & FG). split; [exact FP|].
          unfold FINPROG in FG. destruct (deflate_stored_fin (mid_post s3) flush) as [s' bs]. destruct FG as (G1 & G2 & G3).
          rewrite MAI, SM3 in G1. rewrite MAO, SM3 in G2. rewrite SM3 in MNR.
          unfold SPROG. rewrite G1. split; [lia|]. split; [lia|].
          intros Hnm Ha0 Hi0.
          destruct G3 as [STRICT | (Ebs & LTW & ZC)].
          -- left. rewrite MAO, SM3 in STRICT. destruct ALT1 as [E|LT]; [rewrite E in *; apply STRICT; exact Ha0 | lia].
          -- destruct (Z.eq_dec (mid_n s3) 0) as [N0|N0]; [| right; lia].
             destruct (MDICH N0) as [A0|BIG]; [| exfalso; lia].
             destruct ALT1 as [E|LT]; [| left; lia].
             rewrite SM3, E in A0.
             assert (NF : flush <> Z_NO_FLUSH) by (intros F0; pose proof (Hi0 F0); lia).
             rewrite MAI, SM3, E, A0, N0 in ZC. destruct (ZC ltac:(reflexivity) NF) as [SB NFF].
             rewrite (MID0 ltac:(rewrite SM3, E; exact A0)) in SB.
             exfalso. unfold Z_NO_FLUSH, Z_FINISH in *.
             replace (negb (flush =? 0)) with true in EC by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NF).
             replace (negb (flush =? 4)) with true in EC by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NFF).
             rewrite SM3, E, A0, SB, !Z.eqb_refl in EC. discriminate EC.
      + split.
        * split; [exact (sr_dst _ DR3)|]. split; [intros _; split; [exact (sr_pend _ DR3) | exact (sr_pout _ DR3)]|].
          split; [exact DR3|]. destruct HL as [HL|[_ HL]]; [exfalso; exact (Z0 HL) | exact HL].
        * unfold SPROG. rewrite SM3. split; [exact AO1|]. split; [exact AI1|]. intros [X|X]; discriminate X.
  Qed.
End STORED.
