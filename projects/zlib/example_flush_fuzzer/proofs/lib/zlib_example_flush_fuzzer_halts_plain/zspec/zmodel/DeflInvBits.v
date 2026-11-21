(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateInvKeep OverlayFBS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import DeflateInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition bvol (s : deflate_state) : Z := 8 * ds_pending s + ds_bi_valid s.
Record bits_ok (s : deflate_state) : Prop := MkBITS {
  bo_bv : 0 <= ds_bi_valid s <= 16;
  bo_bb : 0 <= ds_bi_buf s < 2 ^ 16;
  bo_pd : 0 <= ds_pending s }.
Lemma wrap16_range : forall z, 0 <= wrap16 z < 2 ^ 16.
Proof. intros z. rewrite wrap16_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma put_byte_bits : forall s c, bits_ok s ->
  bits_ok (put_byte s c) /\ bvol (put_byte s c) = bvol s + 8 /\ ds_pending (put_byte s c) = ds_pending s + 1
  /\ ds_bi_valid (put_byte s c) = ds_bi_valid s /\ ds_bi_buf (put_byte s c) = ds_bi_buf s.
Proof. intros s c [A B C]. unfold bvol, put_byte. repeat split; dsr; lia. Qed.
Lemma put_short_bits : forall s w, bits_ok s ->
  bits_ok (put_short s w) /\ bvol (put_short s w) = bvol s + 16 /\ ds_pending (put_short s w) = ds_pending s + 2
  /\ ds_bi_valid (put_short s w) = ds_bi_valid s /\ ds_bi_buf (put_short s w) = ds_bi_buf s.
Proof.
  intros s w H. unfold put_short.
  destruct (put_byte_bits s (Z.land w 255) H) as (H1 & V1 & P1 & B1 & BB1).
  destruct (put_byte_bits _ (Z.shiftr (wrap16 w) 8) H1) as (H2 & V2 & P2 & B2 & BB2).
  split; [exact H2|]. rewrite V2, V1, P2, P1, B2, B1, BB2, BB1. lia.
Qed.
Lemma send_bits_bits : forall s v l, bits_ok s -> 1 <= l <= 16 ->
  bits_ok (send_bits s v l) /\ bvol (send_bits s v l) = bvol s + l
  /\ ds_pending s <= ds_pending (send_bits s v l) <= ds_pending s + 2.
Proof.
  intros s v l [A B C] Hl. unfold send_bits, Buf_size.
  destruct (Z.ltb_spec (16 - l) (ds_bi_valid s)) as [X|X].
  - set (s1 := set_bi_buf s _).
    assert (E1 : ds_bi_valid s1 = ds_bi_valid s /\ ds_pending s1 = ds_pending s) by (subst s1; dsr; split; reflexivity).
    destruct (put_short_bits s1 (ds_bi_buf s1) ltac:(subst s1; split; dsr; [exact A | apply wrap16_range | exact C])) as (H2 & V2 & P2 & B2 & BB2).
    destruct E1 as [E1 E1']. destruct H2 as [A2 B2' C2]. unfold bvol in *. pose proof (wrap16_range v) as W.
    assert (R : 0 <= Z.shiftr (wrap16 v) (16 - ds_bi_valid s) < 2 ^ 16).
    { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (16 - ds_bi_valid s) ltac:(lia) ltac:(lia)).
      split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
    repeat split; dsr; rewrite ?B2, ?BB2, ?P2, ?E1, ?E1'; try lia.
  - unfold bvol. pose proof (wrap16_range (Z.lor (ds_bi_buf s) (Z.shiftl (wrap16 v) (ds_bi_valid s)))).
    repeat split; dsr; try lia.
Qed.
Lemma bi_flush_bits : forall s, bits_ok s ->
  bits_ok (bi_flush s) /\ bvol (bi_flush s) = bvol s /\ 0 <= ds_bi_valid (bi_flush s) <= 7
  /\ ds_pending s <= ds_pending (bi_flush s) <= ds_pending s + 2.
Proof.
  intros s [A B C]. unfold bi_flush.
  destruct (Z.eqb_spec (ds_bi_valid s) 16) as [X|X].
  - destruct (put_short_bits s (ds_bi_buf s) ltac:(split; assumption)) as (H2 & V2 & P2 & B2 & BB2).
    unfold bvol in *. destruct H2 as [A2 B2' C2]. repeat split; dsr; rewrite ?BB2; try lia.
  - destruct (Z.leb_spec 8 (ds_bi_valid s)) as [Y|Y].
    + destruct (put_byte_bits s (ds_bi_buf s) ltac:(split; assumption)) as (H2 & V2 & P2 & B2 & BB2).
      unfold bvol in *. destruct H2 as [A2 B2' C2].
      assert (R : 0 <= Z.shiftr (ds_bi_buf s) 8 < 2 ^ 16).
      { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
      repeat split; dsr; rewrite ?BB2; try lia.
    + unfold bvol. repeat split; try assumption; lia.
Qed.
Lemma bi_windup_bits : forall s, bits_ok s ->
  bits_ok (bi_windup s) /\ bvol s <= bvol (bi_windup s) <= bvol s + 7 /\ ds_bi_valid (bi_windup s) = 0
  /\ ds_pending s <= ds_pending (bi_windup s) <= ds_pending s + 2.
Proof.
  intros s [A B C]. unfold bi_windup.
  destruct (Z.ltb_spec 8 (ds_bi_valid s)) as [X|X].
  - destruct (put_short_bits s (ds_bi_buf s) ltac:(split; assumption)) as (H2 & V2 & P2 & B2 & BB2).
    unfold bvol in *. destruct H2 as [A2 B2' C2]. repeat split; dsr; rewrite ?BB2; try lia.
  - destruct (Z.ltb_spec 0 (ds_bi_valid s)) as [Y|Y].
    + destruct (put_byte_bits s (ds_bi_buf s) ltac:(split; assumption)) as (H2 & V2 & P2 & B2 & BB2).
      unfold bvol in *. destruct H2 as [A2 B2' C2]. repeat split; dsr; rewrite ?BB2; try lia.
    + unfold bvol in *. repeat split; dsr; try lia.
Qed.
Lemma tr_align_bits : forall s, bits_ok s ->
  bits_ok (tr_align s) /\ bvol (tr_align s) = bvol s + 10 /\ 0 <= ds_bi_valid (tr_align s) <= 7
  /\ ds_pending s <= ds_pending (tr_align s) <= ds_pending s + 6.
Proof.
  intros s H. unfold tr_align, send_code.
  destruct (send_bits_bits s (Z.shiftl STATIC_TREES 1) 3 H ltac:(lia)) as (H1 & V1 & P1).
  change (arr_get static_ltree_dl END_BLOCK) with 7.
  destruct (send_bits_bits _ (arr_get static_ltree_fc END_BLOCK) 7 H1 ltac:(lia)) as (H2 & V2 & P2).
  destruct (bi_flush_bits _ H2) as (H3 & V3 & B3 & P3).
  split; [exact H3|]. rewrite V3, V2, V1. split; [lia|]. split; [exact B3|]. lia.
Qed.
Lemma tr_stored_block_bits : forall s buf len last, bits_ok s -> 0 <= last <= 1 -> 0 <= len ->
  bits_ok (tr_stored_block s buf len last)
  /\ bvol s + 35 + 8 * len <= bvol (tr_stored_block s buf len last) <= bvol s + 42 + 8 * len
  /\ ds_bi_valid (tr_stored_block s buf len last) = 0
  /\ ds_pending s + 4 + len <= ds_pending (tr_stored_block s buf len last) <= ds_pending s + 7 + len.
Proof.
  intros s buf len last H Hl Hlen. unfold tr_stored_block.
  destruct (send_bits_bits s (Z.shiftl STORED_BLOCK 1 + last) 3 H ltac:(lia)) as (H1 & V1 & P1).
  remember (send_bits s (Z.shiftl STORED_BLOCK 1 + last) 3) as s1 eqn:E1; clear E1.
  destruct (bi_windup_bits _ H1) as (H2 & V2 & B2 & P2). remember (bi_windup s1) as s2 eqn:E2; clear E2.
  destruct (put_short_bits _ (wrap16 len) H2) as (H3 & V3 & P3 & B3 & BB3). remember (put_short s2 (wrap16 len)) as s3 eqn:E3; clear E3.
  destruct (put_short_bits _ (wrap16 (Z.lnot len)) H3) as (H4 & V4 & P4 & B4 & BB4). remember (put_short s3 (wrap16 (Z.lnot len))) as s4 eqn:E4; clear E4.
  set (s5 := if negb (len =? 0) then _ else _).
  assert (E5 : ds_pending s5 = ds_pending s4 /\ ds_bi_valid s5 = ds_bi_valid s4 /\ ds_bi_buf s5 = ds_bi_buf s4).
  { subst s5. destruct (negb (len =? 0)); [destruct buf|]; dsf; repeat split; reflexivity. }
  remember s5 as s6 eqn:E6; clear E6. subst s5.
  destruct E5 as (E5a & E5b & E5c). destruct H4 as [A4 B4' C4].
  pose proof (bo_bv _ H). unfold bvol in *. repeat split; dsf; rewrite ?E5a, ?E5b, ?E5c; lia.
Qed.



Definition fpm_len (s1 : deflate_state) : Z :=
  if cs_avail_out (ds_strm s1) <? ds_pending s1 then cs_avail_out (ds_strm s1) else ds_pending s1.
Definition fpm_post (s1 : deflate_state) (len : Z) : deflate_state :=
  let st := ds_strm s1 in
  let st0 := cs_emit st (arr_slice (ds_pending_buf s1) (ds_pending_out s1) len) in
  let s2 := set_pending_out s1 (ds_pending_out s1 + len) in
  let st1 := cset_total_out st0 (wrap64 (cs_total_out st0 + len)) in
  let st2 := cset_avail_out st1 (cs_avail_out st1 - len) in
  let s3 := set_strm s2 st2 in
  let s4 := set_pending s3 (ds_pending s3 - len) in
  if ds_pending s4 =? 0 then set_pending_out s4 0 else s4.

Lemma flush_pending_eqm : forall s, 0 <= ds_pending (tr_flush_bits s) < 2 ^ 32 ->
  flush_pending s = (let s1 := tr_flush_bits s in let len := fpm_len s1 in if len =? 0 then s1 else fpm_post s1 len).
Proof.
  intros s Hp. unfold flush_pending, fpm_len, fpm_post. cbv zeta.
  rewrite (wrap32_id (ds_pending (tr_flush_bits s))) by exact Hp. reflexivity.
Qed.

Lemma fpm_post_fields : forall s1 len,
  let s' := fpm_post s1 len in let st := ds_strm s1 in let st' := ds_strm s' in
  ds_pending s' = ds_pending s1 - len
  /\ ds_pending_out s' = (if ds_pending s1 - len =? 0 then 0 else ds_pending_out s1 + len)
  /\ cs_out_rev st' = List.rev_append (arr_slice (ds_pending_buf s1) (ds_pending_out s1) len) (cs_out_rev st)
  /\ cs_avail_out st' = cs_avail_out st - len
  /\ cs_total_out st' = wrap64 (cs_total_out st + len)
  /\ cs_next_in st' = cs_next_in st /\ cs_avail_in st' = cs_avail_in st /\ cs_total_in st' = cs_total_in st
  /\ cs_input st' = cs_input st /\ cs_adler st' = cs_adler st /\ cs_data_type st' = cs_data_type st /\ cs_msg st' = cs_msg st
  /\ eproj (set_pending_out (set_strm s' (ds_strm s1)) (ds_pending_out s1)) = eproj s1
  /\ ds_bi_valid s' = ds_bi_valid s1 /\ ds_bi_buf s' = ds_bi_buf s1 /\ ds_pending_buf s' = ds_pending_buf s1 /\ ds_wrap s' = ds_wrap s1.
Proof.
  intros s1 len. cbv zeta. unfold fpm_post.
  destruct s1; destruct ds_strm; dsr.
  destruct (ds_pending - len =? 0); repeat split; reflexivity.
Qed.

Lemma rev_append_length : forall {A} (l acc : list A), length (List.rev_append l acc) = (length l + length acc)%nat.
Proof. intros A l. induction l as [|x l IH]; intros acc; cbn; [reflexivity|]. rewrite IH. cbn. lia. Qed.
Lemma zlength_rev_append : forall {A} (l acc : list A), zlength (List.rev_append l acc) = zlength l + zlength acc.
Proof. intros. unfold zlength. rewrite rev_append_length. lia. Qed.
Lemma Forall_rev_append : forall {A} (P : A -> Prop) l acc, Forall P l -> Forall P acc -> Forall P (List.rev_append l acc).
Proof. intros A P l. induction l as [|x l IH]; intros acc Hl Ha; cbn; [exact Ha|]. inversion Hl; subst. apply IH; [assumption|]. constructor; assumption. Qed.
Lemma wrap64_add_l : forall a b, wrap64 (wrap64 a + b) = wrap64 (a + b).
Proof. intros a b. rewrite !wrap64_mod. rewrite Z.add_mod_idemp_l by lia. reflexivity. Qed.

Definition kspo (q : deflate_state * list Z) (st : cstrm) (po : Z) : deflate_state * list Z :=
  (set_pending_out (set_strm (fst q) st) po, snd q).
Lemma kproj_spo : forall x st po, kproj (set_pending_out (set_strm x st) po) = kspo (kproj x) st po.
Proof. intros x st po. destruct x. unfold kproj, kspo, kzap, klens. lazy -[arr_len]. reflexivity. Qed.
Lemma kspo_kspo : forall q st po st' po', kspo (kspo q st po) st' po' = kspo q st' po'.
Proof. intros [d l] st po st' po'. destruct d. unfold kspo. lazy -[arr_len]. reflexivity. Qed.
Lemma kspo_self : forall x, kspo (kproj x) (ds_strm x) (ds_pending_out x) = kproj x.
Proof. intros x. destruct x. unfold kproj, kspo, kzap, klens. lazy -[arr_len]. reflexivity. Qed.

Lemma kp_spo_fields : forall a b st po, kproj a = kproj (set_pending_out (set_strm b st) po) ->
  ds_status a = ds_status b /\ ds_pending_buf_size a = ds_pending_buf_size b /\ ds_wrap a = ds_wrap b /\ ds_gzhead a = ds_gzhead b /\ ds_gzindex a = ds_gzindex b /\ ds_method a = ds_method b /\ ds_last_flush a = ds_last_flush b /\ ds_w_size a = ds_w_size b /\ ds_w_bits a = ds_w_bits b /\ ds_w_mask a = ds_w_mask b /\ ds_window a = ds_window b /\ ds_window_size a = ds_window_size b /\ ds_prev a = ds_prev b /\ ds_head a = ds_head b /\ ds_ins_h a = ds_ins_h b /\ ds_hash_size a = ds_hash_size b /\ ds_hash_bits a = ds_hash_bits b /\ ds_hash_mask a = ds_hash_mask b /\ ds_hash_shift a = ds_hash_shift b /\ ds_block_start a = ds_block_start b /\ ds_match_length a = ds_match_length b /\ ds_prev_match a = ds_prev_match b /\ ds_match_available a = ds_match_available b /\ ds_strstart a = ds_strstart b /\ ds_match_start a = ds_match_start b /\ ds_lookahead a = ds_lookahead b /\ ds_prev_length a = ds_prev_length b /\ ds_max_chain_length a = ds_max_chain_length b /\ ds_max_lazy_match a = ds_max_lazy_match b /\ ds_level a = ds_level b /\ ds_strategy a = ds_strategy b /\ ds_good_match a = ds_good_match b /\ ds_nice_match a = ds_nice_match b /\ ds_lit_bufsize a = ds_lit_bufsize b /\ ds_sym_next a = ds_sym_next b /\ ds_sym_end a = ds_sym_end b /\ ds_matches a = ds_matches b /\ ds_insert a = ds_insert b /\ ds_high_water a = ds_high_water b /\ ds_self_blk a = ds_self_blk b /\ ds_window_blk a = ds_window_blk b /\ ds_prev_blk a = ds_prev_blk b /\ ds_head_blk a = ds_head_blk b /\ ds_pending_buf_blk a = ds_pending_buf_blk b /\ arr_len (ds_pending_buf a) = arr_len (ds_pending_buf b).
Proof.
  intros a b st po K.
  pose proof (kp_status _ _ K) as E1. rewrite status_set_pending_out, status_set_strm in E1.
  pose proof (kp_pending_buf_size _ _ K) as E2. rewrite pending_buf_size_set_pending_out, pending_buf_size_set_strm in E2.
  pose proof (kp_wrap _ _ K) as E3. rewrite wrap_set_pending_out, wrap_set_strm in E3.
  pose proof (kp_gzhead _ _ K) as E4. rewrite gzhead_set_pending_out, gzhead_set_strm in E4.
  pose proof (kp_gzindex _ _ K) as E5. rewrite gzindex_set_pending_out, gzindex_set_strm in E5.
  pose proof (kp_method _ _ K) as E6. rewrite method_set_pending_out, method_set_strm in E6.
  pose proof (kp_last_flush _ _ K) as E7. rewrite last_flush_set_pending_out, last_flush_set_strm in E7.
  pose proof (kp_w_size _ _ K) as E8. rewrite w_size_set_pending_out, w_size_set_strm in E8.
  pose proof (kp_w_bits _ _ K) as E9. rewrite w_bits_set_pending_out, w_bits_set_strm in E9.
  pose proof (kp_w_mask _ _ K) as E10. rewrite w_mask_set_pending_out, w_mask_set_strm in E10.
  pose proof (kp_window _ _ K) as E11. rewrite window_set_pending_out, window_set_strm in E11.
  pose proof (kp_window_size _ _ K) as E12. rewrite window_size_set_pending_out, window_size_set_strm in E12.
  pose proof (kp_prev _ _ K) as E13. rewrite prev_set_pending_out, prev_set_strm in E13.
  pose proof (kp_head _ _ K) as E14. rewrite head_set_pending_out, head_set_strm in E14.
  pose proof (kp_ins_h _ _ K) as E15. rewrite ins_h_set_pending_out, ins_h_set_strm in E15.
  pose proof (kp_hash_size _ _ K) as E16. rewrite hash_size_set_pending_out, hash_size_set_strm in E16.
  pose proof (kp_hash_bits _ _ K) as E17. rewrite hash_bits_set_pending_out, hash_bits_set_strm in E17.
  pose proof (kp_hash_mask _ _ K) as E18. rewrite hash_mask_set_pending_out, hash_mask_set_strm in E18.
  pose proof (kp_hash_shift _ _ K) as E19. rewrite hash_shift_set_pending_out, hash_shift_set_strm in E19.
  pose proof (kp_block_start _ _ K) as E20. rewrite block_start_set_pending_out, block_start_set_strm in E20.
  pose proof (kp_match_length _ _ K) as E21. rewrite match_length_set_pending_out, match_length_set_strm in E21.
  pose proof (kp_prev_match _ _ K) as E22. rewrite prev_match_set_pending_out, prev_match_set_strm in E22.
  pose proof (kp_match_available _ _ K) as E23. rewrite match_available_set_pending_out, match_available_set_strm in E23.
  pose proof (kp_strstart _ _ K) as E24. rewrite strstart_set_pending_out, strstart_set_strm in E24.
  pose proof (kp_match_start _ _ K) as E25. rewrite match_start_set_pending_out, match_start_set_strm in E25.
  pose proof (kp_lookahead _ _ K) as E26. rewrite lookahead_set_pending_out, lookahead_set_strm in E26.
  pose proof (kp_prev_length _ _ K) as E27. rewrite prev_length_set_pending_out, prev_length_set_strm in E27.
  pose proof (kp_max_chain_length _ _ K) as E28. rewrite max_chain_length_set_pending_out, max_chain_length_set_strm in E28.
  pose proof (kp_max_lazy_match _ _ K) as E29. rewrite max_lazy_match_set_pending_out, max_lazy_match_set_strm in E29.
  pose proof (kp_level _ _ K) as E30. rewrite level_set_pending_out, level_set_strm in E30.
  pose proof (kp_strategy _ _ K) as E31. rewrite strategy_set_pending_out, strategy_set_strm in E31.
  pose proof (kp_good_match _ _ K) as E32. rewrite good_match_set_pending_out, good_match_set_strm in E32.
  pose proof (kp_nice_match _ _ K) as E33. rewrite nice_match_set_pending_out, nice_match_set_strm in E33.
  pose proof (kp_lit_bufsize _ _ K) as E34. rewrite lit_bufsize_set_pending_out, lit_bufsize_set_strm in E34.
  pose proof (kp_sym_next _ _ K) as E35. rewrite sym_next_set_pending_out, sym_next_set_strm in E35.
  pose proof (kp_sym_end _ _ K) as E36. rewrite sym_end_set_pending_out, sym_end_set_strm in E36.
  pose proof (kp_matches _ _ K) as E37. rewrite matches_set_pending_out, matches_set_strm in E37.
  pose proof (kp_insert _ _ K) as E38. rewrite insert_set_pending_out, insert_set_strm in E38.
  pose proof (kp_high_water _ _ K) as E39. rewrite high_water_set_pending_out, high_water_set_strm in E39.
  pose proof (kp_self_blk _ _ K) as E40. rewrite self_blk_set_pending_out, self_blk_set_strm in E40.
  pose proof (kp_window_blk _ _ K) as E41. rewrite window_blk_set_pending_out, window_blk_set_strm in E41.
  pose proof (kp_prev_blk _ _ K) as E42. rewrite prev_blk_set_pending_out, prev_blk_set_strm in E42.
  pose proof (kp_head_blk _ _ K) as E43. rewrite head_blk_set_pending_out, head_blk_set_strm in E43.
  pose proof (kp_pending_buf_blk _ _ K) as E44. rewrite pending_buf_blk_set_pending_out, pending_buf_blk_set_strm in E44.
  pose proof (kp_len_pending_buf _ _ K) as EL. rewrite pending_buf_set_pending_out, pending_buf_set_strm in EL.
  repeat split; assumption.
Qed.

Lemma cty_ep_spo : forall a b st po,
  eproj (set_pending_out (set_strm a st) po) = eproj b -> cs_input (ds_strm a) = cs_input (ds_strm b) ->
  ds_pending_buf a = ds_pending_buf b -> cty b -> cty a.
Proof.
  intros a b st po H Hi Hp HT.
  pose proof (ep_dyn_ltree_fc _ _ H) as Q1. rewrite dyn_ltree_fc_set_pending_out, dyn_ltree_fc_set_strm in Q1.
  pose proof (ep_dyn_ltree_dl _ _ H) as Q2. rewrite dyn_ltree_dl_set_pending_out, dyn_ltree_dl_set_strm in Q2.
  pose proof (ep_dyn_dtree_fc _ _ H) as Q3. rewrite dyn_dtree_fc_set_pending_out, dyn_dtree_fc_set_strm in Q3.
  pose proof (ep_dyn_dtree_dl _ _ H) as Q4. rewrite dyn_dtree_dl_set_pending_out, dyn_dtree_dl_set_strm in Q4.
  pose proof (ep_bl_tree_fc _ _ H) as Q5. rewrite bl_tree_fc_set_pending_out, bl_tree_fc_set_strm in Q5.
  pose proof (ep_bl_tree_dl _ _ H) as Q6. rewrite bl_tree_dl_set_pending_out, bl_tree_dl_set_strm in Q6.
  pose proof (ep_bl_count _ _ H) as Q7. rewrite bl_count_set_pending_out, bl_count_set_strm in Q7.
  pose proof (ep_depth _ _ H) as Q8. rewrite depth_set_pending_out, depth_set_strm in Q8.
  pose proof (ep_window _ _ H) as Q9. rewrite window_set_pending_out, window_set_strm in Q9.
  pose proof (ep_prev _ _ H) as Q10. rewrite prev_set_pending_out, prev_set_strm in Q10.
  pose proof (ep_head _ _ H) as Q11. rewrite head_set_pending_out, head_set_strm in Q11.
  exact (cty_K b a HT Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Hp Q9 Q10 Q11 Hi).
Qed.

Record fp_inv (PBL : Z) (s : deflate_state) : Prop := MkFPINV {
  fi_bits : bits_ok s;
  fi_po : 0 <= ds_pending_out s;
  fi_room : 8 * ds_pending_out s + bvol s <= 8 * PBL;
  fi_pbl : arr_len (ds_pending_buf s) = PBL;
  fi_po0 : ds_pending s = 0 -> ds_pending_out s = 0;
  fi_small : PBL <= 2 ^ 20 }.

Lemma flush_pending_inv : forall ILEN OCAP tot0 PBL s,
  fp_inv PBL s -> dcall ILEN OCAP tot0 s -> cty s ->
  let s' := flush_pending s in
  fp_inv PBL s' /\ dcall ILEN OCAP tot0 s' /\ cty s'
  /\ 0 <= ds_bi_valid s' <= 7 /\ bvol s' <= bvol s
  /\ (cs_avail_out (ds_strm s') <> 0 -> ds_pending s' = 0 /\ ds_pending_out s' = 0)
  /\ kproj s' = kproj (set_pending_out (set_strm s (ds_strm s')) (ds_pending_out s'))
  /\ cs_next_in (ds_strm s') = cs_next_in (ds_strm s) /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s)
  /\ cs_total_in (ds_strm s') = cs_total_in (ds_strm s) /\ cs_adler (ds_strm s') = cs_adler (ds_strm s)
  /\ cs_data_type (ds_strm s') = cs_data_type (ds_strm s) /\ cs_input (ds_strm s') = cs_input (ds_strm s) /\ cs_msg (ds_strm s') = cs_msg (ds_strm s)
  /\ zlength (cs_out_rev (ds_strm s)) <= zlength (cs_out_rev (ds_strm s'))
  /\ cs_avail_out (ds_strm s') <= cs_avail_out (ds_strm s)
  /\ eproj (set_pending_out (set_strm s' (ds_strm s)) (ds_pending_out s)) = eproj s.
Proof.
  intros ILEN OCAP tot0 PBL s [HB Hpo HV HPBL Hpo0 HPS] HC HT.
  assert (SELF : forall x : deflate_state, set_pending_out (set_strm x (ds_strm x)) (ds_pending_out x) = x) by (intros x; destruct x; reflexivity).
  destruct (bi_flush_bits s HB) as (HB1 & V1 & B1 & P1). pose proof (bo_pd _ HB) as B0c. pose proof (bo_bv _ HB) as B0a.
  pose proof (ep_bi_flush s) as EP1.
  assert (S1 : ds_strm (bi_flush s) = ds_strm s) by exact (ep_strm _ _ EP1).
  assert (W1 : ds_wrap (bi_flush s) = ds_wrap s) by exact (ep_wrap _ _ EP1).
  assert (HC1 : dcall ILEN OCAP tot0 (bi_flush s)) by (destruct HC; constructor; rewrite ?S1, ?W1; assumption).
  assert (HT1 : cty (bi_flush s)) by (apply cty_bi_flush; exact HT).
  pose proof (ep_pending_out _ _ EP1) as PO1. pose proof (ep_len_pending_buf _ _ EP1) as PL1.
  assert (Hp32 : 0 <= ds_pending (tr_flush_bits s) < 2 ^ 32).
  { change (tr_flush_bits s) with (bi_flush s). unfold bvol in *. destruct HB1. pose proof (dc_ocap32 _ _ _ _ HC). lia. }
  rewrite (flush_pending_eqm s Hp32). cbv zeta. change (tr_flush_bits s) with (bi_flush s) in *.
  remember (bi_flush s) as s1 eqn:Es1.
  assert (KP1 : kproj s1 = kproj s) by (apply ep_kp; exact EP1).
  destruct (Z.eqb_spec (fpm_len s1) 0) as [Z0|Z0].
  -
    unfold fpm_len in Z0. unfold bvol in *. destruct HB1 as [A1 A2 A3].
    assert (ALT : ds_pending s1 = 0 \/ cs_avail_out (ds_strm s1) = 0).
    { destruct (Z.ltb_spec (cs_avail_out (ds_strm s1)) (ds_pending s1)); lia. }
    split; [split; unfold bvol in *; [split; assumption | rewrite PO1; exact Hpo | rewrite PO1; lia | rewrite PL1; exact HPBL | intros E; rewrite PO1; apply Hpo0; lia | exact HPS]|].
    split; [exact HC1|]. split; [exact HT1|]. split; [lia|]. split; [unfold bvol in *; lia|].
    split; [intros Ha; destruct ALT as [E|E]; [| lia]; split; [exact E | rewrite PO1; apply Hpo0; lia]|].
    split; [rewrite kproj_spo, <- KP1; symmetry; apply kspo_self|].
    rewrite <- S1, <- PO1, SELF. repeat split; try reflexivity; try lia. exact EP1.
  - destruct (fpm_post_fields s1 (fpm_len s1)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17).
    remember (fpm_post s1 (fpm_len s1)) as s2 eqn:Es2.
    assert (LEN : 0 < fpm_len s1 <= ds_pending s1 /\ fpm_len s1 <= cs_avail_out (ds_strm s1)).
    { unfold fpm_len in *. pose proof (dc_ao _ _ _ _ HC1). destruct HB1.
      destruct (Z.ltb_spec (cs_avail_out (ds_strm s1)) (ds_pending s1)); lia. }
    destruct HB1 as [A1 A2 A3]. unfold bvol in *.
    assert (KP2 : kproj s2 = kproj (set_pending_out (set_strm s (ds_strm s2)) (ds_pending_out s2))).
    { rewrite kproj_spo, <- KP1, <- (ep_kp _ _ F13), kproj_spo, kspo_kspo. symmetry. apply kspo_self. }
    assert (SL : Forall (fun b => 0 <= b < 256) (arr_slice (ds_pending_buf s1) (ds_pending_out s1) (fpm_len s1))).
    { apply u8a_slice; [exact (ct_pb _ HT1)|]. intros _. rewrite PL1, HPBL, PO1. lia. }
    split.
    { constructor.
      - split; rewrite ?F1, ?F14, ?F15; lia.
      - rewrite F2. destruct (Z.eqb_spec (ds_pending s1 - fpm_len s1) 0); lia.
      - unfold bvol. rewrite F1, F2, F14. destruct (Z.eqb_spec (ds_pending s1 - fpm_len s1) 0); lia.
      - rewrite F16, PL1. exact HPBL.
      - intros E. rewrite F2. rewrite F1 in E. rewrite E, Z.eqb_refl. reflexivity.
      - exact HPS. }
    split.
    { destruct HC1; constructor; rewrite ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11, ?F17, ?zlength_rev_append, ?arr_slice_length; try assumption; try lia.
      - apply Forall_rev_append; assumption.
      - rewrite dc_to. rewrite wrap64_add_l. f_equal. lia. }
    split.
    { exact (cty_ep_spo _ _ _ _ F13 F9 F16 HT1). }
    split; [rewrite F14; lia|]. split; [rewrite F1, F14; lia|].
    split; [intros Ha; rewrite F4 in Ha; rewrite F1, F2; assert (E : ds_pending s1 - fpm_len s1 = 0) by (unfold fpm_len in *; destruct (Z.ltb_spec (cs_avail_out (ds_strm s1)) (ds_pending s1)); lia); rewrite E, Z.eqb_refl; split; reflexivity|].
    split; [exact KP2|].
    rewrite F6, F7, F8, F10, F11, F9, F12, F3, F4, S1, zlength_rev_append, arr_slice_length. rewrite <- S1, <- PO1, F13. repeat split; try reflexivity; try lia. exact EP1.
Qed.
