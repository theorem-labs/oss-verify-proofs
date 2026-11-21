(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateInvKeep OverlayFBS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import DeflInvTally.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Tfb.
  Variables (s : deflate_state) (buf : option Z) (len last : Z).
  Let s' := tr_flush_block s buf len last.
  Let K := kp_tr_flush_block s buf len last.

  Lemma tfb_fields :
    ds_strstart s' = ds_strstart s /\ ds_lookahead s' = ds_lookahead s /\ ds_block_start s' = ds_block_start s
    /\ ds_insert s' = ds_insert s /\ ds_match_length s' = ds_match_length s /\ ds_match_start s' = ds_match_start s
    /\ ds_prev_length s' = ds_prev_length s /\ ds_prev_match s' = ds_prev_match s /\ ds_match_available s' = ds_match_available s
    /\ ds_ins_h s' = ds_ins_h s /\ ds_high_water s' = ds_high_water s /\ ds_window s' = ds_window s /\ ds_prev s' = ds_prev s
    /\ ds_head s' = ds_head s /\ ds_w_size s' = ds_w_size s /\ ds_hash_size s' = ds_hash_size s
    /\ ds_lit_bufsize s' = ds_lit_bufsize s /\ ds_sym_end s' = ds_sym_end s /\ ds_pending_out s' = ds_pending_out s
    /\ ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s /\ ds_status s' = ds_status s /\ ds_wrap s' = ds_wrap s
    /\ ds_last_flush s' = ds_last_flush s /\ ds_sym_next s' = 0 /\ ds_matches s' = 0
    /\ ds_strm s' = cset_data_type (ds_strm s) (cs_data_type (ds_strm s'))
    /\ arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s)
    /\ ds_w_mask s' = ds_w_mask s /\ ds_hash_mask s' = ds_hash_mask s /\ ds_hash_shift s' = ds_hash_shift s
    /\ ds_window_size s' = ds_window_size s /\ ds_max_lazy_match s' = ds_max_lazy_match s /\ ds_max_chain_length s' = ds_max_chain_length s
    /\ ds_good_match s' = ds_good_match s /\ ds_nice_match s' = ds_nice_match s /\ ds_pending_buf_size s' = ds_pending_buf_size s
    /\ ds_w_bits s' = ds_w_bits s /\ ds_hash_bits s' = ds_hash_bits s /\ ds_gzhead s' = ds_gzhead s /\ ds_method s' = ds_method s
    /\ ds_window_blk s' = ds_window_blk s /\ ds_prev_blk s' = ds_prev_blk s /\ ds_head_blk s' = ds_head_blk s
    /\ ds_pending_buf_blk s' = ds_pending_buf_blk s /\ ds_self_blk s' = ds_self_blk s.
  Proof.
    pose proof (kp_strstart _ _ K) as E1. rewrite ?strstart_set_strm, ?strstart_set_sym_next, ?strstart_set_matches in E1.
    pose proof (kp_lookahead _ _ K) as E2. rewrite ?lookahead_set_strm, ?lookahead_set_sym_next, ?lookahead_set_matches in E2.
    pose proof (kp_block_start _ _ K) as E3. rewrite ?block_start_set_strm, ?block_start_set_sym_next, ?block_start_set_matches in E3.
    pose proof (kp_insert _ _ K) as E4. rewrite ?insert_set_strm, ?insert_set_sym_next, ?insert_set_matches in E4.
    pose proof (kp_match_length _ _ K) as E5. rewrite ?match_length_set_strm, ?match_length_set_sym_next, ?match_length_set_matches in E5.
    pose proof (kp_match_start _ _ K) as E6. rewrite ?match_start_set_strm, ?match_start_set_sym_next, ?match_start_set_matches in E6.
    pose proof (kp_prev_length _ _ K) as E7. rewrite ?prev_length_set_strm, ?prev_length_set_sym_next, ?prev_length_set_matches in E7.
    pose proof (kp_prev_match _ _ K) as E8. rewrite ?prev_match_set_strm, ?prev_match_set_sym_next, ?prev_match_set_matches in E8.
    pose proof (kp_match_available _ _ K) as E9. rewrite ?match_available_set_strm, ?match_available_set_sym_next, ?match_available_set_matches in E9.
    pose proof (kp_ins_h _ _ K) as E10. rewrite ?ins_h_set_strm, ?ins_h_set_sym_next, ?ins_h_set_matches in E10.
    pose proof (kp_high_water _ _ K) as E11. rewrite ?high_water_set_strm, ?high_water_set_sym_next, ?high_water_set_matches in E11.
    pose proof (kp_window _ _ K) as E12. rewrite ?window_set_strm, ?window_set_sym_next, ?window_set_matches in E12.
    pose proof (kp_prev _ _ K) as E13. rewrite ?prev_set_strm, ?prev_set_sym_next, ?prev_set_matches in E13.
    pose proof (kp_head _ _ K) as E14. rewrite ?head_set_strm, ?head_set_sym_next, ?head_set_matches in E14.
    pose proof (kp_w_size _ _ K) as E15. rewrite ?w_size_set_strm, ?w_size_set_sym_next, ?w_size_set_matches in E15.
    pose proof (kp_hash_size _ _ K) as E16. rewrite ?hash_size_set_strm, ?hash_size_set_sym_next, ?hash_size_set_matches in E16.
    pose proof (kp_lit_bufsize _ _ K) as E17. rewrite ?lit_bufsize_set_strm, ?lit_bufsize_set_sym_next, ?lit_bufsize_set_matches in E17.
    pose proof (kp_sym_end _ _ K) as E18. rewrite ?sym_end_set_strm, ?sym_end_set_sym_next, ?sym_end_set_matches in E18.
    pose proof (kp_pending_out _ _ K) as E19. rewrite ?pending_out_set_strm, ?pending_out_set_sym_next, ?pending_out_set_matches in E19.
    pose proof (kp_level _ _ K) as E20. rewrite ?level_set_strm, ?level_set_sym_next, ?level_set_matches in E20.
    pose proof (kp_strategy _ _ K) as E21. rewrite ?strategy_set_strm, ?strategy_set_sym_next, ?strategy_set_matches in E21.
    pose proof (kp_status _ _ K) as E22. rewrite ?status_set_strm, ?status_set_sym_next, ?status_set_matches in E22.
    pose proof (kp_wrap _ _ K) as E23. rewrite ?wrap_set_strm, ?wrap_set_sym_next, ?wrap_set_matches in E23.
    pose proof (kp_last_flush _ _ K) as E24. rewrite ?last_flush_set_strm, ?last_flush_set_sym_next, ?last_flush_set_matches in E24.
    pose proof (kp_sym_next _ _ K) as E25. rewrite ?sym_next_set_strm, ?sym_next_set_sym_next, ?sym_next_set_matches in E25.
    pose proof (kp_matches _ _ K) as E26. rewrite ?matches_set_strm, ?matches_set_sym_next, ?matches_set_matches in E26.
    pose proof (kp_strm _ _ K) as E27. rewrite ?strm_set_strm, ?strm_set_sym_next, ?strm_set_matches in E27.
    pose proof (kp_len_pending_buf _ _ K) as E28. rewrite ?pending_buf_set_strm, ?pending_buf_set_sym_next, ?pending_buf_set_matches in E28.
    pose proof (kp_w_mask _ _ K) as E29. rewrite ?w_mask_set_strm, ?w_mask_set_sym_next, ?w_mask_set_matches in E29.
    pose proof (kp_hash_mask _ _ K) as E30. rewrite ?hash_mask_set_strm, ?hash_mask_set_sym_next, ?hash_mask_set_matches in E30.
    pose proof (kp_hash_shift _ _ K) as E31. rewrite ?hash_shift_set_strm, ?hash_shift_set_sym_next, ?hash_shift_set_matches in E31.
    pose proof (kp_window_size _ _ K) as E32. rewrite ?window_size_set_strm, ?window_size_set_sym_next, ?window_size_set_matches in E32.
    pose proof (kp_max_lazy_match _ _ K) as E33. rewrite ?max_lazy_match_set_strm, ?max_lazy_match_set_sym_next, ?max_lazy_match_set_matches in E33.
    pose proof (kp_max_chain_length _ _ K) as E34. rewrite ?max_chain_length_set_strm, ?max_chain_length_set_sym_next, ?max_chain_length_set_matches in E34.
    pose proof (kp_good_match _ _ K) as E35. rewrite ?good_match_set_strm, ?good_match_set_sym_next, ?good_match_set_matches in E35.
    pose proof (kp_nice_match _ _ K) as E36. rewrite ?nice_match_set_strm, ?nice_match_set_sym_next, ?nice_match_set_matches in E36.
    pose proof (kp_pending_buf_size _ _ K) as E37. rewrite ?pending_buf_size_set_strm, ?pending_buf_size_set_sym_next, ?pending_buf_size_set_matches in E37.
    pose proof (kp_w_bits _ _ K) as E38. rewrite ?w_bits_set_strm, ?w_bits_set_sym_next, ?w_bits_set_matches in E38.
    pose proof (kp_hash_bits _ _ K) as E39. rewrite ?hash_bits_set_strm, ?hash_bits_set_sym_next, ?hash_bits_set_matches in E39.
    pose proof (kp_gzhead _ _ K) as E40. rewrite ?gzhead_set_strm, ?gzhead_set_sym_next, ?gzhead_set_matches in E40.
    pose proof (kp_method _ _ K) as E41. rewrite ?method_set_strm, ?method_set_sym_next, ?method_set_matches in E41.
    pose proof (kp_window_blk _ _ K) as E42. rewrite ?window_blk_set_strm, ?window_blk_set_sym_next, ?window_blk_set_matches in E42.
    pose proof (kp_prev_blk _ _ K) as E43. rewrite ?prev_blk_set_strm, ?prev_blk_set_sym_next, ?prev_blk_set_matches in E43.
    pose proof (kp_head_blk _ _ K) as E44. rewrite ?head_blk_set_strm, ?head_blk_set_sym_next, ?head_blk_set_matches in E44.
    pose proof (kp_pending_buf_blk _ _ K) as E45. rewrite ?pending_buf_blk_set_strm, ?pending_buf_blk_set_sym_next, ?pending_buf_blk_set_matches in E45.
    pose proof (kp_self_blk _ _ K) as E46. rewrite ?self_blk_set_strm, ?self_blk_set_sym_next, ?self_blk_set_matches in E46.
    unfold s'.
    repeat split; assumption.
  Qed.

  Lemma tfb_dsyms_nil : fbs_tree_lens s -> dsyms [] s'.
  Proof.
    intros HT. subst s'. clear K. unfold tr_flush_block.
    set (s1 := if cs_data_type (ds_strm s) =? Z_UNKNOWN then set_strm s (cset_data_type (ds_strm s) (detect_data_type s)) else s).
    assert (K1 : kproj s1 = kproj (set_strm s (cset_data_type (ds_strm s) (cs_data_type (ds_strm s1))))).
    { subst s1. destruct (cs_data_type (ds_strm s) =? Z_UNKNOWN); destruct s; cbn; [reflexivity|]. destruct ds_strm; reflexivity. }
    assert (TLk : forall a b, kproj a = kproj b -> fbs_tree_lens b -> fbs_tree_lens a).
    { intros a b Hk Hb. unfold fbs_tree_lens in *.
      rewrite (kp_len_dyn_ltree_fc _ _ Hk), (kp_len_dyn_ltree_dl _ _ Hk), (kp_len_dyn_dtree_fc _ _ Hk), (kp_len_dyn_dtree_dl _ _ Hk),
              (kp_len_bl_tree_fc _ _ Hk), (kp_len_bl_tree_dl _ _ Hk), (kp_len_bl_count _ _ Hk), (kp_len_heap _ _ Hk), (kp_len_depth _ _ Hk).
      exact Hb. }
    assert (TLs : forall a v, fbs_tree_lens a -> fbs_tree_lens (set_strm a v)) by (intros a v H; destruct a; exact H).
    assert (TAIL : forall a, fbs_tree_lens a -> dsyms [] (if negb (last =? 0) then bi_windup (init_block a) else init_block a)).
    { intros a Ha. destruct (negb (last =? 0)); [| apply dsyms_init_block; exact Ha].
      eapply dsyms_nil_ep; [apply dsyms_init_block; exact Ha | apply ep_bi_windup]. }
    destruct (0 <? ds_level s).
    - destruct (build_bl_tree (build_tree (build_tree s1 TL) TD)) as [s4 mb] eqn:E4.
      pose proof (kp_build_bl_tree (build_tree (build_tree s1 TL) TD)) as K4. rewrite E4 in K4. cbn [fst] in K4. rewrite !kp_build_tree in K4.
      cbv beta iota zeta. apply TAIL.
      match goal with |- fbs_tree_lens ?a => set (X7 := a) in * end.
      assert (KA : kproj X7 = kproj s1).
      { subst X7. repeat match goal with |- context [if ?c then _ else _] => destruct c end;
          rewrite ?kp_tr_stored_block, ?kp_compress_block, ?kp_send_all_trees, ?kp_send_bits; exact K4. }
      apply (TLk _ _ KA). apply (TLk _ _ K1). apply TLs. exact HT.
    - cbv beta iota zeta. apply TAIL.
      match goal with |- fbs_tree_lens ?a => set (X7 := a) in * end.
      assert (KA : kproj X7 = kproj s).
      { subst X7. repeat match goal with |- context [if ?c then _ else _] => destruct c end;
          rewrite ?kp_tr_stored_block, ?kp_compress_block, ?kp_send_all_trees, ?kp_send_bits; reflexivity. }
      exact (TLk _ _ KA HT).
  Qed.
End Tfb.
