(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Definition fw_rest (s : deflate_state) :=
  (ds_status s, ds_pending_buf s, ds_pending_buf_size s, ds_pending_out s, ds_pending s, ds_wrap s,
   ds_gzhead s, ds_gzindex s, ds_method s, ds_last_flush s, ds_w_size s, ds_w_bits s, ds_w_mask s,
   ds_window_size s, ds_hash_size s, ds_hash_bits s, ds_hash_mask s, ds_hash_shift s,
   ds_match_length s, ds_prev_match s, ds_match_available s, ds_prev_length s,
   (ds_max_chain_length s, ds_max_lazy_match s, ds_level s, ds_strategy s, ds_good_match s, ds_nice_match s,
    ds_dyn_ltree_fc s, ds_dyn_ltree_dl s, ds_dyn_dtree_fc s, ds_dyn_dtree_dl s, ds_bl_tree_fc s, ds_bl_tree_dl s,
    ds_l_max_code s, ds_d_max_code s, ds_bl_max_code s, ds_bl_count s, ds_heap s, ds_heap_len s, ds_heap_max s,
    ds_depth s, ds_lit_bufsize s, ds_sym_next s, ds_sym_end s, ds_opt_len s, ds_static_len s, ds_matches s,
    ds_bi_buf s, ds_bi_valid s),
   (cs_input (ds_strm s), cs_out_rev (ds_strm s), cs_avail_out (ds_strm s), cs_total_out (ds_strm s),
    cs_msg (ds_strm s), cs_data_type (ds_strm s))).

Lemma fw_rest_read_buf : forall s off n, fw_rest (fst (read_buf s (RB_window off) n)) = fw_rest s.
Proof.
  intros s off n. unfold read_buf. cbv beta iota zeta. dsred.
  destruct ((if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)) =? 0); [reflexivity|].
  destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; unfold fw_rest; dsred; reflexivity.
Qed.

Lemma fw_rest_insert : forall n s str, fw_rest (fill_window_insert n s str) = fw_rest s.
Proof.
  induction n as [|n IH]; intros s str; [reflexivity|].
  cbn -[fw_rest update_hash Z.ltb Z.eqb Z.add Z.sub Z.land arr_get arr_set wrap16 negb].
  destruct (negb (ds_insert s =? 0)); [|reflexivity].
  destruct (_ <? _); [unfold fw_rest; dsred; reflexivity|].
  rewrite IH. unfold fw_rest; dsred; reflexivity.
Qed.

Lemma fw_rest_slide_hash : forall s, fw_rest (slide_hash s) = fw_rest s.
Proof. intros s. unfold slide_hash, fw_rest. dsred. reflexivity. Qed.

Lemma fw_rest_body : forall s ws, fw_rest (fst (fill_window_body s ws)) = fw_rest s.
Proof.
  intros s ws. rewrite fill_window_body_eq.
  set (s1 := if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then fw_slide s ws (fw_more s) else s).
  set (m1 := if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then wrap32 (fw_more s + ws) else fw_more s).
  assert (E1 : fw_rest s1 = fw_rest s).
  { subst s1. destruct (_ <=? _); [|reflexivity]. unfold fw_slide. rewrite fw_rest_slide_hash.
    destruct (_ <? _); unfold fw_rest; dsred; reflexivity. }
  replace (if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then (fw_slide s ws (fw_more s), wrap32 (fw_more s + ws)) else (s, fw_more s))
    with (s1, m1) by (subst s1 m1; destruct (_ <=? _); reflexivity).
  cbv beta iota zeta.
  destruct (cs_avail_in (ds_strm s1) =? 0); [exact E1|].
  destruct (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) m1) as [s2 n] eqn:E2.
  pose proof (fw_rest_read_buf s1 (ds_strstart s1 + ds_lookahead s1) m1) as E2'. rewrite E2 in E2'. cbn [fst] in E2'.
  cbn [fst]. unfold fw_insert. dsred. destruct (MIN_MATCH <=? _).
  - rewrite fw_rest_insert. rewrite <- E1, <- E2'. unfold fw_rest; dsred; reflexivity.
  - rewrite <- E1, <- E2'. unfold fw_rest; dsred; reflexivity.
Qed.

Lemma fw_rest_loop : forall n s ws, fw_rest (fill_window_loop n s ws) = fw_rest s.
Proof.
  induction n as [|n IH]; intros s ws; [reflexivity|].
  cbn [fill_window_loop]. destruct (fill_window_body s ws) as [s1 b] eqn:E.
  pose proof (fw_rest_body s ws) as E'. rewrite E in E'. cbn [fst] in E'.
  destruct b; [exact E'|]. destruct (_ && _); [rewrite IH; exact E' | exact E'].
Qed.

Lemma fw_rest_high : forall s, fw_rest (fill_window_high s) = fw_rest s.
Proof.
  intros s. unfold fill_window_high.
  destruct (_ <? _); [|reflexivity]. destruct (_ <? _); [unfold fw_rest; dsred; reflexivity|].
  destruct (_ <? _); [unfold fw_rest; dsred; reflexivity | reflexivity].
Qed.

Lemma fw_rest_fill_window : forall s, fw_rest (fill_window s) = fw_rest s.
Proof. intros s. unfold fill_window. rewrite fw_rest_high, fw_rest_loop. reflexivity. Qed.


Lemma longest_match_body_ms : forall s cur cl bl nice lim se1 se,
  exists ms, fst (fst (fst (fst (fst (fst (longest_match_body s cur cl bl nice lim se1 se)))))) = set_match_start s ms.
Proof.
  intros. unfold longest_match_body.
  destruct (_ || _).
  - destruct (_ <? _); [destruct (negb _)|]; exists (ds_match_start s); symmetry; apply set_ms_self.
  - destruct (_ <? _).
    + destruct (_ <=? _); [exists cur; reflexivity|].
      destruct (_ <? _); [destruct (negb _)|]; exists cur; reflexivity.
    + destruct (_ <? _); [destruct (negb _)|]; exists (ds_match_start s); symmetry; apply set_ms_self.
Qed.

Lemma longest_match_loop_ms : forall n s cur cl bl nice lim se1 se,
  exists ms, fst (longest_match_loop n s cur cl bl nice lim se1 se) = set_match_start s ms.
Proof.
  induction n as [|n IH]; intros.
  - exists (ds_match_start s). symmetry. apply set_ms_self.
  - cbn [longest_match_loop].
    destruct (longest_match_body s cur cl bl nice lim se1 se) as [[[[[[s1 bl1] a1] a2] c1] cl1] cont] eqn:E.
    pose proof (longest_match_body_ms s cur cl bl nice lim se1 se) as [ms1 E1]. rewrite E in E1. cbn [fst] in E1.
    destruct cont.
    + destruct (IH s1 c1 cl1 bl1 nice lim a1 a2) as [ms2 E2]. rewrite E2, E1. exists ms2. apply set_ms_twice.
    + exists ms1. exact E1.
Qed.

Lemma longest_match_ms : forall s cur, exists ms, fst (longest_match s cur) = set_match_start s ms.
Proof.
  intros s cur. unfold longest_match.
  destruct (longest_match_loop _ _ _ _ _ _ _ _ _) as [s1 bl] eqn:E.
  match type of E with ?l = _ => pose proof (longest_match_loop_ms (Z.to_nat (if ds_good_match s <=? ds_prev_length s then Z.shiftr (ds_max_chain_length s) 2 else ds_max_chain_length s)) s cur
     (if ds_good_match s <=? ds_prev_length s then Z.shiftr (ds_max_chain_length s) 2 else ds_max_chain_length s)
     (ds_prev_length s) (if ds_lookahead s <? ds_nice_match s then ds_lookahead s else ds_nice_match s)
     (if ds_w_size s - MIN_LOOKAHEAD <? ds_strstart s then ds_strstart s - (ds_w_size s - MIN_LOOKAHEAD) else NIL)
     (arr_get (ds_window s) (ds_strstart s + ds_prev_length s - 1)) (arr_get (ds_window s) (ds_strstart s + ds_prev_length s))) as [ms Hms] end.
  rewrite E in Hms. cbn [fst] in Hms. exists ms. destruct (bl <=? ds_lookahead s1); cbn [fst]; exact Hms.
Qed.


Definition fp_len (s1 : deflate_state) : Z :=
  let len := wrap32 (ds_pending s1) in
  if cs_avail_out (ds_strm s1) <? len then cs_avail_out (ds_strm s1) else len.

Definition fp_tail (s1 : deflate_state) (len : Z) : deflate_state :=
  let st := ds_strm s1 in
  let st1 := cs_emit st (arr_slice (ds_pending_buf s1) (ds_pending_out s1) len) in
  let s2 := set_strm s1 st1 in
  let s3 := set_pending_out s2 (ds_pending_out s1 + len) in
  let s4 := set_strm s3 (cset_avail_out st1 (cs_avail_out st - len)) in
  let s5 := set_strm s4 (cset_total_out (cset_avail_out st1 (cs_avail_out st - len)) (wrap64 (cs_total_out st + len))) in
  let s6 := set_pending s5 (ds_pending s1 - len) in
  if ds_pending s1 - len =? 0 then set_pending_out s6 0 else s6.

Lemma flush_pending_eq : forall s,
  flush_pending s =
  (let s1 := tr_flush_bits s in
   let len := fp_len s1 in
   if len =? 0 then s1 else fp_tail s1 len).
Proof.
  intros s. unfold flush_pending, fp_len, fp_tail. cbv zeta.
  set (s1 := tr_flush_bits s). clearbody s1.
  destruct (_ =? 0) eqn:E0; [reflexivity|].
  destruct s1; cbn -[Z.sub Z.add Z.eqb wrap64 wrap32 arr_slice cs_emit Z.ltb].
  destruct ds_strm; cbn -[Z.sub Z.add Z.eqb wrap64 wrap32 arr_slice Z.ltb].
  destruct (_ =? 0); reflexivity.
Qed.
End FXG.
