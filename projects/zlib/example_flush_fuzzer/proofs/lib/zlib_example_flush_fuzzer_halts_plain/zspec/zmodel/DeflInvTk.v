(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateInvKeep DeflateSetters.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import RefDeflatePost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition tkz (st : cstrm) : Z := (cs_total_in st - cs_next_in st) mod 2 ^ 64.
Definition tk (s : deflate_state) : Z := tkz (ds_strm s).

Lemma tk_kp : forall a b, kproj a = kproj b -> tk a = tk b.
Proof. intros a b K. unfold tk. rewrite (kp_strm _ _ K). reflexivity. Qed.
Lemma tk_set_strm : forall s st, tkz st = tkz (ds_strm s) -> tk (set_strm s st) = tk s.
Proof. intros s st E. unfold tk. destruct s. exact E. Qed.

Lemma tk_tr_tally_lit : forall s c, tk (fst (tr_tally_lit s c)) = tk s.
Proof. intros s c. rewrite (tk_kp _ _ (kp_tr_tally_lit s c)). reflexivity. Qed.
Lemma tk_tr_tally_dist : forall s d l, tk (fst (tr_tally_dist s d l)) = tk s.
Proof. intros s d l. rewrite (tk_kp _ _ (kp_tr_tally_dist s d l)). reflexivity. Qed.
Lemma tk_tr_flush_block : forall s buf len last, tk (tr_flush_block s buf len last) = tk s.
Proof. intros. rewrite (tk_kp _ _ (kp_tr_flush_block s buf len last)). unfold tk. destruct s; reflexivity. Qed.
Lemma tk_tr_stored_block : forall s buf len last, tk (tr_stored_block s buf len last) = tk s.
Proof. intros. exact (tk_kp _ _ (kp_tr_stored_block s buf len last)). Qed.
Lemma tk_tr_align : forall s, tk (tr_align s) = tk s.
Proof. intros. exact (tk_kp _ _ (kp_tr_align s)). Qed.
Lemma tk_bi_flush : forall s, tk (bi_flush s) = tk s.
Proof. intros. unfold bi_flush, put_short. destruct (_ =? _); [reflexivity|]. destruct (_ <=? _); reflexivity. Qed.
Lemma tk_flush_pending : forall s, tk (flush_pending s) = tk s.
Proof.
  intros. unfold flush_pending, tr_flush_bits. cbv zeta.
  destruct (_ =? 0); [apply tk_bi_flush|]. rewrite <- (tk_bi_flush s). destruct (_ =? 0); reflexivity.
Qed.


Ltac tkz_tac :=
  lazymatch goal with
  | |- tkz ?v = tkz (ds_strm ?a) => generalize (ds_strm a); let st := fresh "st" in intros st; destruct st; reflexivity
  end.

Ltac tkgoA1 :=
  lazymatch goal with
  | |- tk ?x = tk ?x => reflexivity
  | |- tk (let x := ?t in @?E x) = tk ?s0 =>
      first [ is_var t; change (tk (E t) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (E t) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (let x := ?t in @?E x)) = tk ?s0 =>
      first [ is_var t; change (tk (fst (E t)) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (fst (E t)) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (?a, ?b)) = _ => change (tk (fst (a, b))) with (tk a)
  | |- tk (set_bi_buf ?a ?v) = _ => change (tk (set_bi_buf a v)) with (tk a)
  | |- tk (set_bi_valid ?a ?v) = _ => change (tk (set_bi_valid a v)) with (tk a)
  | |- tk (set_bl_count ?a ?v) = _ => change (tk (set_bl_count a v)) with (tk a)
  | |- tk (set_bl_max_code ?a ?v) = _ => change (tk (set_bl_max_code a v)) with (tk a)
  | |- tk (set_bl_tree_dl ?a ?v) = _ => change (tk (set_bl_tree_dl a v)) with (tk a)
  | |- tk (set_bl_tree_fc ?a ?v) = _ => change (tk (set_bl_tree_fc a v)) with (tk a)
  | |- tk (set_block_start ?a ?v) = _ => change (tk (set_block_start a v)) with (tk a)
  | |- tk (set_d_max_code ?a ?v) = _ => change (tk (set_d_max_code a v)) with (tk a)
  | |- tk (set_depth ?a ?v) = _ => change (tk (set_depth a v)) with (tk a)
  | |- tk (set_dyn_dtree_dl ?a ?v) = _ => change (tk (set_dyn_dtree_dl a v)) with (tk a)
  | |- tk (set_dyn_dtree_fc ?a ?v) = _ => change (tk (set_dyn_dtree_fc a v)) with (tk a)
  | |- tk (set_dyn_ltree_dl ?a ?v) = _ => change (tk (set_dyn_ltree_dl a v)) with (tk a)
  | |- tk (set_dyn_ltree_fc ?a ?v) = _ => change (tk (set_dyn_ltree_fc a v)) with (tk a)
  | |- tk (set_good_match ?a ?v) = _ => change (tk (set_good_match a v)) with (tk a)
  | |- tk (set_gzhead ?a ?v) = _ => change (tk (set_gzhead a v)) with (tk a)
  | |- tk (set_gzindex ?a ?v) = _ => change (tk (set_gzindex a v)) with (tk a)
  | |- tk (set_hash_bits ?a ?v) = _ => change (tk (set_hash_bits a v)) with (tk a)
  | |- tk (set_hash_mask ?a ?v) = _ => change (tk (set_hash_mask a v)) with (tk a)
  | |- tk (set_hash_shift ?a ?v) = _ => change (tk (set_hash_shift a v)) with (tk a)
  | |- tk (set_head ?a ?v) = _ => change (tk (set_head a v)) with (tk a)
  | |- tk (set_heap ?a ?v) = _ => change (tk (set_heap a v)) with (tk a)
  | |- tk (set_heap_len ?a ?v) = _ => change (tk (set_heap_len a v)) with (tk a)
  | |- tk (set_heap_max ?a ?v) = _ => change (tk (set_heap_max a v)) with (tk a)
  | |- tk (set_high_water ?a ?v) = _ => change (tk (set_high_water a v)) with (tk a)
  | |- tk (set_ins_h ?a ?v) = _ => change (tk (set_ins_h a v)) with (tk a)
  | |- tk (set_insert ?a ?v) = _ => change (tk (set_insert a v)) with (tk a)
  | |- tk (set_l_max_code ?a ?v) = _ => change (tk (set_l_max_code a v)) with (tk a)
  | |- tk (set_last_flush ?a ?v) = _ => change (tk (set_last_flush a v)) with (tk a)
  | |- tk (set_level ?a ?v) = _ => change (tk (set_level a v)) with (tk a)
  | |- tk (set_lookahead ?a ?v) = _ => change (tk (set_lookahead a v)) with (tk a)
  | |- tk (set_match_available ?a ?v) = _ => change (tk (set_match_available a v)) with (tk a)
  | |- tk (set_match_length ?a ?v) = _ => change (tk (set_match_length a v)) with (tk a)
  | |- tk (set_match_start ?a ?v) = _ => change (tk (set_match_start a v)) with (tk a)
  | |- tk (set_matches ?a ?v) = _ => change (tk (set_matches a v)) with (tk a)
  | |- tk (set_max_chain_length ?a ?v) = _ => change (tk (set_max_chain_length a v)) with (tk a)
  | |- tk (set_max_lazy_match ?a ?v) = _ => change (tk (set_max_lazy_match a v)) with (tk a)
  | |- tk (set_method ?a ?v) = _ => change (tk (set_method a v)) with (tk a)
  | |- tk (set_nice_match ?a ?v) = _ => change (tk (set_nice_match a v)) with (tk a)
  | |- tk (set_opt_len ?a ?v) = _ => change (tk (set_opt_len a v)) with (tk a)
  | |- tk (set_pending ?a ?v) = _ => change (tk (set_pending a v)) with (tk a)
  | |- tk (set_pending_buf ?a ?v) = _ => change (tk (set_pending_buf a v)) with (tk a)
  | |- tk (set_pending_buf_size ?a ?v) = _ => change (tk (set_pending_buf_size a v)) with (tk a)
  | |- tk (set_pending_out ?a ?v) = _ => change (tk (set_pending_out a v)) with (tk a)
  | |- tk (set_prev ?a ?v) = _ => change (tk (set_prev a v)) with (tk a)
  | |- tk (set_prev_length ?a ?v) = _ => change (tk (set_prev_length a v)) with (tk a)
  | |- tk (set_prev_match ?a ?v) = _ => change (tk (set_prev_match a v)) with (tk a)
  | |- tk (set_static_len ?a ?v) = _ => change (tk (set_static_len a v)) with (tk a)
  | |- tk (set_status ?a ?v) = _ => change (tk (set_status a v)) with (tk a)
  | |- tk (set_strategy ?a ?v) = _ => change (tk (set_strategy a v)) with (tk a)
  | |- tk (set_strm ?a ?v) = _ => rewrite (tk_set_strm a v) by tkz_tac
  | |- tk (set_strstart ?a ?v) = _ => change (tk (set_strstart a v)) with (tk a)
  | |- tk (set_sym_end ?a ?v) = _ => change (tk (set_sym_end a v)) with (tk a)
  | |- tk (set_sym_next ?a ?v) = _ => change (tk (set_sym_next a v)) with (tk a)
  | |- tk (set_w_bits ?a ?v) = _ => change (tk (set_w_bits a v)) with (tk a)
  | |- tk (set_w_mask ?a ?v) = _ => change (tk (set_w_mask a v)) with (tk a)
  | |- tk (set_window ?a ?v) = _ => change (tk (set_window a v)) with (tk a)
  | |- tk (set_window_size ?a ?v) = _ => change (tk (set_window_size a v)) with (tk a)
  | |- tk (set_wrap ?a ?v) = _ => change (tk (set_wrap a v)) with (tk a)
  | |- tk (put_byte ?a ?v) = _ => change (tk (put_byte a v)) with (tk a)
  | |- tk (putShortMSB ?a ?v) = _ => change (tk (putShortMSB a v)) with (tk a)
  | |- tk (set_tree_fc ?a ?v ?w) = _ => change (tk (set_tree_fc a v w)) with (tk a)
  | |- tk (set_tree_dl ?a ?v ?w) = _ => change (tk (set_tree_dl a v w)) with (tk a)
  | |- tk (set_max_code ?a ?v ?w) = _ => change (tk (set_max_code a v w)) with (tk a)
  | |- tk (sym_buf_set ?a ?v ?w) = _ => change (tk (sym_buf_set a v w)) with (tk a)
  | |- tk (set_Freq ?a ?v ?w ?x) = _ => change (tk (set_Freq a v w x)) with (tk a)
  | |- tk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_flush_block a x0 x1 x2))
  | |- tk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_stored_block a x0 x1 x2))
  | |- tk (tr_align ?a ) = _ => apply (eq_trans (tk_tr_align a ))
  | |- tk (flush_pending ?a ) = _ => apply (eq_trans (tk_flush_pending a ))
  | |- tk (bi_flush ?a ) = _ => apply (eq_trans (tk_bi_flush a ))
  | |- tk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (tk_tr_tally_lit a x0))
  | |- tk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_tr_tally_dist a x0 x1))
  | |- tk (match ?t with pair _ _ => _ end) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (fst (match ?t with pair _ _ => _ end)) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (if ?c then _ else _) = _ => destruct c
  | |- tk (fst (if ?c then _ else _)) = _ => destruct c
  | |- tk ?y = tk _ => is_var y; assumption
  end.
Ltac tkgoA := repeat tkgoA1.


Lemma tk_insert_string : forall s str, tk (fst (insert_string s str)) = tk s.
Proof. intros. cbv beta delta [insert_string]. tkgoA. Qed.
Lemma tk_clear_hash : forall s, tk (clear_hash s) = tk s.
Proof. intros. cbv beta delta [clear_hash]. tkgoA. Qed.
Lemma tk_slide_hash : forall s, tk (slide_hash s) = tk s.
Proof. intros. cbv beta delta [slide_hash]. tkgoA. Qed.
Lemma tkz_bump : forall st st' len, cs_total_in st' = cs_total_in st -> cs_next_in st' = cs_next_in st ->
  tkz (cset_total_in (cset_next_in st' (cs_next_in st' + len)) (wrap64 (cs_total_in (cset_next_in st' (cs_next_in st' + len)) + len))) = tkz st.
Proof.
  intros st st' len A B. unfold tkz. destruct st'; cbn in *. rewrite A, B, wrap64_mod, Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma ds_strm_set_strm' : forall s st, ds_strm (set_strm s st) = st.
Proof. intros s st; destruct s; reflexivity. Qed.
Lemma ds_wrap_set_window' : forall s w, ds_wrap (set_window s w) = ds_wrap s.
Proof. intros s w; destruct s; reflexivity. Qed.
Lemma tk_read_buf : forall s dst size, tk (fst (read_buf s dst size)) = tk s.
Proof.
  intros. unfold read_buf. cbv zeta. destruct (_ =? 0); [reflexivity|].
  unfold tk. generalize (ds_strm s) as st0. intros st0.
  set (len := if size <? cs_avail_in st0 then size else cs_avail_in st0). clearbody len.
  set (bytes := arr_slice _ _ len). clearbody bytes.
  destruct dst as [off|]; cbv beta iota; cbn [fst]; rewrite ds_strm_set_strm', ?ds_wrap_set_window';
    (destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]); apply tkz_bump; destruct st0; reflexivity.
Qed.
Lemma tk_fill_window_insert : forall f s str, tk (fill_window_insert f s str) = tk s.
Proof.
  induction f as [|f IH]; intros s str; [reflexivity|]. cbn [fill_window_insert].
  tkgoA; apply (eq_trans (IH _ _)); tkgoA.
Qed.

Ltac tkgoB1 :=
  lazymatch goal with
  | |- tk ?x = tk ?x => reflexivity
  | |- tk (let x := ?t in @?E x) = tk ?s0 =>
      first [ is_var t; change (tk (E t) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (E t) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (let x := ?t in @?E x)) = tk ?s0 =>
      first [ is_var t; change (tk (fst (E t)) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (fst (E t)) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (?a, ?b)) = _ => change (tk (fst (a, b))) with (tk a)
  | |- tk (set_bi_buf ?a ?v) = _ => change (tk (set_bi_buf a v)) with (tk a)
  | |- tk (set_bi_valid ?a ?v) = _ => change (tk (set_bi_valid a v)) with (tk a)
  | |- tk (set_bl_count ?a ?v) = _ => change (tk (set_bl_count a v)) with (tk a)
  | |- tk (set_bl_max_code ?a ?v) = _ => change (tk (set_bl_max_code a v)) with (tk a)
  | |- tk (set_bl_tree_dl ?a ?v) = _ => change (tk (set_bl_tree_dl a v)) with (tk a)
  | |- tk (set_bl_tree_fc ?a ?v) = _ => change (tk (set_bl_tree_fc a v)) with (tk a)
  | |- tk (set_block_start ?a ?v) = _ => change (tk (set_block_start a v)) with (tk a)
  | |- tk (set_d_max_code ?a ?v) = _ => change (tk (set_d_max_code a v)) with (tk a)
  | |- tk (set_depth ?a ?v) = _ => change (tk (set_depth a v)) with (tk a)
  | |- tk (set_dyn_dtree_dl ?a ?v) = _ => change (tk (set_dyn_dtree_dl a v)) with (tk a)
  | |- tk (set_dyn_dtree_fc ?a ?v) = _ => change (tk (set_dyn_dtree_fc a v)) with (tk a)
  | |- tk (set_dyn_ltree_dl ?a ?v) = _ => change (tk (set_dyn_ltree_dl a v)) with (tk a)
  | |- tk (set_dyn_ltree_fc ?a ?v) = _ => change (tk (set_dyn_ltree_fc a v)) with (tk a)
  | |- tk (set_good_match ?a ?v) = _ => change (tk (set_good_match a v)) with (tk a)
  | |- tk (set_gzhead ?a ?v) = _ => change (tk (set_gzhead a v)) with (tk a)
  | |- tk (set_gzindex ?a ?v) = _ => change (tk (set_gzindex a v)) with (tk a)
  | |- tk (set_hash_bits ?a ?v) = _ => change (tk (set_hash_bits a v)) with (tk a)
  | |- tk (set_hash_mask ?a ?v) = _ => change (tk (set_hash_mask a v)) with (tk a)
  | |- tk (set_hash_shift ?a ?v) = _ => change (tk (set_hash_shift a v)) with (tk a)
  | |- tk (set_head ?a ?v) = _ => change (tk (set_head a v)) with (tk a)
  | |- tk (set_heap ?a ?v) = _ => change (tk (set_heap a v)) with (tk a)
  | |- tk (set_heap_len ?a ?v) = _ => change (tk (set_heap_len a v)) with (tk a)
  | |- tk (set_heap_max ?a ?v) = _ => change (tk (set_heap_max a v)) with (tk a)
  | |- tk (set_high_water ?a ?v) = _ => change (tk (set_high_water a v)) with (tk a)
  | |- tk (set_ins_h ?a ?v) = _ => change (tk (set_ins_h a v)) with (tk a)
  | |- tk (set_insert ?a ?v) = _ => change (tk (set_insert a v)) with (tk a)
  | |- tk (set_l_max_code ?a ?v) = _ => change (tk (set_l_max_code a v)) with (tk a)
  | |- tk (set_last_flush ?a ?v) = _ => change (tk (set_last_flush a v)) with (tk a)
  | |- tk (set_level ?a ?v) = _ => change (tk (set_level a v)) with (tk a)
  | |- tk (set_lookahead ?a ?v) = _ => change (tk (set_lookahead a v)) with (tk a)
  | |- tk (set_match_available ?a ?v) = _ => change (tk (set_match_available a v)) with (tk a)
  | |- tk (set_match_length ?a ?v) = _ => change (tk (set_match_length a v)) with (tk a)
  | |- tk (set_match_start ?a ?v) = _ => change (tk (set_match_start a v)) with (tk a)
  | |- tk (set_matches ?a ?v) = _ => change (tk (set_matches a v)) with (tk a)
  | |- tk (set_max_chain_length ?a ?v) = _ => change (tk (set_max_chain_length a v)) with (tk a)
  | |- tk (set_max_lazy_match ?a ?v) = _ => change (tk (set_max_lazy_match a v)) with (tk a)
  | |- tk (set_method ?a ?v) = _ => change (tk (set_method a v)) with (tk a)
  | |- tk (set_nice_match ?a ?v) = _ => change (tk (set_nice_match a v)) with (tk a)
  | |- tk (set_opt_len ?a ?v) = _ => change (tk (set_opt_len a v)) with (tk a)
  | |- tk (set_pending ?a ?v) = _ => change (tk (set_pending a v)) with (tk a)
  | |- tk (set_pending_buf ?a ?v) = _ => change (tk (set_pending_buf a v)) with (tk a)
  | |- tk (set_pending_buf_size ?a ?v) = _ => change (tk (set_pending_buf_size a v)) with (tk a)
  | |- tk (set_pending_out ?a ?v) = _ => change (tk (set_pending_out a v)) with (tk a)
  | |- tk (set_prev ?a ?v) = _ => change (tk (set_prev a v)) with (tk a)
  | |- tk (set_prev_length ?a ?v) = _ => change (tk (set_prev_length a v)) with (tk a)
  | |- tk (set_prev_match ?a ?v) = _ => change (tk (set_prev_match a v)) with (tk a)
  | |- tk (set_static_len ?a ?v) = _ => change (tk (set_static_len a v)) with (tk a)
  | |- tk (set_status ?a ?v) = _ => change (tk (set_status a v)) with (tk a)
  | |- tk (set_strategy ?a ?v) = _ => change (tk (set_strategy a v)) with (tk a)
  | |- tk (set_strm ?a ?v) = _ => rewrite (tk_set_strm a v) by tkz_tac
  | |- tk (set_strstart ?a ?v) = _ => change (tk (set_strstart a v)) with (tk a)
  | |- tk (set_sym_end ?a ?v) = _ => change (tk (set_sym_end a v)) with (tk a)
  | |- tk (set_sym_next ?a ?v) = _ => change (tk (set_sym_next a v)) with (tk a)
  | |- tk (set_w_bits ?a ?v) = _ => change (tk (set_w_bits a v)) with (tk a)
  | |- tk (set_w_mask ?a ?v) = _ => change (tk (set_w_mask a v)) with (tk a)
  | |- tk (set_window ?a ?v) = _ => change (tk (set_window a v)) with (tk a)
  | |- tk (set_window_size ?a ?v) = _ => change (tk (set_window_size a v)) with (tk a)
  | |- tk (set_wrap ?a ?v) = _ => change (tk (set_wrap a v)) with (tk a)
  | |- tk (put_byte ?a ?v) = _ => change (tk (put_byte a v)) with (tk a)
  | |- tk (putShortMSB ?a ?v) = _ => change (tk (putShortMSB a v)) with (tk a)
  | |- tk (set_tree_fc ?a ?v ?w) = _ => change (tk (set_tree_fc a v w)) with (tk a)
  | |- tk (set_tree_dl ?a ?v ?w) = _ => change (tk (set_tree_dl a v w)) with (tk a)
  | |- tk (set_max_code ?a ?v ?w) = _ => change (tk (set_max_code a v w)) with (tk a)
  | |- tk (sym_buf_set ?a ?v ?w) = _ => change (tk (sym_buf_set a v w)) with (tk a)
  | |- tk (set_Freq ?a ?v ?w ?x) = _ => change (tk (set_Freq a v w x)) with (tk a)
  | |- tk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_flush_block a x0 x1 x2))
  | |- tk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_stored_block a x0 x1 x2))
  | |- tk (tr_align ?a ) = _ => apply (eq_trans (tk_tr_align a ))
  | |- tk (flush_pending ?a ) = _ => apply (eq_trans (tk_flush_pending a ))
  | |- tk (bi_flush ?a ) = _ => apply (eq_trans (tk_bi_flush a ))
  | |- tk (clear_hash ?a ) = _ => apply (eq_trans (tk_clear_hash a ))
  | |- tk (slide_hash ?a ) = _ => apply (eq_trans (tk_slide_hash a ))
  | |- tk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (tk_tr_tally_lit a x0))
  | |- tk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_tr_tally_dist a x0 x1))
  | |- tk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (tk_insert_string a x0))
  | |- tk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_read_buf a x0 x1))
  | |- tk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (tk_fill_window_insert fu a x0))
  | |- tk (match ?t with pair _ _ => _ end) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (fst (match ?t with pair _ _ => _ end)) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (if ?c then _ else _) = _ => destruct c
  | |- tk (fst (if ?c then _ else _)) = _ => destruct c
  | |- tk ?y = tk _ => is_var y; assumption
  end.
Ltac tkgoB := repeat tkgoB1.

Lemma tk_fill_window_body : forall s wsize, tk (fst (fill_window_body s wsize)) = tk s.
Proof. intros. cbv beta delta [fill_window_body]. tkgoB. Qed.
Lemma tk_fill_window_loop : forall f s wsize, tk (fill_window_loop f s wsize) = tk s.
Proof.
  induction f as [|f IH]; intros s wsize; [reflexivity|]. cbn [fill_window_loop].
  pose proof (tk_fill_window_body s wsize) as X. destruct (fill_window_body s wsize) as [s1 b]. cbn [fst] in X.
  destruct b; [exact X|]. destruct (_ && _); [rewrite IH|]; exact X.
Qed.
Lemma tk_fill_window_high : forall s, tk (fill_window_high s) = tk s.
Proof. intros. cbv beta delta [fill_window_high]. tkgoB. Qed.
Lemma tk_fill_window : forall s, tk (fill_window s) = tk s.
Proof. intros. cbv beta delta [fill_window]. cbv zeta. rewrite tk_fill_window_high. apply tk_fill_window_loop. Qed.
Lemma tk_longest_match_body : forall s a b c d e f g,
  tk (fst (fst (fst (fst (fst (fst (longest_match_body s a b c d e f g))))))) = tk s.
Proof.
  intros. cbv beta delta [longest_match_body]. cbv zeta.
  repeat (first [ reflexivity | match goal with |- context [if ?c then _ else _] => destruct c end ]; cbn [fst snd]).
Qed.
Lemma tk_longest_match_loop : forall fuel s a b c d e f g, tk (fst (longest_match_loop fuel s a b c d e f g)) = tk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [longest_match_loop].
  pose proof (tk_longest_match_body s a b c d e f g) as X.
  destruct (longest_match_body s a b c d e f g) as [[[[[[s1 x1] x2] x3] x4] x5] cont]. cbn [fst] in X.
  destruct cont; [rewrite IH|]; exact X.
Qed.
Lemma tk_longest_match : forall s cur, tk (fst (longest_match s cur)) = tk s.
Proof.
  intros. cbv beta delta [longest_match]. cbv zeta.
  match goal with |- context [longest_match_loop ?n s cur ?a ?b ?c ?d ?e ?f] =>
    pose proof (tk_longest_match_loop n s cur a b c d e f) as X; destruct (longest_match_loop n s cur a b c d e f) as [s1 bl] end.
  cbn [fst] in X. destruct (_ <=? _); exact X.
Qed.
Lemma tk_flush_block_only : forall s last, tk (flush_block_only s last) = tk s.
Proof. intros. cbv beta delta [flush_block_only]. tkgoB. Qed.

Ltac tkgoC1 :=
  lazymatch goal with
  | |- tk ?x = tk ?x => reflexivity
  | |- tk (let x := ?t in @?E x) = tk ?s0 =>
      first [ is_var t; change (tk (E t) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (E t) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (let x := ?t in @?E x)) = tk ?s0 =>
      first [ is_var t; change (tk (fst (E t)) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (fst (E t)) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (?a, ?b)) = _ => change (tk (fst (a, b))) with (tk a)
  | |- tk (set_bi_buf ?a ?v) = _ => change (tk (set_bi_buf a v)) with (tk a)
  | |- tk (set_bi_valid ?a ?v) = _ => change (tk (set_bi_valid a v)) with (tk a)
  | |- tk (set_bl_count ?a ?v) = _ => change (tk (set_bl_count a v)) with (tk a)
  | |- tk (set_bl_max_code ?a ?v) = _ => change (tk (set_bl_max_code a v)) with (tk a)
  | |- tk (set_bl_tree_dl ?a ?v) = _ => change (tk (set_bl_tree_dl a v)) with (tk a)
  | |- tk (set_bl_tree_fc ?a ?v) = _ => change (tk (set_bl_tree_fc a v)) with (tk a)
  | |- tk (set_block_start ?a ?v) = _ => change (tk (set_block_start a v)) with (tk a)
  | |- tk (set_d_max_code ?a ?v) = _ => change (tk (set_d_max_code a v)) with (tk a)
  | |- tk (set_depth ?a ?v) = _ => change (tk (set_depth a v)) with (tk a)
  | |- tk (set_dyn_dtree_dl ?a ?v) = _ => change (tk (set_dyn_dtree_dl a v)) with (tk a)
  | |- tk (set_dyn_dtree_fc ?a ?v) = _ => change (tk (set_dyn_dtree_fc a v)) with (tk a)
  | |- tk (set_dyn_ltree_dl ?a ?v) = _ => change (tk (set_dyn_ltree_dl a v)) with (tk a)
  | |- tk (set_dyn_ltree_fc ?a ?v) = _ => change (tk (set_dyn_ltree_fc a v)) with (tk a)
  | |- tk (set_good_match ?a ?v) = _ => change (tk (set_good_match a v)) with (tk a)
  | |- tk (set_gzhead ?a ?v) = _ => change (tk (set_gzhead a v)) with (tk a)
  | |- tk (set_gzindex ?a ?v) = _ => change (tk (set_gzindex a v)) with (tk a)
  | |- tk (set_hash_bits ?a ?v) = _ => change (tk (set_hash_bits a v)) with (tk a)
  | |- tk (set_hash_mask ?a ?v) = _ => change (tk (set_hash_mask a v)) with (tk a)
  | |- tk (set_hash_shift ?a ?v) = _ => change (tk (set_hash_shift a v)) with (tk a)
  | |- tk (set_head ?a ?v) = _ => change (tk (set_head a v)) with (tk a)
  | |- tk (set_heap ?a ?v) = _ => change (tk (set_heap a v)) with (tk a)
  | |- tk (set_heap_len ?a ?v) = _ => change (tk (set_heap_len a v)) with (tk a)
  | |- tk (set_heap_max ?a ?v) = _ => change (tk (set_heap_max a v)) with (tk a)
  | |- tk (set_high_water ?a ?v) = _ => change (tk (set_high_water a v)) with (tk a)
  | |- tk (set_ins_h ?a ?v) = _ => change (tk (set_ins_h a v)) with (tk a)
  | |- tk (set_insert ?a ?v) = _ => change (tk (set_insert a v)) with (tk a)
  | |- tk (set_l_max_code ?a ?v) = _ => change (tk (set_l_max_code a v)) with (tk a)
  | |- tk (set_last_flush ?a ?v) = _ => change (tk (set_last_flush a v)) with (tk a)
  | |- tk (set_level ?a ?v) = _ => change (tk (set_level a v)) with (tk a)
  | |- tk (set_lookahead ?a ?v) = _ => change (tk (set_lookahead a v)) with (tk a)
  | |- tk (set_match_available ?a ?v) = _ => change (tk (set_match_available a v)) with (tk a)
  | |- tk (set_match_length ?a ?v) = _ => change (tk (set_match_length a v)) with (tk a)
  | |- tk (set_match_start ?a ?v) = _ => change (tk (set_match_start a v)) with (tk a)
  | |- tk (set_matches ?a ?v) = _ => change (tk (set_matches a v)) with (tk a)
  | |- tk (set_max_chain_length ?a ?v) = _ => change (tk (set_max_chain_length a v)) with (tk a)
  | |- tk (set_max_lazy_match ?a ?v) = _ => change (tk (set_max_lazy_match a v)) with (tk a)
  | |- tk (set_method ?a ?v) = _ => change (tk (set_method a v)) with (tk a)
  | |- tk (set_nice_match ?a ?v) = _ => change (tk (set_nice_match a v)) with (tk a)
  | |- tk (set_opt_len ?a ?v) = _ => change (tk (set_opt_len a v)) with (tk a)
  | |- tk (set_pending ?a ?v) = _ => change (tk (set_pending a v)) with (tk a)
  | |- tk (set_pending_buf ?a ?v) = _ => change (tk (set_pending_buf a v)) with (tk a)
  | |- tk (set_pending_buf_size ?a ?v) = _ => change (tk (set_pending_buf_size a v)) with (tk a)
  | |- tk (set_pending_out ?a ?v) = _ => change (tk (set_pending_out a v)) with (tk a)
  | |- tk (set_prev ?a ?v) = _ => change (tk (set_prev a v)) with (tk a)
  | |- tk (set_prev_length ?a ?v) = _ => change (tk (set_prev_length a v)) with (tk a)
  | |- tk (set_prev_match ?a ?v) = _ => change (tk (set_prev_match a v)) with (tk a)
  | |- tk (set_static_len ?a ?v) = _ => change (tk (set_static_len a v)) with (tk a)
  | |- tk (set_status ?a ?v) = _ => change (tk (set_status a v)) with (tk a)
  | |- tk (set_strategy ?a ?v) = _ => change (tk (set_strategy a v)) with (tk a)
  | |- tk (set_strm ?a ?v) = _ => rewrite (tk_set_strm a v) by tkz_tac
  | |- tk (set_strstart ?a ?v) = _ => change (tk (set_strstart a v)) with (tk a)
  | |- tk (set_sym_end ?a ?v) = _ => change (tk (set_sym_end a v)) with (tk a)
  | |- tk (set_sym_next ?a ?v) = _ => change (tk (set_sym_next a v)) with (tk a)
  | |- tk (set_w_bits ?a ?v) = _ => change (tk (set_w_bits a v)) with (tk a)
  | |- tk (set_w_mask ?a ?v) = _ => change (tk (set_w_mask a v)) with (tk a)
  | |- tk (set_window ?a ?v) = _ => change (tk (set_window a v)) with (tk a)
  | |- tk (set_window_size ?a ?v) = _ => change (tk (set_window_size a v)) with (tk a)
  | |- tk (set_wrap ?a ?v) = _ => change (tk (set_wrap a v)) with (tk a)
  | |- tk (put_byte ?a ?v) = _ => change (tk (put_byte a v)) with (tk a)
  | |- tk (putShortMSB ?a ?v) = _ => change (tk (putShortMSB a v)) with (tk a)
  | |- tk (set_tree_fc ?a ?v ?w) = _ => change (tk (set_tree_fc a v w)) with (tk a)
  | |- tk (set_tree_dl ?a ?v ?w) = _ => change (tk (set_tree_dl a v w)) with (tk a)
  | |- tk (set_max_code ?a ?v ?w) = _ => change (tk (set_max_code a v w)) with (tk a)
  | |- tk (sym_buf_set ?a ?v ?w) = _ => change (tk (sym_buf_set a v w)) with (tk a)
  | |- tk (set_Freq ?a ?v ?w ?x) = _ => change (tk (set_Freq a v w x)) with (tk a)
  | |- tk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_flush_block a x0 x1 x2))
  | |- tk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_stored_block a x0 x1 x2))
  | |- tk (tr_align ?a ) = _ => apply (eq_trans (tk_tr_align a ))
  | |- tk (flush_pending ?a ) = _ => apply (eq_trans (tk_flush_pending a ))
  | |- tk (bi_flush ?a ) = _ => apply (eq_trans (tk_bi_flush a ))
  | |- tk (clear_hash ?a ) = _ => apply (eq_trans (tk_clear_hash a ))
  | |- tk (slide_hash ?a ) = _ => apply (eq_trans (tk_slide_hash a ))
  | |- tk (fill_window ?a ) = _ => apply (eq_trans (tk_fill_window a ))
  | |- tk (flush_block_only ?a ?x0) = _ => apply (eq_trans (tk_flush_block_only a x0))
  | |- tk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (tk_tr_tally_lit a x0))
  | |- tk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_tr_tally_dist a x0 x1))
  | |- tk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (tk_insert_string a x0))
  | |- tk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_read_buf a x0 x1))
  | |- tk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (tk_longest_match a x0))
  | |- tk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (tk_fill_window_insert fu a x0))
  | |- tk (match ?t with pair _ _ => _ end) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (fst (match ?t with pair _ _ => _ end)) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (if ?c then _ else _) = _ => destruct c
  | |- tk (fst (if ?c then _ else _)) = _ => destruct c
  | |- tk ?y = tk _ => is_var y; assumption
  end.
Ltac tkgoC := repeat tkgoC1.

Lemma tk_flush_block : forall s last, tk (fst (flush_block s last)) = tk s.
Proof. intros. cbv beta delta [flush_block]. tkgoC. Qed.
Lemma tk_deflate_tail : forall s flush, tk (fst (deflate_tail s flush)) = tk s.
Proof. intros. cbv beta delta [deflate_tail]. tkgoC; apply (eq_trans (tk_flush_block _ _)); tkgoC. Qed.

Ltac tkgoD1 :=
  lazymatch goal with
  | |- tk ?x = tk ?x => reflexivity
  | |- tk (let x := ?t in @?E x) = tk ?s0 =>
      first [ is_var t; change (tk (E t) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (E t) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (let x := ?t in @?E x)) = tk ?s0 =>
      first [ is_var t; change (tk (fst (E t)) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (fst (E t)) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (?a, ?b)) = _ => change (tk (fst (a, b))) with (tk a)
  | |- tk (set_bi_buf ?a ?v) = _ => change (tk (set_bi_buf a v)) with (tk a)
  | |- tk (set_bi_valid ?a ?v) = _ => change (tk (set_bi_valid a v)) with (tk a)
  | |- tk (set_bl_count ?a ?v) = _ => change (tk (set_bl_count a v)) with (tk a)
  | |- tk (set_bl_max_code ?a ?v) = _ => change (tk (set_bl_max_code a v)) with (tk a)
  | |- tk (set_bl_tree_dl ?a ?v) = _ => change (tk (set_bl_tree_dl a v)) with (tk a)
  | |- tk (set_bl_tree_fc ?a ?v) = _ => change (tk (set_bl_tree_fc a v)) with (tk a)
  | |- tk (set_block_start ?a ?v) = _ => change (tk (set_block_start a v)) with (tk a)
  | |- tk (set_d_max_code ?a ?v) = _ => change (tk (set_d_max_code a v)) with (tk a)
  | |- tk (set_depth ?a ?v) = _ => change (tk (set_depth a v)) with (tk a)
  | |- tk (set_dyn_dtree_dl ?a ?v) = _ => change (tk (set_dyn_dtree_dl a v)) with (tk a)
  | |- tk (set_dyn_dtree_fc ?a ?v) = _ => change (tk (set_dyn_dtree_fc a v)) with (tk a)
  | |- tk (set_dyn_ltree_dl ?a ?v) = _ => change (tk (set_dyn_ltree_dl a v)) with (tk a)
  | |- tk (set_dyn_ltree_fc ?a ?v) = _ => change (tk (set_dyn_ltree_fc a v)) with (tk a)
  | |- tk (set_good_match ?a ?v) = _ => change (tk (set_good_match a v)) with (tk a)
  | |- tk (set_gzhead ?a ?v) = _ => change (tk (set_gzhead a v)) with (tk a)
  | |- tk (set_gzindex ?a ?v) = _ => change (tk (set_gzindex a v)) with (tk a)
  | |- tk (set_hash_bits ?a ?v) = _ => change (tk (set_hash_bits a v)) with (tk a)
  | |- tk (set_hash_mask ?a ?v) = _ => change (tk (set_hash_mask a v)) with (tk a)
  | |- tk (set_hash_shift ?a ?v) = _ => change (tk (set_hash_shift a v)) with (tk a)
  | |- tk (set_head ?a ?v) = _ => change (tk (set_head a v)) with (tk a)
  | |- tk (set_heap ?a ?v) = _ => change (tk (set_heap a v)) with (tk a)
  | |- tk (set_heap_len ?a ?v) = _ => change (tk (set_heap_len a v)) with (tk a)
  | |- tk (set_heap_max ?a ?v) = _ => change (tk (set_heap_max a v)) with (tk a)
  | |- tk (set_high_water ?a ?v) = _ => change (tk (set_high_water a v)) with (tk a)
  | |- tk (set_ins_h ?a ?v) = _ => change (tk (set_ins_h a v)) with (tk a)
  | |- tk (set_insert ?a ?v) = _ => change (tk (set_insert a v)) with (tk a)
  | |- tk (set_l_max_code ?a ?v) = _ => change (tk (set_l_max_code a v)) with (tk a)
  | |- tk (set_last_flush ?a ?v) = _ => change (tk (set_last_flush a v)) with (tk a)
  | |- tk (set_level ?a ?v) = _ => change (tk (set_level a v)) with (tk a)
  | |- tk (set_lookahead ?a ?v) = _ => change (tk (set_lookahead a v)) with (tk a)
  | |- tk (set_match_available ?a ?v) = _ => change (tk (set_match_available a v)) with (tk a)
  | |- tk (set_match_length ?a ?v) = _ => change (tk (set_match_length a v)) with (tk a)
  | |- tk (set_match_start ?a ?v) = _ => change (tk (set_match_start a v)) with (tk a)
  | |- tk (set_matches ?a ?v) = _ => change (tk (set_matches a v)) with (tk a)
  | |- tk (set_max_chain_length ?a ?v) = _ => change (tk (set_max_chain_length a v)) with (tk a)
  | |- tk (set_max_lazy_match ?a ?v) = _ => change (tk (set_max_lazy_match a v)) with (tk a)
  | |- tk (set_method ?a ?v) = _ => change (tk (set_method a v)) with (tk a)
  | |- tk (set_nice_match ?a ?v) = _ => change (tk (set_nice_match a v)) with (tk a)
  | |- tk (set_opt_len ?a ?v) = _ => change (tk (set_opt_len a v)) with (tk a)
  | |- tk (set_pending ?a ?v) = _ => change (tk (set_pending a v)) with (tk a)
  | |- tk (set_pending_buf ?a ?v) = _ => change (tk (set_pending_buf a v)) with (tk a)
  | |- tk (set_pending_buf_size ?a ?v) = _ => change (tk (set_pending_buf_size a v)) with (tk a)
  | |- tk (set_pending_out ?a ?v) = _ => change (tk (set_pending_out a v)) with (tk a)
  | |- tk (set_prev ?a ?v) = _ => change (tk (set_prev a v)) with (tk a)
  | |- tk (set_prev_length ?a ?v) = _ => change (tk (set_prev_length a v)) with (tk a)
  | |- tk (set_prev_match ?a ?v) = _ => change (tk (set_prev_match a v)) with (tk a)
  | |- tk (set_static_len ?a ?v) = _ => change (tk (set_static_len a v)) with (tk a)
  | |- tk (set_status ?a ?v) = _ => change (tk (set_status a v)) with (tk a)
  | |- tk (set_strategy ?a ?v) = _ => change (tk (set_strategy a v)) with (tk a)
  | |- tk (set_strm ?a ?v) = _ => rewrite (tk_set_strm a v) by tkz_tac
  | |- tk (set_strstart ?a ?v) = _ => change (tk (set_strstart a v)) with (tk a)
  | |- tk (set_sym_end ?a ?v) = _ => change (tk (set_sym_end a v)) with (tk a)
  | |- tk (set_sym_next ?a ?v) = _ => change (tk (set_sym_next a v)) with (tk a)
  | |- tk (set_w_bits ?a ?v) = _ => change (tk (set_w_bits a v)) with (tk a)
  | |- tk (set_w_mask ?a ?v) = _ => change (tk (set_w_mask a v)) with (tk a)
  | |- tk (set_window ?a ?v) = _ => change (tk (set_window a v)) with (tk a)
  | |- tk (set_window_size ?a ?v) = _ => change (tk (set_window_size a v)) with (tk a)
  | |- tk (set_wrap ?a ?v) = _ => change (tk (set_wrap a v)) with (tk a)
  | |- tk (put_byte ?a ?v) = _ => change (tk (put_byte a v)) with (tk a)
  | |- tk (putShortMSB ?a ?v) = _ => change (tk (putShortMSB a v)) with (tk a)
  | |- tk (set_tree_fc ?a ?v ?w) = _ => change (tk (set_tree_fc a v w)) with (tk a)
  | |- tk (set_tree_dl ?a ?v ?w) = _ => change (tk (set_tree_dl a v w)) with (tk a)
  | |- tk (set_max_code ?a ?v ?w) = _ => change (tk (set_max_code a v w)) with (tk a)
  | |- tk (sym_buf_set ?a ?v ?w) = _ => change (tk (sym_buf_set a v w)) with (tk a)
  | |- tk (set_Freq ?a ?v ?w ?x) = _ => change (tk (set_Freq a v w x)) with (tk a)
  | |- tk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_flush_block a x0 x1 x2))
  | |- tk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_stored_block a x0 x1 x2))
  | |- tk (tr_align ?a ) = _ => apply (eq_trans (tk_tr_align a ))
  | |- tk (flush_pending ?a ) = _ => apply (eq_trans (tk_flush_pending a ))
  | |- tk (bi_flush ?a ) = _ => apply (eq_trans (tk_bi_flush a ))
  | |- tk (clear_hash ?a ) = _ => apply (eq_trans (tk_clear_hash a ))
  | |- tk (slide_hash ?a ) = _ => apply (eq_trans (tk_slide_hash a ))
  | |- tk (fill_window ?a ) = _ => apply (eq_trans (tk_fill_window a ))
  | |- tk (flush_block_only ?a ?x0) = _ => apply (eq_trans (tk_flush_block_only a x0))
  | |- tk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (tk_tr_tally_lit a x0))
  | |- tk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_tr_tally_dist a x0 x1))
  | |- tk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (tk_insert_string a x0))
  | |- tk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_read_buf a x0 x1))
  | |- tk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (tk_longest_match a x0))
  | |- tk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (tk_fill_window_insert fu a x0))
  | |- tk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (tk_flush_block a x0))
  | |- tk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (tk_deflate_tail a x0))
  | |- tk (match ?t with pair _ _ => _ end) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (fst (match ?t with pair _ _ => _ end)) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (if ?c then _ else _) = _ => destruct c
  | |- tk (fst (if ?c then _ else _)) = _ => destruct c
  | |- tk ?y = tk _ => is_var y; assumption
  end.
Ltac tkgoD := repeat tkgoD1.


Lemma tk_deflate_stored_body : forall s flush mb, tk (fst (fst (deflate_stored_body s flush mb))) = tk s.
Proof.
  intros. cbv beta delta [deflate_stored_body].
  repeat (tkgoD1
          || lazymatch goal with
             | |- tk (fst (fst (?a, ?b, ?c))) = _ => change (tk (fst (fst (a, b, c)))) with (tk a)
             | |- tk (fst (fst (if ?c then _ else _))) = _ => destruct c
             | |- tk (fst (fst (let x := ?t in @?E x))) = tk ?s0 =>
                 first [ is_var t; change (tk (fst (fst (E t))) = tk s0); cbv beta
                       | lazymatch type of t with
                         | cstrm => change (tk (fst (fst (E t))) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
                         | _ => generalize t; let y := fresh "v" in intros y
                         end ]
             | |- tk (fst (fst (match ?t with pair _ _ => _ end))) = tk ?s0 =>
                 let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
             end).
Qed.
Lemma tk_deflate_stored_loop : forall fuel s flush mb, tk (fst (deflate_stored_loop fuel s flush mb)) = tk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_stored_loop].
  pose proof (tk_deflate_stored_body s flush mb) as X. destruct (deflate_stored_body s flush mb) as [[s1 last] broke]. cbn [fst] in X.
  destruct broke; [exact X|]. destruct (last =? 0); [rewrite IH|]; exact X.
Qed.
Lemma tk_deflate_stored_used : forall s used, tk (deflate_stored_used s used) = tk s.
Proof. intros. cbv beta delta [deflate_stored_used]. tkgoD. Qed.
Lemma tk_deflate_stored_fin : forall s flush, tk (fst (deflate_stored_fin s flush)) = tk s.
Proof. intros. cbv beta delta [deflate_stored_fin]. tkgoD. Qed.
Lemma tk_deflate_stored_slide : forall s hv, tk (fst (deflate_stored_slide s hv)) = tk s.
Proof. intros. cbv beta delta [deflate_stored_slide]. tkgoD. Qed.

Ltac tkgoE1 :=
  lazymatch goal with
  | |- tk ?x = tk ?x => reflexivity
  | |- tk (let x := ?t in @?E x) = tk ?s0 =>
      first [ is_var t; change (tk (E t) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (E t) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (let x := ?t in @?E x)) = tk ?s0 =>
      first [ is_var t; change (tk (fst (E t)) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (fst (E t)) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (?a, ?b)) = _ => change (tk (fst (a, b))) with (tk a)
  | |- tk (set_bi_buf ?a ?v) = _ => change (tk (set_bi_buf a v)) with (tk a)
  | |- tk (set_bi_valid ?a ?v) = _ => change (tk (set_bi_valid a v)) with (tk a)
  | |- tk (set_bl_count ?a ?v) = _ => change (tk (set_bl_count a v)) with (tk a)
  | |- tk (set_bl_max_code ?a ?v) = _ => change (tk (set_bl_max_code a v)) with (tk a)
  | |- tk (set_bl_tree_dl ?a ?v) = _ => change (tk (set_bl_tree_dl a v)) with (tk a)
  | |- tk (set_bl_tree_fc ?a ?v) = _ => change (tk (set_bl_tree_fc a v)) with (tk a)
  | |- tk (set_block_start ?a ?v) = _ => change (tk (set_block_start a v)) with (tk a)
  | |- tk (set_d_max_code ?a ?v) = _ => change (tk (set_d_max_code a v)) with (tk a)
  | |- tk (set_depth ?a ?v) = _ => change (tk (set_depth a v)) with (tk a)
  | |- tk (set_dyn_dtree_dl ?a ?v) = _ => change (tk (set_dyn_dtree_dl a v)) with (tk a)
  | |- tk (set_dyn_dtree_fc ?a ?v) = _ => change (tk (set_dyn_dtree_fc a v)) with (tk a)
  | |- tk (set_dyn_ltree_dl ?a ?v) = _ => change (tk (set_dyn_ltree_dl a v)) with (tk a)
  | |- tk (set_dyn_ltree_fc ?a ?v) = _ => change (tk (set_dyn_ltree_fc a v)) with (tk a)
  | |- tk (set_good_match ?a ?v) = _ => change (tk (set_good_match a v)) with (tk a)
  | |- tk (set_gzhead ?a ?v) = _ => change (tk (set_gzhead a v)) with (tk a)
  | |- tk (set_gzindex ?a ?v) = _ => change (tk (set_gzindex a v)) with (tk a)
  | |- tk (set_hash_bits ?a ?v) = _ => change (tk (set_hash_bits a v)) with (tk a)
  | |- tk (set_hash_mask ?a ?v) = _ => change (tk (set_hash_mask a v)) with (tk a)
  | |- tk (set_hash_shift ?a ?v) = _ => change (tk (set_hash_shift a v)) with (tk a)
  | |- tk (set_head ?a ?v) = _ => change (tk (set_head a v)) with (tk a)
  | |- tk (set_heap ?a ?v) = _ => change (tk (set_heap a v)) with (tk a)
  | |- tk (set_heap_len ?a ?v) = _ => change (tk (set_heap_len a v)) with (tk a)
  | |- tk (set_heap_max ?a ?v) = _ => change (tk (set_heap_max a v)) with (tk a)
  | |- tk (set_high_water ?a ?v) = _ => change (tk (set_high_water a v)) with (tk a)
  | |- tk (set_ins_h ?a ?v) = _ => change (tk (set_ins_h a v)) with (tk a)
  | |- tk (set_insert ?a ?v) = _ => change (tk (set_insert a v)) with (tk a)
  | |- tk (set_l_max_code ?a ?v) = _ => change (tk (set_l_max_code a v)) with (tk a)
  | |- tk (set_last_flush ?a ?v) = _ => change (tk (set_last_flush a v)) with (tk a)
  | |- tk (set_level ?a ?v) = _ => change (tk (set_level a v)) with (tk a)
  | |- tk (set_lookahead ?a ?v) = _ => change (tk (set_lookahead a v)) with (tk a)
  | |- tk (set_match_available ?a ?v) = _ => change (tk (set_match_available a v)) with (tk a)
  | |- tk (set_match_length ?a ?v) = _ => change (tk (set_match_length a v)) with (tk a)
  | |- tk (set_match_start ?a ?v) = _ => change (tk (set_match_start a v)) with (tk a)
  | |- tk (set_matches ?a ?v) = _ => change (tk (set_matches a v)) with (tk a)
  | |- tk (set_max_chain_length ?a ?v) = _ => change (tk (set_max_chain_length a v)) with (tk a)
  | |- tk (set_max_lazy_match ?a ?v) = _ => change (tk (set_max_lazy_match a v)) with (tk a)
  | |- tk (set_method ?a ?v) = _ => change (tk (set_method a v)) with (tk a)
  | |- tk (set_nice_match ?a ?v) = _ => change (tk (set_nice_match a v)) with (tk a)
  | |- tk (set_opt_len ?a ?v) = _ => change (tk (set_opt_len a v)) with (tk a)
  | |- tk (set_pending ?a ?v) = _ => change (tk (set_pending a v)) with (tk a)
  | |- tk (set_pending_buf ?a ?v) = _ => change (tk (set_pending_buf a v)) with (tk a)
  | |- tk (set_pending_buf_size ?a ?v) = _ => change (tk (set_pending_buf_size a v)) with (tk a)
  | |- tk (set_pending_out ?a ?v) = _ => change (tk (set_pending_out a v)) with (tk a)
  | |- tk (set_prev ?a ?v) = _ => change (tk (set_prev a v)) with (tk a)
  | |- tk (set_prev_length ?a ?v) = _ => change (tk (set_prev_length a v)) with (tk a)
  | |- tk (set_prev_match ?a ?v) = _ => change (tk (set_prev_match a v)) with (tk a)
  | |- tk (set_static_len ?a ?v) = _ => change (tk (set_static_len a v)) with (tk a)
  | |- tk (set_status ?a ?v) = _ => change (tk (set_status a v)) with (tk a)
  | |- tk (set_strategy ?a ?v) = _ => change (tk (set_strategy a v)) with (tk a)
  | |- tk (set_strm ?a ?v) = _ => rewrite (tk_set_strm a v) by tkz_tac
  | |- tk (set_strstart ?a ?v) = _ => change (tk (set_strstart a v)) with (tk a)
  | |- tk (set_sym_end ?a ?v) = _ => change (tk (set_sym_end a v)) with (tk a)
  | |- tk (set_sym_next ?a ?v) = _ => change (tk (set_sym_next a v)) with (tk a)
  | |- tk (set_w_bits ?a ?v) = _ => change (tk (set_w_bits a v)) with (tk a)
  | |- tk (set_w_mask ?a ?v) = _ => change (tk (set_w_mask a v)) with (tk a)
  | |- tk (set_window ?a ?v) = _ => change (tk (set_window a v)) with (tk a)
  | |- tk (set_window_size ?a ?v) = _ => change (tk (set_window_size a v)) with (tk a)
  | |- tk (set_wrap ?a ?v) = _ => change (tk (set_wrap a v)) with (tk a)
  | |- tk (put_byte ?a ?v) = _ => change (tk (put_byte a v)) with (tk a)
  | |- tk (putShortMSB ?a ?v) = _ => change (tk (putShortMSB a v)) with (tk a)
  | |- tk (set_tree_fc ?a ?v ?w) = _ => change (tk (set_tree_fc a v w)) with (tk a)
  | |- tk (set_tree_dl ?a ?v ?w) = _ => change (tk (set_tree_dl a v w)) with (tk a)
  | |- tk (set_max_code ?a ?v ?w) = _ => change (tk (set_max_code a v w)) with (tk a)
  | |- tk (sym_buf_set ?a ?v ?w) = _ => change (tk (sym_buf_set a v w)) with (tk a)
  | |- tk (set_Freq ?a ?v ?w ?x) = _ => change (tk (set_Freq a v w x)) with (tk a)
  | |- tk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_flush_block a x0 x1 x2))
  | |- tk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_stored_block a x0 x1 x2))
  | |- tk (tr_align ?a ) = _ => apply (eq_trans (tk_tr_align a ))
  | |- tk (flush_pending ?a ) = _ => apply (eq_trans (tk_flush_pending a ))
  | |- tk (bi_flush ?a ) = _ => apply (eq_trans (tk_bi_flush a ))
  | |- tk (clear_hash ?a ) = _ => apply (eq_trans (tk_clear_hash a ))
  | |- tk (slide_hash ?a ) = _ => apply (eq_trans (tk_slide_hash a ))
  | |- tk (fill_window ?a ) = _ => apply (eq_trans (tk_fill_window a ))
  | |- tk (flush_block_only ?a ?x0) = _ => apply (eq_trans (tk_flush_block_only a x0))
  | |- tk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (tk_tr_tally_lit a x0))
  | |- tk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_tr_tally_dist a x0 x1))
  | |- tk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (tk_insert_string a x0))
  | |- tk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_read_buf a x0 x1))
  | |- tk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (tk_longest_match a x0))
  | |- tk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (tk_fill_window_insert fu a x0))
  | |- tk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (tk_flush_block a x0))
  | |- tk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (tk_deflate_tail a x0))
  | |- tk (deflate_stored_used ?a ?x0) = _ => apply (eq_trans (tk_deflate_stored_used a x0))
  | |- tk (fst (deflate_stored_fin ?a ?x0)) = _ => apply (eq_trans (tk_deflate_stored_fin a x0))
  | |- tk (fst (deflate_stored_slide ?a ?x0)) = _ => apply (eq_trans (tk_deflate_stored_slide a x0))
  | |- tk (fst (deflate_stored_loop ?fu ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_deflate_stored_loop fu a x0 x1))
  | |- tk (match ?t with pair _ _ => _ end) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (fst (match ?t with pair _ _ => _ end)) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (if ?c then _ else _) = _ => destruct c
  | |- tk (fst (if ?c then _ else _)) = _ => destruct c
  | |- tk ?y = tk _ => is_var y; assumption
  end.
Ltac tkgoE := repeat tkgoE1.

Lemma tk_deflate_stored_mid : forall s flush, tk (fst (deflate_stored_mid s flush)) = tk s.
Proof. intros. cbv beta delta [deflate_stored_mid]. tkgoE. Qed.
Lemma tk_deflate_stored : forall s flush, tk (fst (deflate_stored s flush)) = tk s.
Proof.
  intros. cbv beta delta [deflate_stored]. tkgoE; apply (eq_trans (tk_deflate_stored_mid _ _)); tkgoE.
Qed.

Lemma tk_deflate_fast_insert : forall f s, tk (deflate_fast_insert f s) = tk s.
Proof.
  induction f as [|f IH]; intros s; [reflexivity|]. cbn [deflate_fast_insert].
  tkgoE; apply (eq_trans (IH _)); tkgoE.
Qed.
Lemma tk_deflate_slow_insert : forall f s mi, tk (deflate_slow_insert f s mi) = tk s.
Proof.
  induction f as [|f IH]; intros s mi; [reflexivity|]. cbn [deflate_slow_insert].
  tkgoE; apply (eq_trans (IH _ _)); tkgoE.
Qed.

Ltac tkgoF1 :=
  lazymatch goal with
  | |- tk ?x = tk ?x => reflexivity
  | |- tk (let x := ?t in @?E x) = tk ?s0 =>
      first [ is_var t; change (tk (E t) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (E t) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (let x := ?t in @?E x)) = tk ?s0 =>
      first [ is_var t; change (tk (fst (E t)) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (fst (E t)) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (?a, ?b)) = _ => change (tk (fst (a, b))) with (tk a)
  | |- tk (set_bi_buf ?a ?v) = _ => change (tk (set_bi_buf a v)) with (tk a)
  | |- tk (set_bi_valid ?a ?v) = _ => change (tk (set_bi_valid a v)) with (tk a)
  | |- tk (set_bl_count ?a ?v) = _ => change (tk (set_bl_count a v)) with (tk a)
  | |- tk (set_bl_max_code ?a ?v) = _ => change (tk (set_bl_max_code a v)) with (tk a)
  | |- tk (set_bl_tree_dl ?a ?v) = _ => change (tk (set_bl_tree_dl a v)) with (tk a)
  | |- tk (set_bl_tree_fc ?a ?v) = _ => change (tk (set_bl_tree_fc a v)) with (tk a)
  | |- tk (set_block_start ?a ?v) = _ => change (tk (set_block_start a v)) with (tk a)
  | |- tk (set_d_max_code ?a ?v) = _ => change (tk (set_d_max_code a v)) with (tk a)
  | |- tk (set_depth ?a ?v) = _ => change (tk (set_depth a v)) with (tk a)
  | |- tk (set_dyn_dtree_dl ?a ?v) = _ => change (tk (set_dyn_dtree_dl a v)) with (tk a)
  | |- tk (set_dyn_dtree_fc ?a ?v) = _ => change (tk (set_dyn_dtree_fc a v)) with (tk a)
  | |- tk (set_dyn_ltree_dl ?a ?v) = _ => change (tk (set_dyn_ltree_dl a v)) with (tk a)
  | |- tk (set_dyn_ltree_fc ?a ?v) = _ => change (tk (set_dyn_ltree_fc a v)) with (tk a)
  | |- tk (set_good_match ?a ?v) = _ => change (tk (set_good_match a v)) with (tk a)
  | |- tk (set_gzhead ?a ?v) = _ => change (tk (set_gzhead a v)) with (tk a)
  | |- tk (set_gzindex ?a ?v) = _ => change (tk (set_gzindex a v)) with (tk a)
  | |- tk (set_hash_bits ?a ?v) = _ => change (tk (set_hash_bits a v)) with (tk a)
  | |- tk (set_hash_mask ?a ?v) = _ => change (tk (set_hash_mask a v)) with (tk a)
  | |- tk (set_hash_shift ?a ?v) = _ => change (tk (set_hash_shift a v)) with (tk a)
  | |- tk (set_head ?a ?v) = _ => change (tk (set_head a v)) with (tk a)
  | |- tk (set_heap ?a ?v) = _ => change (tk (set_heap a v)) with (tk a)
  | |- tk (set_heap_len ?a ?v) = _ => change (tk (set_heap_len a v)) with (tk a)
  | |- tk (set_heap_max ?a ?v) = _ => change (tk (set_heap_max a v)) with (tk a)
  | |- tk (set_high_water ?a ?v) = _ => change (tk (set_high_water a v)) with (tk a)
  | |- tk (set_ins_h ?a ?v) = _ => change (tk (set_ins_h a v)) with (tk a)
  | |- tk (set_insert ?a ?v) = _ => change (tk (set_insert a v)) with (tk a)
  | |- tk (set_l_max_code ?a ?v) = _ => change (tk (set_l_max_code a v)) with (tk a)
  | |- tk (set_last_flush ?a ?v) = _ => change (tk (set_last_flush a v)) with (tk a)
  | |- tk (set_level ?a ?v) = _ => change (tk (set_level a v)) with (tk a)
  | |- tk (set_lookahead ?a ?v) = _ => change (tk (set_lookahead a v)) with (tk a)
  | |- tk (set_match_available ?a ?v) = _ => change (tk (set_match_available a v)) with (tk a)
  | |- tk (set_match_length ?a ?v) = _ => change (tk (set_match_length a v)) with (tk a)
  | |- tk (set_match_start ?a ?v) = _ => change (tk (set_match_start a v)) with (tk a)
  | |- tk (set_matches ?a ?v) = _ => change (tk (set_matches a v)) with (tk a)
  | |- tk (set_max_chain_length ?a ?v) = _ => change (tk (set_max_chain_length a v)) with (tk a)
  | |- tk (set_max_lazy_match ?a ?v) = _ => change (tk (set_max_lazy_match a v)) with (tk a)
  | |- tk (set_method ?a ?v) = _ => change (tk (set_method a v)) with (tk a)
  | |- tk (set_nice_match ?a ?v) = _ => change (tk (set_nice_match a v)) with (tk a)
  | |- tk (set_opt_len ?a ?v) = _ => change (tk (set_opt_len a v)) with (tk a)
  | |- tk (set_pending ?a ?v) = _ => change (tk (set_pending a v)) with (tk a)
  | |- tk (set_pending_buf ?a ?v) = _ => change (tk (set_pending_buf a v)) with (tk a)
  | |- tk (set_pending_buf_size ?a ?v) = _ => change (tk (set_pending_buf_size a v)) with (tk a)
  | |- tk (set_pending_out ?a ?v) = _ => change (tk (set_pending_out a v)) with (tk a)
  | |- tk (set_prev ?a ?v) = _ => change (tk (set_prev a v)) with (tk a)
  | |- tk (set_prev_length ?a ?v) = _ => change (tk (set_prev_length a v)) with (tk a)
  | |- tk (set_prev_match ?a ?v) = _ => change (tk (set_prev_match a v)) with (tk a)
  | |- tk (set_static_len ?a ?v) = _ => change (tk (set_static_len a v)) with (tk a)
  | |- tk (set_status ?a ?v) = _ => change (tk (set_status a v)) with (tk a)
  | |- tk (set_strategy ?a ?v) = _ => change (tk (set_strategy a v)) with (tk a)
  | |- tk (set_strm ?a ?v) = _ => rewrite (tk_set_strm a v) by tkz_tac
  | |- tk (set_strstart ?a ?v) = _ => change (tk (set_strstart a v)) with (tk a)
  | |- tk (set_sym_end ?a ?v) = _ => change (tk (set_sym_end a v)) with (tk a)
  | |- tk (set_sym_next ?a ?v) = _ => change (tk (set_sym_next a v)) with (tk a)
  | |- tk (set_w_bits ?a ?v) = _ => change (tk (set_w_bits a v)) with (tk a)
  | |- tk (set_w_mask ?a ?v) = _ => change (tk (set_w_mask a v)) with (tk a)
  | |- tk (set_window ?a ?v) = _ => change (tk (set_window a v)) with (tk a)
  | |- tk (set_window_size ?a ?v) = _ => change (tk (set_window_size a v)) with (tk a)
  | |- tk (set_wrap ?a ?v) = _ => change (tk (set_wrap a v)) with (tk a)
  | |- tk (put_byte ?a ?v) = _ => change (tk (put_byte a v)) with (tk a)
  | |- tk (putShortMSB ?a ?v) = _ => change (tk (putShortMSB a v)) with (tk a)
  | |- tk (set_tree_fc ?a ?v ?w) = _ => change (tk (set_tree_fc a v w)) with (tk a)
  | |- tk (set_tree_dl ?a ?v ?w) = _ => change (tk (set_tree_dl a v w)) with (tk a)
  | |- tk (set_max_code ?a ?v ?w) = _ => change (tk (set_max_code a v w)) with (tk a)
  | |- tk (sym_buf_set ?a ?v ?w) = _ => change (tk (sym_buf_set a v w)) with (tk a)
  | |- tk (set_Freq ?a ?v ?w ?x) = _ => change (tk (set_Freq a v w x)) with (tk a)
  | |- tk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_flush_block a x0 x1 x2))
  | |- tk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_stored_block a x0 x1 x2))
  | |- tk (tr_align ?a ) = _ => apply (eq_trans (tk_tr_align a ))
  | |- tk (flush_pending ?a ) = _ => apply (eq_trans (tk_flush_pending a ))
  | |- tk (bi_flush ?a ) = _ => apply (eq_trans (tk_bi_flush a ))
  | |- tk (clear_hash ?a ) = _ => apply (eq_trans (tk_clear_hash a ))
  | |- tk (slide_hash ?a ) = _ => apply (eq_trans (tk_slide_hash a ))
  | |- tk (fill_window ?a ) = _ => apply (eq_trans (tk_fill_window a ))
  | |- tk (flush_block_only ?a ?x0) = _ => apply (eq_trans (tk_flush_block_only a x0))
  | |- tk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (tk_tr_tally_lit a x0))
  | |- tk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_tr_tally_dist a x0 x1))
  | |- tk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (tk_insert_string a x0))
  | |- tk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_read_buf a x0 x1))
  | |- tk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (tk_longest_match a x0))
  | |- tk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (tk_fill_window_insert fu a x0))
  | |- tk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (tk_flush_block a x0))
  | |- tk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (tk_deflate_tail a x0))
  | |- tk (deflate_stored_used ?a ?x0) = _ => apply (eq_trans (tk_deflate_stored_used a x0))
  | |- tk (fst (deflate_stored_fin ?a ?x0)) = _ => apply (eq_trans (tk_deflate_stored_fin a x0))
  | |- tk (fst (deflate_stored_slide ?a ?x0)) = _ => apply (eq_trans (tk_deflate_stored_slide a x0))
  | |- tk (fst (deflate_stored_loop ?fu ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_deflate_stored_loop fu a x0 x1))
  | |- tk (deflate_fast_insert ?fu ?a) = _ => apply (eq_trans (tk_deflate_fast_insert fu a))
  | |- tk (deflate_slow_insert ?fu ?a ?x0) = _ => apply (eq_trans (tk_deflate_slow_insert fu a x0))
  | |- tk (match ?t with pair _ _ => _ end) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (fst (match ?t with pair _ _ => _ end)) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (if ?c then _ else _) = _ => destruct c
  | |- tk (fst (if ?c then _ else _)) = _ => destruct c
  | |- tk ?y = tk _ => is_var y; assumption
  end.
Ltac tkgoF := repeat tkgoF1.

Lemma tk_deflate_fast_body : forall s flush, tk (fst (deflate_fast_body s flush)) = tk s.
Proof. intros. cbv beta delta [deflate_fast_body]. tkgoF. Qed.
Lemma tk_deflate_slow_body : forall s flush, tk (fst (deflate_slow_body s flush)) = tk s.
Proof. intros. cbv beta delta [deflate_slow_body]. tkgoF. Qed.
Lemma tk_deflate_huff_body : forall s flush, tk (fst (deflate_huff_body s flush)) = tk s.
Proof. intros. cbv beta delta [deflate_huff_body]. tkgoF. Qed.
Lemma tk_deflate_rle_body : forall s flush, tk (fst (deflate_rle_body s flush)) = tk s.
Proof. intros. cbv beta delta [deflate_rle_body]. tkgoF. Qed.

Lemma tk_deflate_fast_loop : forall fuel s flush, tk (fst (deflate_fast_loop fuel s flush)) = tk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_fast_loop].
  pose proof (tk_deflate_fast_body s flush) as X. destruct (deflate_fast_body s flush) as [s1 o]. cbn [fst] in X.
  destruct o; cbn [fst]; [rewrite IH; exact X | exact X | exact X].
Qed.
Lemma tk_deflate_slow_loop : forall fuel s flush, tk (fst (deflate_slow_loop fuel s flush)) = tk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_slow_loop].
  pose proof (tk_deflate_slow_body s flush) as X. destruct (deflate_slow_body s flush) as [s1 o]. cbn [fst] in X.
  destruct o; cbn [fst]; [rewrite IH; exact X | exact X | exact X].
Qed.
Lemma tk_deflate_huff_loop : forall fuel s flush, tk (fst (deflate_huff_loop fuel s flush)) = tk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_huff_loop].
  pose proof (tk_deflate_huff_body s flush) as X. destruct (deflate_huff_body s flush) as [s1 o]. cbn [fst] in X.
  destruct o; cbn [fst]; [rewrite IH; exact X | exact X | exact X].
Qed.
Lemma tk_deflate_rle_loop : forall fuel s flush, tk (fst (deflate_rle_loop fuel s flush)) = tk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_rle_loop].
  pose proof (tk_deflate_rle_body s flush) as X. destruct (deflate_rle_body s flush) as [s1 o]. cbn [fst] in X.
  destruct o; cbn [fst]; [rewrite IH; exact X | exact X | exact X].
Qed.

Ltac tkgoG1 :=
  lazymatch goal with
  | |- tk ?x = tk ?x => reflexivity
  | |- tk (let x := ?t in @?E x) = tk ?s0 =>
      first [ is_var t; change (tk (E t) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (E t) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (let x := ?t in @?E x)) = tk ?s0 =>
      first [ is_var t; change (tk (fst (E t)) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (fst (E t)) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (?a, ?b)) = _ => change (tk (fst (a, b))) with (tk a)
  | |- tk (set_bi_buf ?a ?v) = _ => change (tk (set_bi_buf a v)) with (tk a)
  | |- tk (set_bi_valid ?a ?v) = _ => change (tk (set_bi_valid a v)) with (tk a)
  | |- tk (set_bl_count ?a ?v) = _ => change (tk (set_bl_count a v)) with (tk a)
  | |- tk (set_bl_max_code ?a ?v) = _ => change (tk (set_bl_max_code a v)) with (tk a)
  | |- tk (set_bl_tree_dl ?a ?v) = _ => change (tk (set_bl_tree_dl a v)) with (tk a)
  | |- tk (set_bl_tree_fc ?a ?v) = _ => change (tk (set_bl_tree_fc a v)) with (tk a)
  | |- tk (set_block_start ?a ?v) = _ => change (tk (set_block_start a v)) with (tk a)
  | |- tk (set_d_max_code ?a ?v) = _ => change (tk (set_d_max_code a v)) with (tk a)
  | |- tk (set_depth ?a ?v) = _ => change (tk (set_depth a v)) with (tk a)
  | |- tk (set_dyn_dtree_dl ?a ?v) = _ => change (tk (set_dyn_dtree_dl a v)) with (tk a)
  | |- tk (set_dyn_dtree_fc ?a ?v) = _ => change (tk (set_dyn_dtree_fc a v)) with (tk a)
  | |- tk (set_dyn_ltree_dl ?a ?v) = _ => change (tk (set_dyn_ltree_dl a v)) with (tk a)
  | |- tk (set_dyn_ltree_fc ?a ?v) = _ => change (tk (set_dyn_ltree_fc a v)) with (tk a)
  | |- tk (set_good_match ?a ?v) = _ => change (tk (set_good_match a v)) with (tk a)
  | |- tk (set_gzhead ?a ?v) = _ => change (tk (set_gzhead a v)) with (tk a)
  | |- tk (set_gzindex ?a ?v) = _ => change (tk (set_gzindex a v)) with (tk a)
  | |- tk (set_hash_bits ?a ?v) = _ => change (tk (set_hash_bits a v)) with (tk a)
  | |- tk (set_hash_mask ?a ?v) = _ => change (tk (set_hash_mask a v)) with (tk a)
  | |- tk (set_hash_shift ?a ?v) = _ => change (tk (set_hash_shift a v)) with (tk a)
  | |- tk (set_head ?a ?v) = _ => change (tk (set_head a v)) with (tk a)
  | |- tk (set_heap ?a ?v) = _ => change (tk (set_heap a v)) with (tk a)
  | |- tk (set_heap_len ?a ?v) = _ => change (tk (set_heap_len a v)) with (tk a)
  | |- tk (set_heap_max ?a ?v) = _ => change (tk (set_heap_max a v)) with (tk a)
  | |- tk (set_high_water ?a ?v) = _ => change (tk (set_high_water a v)) with (tk a)
  | |- tk (set_ins_h ?a ?v) = _ => change (tk (set_ins_h a v)) with (tk a)
  | |- tk (set_insert ?a ?v) = _ => change (tk (set_insert a v)) with (tk a)
  | |- tk (set_l_max_code ?a ?v) = _ => change (tk (set_l_max_code a v)) with (tk a)
  | |- tk (set_last_flush ?a ?v) = _ => change (tk (set_last_flush a v)) with (tk a)
  | |- tk (set_level ?a ?v) = _ => change (tk (set_level a v)) with (tk a)
  | |- tk (set_lookahead ?a ?v) = _ => change (tk (set_lookahead a v)) with (tk a)
  | |- tk (set_match_available ?a ?v) = _ => change (tk (set_match_available a v)) with (tk a)
  | |- tk (set_match_length ?a ?v) = _ => change (tk (set_match_length a v)) with (tk a)
  | |- tk (set_match_start ?a ?v) = _ => change (tk (set_match_start a v)) with (tk a)
  | |- tk (set_matches ?a ?v) = _ => change (tk (set_matches a v)) with (tk a)
  | |- tk (set_max_chain_length ?a ?v) = _ => change (tk (set_max_chain_length a v)) with (tk a)
  | |- tk (set_max_lazy_match ?a ?v) = _ => change (tk (set_max_lazy_match a v)) with (tk a)
  | |- tk (set_method ?a ?v) = _ => change (tk (set_method a v)) with (tk a)
  | |- tk (set_nice_match ?a ?v) = _ => change (tk (set_nice_match a v)) with (tk a)
  | |- tk (set_opt_len ?a ?v) = _ => change (tk (set_opt_len a v)) with (tk a)
  | |- tk (set_pending ?a ?v) = _ => change (tk (set_pending a v)) with (tk a)
  | |- tk (set_pending_buf ?a ?v) = _ => change (tk (set_pending_buf a v)) with (tk a)
  | |- tk (set_pending_buf_size ?a ?v) = _ => change (tk (set_pending_buf_size a v)) with (tk a)
  | |- tk (set_pending_out ?a ?v) = _ => change (tk (set_pending_out a v)) with (tk a)
  | |- tk (set_prev ?a ?v) = _ => change (tk (set_prev a v)) with (tk a)
  | |- tk (set_prev_length ?a ?v) = _ => change (tk (set_prev_length a v)) with (tk a)
  | |- tk (set_prev_match ?a ?v) = _ => change (tk (set_prev_match a v)) with (tk a)
  | |- tk (set_static_len ?a ?v) = _ => change (tk (set_static_len a v)) with (tk a)
  | |- tk (set_status ?a ?v) = _ => change (tk (set_status a v)) with (tk a)
  | |- tk (set_strategy ?a ?v) = _ => change (tk (set_strategy a v)) with (tk a)
  | |- tk (set_strm ?a ?v) = _ => rewrite (tk_set_strm a v) by tkz_tac
  | |- tk (set_strstart ?a ?v) = _ => change (tk (set_strstart a v)) with (tk a)
  | |- tk (set_sym_end ?a ?v) = _ => change (tk (set_sym_end a v)) with (tk a)
  | |- tk (set_sym_next ?a ?v) = _ => change (tk (set_sym_next a v)) with (tk a)
  | |- tk (set_w_bits ?a ?v) = _ => change (tk (set_w_bits a v)) with (tk a)
  | |- tk (set_w_mask ?a ?v) = _ => change (tk (set_w_mask a v)) with (tk a)
  | |- tk (set_window ?a ?v) = _ => change (tk (set_window a v)) with (tk a)
  | |- tk (set_window_size ?a ?v) = _ => change (tk (set_window_size a v)) with (tk a)
  | |- tk (set_wrap ?a ?v) = _ => change (tk (set_wrap a v)) with (tk a)
  | |- tk (put_byte ?a ?v) = _ => change (tk (put_byte a v)) with (tk a)
  | |- tk (putShortMSB ?a ?v) = _ => change (tk (putShortMSB a v)) with (tk a)
  | |- tk (set_tree_fc ?a ?v ?w) = _ => change (tk (set_tree_fc a v w)) with (tk a)
  | |- tk (set_tree_dl ?a ?v ?w) = _ => change (tk (set_tree_dl a v w)) with (tk a)
  | |- tk (set_max_code ?a ?v ?w) = _ => change (tk (set_max_code a v w)) with (tk a)
  | |- tk (sym_buf_set ?a ?v ?w) = _ => change (tk (sym_buf_set a v w)) with (tk a)
  | |- tk (set_Freq ?a ?v ?w ?x) = _ => change (tk (set_Freq a v w x)) with (tk a)
  | |- tk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_flush_block a x0 x1 x2))
  | |- tk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_stored_block a x0 x1 x2))
  | |- tk (tr_align ?a ) = _ => apply (eq_trans (tk_tr_align a ))
  | |- tk (flush_pending ?a ) = _ => apply (eq_trans (tk_flush_pending a ))
  | |- tk (bi_flush ?a ) = _ => apply (eq_trans (tk_bi_flush a ))
  | |- tk (clear_hash ?a ) = _ => apply (eq_trans (tk_clear_hash a ))
  | |- tk (slide_hash ?a ) = _ => apply (eq_trans (tk_slide_hash a ))
  | |- tk (fill_window ?a ) = _ => apply (eq_trans (tk_fill_window a ))
  | |- tk (flush_block_only ?a ?x0) = _ => apply (eq_trans (tk_flush_block_only a x0))
  | |- tk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (tk_tr_tally_lit a x0))
  | |- tk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_tr_tally_dist a x0 x1))
  | |- tk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (tk_insert_string a x0))
  | |- tk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_read_buf a x0 x1))
  | |- tk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (tk_longest_match a x0))
  | |- tk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (tk_fill_window_insert fu a x0))
  | |- tk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (tk_flush_block a x0))
  | |- tk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (tk_deflate_tail a x0))
  | |- tk (deflate_stored_used ?a ?x0) = _ => apply (eq_trans (tk_deflate_stored_used a x0))
  | |- tk (fst (deflate_stored_fin ?a ?x0)) = _ => apply (eq_trans (tk_deflate_stored_fin a x0))
  | |- tk (fst (deflate_stored_slide ?a ?x0)) = _ => apply (eq_trans (tk_deflate_stored_slide a x0))
  | |- tk (fst (deflate_stored_loop ?fu ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_deflate_stored_loop fu a x0 x1))
  | |- tk (deflate_fast_insert ?fu ?a) = _ => apply (eq_trans (tk_deflate_fast_insert fu a))
  | |- tk (deflate_slow_insert ?fu ?a ?x0) = _ => apply (eq_trans (tk_deflate_slow_insert fu a x0))
  | |- tk (fst (deflate_fast_loop ?fu ?a ?x0)) = _ => apply (eq_trans (tk_deflate_fast_loop fu a x0))
  | |- tk (fst (deflate_slow_loop ?fu ?a ?x0)) = _ => apply (eq_trans (tk_deflate_slow_loop fu a x0))
  | |- tk (fst (deflate_huff_loop ?fu ?a ?x0)) = _ => apply (eq_trans (tk_deflate_huff_loop fu a x0))
  | |- tk (fst (deflate_rle_loop ?fu ?a ?x0)) = _ => apply (eq_trans (tk_deflate_rle_loop fu a x0))
  | |- tk (fst (deflate_stored ?a ?x0)) = _ => apply (eq_trans (tk_deflate_stored a x0))
  | |- tk (match ?t with pair _ _ => _ end) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (fst (match ?t with pair _ _ => _ end)) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (if ?c then _ else _) = _ => destruct c
  | |- tk (fst (if ?c then _ else _)) = _ => destruct c
  | |- tk ?y = tk _ => is_var y; assumption
  end.
Ltac tkgoG := repeat tkgoG1.

Lemma tk_deflate_fast : forall s flush, tk (fst (deflate_fast s flush)) = tk s.
Proof. intros. cbv beta delta [deflate_fast]. tkgoG. Qed.
Lemma tk_deflate_slow : forall s flush, tk (fst (deflate_slow s flush)) = tk s.
Proof. intros. cbv beta delta [deflate_slow]. tkgoG. Qed.
Lemma tk_deflate_huff : forall s flush, tk (fst (deflate_huff s flush)) = tk s.
Proof. intros. cbv beta delta [deflate_huff]. tkgoG. Qed.
Lemma tk_deflate_rle : forall s flush, tk (fst (deflate_rle s flush)) = tk s.
Proof. intros. cbv beta delta [deflate_rle]. tkgoG. Qed.
Lemma tk_run_compress_func : forall s flush, tk (fst (run_compress_func s flush)) = tk s.
Proof.
  intros. cbv beta delta [run_compress_func].
  destruct (_ =? 0); [apply tk_deflate_stored|]. destruct (_ =? _); [apply tk_deflate_huff|].
  destruct (_ =? _); [apply tk_deflate_rle|]. destruct (_ <=? _); [apply tk_deflate_fast | apply tk_deflate_slow].
Qed.
Lemma tk_err_return : forall s e, tk (fst (err_return s e)) = tk s.
Proof. reflexivity. Qed.
Lemma tk_deflate_zlib_header : forall s, tk (fst (deflate_zlib_header s)) = tk s.
Proof. intros. cbv beta delta [deflate_zlib_header]. tkgoG. Qed.
Lemma tk_deflate_gzip_header : forall s, tk (fst (deflate_gzip_header s)) = tk s.
Proof. intros. cbv beta delta [deflate_gzip_header]. tkgoG. Qed.
Lemma tk_deflate_trailer : forall s, tk (fst (deflate_trailer s)) = tk s.
Proof. intros. cbv beta delta [deflate_trailer]. tkgoG. Qed.

Ltac tkgoH1 :=
  lazymatch goal with
  | |- tk ?x = tk ?x => reflexivity
  | |- tk (let x := ?t in @?E x) = tk ?s0 =>
      first [ is_var t; change (tk (E t) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (E t) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (let x := ?t in @?E x)) = tk ?s0 =>
      first [ is_var t; change (tk (fst (E t)) = tk s0); cbv beta
            | lazymatch type of t with
              | cstrm => change (tk (fst (E t)) = tk s0); cbv beta
              | deflate_state => let H := fresh "Htk" in assert (H : tk t = tk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- tk (fst (?a, ?b)) = _ => change (tk (fst (a, b))) with (tk a)
  | |- tk (set_bi_buf ?a ?v) = _ => change (tk (set_bi_buf a v)) with (tk a)
  | |- tk (set_bi_valid ?a ?v) = _ => change (tk (set_bi_valid a v)) with (tk a)
  | |- tk (set_bl_count ?a ?v) = _ => change (tk (set_bl_count a v)) with (tk a)
  | |- tk (set_bl_max_code ?a ?v) = _ => change (tk (set_bl_max_code a v)) with (tk a)
  | |- tk (set_bl_tree_dl ?a ?v) = _ => change (tk (set_bl_tree_dl a v)) with (tk a)
  | |- tk (set_bl_tree_fc ?a ?v) = _ => change (tk (set_bl_tree_fc a v)) with (tk a)
  | |- tk (set_block_start ?a ?v) = _ => change (tk (set_block_start a v)) with (tk a)
  | |- tk (set_d_max_code ?a ?v) = _ => change (tk (set_d_max_code a v)) with (tk a)
  | |- tk (set_depth ?a ?v) = _ => change (tk (set_depth a v)) with (tk a)
  | |- tk (set_dyn_dtree_dl ?a ?v) = _ => change (tk (set_dyn_dtree_dl a v)) with (tk a)
  | |- tk (set_dyn_dtree_fc ?a ?v) = _ => change (tk (set_dyn_dtree_fc a v)) with (tk a)
  | |- tk (set_dyn_ltree_dl ?a ?v) = _ => change (tk (set_dyn_ltree_dl a v)) with (tk a)
  | |- tk (set_dyn_ltree_fc ?a ?v) = _ => change (tk (set_dyn_ltree_fc a v)) with (tk a)
  | |- tk (set_good_match ?a ?v) = _ => change (tk (set_good_match a v)) with (tk a)
  | |- tk (set_gzhead ?a ?v) = _ => change (tk (set_gzhead a v)) with (tk a)
  | |- tk (set_gzindex ?a ?v) = _ => change (tk (set_gzindex a v)) with (tk a)
  | |- tk (set_hash_bits ?a ?v) = _ => change (tk (set_hash_bits a v)) with (tk a)
  | |- tk (set_hash_mask ?a ?v) = _ => change (tk (set_hash_mask a v)) with (tk a)
  | |- tk (set_hash_shift ?a ?v) = _ => change (tk (set_hash_shift a v)) with (tk a)
  | |- tk (set_head ?a ?v) = _ => change (tk (set_head a v)) with (tk a)
  | |- tk (set_heap ?a ?v) = _ => change (tk (set_heap a v)) with (tk a)
  | |- tk (set_heap_len ?a ?v) = _ => change (tk (set_heap_len a v)) with (tk a)
  | |- tk (set_heap_max ?a ?v) = _ => change (tk (set_heap_max a v)) with (tk a)
  | |- tk (set_high_water ?a ?v) = _ => change (tk (set_high_water a v)) with (tk a)
  | |- tk (set_ins_h ?a ?v) = _ => change (tk (set_ins_h a v)) with (tk a)
  | |- tk (set_insert ?a ?v) = _ => change (tk (set_insert a v)) with (tk a)
  | |- tk (set_l_max_code ?a ?v) = _ => change (tk (set_l_max_code a v)) with (tk a)
  | |- tk (set_last_flush ?a ?v) = _ => change (tk (set_last_flush a v)) with (tk a)
  | |- tk (set_level ?a ?v) = _ => change (tk (set_level a v)) with (tk a)
  | |- tk (set_lookahead ?a ?v) = _ => change (tk (set_lookahead a v)) with (tk a)
  | |- tk (set_match_available ?a ?v) = _ => change (tk (set_match_available a v)) with (tk a)
  | |- tk (set_match_length ?a ?v) = _ => change (tk (set_match_length a v)) with (tk a)
  | |- tk (set_match_start ?a ?v) = _ => change (tk (set_match_start a v)) with (tk a)
  | |- tk (set_matches ?a ?v) = _ => change (tk (set_matches a v)) with (tk a)
  | |- tk (set_max_chain_length ?a ?v) = _ => change (tk (set_max_chain_length a v)) with (tk a)
  | |- tk (set_max_lazy_match ?a ?v) = _ => change (tk (set_max_lazy_match a v)) with (tk a)
  | |- tk (set_method ?a ?v) = _ => change (tk (set_method a v)) with (tk a)
  | |- tk (set_nice_match ?a ?v) = _ => change (tk (set_nice_match a v)) with (tk a)
  | |- tk (set_opt_len ?a ?v) = _ => change (tk (set_opt_len a v)) with (tk a)
  | |- tk (set_pending ?a ?v) = _ => change (tk (set_pending a v)) with (tk a)
  | |- tk (set_pending_buf ?a ?v) = _ => change (tk (set_pending_buf a v)) with (tk a)
  | |- tk (set_pending_buf_size ?a ?v) = _ => change (tk (set_pending_buf_size a v)) with (tk a)
  | |- tk (set_pending_out ?a ?v) = _ => change (tk (set_pending_out a v)) with (tk a)
  | |- tk (set_prev ?a ?v) = _ => change (tk (set_prev a v)) with (tk a)
  | |- tk (set_prev_length ?a ?v) = _ => change (tk (set_prev_length a v)) with (tk a)
  | |- tk (set_prev_match ?a ?v) = _ => change (tk (set_prev_match a v)) with (tk a)
  | |- tk (set_static_len ?a ?v) = _ => change (tk (set_static_len a v)) with (tk a)
  | |- tk (set_status ?a ?v) = _ => change (tk (set_status a v)) with (tk a)
  | |- tk (set_strategy ?a ?v) = _ => change (tk (set_strategy a v)) with (tk a)
  | |- tk (set_strm ?a ?v) = _ => rewrite (tk_set_strm a v) by tkz_tac
  | |- tk (set_strstart ?a ?v) = _ => change (tk (set_strstart a v)) with (tk a)
  | |- tk (set_sym_end ?a ?v) = _ => change (tk (set_sym_end a v)) with (tk a)
  | |- tk (set_sym_next ?a ?v) = _ => change (tk (set_sym_next a v)) with (tk a)
  | |- tk (set_w_bits ?a ?v) = _ => change (tk (set_w_bits a v)) with (tk a)
  | |- tk (set_w_mask ?a ?v) = _ => change (tk (set_w_mask a v)) with (tk a)
  | |- tk (set_window ?a ?v) = _ => change (tk (set_window a v)) with (tk a)
  | |- tk (set_window_size ?a ?v) = _ => change (tk (set_window_size a v)) with (tk a)
  | |- tk (set_wrap ?a ?v) = _ => change (tk (set_wrap a v)) with (tk a)
  | |- tk (put_byte ?a ?v) = _ => change (tk (put_byte a v)) with (tk a)
  | |- tk (putShortMSB ?a ?v) = _ => change (tk (putShortMSB a v)) with (tk a)
  | |- tk (set_tree_fc ?a ?v ?w) = _ => change (tk (set_tree_fc a v w)) with (tk a)
  | |- tk (set_tree_dl ?a ?v ?w) = _ => change (tk (set_tree_dl a v w)) with (tk a)
  | |- tk (set_max_code ?a ?v ?w) = _ => change (tk (set_max_code a v w)) with (tk a)
  | |- tk (sym_buf_set ?a ?v ?w) = _ => change (tk (sym_buf_set a v w)) with (tk a)
  | |- tk (set_Freq ?a ?v ?w ?x) = _ => change (tk (set_Freq a v w x)) with (tk a)
  | |- tk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_flush_block a x0 x1 x2))
  | |- tk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (tk_tr_stored_block a x0 x1 x2))
  | |- tk (tr_align ?a ) = _ => apply (eq_trans (tk_tr_align a ))
  | |- tk (flush_pending ?a ) = _ => apply (eq_trans (tk_flush_pending a ))
  | |- tk (bi_flush ?a ) = _ => apply (eq_trans (tk_bi_flush a ))
  | |- tk (clear_hash ?a ) = _ => apply (eq_trans (tk_clear_hash a ))
  | |- tk (slide_hash ?a ) = _ => apply (eq_trans (tk_slide_hash a ))
  | |- tk (fill_window ?a ) = _ => apply (eq_trans (tk_fill_window a ))
  | |- tk (flush_block_only ?a ?x0) = _ => apply (eq_trans (tk_flush_block_only a x0))
  | |- tk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (tk_tr_tally_lit a x0))
  | |- tk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_tr_tally_dist a x0 x1))
  | |- tk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (tk_insert_string a x0))
  | |- tk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_read_buf a x0 x1))
  | |- tk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (tk_longest_match a x0))
  | |- tk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (tk_fill_window_insert fu a x0))
  | |- tk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (tk_flush_block a x0))
  | |- tk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (tk_deflate_tail a x0))
  | |- tk (deflate_stored_used ?a ?x0) = _ => apply (eq_trans (tk_deflate_stored_used a x0))
  | |- tk (fst (deflate_stored_fin ?a ?x0)) = _ => apply (eq_trans (tk_deflate_stored_fin a x0))
  | |- tk (fst (deflate_stored_slide ?a ?x0)) = _ => apply (eq_trans (tk_deflate_stored_slide a x0))
  | |- tk (fst (deflate_stored_loop ?fu ?a ?x0 ?x1)) = _ => apply (eq_trans (tk_deflate_stored_loop fu a x0 x1))
  | |- tk (deflate_fast_insert ?fu ?a) = _ => apply (eq_trans (tk_deflate_fast_insert fu a))
  | |- tk (deflate_slow_insert ?fu ?a ?x0) = _ => apply (eq_trans (tk_deflate_slow_insert fu a x0))
  | |- tk (fst (deflate_fast_loop ?fu ?a ?x0)) = _ => apply (eq_trans (tk_deflate_fast_loop fu a x0))
  | |- tk (fst (deflate_slow_loop ?fu ?a ?x0)) = _ => apply (eq_trans (tk_deflate_slow_loop fu a x0))
  | |- tk (fst (deflate_huff_loop ?fu ?a ?x0)) = _ => apply (eq_trans (tk_deflate_huff_loop fu a x0))
  | |- tk (fst (deflate_rle_loop ?fu ?a ?x0)) = _ => apply (eq_trans (tk_deflate_rle_loop fu a x0))
  | |- tk (fst (deflate_stored ?a ?x0)) = _ => apply (eq_trans (tk_deflate_stored a x0))
  | |- tk (fst (run_compress_func ?a ?x0)) = _ => apply (eq_trans (tk_run_compress_func a x0))
  | |- tk (fst (err_return ?a ?x0)) = _ => apply (eq_trans (tk_err_return a x0))
  | |- tk (fst (deflate_zlib_header ?a)) = _ => apply (eq_trans (tk_deflate_zlib_header a))
  | |- tk (fst (deflate_gzip_header ?a)) = _ => apply (eq_trans (tk_deflate_gzip_header a))
  | |- tk (fst (deflate_trailer ?a)) = _ => apply (eq_trans (tk_deflate_trailer a))
  | |- tk (match ?t with pair _ _ => _ end) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (fst (match ?t with pair _ _ => _ end)) = tk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Htk" in assert (H : tk (fst t) = tk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- tk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- tk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- tk (if ?c then _ else _) = _ => destruct c
  | |- tk (fst (if ?c then _ else _)) = _ => destruct c
  | |- tk ?y = tk _ => is_var y; assumption
  end.
Ltac tkgoH := repeat tkgoH1.


