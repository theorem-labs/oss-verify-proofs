(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateInvKeep DeflateSetters.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import RefDeflatePost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition wk (s : deflate_state) : Z := ds_wrap s.

Lemma wk_kp : forall a b, kproj a = kproj b -> wk a = wk b.
Proof. intros a b K. unfold wk. exact (kp_wrap _ _ K). Qed.

Lemma wk_tr_tally_lit : forall s c, wk (fst (tr_tally_lit s c)) = wk s.
Proof. intros s c. rewrite (wk_kp _ _ (kp_tr_tally_lit s c)). reflexivity. Qed.
Lemma wk_tr_tally_dist : forall s d l, wk (fst (tr_tally_dist s d l)) = wk s.
Proof. intros s d l. rewrite (wk_kp _ _ (kp_tr_tally_dist s d l)). reflexivity. Qed.
Lemma wk_tr_flush_block : forall s buf len last, wk (tr_flush_block s buf len last) = wk s.
Proof. intros. exact (wk_kp _ _ (kp_tr_flush_block s buf len last)). Qed.
Lemma wk_tr_stored_block : forall s buf len last, wk (tr_stored_block s buf len last) = wk s.
Proof. intros. exact (wk_kp _ _ (kp_tr_stored_block s buf len last)). Qed.
Lemma wk_tr_align : forall s, wk (tr_align s) = wk s.
Proof. intros. exact (wk_kp _ _ (kp_tr_align s)). Qed.
Lemma wk_bi_flush : forall s, wk (bi_flush s) = wk s.
Proof. intros. unfold bi_flush, put_short. destruct (_ =? _); [reflexivity|]. destruct (_ <=? _); reflexivity. Qed.
Lemma wk_flush_pending : forall s, wk (flush_pending s) = wk s.
Proof.
  intros. unfold flush_pending, tr_flush_bits. cbv zeta.
  destruct (_ =? 0); [apply wk_bi_flush|]. rewrite <- (wk_bi_flush s). destruct (_ =? 0); reflexivity.
Qed.


Ltac wkgoA1 :=
  lazymatch goal with
  | |- wk ?x = wk ?x => reflexivity
  | |- wk (let x := ?t in @?E x) = wk ?s0 =>
      first [ is_var t; change (wk (E t) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (let x := ?t in @?E x)) = wk ?s0 =>
      first [ is_var t; change (wk (fst (E t)) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (?a, ?b)) = _ => change (wk (fst (a, b))) with (wk a)
  | |- wk (set_bi_buf ?a ?v) = _ => change (wk (set_bi_buf a v)) with (wk a)
  | |- wk (set_bi_valid ?a ?v) = _ => change (wk (set_bi_valid a v)) with (wk a)
  | |- wk (set_bl_count ?a ?v) = _ => change (wk (set_bl_count a v)) with (wk a)
  | |- wk (set_bl_max_code ?a ?v) = _ => change (wk (set_bl_max_code a v)) with (wk a)
  | |- wk (set_bl_tree_dl ?a ?v) = _ => change (wk (set_bl_tree_dl a v)) with (wk a)
  | |- wk (set_bl_tree_fc ?a ?v) = _ => change (wk (set_bl_tree_fc a v)) with (wk a)
  | |- wk (set_block_start ?a ?v) = _ => change (wk (set_block_start a v)) with (wk a)
  | |- wk (set_d_max_code ?a ?v) = _ => change (wk (set_d_max_code a v)) with (wk a)
  | |- wk (set_depth ?a ?v) = _ => change (wk (set_depth a v)) with (wk a)
  | |- wk (set_dyn_dtree_dl ?a ?v) = _ => change (wk (set_dyn_dtree_dl a v)) with (wk a)
  | |- wk (set_dyn_dtree_fc ?a ?v) = _ => change (wk (set_dyn_dtree_fc a v)) with (wk a)
  | |- wk (set_dyn_ltree_dl ?a ?v) = _ => change (wk (set_dyn_ltree_dl a v)) with (wk a)
  | |- wk (set_dyn_ltree_fc ?a ?v) = _ => change (wk (set_dyn_ltree_fc a v)) with (wk a)
  | |- wk (set_good_match ?a ?v) = _ => change (wk (set_good_match a v)) with (wk a)
  | |- wk (set_gzhead ?a ?v) = _ => change (wk (set_gzhead a v)) with (wk a)
  | |- wk (set_gzindex ?a ?v) = _ => change (wk (set_gzindex a v)) with (wk a)
  | |- wk (set_hash_bits ?a ?v) = _ => change (wk (set_hash_bits a v)) with (wk a)
  | |- wk (set_hash_mask ?a ?v) = _ => change (wk (set_hash_mask a v)) with (wk a)
  | |- wk (set_hash_shift ?a ?v) = _ => change (wk (set_hash_shift a v)) with (wk a)
  | |- wk (set_head ?a ?v) = _ => change (wk (set_head a v)) with (wk a)
  | |- wk (set_heap ?a ?v) = _ => change (wk (set_heap a v)) with (wk a)
  | |- wk (set_heap_len ?a ?v) = _ => change (wk (set_heap_len a v)) with (wk a)
  | |- wk (set_heap_max ?a ?v) = _ => change (wk (set_heap_max a v)) with (wk a)
  | |- wk (set_high_water ?a ?v) = _ => change (wk (set_high_water a v)) with (wk a)
  | |- wk (set_ins_h ?a ?v) = _ => change (wk (set_ins_h a v)) with (wk a)
  | |- wk (set_insert ?a ?v) = _ => change (wk (set_insert a v)) with (wk a)
  | |- wk (set_l_max_code ?a ?v) = _ => change (wk (set_l_max_code a v)) with (wk a)
  | |- wk (set_last_flush ?a ?v) = _ => change (wk (set_last_flush a v)) with (wk a)
  | |- wk (set_level ?a ?v) = _ => change (wk (set_level a v)) with (wk a)
  | |- wk (set_lookahead ?a ?v) = _ => change (wk (set_lookahead a v)) with (wk a)
  | |- wk (set_match_available ?a ?v) = _ => change (wk (set_match_available a v)) with (wk a)
  | |- wk (set_match_length ?a ?v) = _ => change (wk (set_match_length a v)) with (wk a)
  | |- wk (set_match_start ?a ?v) = _ => change (wk (set_match_start a v)) with (wk a)
  | |- wk (set_matches ?a ?v) = _ => change (wk (set_matches a v)) with (wk a)
  | |- wk (set_max_chain_length ?a ?v) = _ => change (wk (set_max_chain_length a v)) with (wk a)
  | |- wk (set_max_lazy_match ?a ?v) = _ => change (wk (set_max_lazy_match a v)) with (wk a)
  | |- wk (set_method ?a ?v) = _ => change (wk (set_method a v)) with (wk a)
  | |- wk (set_nice_match ?a ?v) = _ => change (wk (set_nice_match a v)) with (wk a)
  | |- wk (set_opt_len ?a ?v) = _ => change (wk (set_opt_len a v)) with (wk a)
  | |- wk (set_pending ?a ?v) = _ => change (wk (set_pending a v)) with (wk a)
  | |- wk (set_pending_buf ?a ?v) = _ => change (wk (set_pending_buf a v)) with (wk a)
  | |- wk (set_pending_buf_size ?a ?v) = _ => change (wk (set_pending_buf_size a v)) with (wk a)
  | |- wk (set_pending_out ?a ?v) = _ => change (wk (set_pending_out a v)) with (wk a)
  | |- wk (set_prev ?a ?v) = _ => change (wk (set_prev a v)) with (wk a)
  | |- wk (set_prev_length ?a ?v) = _ => change (wk (set_prev_length a v)) with (wk a)
  | |- wk (set_prev_match ?a ?v) = _ => change (wk (set_prev_match a v)) with (wk a)
  | |- wk (set_static_len ?a ?v) = _ => change (wk (set_static_len a v)) with (wk a)
  | |- wk (set_status ?a ?v) = _ => change (wk (set_status a v)) with (wk a)
  | |- wk (set_strategy ?a ?v) = _ => change (wk (set_strategy a v)) with (wk a)
  | |- wk (set_strm ?a ?v) = _ => change (wk (set_strm a v)) with (wk a)
  | |- wk (set_strstart ?a ?v) = _ => change (wk (set_strstart a v)) with (wk a)
  | |- wk (set_sym_end ?a ?v) = _ => change (wk (set_sym_end a v)) with (wk a)
  | |- wk (set_sym_next ?a ?v) = _ => change (wk (set_sym_next a v)) with (wk a)
  | |- wk (set_w_bits ?a ?v) = _ => change (wk (set_w_bits a v)) with (wk a)
  | |- wk (set_w_mask ?a ?v) = _ => change (wk (set_w_mask a v)) with (wk a)
  | |- wk (set_window ?a ?v) = _ => change (wk (set_window a v)) with (wk a)
  | |- wk (set_window_size ?a ?v) = _ => change (wk (set_window_size a v)) with (wk a)
  | |- wk (set_wrap ?a ?v) = _ => change (wk (set_wrap a v)) with (wk a)
  | |- wk (put_byte ?a ?v) = _ => change (wk (put_byte a v)) with (wk a)
  | |- wk (putShortMSB ?a ?v) = _ => change (wk (putShortMSB a v)) with (wk a)
  | |- wk (set_tree_fc ?a ?v ?w) = _ => change (wk (set_tree_fc a v w)) with (wk a)
  | |- wk (set_tree_dl ?a ?v ?w) = _ => change (wk (set_tree_dl a v w)) with (wk a)
  | |- wk (set_max_code ?a ?v ?w) = _ => change (wk (set_max_code a v w)) with (wk a)
  | |- wk (sym_buf_set ?a ?v ?w) = _ => change (wk (sym_buf_set a v w)) with (wk a)
  | |- wk (set_Freq ?a ?v ?w ?x) = _ => change (wk (set_Freq a v w x)) with (wk a)
  | |- wk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_flush_block a x0 x1 x2))
  | |- wk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_stored_block a x0 x1 x2))
  | |- wk (tr_align ?a ) = _ => apply (eq_trans (wk_tr_align a ))
  | |- wk (flush_pending ?a ) = _ => apply (eq_trans (wk_flush_pending a ))
  | |- wk (bi_flush ?a ) = _ => apply (eq_trans (wk_bi_flush a ))
  | |- wk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (wk_tr_tally_lit a x0))
  | |- wk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_tr_tally_dist a x0 x1))
  | |- wk (match ?t with pair _ _ => _ end) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (fst (match ?t with pair _ _ => _ end)) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (if ?c then _ else _) = _ => destruct c
  | |- wk (fst (if ?c then _ else _)) = _ => destruct c
  | |- wk ?y = wk _ => is_var y; assumption
  end.
Ltac wkgoA := repeat wkgoA1.


Lemma wk_insert_string : forall s str, wk (fst (insert_string s str)) = wk s.
Proof. intros. cbv beta delta [insert_string]. wkgoA. Qed.
Lemma wk_clear_hash : forall s, wk (clear_hash s) = wk s.
Proof. intros. cbv beta delta [clear_hash]. wkgoA. Qed.
Lemma wk_slide_hash : forall s, wk (slide_hash s) = wk s.
Proof. intros. cbv beta delta [slide_hash]. wkgoA. Qed.
Lemma wk_read_buf : forall s dst size, wk (fst (read_buf s dst size)) = wk s.
Proof. intros. cbv beta delta [read_buf]. wkgoA. Qed.
Lemma wk_fill_window_insert : forall f s str, wk (fill_window_insert f s str) = wk s.
Proof.
  induction f as [|f IH]; intros s str; [reflexivity|]. cbn [fill_window_insert].
  wkgoA; apply (eq_trans (IH _ _)); wkgoA.
Qed.

Ltac wkgoB1 :=
  lazymatch goal with
  | |- wk ?x = wk ?x => reflexivity
  | |- wk (let x := ?t in @?E x) = wk ?s0 =>
      first [ is_var t; change (wk (E t) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (let x := ?t in @?E x)) = wk ?s0 =>
      first [ is_var t; change (wk (fst (E t)) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (?a, ?b)) = _ => change (wk (fst (a, b))) with (wk a)
  | |- wk (set_bi_buf ?a ?v) = _ => change (wk (set_bi_buf a v)) with (wk a)
  | |- wk (set_bi_valid ?a ?v) = _ => change (wk (set_bi_valid a v)) with (wk a)
  | |- wk (set_bl_count ?a ?v) = _ => change (wk (set_bl_count a v)) with (wk a)
  | |- wk (set_bl_max_code ?a ?v) = _ => change (wk (set_bl_max_code a v)) with (wk a)
  | |- wk (set_bl_tree_dl ?a ?v) = _ => change (wk (set_bl_tree_dl a v)) with (wk a)
  | |- wk (set_bl_tree_fc ?a ?v) = _ => change (wk (set_bl_tree_fc a v)) with (wk a)
  | |- wk (set_block_start ?a ?v) = _ => change (wk (set_block_start a v)) with (wk a)
  | |- wk (set_d_max_code ?a ?v) = _ => change (wk (set_d_max_code a v)) with (wk a)
  | |- wk (set_depth ?a ?v) = _ => change (wk (set_depth a v)) with (wk a)
  | |- wk (set_dyn_dtree_dl ?a ?v) = _ => change (wk (set_dyn_dtree_dl a v)) with (wk a)
  | |- wk (set_dyn_dtree_fc ?a ?v) = _ => change (wk (set_dyn_dtree_fc a v)) with (wk a)
  | |- wk (set_dyn_ltree_dl ?a ?v) = _ => change (wk (set_dyn_ltree_dl a v)) with (wk a)
  | |- wk (set_dyn_ltree_fc ?a ?v) = _ => change (wk (set_dyn_ltree_fc a v)) with (wk a)
  | |- wk (set_good_match ?a ?v) = _ => change (wk (set_good_match a v)) with (wk a)
  | |- wk (set_gzhead ?a ?v) = _ => change (wk (set_gzhead a v)) with (wk a)
  | |- wk (set_gzindex ?a ?v) = _ => change (wk (set_gzindex a v)) with (wk a)
  | |- wk (set_hash_bits ?a ?v) = _ => change (wk (set_hash_bits a v)) with (wk a)
  | |- wk (set_hash_mask ?a ?v) = _ => change (wk (set_hash_mask a v)) with (wk a)
  | |- wk (set_hash_shift ?a ?v) = _ => change (wk (set_hash_shift a v)) with (wk a)
  | |- wk (set_head ?a ?v) = _ => change (wk (set_head a v)) with (wk a)
  | |- wk (set_heap ?a ?v) = _ => change (wk (set_heap a v)) with (wk a)
  | |- wk (set_heap_len ?a ?v) = _ => change (wk (set_heap_len a v)) with (wk a)
  | |- wk (set_heap_max ?a ?v) = _ => change (wk (set_heap_max a v)) with (wk a)
  | |- wk (set_high_water ?a ?v) = _ => change (wk (set_high_water a v)) with (wk a)
  | |- wk (set_ins_h ?a ?v) = _ => change (wk (set_ins_h a v)) with (wk a)
  | |- wk (set_insert ?a ?v) = _ => change (wk (set_insert a v)) with (wk a)
  | |- wk (set_l_max_code ?a ?v) = _ => change (wk (set_l_max_code a v)) with (wk a)
  | |- wk (set_last_flush ?a ?v) = _ => change (wk (set_last_flush a v)) with (wk a)
  | |- wk (set_level ?a ?v) = _ => change (wk (set_level a v)) with (wk a)
  | |- wk (set_lookahead ?a ?v) = _ => change (wk (set_lookahead a v)) with (wk a)
  | |- wk (set_match_available ?a ?v) = _ => change (wk (set_match_available a v)) with (wk a)
  | |- wk (set_match_length ?a ?v) = _ => change (wk (set_match_length a v)) with (wk a)
  | |- wk (set_match_start ?a ?v) = _ => change (wk (set_match_start a v)) with (wk a)
  | |- wk (set_matches ?a ?v) = _ => change (wk (set_matches a v)) with (wk a)
  | |- wk (set_max_chain_length ?a ?v) = _ => change (wk (set_max_chain_length a v)) with (wk a)
  | |- wk (set_max_lazy_match ?a ?v) = _ => change (wk (set_max_lazy_match a v)) with (wk a)
  | |- wk (set_method ?a ?v) = _ => change (wk (set_method a v)) with (wk a)
  | |- wk (set_nice_match ?a ?v) = _ => change (wk (set_nice_match a v)) with (wk a)
  | |- wk (set_opt_len ?a ?v) = _ => change (wk (set_opt_len a v)) with (wk a)
  | |- wk (set_pending ?a ?v) = _ => change (wk (set_pending a v)) with (wk a)
  | |- wk (set_pending_buf ?a ?v) = _ => change (wk (set_pending_buf a v)) with (wk a)
  | |- wk (set_pending_buf_size ?a ?v) = _ => change (wk (set_pending_buf_size a v)) with (wk a)
  | |- wk (set_pending_out ?a ?v) = _ => change (wk (set_pending_out a v)) with (wk a)
  | |- wk (set_prev ?a ?v) = _ => change (wk (set_prev a v)) with (wk a)
  | |- wk (set_prev_length ?a ?v) = _ => change (wk (set_prev_length a v)) with (wk a)
  | |- wk (set_prev_match ?a ?v) = _ => change (wk (set_prev_match a v)) with (wk a)
  | |- wk (set_static_len ?a ?v) = _ => change (wk (set_static_len a v)) with (wk a)
  | |- wk (set_status ?a ?v) = _ => change (wk (set_status a v)) with (wk a)
  | |- wk (set_strategy ?a ?v) = _ => change (wk (set_strategy a v)) with (wk a)
  | |- wk (set_strm ?a ?v) = _ => change (wk (set_strm a v)) with (wk a)
  | |- wk (set_strstart ?a ?v) = _ => change (wk (set_strstart a v)) with (wk a)
  | |- wk (set_sym_end ?a ?v) = _ => change (wk (set_sym_end a v)) with (wk a)
  | |- wk (set_sym_next ?a ?v) = _ => change (wk (set_sym_next a v)) with (wk a)
  | |- wk (set_w_bits ?a ?v) = _ => change (wk (set_w_bits a v)) with (wk a)
  | |- wk (set_w_mask ?a ?v) = _ => change (wk (set_w_mask a v)) with (wk a)
  | |- wk (set_window ?a ?v) = _ => change (wk (set_window a v)) with (wk a)
  | |- wk (set_window_size ?a ?v) = _ => change (wk (set_window_size a v)) with (wk a)
  | |- wk (set_wrap ?a ?v) = _ => change (wk (set_wrap a v)) with (wk a)
  | |- wk (put_byte ?a ?v) = _ => change (wk (put_byte a v)) with (wk a)
  | |- wk (putShortMSB ?a ?v) = _ => change (wk (putShortMSB a v)) with (wk a)
  | |- wk (set_tree_fc ?a ?v ?w) = _ => change (wk (set_tree_fc a v w)) with (wk a)
  | |- wk (set_tree_dl ?a ?v ?w) = _ => change (wk (set_tree_dl a v w)) with (wk a)
  | |- wk (set_max_code ?a ?v ?w) = _ => change (wk (set_max_code a v w)) with (wk a)
  | |- wk (sym_buf_set ?a ?v ?w) = _ => change (wk (sym_buf_set a v w)) with (wk a)
  | |- wk (set_Freq ?a ?v ?w ?x) = _ => change (wk (set_Freq a v w x)) with (wk a)
  | |- wk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_flush_block a x0 x1 x2))
  | |- wk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_stored_block a x0 x1 x2))
  | |- wk (tr_align ?a ) = _ => apply (eq_trans (wk_tr_align a ))
  | |- wk (flush_pending ?a ) = _ => apply (eq_trans (wk_flush_pending a ))
  | |- wk (bi_flush ?a ) = _ => apply (eq_trans (wk_bi_flush a ))
  | |- wk (clear_hash ?a ) = _ => apply (eq_trans (wk_clear_hash a ))
  | |- wk (slide_hash ?a ) = _ => apply (eq_trans (wk_slide_hash a ))
  | |- wk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (wk_tr_tally_lit a x0))
  | |- wk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_tr_tally_dist a x0 x1))
  | |- wk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (wk_insert_string a x0))
  | |- wk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_read_buf a x0 x1))
  | |- wk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (wk_fill_window_insert fu a x0))
  | |- wk (match ?t with pair _ _ => _ end) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (fst (match ?t with pair _ _ => _ end)) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (if ?c then _ else _) = _ => destruct c
  | |- wk (fst (if ?c then _ else _)) = _ => destruct c
  | |- wk ?y = wk _ => is_var y; assumption
  end.
Ltac wkgoB := repeat wkgoB1.

Lemma wk_fill_window_body : forall s wsize, wk (fst (fill_window_body s wsize)) = wk s.
Proof. intros. cbv beta delta [fill_window_body]. wkgoB. Qed.
Lemma wk_fill_window_loop : forall f s wsize, wk (fill_window_loop f s wsize) = wk s.
Proof.
  induction f as [|f IH]; intros s wsize; [reflexivity|]. cbn [fill_window_loop].
  pose proof (wk_fill_window_body s wsize) as X. destruct (fill_window_body s wsize) as [s1 b]. cbn [fst] in X.
  destruct b; [exact X|]. destruct (_ && _); [rewrite IH|]; exact X.
Qed.
Lemma wk_fill_window_high : forall s, wk (fill_window_high s) = wk s.
Proof. intros. cbv beta delta [fill_window_high]. wkgoB. Qed.
Lemma wk_fill_window : forall s, wk (fill_window s) = wk s.
Proof. intros. cbv beta delta [fill_window]. cbv zeta. rewrite wk_fill_window_high. apply wk_fill_window_loop. Qed.
Lemma wk_longest_match_body : forall s a b c d e f g,
  wk (fst (fst (fst (fst (fst (fst (longest_match_body s a b c d e f g))))))) = wk s.
Proof.
  intros. cbv beta delta [longest_match_body]. cbv zeta.
  repeat (first [ reflexivity | match goal with |- context [if ?c then _ else _] => destruct c end ]; cbn [fst snd]).
Qed.
Lemma wk_longest_match_loop : forall fuel s a b c d e f g, wk (fst (longest_match_loop fuel s a b c d e f g)) = wk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [longest_match_loop].
  pose proof (wk_longest_match_body s a b c d e f g) as X.
  destruct (longest_match_body s a b c d e f g) as [[[[[[s1 x1] x2] x3] x4] x5] cont]. cbn [fst] in X.
  destruct cont; [rewrite IH|]; exact X.
Qed.
Lemma wk_longest_match : forall s cur, wk (fst (longest_match s cur)) = wk s.
Proof.
  intros. cbv beta delta [longest_match]. cbv zeta.
  match goal with |- context [longest_match_loop ?n s cur ?a ?b ?c ?d ?e ?f] =>
    pose proof (wk_longest_match_loop n s cur a b c d e f) as X; destruct (longest_match_loop n s cur a b c d e f) as [s1 bl] end.
  cbn [fst] in X. destruct (_ <=? _); exact X.
Qed.
Lemma wk_flush_block_only : forall s last, wk (flush_block_only s last) = wk s.
Proof. intros. cbv beta delta [flush_block_only]. wkgoB. Qed.

Ltac wkgoC1 :=
  lazymatch goal with
  | |- wk ?x = wk ?x => reflexivity
  | |- wk (let x := ?t in @?E x) = wk ?s0 =>
      first [ is_var t; change (wk (E t) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (let x := ?t in @?E x)) = wk ?s0 =>
      first [ is_var t; change (wk (fst (E t)) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (?a, ?b)) = _ => change (wk (fst (a, b))) with (wk a)
  | |- wk (set_bi_buf ?a ?v) = _ => change (wk (set_bi_buf a v)) with (wk a)
  | |- wk (set_bi_valid ?a ?v) = _ => change (wk (set_bi_valid a v)) with (wk a)
  | |- wk (set_bl_count ?a ?v) = _ => change (wk (set_bl_count a v)) with (wk a)
  | |- wk (set_bl_max_code ?a ?v) = _ => change (wk (set_bl_max_code a v)) with (wk a)
  | |- wk (set_bl_tree_dl ?a ?v) = _ => change (wk (set_bl_tree_dl a v)) with (wk a)
  | |- wk (set_bl_tree_fc ?a ?v) = _ => change (wk (set_bl_tree_fc a v)) with (wk a)
  | |- wk (set_block_start ?a ?v) = _ => change (wk (set_block_start a v)) with (wk a)
  | |- wk (set_d_max_code ?a ?v) = _ => change (wk (set_d_max_code a v)) with (wk a)
  | |- wk (set_depth ?a ?v) = _ => change (wk (set_depth a v)) with (wk a)
  | |- wk (set_dyn_dtree_dl ?a ?v) = _ => change (wk (set_dyn_dtree_dl a v)) with (wk a)
  | |- wk (set_dyn_dtree_fc ?a ?v) = _ => change (wk (set_dyn_dtree_fc a v)) with (wk a)
  | |- wk (set_dyn_ltree_dl ?a ?v) = _ => change (wk (set_dyn_ltree_dl a v)) with (wk a)
  | |- wk (set_dyn_ltree_fc ?a ?v) = _ => change (wk (set_dyn_ltree_fc a v)) with (wk a)
  | |- wk (set_good_match ?a ?v) = _ => change (wk (set_good_match a v)) with (wk a)
  | |- wk (set_gzhead ?a ?v) = _ => change (wk (set_gzhead a v)) with (wk a)
  | |- wk (set_gzindex ?a ?v) = _ => change (wk (set_gzindex a v)) with (wk a)
  | |- wk (set_hash_bits ?a ?v) = _ => change (wk (set_hash_bits a v)) with (wk a)
  | |- wk (set_hash_mask ?a ?v) = _ => change (wk (set_hash_mask a v)) with (wk a)
  | |- wk (set_hash_shift ?a ?v) = _ => change (wk (set_hash_shift a v)) with (wk a)
  | |- wk (set_head ?a ?v) = _ => change (wk (set_head a v)) with (wk a)
  | |- wk (set_heap ?a ?v) = _ => change (wk (set_heap a v)) with (wk a)
  | |- wk (set_heap_len ?a ?v) = _ => change (wk (set_heap_len a v)) with (wk a)
  | |- wk (set_heap_max ?a ?v) = _ => change (wk (set_heap_max a v)) with (wk a)
  | |- wk (set_high_water ?a ?v) = _ => change (wk (set_high_water a v)) with (wk a)
  | |- wk (set_ins_h ?a ?v) = _ => change (wk (set_ins_h a v)) with (wk a)
  | |- wk (set_insert ?a ?v) = _ => change (wk (set_insert a v)) with (wk a)
  | |- wk (set_l_max_code ?a ?v) = _ => change (wk (set_l_max_code a v)) with (wk a)
  | |- wk (set_last_flush ?a ?v) = _ => change (wk (set_last_flush a v)) with (wk a)
  | |- wk (set_level ?a ?v) = _ => change (wk (set_level a v)) with (wk a)
  | |- wk (set_lookahead ?a ?v) = _ => change (wk (set_lookahead a v)) with (wk a)
  | |- wk (set_match_available ?a ?v) = _ => change (wk (set_match_available a v)) with (wk a)
  | |- wk (set_match_length ?a ?v) = _ => change (wk (set_match_length a v)) with (wk a)
  | |- wk (set_match_start ?a ?v) = _ => change (wk (set_match_start a v)) with (wk a)
  | |- wk (set_matches ?a ?v) = _ => change (wk (set_matches a v)) with (wk a)
  | |- wk (set_max_chain_length ?a ?v) = _ => change (wk (set_max_chain_length a v)) with (wk a)
  | |- wk (set_max_lazy_match ?a ?v) = _ => change (wk (set_max_lazy_match a v)) with (wk a)
  | |- wk (set_method ?a ?v) = _ => change (wk (set_method a v)) with (wk a)
  | |- wk (set_nice_match ?a ?v) = _ => change (wk (set_nice_match a v)) with (wk a)
  | |- wk (set_opt_len ?a ?v) = _ => change (wk (set_opt_len a v)) with (wk a)
  | |- wk (set_pending ?a ?v) = _ => change (wk (set_pending a v)) with (wk a)
  | |- wk (set_pending_buf ?a ?v) = _ => change (wk (set_pending_buf a v)) with (wk a)
  | |- wk (set_pending_buf_size ?a ?v) = _ => change (wk (set_pending_buf_size a v)) with (wk a)
  | |- wk (set_pending_out ?a ?v) = _ => change (wk (set_pending_out a v)) with (wk a)
  | |- wk (set_prev ?a ?v) = _ => change (wk (set_prev a v)) with (wk a)
  | |- wk (set_prev_length ?a ?v) = _ => change (wk (set_prev_length a v)) with (wk a)
  | |- wk (set_prev_match ?a ?v) = _ => change (wk (set_prev_match a v)) with (wk a)
  | |- wk (set_static_len ?a ?v) = _ => change (wk (set_static_len a v)) with (wk a)
  | |- wk (set_status ?a ?v) = _ => change (wk (set_status a v)) with (wk a)
  | |- wk (set_strategy ?a ?v) = _ => change (wk (set_strategy a v)) with (wk a)
  | |- wk (set_strm ?a ?v) = _ => change (wk (set_strm a v)) with (wk a)
  | |- wk (set_strstart ?a ?v) = _ => change (wk (set_strstart a v)) with (wk a)
  | |- wk (set_sym_end ?a ?v) = _ => change (wk (set_sym_end a v)) with (wk a)
  | |- wk (set_sym_next ?a ?v) = _ => change (wk (set_sym_next a v)) with (wk a)
  | |- wk (set_w_bits ?a ?v) = _ => change (wk (set_w_bits a v)) with (wk a)
  | |- wk (set_w_mask ?a ?v) = _ => change (wk (set_w_mask a v)) with (wk a)
  | |- wk (set_window ?a ?v) = _ => change (wk (set_window a v)) with (wk a)
  | |- wk (set_window_size ?a ?v) = _ => change (wk (set_window_size a v)) with (wk a)
  | |- wk (set_wrap ?a ?v) = _ => change (wk (set_wrap a v)) with (wk a)
  | |- wk (put_byte ?a ?v) = _ => change (wk (put_byte a v)) with (wk a)
  | |- wk (putShortMSB ?a ?v) = _ => change (wk (putShortMSB a v)) with (wk a)
  | |- wk (set_tree_fc ?a ?v ?w) = _ => change (wk (set_tree_fc a v w)) with (wk a)
  | |- wk (set_tree_dl ?a ?v ?w) = _ => change (wk (set_tree_dl a v w)) with (wk a)
  | |- wk (set_max_code ?a ?v ?w) = _ => change (wk (set_max_code a v w)) with (wk a)
  | |- wk (sym_buf_set ?a ?v ?w) = _ => change (wk (sym_buf_set a v w)) with (wk a)
  | |- wk (set_Freq ?a ?v ?w ?x) = _ => change (wk (set_Freq a v w x)) with (wk a)
  | |- wk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_flush_block a x0 x1 x2))
  | |- wk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_stored_block a x0 x1 x2))
  | |- wk (tr_align ?a ) = _ => apply (eq_trans (wk_tr_align a ))
  | |- wk (flush_pending ?a ) = _ => apply (eq_trans (wk_flush_pending a ))
  | |- wk (bi_flush ?a ) = _ => apply (eq_trans (wk_bi_flush a ))
  | |- wk (clear_hash ?a ) = _ => apply (eq_trans (wk_clear_hash a ))
  | |- wk (slide_hash ?a ) = _ => apply (eq_trans (wk_slide_hash a ))
  | |- wk (fill_window ?a ) = _ => apply (eq_trans (wk_fill_window a ))
  | |- wk (flush_block_only ?a ?x0) = _ => apply (eq_trans (wk_flush_block_only a x0))
  | |- wk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (wk_tr_tally_lit a x0))
  | |- wk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_tr_tally_dist a x0 x1))
  | |- wk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (wk_insert_string a x0))
  | |- wk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_read_buf a x0 x1))
  | |- wk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (wk_longest_match a x0))
  | |- wk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (wk_fill_window_insert fu a x0))
  | |- wk (match ?t with pair _ _ => _ end) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (fst (match ?t with pair _ _ => _ end)) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (if ?c then _ else _) = _ => destruct c
  | |- wk (fst (if ?c then _ else _)) = _ => destruct c
  | |- wk ?y = wk _ => is_var y; assumption
  end.
Ltac wkgoC := repeat wkgoC1.

Lemma wk_flush_block : forall s last, wk (fst (flush_block s last)) = wk s.
Proof. intros. cbv beta delta [flush_block]. wkgoC. Qed.
Lemma wk_deflate_tail : forall s flush, wk (fst (deflate_tail s flush)) = wk s.
Proof. intros. cbv beta delta [deflate_tail]. wkgoC; apply (eq_trans (wk_flush_block _ _)); wkgoC. Qed.

Ltac wkgoD1 :=
  lazymatch goal with
  | |- wk ?x = wk ?x => reflexivity
  | |- wk (let x := ?t in @?E x) = wk ?s0 =>
      first [ is_var t; change (wk (E t) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (let x := ?t in @?E x)) = wk ?s0 =>
      first [ is_var t; change (wk (fst (E t)) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (?a, ?b)) = _ => change (wk (fst (a, b))) with (wk a)
  | |- wk (set_bi_buf ?a ?v) = _ => change (wk (set_bi_buf a v)) with (wk a)
  | |- wk (set_bi_valid ?a ?v) = _ => change (wk (set_bi_valid a v)) with (wk a)
  | |- wk (set_bl_count ?a ?v) = _ => change (wk (set_bl_count a v)) with (wk a)
  | |- wk (set_bl_max_code ?a ?v) = _ => change (wk (set_bl_max_code a v)) with (wk a)
  | |- wk (set_bl_tree_dl ?a ?v) = _ => change (wk (set_bl_tree_dl a v)) with (wk a)
  | |- wk (set_bl_tree_fc ?a ?v) = _ => change (wk (set_bl_tree_fc a v)) with (wk a)
  | |- wk (set_block_start ?a ?v) = _ => change (wk (set_block_start a v)) with (wk a)
  | |- wk (set_d_max_code ?a ?v) = _ => change (wk (set_d_max_code a v)) with (wk a)
  | |- wk (set_depth ?a ?v) = _ => change (wk (set_depth a v)) with (wk a)
  | |- wk (set_dyn_dtree_dl ?a ?v) = _ => change (wk (set_dyn_dtree_dl a v)) with (wk a)
  | |- wk (set_dyn_dtree_fc ?a ?v) = _ => change (wk (set_dyn_dtree_fc a v)) with (wk a)
  | |- wk (set_dyn_ltree_dl ?a ?v) = _ => change (wk (set_dyn_ltree_dl a v)) with (wk a)
  | |- wk (set_dyn_ltree_fc ?a ?v) = _ => change (wk (set_dyn_ltree_fc a v)) with (wk a)
  | |- wk (set_good_match ?a ?v) = _ => change (wk (set_good_match a v)) with (wk a)
  | |- wk (set_gzhead ?a ?v) = _ => change (wk (set_gzhead a v)) with (wk a)
  | |- wk (set_gzindex ?a ?v) = _ => change (wk (set_gzindex a v)) with (wk a)
  | |- wk (set_hash_bits ?a ?v) = _ => change (wk (set_hash_bits a v)) with (wk a)
  | |- wk (set_hash_mask ?a ?v) = _ => change (wk (set_hash_mask a v)) with (wk a)
  | |- wk (set_hash_shift ?a ?v) = _ => change (wk (set_hash_shift a v)) with (wk a)
  | |- wk (set_head ?a ?v) = _ => change (wk (set_head a v)) with (wk a)
  | |- wk (set_heap ?a ?v) = _ => change (wk (set_heap a v)) with (wk a)
  | |- wk (set_heap_len ?a ?v) = _ => change (wk (set_heap_len a v)) with (wk a)
  | |- wk (set_heap_max ?a ?v) = _ => change (wk (set_heap_max a v)) with (wk a)
  | |- wk (set_high_water ?a ?v) = _ => change (wk (set_high_water a v)) with (wk a)
  | |- wk (set_ins_h ?a ?v) = _ => change (wk (set_ins_h a v)) with (wk a)
  | |- wk (set_insert ?a ?v) = _ => change (wk (set_insert a v)) with (wk a)
  | |- wk (set_l_max_code ?a ?v) = _ => change (wk (set_l_max_code a v)) with (wk a)
  | |- wk (set_last_flush ?a ?v) = _ => change (wk (set_last_flush a v)) with (wk a)
  | |- wk (set_level ?a ?v) = _ => change (wk (set_level a v)) with (wk a)
  | |- wk (set_lookahead ?a ?v) = _ => change (wk (set_lookahead a v)) with (wk a)
  | |- wk (set_match_available ?a ?v) = _ => change (wk (set_match_available a v)) with (wk a)
  | |- wk (set_match_length ?a ?v) = _ => change (wk (set_match_length a v)) with (wk a)
  | |- wk (set_match_start ?a ?v) = _ => change (wk (set_match_start a v)) with (wk a)
  | |- wk (set_matches ?a ?v) = _ => change (wk (set_matches a v)) with (wk a)
  | |- wk (set_max_chain_length ?a ?v) = _ => change (wk (set_max_chain_length a v)) with (wk a)
  | |- wk (set_max_lazy_match ?a ?v) = _ => change (wk (set_max_lazy_match a v)) with (wk a)
  | |- wk (set_method ?a ?v) = _ => change (wk (set_method a v)) with (wk a)
  | |- wk (set_nice_match ?a ?v) = _ => change (wk (set_nice_match a v)) with (wk a)
  | |- wk (set_opt_len ?a ?v) = _ => change (wk (set_opt_len a v)) with (wk a)
  | |- wk (set_pending ?a ?v) = _ => change (wk (set_pending a v)) with (wk a)
  | |- wk (set_pending_buf ?a ?v) = _ => change (wk (set_pending_buf a v)) with (wk a)
  | |- wk (set_pending_buf_size ?a ?v) = _ => change (wk (set_pending_buf_size a v)) with (wk a)
  | |- wk (set_pending_out ?a ?v) = _ => change (wk (set_pending_out a v)) with (wk a)
  | |- wk (set_prev ?a ?v) = _ => change (wk (set_prev a v)) with (wk a)
  | |- wk (set_prev_length ?a ?v) = _ => change (wk (set_prev_length a v)) with (wk a)
  | |- wk (set_prev_match ?a ?v) = _ => change (wk (set_prev_match a v)) with (wk a)
  | |- wk (set_static_len ?a ?v) = _ => change (wk (set_static_len a v)) with (wk a)
  | |- wk (set_status ?a ?v) = _ => change (wk (set_status a v)) with (wk a)
  | |- wk (set_strategy ?a ?v) = _ => change (wk (set_strategy a v)) with (wk a)
  | |- wk (set_strm ?a ?v) = _ => change (wk (set_strm a v)) with (wk a)
  | |- wk (set_strstart ?a ?v) = _ => change (wk (set_strstart a v)) with (wk a)
  | |- wk (set_sym_end ?a ?v) = _ => change (wk (set_sym_end a v)) with (wk a)
  | |- wk (set_sym_next ?a ?v) = _ => change (wk (set_sym_next a v)) with (wk a)
  | |- wk (set_w_bits ?a ?v) = _ => change (wk (set_w_bits a v)) with (wk a)
  | |- wk (set_w_mask ?a ?v) = _ => change (wk (set_w_mask a v)) with (wk a)
  | |- wk (set_window ?a ?v) = _ => change (wk (set_window a v)) with (wk a)
  | |- wk (set_window_size ?a ?v) = _ => change (wk (set_window_size a v)) with (wk a)
  | |- wk (set_wrap ?a ?v) = _ => change (wk (set_wrap a v)) with (wk a)
  | |- wk (put_byte ?a ?v) = _ => change (wk (put_byte a v)) with (wk a)
  | |- wk (putShortMSB ?a ?v) = _ => change (wk (putShortMSB a v)) with (wk a)
  | |- wk (set_tree_fc ?a ?v ?w) = _ => change (wk (set_tree_fc a v w)) with (wk a)
  | |- wk (set_tree_dl ?a ?v ?w) = _ => change (wk (set_tree_dl a v w)) with (wk a)
  | |- wk (set_max_code ?a ?v ?w) = _ => change (wk (set_max_code a v w)) with (wk a)
  | |- wk (sym_buf_set ?a ?v ?w) = _ => change (wk (sym_buf_set a v w)) with (wk a)
  | |- wk (set_Freq ?a ?v ?w ?x) = _ => change (wk (set_Freq a v w x)) with (wk a)
  | |- wk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_flush_block a x0 x1 x2))
  | |- wk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_stored_block a x0 x1 x2))
  | |- wk (tr_align ?a ) = _ => apply (eq_trans (wk_tr_align a ))
  | |- wk (flush_pending ?a ) = _ => apply (eq_trans (wk_flush_pending a ))
  | |- wk (bi_flush ?a ) = _ => apply (eq_trans (wk_bi_flush a ))
  | |- wk (clear_hash ?a ) = _ => apply (eq_trans (wk_clear_hash a ))
  | |- wk (slide_hash ?a ) = _ => apply (eq_trans (wk_slide_hash a ))
  | |- wk (fill_window ?a ) = _ => apply (eq_trans (wk_fill_window a ))
  | |- wk (flush_block_only ?a ?x0) = _ => apply (eq_trans (wk_flush_block_only a x0))
  | |- wk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (wk_tr_tally_lit a x0))
  | |- wk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_tr_tally_dist a x0 x1))
  | |- wk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (wk_insert_string a x0))
  | |- wk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_read_buf a x0 x1))
  | |- wk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (wk_longest_match a x0))
  | |- wk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (wk_fill_window_insert fu a x0))
  | |- wk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (wk_flush_block a x0))
  | |- wk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (wk_deflate_tail a x0))
  | |- wk (match ?t with pair _ _ => _ end) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (fst (match ?t with pair _ _ => _ end)) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (if ?c then _ else _) = _ => destruct c
  | |- wk (fst (if ?c then _ else _)) = _ => destruct c
  | |- wk ?y = wk _ => is_var y; assumption
  end.
Ltac wkgoD := repeat wkgoD1.


Lemma wk_deflate_stored_body : forall s flush mb, wk (fst (fst (deflate_stored_body s flush mb))) = wk s.
Proof.
  intros. cbv beta delta [deflate_stored_body].
  repeat (wkgoD1
          || lazymatch goal with
             | |- wk (fst (fst (?a, ?b, ?c))) = _ => change (wk (fst (fst (a, b, c)))) with (wk a)
             | |- wk (fst (fst (if ?c then _ else _))) = _ => destruct c
             | |- wk (fst (fst (let x := ?t in @?E x))) = wk ?s0 =>
                 first [ is_var t; change (wk (fst (fst (E t))) = wk s0); cbv beta
                       | lazymatch type of t with
                         | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
                         | _ => generalize t; let y := fresh "v" in intros y
                         end ]
             | |- wk (fst (fst (match ?t with pair _ _ => _ end))) = wk ?s0 =>
                 let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
             end).
Qed.
Lemma wk_deflate_stored_loop : forall fuel s flush mb, wk (fst (deflate_stored_loop fuel s flush mb)) = wk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_stored_loop].
  pose proof (wk_deflate_stored_body s flush mb) as X. destruct (deflate_stored_body s flush mb) as [[s1 last] broke]. cbn [fst] in X.
  destruct broke; [exact X|]. destruct (last =? 0); [rewrite IH|]; exact X.
Qed.
Lemma wk_deflate_stored_used : forall s used, wk (deflate_stored_used s used) = wk s.
Proof. intros. cbv beta delta [deflate_stored_used]. wkgoD. Qed.
Lemma wk_deflate_stored_fin : forall s flush, wk (fst (deflate_stored_fin s flush)) = wk s.
Proof. intros. cbv beta delta [deflate_stored_fin]. wkgoD. Qed.
Lemma wk_deflate_stored_slide : forall s hv, wk (fst (deflate_stored_slide s hv)) = wk s.
Proof. intros. cbv beta delta [deflate_stored_slide]. wkgoD. Qed.

Ltac wkgoE1 :=
  lazymatch goal with
  | |- wk ?x = wk ?x => reflexivity
  | |- wk (let x := ?t in @?E x) = wk ?s0 =>
      first [ is_var t; change (wk (E t) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (let x := ?t in @?E x)) = wk ?s0 =>
      first [ is_var t; change (wk (fst (E t)) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (?a, ?b)) = _ => change (wk (fst (a, b))) with (wk a)
  | |- wk (set_bi_buf ?a ?v) = _ => change (wk (set_bi_buf a v)) with (wk a)
  | |- wk (set_bi_valid ?a ?v) = _ => change (wk (set_bi_valid a v)) with (wk a)
  | |- wk (set_bl_count ?a ?v) = _ => change (wk (set_bl_count a v)) with (wk a)
  | |- wk (set_bl_max_code ?a ?v) = _ => change (wk (set_bl_max_code a v)) with (wk a)
  | |- wk (set_bl_tree_dl ?a ?v) = _ => change (wk (set_bl_tree_dl a v)) with (wk a)
  | |- wk (set_bl_tree_fc ?a ?v) = _ => change (wk (set_bl_tree_fc a v)) with (wk a)
  | |- wk (set_block_start ?a ?v) = _ => change (wk (set_block_start a v)) with (wk a)
  | |- wk (set_d_max_code ?a ?v) = _ => change (wk (set_d_max_code a v)) with (wk a)
  | |- wk (set_depth ?a ?v) = _ => change (wk (set_depth a v)) with (wk a)
  | |- wk (set_dyn_dtree_dl ?a ?v) = _ => change (wk (set_dyn_dtree_dl a v)) with (wk a)
  | |- wk (set_dyn_dtree_fc ?a ?v) = _ => change (wk (set_dyn_dtree_fc a v)) with (wk a)
  | |- wk (set_dyn_ltree_dl ?a ?v) = _ => change (wk (set_dyn_ltree_dl a v)) with (wk a)
  | |- wk (set_dyn_ltree_fc ?a ?v) = _ => change (wk (set_dyn_ltree_fc a v)) with (wk a)
  | |- wk (set_good_match ?a ?v) = _ => change (wk (set_good_match a v)) with (wk a)
  | |- wk (set_gzhead ?a ?v) = _ => change (wk (set_gzhead a v)) with (wk a)
  | |- wk (set_gzindex ?a ?v) = _ => change (wk (set_gzindex a v)) with (wk a)
  | |- wk (set_hash_bits ?a ?v) = _ => change (wk (set_hash_bits a v)) with (wk a)
  | |- wk (set_hash_mask ?a ?v) = _ => change (wk (set_hash_mask a v)) with (wk a)
  | |- wk (set_hash_shift ?a ?v) = _ => change (wk (set_hash_shift a v)) with (wk a)
  | |- wk (set_head ?a ?v) = _ => change (wk (set_head a v)) with (wk a)
  | |- wk (set_heap ?a ?v) = _ => change (wk (set_heap a v)) with (wk a)
  | |- wk (set_heap_len ?a ?v) = _ => change (wk (set_heap_len a v)) with (wk a)
  | |- wk (set_heap_max ?a ?v) = _ => change (wk (set_heap_max a v)) with (wk a)
  | |- wk (set_high_water ?a ?v) = _ => change (wk (set_high_water a v)) with (wk a)
  | |- wk (set_ins_h ?a ?v) = _ => change (wk (set_ins_h a v)) with (wk a)
  | |- wk (set_insert ?a ?v) = _ => change (wk (set_insert a v)) with (wk a)
  | |- wk (set_l_max_code ?a ?v) = _ => change (wk (set_l_max_code a v)) with (wk a)
  | |- wk (set_last_flush ?a ?v) = _ => change (wk (set_last_flush a v)) with (wk a)
  | |- wk (set_level ?a ?v) = _ => change (wk (set_level a v)) with (wk a)
  | |- wk (set_lookahead ?a ?v) = _ => change (wk (set_lookahead a v)) with (wk a)
  | |- wk (set_match_available ?a ?v) = _ => change (wk (set_match_available a v)) with (wk a)
  | |- wk (set_match_length ?a ?v) = _ => change (wk (set_match_length a v)) with (wk a)
  | |- wk (set_match_start ?a ?v) = _ => change (wk (set_match_start a v)) with (wk a)
  | |- wk (set_matches ?a ?v) = _ => change (wk (set_matches a v)) with (wk a)
  | |- wk (set_max_chain_length ?a ?v) = _ => change (wk (set_max_chain_length a v)) with (wk a)
  | |- wk (set_max_lazy_match ?a ?v) = _ => change (wk (set_max_lazy_match a v)) with (wk a)
  | |- wk (set_method ?a ?v) = _ => change (wk (set_method a v)) with (wk a)
  | |- wk (set_nice_match ?a ?v) = _ => change (wk (set_nice_match a v)) with (wk a)
  | |- wk (set_opt_len ?a ?v) = _ => change (wk (set_opt_len a v)) with (wk a)
  | |- wk (set_pending ?a ?v) = _ => change (wk (set_pending a v)) with (wk a)
  | |- wk (set_pending_buf ?a ?v) = _ => change (wk (set_pending_buf a v)) with (wk a)
  | |- wk (set_pending_buf_size ?a ?v) = _ => change (wk (set_pending_buf_size a v)) with (wk a)
  | |- wk (set_pending_out ?a ?v) = _ => change (wk (set_pending_out a v)) with (wk a)
  | |- wk (set_prev ?a ?v) = _ => change (wk (set_prev a v)) with (wk a)
  | |- wk (set_prev_length ?a ?v) = _ => change (wk (set_prev_length a v)) with (wk a)
  | |- wk (set_prev_match ?a ?v) = _ => change (wk (set_prev_match a v)) with (wk a)
  | |- wk (set_static_len ?a ?v) = _ => change (wk (set_static_len a v)) with (wk a)
  | |- wk (set_status ?a ?v) = _ => change (wk (set_status a v)) with (wk a)
  | |- wk (set_strategy ?a ?v) = _ => change (wk (set_strategy a v)) with (wk a)
  | |- wk (set_strm ?a ?v) = _ => change (wk (set_strm a v)) with (wk a)
  | |- wk (set_strstart ?a ?v) = _ => change (wk (set_strstart a v)) with (wk a)
  | |- wk (set_sym_end ?a ?v) = _ => change (wk (set_sym_end a v)) with (wk a)
  | |- wk (set_sym_next ?a ?v) = _ => change (wk (set_sym_next a v)) with (wk a)
  | |- wk (set_w_bits ?a ?v) = _ => change (wk (set_w_bits a v)) with (wk a)
  | |- wk (set_w_mask ?a ?v) = _ => change (wk (set_w_mask a v)) with (wk a)
  | |- wk (set_window ?a ?v) = _ => change (wk (set_window a v)) with (wk a)
  | |- wk (set_window_size ?a ?v) = _ => change (wk (set_window_size a v)) with (wk a)
  | |- wk (set_wrap ?a ?v) = _ => change (wk (set_wrap a v)) with (wk a)
  | |- wk (put_byte ?a ?v) = _ => change (wk (put_byte a v)) with (wk a)
  | |- wk (putShortMSB ?a ?v) = _ => change (wk (putShortMSB a v)) with (wk a)
  | |- wk (set_tree_fc ?a ?v ?w) = _ => change (wk (set_tree_fc a v w)) with (wk a)
  | |- wk (set_tree_dl ?a ?v ?w) = _ => change (wk (set_tree_dl a v w)) with (wk a)
  | |- wk (set_max_code ?a ?v ?w) = _ => change (wk (set_max_code a v w)) with (wk a)
  | |- wk (sym_buf_set ?a ?v ?w) = _ => change (wk (sym_buf_set a v w)) with (wk a)
  | |- wk (set_Freq ?a ?v ?w ?x) = _ => change (wk (set_Freq a v w x)) with (wk a)
  | |- wk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_flush_block a x0 x1 x2))
  | |- wk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_stored_block a x0 x1 x2))
  | |- wk (tr_align ?a ) = _ => apply (eq_trans (wk_tr_align a ))
  | |- wk (flush_pending ?a ) = _ => apply (eq_trans (wk_flush_pending a ))
  | |- wk (bi_flush ?a ) = _ => apply (eq_trans (wk_bi_flush a ))
  | |- wk (clear_hash ?a ) = _ => apply (eq_trans (wk_clear_hash a ))
  | |- wk (slide_hash ?a ) = _ => apply (eq_trans (wk_slide_hash a ))
  | |- wk (fill_window ?a ) = _ => apply (eq_trans (wk_fill_window a ))
  | |- wk (flush_block_only ?a ?x0) = _ => apply (eq_trans (wk_flush_block_only a x0))
  | |- wk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (wk_tr_tally_lit a x0))
  | |- wk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_tr_tally_dist a x0 x1))
  | |- wk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (wk_insert_string a x0))
  | |- wk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_read_buf a x0 x1))
  | |- wk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (wk_longest_match a x0))
  | |- wk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (wk_fill_window_insert fu a x0))
  | |- wk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (wk_flush_block a x0))
  | |- wk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (wk_deflate_tail a x0))
  | |- wk (deflate_stored_used ?a ?x0) = _ => apply (eq_trans (wk_deflate_stored_used a x0))
  | |- wk (fst (deflate_stored_fin ?a ?x0)) = _ => apply (eq_trans (wk_deflate_stored_fin a x0))
  | |- wk (fst (deflate_stored_slide ?a ?x0)) = _ => apply (eq_trans (wk_deflate_stored_slide a x0))
  | |- wk (fst (deflate_stored_loop ?fu ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_deflate_stored_loop fu a x0 x1))
  | |- wk (match ?t with pair _ _ => _ end) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (fst (match ?t with pair _ _ => _ end)) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (if ?c then _ else _) = _ => destruct c
  | |- wk (fst (if ?c then _ else _)) = _ => destruct c
  | |- wk ?y = wk _ => is_var y; assumption
  end.
Ltac wkgoE := repeat wkgoE1.

Lemma wk_deflate_stored_mid : forall s flush, wk (fst (deflate_stored_mid s flush)) = wk s.
Proof. intros. cbv beta delta [deflate_stored_mid]. wkgoE. Qed.
Lemma wk_deflate_stored : forall s flush, wk (fst (deflate_stored s flush)) = wk s.
Proof.
  intros. cbv beta delta [deflate_stored]. wkgoE; apply (eq_trans (wk_deflate_stored_mid _ _)); wkgoE.
Qed.

Lemma wk_deflate_fast_insert : forall f s, wk (deflate_fast_insert f s) = wk s.
Proof.
  induction f as [|f IH]; intros s; [reflexivity|]. cbn [deflate_fast_insert].
  wkgoE; apply (eq_trans (IH _)); wkgoE.
Qed.
Lemma wk_deflate_slow_insert : forall f s mi, wk (deflate_slow_insert f s mi) = wk s.
Proof.
  induction f as [|f IH]; intros s mi; [reflexivity|]. cbn [deflate_slow_insert].
  wkgoE; apply (eq_trans (IH _ _)); wkgoE.
Qed.

Ltac wkgoF1 :=
  lazymatch goal with
  | |- wk ?x = wk ?x => reflexivity
  | |- wk (let x := ?t in @?E x) = wk ?s0 =>
      first [ is_var t; change (wk (E t) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (let x := ?t in @?E x)) = wk ?s0 =>
      first [ is_var t; change (wk (fst (E t)) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (?a, ?b)) = _ => change (wk (fst (a, b))) with (wk a)
  | |- wk (set_bi_buf ?a ?v) = _ => change (wk (set_bi_buf a v)) with (wk a)
  | |- wk (set_bi_valid ?a ?v) = _ => change (wk (set_bi_valid a v)) with (wk a)
  | |- wk (set_bl_count ?a ?v) = _ => change (wk (set_bl_count a v)) with (wk a)
  | |- wk (set_bl_max_code ?a ?v) = _ => change (wk (set_bl_max_code a v)) with (wk a)
  | |- wk (set_bl_tree_dl ?a ?v) = _ => change (wk (set_bl_tree_dl a v)) with (wk a)
  | |- wk (set_bl_tree_fc ?a ?v) = _ => change (wk (set_bl_tree_fc a v)) with (wk a)
  | |- wk (set_block_start ?a ?v) = _ => change (wk (set_block_start a v)) with (wk a)
  | |- wk (set_d_max_code ?a ?v) = _ => change (wk (set_d_max_code a v)) with (wk a)
  | |- wk (set_depth ?a ?v) = _ => change (wk (set_depth a v)) with (wk a)
  | |- wk (set_dyn_dtree_dl ?a ?v) = _ => change (wk (set_dyn_dtree_dl a v)) with (wk a)
  | |- wk (set_dyn_dtree_fc ?a ?v) = _ => change (wk (set_dyn_dtree_fc a v)) with (wk a)
  | |- wk (set_dyn_ltree_dl ?a ?v) = _ => change (wk (set_dyn_ltree_dl a v)) with (wk a)
  | |- wk (set_dyn_ltree_fc ?a ?v) = _ => change (wk (set_dyn_ltree_fc a v)) with (wk a)
  | |- wk (set_good_match ?a ?v) = _ => change (wk (set_good_match a v)) with (wk a)
  | |- wk (set_gzhead ?a ?v) = _ => change (wk (set_gzhead a v)) with (wk a)
  | |- wk (set_gzindex ?a ?v) = _ => change (wk (set_gzindex a v)) with (wk a)
  | |- wk (set_hash_bits ?a ?v) = _ => change (wk (set_hash_bits a v)) with (wk a)
  | |- wk (set_hash_mask ?a ?v) = _ => change (wk (set_hash_mask a v)) with (wk a)
  | |- wk (set_hash_shift ?a ?v) = _ => change (wk (set_hash_shift a v)) with (wk a)
  | |- wk (set_head ?a ?v) = _ => change (wk (set_head a v)) with (wk a)
  | |- wk (set_heap ?a ?v) = _ => change (wk (set_heap a v)) with (wk a)
  | |- wk (set_heap_len ?a ?v) = _ => change (wk (set_heap_len a v)) with (wk a)
  | |- wk (set_heap_max ?a ?v) = _ => change (wk (set_heap_max a v)) with (wk a)
  | |- wk (set_high_water ?a ?v) = _ => change (wk (set_high_water a v)) with (wk a)
  | |- wk (set_ins_h ?a ?v) = _ => change (wk (set_ins_h a v)) with (wk a)
  | |- wk (set_insert ?a ?v) = _ => change (wk (set_insert a v)) with (wk a)
  | |- wk (set_l_max_code ?a ?v) = _ => change (wk (set_l_max_code a v)) with (wk a)
  | |- wk (set_last_flush ?a ?v) = _ => change (wk (set_last_flush a v)) with (wk a)
  | |- wk (set_level ?a ?v) = _ => change (wk (set_level a v)) with (wk a)
  | |- wk (set_lookahead ?a ?v) = _ => change (wk (set_lookahead a v)) with (wk a)
  | |- wk (set_match_available ?a ?v) = _ => change (wk (set_match_available a v)) with (wk a)
  | |- wk (set_match_length ?a ?v) = _ => change (wk (set_match_length a v)) with (wk a)
  | |- wk (set_match_start ?a ?v) = _ => change (wk (set_match_start a v)) with (wk a)
  | |- wk (set_matches ?a ?v) = _ => change (wk (set_matches a v)) with (wk a)
  | |- wk (set_max_chain_length ?a ?v) = _ => change (wk (set_max_chain_length a v)) with (wk a)
  | |- wk (set_max_lazy_match ?a ?v) = _ => change (wk (set_max_lazy_match a v)) with (wk a)
  | |- wk (set_method ?a ?v) = _ => change (wk (set_method a v)) with (wk a)
  | |- wk (set_nice_match ?a ?v) = _ => change (wk (set_nice_match a v)) with (wk a)
  | |- wk (set_opt_len ?a ?v) = _ => change (wk (set_opt_len a v)) with (wk a)
  | |- wk (set_pending ?a ?v) = _ => change (wk (set_pending a v)) with (wk a)
  | |- wk (set_pending_buf ?a ?v) = _ => change (wk (set_pending_buf a v)) with (wk a)
  | |- wk (set_pending_buf_size ?a ?v) = _ => change (wk (set_pending_buf_size a v)) with (wk a)
  | |- wk (set_pending_out ?a ?v) = _ => change (wk (set_pending_out a v)) with (wk a)
  | |- wk (set_prev ?a ?v) = _ => change (wk (set_prev a v)) with (wk a)
  | |- wk (set_prev_length ?a ?v) = _ => change (wk (set_prev_length a v)) with (wk a)
  | |- wk (set_prev_match ?a ?v) = _ => change (wk (set_prev_match a v)) with (wk a)
  | |- wk (set_static_len ?a ?v) = _ => change (wk (set_static_len a v)) with (wk a)
  | |- wk (set_status ?a ?v) = _ => change (wk (set_status a v)) with (wk a)
  | |- wk (set_strategy ?a ?v) = _ => change (wk (set_strategy a v)) with (wk a)
  | |- wk (set_strm ?a ?v) = _ => change (wk (set_strm a v)) with (wk a)
  | |- wk (set_strstart ?a ?v) = _ => change (wk (set_strstart a v)) with (wk a)
  | |- wk (set_sym_end ?a ?v) = _ => change (wk (set_sym_end a v)) with (wk a)
  | |- wk (set_sym_next ?a ?v) = _ => change (wk (set_sym_next a v)) with (wk a)
  | |- wk (set_w_bits ?a ?v) = _ => change (wk (set_w_bits a v)) with (wk a)
  | |- wk (set_w_mask ?a ?v) = _ => change (wk (set_w_mask a v)) with (wk a)
  | |- wk (set_window ?a ?v) = _ => change (wk (set_window a v)) with (wk a)
  | |- wk (set_window_size ?a ?v) = _ => change (wk (set_window_size a v)) with (wk a)
  | |- wk (set_wrap ?a ?v) = _ => change (wk (set_wrap a v)) with (wk a)
  | |- wk (put_byte ?a ?v) = _ => change (wk (put_byte a v)) with (wk a)
  | |- wk (putShortMSB ?a ?v) = _ => change (wk (putShortMSB a v)) with (wk a)
  | |- wk (set_tree_fc ?a ?v ?w) = _ => change (wk (set_tree_fc a v w)) with (wk a)
  | |- wk (set_tree_dl ?a ?v ?w) = _ => change (wk (set_tree_dl a v w)) with (wk a)
  | |- wk (set_max_code ?a ?v ?w) = _ => change (wk (set_max_code a v w)) with (wk a)
  | |- wk (sym_buf_set ?a ?v ?w) = _ => change (wk (sym_buf_set a v w)) with (wk a)
  | |- wk (set_Freq ?a ?v ?w ?x) = _ => change (wk (set_Freq a v w x)) with (wk a)
  | |- wk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_flush_block a x0 x1 x2))
  | |- wk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_stored_block a x0 x1 x2))
  | |- wk (tr_align ?a ) = _ => apply (eq_trans (wk_tr_align a ))
  | |- wk (flush_pending ?a ) = _ => apply (eq_trans (wk_flush_pending a ))
  | |- wk (bi_flush ?a ) = _ => apply (eq_trans (wk_bi_flush a ))
  | |- wk (clear_hash ?a ) = _ => apply (eq_trans (wk_clear_hash a ))
  | |- wk (slide_hash ?a ) = _ => apply (eq_trans (wk_slide_hash a ))
  | |- wk (fill_window ?a ) = _ => apply (eq_trans (wk_fill_window a ))
  | |- wk (flush_block_only ?a ?x0) = _ => apply (eq_trans (wk_flush_block_only a x0))
  | |- wk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (wk_tr_tally_lit a x0))
  | |- wk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_tr_tally_dist a x0 x1))
  | |- wk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (wk_insert_string a x0))
  | |- wk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_read_buf a x0 x1))
  | |- wk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (wk_longest_match a x0))
  | |- wk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (wk_fill_window_insert fu a x0))
  | |- wk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (wk_flush_block a x0))
  | |- wk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (wk_deflate_tail a x0))
  | |- wk (deflate_stored_used ?a ?x0) = _ => apply (eq_trans (wk_deflate_stored_used a x0))
  | |- wk (fst (deflate_stored_fin ?a ?x0)) = _ => apply (eq_trans (wk_deflate_stored_fin a x0))
  | |- wk (fst (deflate_stored_slide ?a ?x0)) = _ => apply (eq_trans (wk_deflate_stored_slide a x0))
  | |- wk (fst (deflate_stored_loop ?fu ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_deflate_stored_loop fu a x0 x1))
  | |- wk (deflate_fast_insert ?fu ?a) = _ => apply (eq_trans (wk_deflate_fast_insert fu a))
  | |- wk (deflate_slow_insert ?fu ?a ?x0) = _ => apply (eq_trans (wk_deflate_slow_insert fu a x0))
  | |- wk (match ?t with pair _ _ => _ end) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (fst (match ?t with pair _ _ => _ end)) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (if ?c then _ else _) = _ => destruct c
  | |- wk (fst (if ?c then _ else _)) = _ => destruct c
  | |- wk ?y = wk _ => is_var y; assumption
  end.
Ltac wkgoF := repeat wkgoF1.

Lemma wk_deflate_fast_body : forall s flush, wk (fst (deflate_fast_body s flush)) = wk s.
Proof. intros. cbv beta delta [deflate_fast_body]. wkgoF. Qed.
Lemma wk_deflate_slow_body : forall s flush, wk (fst (deflate_slow_body s flush)) = wk s.
Proof. intros. cbv beta delta [deflate_slow_body]. wkgoF. Qed.
Lemma wk_deflate_huff_body : forall s flush, wk (fst (deflate_huff_body s flush)) = wk s.
Proof. intros. cbv beta delta [deflate_huff_body]. wkgoF. Qed.
Lemma wk_deflate_rle_body : forall s flush, wk (fst (deflate_rle_body s flush)) = wk s.
Proof. intros. cbv beta delta [deflate_rle_body]. wkgoF. Qed.

Lemma wk_deflate_fast_loop : forall fuel s flush, wk (fst (deflate_fast_loop fuel s flush)) = wk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_fast_loop].
  pose proof (wk_deflate_fast_body s flush) as X. destruct (deflate_fast_body s flush) as [s1 o]. cbn [fst] in X.
  destruct o; cbn [fst]; [rewrite IH; exact X | exact X | exact X].
Qed.
Lemma wk_deflate_slow_loop : forall fuel s flush, wk (fst (deflate_slow_loop fuel s flush)) = wk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_slow_loop].
  pose proof (wk_deflate_slow_body s flush) as X. destruct (deflate_slow_body s flush) as [s1 o]. cbn [fst] in X.
  destruct o; cbn [fst]; [rewrite IH; exact X | exact X | exact X].
Qed.
Lemma wk_deflate_huff_loop : forall fuel s flush, wk (fst (deflate_huff_loop fuel s flush)) = wk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_huff_loop].
  pose proof (wk_deflate_huff_body s flush) as X. destruct (deflate_huff_body s flush) as [s1 o]. cbn [fst] in X.
  destruct o; cbn [fst]; [rewrite IH; exact X | exact X | exact X].
Qed.
Lemma wk_deflate_rle_loop : forall fuel s flush, wk (fst (deflate_rle_loop fuel s flush)) = wk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_rle_loop].
  pose proof (wk_deflate_rle_body s flush) as X. destruct (deflate_rle_body s flush) as [s1 o]. cbn [fst] in X.
  destruct o; cbn [fst]; [rewrite IH; exact X | exact X | exact X].
Qed.

Ltac wkgoG1 :=
  lazymatch goal with
  | |- wk ?x = wk ?x => reflexivity
  | |- wk (let x := ?t in @?E x) = wk ?s0 =>
      first [ is_var t; change (wk (E t) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (let x := ?t in @?E x)) = wk ?s0 =>
      first [ is_var t; change (wk (fst (E t)) = wk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hwk" in assert (H : wk t = wk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- wk (fst (?a, ?b)) = _ => change (wk (fst (a, b))) with (wk a)
  | |- wk (set_bi_buf ?a ?v) = _ => change (wk (set_bi_buf a v)) with (wk a)
  | |- wk (set_bi_valid ?a ?v) = _ => change (wk (set_bi_valid a v)) with (wk a)
  | |- wk (set_bl_count ?a ?v) = _ => change (wk (set_bl_count a v)) with (wk a)
  | |- wk (set_bl_max_code ?a ?v) = _ => change (wk (set_bl_max_code a v)) with (wk a)
  | |- wk (set_bl_tree_dl ?a ?v) = _ => change (wk (set_bl_tree_dl a v)) with (wk a)
  | |- wk (set_bl_tree_fc ?a ?v) = _ => change (wk (set_bl_tree_fc a v)) with (wk a)
  | |- wk (set_block_start ?a ?v) = _ => change (wk (set_block_start a v)) with (wk a)
  | |- wk (set_d_max_code ?a ?v) = _ => change (wk (set_d_max_code a v)) with (wk a)
  | |- wk (set_depth ?a ?v) = _ => change (wk (set_depth a v)) with (wk a)
  | |- wk (set_dyn_dtree_dl ?a ?v) = _ => change (wk (set_dyn_dtree_dl a v)) with (wk a)
  | |- wk (set_dyn_dtree_fc ?a ?v) = _ => change (wk (set_dyn_dtree_fc a v)) with (wk a)
  | |- wk (set_dyn_ltree_dl ?a ?v) = _ => change (wk (set_dyn_ltree_dl a v)) with (wk a)
  | |- wk (set_dyn_ltree_fc ?a ?v) = _ => change (wk (set_dyn_ltree_fc a v)) with (wk a)
  | |- wk (set_good_match ?a ?v) = _ => change (wk (set_good_match a v)) with (wk a)
  | |- wk (set_gzhead ?a ?v) = _ => change (wk (set_gzhead a v)) with (wk a)
  | |- wk (set_gzindex ?a ?v) = _ => change (wk (set_gzindex a v)) with (wk a)
  | |- wk (set_hash_bits ?a ?v) = _ => change (wk (set_hash_bits a v)) with (wk a)
  | |- wk (set_hash_mask ?a ?v) = _ => change (wk (set_hash_mask a v)) with (wk a)
  | |- wk (set_hash_shift ?a ?v) = _ => change (wk (set_hash_shift a v)) with (wk a)
  | |- wk (set_head ?a ?v) = _ => change (wk (set_head a v)) with (wk a)
  | |- wk (set_heap ?a ?v) = _ => change (wk (set_heap a v)) with (wk a)
  | |- wk (set_heap_len ?a ?v) = _ => change (wk (set_heap_len a v)) with (wk a)
  | |- wk (set_heap_max ?a ?v) = _ => change (wk (set_heap_max a v)) with (wk a)
  | |- wk (set_high_water ?a ?v) = _ => change (wk (set_high_water a v)) with (wk a)
  | |- wk (set_ins_h ?a ?v) = _ => change (wk (set_ins_h a v)) with (wk a)
  | |- wk (set_insert ?a ?v) = _ => change (wk (set_insert a v)) with (wk a)
  | |- wk (set_l_max_code ?a ?v) = _ => change (wk (set_l_max_code a v)) with (wk a)
  | |- wk (set_last_flush ?a ?v) = _ => change (wk (set_last_flush a v)) with (wk a)
  | |- wk (set_level ?a ?v) = _ => change (wk (set_level a v)) with (wk a)
  | |- wk (set_lookahead ?a ?v) = _ => change (wk (set_lookahead a v)) with (wk a)
  | |- wk (set_match_available ?a ?v) = _ => change (wk (set_match_available a v)) with (wk a)
  | |- wk (set_match_length ?a ?v) = _ => change (wk (set_match_length a v)) with (wk a)
  | |- wk (set_match_start ?a ?v) = _ => change (wk (set_match_start a v)) with (wk a)
  | |- wk (set_matches ?a ?v) = _ => change (wk (set_matches a v)) with (wk a)
  | |- wk (set_max_chain_length ?a ?v) = _ => change (wk (set_max_chain_length a v)) with (wk a)
  | |- wk (set_max_lazy_match ?a ?v) = _ => change (wk (set_max_lazy_match a v)) with (wk a)
  | |- wk (set_method ?a ?v) = _ => change (wk (set_method a v)) with (wk a)
  | |- wk (set_nice_match ?a ?v) = _ => change (wk (set_nice_match a v)) with (wk a)
  | |- wk (set_opt_len ?a ?v) = _ => change (wk (set_opt_len a v)) with (wk a)
  | |- wk (set_pending ?a ?v) = _ => change (wk (set_pending a v)) with (wk a)
  | |- wk (set_pending_buf ?a ?v) = _ => change (wk (set_pending_buf a v)) with (wk a)
  | |- wk (set_pending_buf_size ?a ?v) = _ => change (wk (set_pending_buf_size a v)) with (wk a)
  | |- wk (set_pending_out ?a ?v) = _ => change (wk (set_pending_out a v)) with (wk a)
  | |- wk (set_prev ?a ?v) = _ => change (wk (set_prev a v)) with (wk a)
  | |- wk (set_prev_length ?a ?v) = _ => change (wk (set_prev_length a v)) with (wk a)
  | |- wk (set_prev_match ?a ?v) = _ => change (wk (set_prev_match a v)) with (wk a)
  | |- wk (set_static_len ?a ?v) = _ => change (wk (set_static_len a v)) with (wk a)
  | |- wk (set_status ?a ?v) = _ => change (wk (set_status a v)) with (wk a)
  | |- wk (set_strategy ?a ?v) = _ => change (wk (set_strategy a v)) with (wk a)
  | |- wk (set_strm ?a ?v) = _ => change (wk (set_strm a v)) with (wk a)
  | |- wk (set_strstart ?a ?v) = _ => change (wk (set_strstart a v)) with (wk a)
  | |- wk (set_sym_end ?a ?v) = _ => change (wk (set_sym_end a v)) with (wk a)
  | |- wk (set_sym_next ?a ?v) = _ => change (wk (set_sym_next a v)) with (wk a)
  | |- wk (set_w_bits ?a ?v) = _ => change (wk (set_w_bits a v)) with (wk a)
  | |- wk (set_w_mask ?a ?v) = _ => change (wk (set_w_mask a v)) with (wk a)
  | |- wk (set_window ?a ?v) = _ => change (wk (set_window a v)) with (wk a)
  | |- wk (set_window_size ?a ?v) = _ => change (wk (set_window_size a v)) with (wk a)
  | |- wk (set_wrap ?a ?v) = _ => change (wk (set_wrap a v)) with (wk a)
  | |- wk (put_byte ?a ?v) = _ => change (wk (put_byte a v)) with (wk a)
  | |- wk (putShortMSB ?a ?v) = _ => change (wk (putShortMSB a v)) with (wk a)
  | |- wk (set_tree_fc ?a ?v ?w) = _ => change (wk (set_tree_fc a v w)) with (wk a)
  | |- wk (set_tree_dl ?a ?v ?w) = _ => change (wk (set_tree_dl a v w)) with (wk a)
  | |- wk (set_max_code ?a ?v ?w) = _ => change (wk (set_max_code a v w)) with (wk a)
  | |- wk (sym_buf_set ?a ?v ?w) = _ => change (wk (sym_buf_set a v w)) with (wk a)
  | |- wk (set_Freq ?a ?v ?w ?x) = _ => change (wk (set_Freq a v w x)) with (wk a)
  | |- wk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_flush_block a x0 x1 x2))
  | |- wk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (wk_tr_stored_block a x0 x1 x2))
  | |- wk (tr_align ?a ) = _ => apply (eq_trans (wk_tr_align a ))
  | |- wk (flush_pending ?a ) = _ => apply (eq_trans (wk_flush_pending a ))
  | |- wk (bi_flush ?a ) = _ => apply (eq_trans (wk_bi_flush a ))
  | |- wk (clear_hash ?a ) = _ => apply (eq_trans (wk_clear_hash a ))
  | |- wk (slide_hash ?a ) = _ => apply (eq_trans (wk_slide_hash a ))
  | |- wk (fill_window ?a ) = _ => apply (eq_trans (wk_fill_window a ))
  | |- wk (flush_block_only ?a ?x0) = _ => apply (eq_trans (wk_flush_block_only a x0))
  | |- wk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (wk_tr_tally_lit a x0))
  | |- wk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_tr_tally_dist a x0 x1))
  | |- wk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (wk_insert_string a x0))
  | |- wk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_read_buf a x0 x1))
  | |- wk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (wk_longest_match a x0))
  | |- wk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (wk_fill_window_insert fu a x0))
  | |- wk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (wk_flush_block a x0))
  | |- wk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (wk_deflate_tail a x0))
  | |- wk (deflate_stored_used ?a ?x0) = _ => apply (eq_trans (wk_deflate_stored_used a x0))
  | |- wk (fst (deflate_stored_fin ?a ?x0)) = _ => apply (eq_trans (wk_deflate_stored_fin a x0))
  | |- wk (fst (deflate_stored_slide ?a ?x0)) = _ => apply (eq_trans (wk_deflate_stored_slide a x0))
  | |- wk (fst (deflate_stored_loop ?fu ?a ?x0 ?x1)) = _ => apply (eq_trans (wk_deflate_stored_loop fu a x0 x1))
  | |- wk (deflate_fast_insert ?fu ?a) = _ => apply (eq_trans (wk_deflate_fast_insert fu a))
  | |- wk (deflate_slow_insert ?fu ?a ?x0) = _ => apply (eq_trans (wk_deflate_slow_insert fu a x0))
  | |- wk (fst (deflate_fast_loop ?fu ?a ?x0)) = _ => apply (eq_trans (wk_deflate_fast_loop fu a x0))
  | |- wk (fst (deflate_slow_loop ?fu ?a ?x0)) = _ => apply (eq_trans (wk_deflate_slow_loop fu a x0))
  | |- wk (fst (deflate_huff_loop ?fu ?a ?x0)) = _ => apply (eq_trans (wk_deflate_huff_loop fu a x0))
  | |- wk (fst (deflate_rle_loop ?fu ?a ?x0)) = _ => apply (eq_trans (wk_deflate_rle_loop fu a x0))
  | |- wk (fst (deflate_stored ?a ?x0)) = _ => apply (eq_trans (wk_deflate_stored a x0))
  | |- wk (match ?t with pair _ _ => _ end) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (fst (match ?t with pair _ _ => _ end)) = wk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hwk" in assert (H : wk (fst t) = wk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- wk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- wk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- wk (if ?c then _ else _) = _ => destruct c
  | |- wk (fst (if ?c then _ else _)) = _ => destruct c
  | |- wk ?y = wk _ => is_var y; assumption
  end.
Ltac wkgoG := repeat wkgoG1.

Lemma wk_deflate_slow : forall s flush, wk (fst (deflate_slow s flush)) = wk s.
Proof. intros. cbv beta delta [deflate_slow]. wkgoG. Qed.
