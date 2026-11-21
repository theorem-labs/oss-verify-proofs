(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateInvKeep DeflateSetters.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import RefDeflatePost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition bk (s : deflate_state) :=
  (ds_self_blk s, ds_window_blk s, ds_prev_blk s, ds_head_blk s, ds_pending_buf_blk s, ds_w_size s, ds_hash_size s, ds_lit_bufsize s).

Lemma dkeep_of_bk : forall s0 s1, bk s1 = bk s0 -> dkeep s0 s1.
Proof. intros s0 s1 E. unfold bk in E. injection E as E1 E2 E3 E4 E5 E6 E7 E8. unfold dkeep. repeat split; assumption. Qed.

Lemma bk_kp : forall a b, kproj a = kproj b -> bk a = bk b.
Proof.
  intros a b K. unfold bk.
  rewrite (kp_self_blk _ _ K), (kp_window_blk _ _ K), (kp_prev_blk _ _ K), (kp_head_blk _ _ K), (kp_pending_buf_blk _ _ K),
          (kp_w_size _ _ K), (kp_hash_size _ _ K), (kp_lit_bufsize _ _ K). reflexivity.
Qed.

Lemma bk_tr_tally_lit : forall s c, bk (fst (tr_tally_lit s c)) = bk s.
Proof. intros s c. rewrite (bk_kp _ _ (kp_tr_tally_lit s c)). reflexivity. Qed.
Lemma bk_tr_tally_dist : forall s d l, bk (fst (tr_tally_dist s d l)) = bk s.
Proof. intros s d l. rewrite (bk_kp _ _ (kp_tr_tally_dist s d l)). reflexivity. Qed.
Lemma bk_tr_flush_block : forall s buf len last, bk (tr_flush_block s buf len last) = bk s.
Proof. intros. exact (bk_kp _ _ (kp_tr_flush_block s buf len last)). Qed.
Lemma bk_tr_stored_block : forall s buf len last, bk (tr_stored_block s buf len last) = bk s.
Proof. intros. exact (bk_kp _ _ (kp_tr_stored_block s buf len last)). Qed.
Lemma bk_tr_align : forall s, bk (tr_align s) = bk s.
Proof. intros. exact (bk_kp _ _ (kp_tr_align s)). Qed.
Lemma bk_bi_flush : forall s, bk (bi_flush s) = bk s.
Proof. intros. unfold bi_flush, put_short. destruct (_ =? _); [reflexivity|]. destruct (_ <=? _); reflexivity. Qed.
Lemma bk_flush_pending : forall s, bk (flush_pending s) = bk s.
Proof.
  intros. unfold flush_pending, tr_flush_bits. cbv zeta.
  destruct (_ =? 0); [apply bk_bi_flush|]. rewrite <- (bk_bi_flush s). destruct (_ =? 0); reflexivity.
Qed.


Ltac bkgoA1 :=
  lazymatch goal with
  | |- bk ?x = bk ?x => reflexivity
  | |- bk (let x := ?t in @?E x) = bk ?s0 =>
      first [ is_var t; change (bk (E t) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (let x := ?t in @?E x)) = bk ?s0 =>
      first [ is_var t; change (bk (fst (E t)) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (?a, ?b)) = _ => change (bk (fst (a, b))) with (bk a)
  | |- bk (set_bi_buf ?a ?v) = _ => change (bk (set_bi_buf a v)) with (bk a)
  | |- bk (set_bi_valid ?a ?v) = _ => change (bk (set_bi_valid a v)) with (bk a)
  | |- bk (set_bl_count ?a ?v) = _ => change (bk (set_bl_count a v)) with (bk a)
  | |- bk (set_bl_max_code ?a ?v) = _ => change (bk (set_bl_max_code a v)) with (bk a)
  | |- bk (set_bl_tree_dl ?a ?v) = _ => change (bk (set_bl_tree_dl a v)) with (bk a)
  | |- bk (set_bl_tree_fc ?a ?v) = _ => change (bk (set_bl_tree_fc a v)) with (bk a)
  | |- bk (set_block_start ?a ?v) = _ => change (bk (set_block_start a v)) with (bk a)
  | |- bk (set_d_max_code ?a ?v) = _ => change (bk (set_d_max_code a v)) with (bk a)
  | |- bk (set_depth ?a ?v) = _ => change (bk (set_depth a v)) with (bk a)
  | |- bk (set_dyn_dtree_dl ?a ?v) = _ => change (bk (set_dyn_dtree_dl a v)) with (bk a)
  | |- bk (set_dyn_dtree_fc ?a ?v) = _ => change (bk (set_dyn_dtree_fc a v)) with (bk a)
  | |- bk (set_dyn_ltree_dl ?a ?v) = _ => change (bk (set_dyn_ltree_dl a v)) with (bk a)
  | |- bk (set_dyn_ltree_fc ?a ?v) = _ => change (bk (set_dyn_ltree_fc a v)) with (bk a)
  | |- bk (set_good_match ?a ?v) = _ => change (bk (set_good_match a v)) with (bk a)
  | |- bk (set_gzhead ?a ?v) = _ => change (bk (set_gzhead a v)) with (bk a)
  | |- bk (set_gzindex ?a ?v) = _ => change (bk (set_gzindex a v)) with (bk a)
  | |- bk (set_hash_bits ?a ?v) = _ => change (bk (set_hash_bits a v)) with (bk a)
  | |- bk (set_hash_mask ?a ?v) = _ => change (bk (set_hash_mask a v)) with (bk a)
  | |- bk (set_hash_shift ?a ?v) = _ => change (bk (set_hash_shift a v)) with (bk a)
  | |- bk (set_head ?a ?v) = _ => change (bk (set_head a v)) with (bk a)
  | |- bk (set_heap ?a ?v) = _ => change (bk (set_heap a v)) with (bk a)
  | |- bk (set_heap_len ?a ?v) = _ => change (bk (set_heap_len a v)) with (bk a)
  | |- bk (set_heap_max ?a ?v) = _ => change (bk (set_heap_max a v)) with (bk a)
  | |- bk (set_high_water ?a ?v) = _ => change (bk (set_high_water a v)) with (bk a)
  | |- bk (set_ins_h ?a ?v) = _ => change (bk (set_ins_h a v)) with (bk a)
  | |- bk (set_insert ?a ?v) = _ => change (bk (set_insert a v)) with (bk a)
  | |- bk (set_l_max_code ?a ?v) = _ => change (bk (set_l_max_code a v)) with (bk a)
  | |- bk (set_last_flush ?a ?v) = _ => change (bk (set_last_flush a v)) with (bk a)
  | |- bk (set_level ?a ?v) = _ => change (bk (set_level a v)) with (bk a)
  | |- bk (set_lookahead ?a ?v) = _ => change (bk (set_lookahead a v)) with (bk a)
  | |- bk (set_match_available ?a ?v) = _ => change (bk (set_match_available a v)) with (bk a)
  | |- bk (set_match_length ?a ?v) = _ => change (bk (set_match_length a v)) with (bk a)
  | |- bk (set_match_start ?a ?v) = _ => change (bk (set_match_start a v)) with (bk a)
  | |- bk (set_matches ?a ?v) = _ => change (bk (set_matches a v)) with (bk a)
  | |- bk (set_max_chain_length ?a ?v) = _ => change (bk (set_max_chain_length a v)) with (bk a)
  | |- bk (set_max_lazy_match ?a ?v) = _ => change (bk (set_max_lazy_match a v)) with (bk a)
  | |- bk (set_method ?a ?v) = _ => change (bk (set_method a v)) with (bk a)
  | |- bk (set_nice_match ?a ?v) = _ => change (bk (set_nice_match a v)) with (bk a)
  | |- bk (set_opt_len ?a ?v) = _ => change (bk (set_opt_len a v)) with (bk a)
  | |- bk (set_pending ?a ?v) = _ => change (bk (set_pending a v)) with (bk a)
  | |- bk (set_pending_buf ?a ?v) = _ => change (bk (set_pending_buf a v)) with (bk a)
  | |- bk (set_pending_buf_size ?a ?v) = _ => change (bk (set_pending_buf_size a v)) with (bk a)
  | |- bk (set_pending_out ?a ?v) = _ => change (bk (set_pending_out a v)) with (bk a)
  | |- bk (set_prev ?a ?v) = _ => change (bk (set_prev a v)) with (bk a)
  | |- bk (set_prev_length ?a ?v) = _ => change (bk (set_prev_length a v)) with (bk a)
  | |- bk (set_prev_match ?a ?v) = _ => change (bk (set_prev_match a v)) with (bk a)
  | |- bk (set_static_len ?a ?v) = _ => change (bk (set_static_len a v)) with (bk a)
  | |- bk (set_status ?a ?v) = _ => change (bk (set_status a v)) with (bk a)
  | |- bk (set_strategy ?a ?v) = _ => change (bk (set_strategy a v)) with (bk a)
  | |- bk (set_strm ?a ?v) = _ => change (bk (set_strm a v)) with (bk a)
  | |- bk (set_strstart ?a ?v) = _ => change (bk (set_strstart a v)) with (bk a)
  | |- bk (set_sym_end ?a ?v) = _ => change (bk (set_sym_end a v)) with (bk a)
  | |- bk (set_sym_next ?a ?v) = _ => change (bk (set_sym_next a v)) with (bk a)
  | |- bk (set_w_bits ?a ?v) = _ => change (bk (set_w_bits a v)) with (bk a)
  | |- bk (set_w_mask ?a ?v) = _ => change (bk (set_w_mask a v)) with (bk a)
  | |- bk (set_window ?a ?v) = _ => change (bk (set_window a v)) with (bk a)
  | |- bk (set_window_size ?a ?v) = _ => change (bk (set_window_size a v)) with (bk a)
  | |- bk (set_wrap ?a ?v) = _ => change (bk (set_wrap a v)) with (bk a)
  | |- bk (put_byte ?a ?v) = _ => change (bk (put_byte a v)) with (bk a)
  | |- bk (putShortMSB ?a ?v) = _ => change (bk (putShortMSB a v)) with (bk a)
  | |- bk (set_tree_fc ?a ?v ?w) = _ => change (bk (set_tree_fc a v w)) with (bk a)
  | |- bk (set_tree_dl ?a ?v ?w) = _ => change (bk (set_tree_dl a v w)) with (bk a)
  | |- bk (set_max_code ?a ?v ?w) = _ => change (bk (set_max_code a v w)) with (bk a)
  | |- bk (sym_buf_set ?a ?v ?w) = _ => change (bk (sym_buf_set a v w)) with (bk a)
  | |- bk (set_Freq ?a ?v ?w ?x) = _ => change (bk (set_Freq a v w x)) with (bk a)
  | |- bk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_flush_block a x0 x1 x2))
  | |- bk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_stored_block a x0 x1 x2))
  | |- bk (tr_align ?a ) = _ => apply (eq_trans (bk_tr_align a ))
  | |- bk (flush_pending ?a ) = _ => apply (eq_trans (bk_flush_pending a ))
  | |- bk (bi_flush ?a ) = _ => apply (eq_trans (bk_bi_flush a ))
  | |- bk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (bk_tr_tally_lit a x0))
  | |- bk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_tr_tally_dist a x0 x1))
  | |- bk (match ?t with pair _ _ => _ end) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (fst (match ?t with pair _ _ => _ end)) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (if ?c then _ else _) = _ => destruct c
  | |- bk (fst (if ?c then _ else _)) = _ => destruct c
  | |- bk ?y = bk _ => is_var y; assumption
  end.
Ltac bkgoA := repeat bkgoA1.


Lemma bk_insert_string : forall s str, bk (fst (insert_string s str)) = bk s.
Proof. intros. cbv beta delta [insert_string]. bkgoA. Qed.
Lemma bk_clear_hash : forall s, bk (clear_hash s) = bk s.
Proof. intros. cbv beta delta [clear_hash]. bkgoA. Qed.
Lemma bk_slide_hash : forall s, bk (slide_hash s) = bk s.
Proof. intros. cbv beta delta [slide_hash]. bkgoA. Qed.
Lemma bk_read_buf : forall s dst size, bk (fst (read_buf s dst size)) = bk s.
Proof. intros. cbv beta delta [read_buf]. bkgoA. Qed.
Lemma bk_fill_window_insert : forall f s str, bk (fill_window_insert f s str) = bk s.
Proof.
  induction f as [|f IH]; intros s str; [reflexivity|]. cbn [fill_window_insert].
  bkgoA; apply (eq_trans (IH _ _)); bkgoA.
Qed.

Ltac bkgoB1 :=
  lazymatch goal with
  | |- bk ?x = bk ?x => reflexivity
  | |- bk (let x := ?t in @?E x) = bk ?s0 =>
      first [ is_var t; change (bk (E t) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (let x := ?t in @?E x)) = bk ?s0 =>
      first [ is_var t; change (bk (fst (E t)) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (?a, ?b)) = _ => change (bk (fst (a, b))) with (bk a)
  | |- bk (set_bi_buf ?a ?v) = _ => change (bk (set_bi_buf a v)) with (bk a)
  | |- bk (set_bi_valid ?a ?v) = _ => change (bk (set_bi_valid a v)) with (bk a)
  | |- bk (set_bl_count ?a ?v) = _ => change (bk (set_bl_count a v)) with (bk a)
  | |- bk (set_bl_max_code ?a ?v) = _ => change (bk (set_bl_max_code a v)) with (bk a)
  | |- bk (set_bl_tree_dl ?a ?v) = _ => change (bk (set_bl_tree_dl a v)) with (bk a)
  | |- bk (set_bl_tree_fc ?a ?v) = _ => change (bk (set_bl_tree_fc a v)) with (bk a)
  | |- bk (set_block_start ?a ?v) = _ => change (bk (set_block_start a v)) with (bk a)
  | |- bk (set_d_max_code ?a ?v) = _ => change (bk (set_d_max_code a v)) with (bk a)
  | |- bk (set_depth ?a ?v) = _ => change (bk (set_depth a v)) with (bk a)
  | |- bk (set_dyn_dtree_dl ?a ?v) = _ => change (bk (set_dyn_dtree_dl a v)) with (bk a)
  | |- bk (set_dyn_dtree_fc ?a ?v) = _ => change (bk (set_dyn_dtree_fc a v)) with (bk a)
  | |- bk (set_dyn_ltree_dl ?a ?v) = _ => change (bk (set_dyn_ltree_dl a v)) with (bk a)
  | |- bk (set_dyn_ltree_fc ?a ?v) = _ => change (bk (set_dyn_ltree_fc a v)) with (bk a)
  | |- bk (set_good_match ?a ?v) = _ => change (bk (set_good_match a v)) with (bk a)
  | |- bk (set_gzhead ?a ?v) = _ => change (bk (set_gzhead a v)) with (bk a)
  | |- bk (set_gzindex ?a ?v) = _ => change (bk (set_gzindex a v)) with (bk a)
  | |- bk (set_hash_bits ?a ?v) = _ => change (bk (set_hash_bits a v)) with (bk a)
  | |- bk (set_hash_mask ?a ?v) = _ => change (bk (set_hash_mask a v)) with (bk a)
  | |- bk (set_hash_shift ?a ?v) = _ => change (bk (set_hash_shift a v)) with (bk a)
  | |- bk (set_head ?a ?v) = _ => change (bk (set_head a v)) with (bk a)
  | |- bk (set_heap ?a ?v) = _ => change (bk (set_heap a v)) with (bk a)
  | |- bk (set_heap_len ?a ?v) = _ => change (bk (set_heap_len a v)) with (bk a)
  | |- bk (set_heap_max ?a ?v) = _ => change (bk (set_heap_max a v)) with (bk a)
  | |- bk (set_high_water ?a ?v) = _ => change (bk (set_high_water a v)) with (bk a)
  | |- bk (set_ins_h ?a ?v) = _ => change (bk (set_ins_h a v)) with (bk a)
  | |- bk (set_insert ?a ?v) = _ => change (bk (set_insert a v)) with (bk a)
  | |- bk (set_l_max_code ?a ?v) = _ => change (bk (set_l_max_code a v)) with (bk a)
  | |- bk (set_last_flush ?a ?v) = _ => change (bk (set_last_flush a v)) with (bk a)
  | |- bk (set_level ?a ?v) = _ => change (bk (set_level a v)) with (bk a)
  | |- bk (set_lookahead ?a ?v) = _ => change (bk (set_lookahead a v)) with (bk a)
  | |- bk (set_match_available ?a ?v) = _ => change (bk (set_match_available a v)) with (bk a)
  | |- bk (set_match_length ?a ?v) = _ => change (bk (set_match_length a v)) with (bk a)
  | |- bk (set_match_start ?a ?v) = _ => change (bk (set_match_start a v)) with (bk a)
  | |- bk (set_matches ?a ?v) = _ => change (bk (set_matches a v)) with (bk a)
  | |- bk (set_max_chain_length ?a ?v) = _ => change (bk (set_max_chain_length a v)) with (bk a)
  | |- bk (set_max_lazy_match ?a ?v) = _ => change (bk (set_max_lazy_match a v)) with (bk a)
  | |- bk (set_method ?a ?v) = _ => change (bk (set_method a v)) with (bk a)
  | |- bk (set_nice_match ?a ?v) = _ => change (bk (set_nice_match a v)) with (bk a)
  | |- bk (set_opt_len ?a ?v) = _ => change (bk (set_opt_len a v)) with (bk a)
  | |- bk (set_pending ?a ?v) = _ => change (bk (set_pending a v)) with (bk a)
  | |- bk (set_pending_buf ?a ?v) = _ => change (bk (set_pending_buf a v)) with (bk a)
  | |- bk (set_pending_buf_size ?a ?v) = _ => change (bk (set_pending_buf_size a v)) with (bk a)
  | |- bk (set_pending_out ?a ?v) = _ => change (bk (set_pending_out a v)) with (bk a)
  | |- bk (set_prev ?a ?v) = _ => change (bk (set_prev a v)) with (bk a)
  | |- bk (set_prev_length ?a ?v) = _ => change (bk (set_prev_length a v)) with (bk a)
  | |- bk (set_prev_match ?a ?v) = _ => change (bk (set_prev_match a v)) with (bk a)
  | |- bk (set_static_len ?a ?v) = _ => change (bk (set_static_len a v)) with (bk a)
  | |- bk (set_status ?a ?v) = _ => change (bk (set_status a v)) with (bk a)
  | |- bk (set_strategy ?a ?v) = _ => change (bk (set_strategy a v)) with (bk a)
  | |- bk (set_strm ?a ?v) = _ => change (bk (set_strm a v)) with (bk a)
  | |- bk (set_strstart ?a ?v) = _ => change (bk (set_strstart a v)) with (bk a)
  | |- bk (set_sym_end ?a ?v) = _ => change (bk (set_sym_end a v)) with (bk a)
  | |- bk (set_sym_next ?a ?v) = _ => change (bk (set_sym_next a v)) with (bk a)
  | |- bk (set_w_bits ?a ?v) = _ => change (bk (set_w_bits a v)) with (bk a)
  | |- bk (set_w_mask ?a ?v) = _ => change (bk (set_w_mask a v)) with (bk a)
  | |- bk (set_window ?a ?v) = _ => change (bk (set_window a v)) with (bk a)
  | |- bk (set_window_size ?a ?v) = _ => change (bk (set_window_size a v)) with (bk a)
  | |- bk (set_wrap ?a ?v) = _ => change (bk (set_wrap a v)) with (bk a)
  | |- bk (put_byte ?a ?v) = _ => change (bk (put_byte a v)) with (bk a)
  | |- bk (putShortMSB ?a ?v) = _ => change (bk (putShortMSB a v)) with (bk a)
  | |- bk (set_tree_fc ?a ?v ?w) = _ => change (bk (set_tree_fc a v w)) with (bk a)
  | |- bk (set_tree_dl ?a ?v ?w) = _ => change (bk (set_tree_dl a v w)) with (bk a)
  | |- bk (set_max_code ?a ?v ?w) = _ => change (bk (set_max_code a v w)) with (bk a)
  | |- bk (sym_buf_set ?a ?v ?w) = _ => change (bk (sym_buf_set a v w)) with (bk a)
  | |- bk (set_Freq ?a ?v ?w ?x) = _ => change (bk (set_Freq a v w x)) with (bk a)
  | |- bk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_flush_block a x0 x1 x2))
  | |- bk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_stored_block a x0 x1 x2))
  | |- bk (tr_align ?a ) = _ => apply (eq_trans (bk_tr_align a ))
  | |- bk (flush_pending ?a ) = _ => apply (eq_trans (bk_flush_pending a ))
  | |- bk (bi_flush ?a ) = _ => apply (eq_trans (bk_bi_flush a ))
  | |- bk (clear_hash ?a ) = _ => apply (eq_trans (bk_clear_hash a ))
  | |- bk (slide_hash ?a ) = _ => apply (eq_trans (bk_slide_hash a ))
  | |- bk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (bk_tr_tally_lit a x0))
  | |- bk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_tr_tally_dist a x0 x1))
  | |- bk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (bk_insert_string a x0))
  | |- bk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_read_buf a x0 x1))
  | |- bk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (bk_fill_window_insert fu a x0))
  | |- bk (match ?t with pair _ _ => _ end) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (fst (match ?t with pair _ _ => _ end)) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (if ?c then _ else _) = _ => destruct c
  | |- bk (fst (if ?c then _ else _)) = _ => destruct c
  | |- bk ?y = bk _ => is_var y; assumption
  end.
Ltac bkgoB := repeat bkgoB1.

Lemma bk_fill_window_body : forall s wsize, bk (fst (fill_window_body s wsize)) = bk s.
Proof. intros. cbv beta delta [fill_window_body]. bkgoB. Qed.
Lemma bk_fill_window_loop : forall f s wsize, bk (fill_window_loop f s wsize) = bk s.
Proof.
  induction f as [|f IH]; intros s wsize; [reflexivity|]. cbn [fill_window_loop].
  pose proof (bk_fill_window_body s wsize) as X. destruct (fill_window_body s wsize) as [s1 b]. cbn [fst] in X.
  destruct b; [exact X|]. destruct (_ && _); [rewrite IH|]; exact X.
Qed.
Lemma bk_fill_window_high : forall s, bk (fill_window_high s) = bk s.
Proof. intros. cbv beta delta [fill_window_high]. bkgoB. Qed.
Lemma bk_fill_window : forall s, bk (fill_window s) = bk s.
Proof. intros. cbv beta delta [fill_window]. cbv zeta. rewrite bk_fill_window_high. apply bk_fill_window_loop. Qed.
Lemma bk_longest_match_body : forall s a b c d e f g,
  bk (fst (fst (fst (fst (fst (fst (longest_match_body s a b c d e f g))))))) = bk s.
Proof.
  intros. cbv beta delta [longest_match_body]. cbv zeta.
  repeat (first [ reflexivity | match goal with |- context [if ?c then _ else _] => destruct c end ]; cbn [fst snd]).
Qed.
Lemma bk_longest_match_loop : forall fuel s a b c d e f g, bk (fst (longest_match_loop fuel s a b c d e f g)) = bk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [longest_match_loop].
  pose proof (bk_longest_match_body s a b c d e f g) as X.
  destruct (longest_match_body s a b c d e f g) as [[[[[[s1 x1] x2] x3] x4] x5] cont]. cbn [fst] in X.
  destruct cont; [rewrite IH|]; exact X.
Qed.
Lemma bk_longest_match : forall s cur, bk (fst (longest_match s cur)) = bk s.
Proof.
  intros. cbv beta delta [longest_match]. cbv zeta.
  match goal with |- context [longest_match_loop ?n s cur ?a ?b ?c ?d ?e ?f] =>
    pose proof (bk_longest_match_loop n s cur a b c d e f) as X; destruct (longest_match_loop n s cur a b c d e f) as [s1 bl] end.
  cbn [fst] in X. destruct (_ <=? _); exact X.
Qed.
Lemma bk_flush_block_only : forall s last, bk (flush_block_only s last) = bk s.
Proof. intros. cbv beta delta [flush_block_only]. bkgoB. Qed.

Ltac bkgoC1 :=
  lazymatch goal with
  | |- bk ?x = bk ?x => reflexivity
  | |- bk (let x := ?t in @?E x) = bk ?s0 =>
      first [ is_var t; change (bk (E t) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (let x := ?t in @?E x)) = bk ?s0 =>
      first [ is_var t; change (bk (fst (E t)) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (?a, ?b)) = _ => change (bk (fst (a, b))) with (bk a)
  | |- bk (set_bi_buf ?a ?v) = _ => change (bk (set_bi_buf a v)) with (bk a)
  | |- bk (set_bi_valid ?a ?v) = _ => change (bk (set_bi_valid a v)) with (bk a)
  | |- bk (set_bl_count ?a ?v) = _ => change (bk (set_bl_count a v)) with (bk a)
  | |- bk (set_bl_max_code ?a ?v) = _ => change (bk (set_bl_max_code a v)) with (bk a)
  | |- bk (set_bl_tree_dl ?a ?v) = _ => change (bk (set_bl_tree_dl a v)) with (bk a)
  | |- bk (set_bl_tree_fc ?a ?v) = _ => change (bk (set_bl_tree_fc a v)) with (bk a)
  | |- bk (set_block_start ?a ?v) = _ => change (bk (set_block_start a v)) with (bk a)
  | |- bk (set_d_max_code ?a ?v) = _ => change (bk (set_d_max_code a v)) with (bk a)
  | |- bk (set_depth ?a ?v) = _ => change (bk (set_depth a v)) with (bk a)
  | |- bk (set_dyn_dtree_dl ?a ?v) = _ => change (bk (set_dyn_dtree_dl a v)) with (bk a)
  | |- bk (set_dyn_dtree_fc ?a ?v) = _ => change (bk (set_dyn_dtree_fc a v)) with (bk a)
  | |- bk (set_dyn_ltree_dl ?a ?v) = _ => change (bk (set_dyn_ltree_dl a v)) with (bk a)
  | |- bk (set_dyn_ltree_fc ?a ?v) = _ => change (bk (set_dyn_ltree_fc a v)) with (bk a)
  | |- bk (set_good_match ?a ?v) = _ => change (bk (set_good_match a v)) with (bk a)
  | |- bk (set_gzhead ?a ?v) = _ => change (bk (set_gzhead a v)) with (bk a)
  | |- bk (set_gzindex ?a ?v) = _ => change (bk (set_gzindex a v)) with (bk a)
  | |- bk (set_hash_bits ?a ?v) = _ => change (bk (set_hash_bits a v)) with (bk a)
  | |- bk (set_hash_mask ?a ?v) = _ => change (bk (set_hash_mask a v)) with (bk a)
  | |- bk (set_hash_shift ?a ?v) = _ => change (bk (set_hash_shift a v)) with (bk a)
  | |- bk (set_head ?a ?v) = _ => change (bk (set_head a v)) with (bk a)
  | |- bk (set_heap ?a ?v) = _ => change (bk (set_heap a v)) with (bk a)
  | |- bk (set_heap_len ?a ?v) = _ => change (bk (set_heap_len a v)) with (bk a)
  | |- bk (set_heap_max ?a ?v) = _ => change (bk (set_heap_max a v)) with (bk a)
  | |- bk (set_high_water ?a ?v) = _ => change (bk (set_high_water a v)) with (bk a)
  | |- bk (set_ins_h ?a ?v) = _ => change (bk (set_ins_h a v)) with (bk a)
  | |- bk (set_insert ?a ?v) = _ => change (bk (set_insert a v)) with (bk a)
  | |- bk (set_l_max_code ?a ?v) = _ => change (bk (set_l_max_code a v)) with (bk a)
  | |- bk (set_last_flush ?a ?v) = _ => change (bk (set_last_flush a v)) with (bk a)
  | |- bk (set_level ?a ?v) = _ => change (bk (set_level a v)) with (bk a)
  | |- bk (set_lookahead ?a ?v) = _ => change (bk (set_lookahead a v)) with (bk a)
  | |- bk (set_match_available ?a ?v) = _ => change (bk (set_match_available a v)) with (bk a)
  | |- bk (set_match_length ?a ?v) = _ => change (bk (set_match_length a v)) with (bk a)
  | |- bk (set_match_start ?a ?v) = _ => change (bk (set_match_start a v)) with (bk a)
  | |- bk (set_matches ?a ?v) = _ => change (bk (set_matches a v)) with (bk a)
  | |- bk (set_max_chain_length ?a ?v) = _ => change (bk (set_max_chain_length a v)) with (bk a)
  | |- bk (set_max_lazy_match ?a ?v) = _ => change (bk (set_max_lazy_match a v)) with (bk a)
  | |- bk (set_method ?a ?v) = _ => change (bk (set_method a v)) with (bk a)
  | |- bk (set_nice_match ?a ?v) = _ => change (bk (set_nice_match a v)) with (bk a)
  | |- bk (set_opt_len ?a ?v) = _ => change (bk (set_opt_len a v)) with (bk a)
  | |- bk (set_pending ?a ?v) = _ => change (bk (set_pending a v)) with (bk a)
  | |- bk (set_pending_buf ?a ?v) = _ => change (bk (set_pending_buf a v)) with (bk a)
  | |- bk (set_pending_buf_size ?a ?v) = _ => change (bk (set_pending_buf_size a v)) with (bk a)
  | |- bk (set_pending_out ?a ?v) = _ => change (bk (set_pending_out a v)) with (bk a)
  | |- bk (set_prev ?a ?v) = _ => change (bk (set_prev a v)) with (bk a)
  | |- bk (set_prev_length ?a ?v) = _ => change (bk (set_prev_length a v)) with (bk a)
  | |- bk (set_prev_match ?a ?v) = _ => change (bk (set_prev_match a v)) with (bk a)
  | |- bk (set_static_len ?a ?v) = _ => change (bk (set_static_len a v)) with (bk a)
  | |- bk (set_status ?a ?v) = _ => change (bk (set_status a v)) with (bk a)
  | |- bk (set_strategy ?a ?v) = _ => change (bk (set_strategy a v)) with (bk a)
  | |- bk (set_strm ?a ?v) = _ => change (bk (set_strm a v)) with (bk a)
  | |- bk (set_strstart ?a ?v) = _ => change (bk (set_strstart a v)) with (bk a)
  | |- bk (set_sym_end ?a ?v) = _ => change (bk (set_sym_end a v)) with (bk a)
  | |- bk (set_sym_next ?a ?v) = _ => change (bk (set_sym_next a v)) with (bk a)
  | |- bk (set_w_bits ?a ?v) = _ => change (bk (set_w_bits a v)) with (bk a)
  | |- bk (set_w_mask ?a ?v) = _ => change (bk (set_w_mask a v)) with (bk a)
  | |- bk (set_window ?a ?v) = _ => change (bk (set_window a v)) with (bk a)
  | |- bk (set_window_size ?a ?v) = _ => change (bk (set_window_size a v)) with (bk a)
  | |- bk (set_wrap ?a ?v) = _ => change (bk (set_wrap a v)) with (bk a)
  | |- bk (put_byte ?a ?v) = _ => change (bk (put_byte a v)) with (bk a)
  | |- bk (putShortMSB ?a ?v) = _ => change (bk (putShortMSB a v)) with (bk a)
  | |- bk (set_tree_fc ?a ?v ?w) = _ => change (bk (set_tree_fc a v w)) with (bk a)
  | |- bk (set_tree_dl ?a ?v ?w) = _ => change (bk (set_tree_dl a v w)) with (bk a)
  | |- bk (set_max_code ?a ?v ?w) = _ => change (bk (set_max_code a v w)) with (bk a)
  | |- bk (sym_buf_set ?a ?v ?w) = _ => change (bk (sym_buf_set a v w)) with (bk a)
  | |- bk (set_Freq ?a ?v ?w ?x) = _ => change (bk (set_Freq a v w x)) with (bk a)
  | |- bk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_flush_block a x0 x1 x2))
  | |- bk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_stored_block a x0 x1 x2))
  | |- bk (tr_align ?a ) = _ => apply (eq_trans (bk_tr_align a ))
  | |- bk (flush_pending ?a ) = _ => apply (eq_trans (bk_flush_pending a ))
  | |- bk (bi_flush ?a ) = _ => apply (eq_trans (bk_bi_flush a ))
  | |- bk (clear_hash ?a ) = _ => apply (eq_trans (bk_clear_hash a ))
  | |- bk (slide_hash ?a ) = _ => apply (eq_trans (bk_slide_hash a ))
  | |- bk (fill_window ?a ) = _ => apply (eq_trans (bk_fill_window a ))
  | |- bk (flush_block_only ?a ?x0) = _ => apply (eq_trans (bk_flush_block_only a x0))
  | |- bk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (bk_tr_tally_lit a x0))
  | |- bk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_tr_tally_dist a x0 x1))
  | |- bk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (bk_insert_string a x0))
  | |- bk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_read_buf a x0 x1))
  | |- bk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (bk_longest_match a x0))
  | |- bk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (bk_fill_window_insert fu a x0))
  | |- bk (match ?t with pair _ _ => _ end) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (fst (match ?t with pair _ _ => _ end)) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (if ?c then _ else _) = _ => destruct c
  | |- bk (fst (if ?c then _ else _)) = _ => destruct c
  | |- bk ?y = bk _ => is_var y; assumption
  end.
Ltac bkgoC := repeat bkgoC1.

Lemma bk_flush_block : forall s last, bk (fst (flush_block s last)) = bk s.
Proof. intros. cbv beta delta [flush_block]. bkgoC. Qed.
Lemma bk_deflate_tail : forall s flush, bk (fst (deflate_tail s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_tail]. bkgoC; apply (eq_trans (bk_flush_block _ _)); bkgoC. Qed.

Ltac bkgoD1 :=
  lazymatch goal with
  | |- bk ?x = bk ?x => reflexivity
  | |- bk (let x := ?t in @?E x) = bk ?s0 =>
      first [ is_var t; change (bk (E t) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (let x := ?t in @?E x)) = bk ?s0 =>
      first [ is_var t; change (bk (fst (E t)) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (?a, ?b)) = _ => change (bk (fst (a, b))) with (bk a)
  | |- bk (set_bi_buf ?a ?v) = _ => change (bk (set_bi_buf a v)) with (bk a)
  | |- bk (set_bi_valid ?a ?v) = _ => change (bk (set_bi_valid a v)) with (bk a)
  | |- bk (set_bl_count ?a ?v) = _ => change (bk (set_bl_count a v)) with (bk a)
  | |- bk (set_bl_max_code ?a ?v) = _ => change (bk (set_bl_max_code a v)) with (bk a)
  | |- bk (set_bl_tree_dl ?a ?v) = _ => change (bk (set_bl_tree_dl a v)) with (bk a)
  | |- bk (set_bl_tree_fc ?a ?v) = _ => change (bk (set_bl_tree_fc a v)) with (bk a)
  | |- bk (set_block_start ?a ?v) = _ => change (bk (set_block_start a v)) with (bk a)
  | |- bk (set_d_max_code ?a ?v) = _ => change (bk (set_d_max_code a v)) with (bk a)
  | |- bk (set_depth ?a ?v) = _ => change (bk (set_depth a v)) with (bk a)
  | |- bk (set_dyn_dtree_dl ?a ?v) = _ => change (bk (set_dyn_dtree_dl a v)) with (bk a)
  | |- bk (set_dyn_dtree_fc ?a ?v) = _ => change (bk (set_dyn_dtree_fc a v)) with (bk a)
  | |- bk (set_dyn_ltree_dl ?a ?v) = _ => change (bk (set_dyn_ltree_dl a v)) with (bk a)
  | |- bk (set_dyn_ltree_fc ?a ?v) = _ => change (bk (set_dyn_ltree_fc a v)) with (bk a)
  | |- bk (set_good_match ?a ?v) = _ => change (bk (set_good_match a v)) with (bk a)
  | |- bk (set_gzhead ?a ?v) = _ => change (bk (set_gzhead a v)) with (bk a)
  | |- bk (set_gzindex ?a ?v) = _ => change (bk (set_gzindex a v)) with (bk a)
  | |- bk (set_hash_bits ?a ?v) = _ => change (bk (set_hash_bits a v)) with (bk a)
  | |- bk (set_hash_mask ?a ?v) = _ => change (bk (set_hash_mask a v)) with (bk a)
  | |- bk (set_hash_shift ?a ?v) = _ => change (bk (set_hash_shift a v)) with (bk a)
  | |- bk (set_head ?a ?v) = _ => change (bk (set_head a v)) with (bk a)
  | |- bk (set_heap ?a ?v) = _ => change (bk (set_heap a v)) with (bk a)
  | |- bk (set_heap_len ?a ?v) = _ => change (bk (set_heap_len a v)) with (bk a)
  | |- bk (set_heap_max ?a ?v) = _ => change (bk (set_heap_max a v)) with (bk a)
  | |- bk (set_high_water ?a ?v) = _ => change (bk (set_high_water a v)) with (bk a)
  | |- bk (set_ins_h ?a ?v) = _ => change (bk (set_ins_h a v)) with (bk a)
  | |- bk (set_insert ?a ?v) = _ => change (bk (set_insert a v)) with (bk a)
  | |- bk (set_l_max_code ?a ?v) = _ => change (bk (set_l_max_code a v)) with (bk a)
  | |- bk (set_last_flush ?a ?v) = _ => change (bk (set_last_flush a v)) with (bk a)
  | |- bk (set_level ?a ?v) = _ => change (bk (set_level a v)) with (bk a)
  | |- bk (set_lookahead ?a ?v) = _ => change (bk (set_lookahead a v)) with (bk a)
  | |- bk (set_match_available ?a ?v) = _ => change (bk (set_match_available a v)) with (bk a)
  | |- bk (set_match_length ?a ?v) = _ => change (bk (set_match_length a v)) with (bk a)
  | |- bk (set_match_start ?a ?v) = _ => change (bk (set_match_start a v)) with (bk a)
  | |- bk (set_matches ?a ?v) = _ => change (bk (set_matches a v)) with (bk a)
  | |- bk (set_max_chain_length ?a ?v) = _ => change (bk (set_max_chain_length a v)) with (bk a)
  | |- bk (set_max_lazy_match ?a ?v) = _ => change (bk (set_max_lazy_match a v)) with (bk a)
  | |- bk (set_method ?a ?v) = _ => change (bk (set_method a v)) with (bk a)
  | |- bk (set_nice_match ?a ?v) = _ => change (bk (set_nice_match a v)) with (bk a)
  | |- bk (set_opt_len ?a ?v) = _ => change (bk (set_opt_len a v)) with (bk a)
  | |- bk (set_pending ?a ?v) = _ => change (bk (set_pending a v)) with (bk a)
  | |- bk (set_pending_buf ?a ?v) = _ => change (bk (set_pending_buf a v)) with (bk a)
  | |- bk (set_pending_buf_size ?a ?v) = _ => change (bk (set_pending_buf_size a v)) with (bk a)
  | |- bk (set_pending_out ?a ?v) = _ => change (bk (set_pending_out a v)) with (bk a)
  | |- bk (set_prev ?a ?v) = _ => change (bk (set_prev a v)) with (bk a)
  | |- bk (set_prev_length ?a ?v) = _ => change (bk (set_prev_length a v)) with (bk a)
  | |- bk (set_prev_match ?a ?v) = _ => change (bk (set_prev_match a v)) with (bk a)
  | |- bk (set_static_len ?a ?v) = _ => change (bk (set_static_len a v)) with (bk a)
  | |- bk (set_status ?a ?v) = _ => change (bk (set_status a v)) with (bk a)
  | |- bk (set_strategy ?a ?v) = _ => change (bk (set_strategy a v)) with (bk a)
  | |- bk (set_strm ?a ?v) = _ => change (bk (set_strm a v)) with (bk a)
  | |- bk (set_strstart ?a ?v) = _ => change (bk (set_strstart a v)) with (bk a)
  | |- bk (set_sym_end ?a ?v) = _ => change (bk (set_sym_end a v)) with (bk a)
  | |- bk (set_sym_next ?a ?v) = _ => change (bk (set_sym_next a v)) with (bk a)
  | |- bk (set_w_bits ?a ?v) = _ => change (bk (set_w_bits a v)) with (bk a)
  | |- bk (set_w_mask ?a ?v) = _ => change (bk (set_w_mask a v)) with (bk a)
  | |- bk (set_window ?a ?v) = _ => change (bk (set_window a v)) with (bk a)
  | |- bk (set_window_size ?a ?v) = _ => change (bk (set_window_size a v)) with (bk a)
  | |- bk (set_wrap ?a ?v) = _ => change (bk (set_wrap a v)) with (bk a)
  | |- bk (put_byte ?a ?v) = _ => change (bk (put_byte a v)) with (bk a)
  | |- bk (putShortMSB ?a ?v) = _ => change (bk (putShortMSB a v)) with (bk a)
  | |- bk (set_tree_fc ?a ?v ?w) = _ => change (bk (set_tree_fc a v w)) with (bk a)
  | |- bk (set_tree_dl ?a ?v ?w) = _ => change (bk (set_tree_dl a v w)) with (bk a)
  | |- bk (set_max_code ?a ?v ?w) = _ => change (bk (set_max_code a v w)) with (bk a)
  | |- bk (sym_buf_set ?a ?v ?w) = _ => change (bk (sym_buf_set a v w)) with (bk a)
  | |- bk (set_Freq ?a ?v ?w ?x) = _ => change (bk (set_Freq a v w x)) with (bk a)
  | |- bk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_flush_block a x0 x1 x2))
  | |- bk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_stored_block a x0 x1 x2))
  | |- bk (tr_align ?a ) = _ => apply (eq_trans (bk_tr_align a ))
  | |- bk (flush_pending ?a ) = _ => apply (eq_trans (bk_flush_pending a ))
  | |- bk (bi_flush ?a ) = _ => apply (eq_trans (bk_bi_flush a ))
  | |- bk (clear_hash ?a ) = _ => apply (eq_trans (bk_clear_hash a ))
  | |- bk (slide_hash ?a ) = _ => apply (eq_trans (bk_slide_hash a ))
  | |- bk (fill_window ?a ) = _ => apply (eq_trans (bk_fill_window a ))
  | |- bk (flush_block_only ?a ?x0) = _ => apply (eq_trans (bk_flush_block_only a x0))
  | |- bk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (bk_tr_tally_lit a x0))
  | |- bk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_tr_tally_dist a x0 x1))
  | |- bk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (bk_insert_string a x0))
  | |- bk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_read_buf a x0 x1))
  | |- bk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (bk_longest_match a x0))
  | |- bk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (bk_fill_window_insert fu a x0))
  | |- bk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (bk_flush_block a x0))
  | |- bk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (bk_deflate_tail a x0))
  | |- bk (match ?t with pair _ _ => _ end) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (fst (match ?t with pair _ _ => _ end)) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (if ?c then _ else _) = _ => destruct c
  | |- bk (fst (if ?c then _ else _)) = _ => destruct c
  | |- bk ?y = bk _ => is_var y; assumption
  end.
Ltac bkgoD := repeat bkgoD1.


Lemma bk_deflate_stored_body : forall s flush mb, bk (fst (fst (deflate_stored_body s flush mb))) = bk s.
Proof.
  intros. cbv beta delta [deflate_stored_body].
  repeat (bkgoD1
          || lazymatch goal with
             | |- bk (fst (fst (?a, ?b, ?c))) = _ => change (bk (fst (fst (a, b, c)))) with (bk a)
             | |- bk (fst (fst (if ?c then _ else _))) = _ => destruct c
             | |- bk (fst (fst (let x := ?t in @?E x))) = bk ?s0 =>
                 first [ is_var t; change (bk (fst (fst (E t))) = bk s0); cbv beta
                       | lazymatch type of t with
                         | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
                         | _ => generalize t; let y := fresh "v" in intros y
                         end ]
             | |- bk (fst (fst (match ?t with pair _ _ => _ end))) = bk ?s0 =>
                 let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
             end).
Qed.
Lemma bk_deflate_stored_loop : forall fuel s flush mb, bk (fst (deflate_stored_loop fuel s flush mb)) = bk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_stored_loop].
  pose proof (bk_deflate_stored_body s flush mb) as X. destruct (deflate_stored_body s flush mb) as [[s1 last] broke]. cbn [fst] in X.
  destruct broke; [exact X|]. destruct (last =? 0); [rewrite IH|]; exact X.
Qed.
Lemma bk_deflate_stored_used : forall s used, bk (deflate_stored_used s used) = bk s.
Proof. intros. cbv beta delta [deflate_stored_used]. bkgoD. Qed.
Lemma bk_deflate_stored_fin : forall s flush, bk (fst (deflate_stored_fin s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_stored_fin]. bkgoD. Qed.
Lemma bk_deflate_stored_slide : forall s hv, bk (fst (deflate_stored_slide s hv)) = bk s.
Proof. intros. cbv beta delta [deflate_stored_slide]. bkgoD. Qed.

Ltac bkgoE1 :=
  lazymatch goal with
  | |- bk ?x = bk ?x => reflexivity
  | |- bk (let x := ?t in @?E x) = bk ?s0 =>
      first [ is_var t; change (bk (E t) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (let x := ?t in @?E x)) = bk ?s0 =>
      first [ is_var t; change (bk (fst (E t)) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (?a, ?b)) = _ => change (bk (fst (a, b))) with (bk a)
  | |- bk (set_bi_buf ?a ?v) = _ => change (bk (set_bi_buf a v)) with (bk a)
  | |- bk (set_bi_valid ?a ?v) = _ => change (bk (set_bi_valid a v)) with (bk a)
  | |- bk (set_bl_count ?a ?v) = _ => change (bk (set_bl_count a v)) with (bk a)
  | |- bk (set_bl_max_code ?a ?v) = _ => change (bk (set_bl_max_code a v)) with (bk a)
  | |- bk (set_bl_tree_dl ?a ?v) = _ => change (bk (set_bl_tree_dl a v)) with (bk a)
  | |- bk (set_bl_tree_fc ?a ?v) = _ => change (bk (set_bl_tree_fc a v)) with (bk a)
  | |- bk (set_block_start ?a ?v) = _ => change (bk (set_block_start a v)) with (bk a)
  | |- bk (set_d_max_code ?a ?v) = _ => change (bk (set_d_max_code a v)) with (bk a)
  | |- bk (set_depth ?a ?v) = _ => change (bk (set_depth a v)) with (bk a)
  | |- bk (set_dyn_dtree_dl ?a ?v) = _ => change (bk (set_dyn_dtree_dl a v)) with (bk a)
  | |- bk (set_dyn_dtree_fc ?a ?v) = _ => change (bk (set_dyn_dtree_fc a v)) with (bk a)
  | |- bk (set_dyn_ltree_dl ?a ?v) = _ => change (bk (set_dyn_ltree_dl a v)) with (bk a)
  | |- bk (set_dyn_ltree_fc ?a ?v) = _ => change (bk (set_dyn_ltree_fc a v)) with (bk a)
  | |- bk (set_good_match ?a ?v) = _ => change (bk (set_good_match a v)) with (bk a)
  | |- bk (set_gzhead ?a ?v) = _ => change (bk (set_gzhead a v)) with (bk a)
  | |- bk (set_gzindex ?a ?v) = _ => change (bk (set_gzindex a v)) with (bk a)
  | |- bk (set_hash_bits ?a ?v) = _ => change (bk (set_hash_bits a v)) with (bk a)
  | |- bk (set_hash_mask ?a ?v) = _ => change (bk (set_hash_mask a v)) with (bk a)
  | |- bk (set_hash_shift ?a ?v) = _ => change (bk (set_hash_shift a v)) with (bk a)
  | |- bk (set_head ?a ?v) = _ => change (bk (set_head a v)) with (bk a)
  | |- bk (set_heap ?a ?v) = _ => change (bk (set_heap a v)) with (bk a)
  | |- bk (set_heap_len ?a ?v) = _ => change (bk (set_heap_len a v)) with (bk a)
  | |- bk (set_heap_max ?a ?v) = _ => change (bk (set_heap_max a v)) with (bk a)
  | |- bk (set_high_water ?a ?v) = _ => change (bk (set_high_water a v)) with (bk a)
  | |- bk (set_ins_h ?a ?v) = _ => change (bk (set_ins_h a v)) with (bk a)
  | |- bk (set_insert ?a ?v) = _ => change (bk (set_insert a v)) with (bk a)
  | |- bk (set_l_max_code ?a ?v) = _ => change (bk (set_l_max_code a v)) with (bk a)
  | |- bk (set_last_flush ?a ?v) = _ => change (bk (set_last_flush a v)) with (bk a)
  | |- bk (set_level ?a ?v) = _ => change (bk (set_level a v)) with (bk a)
  | |- bk (set_lookahead ?a ?v) = _ => change (bk (set_lookahead a v)) with (bk a)
  | |- bk (set_match_available ?a ?v) = _ => change (bk (set_match_available a v)) with (bk a)
  | |- bk (set_match_length ?a ?v) = _ => change (bk (set_match_length a v)) with (bk a)
  | |- bk (set_match_start ?a ?v) = _ => change (bk (set_match_start a v)) with (bk a)
  | |- bk (set_matches ?a ?v) = _ => change (bk (set_matches a v)) with (bk a)
  | |- bk (set_max_chain_length ?a ?v) = _ => change (bk (set_max_chain_length a v)) with (bk a)
  | |- bk (set_max_lazy_match ?a ?v) = _ => change (bk (set_max_lazy_match a v)) with (bk a)
  | |- bk (set_method ?a ?v) = _ => change (bk (set_method a v)) with (bk a)
  | |- bk (set_nice_match ?a ?v) = _ => change (bk (set_nice_match a v)) with (bk a)
  | |- bk (set_opt_len ?a ?v) = _ => change (bk (set_opt_len a v)) with (bk a)
  | |- bk (set_pending ?a ?v) = _ => change (bk (set_pending a v)) with (bk a)
  | |- bk (set_pending_buf ?a ?v) = _ => change (bk (set_pending_buf a v)) with (bk a)
  | |- bk (set_pending_buf_size ?a ?v) = _ => change (bk (set_pending_buf_size a v)) with (bk a)
  | |- bk (set_pending_out ?a ?v) = _ => change (bk (set_pending_out a v)) with (bk a)
  | |- bk (set_prev ?a ?v) = _ => change (bk (set_prev a v)) with (bk a)
  | |- bk (set_prev_length ?a ?v) = _ => change (bk (set_prev_length a v)) with (bk a)
  | |- bk (set_prev_match ?a ?v) = _ => change (bk (set_prev_match a v)) with (bk a)
  | |- bk (set_static_len ?a ?v) = _ => change (bk (set_static_len a v)) with (bk a)
  | |- bk (set_status ?a ?v) = _ => change (bk (set_status a v)) with (bk a)
  | |- bk (set_strategy ?a ?v) = _ => change (bk (set_strategy a v)) with (bk a)
  | |- bk (set_strm ?a ?v) = _ => change (bk (set_strm a v)) with (bk a)
  | |- bk (set_strstart ?a ?v) = _ => change (bk (set_strstart a v)) with (bk a)
  | |- bk (set_sym_end ?a ?v) = _ => change (bk (set_sym_end a v)) with (bk a)
  | |- bk (set_sym_next ?a ?v) = _ => change (bk (set_sym_next a v)) with (bk a)
  | |- bk (set_w_bits ?a ?v) = _ => change (bk (set_w_bits a v)) with (bk a)
  | |- bk (set_w_mask ?a ?v) = _ => change (bk (set_w_mask a v)) with (bk a)
  | |- bk (set_window ?a ?v) = _ => change (bk (set_window a v)) with (bk a)
  | |- bk (set_window_size ?a ?v) = _ => change (bk (set_window_size a v)) with (bk a)
  | |- bk (set_wrap ?a ?v) = _ => change (bk (set_wrap a v)) with (bk a)
  | |- bk (put_byte ?a ?v) = _ => change (bk (put_byte a v)) with (bk a)
  | |- bk (putShortMSB ?a ?v) = _ => change (bk (putShortMSB a v)) with (bk a)
  | |- bk (set_tree_fc ?a ?v ?w) = _ => change (bk (set_tree_fc a v w)) with (bk a)
  | |- bk (set_tree_dl ?a ?v ?w) = _ => change (bk (set_tree_dl a v w)) with (bk a)
  | |- bk (set_max_code ?a ?v ?w) = _ => change (bk (set_max_code a v w)) with (bk a)
  | |- bk (sym_buf_set ?a ?v ?w) = _ => change (bk (sym_buf_set a v w)) with (bk a)
  | |- bk (set_Freq ?a ?v ?w ?x) = _ => change (bk (set_Freq a v w x)) with (bk a)
  | |- bk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_flush_block a x0 x1 x2))
  | |- bk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_stored_block a x0 x1 x2))
  | |- bk (tr_align ?a ) = _ => apply (eq_trans (bk_tr_align a ))
  | |- bk (flush_pending ?a ) = _ => apply (eq_trans (bk_flush_pending a ))
  | |- bk (bi_flush ?a ) = _ => apply (eq_trans (bk_bi_flush a ))
  | |- bk (clear_hash ?a ) = _ => apply (eq_trans (bk_clear_hash a ))
  | |- bk (slide_hash ?a ) = _ => apply (eq_trans (bk_slide_hash a ))
  | |- bk (fill_window ?a ) = _ => apply (eq_trans (bk_fill_window a ))
  | |- bk (flush_block_only ?a ?x0) = _ => apply (eq_trans (bk_flush_block_only a x0))
  | |- bk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (bk_tr_tally_lit a x0))
  | |- bk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_tr_tally_dist a x0 x1))
  | |- bk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (bk_insert_string a x0))
  | |- bk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_read_buf a x0 x1))
  | |- bk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (bk_longest_match a x0))
  | |- bk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (bk_fill_window_insert fu a x0))
  | |- bk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (bk_flush_block a x0))
  | |- bk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (bk_deflate_tail a x0))
  | |- bk (deflate_stored_used ?a ?x0) = _ => apply (eq_trans (bk_deflate_stored_used a x0))
  | |- bk (fst (deflate_stored_fin ?a ?x0)) = _ => apply (eq_trans (bk_deflate_stored_fin a x0))
  | |- bk (fst (deflate_stored_slide ?a ?x0)) = _ => apply (eq_trans (bk_deflate_stored_slide a x0))
  | |- bk (fst (deflate_stored_loop ?fu ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_deflate_stored_loop fu a x0 x1))
  | |- bk (match ?t with pair _ _ => _ end) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (fst (match ?t with pair _ _ => _ end)) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (if ?c then _ else _) = _ => destruct c
  | |- bk (fst (if ?c then _ else _)) = _ => destruct c
  | |- bk ?y = bk _ => is_var y; assumption
  end.
Ltac bkgoE := repeat bkgoE1.

Lemma bk_deflate_stored_mid : forall s flush, bk (fst (deflate_stored_mid s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_stored_mid]. bkgoE. Qed.
Lemma bk_deflate_stored : forall s flush, bk (fst (deflate_stored s flush)) = bk s.
Proof.
  intros. cbv beta delta [deflate_stored]. bkgoE; apply (eq_trans (bk_deflate_stored_mid _ _)); bkgoE.
Qed.

Lemma bk_deflate_fast_insert : forall f s, bk (deflate_fast_insert f s) = bk s.
Proof.
  induction f as [|f IH]; intros s; [reflexivity|]. cbn [deflate_fast_insert].
  bkgoE; apply (eq_trans (IH _)); bkgoE.
Qed.
Lemma bk_deflate_slow_insert : forall f s mi, bk (deflate_slow_insert f s mi) = bk s.
Proof.
  induction f as [|f IH]; intros s mi; [reflexivity|]. cbn [deflate_slow_insert].
  bkgoE; apply (eq_trans (IH _ _)); bkgoE.
Qed.

Ltac bkgoF1 :=
  lazymatch goal with
  | |- bk ?x = bk ?x => reflexivity
  | |- bk (let x := ?t in @?E x) = bk ?s0 =>
      first [ is_var t; change (bk (E t) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (let x := ?t in @?E x)) = bk ?s0 =>
      first [ is_var t; change (bk (fst (E t)) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (?a, ?b)) = _ => change (bk (fst (a, b))) with (bk a)
  | |- bk (set_bi_buf ?a ?v) = _ => change (bk (set_bi_buf a v)) with (bk a)
  | |- bk (set_bi_valid ?a ?v) = _ => change (bk (set_bi_valid a v)) with (bk a)
  | |- bk (set_bl_count ?a ?v) = _ => change (bk (set_bl_count a v)) with (bk a)
  | |- bk (set_bl_max_code ?a ?v) = _ => change (bk (set_bl_max_code a v)) with (bk a)
  | |- bk (set_bl_tree_dl ?a ?v) = _ => change (bk (set_bl_tree_dl a v)) with (bk a)
  | |- bk (set_bl_tree_fc ?a ?v) = _ => change (bk (set_bl_tree_fc a v)) with (bk a)
  | |- bk (set_block_start ?a ?v) = _ => change (bk (set_block_start a v)) with (bk a)
  | |- bk (set_d_max_code ?a ?v) = _ => change (bk (set_d_max_code a v)) with (bk a)
  | |- bk (set_depth ?a ?v) = _ => change (bk (set_depth a v)) with (bk a)
  | |- bk (set_dyn_dtree_dl ?a ?v) = _ => change (bk (set_dyn_dtree_dl a v)) with (bk a)
  | |- bk (set_dyn_dtree_fc ?a ?v) = _ => change (bk (set_dyn_dtree_fc a v)) with (bk a)
  | |- bk (set_dyn_ltree_dl ?a ?v) = _ => change (bk (set_dyn_ltree_dl a v)) with (bk a)
  | |- bk (set_dyn_ltree_fc ?a ?v) = _ => change (bk (set_dyn_ltree_fc a v)) with (bk a)
  | |- bk (set_good_match ?a ?v) = _ => change (bk (set_good_match a v)) with (bk a)
  | |- bk (set_gzhead ?a ?v) = _ => change (bk (set_gzhead a v)) with (bk a)
  | |- bk (set_gzindex ?a ?v) = _ => change (bk (set_gzindex a v)) with (bk a)
  | |- bk (set_hash_bits ?a ?v) = _ => change (bk (set_hash_bits a v)) with (bk a)
  | |- bk (set_hash_mask ?a ?v) = _ => change (bk (set_hash_mask a v)) with (bk a)
  | |- bk (set_hash_shift ?a ?v) = _ => change (bk (set_hash_shift a v)) with (bk a)
  | |- bk (set_head ?a ?v) = _ => change (bk (set_head a v)) with (bk a)
  | |- bk (set_heap ?a ?v) = _ => change (bk (set_heap a v)) with (bk a)
  | |- bk (set_heap_len ?a ?v) = _ => change (bk (set_heap_len a v)) with (bk a)
  | |- bk (set_heap_max ?a ?v) = _ => change (bk (set_heap_max a v)) with (bk a)
  | |- bk (set_high_water ?a ?v) = _ => change (bk (set_high_water a v)) with (bk a)
  | |- bk (set_ins_h ?a ?v) = _ => change (bk (set_ins_h a v)) with (bk a)
  | |- bk (set_insert ?a ?v) = _ => change (bk (set_insert a v)) with (bk a)
  | |- bk (set_l_max_code ?a ?v) = _ => change (bk (set_l_max_code a v)) with (bk a)
  | |- bk (set_last_flush ?a ?v) = _ => change (bk (set_last_flush a v)) with (bk a)
  | |- bk (set_level ?a ?v) = _ => change (bk (set_level a v)) with (bk a)
  | |- bk (set_lookahead ?a ?v) = _ => change (bk (set_lookahead a v)) with (bk a)
  | |- bk (set_match_available ?a ?v) = _ => change (bk (set_match_available a v)) with (bk a)
  | |- bk (set_match_length ?a ?v) = _ => change (bk (set_match_length a v)) with (bk a)
  | |- bk (set_match_start ?a ?v) = _ => change (bk (set_match_start a v)) with (bk a)
  | |- bk (set_matches ?a ?v) = _ => change (bk (set_matches a v)) with (bk a)
  | |- bk (set_max_chain_length ?a ?v) = _ => change (bk (set_max_chain_length a v)) with (bk a)
  | |- bk (set_max_lazy_match ?a ?v) = _ => change (bk (set_max_lazy_match a v)) with (bk a)
  | |- bk (set_method ?a ?v) = _ => change (bk (set_method a v)) with (bk a)
  | |- bk (set_nice_match ?a ?v) = _ => change (bk (set_nice_match a v)) with (bk a)
  | |- bk (set_opt_len ?a ?v) = _ => change (bk (set_opt_len a v)) with (bk a)
  | |- bk (set_pending ?a ?v) = _ => change (bk (set_pending a v)) with (bk a)
  | |- bk (set_pending_buf ?a ?v) = _ => change (bk (set_pending_buf a v)) with (bk a)
  | |- bk (set_pending_buf_size ?a ?v) = _ => change (bk (set_pending_buf_size a v)) with (bk a)
  | |- bk (set_pending_out ?a ?v) = _ => change (bk (set_pending_out a v)) with (bk a)
  | |- bk (set_prev ?a ?v) = _ => change (bk (set_prev a v)) with (bk a)
  | |- bk (set_prev_length ?a ?v) = _ => change (bk (set_prev_length a v)) with (bk a)
  | |- bk (set_prev_match ?a ?v) = _ => change (bk (set_prev_match a v)) with (bk a)
  | |- bk (set_static_len ?a ?v) = _ => change (bk (set_static_len a v)) with (bk a)
  | |- bk (set_status ?a ?v) = _ => change (bk (set_status a v)) with (bk a)
  | |- bk (set_strategy ?a ?v) = _ => change (bk (set_strategy a v)) with (bk a)
  | |- bk (set_strm ?a ?v) = _ => change (bk (set_strm a v)) with (bk a)
  | |- bk (set_strstart ?a ?v) = _ => change (bk (set_strstart a v)) with (bk a)
  | |- bk (set_sym_end ?a ?v) = _ => change (bk (set_sym_end a v)) with (bk a)
  | |- bk (set_sym_next ?a ?v) = _ => change (bk (set_sym_next a v)) with (bk a)
  | |- bk (set_w_bits ?a ?v) = _ => change (bk (set_w_bits a v)) with (bk a)
  | |- bk (set_w_mask ?a ?v) = _ => change (bk (set_w_mask a v)) with (bk a)
  | |- bk (set_window ?a ?v) = _ => change (bk (set_window a v)) with (bk a)
  | |- bk (set_window_size ?a ?v) = _ => change (bk (set_window_size a v)) with (bk a)
  | |- bk (set_wrap ?a ?v) = _ => change (bk (set_wrap a v)) with (bk a)
  | |- bk (put_byte ?a ?v) = _ => change (bk (put_byte a v)) with (bk a)
  | |- bk (putShortMSB ?a ?v) = _ => change (bk (putShortMSB a v)) with (bk a)
  | |- bk (set_tree_fc ?a ?v ?w) = _ => change (bk (set_tree_fc a v w)) with (bk a)
  | |- bk (set_tree_dl ?a ?v ?w) = _ => change (bk (set_tree_dl a v w)) with (bk a)
  | |- bk (set_max_code ?a ?v ?w) = _ => change (bk (set_max_code a v w)) with (bk a)
  | |- bk (sym_buf_set ?a ?v ?w) = _ => change (bk (sym_buf_set a v w)) with (bk a)
  | |- bk (set_Freq ?a ?v ?w ?x) = _ => change (bk (set_Freq a v w x)) with (bk a)
  | |- bk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_flush_block a x0 x1 x2))
  | |- bk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_stored_block a x0 x1 x2))
  | |- bk (tr_align ?a ) = _ => apply (eq_trans (bk_tr_align a ))
  | |- bk (flush_pending ?a ) = _ => apply (eq_trans (bk_flush_pending a ))
  | |- bk (bi_flush ?a ) = _ => apply (eq_trans (bk_bi_flush a ))
  | |- bk (clear_hash ?a ) = _ => apply (eq_trans (bk_clear_hash a ))
  | |- bk (slide_hash ?a ) = _ => apply (eq_trans (bk_slide_hash a ))
  | |- bk (fill_window ?a ) = _ => apply (eq_trans (bk_fill_window a ))
  | |- bk (flush_block_only ?a ?x0) = _ => apply (eq_trans (bk_flush_block_only a x0))
  | |- bk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (bk_tr_tally_lit a x0))
  | |- bk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_tr_tally_dist a x0 x1))
  | |- bk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (bk_insert_string a x0))
  | |- bk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_read_buf a x0 x1))
  | |- bk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (bk_longest_match a x0))
  | |- bk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (bk_fill_window_insert fu a x0))
  | |- bk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (bk_flush_block a x0))
  | |- bk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (bk_deflate_tail a x0))
  | |- bk (deflate_stored_used ?a ?x0) = _ => apply (eq_trans (bk_deflate_stored_used a x0))
  | |- bk (fst (deflate_stored_fin ?a ?x0)) = _ => apply (eq_trans (bk_deflate_stored_fin a x0))
  | |- bk (fst (deflate_stored_slide ?a ?x0)) = _ => apply (eq_trans (bk_deflate_stored_slide a x0))
  | |- bk (fst (deflate_stored_loop ?fu ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_deflate_stored_loop fu a x0 x1))
  | |- bk (deflate_fast_insert ?fu ?a) = _ => apply (eq_trans (bk_deflate_fast_insert fu a))
  | |- bk (deflate_slow_insert ?fu ?a ?x0) = _ => apply (eq_trans (bk_deflate_slow_insert fu a x0))
  | |- bk (match ?t with pair _ _ => _ end) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (fst (match ?t with pair _ _ => _ end)) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (if ?c then _ else _) = _ => destruct c
  | |- bk (fst (if ?c then _ else _)) = _ => destruct c
  | |- bk ?y = bk _ => is_var y; assumption
  end.
Ltac bkgoF := repeat bkgoF1.

Lemma bk_deflate_fast_body : forall s flush, bk (fst (deflate_fast_body s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_fast_body]. bkgoF. Qed.
Lemma bk_deflate_slow_body : forall s flush, bk (fst (deflate_slow_body s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_slow_body]. bkgoF. Qed.
Lemma bk_deflate_huff_body : forall s flush, bk (fst (deflate_huff_body s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_huff_body]. bkgoF. Qed.
Lemma bk_deflate_rle_body : forall s flush, bk (fst (deflate_rle_body s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_rle_body]. bkgoF. Qed.

Lemma bk_deflate_fast_loop : forall fuel s flush, bk (fst (deflate_fast_loop fuel s flush)) = bk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_fast_loop].
  pose proof (bk_deflate_fast_body s flush) as X. destruct (deflate_fast_body s flush) as [s1 o]. cbn [fst] in X.
  destruct o; cbn [fst]; [rewrite IH; exact X | exact X | exact X].
Qed.
Lemma bk_deflate_slow_loop : forall fuel s flush, bk (fst (deflate_slow_loop fuel s flush)) = bk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_slow_loop].
  pose proof (bk_deflate_slow_body s flush) as X. destruct (deflate_slow_body s flush) as [s1 o]. cbn [fst] in X.
  destruct o; cbn [fst]; [rewrite IH; exact X | exact X | exact X].
Qed.
Lemma bk_deflate_huff_loop : forall fuel s flush, bk (fst (deflate_huff_loop fuel s flush)) = bk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_huff_loop].
  pose proof (bk_deflate_huff_body s flush) as X. destruct (deflate_huff_body s flush) as [s1 o]. cbn [fst] in X.
  destruct o; cbn [fst]; [rewrite IH; exact X | exact X | exact X].
Qed.
Lemma bk_deflate_rle_loop : forall fuel s flush, bk (fst (deflate_rle_loop fuel s flush)) = bk s.
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|]. cbn [deflate_rle_loop].
  pose proof (bk_deflate_rle_body s flush) as X. destruct (deflate_rle_body s flush) as [s1 o]. cbn [fst] in X.
  destruct o; cbn [fst]; [rewrite IH; exact X | exact X | exact X].
Qed.

Ltac bkgoG1 :=
  lazymatch goal with
  | |- bk ?x = bk ?x => reflexivity
  | |- bk (let x := ?t in @?E x) = bk ?s0 =>
      first [ is_var t; change (bk (E t) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (let x := ?t in @?E x)) = bk ?s0 =>
      first [ is_var t; change (bk (fst (E t)) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (?a, ?b)) = _ => change (bk (fst (a, b))) with (bk a)
  | |- bk (set_bi_buf ?a ?v) = _ => change (bk (set_bi_buf a v)) with (bk a)
  | |- bk (set_bi_valid ?a ?v) = _ => change (bk (set_bi_valid a v)) with (bk a)
  | |- bk (set_bl_count ?a ?v) = _ => change (bk (set_bl_count a v)) with (bk a)
  | |- bk (set_bl_max_code ?a ?v) = _ => change (bk (set_bl_max_code a v)) with (bk a)
  | |- bk (set_bl_tree_dl ?a ?v) = _ => change (bk (set_bl_tree_dl a v)) with (bk a)
  | |- bk (set_bl_tree_fc ?a ?v) = _ => change (bk (set_bl_tree_fc a v)) with (bk a)
  | |- bk (set_block_start ?a ?v) = _ => change (bk (set_block_start a v)) with (bk a)
  | |- bk (set_d_max_code ?a ?v) = _ => change (bk (set_d_max_code a v)) with (bk a)
  | |- bk (set_depth ?a ?v) = _ => change (bk (set_depth a v)) with (bk a)
  | |- bk (set_dyn_dtree_dl ?a ?v) = _ => change (bk (set_dyn_dtree_dl a v)) with (bk a)
  | |- bk (set_dyn_dtree_fc ?a ?v) = _ => change (bk (set_dyn_dtree_fc a v)) with (bk a)
  | |- bk (set_dyn_ltree_dl ?a ?v) = _ => change (bk (set_dyn_ltree_dl a v)) with (bk a)
  | |- bk (set_dyn_ltree_fc ?a ?v) = _ => change (bk (set_dyn_ltree_fc a v)) with (bk a)
  | |- bk (set_good_match ?a ?v) = _ => change (bk (set_good_match a v)) with (bk a)
  | |- bk (set_gzhead ?a ?v) = _ => change (bk (set_gzhead a v)) with (bk a)
  | |- bk (set_gzindex ?a ?v) = _ => change (bk (set_gzindex a v)) with (bk a)
  | |- bk (set_hash_bits ?a ?v) = _ => change (bk (set_hash_bits a v)) with (bk a)
  | |- bk (set_hash_mask ?a ?v) = _ => change (bk (set_hash_mask a v)) with (bk a)
  | |- bk (set_hash_shift ?a ?v) = _ => change (bk (set_hash_shift a v)) with (bk a)
  | |- bk (set_head ?a ?v) = _ => change (bk (set_head a v)) with (bk a)
  | |- bk (set_heap ?a ?v) = _ => change (bk (set_heap a v)) with (bk a)
  | |- bk (set_heap_len ?a ?v) = _ => change (bk (set_heap_len a v)) with (bk a)
  | |- bk (set_heap_max ?a ?v) = _ => change (bk (set_heap_max a v)) with (bk a)
  | |- bk (set_high_water ?a ?v) = _ => change (bk (set_high_water a v)) with (bk a)
  | |- bk (set_ins_h ?a ?v) = _ => change (bk (set_ins_h a v)) with (bk a)
  | |- bk (set_insert ?a ?v) = _ => change (bk (set_insert a v)) with (bk a)
  | |- bk (set_l_max_code ?a ?v) = _ => change (bk (set_l_max_code a v)) with (bk a)
  | |- bk (set_last_flush ?a ?v) = _ => change (bk (set_last_flush a v)) with (bk a)
  | |- bk (set_level ?a ?v) = _ => change (bk (set_level a v)) with (bk a)
  | |- bk (set_lookahead ?a ?v) = _ => change (bk (set_lookahead a v)) with (bk a)
  | |- bk (set_match_available ?a ?v) = _ => change (bk (set_match_available a v)) with (bk a)
  | |- bk (set_match_length ?a ?v) = _ => change (bk (set_match_length a v)) with (bk a)
  | |- bk (set_match_start ?a ?v) = _ => change (bk (set_match_start a v)) with (bk a)
  | |- bk (set_matches ?a ?v) = _ => change (bk (set_matches a v)) with (bk a)
  | |- bk (set_max_chain_length ?a ?v) = _ => change (bk (set_max_chain_length a v)) with (bk a)
  | |- bk (set_max_lazy_match ?a ?v) = _ => change (bk (set_max_lazy_match a v)) with (bk a)
  | |- bk (set_method ?a ?v) = _ => change (bk (set_method a v)) with (bk a)
  | |- bk (set_nice_match ?a ?v) = _ => change (bk (set_nice_match a v)) with (bk a)
  | |- bk (set_opt_len ?a ?v) = _ => change (bk (set_opt_len a v)) with (bk a)
  | |- bk (set_pending ?a ?v) = _ => change (bk (set_pending a v)) with (bk a)
  | |- bk (set_pending_buf ?a ?v) = _ => change (bk (set_pending_buf a v)) with (bk a)
  | |- bk (set_pending_buf_size ?a ?v) = _ => change (bk (set_pending_buf_size a v)) with (bk a)
  | |- bk (set_pending_out ?a ?v) = _ => change (bk (set_pending_out a v)) with (bk a)
  | |- bk (set_prev ?a ?v) = _ => change (bk (set_prev a v)) with (bk a)
  | |- bk (set_prev_length ?a ?v) = _ => change (bk (set_prev_length a v)) with (bk a)
  | |- bk (set_prev_match ?a ?v) = _ => change (bk (set_prev_match a v)) with (bk a)
  | |- bk (set_static_len ?a ?v) = _ => change (bk (set_static_len a v)) with (bk a)
  | |- bk (set_status ?a ?v) = _ => change (bk (set_status a v)) with (bk a)
  | |- bk (set_strategy ?a ?v) = _ => change (bk (set_strategy a v)) with (bk a)
  | |- bk (set_strm ?a ?v) = _ => change (bk (set_strm a v)) with (bk a)
  | |- bk (set_strstart ?a ?v) = _ => change (bk (set_strstart a v)) with (bk a)
  | |- bk (set_sym_end ?a ?v) = _ => change (bk (set_sym_end a v)) with (bk a)
  | |- bk (set_sym_next ?a ?v) = _ => change (bk (set_sym_next a v)) with (bk a)
  | |- bk (set_w_bits ?a ?v) = _ => change (bk (set_w_bits a v)) with (bk a)
  | |- bk (set_w_mask ?a ?v) = _ => change (bk (set_w_mask a v)) with (bk a)
  | |- bk (set_window ?a ?v) = _ => change (bk (set_window a v)) with (bk a)
  | |- bk (set_window_size ?a ?v) = _ => change (bk (set_window_size a v)) with (bk a)
  | |- bk (set_wrap ?a ?v) = _ => change (bk (set_wrap a v)) with (bk a)
  | |- bk (put_byte ?a ?v) = _ => change (bk (put_byte a v)) with (bk a)
  | |- bk (putShortMSB ?a ?v) = _ => change (bk (putShortMSB a v)) with (bk a)
  | |- bk (set_tree_fc ?a ?v ?w) = _ => change (bk (set_tree_fc a v w)) with (bk a)
  | |- bk (set_tree_dl ?a ?v ?w) = _ => change (bk (set_tree_dl a v w)) with (bk a)
  | |- bk (set_max_code ?a ?v ?w) = _ => change (bk (set_max_code a v w)) with (bk a)
  | |- bk (sym_buf_set ?a ?v ?w) = _ => change (bk (sym_buf_set a v w)) with (bk a)
  | |- bk (set_Freq ?a ?v ?w ?x) = _ => change (bk (set_Freq a v w x)) with (bk a)
  | |- bk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_flush_block a x0 x1 x2))
  | |- bk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_stored_block a x0 x1 x2))
  | |- bk (tr_align ?a ) = _ => apply (eq_trans (bk_tr_align a ))
  | |- bk (flush_pending ?a ) = _ => apply (eq_trans (bk_flush_pending a ))
  | |- bk (bi_flush ?a ) = _ => apply (eq_trans (bk_bi_flush a ))
  | |- bk (clear_hash ?a ) = _ => apply (eq_trans (bk_clear_hash a ))
  | |- bk (slide_hash ?a ) = _ => apply (eq_trans (bk_slide_hash a ))
  | |- bk (fill_window ?a ) = _ => apply (eq_trans (bk_fill_window a ))
  | |- bk (flush_block_only ?a ?x0) = _ => apply (eq_trans (bk_flush_block_only a x0))
  | |- bk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (bk_tr_tally_lit a x0))
  | |- bk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_tr_tally_dist a x0 x1))
  | |- bk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (bk_insert_string a x0))
  | |- bk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_read_buf a x0 x1))
  | |- bk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (bk_longest_match a x0))
  | |- bk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (bk_fill_window_insert fu a x0))
  | |- bk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (bk_flush_block a x0))
  | |- bk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (bk_deflate_tail a x0))
  | |- bk (deflate_stored_used ?a ?x0) = _ => apply (eq_trans (bk_deflate_stored_used a x0))
  | |- bk (fst (deflate_stored_fin ?a ?x0)) = _ => apply (eq_trans (bk_deflate_stored_fin a x0))
  | |- bk (fst (deflate_stored_slide ?a ?x0)) = _ => apply (eq_trans (bk_deflate_stored_slide a x0))
  | |- bk (fst (deflate_stored_loop ?fu ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_deflate_stored_loop fu a x0 x1))
  | |- bk (deflate_fast_insert ?fu ?a) = _ => apply (eq_trans (bk_deflate_fast_insert fu a))
  | |- bk (deflate_slow_insert ?fu ?a ?x0) = _ => apply (eq_trans (bk_deflate_slow_insert fu a x0))
  | |- bk (fst (deflate_fast_loop ?fu ?a ?x0)) = _ => apply (eq_trans (bk_deflate_fast_loop fu a x0))
  | |- bk (fst (deflate_slow_loop ?fu ?a ?x0)) = _ => apply (eq_trans (bk_deflate_slow_loop fu a x0))
  | |- bk (fst (deflate_huff_loop ?fu ?a ?x0)) = _ => apply (eq_trans (bk_deflate_huff_loop fu a x0))
  | |- bk (fst (deflate_rle_loop ?fu ?a ?x0)) = _ => apply (eq_trans (bk_deflate_rle_loop fu a x0))
  | |- bk (fst (deflate_stored ?a ?x0)) = _ => apply (eq_trans (bk_deflate_stored a x0))
  | |- bk (match ?t with pair _ _ => _ end) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (fst (match ?t with pair _ _ => _ end)) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (if ?c then _ else _) = _ => destruct c
  | |- bk (fst (if ?c then _ else _)) = _ => destruct c
  | |- bk ?y = bk _ => is_var y; assumption
  end.
Ltac bkgoG := repeat bkgoG1.

Lemma bk_deflate_fast : forall s flush, bk (fst (deflate_fast s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_fast]. bkgoG. Qed.
Lemma bk_deflate_slow : forall s flush, bk (fst (deflate_slow s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_slow]. bkgoG. Qed.
Lemma bk_deflate_huff : forall s flush, bk (fst (deflate_huff s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_huff]. bkgoG. Qed.
Lemma bk_deflate_rle : forall s flush, bk (fst (deflate_rle s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_rle]. bkgoG. Qed.
Lemma bk_run_compress_func : forall s flush, bk (fst (run_compress_func s flush)) = bk s.
Proof.
  intros. cbv beta delta [run_compress_func].
  destruct (_ =? 0); [apply bk_deflate_stored|]. destruct (_ =? _); [apply bk_deflate_huff|].
  destruct (_ =? _); [apply bk_deflate_rle|]. destruct (_ <=? _); [apply bk_deflate_fast | apply bk_deflate_slow].
Qed.
Lemma bk_err_return : forall s e, bk (fst (err_return s e)) = bk s.
Proof. reflexivity. Qed.
Lemma bk_deflate_zlib_header : forall s, bk (fst (deflate_zlib_header s)) = bk s.
Proof. intros. cbv beta delta [deflate_zlib_header]. bkgoG. Qed.
Lemma bk_deflate_gzip_header : forall s, bk (fst (deflate_gzip_header s)) = bk s.
Proof. intros. cbv beta delta [deflate_gzip_header]. bkgoG. Qed.
Lemma bk_deflate_trailer : forall s, bk (fst (deflate_trailer s)) = bk s.
Proof. intros. cbv beta delta [deflate_trailer]. bkgoG. Qed.

Ltac bkgoH1 :=
  lazymatch goal with
  | |- bk ?x = bk ?x => reflexivity
  | |- bk (let x := ?t in @?E x) = bk ?s0 =>
      first [ is_var t; change (bk (E t) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (let x := ?t in @?E x)) = bk ?s0 =>
      first [ is_var t; change (bk (fst (E t)) = bk s0); cbv beta
            | lazymatch type of t with
              | deflate_state => let H := fresh "Hbk" in assert (H : bk t = bk s0); [ | generalize H; generalize t; let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy ]
              | _ => generalize t; let y := fresh "v" in intros y
              end ]
  | |- bk (fst (?a, ?b)) = _ => change (bk (fst (a, b))) with (bk a)
  | |- bk (set_bi_buf ?a ?v) = _ => change (bk (set_bi_buf a v)) with (bk a)
  | |- bk (set_bi_valid ?a ?v) = _ => change (bk (set_bi_valid a v)) with (bk a)
  | |- bk (set_bl_count ?a ?v) = _ => change (bk (set_bl_count a v)) with (bk a)
  | |- bk (set_bl_max_code ?a ?v) = _ => change (bk (set_bl_max_code a v)) with (bk a)
  | |- bk (set_bl_tree_dl ?a ?v) = _ => change (bk (set_bl_tree_dl a v)) with (bk a)
  | |- bk (set_bl_tree_fc ?a ?v) = _ => change (bk (set_bl_tree_fc a v)) with (bk a)
  | |- bk (set_block_start ?a ?v) = _ => change (bk (set_block_start a v)) with (bk a)
  | |- bk (set_d_max_code ?a ?v) = _ => change (bk (set_d_max_code a v)) with (bk a)
  | |- bk (set_depth ?a ?v) = _ => change (bk (set_depth a v)) with (bk a)
  | |- bk (set_dyn_dtree_dl ?a ?v) = _ => change (bk (set_dyn_dtree_dl a v)) with (bk a)
  | |- bk (set_dyn_dtree_fc ?a ?v) = _ => change (bk (set_dyn_dtree_fc a v)) with (bk a)
  | |- bk (set_dyn_ltree_dl ?a ?v) = _ => change (bk (set_dyn_ltree_dl a v)) with (bk a)
  | |- bk (set_dyn_ltree_fc ?a ?v) = _ => change (bk (set_dyn_ltree_fc a v)) with (bk a)
  | |- bk (set_good_match ?a ?v) = _ => change (bk (set_good_match a v)) with (bk a)
  | |- bk (set_gzhead ?a ?v) = _ => change (bk (set_gzhead a v)) with (bk a)
  | |- bk (set_gzindex ?a ?v) = _ => change (bk (set_gzindex a v)) with (bk a)
  | |- bk (set_hash_bits ?a ?v) = _ => change (bk (set_hash_bits a v)) with (bk a)
  | |- bk (set_hash_mask ?a ?v) = _ => change (bk (set_hash_mask a v)) with (bk a)
  | |- bk (set_hash_shift ?a ?v) = _ => change (bk (set_hash_shift a v)) with (bk a)
  | |- bk (set_head ?a ?v) = _ => change (bk (set_head a v)) with (bk a)
  | |- bk (set_heap ?a ?v) = _ => change (bk (set_heap a v)) with (bk a)
  | |- bk (set_heap_len ?a ?v) = _ => change (bk (set_heap_len a v)) with (bk a)
  | |- bk (set_heap_max ?a ?v) = _ => change (bk (set_heap_max a v)) with (bk a)
  | |- bk (set_high_water ?a ?v) = _ => change (bk (set_high_water a v)) with (bk a)
  | |- bk (set_ins_h ?a ?v) = _ => change (bk (set_ins_h a v)) with (bk a)
  | |- bk (set_insert ?a ?v) = _ => change (bk (set_insert a v)) with (bk a)
  | |- bk (set_l_max_code ?a ?v) = _ => change (bk (set_l_max_code a v)) with (bk a)
  | |- bk (set_last_flush ?a ?v) = _ => change (bk (set_last_flush a v)) with (bk a)
  | |- bk (set_level ?a ?v) = _ => change (bk (set_level a v)) with (bk a)
  | |- bk (set_lookahead ?a ?v) = _ => change (bk (set_lookahead a v)) with (bk a)
  | |- bk (set_match_available ?a ?v) = _ => change (bk (set_match_available a v)) with (bk a)
  | |- bk (set_match_length ?a ?v) = _ => change (bk (set_match_length a v)) with (bk a)
  | |- bk (set_match_start ?a ?v) = _ => change (bk (set_match_start a v)) with (bk a)
  | |- bk (set_matches ?a ?v) = _ => change (bk (set_matches a v)) with (bk a)
  | |- bk (set_max_chain_length ?a ?v) = _ => change (bk (set_max_chain_length a v)) with (bk a)
  | |- bk (set_max_lazy_match ?a ?v) = _ => change (bk (set_max_lazy_match a v)) with (bk a)
  | |- bk (set_method ?a ?v) = _ => change (bk (set_method a v)) with (bk a)
  | |- bk (set_nice_match ?a ?v) = _ => change (bk (set_nice_match a v)) with (bk a)
  | |- bk (set_opt_len ?a ?v) = _ => change (bk (set_opt_len a v)) with (bk a)
  | |- bk (set_pending ?a ?v) = _ => change (bk (set_pending a v)) with (bk a)
  | |- bk (set_pending_buf ?a ?v) = _ => change (bk (set_pending_buf a v)) with (bk a)
  | |- bk (set_pending_buf_size ?a ?v) = _ => change (bk (set_pending_buf_size a v)) with (bk a)
  | |- bk (set_pending_out ?a ?v) = _ => change (bk (set_pending_out a v)) with (bk a)
  | |- bk (set_prev ?a ?v) = _ => change (bk (set_prev a v)) with (bk a)
  | |- bk (set_prev_length ?a ?v) = _ => change (bk (set_prev_length a v)) with (bk a)
  | |- bk (set_prev_match ?a ?v) = _ => change (bk (set_prev_match a v)) with (bk a)
  | |- bk (set_static_len ?a ?v) = _ => change (bk (set_static_len a v)) with (bk a)
  | |- bk (set_status ?a ?v) = _ => change (bk (set_status a v)) with (bk a)
  | |- bk (set_strategy ?a ?v) = _ => change (bk (set_strategy a v)) with (bk a)
  | |- bk (set_strm ?a ?v) = _ => change (bk (set_strm a v)) with (bk a)
  | |- bk (set_strstart ?a ?v) = _ => change (bk (set_strstart a v)) with (bk a)
  | |- bk (set_sym_end ?a ?v) = _ => change (bk (set_sym_end a v)) with (bk a)
  | |- bk (set_sym_next ?a ?v) = _ => change (bk (set_sym_next a v)) with (bk a)
  | |- bk (set_w_bits ?a ?v) = _ => change (bk (set_w_bits a v)) with (bk a)
  | |- bk (set_w_mask ?a ?v) = _ => change (bk (set_w_mask a v)) with (bk a)
  | |- bk (set_window ?a ?v) = _ => change (bk (set_window a v)) with (bk a)
  | |- bk (set_window_size ?a ?v) = _ => change (bk (set_window_size a v)) with (bk a)
  | |- bk (set_wrap ?a ?v) = _ => change (bk (set_wrap a v)) with (bk a)
  | |- bk (put_byte ?a ?v) = _ => change (bk (put_byte a v)) with (bk a)
  | |- bk (putShortMSB ?a ?v) = _ => change (bk (putShortMSB a v)) with (bk a)
  | |- bk (set_tree_fc ?a ?v ?w) = _ => change (bk (set_tree_fc a v w)) with (bk a)
  | |- bk (set_tree_dl ?a ?v ?w) = _ => change (bk (set_tree_dl a v w)) with (bk a)
  | |- bk (set_max_code ?a ?v ?w) = _ => change (bk (set_max_code a v w)) with (bk a)
  | |- bk (sym_buf_set ?a ?v ?w) = _ => change (bk (sym_buf_set a v w)) with (bk a)
  | |- bk (set_Freq ?a ?v ?w ?x) = _ => change (bk (set_Freq a v w x)) with (bk a)
  | |- bk (tr_flush_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_flush_block a x0 x1 x2))
  | |- bk (tr_stored_block ?a ?x0 ?x1 ?x2) = _ => apply (eq_trans (bk_tr_stored_block a x0 x1 x2))
  | |- bk (tr_align ?a ) = _ => apply (eq_trans (bk_tr_align a ))
  | |- bk (flush_pending ?a ) = _ => apply (eq_trans (bk_flush_pending a ))
  | |- bk (bi_flush ?a ) = _ => apply (eq_trans (bk_bi_flush a ))
  | |- bk (clear_hash ?a ) = _ => apply (eq_trans (bk_clear_hash a ))
  | |- bk (slide_hash ?a ) = _ => apply (eq_trans (bk_slide_hash a ))
  | |- bk (fill_window ?a ) = _ => apply (eq_trans (bk_fill_window a ))
  | |- bk (flush_block_only ?a ?x0) = _ => apply (eq_trans (bk_flush_block_only a x0))
  | |- bk (fst (tr_tally_lit ?a ?x0)) = _ => apply (eq_trans (bk_tr_tally_lit a x0))
  | |- bk (fst (tr_tally_dist ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_tr_tally_dist a x0 x1))
  | |- bk (fst (insert_string ?a ?x0)) = _ => apply (eq_trans (bk_insert_string a x0))
  | |- bk (fst (read_buf ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_read_buf a x0 x1))
  | |- bk (fst (longest_match ?a ?x0)) = _ => apply (eq_trans (bk_longest_match a x0))
  | |- bk (fill_window_insert ?fu ?a ?x0) = _ => apply (eq_trans (bk_fill_window_insert fu a x0))
  | |- bk (fst (flush_block ?a ?x0)) = _ => apply (eq_trans (bk_flush_block a x0))
  | |- bk (fst (deflate_tail ?a ?x0)) = _ => apply (eq_trans (bk_deflate_tail a x0))
  | |- bk (deflate_stored_used ?a ?x0) = _ => apply (eq_trans (bk_deflate_stored_used a x0))
  | |- bk (fst (deflate_stored_fin ?a ?x0)) = _ => apply (eq_trans (bk_deflate_stored_fin a x0))
  | |- bk (fst (deflate_stored_slide ?a ?x0)) = _ => apply (eq_trans (bk_deflate_stored_slide a x0))
  | |- bk (fst (deflate_stored_loop ?fu ?a ?x0 ?x1)) = _ => apply (eq_trans (bk_deflate_stored_loop fu a x0 x1))
  | |- bk (deflate_fast_insert ?fu ?a) = _ => apply (eq_trans (bk_deflate_fast_insert fu a))
  | |- bk (deflate_slow_insert ?fu ?a ?x0) = _ => apply (eq_trans (bk_deflate_slow_insert fu a x0))
  | |- bk (fst (deflate_fast_loop ?fu ?a ?x0)) = _ => apply (eq_trans (bk_deflate_fast_loop fu a x0))
  | |- bk (fst (deflate_slow_loop ?fu ?a ?x0)) = _ => apply (eq_trans (bk_deflate_slow_loop fu a x0))
  | |- bk (fst (deflate_huff_loop ?fu ?a ?x0)) = _ => apply (eq_trans (bk_deflate_huff_loop fu a x0))
  | |- bk (fst (deflate_rle_loop ?fu ?a ?x0)) = _ => apply (eq_trans (bk_deflate_rle_loop fu a x0))
  | |- bk (fst (deflate_stored ?a ?x0)) = _ => apply (eq_trans (bk_deflate_stored a x0))
  | |- bk (fst (run_compress_func ?a ?x0)) = _ => apply (eq_trans (bk_run_compress_func a x0))
  | |- bk (fst (err_return ?a ?x0)) = _ => apply (eq_trans (bk_err_return a x0))
  | |- bk (fst (deflate_zlib_header ?a)) = _ => apply (eq_trans (bk_deflate_zlib_header a))
  | |- bk (fst (deflate_gzip_header ?a)) = _ => apply (eq_trans (bk_deflate_gzip_header a))
  | |- bk (fst (deflate_trailer ?a)) = _ => apply (eq_trans (bk_deflate_trailer a))
  | |- bk (match ?t with pair _ _ => _ end) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (fst (match ?t with pair _ _ => _ end)) = bk ?s0 =>
      lazymatch type of t with
      | (deflate_state * _)%type => let H := fresh "Hbk" in assert (H : bk (fst t) = bk s0); [ | let y := fresh "y" in let n := fresh "n" in destruct t as [y n]; cbn [fst] in H; cbv beta iota ]
      | _ => let y := fresh "v" in let n := fresh "v" in destruct t as [y n]; cbv beta iota
      end
  | |- bk (match ?o with Some _ => _ | None => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with Some _ => _ | None => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with LCont => _ | LBreak => _ | LRet _ => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with RB_window _ => _ | RB_next_out => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with RB_window _ => _ | RB_next_out => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end) = _ => destruct o; cbv beta iota
  | |- bk (fst (match ?o with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end)) = _ => destruct o; cbv beta iota
  | |- bk (if ?c then _ else _) = _ => destruct c
  | |- bk (fst (if ?c then _ else _)) = _ => destruct c
  | |- bk ?y = bk _ => is_var y; assumption
  end.
Ltac bkgoH := repeat bkgoH1.

Lemma bk_deflate_blocks : forall s flush, bk (fst (deflate_blocks s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_blocks]. bkgoH. Qed.
Lemma bk_deflate_core : forall s flush, bk (fst (deflate_core s flush)) = bk s.
Proof. intros. cbv beta delta [deflate_core]. bkgoH; apply (eq_trans (bk_deflate_blocks _ _)); bkgoH. Qed.

Theorem dkeep_deflate_core : forall s0 st flush, dkeep s0 (fst (deflate_core (set_strm s0 st) flush)).
Proof. intros. apply dkeep_of_bk. rewrite bk_deflate_core. reflexivity. Qed.
