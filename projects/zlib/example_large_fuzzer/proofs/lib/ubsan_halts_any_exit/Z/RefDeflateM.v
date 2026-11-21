(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma put_byte_pending : forall s c, ds_pending (put_byte s c) = ds_pending s + 1.
Proof. intros s c. reflexivity. Qed.


Ltac is_ds_getter f := lazymatch f with ds_status => idtac | ds_pending_buf => idtac | ds_pending_buf_size => idtac | ds_pending_out => idtac | ds_pending => idtac | ds_wrap => idtac | ds_gzhead => idtac | ds_gzindex => idtac | ds_method => idtac | ds_last_flush => idtac | ds_w_size => idtac | ds_w_bits => idtac | ds_w_mask => idtac | ds_window => idtac | ds_window_size => idtac | ds_prev => idtac | ds_head => idtac | ds_ins_h => idtac | ds_hash_size => idtac | ds_hash_bits => idtac | ds_hash_mask => idtac | ds_hash_shift => idtac | ds_block_start => idtac | ds_match_length => idtac | ds_prev_match => idtac | ds_match_available => idtac | ds_strstart => idtac | ds_match_start => idtac | ds_lookahead => idtac | ds_prev_length => idtac | ds_max_chain_length => idtac | ds_max_lazy_match => idtac | ds_level => idtac | ds_strategy => idtac | ds_good_match => idtac | ds_nice_match => idtac | ds_dyn_ltree_fc => idtac | ds_dyn_ltree_dl => idtac | ds_dyn_dtree_fc => idtac | ds_dyn_dtree_dl => idtac | ds_bl_tree_fc => idtac | ds_bl_tree_dl => idtac | ds_l_max_code => idtac | ds_d_max_code => idtac | ds_bl_max_code => idtac | ds_bl_count => idtac | ds_heap => idtac | ds_heap_len => idtac | ds_heap_max => idtac | ds_depth => idtac | ds_lit_bufsize => idtac | ds_sym_next => idtac | ds_sym_end => idtac | ds_opt_len => idtac | ds_static_len => idtac | ds_matches => idtac | ds_insert => idtac | ds_bi_buf => idtac | ds_bi_valid => idtac | ds_high_water => idtac | ds_self_blk => idtac | ds_window_blk => idtac | ds_prev_blk => idtac | ds_head_blk => idtac | ds_pending_buf_blk => idtac | ds_strm => idtac end.
Ltac is_ds_setter f := lazymatch f with set_status => idtac | set_pending_buf => idtac | set_pending_buf_size => idtac | set_pending_out => idtac | set_pending => idtac | set_wrap => idtac | set_gzhead => idtac | set_gzindex => idtac | set_method => idtac | set_last_flush => idtac | set_w_size => idtac | set_w_bits => idtac | set_w_mask => idtac | set_window => idtac | set_window_size => idtac | set_prev => idtac | set_head => idtac | set_ins_h => idtac | set_hash_size => idtac | set_hash_bits => idtac | set_hash_mask => idtac | set_hash_shift => idtac | set_block_start => idtac | set_match_length => idtac | set_prev_match => idtac | set_match_available => idtac | set_strstart => idtac | set_match_start => idtac | set_lookahead => idtac | set_prev_length => idtac | set_max_chain_length => idtac | set_max_lazy_match => idtac | set_level => idtac | set_strategy => idtac | set_good_match => idtac | set_nice_match => idtac | set_dyn_ltree_fc => idtac | set_dyn_ltree_dl => idtac | set_dyn_dtree_fc => idtac | set_dyn_dtree_dl => idtac | set_bl_tree_fc => idtac | set_bl_tree_dl => idtac | set_l_max_code => idtac | set_d_max_code => idtac | set_bl_max_code => idtac | set_bl_count => idtac | set_heap => idtac | set_heap_len => idtac | set_heap_max => idtac | set_depth => idtac | set_lit_bufsize => idtac | set_sym_next => idtac | set_sym_end => idtac | set_opt_len => idtac | set_static_len => idtac | set_matches => idtac | set_insert => idtac | set_bi_buf => idtac | set_bi_valid => idtac | set_high_water => idtac | set_self_blk => idtac | set_window_blk => idtac | set_prev_blk => idtac | set_head_blk => idtac | set_pending_buf_blk => idtac | set_strm => idtac end.

Ltac gs_rw f st tac :=
  let E := fresh "GSE" in
  first [ assert (E : forall s' v', f (st s' v') = v') by (intros; reflexivity)
        | assert (E : forall s' v', f (st s' v') = f s') by (intros; reflexivity) ];
  tac E; clear E.
Ltac gs_pb f tac :=
  let E := fresh "GSE" in
  first [ assert (E : forall s' c', f (put_byte s' c') = f s') by (intros; reflexivity)
        | constr_eq f ds_pending; pose proof put_byte_pending as E ];
  tac E; clear E.
Ltac gs1 :=
  match goal with
  | |- context [?f (?st ?s ?v)] =>
      is_ds_getter f;
      first [ is_ds_setter st; gs_rw f st ltac:(fun E => rewrite !E)
            | constr_eq st put_byte; gs_pb f ltac:(fun E => rewrite !E) ]
  end.
Ltac gs := repeat gs1.
Ltac gs1_in H :=
  match type of H with
  | context [?f (?st ?s ?v)] =>
      is_ds_getter f;
      first [ is_ds_setter st; gs_rw f st ltac:(fun E => rewrite !E in H)
            | constr_eq st put_byte; gs_pb f ltac:(fun E => rewrite !E in H) ]
  end.
Ltac gs_in H := repeat (gs1_in H).


Definition mput (s : deflate_state) (i c pn : Z) : deflate_state :=
  set_pending_buf (set_pending s pn) (arr_set (ds_pending_buf s) i (wrap8 c)).

Lemma mput_put : forall s i c pn c',
  i = ds_pending s -> pn = ds_pending s + 1 -> wrap8 c = wrap8 c' -> mput s i c pn = put_byte s c'.
Proof. intros s i c pn c' -> -> E. unfold mput, put_byte. rewrite E. destruct s; reflexivity. Qed.


Definition mput2 (s : deflate_state) (i c pn : Z) : deflate_state :=
  set_pending_buf (set_pending s pn) (arr_set (ds_pending_buf (set_pending s pn)) i (wrap8 c)).

Fixpoint mputl2 (s : deflate_state) (l : list (Z * Z * Z)) : deflate_state :=
  match l with [] => s | (i, c, pn) :: l' => mputl2 (mput2 s i c pn) l' end.

Ltac mput_step c' :=
  match goal with
  | |- context [mput ?s ?i ?c ?pn] =>
      lazymatch s with
      | context [mput _ _ _ _] => fail
      | _ => rewrite (mput_put s i c pn c'); [| dsred; rewrite ?put_byte_pending; dsred; lia | dsred; rewrite ?put_byte_pending; dsred; lia | ]
      end
  end.
Ltac mput_steps cs :=
  lazymatch cs with
  | nil => idtac
  | ?c' :: ?rest => mput_step c'; [mput_steps rest | ]
  end.


Definition hfix (h : Z) : Z :=
  ((h - h * 138547333 / 2 ^ 32) mod 2 ^ 32 / 2 ^ 1 + h * 138547333 / 2 ^ 32) / 2 ^ 4 * 2 ^ 5
  - ((h - h * 138547333 / 2 ^ 32) mod 2 ^ 32 / 2 ^ 1 + h * 138547333 / 2 ^ 32) / 2 ^ 4 + 31.

Definition hdiv31 (h : Z) : Z := ((h - h * 138547333 / 2 ^ 32) mod 2 ^ 32 / 2 ^ 1 + h * 138547333 / 2 ^ 32) / 2 ^ 4.

Fixpoint hdiv31_chk (fuel : nat) (h : Z) : bool :=
  match fuel with O => true | S f => Z.eqb (hdiv31 h) (h / 31) && hdiv31_chk f (h + 1) end.



Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition zh_lf (X : deflate_state) : Z :=
  if Z.leb Z_HUFFMAN_ONLY (ds_strategy X) || Z.ltb (ds_level X) 2 then 0
  else if Z.ltb (ds_level X) 6 then 1 else if Z.eqb (ds_level X) 6 then 2 else 3.
Definition zh_h0 (X : deflate_state) : Z := Z.shiftl (Z_DEFLATED + Z.shiftl (ds_w_bits X - 8) 4) 8.
Definition zh_h1 (X : deflate_state) : Z := Z.lor (zh_h0 X) (Z.shiftl (zh_lf X) 6).
Definition zh_h2 (X : deflate_state) : Z := if ds_strstart X =? 0 then zh_h1 X else Z.lor (zh_h1 X) PRESET_DICT.
Definition zh_hdr (X : deflate_state) : Z := zh_h2 X + (31 - zh_h2 X mod 31).


Definition zh_st (X : deflate_state) : deflate_state :=
  let s := putShortMSB X (zh_hdr X) in
  if negb (ds_strstart X =? 0) then
    let adler := cs_adler (ds_strm s) in
    putShortMSB (putShortMSB s (wrap32 (Z.shiftr adler 16))) (Z.land adler 65535)
  else s.

Definition zh_stM (X : deflate_state) : deflate_state :=
  let p := ds_pending X in
  let h := hfix (zh_h2 X) in
  let ad := cs_adler (ds_strm X) in
  let s2 := mput (mput X p (h mod 2 ^ 32 / 2 ^ 8) (p + 1)) (p + 1) (szwrap 32 h) (p + 2) in
  if ds_strstart X =? 0 then s2
  else mput (mput (mput (mput s2 (p + 2) ((ad / 2 ^ 16) mod 2 ^ 32 / 2 ^ 8) (p + 3)) (p + 3) (ad / 2 ^ 16) (p + 4))
                  (p + 4) (ad mod 2 ^ 32 / 2 ^ 8) (p + 5)) (p + 5) ad (p + 6).



Definition gz_xfl (X : deflate_state) : Z :=
  if Z.eqb (ds_level X) 9 then 2
  else if Z.leb Z_HUFFMAN_ONLY (ds_strategy X) || Z.ltb (ds_level X) 2 then 4 else 0.

Definition gz_st (X : deflate_state) : deflate_state :=
  let s := set_strm X (cset_adler (ds_strm X) crc32_init) in
  let s := put_byte s 31 in let s := put_byte s 139 in let s := put_byte s 8 in
  let s := put_byte s 0 in let s := put_byte s 0 in let s := put_byte s 0 in let s := put_byte s 0 in let s := put_byte s 0 in
  let s := put_byte s (gz_xfl X) in
  let s := put_byte s OS_CODE in
  set_status s BUSY_STATE.

Definition gz_xflM (X : deflate_state) : Z :=
  Z.lor (if 1 <? ds_strategy X then 1 else 0) (if ds_level X <? 2 then 1 else 0) * 2 ^ 2.

Definition gz_stM (X : deflate_state) (xfl : Z) : deflate_state :=
  let p := ds_pending X in
  let s := set_strm X (cset_adler (ds_strm X) 0) in
  let s := mput2 s p 31 (p + 1) in let s := mput2 s (p + 1) (-117) (p + 2) in let s := mput2 s (p + 2) 8 (p + 3) in
  let s := mput2 s (p + 3) 0 (p + 4) in let s := mput2 s (p + 4) 0 (p + 5) in let s := mput2 s (p + 5) 0 (p + 6) in
  let s := mput2 s (p + 6) 0 (p + 7) in let s := mput2 s (p + 7) 0 (p + 8) in
  let s := mput2 s (p + 8) xfl (p + 9) in
  let s := mput2 s (p + 9) 3 (p + 10) in
  set_status s 113.

Fixpoint mputl (s : deflate_state) (l : list (Z * Z * Z)) : deflate_state :=
  match l with [] => s | (i, c, pn) :: l' => mputl (mput s i c pn) l' end.
Fixpoint putl (s : deflate_state) (cs : list Z) : deflate_state :=
  match cs with [] => s | c :: cs' => putl (put_byte s c) cs' end.
Fixpoint MOK (p : Z) (l : list (Z * Z * Z)) (cs : list Z) : Prop :=
  match l, cs with
  | [], [] => True
  | (i, c, pn) :: l', c' :: cs' => i = p /\ pn = p + 1 /\ wrap8 c = wrap8 c' /\ MOK (p + 1) l' cs'
  | _, _ => False
  end.


