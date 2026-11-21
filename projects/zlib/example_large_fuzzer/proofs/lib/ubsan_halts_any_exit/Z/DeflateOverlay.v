(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import NArith.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition nsym (s : deflate_state) : Z := ds_sym_next s / 3.

Definition sym_lcode (s : deflate_state) (j : Z) : Z :=
  if sym_dist s (3 * j) =? 0 then sym_lc s (3 * j)
  else arr_get length_code_a (sym_lc s (3 * j)) + LITERALS + 1.
Definition sym_isdist (s : deflate_state) (j : Z) : bool := negb (sym_dist s (3 * j) =? 0).
Definition sym_dcode (s : deflate_state) (j : Z) : Z := d_code (sym_dist s (3 * j) - 1).

Definition sym_okb (s : deflate_state) (j : Z) : Prop :=
  0 <= sym_lc s (3 * j) < 256 /\ 0 <= sym_dist s (3 * j) <= 32768.

Definition freq_hist (s : deflate_state) : Prop :=
  (forall c, 0 <= c < L_CODES ->
     arr_get (ds_dyn_ltree_fc s) c = zsum (fun j => zind (sym_lcode s j =? c)) 0 (Z.to_nat (nsym s)) + zind (c =? END_BLOCK))
  /\ (forall d, 0 <= d < D_CODES ->
     arr_get (ds_dyn_dtree_fc s) d = zsum (fun j => zind (sym_isdist s j && (sym_dcode s j =? d))) 0 (Z.to_nat (nsym s)))
  /\ (forall b, 0 <= b < BL_CODES -> arr_get (ds_bl_tree_fc s) b = 0).

Definition fb_buf (s : deflate_state) : option Z :=
  if 0 <=? ds_block_start s then Some (wrap32 (ds_block_start s)) else None.
Definition fb_len (s : deflate_state) : Z := wrap64 (ds_strstart s - ds_block_start s).


Definition sym_xl (s : deflate_state) (j : Z) : Z :=
  arr_get extra_lbits_a (arr_get length_code_a (sym_lc s (3 * j))).
Definition sym_xd (s : deflate_state) (j : Z) : Z := arr_get extra_dbits_a (sym_dcode s j).

Definition dcost (LD DD : arr) (s : deflate_state) (j : Z) : Z :=
  if sym_isdist s j
  then arr_get LD (sym_lcode s j) + sym_xl s j + arr_get DD (sym_dcode s j) + sym_xd s j
  else arr_get LD (sym_lcode s j).

Definition scost (s : deflate_state) (j : Z) : Z := dcost static_ltree_dl static_dtree_dl s j.


Definition ov_X0 (s : deflate_state) : deflate_state := tfb_X0 s.
Definition ov_X1 (s : deflate_state) : deflate_state := build_tree (ov_X0 s) TL.
Definition ov_X2 (s : deflate_state) : deflate_state := build_tree (ov_X1 s) TD.
Definition ov_X3 (s : deflate_state) : deflate_state := scan_tree (ov_X2 s) TL (ds_l_max_code (ov_X2 s)).
Definition ov_X4 (s : deflate_state) : deflate_state := scan_tree (ov_X3 s) TD (ds_d_max_code (ov_X3 s)).
Definition ov_X5 (s : deflate_state) : deflate_state := build_tree (ov_X4 s) TB.
Definition ov_mb (s : deflate_state) : Z := tfb_mb (ov_X5 s).
Definition ov_X6 (s : deflate_state) : deflate_state := tfb_X6 (ov_X5 s) (ov_mb s).

Strategy expand [ov_X0 ov_X1 ov_X2 ov_X3 ov_X4 ov_X5 ov_X6 ov_mb].

Lemma ov_X5_tfb : forall s, ov_X5 s = tfb_X5 (tfb_X0 s).
Proof. reflexivity. Qed.
Lemma ov_X6_tfb : forall s, ov_X6 s = tfb_X6 (tfb_X5 (tfb_X0 s)) (tfb_mb (tfb_X5 (tfb_X0 s))).
Proof. reflexivity. Qed.

Definition ov_LD (s : deflate_state) : arr := ds_dyn_ltree_dl (ov_X6 s).
Definition ov_DD (s : deflate_state) : arr := ds_dyn_dtree_dl (ov_X6 s).
Definition ov_BD (s : deflate_state) : arr := ds_bl_tree_dl (ov_X6 s).
Definition ov_BC (s : deflate_state) : arr := ds_bl_tree_fc (ov_X4 s).

Definition ov_hdr (s : deflate_state) : Z :=
  3 + (5 + 5 + 4) + 3 * (ov_mb s + 1)
  + zsum (fun b => arr_get (ov_BC s) b * (arr_get (ov_BD s) b + arr_get extra_blbits_a b)) 0 19.

Definition ov_wpos (s : deflate_state) (k : Z) : Z :=
  ds_bi_valid s + ov_hdr s + zsum (dcost (ov_LD s) (ov_DD s) s) 0 (Z.to_nat k).
Definition ov_rpos (s : deflate_state) (k : Z) : Z := 8 * (ds_lit_bufsize s + 3 * k).

Strategy expand [ov_LD ov_DD ov_BD ov_BC ov_hdr ov_wpos ov_rpos].


Record overlay_pre (s : deflate_state) : Prop := {
  op_lbs : 2048 <= ds_lit_bufsize s <= 32768;
  op_pbl : arr_len (ds_pending_buf s) = ds_lit_bufsize s * 4;
  op_pbb : forall i, 0 <= i < arr_len (ds_pending_buf s) -> 0 <= arr_get (ds_pending_buf s) i < 256;
  op_pending : ds_pending s = 0;
  op_biv : 0 <= ds_bi_valid s <= 7;
  op_level : 1 <= ds_level s <= 9;
  op_strategy : 0 <= ds_strategy s <= 4;
  op_sn : ds_sym_next s = 3 * nsym s;
  op_nsym : 0 <= nsym s <= ds_lit_bufsize s - 1;
  op_syms : forall j, 0 <= j < nsym s -> sym_okb s j;
  op_hist : freq_hist s;
  op_optlen : ds_opt_len s = 0;
  op_statlen : ds_static_len s = 0;
  op_tl : tree_lens s;
  op_fc : forall t i, 0 <= arr_get (tree_fc s t) i < 65536;
  op_dl : forall t i, 0 <= arr_get (tree_dl s t) i < 65536;
  op_depth : forall i, 0 <= arr_get (ds_depth s) i < 256;
  op_lbs2 : exists k, ds_lit_bufsize s = 2 ^ k }.

Definition OVERLAY_CORE : Prop :=
  forall s, overlay_pre s ->
    tfb_branch (ov_X6 s) (fb_buf s) (fb_len s) = 1 ->
    forall k, 0 <= k < nsym s -> ov_wpos s k <= ov_rpos s k.


Fixpoint ov_slacks_loop (fuel : nat) (s : deflate_state) (LD DD : arr) (k w : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => rev acc
  | S f => ov_slacks_loop f s LD DD (k + 1) (w + dcost LD DD s k) ((ov_rpos s k - w) :: acc)
  end.

Definition ov_slacks (s : deflate_state) : list Z :=
  ov_slacks_loop (Z.to_nat (nsym s)) s (ov_LD s) (ov_DD s) 0 (ds_bi_valid s + ov_hdr s) [].

Definition ov_min_slack (s : deflate_state) : option Z :=
  fold_left (fun acc x => match acc with None => Some x | Some m => Some (Z.min m x) end) (ov_slacks s) None.

Definition ov_branch (s : deflate_state) : Z := tfb_branch (ov_X6 s) (fb_buf s) (fb_len s).
Definition overlay_check (s : deflate_state) : bool :=
  if ov_branch s =? 1 then forallb (fun x => 0 <=? x) (ov_slacks s) else true.

Definition ov_cs0 : cstrm := mkCS (arr_make 0 0) 0 0 [] 0 0 0 MSG_NULL Z_UNKNOWN 0.
Definition ov_base (lbs biv strategy bstart str : Z) : deflate_state :=
  let s := ds_of_oracle (fun _ => 0) 0%N ov_cs0 in
  let s := set_lit_bufsize s lbs in
  let s := set_pending_buf s (arr_make (lbs * 4) 0) in
  let s := set_pending_buf_size s (lbs * 4) in
  let s := set_sym_end s ((lbs - 1) * 3) in
  let s := set_level s 6 in
  let s := set_strategy s strategy in
  let s := set_bi_valid s biv in
  let s := set_block_start s bstart in
  let s := set_strstart s str in
  let s := set_w_size s 32768 in
  init_block s.
Definition ov_tally (s : deflate_state) (sym : Z * Z) : deflate_state :=
  let '(dist, lc) := sym in
  if dist =? 0 then fst (tr_tally_lit s lc) else fst (tr_tally_dist s dist lc).
Definition mk_overlay_state (lbs biv strategy bstart str : Z) (syms : list (Z * Z)) : deflate_state :=
  fold_left ov_tally syms (ov_base lbs biv strategy bstart str).

Definition ov_W (x : deflate_state) : Z := 8 * ds_pending x + ds_bi_valid x.
Strategy expand [ov_W].


