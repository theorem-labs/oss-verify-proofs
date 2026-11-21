(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees TreeModel ScanModel
  SendModel CompressModel RefSendTree3 RefSendTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variables (PBL : Z) (last : Z).

Fixpoint sat_ok (PBLv : Z) (fuel : nat) (s : deflate_state) (blcodes rank : Z) : Prop :=
  match fuel with
  | O => True
  | Datatypes.S f =>
      if rank <? blcodes
      then sb_room PBLv s 3 /\ sat_ok PBLv f (send_bits s (Len s TB (arr_get bl_order_a rank)) 3) blcodes (rank + 1)
      else True
  end.

Lemma sat_loop_step : forall f s b r,
  send_all_trees_loop (Datatypes.S f) s b r =
    (if r <? b then send_all_trees_loop f (send_bits s (Len s TB (arr_get bl_order_a r)) 3) b (r + 1) else s).
Proof. reflexivity. Qed.

Lemma sat_loop_done : forall f s b r, b <= r -> send_all_trees_loop f s b r = s.
Proof. intros [|f] s b r H; [reflexivity|]. rewrite sat_loop_step. rewrite (proj2 (Z.ltb_ge r b) H). reflexivity. Qed.

Lemma sat_ok_step : forall PBLv f s b r,
  sat_ok PBLv (Datatypes.S f) s b r =
    (if r <? b then sb_room PBLv s 3 /\ sat_ok PBLv f (send_bits s (Len s TB (arr_get bl_order_a r)) 3) b (r + 1) else True).
Proof. reflexivity. Qed.

Lemma sb_tree_dl_TB : forall s v l, tree_dl (send_bits s v l) TB = tree_dl s TB.
Proof. intros. apply sb_tree_dl. Qed.

Definition dyn_ok (X : deflate_state) (mb : Z) : Prop :=
  let lmc := ds_l_max_code X in
  let dmc := ds_d_max_code X in
  let X7 := send_bits X (Z.shiftl DYN_TREES 1 + last) 3 in
  let X8 := send_bits X7 (lmc + 1 - 257) 5 in
  let X9 := send_bits X8 (dmc + 1 - 1) 5 in
  let X10 := send_bits X9 (mb + 1 - 4) 4 in
  let X11 := send_all_trees_loop 19 X10 (mb + 1) 0 in
  let X12 := send_tree X11 TL lmc in
  let X13 := send_tree X12 TD dmc in
  (BINV PBL X /\ sb_room PBL X 3 /\ sb_room PBL X7 5 /\ sb_room PBL X8 5 /\ sb_room PBL X9 4 /\ sat_ok PBL 19 X10 (mb + 1) 0)
  /\ (0 <= lmc /\ lmc + 1 < 573) /\ (0 <= dmc /\ dmc + 1 < 61)
  /\ (forall k, 0 <= k < 39 -> 0 <= arr_get (ds_bl_tree_dl X) k < 65536)
  /\ ((forall i, 0 <= i <= lmc -> 0 <= Len X11 TL i <= 15) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl X11 TL) i < 65536)
      /\ (forall c, 0 <= c < 39 -> 0 <= arr_get (ds_bl_tree_fc X11) c < 65536) /\ (forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_dl X11) c < 16)
      /\ RefSendTree4.send_tree_safe PBL X11 TL lmc)
  /\ ((forall i, 0 <= i <= dmc -> 0 <= Len X12 TD i <= 15) /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X12 TD) i < 65536)
      /\ (forall c, 0 <= c < 39 -> 0 <= arr_get (ds_bl_tree_fc X12) c < 65536) /\ (forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_dl X12) c < 16)
      /\ RefSendTree4.send_tree_safe PBL X12 TD dmc)
  /\ (compress_block_ok PBL X13 (ds_dyn_ltree_fc X13) (ds_dyn_ltree_dl X13) (ds_dyn_dtree_fc X13) (ds_dyn_dtree_dl X13)
      /\ (forall i, 0 <= i < 286 -> 0 <= arr_get (ds_dyn_ltree_fc X13) i < 65536)
      /\ (forall i, 0 <= i < 30 -> 0 <= arr_get (ds_dyn_dtree_fc X13) i < 65536)
      /\ (0 <= ds_sym_next X13 /\ ds_sym_next X13 + 3 < 2 ^ 31) /\ (0 <= ds_lit_bufsize X13 < 2 ^ 32)).

Definition dyn_res (X : deflate_state) (mb : Z) : deflate_state :=
  let lmc := ds_l_max_code X in
  let dmc := ds_d_max_code X in
  let X7 := send_bits X (Z.shiftl DYN_TREES 1 + last) 3 in
  let X11 := send_all_trees_loop 19 (send_bits (send_bits (send_bits X7 (lmc + 1 - 257) 5) (dmc + 1 - 1) 5) (mb + 1 - 4) 4) (mb + 1) 0 in
  let X13 := send_tree (send_tree X11 TL lmc) TD dmc in
  compress_block X13 (ds_dyn_ltree_fc X13) (ds_dyn_ltree_dl X13) (ds_dyn_dtree_fc X13) (ds_dyn_dtree_dl X13).

Lemma sb_lmc : forall s v l, ds_l_max_code (send_bits s v l) = ds_l_max_code s.
Proof. intros. rewrite send_bits_shape. destruct s; reflexivity. Qed.
Lemma sb_dmc : forall s v l, ds_d_max_code (send_bits s v l) = ds_d_max_code s.
Proof. intros. rewrite send_bits_shape. destruct s; reflexivity. Qed.

End Walk.
