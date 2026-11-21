(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees TreeModel ScanModel
  FillWinModel SendModel CompressModel BuildTreeModel GenBitlenModel TreesTab RefSendTree3 RefSendTree4 RefFlushBlk9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition stat_ok (PBL : Z) (X : deflate_state) (last : Z) : Prop :=
  BINV PBL X /\ sb_room PBL X 3
  /\ (let X1 := send_bits X (Z.shiftl STATIC_TREES 1 + last) 3 in
      compress_block_ok PBL X1 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl
      /\ (0 <= ds_sym_next X1 /\ ds_sym_next X1 + 3 < 2 ^ 31) /\ (0 <= ds_lit_bufsize X1 < 2 ^ 32)).

Definition sto_ok (PBL : Z) (ds X : deflate_state) (buf : option Z) (len last : Z) : Prop :=
  BINV PBL X /\ ds_pending (tr_stored_block X buf len last) <= PBL /\ ds_window X = ds_window ds.

Definition tail_ok (PBL : Z) (X7 : deflate_state) (last : Z) : Prop :=
  BINV PBL (init_block X7) /\ (last <> 0 -> ds_pending (bi_windup (init_block X7)) <= PBL).

Definition fb_safe (ds : deflate_state) (buf : option Z) (len last : Z) : Prop :=
  let PBL := arr_len (ds_pending_buf ds) in
  0 <= ds_level ds < 100 /\ - 2 ^ 31 <= cs_data_type (ds_strm ds) < 2 ^ 31 /\ 0 < PBL
  /\ cs_data_type (ds_strm (tr_flush_block ds buf len last))
       = (if (0 <? ds_level ds) && (cs_data_type (ds_strm ds) =? Z_UNKNOWN) then detect_data_type ds else cs_data_type (ds_strm ds))
  /\ if 0 <? ds_level ds then
       (cs_data_type (ds_strm ds) = Z_UNKNOWN -> forall k, 0 <= k < 573 -> 0 <= arr_get (ds_dyn_ltree_fc ds) k < 65536)
       /\ (let s0 := if cs_data_type (ds_strm ds) =? Z_UNKNOWN
                     then set_strm ds (cset_data_type (ds_strm ds) (detect_data_type ds)) else ds in
           let X1 := build_tree s0 TL in
           let X2 := build_tree X1 TD in
           let mcl := ds_l_max_code X2 in
           let X3 := scan_tree X2 TL mcl in
           let mcd := ds_d_max_code X3 in
           let X4 := scan_tree X3 TD mcd in
           let X5 := build_tree X4 TB in
           let mb := build_bl_tree_loop 17 X5 18 in
           let X6 := set_opt_len X5 (wrap64 (ds_opt_len X5 + 3 * (mb + 1) + 5 + 5 + 4)) in
           let opt_lenb := Z.shiftr (wrap64 (ds_opt_len X6 + 3 + 7)) 3 in
           let static_lenb := Z.shiftr (wrap64 (ds_static_len X6 + 3 + 7)) 3 in
           let opt_lenb0 := if (static_lenb <=? opt_lenb) || (ds_strategy X6 =? Z_FIXED) then static_lenb else opt_lenb in
           let sto := (wrap64 (len + 4) <=? opt_lenb0) && match buf with Some _ => true | None => false end in
           let sta := static_lenb =? opt_lenb0 in
           let X7 := if sto then tr_stored_block X6 buf len last
                     else if sta
                     then (let s := send_bits X6 (Z.shiftl STATIC_TREES 1 + last) 3 in
                           compress_block s static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl)
                     else (let s := send_bits X6 (Z.shiftl DYN_TREES 1 + last) 3 in
                           let s := send_all_trees s (ds_l_max_code s + 1) (ds_d_max_code s + 1) (mb + 1) in
                           compress_block s (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s)) in
           bt_safe s0 TL /\ bt_safe X1 TD
           /\ (0 <= mcl /\ mcl + 1 < 573) /\ (forall i, 0 <= i <= mcl -> 0 <= Len X2 TL i <= 15)
           /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl X2 TL) i < 65536)
           /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X2) i < 65536)
           /\ (0 <= mcd /\ mcd + 1 < 61) /\ (forall i, 0 <= i <= mcd -> 0 <= Len X3 TD i <= 15)
           /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X3 TD) i < 65536)
           /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X3) i < 65536)
           /\ bt_safe X4 TB
           /\ (forall k, 0 <= k < 39 -> 0 <= arr_get (tree_dl X5 TB) k < 65536)
           /\ (0 <= ds_opt_len X5 < 2 ^ 64) /\ (0 <= ds_static_len X5 < 2 ^ 64) /\ (0 <= ds_strategy X5 <= 4)
           /\ (if sto then sto_ok PBL ds X6 buf len last
               else if sta then stat_ok PBL X6 last
               else dyn_ok PBL last X6 mb)
           /\ tail_ok PBL X7 last)
     else
       match buf with
       | Some _ => sto_ok PBL ds ds buf len last /\ tail_ok PBL (tr_stored_block ds buf len last) last
       | None => stat_ok PBL ds last
                 /\ tail_ok PBL (compress_block (send_bits ds (Z.shiftl STATIC_TREES 1 + last) 3)
                                   static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl) last
       end.


Lemma tfb_eq_raw : forall ds buf len last, 0 < ds_level ds ->
  tr_flush_block ds buf len last =
   (let s := if cs_data_type (ds_strm ds) =? Z_UNKNOWN
            then set_strm ds (cset_data_type (ds_strm ds) (detect_data_type ds)) else ds in
    let s0 := build_tree s TL in
    let s1 := build_tree s0 TD in
    let s2 := scan_tree s1 TL (ds_l_max_code s1) in
    let s3 := scan_tree s2 TD (ds_d_max_code s2) in
    let s4 := build_tree s3 TB in
    let max_blindex := build_bl_tree_loop 17 s4 (BL_CODES - 1) in
    let s5 := set_opt_len s4 (wrap64 (ds_opt_len s4 + 3 * (max_blindex + 1) + 5 + 5 + 4)) in
    let opt_lenb := Z.shiftr (wrap64 (ds_opt_len s5 + 3 + 7)) 3 in
    let static_lenb := Z.shiftr (wrap64 (ds_static_len s5 + 3 + 7)) 3 in
    let opt_lenb0 := if (static_lenb <=? opt_lenb) || (ds_strategy s5 =? Z_FIXED) then static_lenb else opt_lenb in
    let s6 := if (wrap64 (len + 4) <=? opt_lenb0) && match buf with Some _ => true | None => false end
              then tr_stored_block s5 buf len last
              else if static_lenb =? opt_lenb0
              then (let s0 := send_bits s5 (Z.shiftl STATIC_TREES 1 + last) 3 in
                    compress_block s0 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl)
              else (let s0 := send_bits s5 (Z.shiftl DYN_TREES 1 + last) 3 in
                    let s1 := send_all_trees s0 (ds_l_max_code s0 + 1) (ds_d_max_code s0 + 1) (max_blindex + 1) in
                    compress_block s1 (ds_dyn_ltree_fc s1) (ds_dyn_ltree_dl s1) (ds_dyn_dtree_fc s1) (ds_dyn_dtree_dl s1)) in
    let s7 := init_block s6 in
    if negb (last =? 0) then bi_windup s7 else s7).
Proof.
  intros ds buf len last Hl.
  cbv beta delta [tr_flush_block build_bl_tree].
  rewrite (proj2 (Z.ltb_lt 0 _) Hl). reflexivity.
Qed.

Lemma tfb_eq_low : forall ds buf len last, ds_level ds <= 0 -> 0 <= len < 2 ^ 32 ->
  tr_flush_block ds buf len last =
    (let X7 := match buf with
               | Some _ => tr_stored_block ds buf len last
               | None => compress_block (send_bits ds (Z.shiftl STATIC_TREES 1 + last) 3)
                           static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl
               end in
     let X8 := init_block X7 in
     if negb (last =? 0) then bi_windup X8 else X8).
Proof.
  intros ds buf len last Hl Hlen.
  cbv beta delta [tr_flush_block]. rewrite (proj2 (Z.ltb_ge 0 _) Hl).
  rewrite !wrap64_id by lia. rewrite (proj2 (Z.leb_le (len + 4) (len + 5))) by lia. rewrite Z.eqb_refl.
  destruct buf; reflexivity.
Qed.

