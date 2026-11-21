(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSlow1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSlow2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation SP := (sp - 112).

Local Ltac nf := cbn [dfF].

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P24 := fresh "P24" in let P22 := fresh "P22" in
  let P20 := fresh "P20" in let P19 := fresh "P19" in let P18 := fresh "P18" in let P21 := fresh "P21" in
  pose proof HRG as (P8 & P2 & P24 & P22 & P20 & P19 & P18 & P21).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 ].

Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].

Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.


Definition hash_st (X : deflate_state) : deflate_state :=
  set_match_length (set_prev_length (set_prev_match (ins_str X (ds_strstart X)) (ds_match_start X)) (ds_match_length X)) 2.

Definition sdist (X : deflate_state) : Z := wrap16 (wrap32 (ds_strstart X - 1 - ds_prev_match X)).

Definition sdist1 (X : deflate_state) : deflate_state :=
  let sn := ds_sym_next X in
  let lb := ds_lit_bufsize X in
  let dist := sdist X in
  let len := wrap8 (ds_prev_length X - 3) in
  let X1 := set_sym_next X (sn + 1) in
  let X2 := set_pending_buf X1 (arr_set (ds_pending_buf X) (lb + sn) (wrap8 dist)) in
  let X3 := set_sym_next X2 (sn + 2) in
  let X4 := set_pending_buf X3 (arr_set (ds_pending_buf X2) (lb + sn + 1) (wrap8 (Z.shiftr dist 8))) in
  let X5 := set_sym_next X4 (sn + 3) in
  let X6 := set_pending_buf X5 (arr_set (ds_pending_buf X4) (lb + sn + 2) (wrap8 len)) in
  let code := arr_get length_code_a len + 257 in
  set_dyn_ltree_fc X6 (arr_set (ds_dyn_ltree_fc X) code (wrap16 (arr_get (ds_dyn_ltree_fc X) code + 1))).

Definition sdist_D (X : deflate_state) : Z := (ds_strstart X - ds_prev_match X + -2) mod 2 ^ 16.


Definition sdist2 (X : deflate_state) (dc : Z) : deflate_state :=
  set_dyn_dtree_fc X (arr_set (ds_dyn_dtree_fc X) dc (wrap16 (arr_get (ds_dyn_dtree_fc X) dc + 1))).

Definition dist2_st (X : deflate_state) : deflate_state :=
  set_prev_length (set_lookahead X (ds_lookahead X + 1 - ds_prev_length X)) (ds_prev_length X - 2).


Definition insl_st (X : deflate_state) (mi : Z) : deflate_state :=
  set_prev_length (if ds_strstart X + 1 <=? mi then ins_str (set_strstart X (ds_strstart X + 1)) (ds_strstart X + 1)
                   else set_strstart X (ds_strstart X + 1))
                  (ds_prev_length X - 1).

Definition exit_st (X : deflate_state) : deflate_state :=
  set_match_length (set_strstart (set_match_available X 0) (ds_strstart X + 1)) 2.


Definition slit1 (X : deflate_state) : deflate_state :=
  let sn := ds_sym_next X in
  let lb := ds_lit_bufsize X in
  let c := arr_get (ds_window X) (ds_strstart X - 1) in
  let X1 := set_sym_next X (sn + 1) in
  let X2 := set_pending_buf X1 (arr_set (ds_pending_buf X) (lb + sn) (wrap8 0)) in
  let X3 := set_sym_next X2 (sn + 2) in
  let X4 := set_pending_buf X3 (arr_set (ds_pending_buf X2) (lb + sn + 1) (wrap8 0)) in
  let X5 := set_sym_next X4 (sn + 3) in
  let X6 := set_pending_buf X5 (arr_set (ds_pending_buf X4) (lb + sn + 2) (wrap8 (wrap8 c))) in
  set_dyn_ltree_fc X6 (arr_set (ds_dyn_ltree_fc X) (wrap8 c) (wrap16 (arr_get (ds_dyn_ltree_fc X) (wrap8 c) + 1))).

End Walk.
