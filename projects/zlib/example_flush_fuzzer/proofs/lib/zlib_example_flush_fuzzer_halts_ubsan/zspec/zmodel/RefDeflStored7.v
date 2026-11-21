(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk
  TreeModel FillWinModel SendModel BitsModel AdlerModel ZChkAdl SymEx2Expr RefFlushPend1 RefDeflStored2 RefDeflStored3 RefDeflStored4 RefDeflStored5 RefDeflStored6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition slide2 (s : deflate_state) : deflate_state :=
  let s := set_block_start s (ds_block_start s - ds_w_size s) in
  let s := set_strstart s (ds_strstart s - ds_w_size s) in
  let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) (ds_w_size s) (ds_strstart s)) in
  let s := if Z.ltb (ds_matches s) 2 then set_matches s (ds_matches s + 1) else s in
  if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s.

Definition rbc3post (s : deflate_state) (n : Z) : deflate_state :=
  let st := ds_strm s in
  let st := cset_next_in st (cs_next_in st + n) in
  let st := cset_total_in st (wrap64 (cs_total_in st + n)) in
  let s := set_strm s st in
  let s := set_strstart s (ds_strstart s + n) in
  set_insert s (ds_insert s + MIN n (wrap32 (ds_w_size s - ds_insert s))).



