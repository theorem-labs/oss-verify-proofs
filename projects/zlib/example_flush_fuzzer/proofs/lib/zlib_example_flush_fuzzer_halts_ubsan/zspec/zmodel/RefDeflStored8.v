(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk
  TreeModel FillWinModel SendModel BitsModel AdlerModel ZChkAdl SymEx2Expr RefFlushPend1 RefDeflStored2 RefDeflStored3 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition thave (s : deflate_state) : Z := MIN (ds_pending_buf_size s - hdrb s) MAX_STORED.

Definition tmb (s : deflate_state) : Z := MIN (thave s) (ds_w_size s).

Definition tleft (s : deflate_state) : Z := ds_strstart s - ds_block_start s.

Definition tlen (s : deflate_state) : Z := MIN (tleft s) (thave s).

Definition tlast (flush : Z) (s : deflate_state) : Z :=
  if (flush =? Z_FINISH) && (cs_avail_in (ds_strm s) =? 0) && (tlen s =? tleft s) then 1 else 0.

Definition tcond1 (s : deflate_state) : bool := tmb s <=? tleft s.

Definition tcond2 (flush : Z) (s : deflate_state) : bool :=
  (negb (tleft s =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH)
  && (cs_avail_in (ds_strm s) =? 0) && (tleft s <=? thave s).

Definition bs_code (b : block_state) : Z :=
  match b with need_more => 0 | block_done => 1 | finish_started => 2 | finish_done => 3 end.





