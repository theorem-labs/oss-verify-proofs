(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk
  TreeModel FillWinModel SendModel BitsModel AdlerModel ZChkAdl SymEx2Expr RefFlushPend1 RefDeflStored2 RefDeflStored3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition sbrkB (mb : Z) (s : deflate_state) : bool :=
  (slen s <? mb) && negb (slen s =? wrap32 (sleft s + cs_avail_in (ds_strm s))).

Definition slast (s : deflate_state) : Z :=
  if slen s =? wrap32 (sleft s + cs_avail_in (ds_strm s)) then 1 else 0.


