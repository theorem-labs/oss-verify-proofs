(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import LmatchModel FillWinModel SendModel DeflFastModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import RefFlushBlk11 RefFlushPend1 RefDeflFastOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section P.
Variables (ws hs PBL OCAP : Z).
Local Notation fbo_ok := (RefDeflFastOk.fbo_ok ws PBL OCAP).

Definition hlit_ok (s : deflate_state) : Prop :=
  lzw s /\ ds_sym_next s + 3 <= ds_sym_end s /\ 1 <= ds_lookahead s
  /\ let s0 := set_match_length s 0 in
     let '(s1, bflush) := tr_tally_lit s0 (arr_get (ds_window s0) (ds_strstart s0)) in
     let s2 := set_lookahead s1 (ds_lookahead s1 - 1) in
     let s3 := set_strstart s2 (ds_strstart s2 + 1) in
     lzw s3 /\ (bflush = true -> fbo_ok s3 0).

Definition huff_trip_ok (s : deflate_state) (flush : Z) : Prop :=
  lzw s
  /\ if Z.eqb (ds_lookahead s) 0 then
       fw_wf ws hs s
       /\ let s1 := fill_window s in
          lzw s1 /\ (if Z.eqb (ds_lookahead s1) 0 then True else hlit_ok s1)
     else hlit_ok s.

Fixpoint huff_loop_ok (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => False
  | S f =>
      huff_trip_ok s flush
      /\ let '(s', o) := deflate_huff_body s flush in
         match o with LCont => huff_loop_ok f s' flush | _ => True end
  end.

Definition tail0_ok (s : deflate_state) (flush : Z) : Prop :=
  lzw s
  /\ let s1 := set_insert s 0 in
     - 2 ^ 63 <= ds_block_start s1 < 2 ^ 63
     /\ if Z.eqb flush Z_FINISH then fbo_ok s1 1
        else (ds_sym_next s1 <> 0 -> fbo_ok s1 0).

Definition huff_ok (s : deflate_state) (flush : Z) : Prop :=
  huff_loop_ok (lz_fuel s) s flush
  /\ let '(s', r) := deflate_huff_loop (lz_fuel s) s flush in
     match r with Some _ => True | None => tail0_ok s' flush end.
End P.
