(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import LmatchModel FillWinModel SendModel DeflFastModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflSlowOk RefDeflStoredOk RefDeflHuffOk RefDeflRleOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section P.
Variables (ws hs PBL ILEN OCAP : Z).

Definition bd_ok (s : deflate_state) (flush : Z) : Prop :=
  (flush = Z_PARTIAL_FLUSH -> BINV PBL s /\ ds_pending (tr_align s) <= PBL)
  /\ (flush <> Z_PARTIAL_FLUSH -> flush <> Z_BLOCK -> BINV PBL s /\ ds_pending (tr_stored_block s None 0 0) <= PBL)
  /\ (flush = Z_FULL_FLUSH -> lzw (clear_hash (tr_stored_block s None 0 0)))
  /\ let s1 :=
       if Z.eqb flush Z_PARTIAL_FLUSH then tr_align s
       else if negb (Z.eqb flush Z_BLOCK) then
         let s := tr_stored_block s None 0 0 in
         if Z.eqb flush Z_FULL_FLUSH then
           let s := clear_hash s in
           if Z.eqb (ds_lookahead s) 0 then
             let s := set_strstart s 0 in
             let s := set_block_start s 0 in
             set_insert s 0
           else s
         else s
       else s in
     fp_ok PBL OCAP s1 /\ 0 <= cs_avail_out (ds_strm (flush_pending s1)) < 2 ^ 32.

Definition cfunc_ok (s : deflate_state) (flush : Z) : Prop :=
  if Z.eqb (ds_level s) 0 then stored_ok ws PBL ILEN OCAP s flush
  else if Z.eqb (ds_strategy s) Z_HUFFMAN_ONLY then huff_ok ws hs PBL OCAP s flush
  else if Z.eqb (ds_strategy s) Z_RLE then rle_ok ws hs PBL OCAP s flush
  else if Z.leb (ds_level s) 3 then fast_ok ws hs PBL OCAP s flush
  else slow_ok ws hs PBL OCAP s flush.

Definition blocks_ok (s : deflate_state) (flush : Z) : Prop :=
  0 <= ds_level s <= 9 /\ 0 <= ds_strategy s <= 4
  /\ cfunc_ok s flush
  /\ let '(s1, bstate) := run_compress_func s flush in
     let s2 := if block_state_eqb bstate finish_started || block_state_eqb bstate finish_done
               then set_status s1 FINISH_STATE else s1 in
     (block_state_eqb bstate need_more || block_state_eqb bstate finish_started = true ->
        0 <= cs_avail_out (ds_strm s2) < 2 ^ 32)
     /\ (bstate = block_done -> bd_ok s2 flush).
End P.
