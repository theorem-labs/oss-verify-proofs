(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import RefFlushPend1 RefDeflStored2 RefDeflStored3 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8 RefDeflStored9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition stored_ok (ws PBL ILEN OCAP : Z) (s : deflate_state) (flush : Z) : Prop :=
  let mb := MIN (ds_pending_buf_size s - 5) ws in
  let fuel := Z.to_nat (cs_avail_out (ds_strm s) + 1) in
  let ain0 := cs_avail_in (ds_strm s) in
  let r := deflate_stored_loop fuel s flush mb in
  let s1 := fst r in
  let s3 := deflate_stored_used s1 ain0 in
  5 < ds_pending_buf_size s < 2 ^ 31 /\ 0 <= ain0 < 2 ^ 32
  /\ 0 <= ds_bi_valid s <= 16 /\ 0 <= cs_avail_out (ds_strm s) < 2 ^ 32
  /\ (flush <> Z_FINISH -> loopA_ok ws PBL ILEN OCAP flush mb fuel s)
  /\ (flush = Z_FINISH -> loopB_ok ws PBL ILEN OCAP mb fuel s)
  /\ used_ok ws ILEN ain0 s1
  /\ mid_ok ws ILEN s3
  /\ (snd r = 0 ->
      negb (Z.eqb flush Z_NO_FLUSH) && negb (Z.eqb flush Z_FINISH)
        && Z.eqb (cs_avail_in (ds_strm s3)) 0 && Z.eqb (ds_strstart s3) (ds_block_start s3) = false ->
      fin_ok ws PBL OCAP flush (mid_post s3)).
