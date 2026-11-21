(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import LmatchModel FillWinModel SendModel DeflFastModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import RefFlushBlk11 RefFlushPend1 RefDeflFastOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import RefDeflHuffOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section P.
Variables (ws hs PBL OCAP : Z).
Local Notation fbo_ok := (RefDeflFastOk.fbo_ok ws PBL OCAP).

Definition rbody_ok (s : deflate_state) : Prop :=
  lzw s /\ 1 <= ds_lookahead s /\ ds_sym_next s + 3 <= ds_sym_end s
  /\ (MIN_MATCH <= ds_lookahead s -> 0 < ds_strstart s -> ds_strstart s + MAX_MATCH < arr_len (ds_window s))
  /\ let s0 := set_match_length s 0 in
     let s2 :=
       if Z.leb MIN_MATCH (ds_lookahead s0) && Z.ltb 0 (ds_strstart s0) then
         let w := ds_window s0 in
         let scan := ds_strstart s0 - 1 in
         let prev := arr_get w scan in
         let '(scan, ok) := rle_cmpk 3%nat w prev scan in
         if ok then
           let strend := ds_strstart s0 + MAX_MATCH in
           let scan := rle_cmp_loop 33%nat w prev scan strend in
           let s := set_match_length s0 (MAX_MATCH - (strend - scan)) in
           if Z.ltb (ds_lookahead s) (ds_match_length s) then set_match_length s (ds_lookahead s) else s
         else s0
       else s0 in
     lzw s2
     /\ if Z.leb MIN_MATCH (ds_match_length s2) then
          let '(s3, bflush) := tr_tally_dist s2 1 (ds_match_length s2 - MIN_MATCH) in
          let s4 := set_lookahead s3 (ds_lookahead s3 - ds_match_length s3) in
          let s5 := set_strstart s4 (ds_strstart s4 + ds_match_length s4) in
          let s6 := set_match_length s5 0 in
          lzw s6 /\ (bflush = true -> fbo_ok s6 0)
        else
          let '(s3, bflush) := tr_tally_lit s2 (arr_get (ds_window s2) (ds_strstart s2)) in
          let s4 := set_lookahead s3 (ds_lookahead s3 - 1) in
          let s5 := set_strstart s4 (ds_strstart s4 + 1) in
          lzw s5 /\ (bflush = true -> fbo_ok s5 0).

Definition rle_trip_ok (s : deflate_state) (flush : Z) : Prop :=
  lzw s
  /\ if Z.leb (ds_lookahead s) MAX_MATCH then
       fw_wf ws hs s
       /\ let s1 := fill_window s in
          lzw s1
          /\ (if Z.leb (ds_lookahead s1) MAX_MATCH && Z.eqb flush Z_NO_FLUSH then True
              else if Z.eqb (ds_lookahead s1) 0 then True
              else rbody_ok s1)
     else rbody_ok s.

Fixpoint rle_loop_ok (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => False
  | S f =>
      rle_trip_ok s flush
      /\ let '(s', o) := deflate_rle_body s flush in
         match o with LCont => rle_loop_ok f s' flush | _ => True end
  end.

Definition rle_ok (s : deflate_state) (flush : Z) : Prop :=
  rle_loop_ok (lz_fuel s) s flush
  /\ let '(s', r) := deflate_rle_loop (lz_fuel s) s flush in
     match r with Some _ => True | None => tail0_ok ws PBL OCAP s' flush end.
End P.
