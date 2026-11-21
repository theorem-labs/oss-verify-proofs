(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import LmatchModel FillWinModel SendModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import DeflFastModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import RefFlushBlk11 RefFlushPend1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition tfb_keeps (s s' : deflate_state) : Prop :=
  ds_window s' = ds_window s /\ ds_prev s' = ds_prev s /\ ds_head s' = ds_head s
  /\ ds_w_size s' = ds_w_size s /\ ds_hash_size s' = ds_hash_size s
  /\ ds_strm s' = cset_data_type (ds_strm s) (cs_data_type (ds_strm s')).

Fixpoint iloop_ok (n : nat) (s : deflate_state) : Prop :=
  match n with
  | O => True
  | S k => lzw s /\ iloop_ok k (istep s)
  end.

Section P.
Variables (ws hs PBL OCAP : Z).

Definition tfb_ok (s : deflate_state) (buf : option Z) (len last : Z) : Prop :=
  BINV PBL s /\ fb_safe s buf len last /\ tfb_keeps s (tr_flush_block s buf len last) /\ len < 2 ^ 32
  /\ match buf with Some off => len <> 0 -> off + len <= 2 * ws | None => True end.

Definition fbo_ok (s : deflate_state) (last : Z) : Prop :=
  let buf := if 0 <=? ds_block_start s then Some (wrap32 (ds_block_start s)) else None in
  let len := wrap64 (ds_strstart s - ds_block_start s) in
  lzw s /\ - 2 ^ 63 <= ds_block_start s < 2 ^ 63
  /\ tfb_ok s buf len last
  /\ let s1 := tr_flush_block s buf len last in
     0 <= ds_strstart s1 < 2 ^ 32
     /\ let s2 := set_block_start s1 (ds_strstart s1) in
        fp_ok PBL OCAP s2
        /\ 0 <= cs_avail_out (ds_strm (flush_pending s2)) < 2 ^ 32.

Definition match_ok (s : deflate_state) : Prop :=
  lzw s /\ ds_sym_next s + 3 <= ds_sym_end s
  /\ (ds_strstart s - ds_match_start s - 1) mod 65536 < 32768
  /\ ds_match_length s <= ds_lookahead s
  /\ let '(s5, bflush) := tr_tally_dist s (wrap32 (ds_strstart s - ds_match_start s)) (ds_match_length s - MIN_MATCH) in
     lzw s5
     /\ let s6 := set_lookahead s5 (ds_lookahead s5 - ds_match_length s5) in
        lzw s6
        /\ if Z.leb (ds_match_length s6) (ds_max_lazy_match s6) && Z.leb MIN_MATCH (ds_lookahead s6) then
             ds_strstart s6 + ds_match_length s6 + 1 < 2 * ws /\ ds_strstart s6 + ds_match_length s6 < 2 ^ 17
             /\ let s7 := set_match_length s6 (ds_match_length s6 - 1) in
                iloop_ok (Z.to_nat (ds_match_length s7)) s7
                /\ let s8 := deflate_fast_insert (Z.to_nat (ds_match_length s7)) s7 in
                   lzw s8
                   /\ let s9 := set_strstart s8 (ds_strstart s8 + 1) in
                      lzw s9 /\ (bflush = true -> fbo_ok s9 0)
           else
             ds_strstart s6 + ds_match_length s6 + 2 <= 2 * ws
             /\ let s7 := set_strstart s6 (ds_strstart s6 + ds_match_length s6) in
                let s8 := set_match_length s7 0 in
                let s9 := set_ins_h s8 (arr_get (ds_window s8) (ds_strstart s8)) in
                let s10 := set_ins_h s9 (update_hash s9 (ds_ins_h s9) (arr_get (ds_window s9) (ds_strstart s9 + 1))) in
                lzw s10 /\ (bflush = true -> fbo_ok s10 0).

Definition lit_ok (s : deflate_state) : Prop :=
  lzw s /\ ds_sym_next s + 3 <= ds_sym_end s /\ 1 <= ds_lookahead s
  /\ let '(s1, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s)) in
     let s2 := set_lookahead s1 (ds_lookahead s1 - 1) in
     let s3 := set_strstart s2 (ds_strstart s2 + 1) in
     lzw s3 /\ (bflush = true -> fbo_ok s3 0).

Definition dispatch_ok (s : deflate_state) : Prop :=
  if Z.leb MIN_MATCH (ds_match_length s) then match_ok s else lit_ok s.

Definition p1_ok (s : deflate_state) : Prop :=
  lzw s /\ 1 <= ds_lookahead s
  /\ let '(s2, hash_head) :=
       if Z.leb MIN_MATCH (ds_lookahead s) then insert_string s (ds_strstart s) else (s, NIL) in
     lzw s2
     /\ if negb (Z.eqb hash_head NIL) && Z.leb (wrap32 (ds_strstart s2 - hash_head)) (ds_w_size s2 - MIN_LOOKAHEAD)
        then lm_pre s2 hash_head
             /\ let '(s3, ml) := longest_match s2 hash_head in
                lzw s3 /\ 0 <= ml < 2 ^ 32 /\ dispatch_ok (set_match_length s3 ml)
        else dispatch_ok s2.

Definition fast_trip_ok (s : deflate_state) (flush : Z) : Prop :=
  lzw s
  /\ if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD then
       fw_wf ws hs s
       /\ let s1 := fill_window s in
          lzw s1
          /\ if Z.ltb (ds_lookahead s1) MIN_LOOKAHEAD && Z.eqb flush Z_NO_FLUSH then True
             else if Z.eqb (ds_lookahead s1) 0 then True
             else p1_ok s1
     else p1_ok s.

Fixpoint fast_loop_ok (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => False
  | S f =>
      fast_trip_ok s flush
      /\ let '(s', o) := deflate_fast_body s flush in
         match o with LCont => fast_loop_ok f s' flush | _ => True end
  end.

Definition tail_ok (s : deflate_state) (flush : Z) : Prop :=
  lzw s
  /\ let s1 := set_insert s (if Z.ltb (ds_strstart s) (MIN_MATCH - 1) then ds_strstart s else MIN_MATCH - 1) in
     - 2 ^ 63 <= ds_block_start s1 < 2 ^ 63
     /\ if Z.eqb flush Z_FINISH then fbo_ok s1 1
        else (ds_sym_next s1 <> 0 -> fbo_ok s1 0).

Definition fast_ok (s : deflate_state) (flush : Z) : Prop :=
  fast_loop_ok (lz_fuel s) s flush
  /\ let '(s', r) := deflate_fast_loop (lz_fuel s) s flush in
     match r with Some _ => True | None => tail_ok s' flush end.

End P.
