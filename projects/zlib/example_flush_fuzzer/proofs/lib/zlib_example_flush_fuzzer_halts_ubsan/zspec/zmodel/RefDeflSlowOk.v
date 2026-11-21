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

Fixpoint siloop_ok (n : nat) (s : deflate_state) (mi : Z) : Prop :=
  match n with
  | O => True
  | S k => lzw s /\ siloop_ok k
      (let s1 := set_strstart s (ds_strstart s + 1) in
       let s2 := if Z.leb (ds_strstart s1) mi then fst (insert_string s1 (ds_strstart s1)) else s1 in
       set_prev_length s2 (ds_prev_length s2 - 1)) mi
  end.

Section P.
Variables (ws hs PBL OCAP : Z).

Local Notation fbo_ok := (RefDeflFastOk.fbo_ok ws PBL OCAP).

Definition smatch_ok (s : deflate_state) : Prop :=
  lzw s /\ ds_sym_next s + 3 <= ds_sym_end s /\ 3 <= ds_prev_length s <= 258
  /\ (ds_strstart s - 1 - ds_prev_match s - 1) mod 65536 < 32768
  /\ ds_prev_length s <= ds_lookahead s + 1 /\ 3 <= ds_strstart s + ds_lookahead s /\ 0 <= ds_prev_match s < 2 ^ 32
  /\ let max_insert := wrap32 (ds_strstart s + ds_lookahead s - MIN_MATCH) in
     let '(s5, bflush) := tr_tally_dist s (wrap32 (ds_strstart s - 1 - ds_prev_match s)) (ds_prev_length s - MIN_MATCH) in
     lzw s5
     /\ let s6 := set_lookahead s5 (wrap32 (ds_lookahead s5 - (ds_prev_length s5 - 1))) in
        let s7 := set_prev_length s6 (ds_prev_length s6 - 2) in
        siloop_ok (Z.to_nat (ds_prev_length s7)) s7 max_insert
        /\ let s8 := deflate_slow_insert (Z.to_nat (ds_prev_length s7)) s7 max_insert in
           lzw s8
           /\ let s9 := set_match_available s8 0 in
              let s10 := set_match_length s9 (MIN_MATCH - 1) in
              let s11 := set_strstart s10 (ds_strstart s10 + 1) in
              lzw s11
              /\ (bflush = true -> fbo_ok s11 0 /\ lzw (flush_block_only s11 0)).

Definition slit_ok (s : deflate_state) : Prop :=
  lzw s /\ ds_sym_next s + 3 <= ds_sym_end s /\ 1 <= ds_strstart s /\ 0 <= ds_match_available s < 2 ^ 32
  /\ let '(s1, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in
     lzw s1 /\ (bflush = true -> fbo_ok s1 0)
     /\ let s2 := if bflush then flush_block_only s1 0 else s1 in
        lzw s2 /\ 1 <= ds_lookahead s2 /\ 0 <= cs_avail_out (ds_strm s2) < 2 ^ 32.

Definition snone_ok (s : deflate_state) : Prop := lzw s /\ 1 <= ds_lookahead s.

Definition sdisp_ok (s : deflate_state) : Prop :=
  if Z.leb MIN_MATCH (ds_prev_length s) && Z.leb (ds_match_length s) (ds_prev_length s) then smatch_ok s
  else if negb (Z.eqb (ds_match_available s) 0) then slit_ok s else snone_ok s.

Definition sp2_ok (s : deflate_state) (hash_head : Z) : Prop :=
  let s := set_prev_length s (ds_match_length s) in
  let s := set_prev_match s (ds_match_start s) in
  let s := set_match_length s (MIN_MATCH - 1) in
  lzw s /\ 0 <= ds_prev_length s <= 258 /\ 0 <= hash_head < 2 ^ 32
  /\ if negb (Z.eqb hash_head NIL) && Z.ltb (ds_prev_length s) (ds_max_lazy_match s)
        && Z.leb (wrap32 (ds_strstart s - hash_head)) (ds_w_size s - MIN_LOOKAHEAD)
     then
       lm_pre s hash_head
       /\ let '(s, ml) := longest_match s hash_head in
          lzw s /\ 0 <= ml < 2 ^ 32
          /\ let s := set_match_length s ml in
             lzw s /\ 0 <= ds_strategy s < 2 ^ 31 /\ 0 <= ds_prev_length s <= 258
             /\ let s := if Z.leb (ds_match_length s) 5
                            && (Z.eqb (ds_strategy s) Z_FILTERED
                                || (Z.eqb (ds_match_length s) MIN_MATCH
                                    && Z.ltb TOO_FAR (wrap32 (ds_strstart s - ds_match_start s))))
                         then set_match_length s (MIN_MATCH - 1) else s in
                lzw s /\ sdisp_ok s
     else sdisp_ok s.

Definition sp1_ok (s : deflate_state) : Prop :=
  lzw s /\ 1 <= ds_lookahead s
  /\ let '(s2, hash_head) :=
       if Z.leb MIN_MATCH (ds_lookahead s) then insert_string s (ds_strstart s) else (s, NIL) in
     lzw s2 /\ sp2_ok s2 hash_head.

Definition slow_trip_ok (s : deflate_state) (flush : Z) : Prop :=
  lzw s
  /\ if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD then
       fw_wf ws hs s
       /\ let s1 := fill_window s in
          lzw s1
          /\ if Z.ltb (ds_lookahead s1) MIN_LOOKAHEAD && Z.eqb flush Z_NO_FLUSH then True
             else if Z.eqb (ds_lookahead s1) 0 then True
             else sp1_ok s1
     else sp1_ok s.

Fixpoint slow_loop_ok (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => False
  | S f =>
      slow_trip_ok s flush
      /\ let '(s', o) := deflate_slow_body s flush in
         match o with LCont => slow_loop_ok f s' flush | _ => True end
  end.

Definition slow_tail_ok (s : deflate_state) (flush : Z) : Prop :=
  lzw s /\ 0 <= ds_match_available s < 2 ^ 32
  /\ (ds_match_available s <> 0 -> ds_sym_next s < ds_sym_end s /\ 1 <= ds_strstart s)
  /\ let s1 := if negb (Z.eqb (ds_match_available s) 0) then
                 let '(s1, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in
                 set_match_available s1 0
               else s in
     lzw s1
     /\ let s2 := set_insert s1 (if Z.ltb (ds_strstart s1) (MIN_MATCH - 1) then ds_strstart s1 else MIN_MATCH - 1) in
        - 2 ^ 63 <= ds_block_start s2 < 2 ^ 63
        /\ if Z.eqb flush Z_FINISH then fbo_ok s2 1
           else (ds_sym_next s2 <> 0 -> fbo_ok s2 0).

Definition slow_ok (s : deflate_state) (flush : Z) : Prop :=
  slow_loop_ok (lz_fuel s) s flush
  /\ let '(s', r) := deflate_slow_loop (lz_fuel s) s flush in
     match r with Some _ => True | None => slow_tail_ok s' flush end.

End P.
