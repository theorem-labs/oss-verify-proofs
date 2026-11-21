(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface DeflateState Trees DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Inductive loop_out : Set := LCont | LBreak | LRet (bs : block_state).

Definition flush_block (s : deflate_state) (last : Z) : deflate_state * option block_state :=
  let s := flush_block_only s last in
  if Z.eqb (cs_avail_out (ds_strm s)) 0
  then (s, Some (if negb (Z.eqb last 0) then finish_started else need_more))
  else (s, None).

Definition deflate_tail (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  if Z.eqb flush Z_FINISH then
    let '(s, r) := flush_block s 1 in
    match r with Some bs => (s, bs) | None => (s, finish_done) end
  else
    let '(s, r) := if negb (Z.eqb (ds_sym_next s) 0) then flush_block s 0 else (s, None) in
    match r with Some bs => (s, bs) | None => (s, block_done) end.

Definition lz_fuel (s : deflate_state) : nat :=
  Z.to_nat (ds_lookahead s + cs_avail_in (ds_strm s) + 1).


Definition MIN (a b : Z) : Z := if Z.ltb b a then b else a.

Definition deflate_stored_body (s : deflate_state) (flush min_block : Z)
  : deflate_state * Z * bool :=
  let len := MAX_STORED in
  let have := Z.shiftr (ds_bi_valid s + 42) 3 in
  if Z.ltb (cs_avail_out (ds_strm s)) have then (s, 0, true)
  else
    let have := cs_avail_out (ds_strm s) - have in
    let left := wrap32 (ds_strstart s - ds_block_start s) in
    let avail_in := cs_avail_in (ds_strm s) in
    let len := if Z.ltb (left + avail_in) len
               then wrap32 (left + avail_in) else len in
    let len := if Z.ltb have len then have else len in
    if Z.ltb len min_block
       && ((Z.eqb len 0 && negb (Z.eqb flush Z_FINISH))
           || Z.eqb flush Z_NO_FLUSH
           || negb (Z.eqb len (wrap32 (left + avail_in))))
    then (s, 0, true)
    else
      let last := if Z.eqb flush Z_FINISH && Z.eqb len (wrap32 (left + avail_in)) then 1 else 0 in
      let s := tr_stored_block s None 0 last in
      let pb := ds_pending_buf s in
      let p := ds_pending s in
      let pb := arr_set pb (p - 4) (wrap8 len) in
      let pb := arr_set pb (p - 3) (wrap8 (Z.shiftr len 8)) in
      let pb := arr_set pb (p - 2) (wrap8 (Z.lnot len)) in
      let pb := arr_set pb (p - 1) (wrap8 (Z.shiftr (wrap32 (Z.lnot len)) 8)) in
      let s := set_pending_buf s pb in
      let s := flush_pending s in
      let '(s, len) :=
        if negb (Z.eqb left 0) then
          let left := if Z.ltb len left then len else left in
          let st := ds_strm s in
          let st := cs_emit st (arr_slice (ds_window s) (ds_block_start s) left) in
          let st := cset_avail_out st (cs_avail_out st - left) in
          let st := cset_total_out st (wrap64 (cs_total_out st + left)) in
          let s := set_strm s st in
          let s := set_block_start s (ds_block_start s + left) in
          (s, len - left)
        else (s, len) in
      let s :=
        if negb (Z.eqb len 0) then
          let '(s, _) := read_buf s RB_next_out len in
          let st := ds_strm s in
          let st := cset_avail_out st (cs_avail_out st - len) in
          let st := cset_total_out st (wrap64 (cs_total_out st + len)) in
          set_strm s st
        else s in
      (s, last, false).

Fixpoint deflate_stored_loop (fuel : nat) (s : deflate_state) (flush min_block : Z)
  : deflate_state * Z :=
  match fuel with
  | O => (s, 0)
  | S f =>
      let '(s, last, broke) := deflate_stored_body s flush min_block in
      if broke then (s, last)
      else if Z.eqb last 0 then deflate_stored_loop f s flush min_block
      else (s, last)
  end.


Definition deflate_stored_used (s : deflate_state) (used : Z) : deflate_state :=
  let used := wrap32 (used - cs_avail_in (ds_strm s)) in
  let s :=
    if negb (Z.eqb used 0) then
      let s :=
        if Z.leb (ds_w_size s) used then
          let s := set_matches s 2 in
          let st := ds_strm s in
          let s := set_window s (arr_upd (ds_window s) 0
                     (arr_slice (cs_input st) (cs_next_in st - ds_w_size s) (ds_w_size s))) in
          let s := set_strstart s (ds_w_size s) in
          set_insert s (ds_strstart s)
        else
          let s :=
            if Z.leb (ds_window_size s - ds_strstart s) used then
              let s := set_strstart s (ds_strstart s - ds_w_size s) in
              let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) (ds_w_size s) (ds_strstart s)) in
              let s := if Z.ltb (ds_matches s) 2 then set_matches s (ds_matches s + 1) else s in
              if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s
            else s in
          let st := ds_strm s in
          let s := set_window s (arr_upd (ds_window s) (ds_strstart s)
                     (arr_slice (cs_input st) (cs_next_in st - used) used)) in
          let s := set_strstart s (ds_strstart s + used) in
          set_insert s (ds_insert s + MIN used (wrap32 (ds_w_size s - ds_insert s))) in
      set_block_start s (ds_strstart s)
    else s in
  if Z.ltb (ds_high_water s) (ds_strstart s) then set_high_water s (ds_strstart s) else s.

Definition deflate_stored_fin (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  let s := if Z.ltb (ds_high_water s) (ds_strstart s) then set_high_water s (ds_strstart s) else s in
  let have := Z.shiftr (ds_bi_valid s + 42) 3 in
  let have := MIN (ds_pending_buf_size s - have) MAX_STORED in
  let min_block := MIN have (ds_w_size s) in
  let left := wrap32 (ds_strstart s - ds_block_start s) in
  if Z.leb min_block left
     || ((negb (Z.eqb left 0) || Z.eqb flush Z_FINISH) && negb (Z.eqb flush Z_NO_FLUSH)
         && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.leb left have)
  then
    let len := MIN left have in
    let last := if Z.eqb flush Z_FINISH && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.eqb len left
                then 1 else 0 in
    let s := tr_stored_block s (Some (ds_block_start s)) len last in
    let s := set_block_start s (ds_block_start s + len) in
    let s := flush_pending s in
    (s, if negb (Z.eqb last 0) then finish_started else need_more)
  else (s, need_more).

Definition deflate_stored_slide (s : deflate_state) (have : Z) : deflate_state * Z :=
  let s := set_block_start s (ds_block_start s - ds_w_size s) in
  let s := set_strstart s (ds_strstart s - ds_w_size s) in
  let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) (ds_w_size s) (ds_strstart s)) in
  let s := if Z.ltb (ds_matches s) 2 then set_matches s (ds_matches s + 1) else s in
  let have := wrap32 (have + ds_w_size s) in
  let s := if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s in
  (s, have).

Definition deflate_stored_mid (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  let have := wrap32 (ds_window_size s - ds_strstart s) in
  let '(s, have) :=
    if Z.ltb have (cs_avail_in (ds_strm s)) && Z.leb (ds_w_size s) (ds_block_start s)
    then deflate_stored_slide s have
    else (s, have) in
  let have := if Z.ltb (cs_avail_in (ds_strm s)) have then cs_avail_in (ds_strm s) else have in
  let s :=
    if negb (Z.eqb have 0) then
      let '(s, _) := read_buf s (RB_window (ds_strstart s)) have in
      let s := set_strstart s (ds_strstart s + have) in
      set_insert s (ds_insert s + MIN have (wrap32 (ds_w_size s - ds_insert s)))
    else s in
  deflate_stored_fin s flush.

Definition deflate_stored (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  let min_block := wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s)) in
  let used := cs_avail_in (ds_strm s) in
  let '(s, last) := deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm s) + 1)) s flush min_block in
  let s := deflate_stored_used s used in
  if negb (Z.eqb last 0) then (s, finish_done)
  else if negb (Z.eqb flush Z_NO_FLUSH) && negb (Z.eqb flush Z_FINISH)
          && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.eqb (ds_strstart s) (ds_block_start s)
  then (s, block_done)
  else deflate_stored_mid s flush.


Fixpoint deflate_fast_insert (fuel : nat) (s : deflate_state) : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      let s := set_strstart s (ds_strstart s + 1) in
      let '(s, _) := insert_string s (ds_strstart s) in
      let s := set_match_length s (ds_match_length s - 1) in
      if negb (Z.eqb (ds_match_length s) 0) then deflate_fast_insert f s else s
  end.

Definition deflate_fast_body (s : deflate_state) (flush : Z) : deflate_state * loop_out :=
  let '(s, early) :=
    if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD then
      let s := fill_window s in
      if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD && Z.eqb flush Z_NO_FLUSH then (s, Some (LRet need_more))
      else if Z.eqb (ds_lookahead s) 0 then (s, Some LBreak)
      else (s, None)
    else (s, None) in
  match early with
  | Some o => (s, o)
  | None =>
  let '(s, hash_head) :=
    if Z.leb MIN_MATCH (ds_lookahead s) then insert_string s (ds_strstart s) else (s, NIL) in
  let s :=
    if negb (Z.eqb hash_head NIL)
       && Z.leb (wrap32 (ds_strstart s - hash_head)) (ds_w_size s - MIN_LOOKAHEAD)
    then let '(s, ml) := longest_match s hash_head in set_match_length s ml
    else s in
  let '(s, bflush) :=
    if Z.leb MIN_MATCH (ds_match_length s) then
      let '(s, bflush) := tr_tally_dist s (wrap32 (ds_strstart s - ds_match_start s))
                                          (ds_match_length s - MIN_MATCH) in
      let s := set_lookahead s (ds_lookahead s - ds_match_length s) in
      let s :=
        if Z.leb (ds_match_length s) (ds_max_lazy_match s)
           && Z.leb MIN_MATCH (ds_lookahead s)
        then
          let s := set_match_length s (ds_match_length s - 1) in
          let s := deflate_fast_insert (Z.to_nat (ds_match_length s)) s in
          set_strstart s (ds_strstart s + 1)
        else
          let s := set_strstart s (ds_strstart s + ds_match_length s) in
          let s := set_match_length s 0 in
          let s := set_ins_h s (arr_get (ds_window s) (ds_strstart s)) in
          set_ins_h s (update_hash s (ds_ins_h s) (arr_get (ds_window s) (ds_strstart s + 1)))
      in (s, bflush)
    else
      let '(s, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s)) in
      let s := set_lookahead s (ds_lookahead s - 1) in
      let s := set_strstart s (ds_strstart s + 1) in
      (s, bflush) in
  if bflush then
    let '(s, r) := flush_block s 0 in
    match r with Some bs => (s, LRet bs) | None => (s, LCont) end
  else (s, LCont)
  end.

Fixpoint deflate_fast_loop (fuel : nat) (s : deflate_state) (flush : Z)
  : deflate_state * option block_state :=
  match fuel with
  | O => (s, None)
  | S f =>
      let '(s, o) := deflate_fast_body s flush in
      match o with
      | LCont => deflate_fast_loop f s flush
      | LBreak => (s, None)
      | LRet bs => (s, Some bs)
      end
  end.

Definition deflate_fast (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  let '(s, r) := deflate_fast_loop (lz_fuel s) s flush in
  match r with
  | Some bs => (s, bs)
  | None =>
      let s := set_insert s (if Z.ltb (ds_strstart s) (MIN_MATCH - 1) then ds_strstart s else MIN_MATCH - 1) in
      deflate_tail s flush
  end.


Fixpoint deflate_slow_insert (fuel : nat) (s : deflate_state) (max_insert : Z) : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      let s := set_strstart s (ds_strstart s + 1) in
      let s := if Z.leb (ds_strstart s) max_insert
               then fst (insert_string s (ds_strstart s)) else s in
      let s := set_prev_length s (ds_prev_length s - 1) in
      if negb (Z.eqb (ds_prev_length s) 0) then deflate_slow_insert f s max_insert else s
  end.

Definition deflate_slow_body (s : deflate_state) (flush : Z) : deflate_state * loop_out :=
  let '(s, early) :=
    if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD then
      let s := fill_window s in
      if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD && Z.eqb flush Z_NO_FLUSH then (s, Some (LRet need_more))
      else if Z.eqb (ds_lookahead s) 0 then (s, Some LBreak)
      else (s, None)
    else (s, None) in
  match early with
  | Some o => (s, o)
  | None =>
  let '(s, hash_head) :=
    if Z.leb MIN_MATCH (ds_lookahead s) then insert_string s (ds_strstart s) else (s, NIL) in
  let s := set_prev_length s (ds_match_length s) in
  let s := set_prev_match s (ds_match_start s) in
  let s := set_match_length s (MIN_MATCH - 1) in
  let s :=
    if negb (Z.eqb hash_head NIL) && Z.ltb (ds_prev_length s) (ds_max_lazy_match s)
       && Z.leb (wrap32 (ds_strstart s - hash_head)) (ds_w_size s - MIN_LOOKAHEAD)
    then
      let '(s, ml) := longest_match s hash_head in
      let s := set_match_length s ml in
      if Z.leb (ds_match_length s) 5
         && (Z.eqb (ds_strategy s) Z_FILTERED
             || (Z.eqb (ds_match_length s) MIN_MATCH
                 && Z.ltb TOO_FAR (wrap32 (ds_strstart s - ds_match_start s))))
      then set_match_length s (MIN_MATCH - 1)
      else s
    else s in
  if Z.leb MIN_MATCH (ds_prev_length s) && Z.leb (ds_match_length s) (ds_prev_length s) then
    let max_insert := wrap32 (ds_strstart s + ds_lookahead s - MIN_MATCH) in
    let '(s, bflush) := tr_tally_dist s (wrap32 (ds_strstart s - 1 - ds_prev_match s))
                                        (ds_prev_length s - MIN_MATCH) in
    let s := set_lookahead s (wrap32 (ds_lookahead s - (ds_prev_length s - 1))) in
    let s := set_prev_length s (ds_prev_length s - 2) in
    let s := deflate_slow_insert (Z.to_nat (ds_prev_length s)) s max_insert in
    let s := set_match_available s 0 in
    let s := set_match_length s (MIN_MATCH - 1) in
    let s := set_strstart s (ds_strstart s + 1) in
    if bflush then
      let '(s, r) := flush_block s 0 in
      match r with Some bs => (s, LRet bs) | None => (s, LCont) end
    else (s, LCont)
  else if negb (Z.eqb (ds_match_available s) 0) then
    let '(s, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in
    let s := if bflush then flush_block_only s 0 else s in
    let s := set_strstart s (ds_strstart s + 1) in
    let s := set_lookahead s (ds_lookahead s - 1) in
    if Z.eqb (cs_avail_out (ds_strm s)) 0 then (s, LRet need_more) else (s, LCont)
  else
    let s := set_match_available s 1 in
    let s := set_strstart s (ds_strstart s + 1) in
    let s := set_lookahead s (ds_lookahead s - 1) in
    (s, LCont)
  end.

Fixpoint deflate_slow_loop (fuel : nat) (s : deflate_state) (flush : Z)
  : deflate_state * option block_state :=
  match fuel with
  | O => (s, None)
  | S f =>
      let '(s, o) := deflate_slow_body s flush in
      match o with
      | LCont => deflate_slow_loop f s flush
      | LBreak => (s, None)
      | LRet bs => (s, Some bs)
      end
  end.

Definition deflate_slow (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  let '(s, r) := deflate_slow_loop (lz_fuel s) s flush in
  match r with
  | Some bs => (s, bs)
  | None =>
      let s :=
        if negb (Z.eqb (ds_match_available s) 0) then
          let '(s, _) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in
          set_match_available s 0
        else s in
      let s := set_insert s (if Z.ltb (ds_strstart s) (MIN_MATCH - 1) then ds_strstart s else MIN_MATCH - 1) in
      deflate_tail s flush
  end.


Fixpoint rle_cmpk (k : nat) (w : arr) (prev scan : Z) : Z * bool :=
  match k with
  | O => (scan, true)
  | S k' =>
      let scan := scan + 1 in
      if Z.eqb prev (arr_get w scan) then rle_cmpk k' w prev scan else (scan, false)
  end.

Fixpoint rle_cmp_loop (fuel : nat) (w : arr) (prev scan strend : Z) : Z :=
  match fuel with
  | O => scan
  | S f =>
      let '(scan, ok) := rle_cmpk 8%nat w prev scan in
      if ok && Z.ltb scan strend then rle_cmp_loop f w prev scan strend else scan
  end.

Definition deflate_rle_body (s : deflate_state) (flush : Z) : deflate_state * loop_out :=
  let '(s, early) :=
    if Z.leb (ds_lookahead s) MAX_MATCH then
      let s := fill_window s in
      if Z.leb (ds_lookahead s) MAX_MATCH && Z.eqb flush Z_NO_FLUSH then (s, Some (LRet need_more))
      else if Z.eqb (ds_lookahead s) 0 then (s, Some LBreak)
      else (s, None)
    else (s, None) in
  match early with
  | Some o => (s, o)
  | None =>
  let s := set_match_length s 0 in
  let s :=
    if Z.leb MIN_MATCH (ds_lookahead s) && Z.ltb 0 (ds_strstart s) then
      let w := ds_window s in
      let scan := ds_strstart s - 1 in
      let prev := arr_get w scan in
      let '(scan, ok) := rle_cmpk 3%nat w prev scan in
      if ok then
        let strend := ds_strstart s + MAX_MATCH in
        let scan := rle_cmp_loop 33%nat w prev scan strend in
        let s := set_match_length s (MAX_MATCH - (strend - scan)) in
        if Z.ltb (ds_lookahead s) (ds_match_length s) then set_match_length s (ds_lookahead s) else s
      else s
    else s in
  let '(s, bflush) :=
    if Z.leb MIN_MATCH (ds_match_length s) then
      let '(s, bflush) := tr_tally_dist s 1 (ds_match_length s - MIN_MATCH) in
      let s := set_lookahead s (ds_lookahead s - ds_match_length s) in
      let s := set_strstart s (ds_strstart s + ds_match_length s) in
      let s := set_match_length s 0 in
      (s, bflush)
    else
      let '(s, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s)) in
      let s := set_lookahead s (ds_lookahead s - 1) in
      let s := set_strstart s (ds_strstart s + 1) in
      (s, bflush) in
  if bflush then
    let '(s, r) := flush_block s 0 in
    match r with Some bs => (s, LRet bs) | None => (s, LCont) end
  else (s, LCont)
  end.

Fixpoint deflate_rle_loop (fuel : nat) (s : deflate_state) (flush : Z)
  : deflate_state * option block_state :=
  match fuel with
  | O => (s, None)
  | S f =>
      let '(s, o) := deflate_rle_body s flush in
      match o with
      | LCont => deflate_rle_loop f s flush
      | LBreak => (s, None)
      | LRet bs => (s, Some bs)
      end
  end.

Definition deflate_rle (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  let '(s, r) := deflate_rle_loop (lz_fuel s) s flush in
  match r with
  | Some bs => (s, bs)
  | None => let s := set_insert s 0 in deflate_tail s flush
  end.


Definition deflate_huff_body (s : deflate_state) (flush : Z) : deflate_state * loop_out :=
  let '(s, early) :=
    if Z.eqb (ds_lookahead s) 0 then
      let s := fill_window s in
      if Z.eqb (ds_lookahead s) 0 then
        if Z.eqb flush Z_NO_FLUSH then (s, Some (LRet need_more)) else (s, Some LBreak)
      else (s, None)
    else (s, None) in
  match early with
  | Some o => (s, o)
  | None =>
  let s := set_match_length s 0 in
  let '(s, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s)) in
  let s := set_lookahead s (ds_lookahead s - 1) in
  let s := set_strstart s (ds_strstart s + 1) in
  if bflush then
    let '(s, r) := flush_block s 0 in
    match r with Some bs => (s, LRet bs) | None => (s, LCont) end
  else (s, LCont)
  end.

Fixpoint deflate_huff_loop (fuel : nat) (s : deflate_state) (flush : Z)
  : deflate_state * option block_state :=
  match fuel with
  | O => (s, None)
  | S f =>
      let '(s, o) := deflate_huff_body s flush in
      match o with
      | LCont => deflate_huff_loop f s flush
      | LBreak => (s, None)
      | LRet bs => (s, Some bs)
      end
  end.

Definition deflate_huff (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  let '(s, r) := deflate_huff_loop (lz_fuel s) s flush in
  match r with
  | Some bs => (s, bs)
  | None => let s := set_insert s 0 in deflate_tail s flush
  end.
