(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface DeflateState Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition adler32_upd (adler : Z) (buf : list Z) : Z := adler32_model adler buf.
Definition adler32_init : Z := 1.
Definition crc32_upd (crc : Z) (buf : list Z) : Z := crc32_model (wrap32 crc) buf.
Definition crc32_init : Z := 0.


Inductive block_state : Set := need_more | block_done | finish_started | finish_done.

Definition block_state_eqb (a b : block_state) : bool :=
  match a, b with
  | need_more, need_more | block_done, block_done
  | finish_started, finish_started | finish_done, finish_done => true
  | _, _ => false
  end.


Definition update_hash (s : deflate_state) (h c : Z) : Z :=
  Z.land (Z.lxor (wrap32 (Z.shiftl h (ds_hash_shift s))) c) (ds_hash_mask s).

Definition insert_string (s : deflate_state) (str : Z) : deflate_state * Z :=
  let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) in
  let s := set_ins_h s h in
  let mh := arr_get (ds_head s) h in
  let s := set_prev s (arr_set (ds_prev s) (Z.land str (ds_w_mask s)) mh) in
  let s := set_head s (arr_set (ds_head s) h (wrap16 str)) in
  (s, mh).

Definition clear_hash (s : deflate_state) : deflate_state :=
  let s := set_head s (arr_set (ds_head s) (ds_hash_size s - 1) NIL) in
  set_head s (arr_fill (ds_head s) 0 (ds_hash_size s - 1) 0).

Fixpoint slide_hash_loop (fuel : nat) (a : arr) (n wsize : Z) : arr :=
  match fuel with
  | O => a
  | S f =>
      let p := n - 1 in
      let m := arr_get a p in
      let a := arr_set a p (wrap16 (if Z.leb wsize m then m - wsize else NIL)) in
      let n := n - 1 in
      if negb (Z.eqb n 0) then slide_hash_loop f a n wsize else a
  end.

Definition slide_hash (s : deflate_state) : deflate_state :=
  let wsize := ds_w_size s in
  let s := set_head s (slide_hash_loop (Z.to_nat (ds_hash_size s)) (ds_head s) (ds_hash_size s) wsize) in
  set_prev s (slide_hash_loop (Z.to_nat wsize) (ds_prev s) wsize wsize).


Inductive rb_dst : Set := RB_window (off : Z) | RB_next_out.

Definition read_buf (s : deflate_state) (dst : rb_dst) (size : Z) : deflate_state * Z :=
  let st := ds_strm s in
  let len := cs_avail_in st in
  let len := if Z.ltb size len then size else len in
  if Z.eqb len 0 then (s, 0)
  else
    let st := cset_avail_in st (cs_avail_in st - len) in
    let bytes := arr_slice (cs_input st) (cs_next_in st) len in
    let '(s, st) :=
      match dst with
      | RB_window off => (set_window s (arr_upd (ds_window s) off bytes), st)
      | RB_next_out => (s, cs_emit st bytes)
      end in
    let st :=
      if Z.eqb (ds_wrap s) 1 then cset_adler st (adler32_upd (cs_adler st) bytes)
      else if Z.eqb (ds_wrap s) 2 then cset_adler st (crc32_upd (cs_adler st) bytes)
      else st in
    let st := cset_next_in st (cs_next_in st + len) in
    let st := cset_total_in st (wrap64 (cs_total_in st + len)) in
    (set_strm s st, len).


Fixpoint fill_window_insert (fuel : nat) (s : deflate_state) (str : Z) : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      if negb (Z.eqb (ds_insert s) 0) then
        let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) in
        let s := set_ins_h s h in
        let s := set_prev s (arr_set (ds_prev s) (Z.land str (ds_w_mask s)) (arr_get (ds_head s) h)) in
        let s := set_head s (arr_set (ds_head s) h (wrap16 str)) in
        let str := str + 1 in
        let s := set_insert s (ds_insert s - 1) in
        if Z.ltb (ds_lookahead s + ds_insert s) MIN_MATCH then s
        else fill_window_insert f s str
      else s
  end.

Definition fill_window_body (s : deflate_state) (wsize : Z) : deflate_state * bool :=
  let more := wrap32 (ds_window_size s - ds_lookahead s - ds_strstart s) in
  let '(s, more) :=
    if Z.leb (wsize + (ds_w_size s - MIN_LOOKAHEAD)) (ds_strstart s) then
      let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) wsize (wrap32 (wsize - more))) in
      let s := set_match_start s (wrap32 (ds_match_start s - wsize)) in
      let s := set_strstart s (ds_strstart s - wsize) in
      let s := set_block_start s (ds_block_start s - wsize) in
      let s := if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s in
      let s := slide_hash s in
      (s, wrap32 (more + wsize))
    else (s, more) in
  if Z.eqb (cs_avail_in (ds_strm s)) 0 then (s, true)
  else
    let '(s, n) := read_buf s (RB_window (ds_strstart s + ds_lookahead s)) more in
    let s := set_lookahead s (ds_lookahead s + n) in
    let s :=
      if Z.leb MIN_MATCH (ds_lookahead s + ds_insert s) then
        let str := ds_strstart s - ds_insert s in
        let s := set_ins_h s (arr_get (ds_window s) str) in
        let s := set_ins_h s (update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + 1))) in
        fill_window_insert (Z.to_nat (ds_insert s)) s str
      else s in
    (s, false).

Fixpoint fill_window_loop (fuel : nat) (s : deflate_state) (wsize : Z) : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      let '(s, brk) := fill_window_body s wsize in
      if brk then s
      else if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD && negb (Z.eqb (cs_avail_in (ds_strm s)) 0)
           then fill_window_loop f s wsize
           else s
  end.

Definition fill_window_high (s : deflate_state) : deflate_state :=
  if Z.ltb (ds_high_water s) (ds_window_size s) then
    let curr := ds_strstart s + ds_lookahead s in
    if Z.ltb (ds_high_water s) curr then
      let init := ds_window_size s - curr in
      let init := if Z.ltb WIN_INIT init then WIN_INIT else init in
      let s := set_window s (arr_fill (ds_window s) curr (wrap32 init) 0) in
      set_high_water s (curr + init)
    else if Z.ltb (ds_high_water s) (curr + WIN_INIT) then
      let init := curr + WIN_INIT - ds_high_water s in
      let init := if Z.ltb (ds_window_size s - ds_high_water s) init
                  then ds_window_size s - ds_high_water s else init in
      let s := set_window s (arr_fill (ds_window s) (ds_high_water s) (wrap32 init) 0) in
      set_high_water s (ds_high_water s + init)
    else s
  else s.

Definition fill_window (s : deflate_state) : deflate_state :=
  let wsize := ds_w_size s in
  let s := fill_window_loop 263%nat s wsize in
  fill_window_high s.


Definition configuration_table (level : Z) : Z * Z * Z * Z :=
  match level with
  | 0 => (0, 0, 0, 0)
  | 1 => (4, 4, 8, 4)
  | 2 => (4, 5, 16, 8)
  | 3 => (4, 6, 32, 32)
  | 4 => (4, 4, 16, 16)
  | 5 => (8, 16, 32, 32)
  | 6 => (8, 16, 128, 128)
  | 7 => (8, 32, 128, 256)
  | 8 => (32, 128, 258, 1024)
  | _ => (32, 258, 258, 4096)
  end.

Definition lm_init (s : deflate_state) : deflate_state :=
  let s := set_window_size s (2 * ds_w_size s) in
  let s := clear_hash s in
  let '(good, lazy, nice, chain) := configuration_table (ds_level s) in
  let s := set_max_lazy_match s lazy in
  let s := set_good_match s good in
  let s := set_nice_match s nice in
  let s := set_max_chain_length s chain in
  let s := set_strstart s 0 in
  let s := set_block_start s 0 in
  let s := set_lookahead s 0 in
  let s := set_insert s 0 in
  let s := set_prev_length s (MIN_MATCH - 1) in
  let s := set_match_length s (MIN_MATCH - 1) in
  let s := set_match_available s 0 in
  set_ins_h s 0.


Fixpoint lm_cmpk (k : nat) (w : arr) (scan mtch : Z) : Z * Z * bool :=
  match k with
  | O => (scan, mtch, true)
  | S k' =>
      let scan := scan + 1 in
      let mtch := mtch + 1 in
      if Z.eqb (arr_get w scan) (arr_get w mtch) then lm_cmpk k' w scan mtch
      else (scan, mtch, false)
  end.

Fixpoint lm_cmp_loop (fuel : nat) (w : arr) (scan mtch strend : Z) : Z :=
  match fuel with
  | O => scan
  | S f =>
      let '(scan, mtch, ok) := lm_cmpk 8%nat w scan mtch in
      if ok && Z.ltb scan strend then lm_cmp_loop f w scan mtch strend else scan
  end.

Definition longest_match_body (s : deflate_state)
  (cur_match chain_length best_len nice_match limit scan_end1 scan_end : Z)
  : deflate_state * Z * Z * Z * Z * Z * bool :=
  let w := ds_window s in
  let scan := ds_strstart s in
  let mtch := cur_match in
  let '(s, best_len, scan_end1, scan_end, brk) :=
    if negb (Z.eqb (arr_get w (mtch + best_len)) scan_end)
       || negb (Z.eqb (arr_get w (mtch + best_len - 1)) scan_end1)
       || negb (Z.eqb (arr_get w mtch) (arr_get w scan))
       || negb (Z.eqb (arr_get w (mtch + 1)) (arr_get w (scan + 1)))
    then (s, best_len, scan_end1, scan_end, false)
    else
      let strend := scan + MAX_MATCH in
      let scan' := lm_cmp_loop 33%nat w (scan + 2) (mtch + 2) strend in
      let len := MAX_MATCH - (strend - scan') in
      if Z.ltb best_len len then
        let s := set_match_start s cur_match in
        let best_len := len in
        if Z.leb nice_match len then (s, best_len, scan_end1, scan_end, true)
        else (s, best_len, arr_get w (scan + best_len - 1), arr_get w (scan + best_len), false)
      else (s, best_len, scan_end1, scan_end, false) in
  if brk then (s, best_len, scan_end1, scan_end, cur_match, chain_length, false)
  else
    let cur_match := arr_get (ds_prev s) (Z.land cur_match (ds_w_mask s)) in
    if Z.ltb limit cur_match then
      let chain_length := wrap32 (chain_length - 1) in
      if negb (Z.eqb chain_length 0)
      then (s, best_len, scan_end1, scan_end, cur_match, chain_length, true)
      else (s, best_len, scan_end1, scan_end, cur_match, chain_length, false)
    else (s, best_len, scan_end1, scan_end, cur_match, chain_length, false).

Fixpoint longest_match_loop (fuel : nat) (s : deflate_state)
  (cur_match chain_length best_len nice_match limit scan_end1 scan_end : Z)
  : deflate_state * Z :=
  match fuel with
  | O => (s, best_len)
  | S f =>
      let '(s, best_len, scan_end1, scan_end, cur_match, chain_length, cont) :=
        longest_match_body s cur_match chain_length best_len nice_match limit scan_end1 scan_end in
      if cont then longest_match_loop f s cur_match chain_length best_len nice_match limit scan_end1 scan_end
      else (s, best_len)
  end.

Definition longest_match (s : deflate_state) (cur_match : Z) : deflate_state * Z :=
  let chain_length := ds_max_chain_length s in
  let scan := ds_strstart s in
  let best_len := ds_prev_length s in
  let nice_match := ds_nice_match s in
  let max_dist := ds_w_size s - MIN_LOOKAHEAD in
  let limit := if Z.ltb max_dist (ds_strstart s) then ds_strstart s - max_dist else NIL in
  let w := ds_window s in
  let scan_end1 := arr_get w (scan + best_len - 1) in
  let scan_end := arr_get w (scan + best_len) in
  let chain_length := if Z.leb (ds_good_match s) (ds_prev_length s)
                      then Z.shiftr chain_length 2 else chain_length in
  let nice_match := if Z.ltb (ds_lookahead s) nice_match
                    then ds_lookahead s else nice_match in
  let '(s, best_len) :=
    longest_match_loop (Z.to_nat chain_length) s cur_match chain_length best_len
                       nice_match limit scan_end1 scan_end in
  if Z.leb best_len (ds_lookahead s) then (s, best_len) else (s, ds_lookahead s).


Definition putShortMSB (s : deflate_state) (b : Z) : deflate_state :=
  let s := put_byte s (Z.shiftr b 8) in
  put_byte s (Z.land b 255).

Definition flush_pending (s : deflate_state) : deflate_state :=
  let s := tr_flush_bits s in
  let len := wrap32 (ds_pending s) in
  let st := ds_strm s in
  let len := if Z.ltb (cs_avail_out st) len then cs_avail_out st else len in
  if Z.eqb len 0 then s
  else
    let st := cs_emit st (arr_slice (ds_pending_buf s) (ds_pending_out s) len) in
    let s := set_pending_out s (ds_pending_out s + len) in
    let st := cset_total_out st (wrap64 (cs_total_out st + len)) in
    let st := cset_avail_out st (cs_avail_out st - len) in
    let s := set_strm s st in
    let s := set_pending s (ds_pending s - len) in
    if Z.eqb (ds_pending s) 0 then set_pending_out s 0 else s.

Definition flush_block_only (s : deflate_state) (last : Z) : deflate_state :=
  let buf := if Z.leb 0 (ds_block_start s) then Some (wrap32 (ds_block_start s)) else None in
  let stored_len := wrap64 (ds_strstart s - ds_block_start s) in
  let s := tr_flush_block s buf stored_len last in
  let s := set_block_start s (ds_strstart s) in
  flush_pending s.
