(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.

Module Trees.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition heap_get (s : deflate_state) (i : Z) : Z := arr_get (ds_heap s) i.
Definition heap_set (s : deflate_state) (i v : Z) : deflate_state :=
  set_heap s (arr_set (ds_heap s) i v).
Definition depth_get (s : deflate_state) (i : Z) : Z := arr_get (ds_depth s) i.
Definition depth_set (s : deflate_state) (i v : Z) : deflate_state :=
  set_depth s (arr_set (ds_depth s) i (wrap8 v)).
Definition bl_count_get (s : deflate_state) (i : Z) : Z := arr_get (ds_bl_count s) i.
Definition bl_count_set (s : deflate_state) (i v : Z) : deflate_state :=
  set_bl_count s (arr_set (ds_bl_count s) i (wrap16 v)).


Definition put_short (s : deflate_state) (w : Z) : deflate_state :=
  let s := put_byte s (Z.land w 255) in
  put_byte s (Z.shiftr (wrap16 w) 8).

Fixpoint bi_reverse_loop (fuel : nat) (code res len : Z) : Z :=
  match fuel with
  | O => Z.shiftr res 1
  | S f =>
      let res := Z.lor res (Z.land code 1) in
      let code := Z.shiftr code 1 in
      let res := wrap32 (Z.shiftl res 1) in
      let len := len - 1 in
      if Z.ltb 0 len then bi_reverse_loop f code res len else Z.shiftr res 1
  end.
Definition bi_reverse (code len : Z) : Z :=
  bi_reverse_loop (Z.to_nat (Z.max len 1)) code 0 len.

Definition bi_flush (s : deflate_state) : deflate_state :=
  if Z.eqb (ds_bi_valid s) 16 then
    let s := put_short s (ds_bi_buf s) in
    let s := set_bi_buf s 0 in
    set_bi_valid s 0
  else if Z.leb 8 (ds_bi_valid s) then
    let s := put_byte s (ds_bi_buf s) in
    let s := set_bi_buf s (Z.shiftr (ds_bi_buf s) 8) in
    set_bi_valid s (ds_bi_valid s - 8)
  else s.

Definition bi_windup (s : deflate_state) : deflate_state :=
  let s :=
    if Z.ltb 8 (ds_bi_valid s) then put_short s (ds_bi_buf s)
    else if Z.ltb 0 (ds_bi_valid s) then put_byte s (ds_bi_buf s)
    else s in
  let s := set_bi_buf s 0 in
  set_bi_valid s 0.

Definition send_bits (s : deflate_state) (value length : Z) : deflate_state :=
  let len := length in
  if Z.ltb (Buf_size - len) (ds_bi_valid s) then
    let val := value in
    let s := set_bi_buf s (wrap16 (Z.lor (ds_bi_buf s) (Z.shiftl (wrap16 val) (ds_bi_valid s)))) in
    let s := put_short s (ds_bi_buf s) in
    let s := set_bi_buf s (Z.shiftr (wrap16 val) (Buf_size - ds_bi_valid s)) in
    set_bi_valid s (ds_bi_valid s + len - Buf_size)
  else
    let s := set_bi_buf s (wrap16 (Z.lor (ds_bi_buf s) (Z.shiftl (wrap16 value) (ds_bi_valid s)))) in
    set_bi_valid s (ds_bi_valid s + len).

Definition send_code (s : deflate_state) (c : Z) (tfc tdl : arr) : deflate_state :=
  send_bits s (arr_get tfc c) (arr_get tdl c).

Definition send_dcode (s : deflate_state) (c : Z) (t : tree_id) : deflate_state :=
  send_bits s (Code s t c) (Len s t c).


Definition init_block (s : deflate_state) : deflate_state :=
  let s := set_dyn_ltree_fc s (arr_fill (ds_dyn_ltree_fc s) 0 L_CODES 0) in
  let s := set_dyn_dtree_fc s (arr_fill (ds_dyn_dtree_fc s) 0 D_CODES 0) in
  let s := set_bl_tree_fc s (arr_fill (ds_bl_tree_fc s) 0 BL_CODES 0) in
  let s := set_Freq s TL END_BLOCK 1 in
  let s := set_opt_len s 0 in
  let s := set_static_len s 0 in
  let s := set_sym_next s 0 in
  set_matches s 0.

Definition tr_init (s : deflate_state) : deflate_state :=
  let s := set_bi_buf s 0 in
  let s := set_bi_valid s 0 in
  init_block s.


Definition smaller (s : deflate_state) (t : tree_id) (n m : Z) : bool :=
  Z.ltb (Freq s t n) (Freq s t m)
  || (Z.eqb (Freq s t n) (Freq s t m) && Z.leb (depth_get s n) (depth_get s m)).

Fixpoint pqdownheap_loop (fuel : nat) (s : deflate_state) (t : tree_id) (v k j : Z)
  : deflate_state * Z :=
  match fuel with
  | O => (s, k)
  | S f =>
      if Z.leb j (ds_heap_len s) then
        let j := if Z.ltb j (ds_heap_len s) && smaller s t (heap_get s (j + 1)) (heap_get s j)
                 then j + 1 else j in
        if smaller s t v (heap_get s j) then (s, k)
        else
          let s := heap_set s k (heap_get s j) in
          let k := j in
          pqdownheap_loop f s t v k (Z.shiftl j 1)
      else (s, k)
  end.

Definition pqdownheap (s : deflate_state) (t : tree_id) (k : Z) : deflate_state :=
  let v := heap_get s k in
  let j := Z.shiftl k 1 in
  let '(s, k) := pqdownheap_loop 32%nat s t v k j in
  heap_set s k v.


Fixpoint gen_bitlen_loop1 (fuel : nat) (s : deflate_state) (t : tree_id)
         (max_code base max_length h overflow : Z) : deflate_state * Z :=
  match fuel with
  | O => (s, overflow)
  | S f =>
      if Z.ltb h HEAP_SIZE then
        let n := heap_get s h in
        let bits := Len s t (Dad s t n) + 1 in
        let '(bits, overflow) :=
          if Z.ltb max_length bits then (max_length, overflow + 1) else (bits, overflow) in
        let s := set_Len s t n bits in
        if Z.ltb max_code n then gen_bitlen_loop1 f s t max_code base max_length (h + 1) overflow
        else
          let s := bl_count_set s bits (bl_count_get s bits + 1) in
          let xbits := if Z.leb base n then arr_get (sd_extra_bits t) (n - base) else 0 in
          let fq := Freq s t n in
          let s := set_opt_len s (wrap64 (ds_opt_len s + fq * (bits + xbits))) in
          let s := if stree_has t
                   then set_static_len s (wrap64 (ds_static_len s + fq * (stree_Len t n + xbits)))
                   else s in
          gen_bitlen_loop1 f s t max_code base max_length (h + 1) overflow
      else (s, overflow)
  end.

Fixpoint gen_bitlen_find (fuel : nat) (s : deflate_state) (bits : Z) : Z :=
  match fuel with
  | O => bits
  | S f => if Z.eqb (bl_count_get s bits) 0 then gen_bitlen_find f s (bits - 1) else bits
  end.

Fixpoint gen_bitlen_loop2 (fuel : nat) (s : deflate_state) (max_length overflow : Z)
  : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      let bits := gen_bitlen_find (Z.to_nat max_length) s (max_length - 1) in
      let s := bl_count_set s bits (bl_count_get s bits - 1) in
      let s := bl_count_set s (bits + 1) (bl_count_get s (bits + 1) + 2) in
      let s := bl_count_set s max_length (bl_count_get s max_length - 1) in
      let overflow := overflow - 2 in
      if Z.ltb 0 overflow then gen_bitlen_loop2 f s max_length overflow else s
  end.

Fixpoint gen_bitlen_loop3i (fuel : nat) (s : deflate_state) (t : tree_id)
         (max_code bits n h : Z) : deflate_state * Z :=
  match fuel with
  | O => (s, h)
  | S f =>
      if negb (Z.eqb n 0) then
        let h := h - 1 in
        let m := heap_get s h in
        if Z.ltb max_code m then gen_bitlen_loop3i f s t max_code bits n h
        else
          let s :=
            if negb (Z.eqb (Len s t m) bits) then
              let s := set_opt_len s (wrap64 (ds_opt_len s + (bits - Len s t m) * Freq s t m)) in
              set_Len s t m bits
            else s in
          gen_bitlen_loop3i f s t max_code bits (n - 1) h
      else (s, h)
  end.

Fixpoint gen_bitlen_loop3 (fuel : nat) (s : deflate_state) (t : tree_id)
         (max_code bits h : Z) : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      if negb (Z.eqb bits 0) then
        let n := bl_count_get s bits in
        let '(s, h) := gen_bitlen_loop3i 574%nat s t max_code bits n h in
        gen_bitlen_loop3 f s t max_code (bits - 1) h
      else s
  end.

Definition gen_bitlen (s : deflate_state) (t : tree_id) : deflate_state :=
  let max_code := max_code s t in
  let base := sd_extra_base t in
  let max_length := sd_max_length t in
  let s := set_bl_count s (arr_fill (ds_bl_count s) 0 (MAX_BITS + 1) 0) in
  let s := set_Len s t (heap_get s (ds_heap_max s)) 0 in
  let '(s, overflow) := gen_bitlen_loop1 573%nat s t max_code base max_length (ds_heap_max s + 1) 0 in
  if Z.eqb overflow 0 then s
  else
    let s := gen_bitlen_loop2 573%nat s max_length overflow in
    gen_bitlen_loop3 (Z.to_nat max_length) s t max_code max_length HEAP_SIZE.


Fixpoint gen_codes_loop1 (fuel : nat) (blc : arr) (next_code : arr) (code bits : Z) : arr :=
  match fuel with
  | O => next_code
  | S f =>
      if Z.leb bits MAX_BITS then
        let code := wrap32 (Z.shiftl (code + arr_get blc (bits - 1)) 1) in
        let next_code := arr_set next_code bits (wrap16 code) in
        gen_codes_loop1 f blc next_code code (bits + 1)
      else next_code
  end.

Fixpoint gen_codes_loop2 (fuel : nat) (s : deflate_state) (t : tree_id)
         (next_code : arr) (max_code n : Z) : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      if Z.leb n max_code then
        let len := Len s t n in
        if Z.eqb len 0 then gen_codes_loop2 f s t next_code max_code (n + 1)
        else
          let nc := arr_get next_code len in
          let next_code := arr_set next_code len (wrap16 (nc + 1)) in
          let s := set_Code s t n (bi_reverse nc len) in
          gen_codes_loop2 f s t next_code max_code (n + 1)
      else s
  end.

Definition gen_codes (s : deflate_state) (t : tree_id) (max_code : Z) : deflate_state :=
  let next_code := gen_codes_loop1 16%nat (ds_bl_count s) (arr_make (MAX_BITS + 1) 0) 0 1 in
  gen_codes_loop2 (Z.to_nat (max_code + 1)) s t next_code max_code 0.


Fixpoint build_tree_loop1 (fuel : nat) (s : deflate_state) (t : tree_id)
         (elems n max_code : Z) : deflate_state * Z :=
  match fuel with
  | O => (s, max_code)
  | S f =>
      if Z.ltb n elems then
        if negb (Z.eqb (Freq s t n) 0) then
          let s := set_heap_len s (ds_heap_len s + 1) in
          let s := heap_set s (ds_heap_len s) n in
          let s := depth_set s n 0 in
          build_tree_loop1 f s t elems (n + 1) n
        else
          let s := set_Len s t n 0 in
          build_tree_loop1 f s t elems (n + 1) max_code
      else (s, max_code)
  end.

Fixpoint build_tree_loop2 (fuel : nat) (s : deflate_state) (t : tree_id) (max_code : Z)
  : deflate_state * Z :=
  match fuel with
  | O => (s, max_code)
  | S f =>
      if Z.ltb (ds_heap_len s) 2 then
        let '(node, max_code) :=
          if Z.ltb max_code 2 then (max_code + 1, max_code + 1) else (0, max_code) in
        let s := set_heap_len s (ds_heap_len s + 1) in
        let s := heap_set s (ds_heap_len s) node in
        let s := set_Freq s t node 1 in
        let s := depth_set s node 0 in
        let s := set_opt_len s (wrap64 (ds_opt_len s - 1)) in
        let s := if stree_has t then set_static_len s (wrap64 (ds_static_len s - stree_Len t node)) else s in
        build_tree_loop2 f s t max_code
      else (s, max_code)
  end.

Fixpoint build_tree_loop3 (fuel : nat) (s : deflate_state) (t : tree_id) (n : Z) : deflate_state :=
  match fuel with
  | O => s
  | S f => if Z.leb 1 n then build_tree_loop3 f (pqdownheap s t n) t (n - 1) else s
  end.

Fixpoint build_tree_loop4 (fuel : nat) (s : deflate_state) (t : tree_id) (node : Z)
  : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      let n := heap_get s SMALLEST in
      let s := heap_set s SMALLEST (heap_get s (ds_heap_len s)) in
      let s := set_heap_len s (ds_heap_len s - 1) in
      let s := pqdownheap s t SMALLEST in
      let m := heap_get s SMALLEST in
      let s := set_heap_max s (ds_heap_max s - 1) in
      let s := heap_set s (ds_heap_max s) n in
      let s := set_heap_max s (ds_heap_max s - 1) in
      let s := heap_set s (ds_heap_max s) m in
      let s := set_Freq s t node (Freq s t n + Freq s t m) in
      let dn := depth_get s n in let dm := depth_get s m in
      let s := depth_set s node ((if Z.leb dm dn then dn else dm) + 1) in
      let s := set_Dad s t m node in
      let s := set_Dad s t n node in
      let s := heap_set s SMALLEST node in
      let node := node + 1 in
      let s := pqdownheap s t SMALLEST in
      if Z.leb 2 (ds_heap_len s) then build_tree_loop4 f s t node else s
  end.

Definition build_tree (s : deflate_state) (t : tree_id) : deflate_state :=
  let elems := sd_elems t in
  let s := set_heap_len s 0 in
  let s := set_heap_max s HEAP_SIZE in
  let '(s, max_code) := build_tree_loop1 (Z.to_nat elems) s t elems 0 (-1) in
  let '(s, max_code) := build_tree_loop2 2%nat s t max_code in
  let s := set_max_code s t max_code in
  let s := build_tree_loop3 (Z.to_nat (ds_heap_len s / 2)) s t (ds_heap_len s / 2) in
  let s := build_tree_loop4 573%nat s t elems in
  let s := set_heap_max s (ds_heap_max s - 1) in
  let s := heap_set s (ds_heap_max s) (heap_get s SMALLEST) in
  let s := gen_bitlen s t in
  gen_codes s t max_code.


Definition tree_counts (curlen nextlen : Z) : Z * Z :=
  if Z.eqb nextlen 0 then (138, 3)
  else if Z.eqb curlen nextlen then (6, 3)
  else (7, 4).

Fixpoint scan_tree_loop (fuel : nat) (s : deflate_state) (t : tree_id) (max_code n : Z)
         (prevlen nextlen count max_count min_count : Z) : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      if Z.leb n max_code then
        let curlen := nextlen in
        let nextlen := Len s t (n + 1) in
        let count := count + 1 in
        if Z.ltb count max_count && Z.eqb curlen nextlen then
          scan_tree_loop f s t max_code (n + 1) prevlen nextlen count max_count min_count
        else
          let s :=
            if Z.ltb count min_count then
              set_Freq s TB curlen (Freq s TB curlen + count)
            else if negb (Z.eqb curlen 0) then
              let s := if negb (Z.eqb curlen prevlen)
                       then set_Freq s TB curlen (Freq s TB curlen + 1) else s in
              set_Freq s TB REP_3_6 (Freq s TB REP_3_6 + 1)
            else if Z.leb count 10 then
              set_Freq s TB REPZ_3_10 (Freq s TB REPZ_3_10 + 1)
            else
              set_Freq s TB REPZ_11_138 (Freq s TB REPZ_11_138 + 1) in
          let '(max_count, min_count) := tree_counts curlen nextlen in
          scan_tree_loop f s t max_code (n + 1) curlen nextlen 0 max_count min_count
      else s
  end.

Definition scan_tree (s : deflate_state) (t : tree_id) (max_code : Z) : deflate_state :=
  let nextlen := Len s t 0 in
  let '(max_count, min_count) := if Z.eqb nextlen 0 then (138, 3) else (7, 4) in
  let s := set_Len s t (max_code + 1) 65535 in
  scan_tree_loop (Z.to_nat (max_code + 1)) s t max_code 0 (-1) nextlen 0 max_count min_count.

Fixpoint send_tree_rep (fuel : nat) (s : deflate_state) (curlen count : Z) : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      let s := send_dcode s curlen TB in
      let count := count - 1 in
      if negb (Z.eqb count 0) then send_tree_rep f s curlen count else s
  end.

Fixpoint send_tree_loop (fuel : nat) (s : deflate_state) (t : tree_id) (max_code n : Z)
         (prevlen nextlen count max_count min_count : Z) : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      if Z.leb n max_code then
        let curlen := nextlen in
        let nextlen := Len s t (n + 1) in
        let count := count + 1 in
        if Z.ltb count max_count && Z.eqb curlen nextlen then
          send_tree_loop f s t max_code (n + 1) prevlen nextlen count max_count min_count
        else
          let s :=
            if Z.ltb count min_count then
              send_tree_rep (Z.to_nat count) s curlen count
            else if negb (Z.eqb curlen 0) then
              let '(s, count) :=
                if negb (Z.eqb curlen prevlen)
                then (send_dcode s curlen TB, count - 1) else (s, count) in
              let s := send_dcode s REP_3_6 TB in
              send_bits s (count - 3) 2
            else if Z.leb count 10 then
              let s := send_dcode s REPZ_3_10 TB in
              send_bits s (count - 3) 3
            else
              let s := send_dcode s REPZ_11_138 TB in
              send_bits s (count - 11) 7 in
          let '(max_count, min_count) := tree_counts curlen nextlen in
          send_tree_loop f s t max_code (n + 1) curlen nextlen 0 max_count min_count
      else s
  end.

Definition send_tree (s : deflate_state) (t : tree_id) (max_code : Z) : deflate_state :=
  let nextlen := Len s t 0 in
  let '(max_count, min_count) := if Z.eqb nextlen 0 then (138, 3) else (7, 4) in
  send_tree_loop (Z.to_nat (max_code + 1)) s t max_code 0 (-1) nextlen 0 max_count min_count.


Fixpoint build_bl_tree_loop (fuel : nat) (s : deflate_state) (max_blindex : Z) : Z :=
  match fuel with
  | O => max_blindex
  | S f =>
      if Z.leb 3 max_blindex then
        if negb (Z.eqb (Len s TB (arr_get bl_order_a max_blindex)) 0) then max_blindex
        else build_bl_tree_loop f s (max_blindex - 1)
      else max_blindex
  end.

Definition build_bl_tree (s : deflate_state) : deflate_state * Z :=
  let s := scan_tree s TL (ds_l_max_code s) in
  let s := scan_tree s TD (ds_d_max_code s) in
  let s := build_tree s TB in
  let max_blindex := build_bl_tree_loop 17%nat s (BL_CODES - 1) in
  let s := set_opt_len s (wrap64 (ds_opt_len s + 3 * (max_blindex + 1) + 5 + 5 + 4)) in
  (s, max_blindex).

Fixpoint send_all_trees_loop (fuel : nat) (s : deflate_state) (blcodes rank : Z) : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      if Z.ltb rank blcodes then
        let s := send_bits s (Len s TB (arr_get bl_order_a rank)) 3 in
        send_all_trees_loop f s blcodes (rank + 1)
      else s
  end.

Definition send_all_trees (s : deflate_state) (lcodes dcodes blcodes : Z) : deflate_state :=
  let s := send_bits s (lcodes - 257) 5 in
  let s := send_bits s (dcodes - 1) 5 in
  let s := send_bits s (blcodes - 4) 4 in
  let s := send_all_trees_loop 19%nat s blcodes 0 in
  let s := send_tree s TL (lcodes - 1) in
  send_tree s TD (dcodes - 1).


Definition tr_stored_block (s : deflate_state) (buf : option Z) (stored_len last : Z)
  : deflate_state :=
  let s := send_bits s (Z.shiftl STORED_BLOCK 1 + last) 3 in
  let s := bi_windup s in
  let s := put_short s (wrap16 stored_len) in
  let s := put_short s (wrap16 (Z.lnot stored_len)) in
  let s :=
    if negb (Z.eqb stored_len 0) then
      match buf with
      | Some off => set_pending_buf s (arr_blit (ds_pending_buf s) (ds_pending s) (ds_window s) off stored_len)
      | None => s
      end
    else s in
  set_pending s (ds_pending s + stored_len).

Definition tr_flush_bits (s : deflate_state) : deflate_state := bi_flush s.

Definition tr_align (s : deflate_state) : deflate_state :=
  let s := send_bits s (Z.shiftl STATIC_TREES 1) 3 in
  let s := send_code s END_BLOCK static_ltree_fc static_ltree_dl in
  bi_flush s.


Definition compress_block_sym (s : deflate_state) (lfc ldl dfc ddl : arr) (sx : Z)
  : deflate_state * Z :=
  let dist := Z.land (sym_buf_get s sx) 255 in let sx := sx + 1 in
  let dist := dist + Z.shiftl (Z.land (sym_buf_get s sx) 255) 8 in let sx := sx + 1 in
  let lc := sym_buf_get s sx in let sx := sx + 1 in
  if Z.eqb dist 0 then (send_code s lc lfc ldl, sx)
  else
    let code := arr_get length_code_a lc in
    let s := send_code s (code + LITERALS + 1) lfc ldl in
    let extra := arr_get extra_lbits_a code in
    let s := if negb (Z.eqb extra 0)
             then let lc := lc - arr_get base_length_a code in send_bits s lc extra
             else s in
    let dist := dist - 1 in
    let code := d_code dist in
    let s := send_code s code dfc ddl in
    let extra := arr_get extra_dbits_a code in
    let s := if negb (Z.eqb extra 0)
             then let dist := wrap32 (dist - arr_get base_dist_a code) in send_bits s dist extra
             else s in
    (s, sx).

Fixpoint compress_block_loop (fuel : nat) (s : deflate_state) (lfc ldl dfc ddl : arr) (sx : Z)
  : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      let '(s, sx) := compress_block_sym s lfc ldl dfc ddl sx in
      if Z.ltb sx (ds_sym_next s) then compress_block_loop f s lfc ldl dfc ddl sx else s
  end.

Definition compress_block (s : deflate_state) (lfc ldl dfc ddl : arr) : deflate_state :=
  let s := if negb (Z.eqb (ds_sym_next s) 0)
           then compress_block_loop (Z.to_nat (ds_sym_next s)) s lfc ldl dfc ddl 0
           else s in
  send_code s END_BLOCK lfc ldl.


Fixpoint detect_loop1 (fuel : nat) (s : deflate_state) (n block_mask : Z) : option Z :=
  match fuel with
  | O => None
  | S f =>
      if Z.leb n 31 then
        if negb (Z.eqb (Z.land block_mask 1) 0) && negb (Z.eqb (Freq s TL n) 0) then Some Z_BINARY
        else detect_loop1 f s (n + 1) (Z.shiftr block_mask 1)
      else None
  end.

Fixpoint detect_loop2 (fuel : nat) (s : deflate_state) (n : Z) : option Z :=
  match fuel with
  | O => None
  | S f =>
      if Z.ltb n LITERALS then
        if negb (Z.eqb (Freq s TL n) 0) then Some Z_TEXT else detect_loop2 f s (n + 1)
      else None
  end.

Definition detect_data_type (s : deflate_state) : Z :=
  match detect_loop1 32%nat s 0 4093624447 with
  | Some r => r
  | None =>
      if negb (Z.eqb (Freq s TL 9) 0) || negb (Z.eqb (Freq s TL 10) 0) || negb (Z.eqb (Freq s TL 13) 0)
      then Z_TEXT
      else match detect_loop2 224%nat s 32 with Some r => r | None => Z_BINARY end
  end.


Definition tr_flush_block (s : deflate_state) (buf : option Z) (stored_len last : Z)
  : deflate_state :=
  let '(s, opt_lenb, static_lenb, max_blindex) :=
    if Z.ltb 0 (ds_level s) then
      let s := if Z.eqb (cs_data_type (ds_strm s)) Z_UNKNOWN
               then set_strm s (cset_data_type (ds_strm s) (detect_data_type s)) else s in
      let s := build_tree s TL in
      let s := build_tree s TD in
      let '(s, max_blindex) := build_bl_tree s in
      let opt_lenb := Z.shiftr (wrap64 (ds_opt_len s + 3 + 7)) 3 in
      let static_lenb := Z.shiftr (wrap64 (ds_static_len s + 3 + 7)) 3 in
      let opt_lenb := if Z.leb static_lenb opt_lenb || Z.eqb (ds_strategy s) Z_FIXED
                      then static_lenb else opt_lenb in
      (s, opt_lenb, static_lenb, max_blindex)
    else
      (s, wrap64 (stored_len + 5), wrap64 (stored_len + 5), 0) in
  let s :=
    if Z.leb (wrap64 (stored_len + 4)) opt_lenb && (match buf with Some _ => true | None => false end)
    then tr_stored_block s buf stored_len last
    else if Z.eqb static_lenb opt_lenb then
      let s := send_bits s (Z.shiftl STATIC_TREES 1 + last) 3 in
      compress_block s static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl
    else
      let s := send_bits s (Z.shiftl DYN_TREES 1 + last) 3 in
      let s := send_all_trees s (ds_l_max_code s + 1) (ds_d_max_code s + 1) (max_blindex + 1) in
      compress_block s (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) in
  let s := init_block s in
  if negb (Z.eqb last 0) then bi_windup s else s.


Definition tr_tally_lit (s : deflate_state) (c : Z) : deflate_state * bool :=
  let cc := wrap8 c in
  let s := sym_buf_set s (ds_sym_next s) 0 in let s := set_sym_next s (ds_sym_next s + 1) in
  let s := sym_buf_set s (ds_sym_next s) 0 in let s := set_sym_next s (ds_sym_next s + 1) in
  let s := sym_buf_set s (ds_sym_next s) cc in let s := set_sym_next s (ds_sym_next s + 1) in
  let s := set_Freq s TL cc (Freq s TL cc + 1) in
  (s, Z.eqb (ds_sym_next s) (ds_sym_end s)).

Definition tr_tally_dist (s : deflate_state) (distance length : Z) : deflate_state * bool :=
  let len := wrap8 length in
  let dist := wrap16 distance in
  let s := sym_buf_set s (ds_sym_next s) dist in let s := set_sym_next s (ds_sym_next s + 1) in
  let s := sym_buf_set s (ds_sym_next s) (Z.shiftr dist 8) in let s := set_sym_next s (ds_sym_next s + 1) in
  let s := sym_buf_set s (ds_sym_next s) len in let s := set_sym_next s (ds_sym_next s + 1) in
  let dist := wrap16 (dist - 1) in
  let s := set_Freq s TL (arr_get length_code_a len + LITERALS + 1)
                        (Freq s TL (arr_get length_code_a len + LITERALS + 1) + 1) in
  let s := set_Freq s TD (d_code dist) (Freq s TD (d_code dist) + 1) in
  (s, Z.eqb (ds_sym_next s) (ds_sym_end s)).

Definition tr_tally (s : deflate_state) (dist lc : Z) : deflate_state * bool :=
  let s := sym_buf_set s (ds_sym_next s) dist in let s := set_sym_next s (ds_sym_next s + 1) in
  let s := sym_buf_set s (ds_sym_next s) (Z.shiftr dist 8) in let s := set_sym_next s (ds_sym_next s + 1) in
  let s := sym_buf_set s (ds_sym_next s) lc in let s := set_sym_next s (ds_sym_next s + 1) in
  let s :=
    if Z.eqb dist 0 then set_Freq s TL lc (Freq s TL lc + 1)
    else
      let s := set_matches s (wrap32 (ds_matches s + 1)) in
      let dist := wrap32 (dist - 1) in
      let s := set_Freq s TL (arr_get length_code_a lc + LITERALS + 1)
                            (Freq s TL (arr_get length_code_a lc + LITERALS + 1) + 1) in
      set_Freq s TD (d_code dist) (Freq s TD (d_code dist) + 1) in
  (s, Z.eqb (ds_sym_next s) (ds_sym_end s)).
End Trees.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition adler_csub (x : Z) : Z := if 65520 <? x then x - 65521 else x.
Definition adler32_len1 (adler c : Z) : Z :=
  let a := adler_csub (adler mod 2 ^ 16 + c) in
  let b := adler_csub (a + (adler mod 2 ^ 32) / 2 ^ 16) in
  Z.lor (b * 2 ^ 16) a.
Definition adler32_upd (adler : Z) (buf : list Z) : Z :=
  match buf with
  | [c] => adler32_len1 adler c
  | _ => adler32_model adler buf
  end.
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
