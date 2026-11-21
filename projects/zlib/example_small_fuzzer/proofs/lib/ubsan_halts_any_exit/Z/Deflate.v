(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.


Definition deflateStateCheck (s : deflate_state) : bool :=
  let st := ds_status s in
  negb ((st =? INIT_STATE) || (st =? GZIP_STATE) || (st =? EXTRA_STATE) || (st =? NAME_STATE)
        || (st =? COMMENT_STATE) || (st =? HCRC_STATE) || (st =? BUSY_STATE) || (st =? FINISH_STATE)).


Definition deflateResetKeep (s : deflate_state) : deflate_state * Z :=
  if deflateStateCheck s then (s, Z_STREAM_ERROR)
  else
    let st := ds_strm s in
    let st := cset_total_in st 0 in
    let st := cset_total_out st 0 in
    let st := cset_msg st MSG_NULL in
    let st := cset_data_type st Z_UNKNOWN in
    let s := set_strm s st in
    let s := set_pending s 0 in
    let s := set_pending_out s 0 in
    let s := if Z.ltb (ds_wrap s) 0 then set_wrap s (- ds_wrap s) else s in
    let s := set_status s (if Z.eqb (ds_wrap s) 2 then GZIP_STATE else INIT_STATE) in
    let s := set_strm s (cset_adler (ds_strm s) (if Z.eqb (ds_wrap s) 2 then crc32_init else adler32_init)) in
    let s := set_last_flush s (-2) in
    let s := tr_init s in
    (s, Z_OK).

Definition deflateReset (s : deflate_state) : deflate_state * Z :=
  let '(s, ret) := deflateResetKeep s in
  if Z.eqb ret Z_OK then (lm_init s, ret) else (s, ret).


Section WithHooks.
  Context {St : Type}.
  Variable hooks : zhooks St.

  Definition try_free (b : option blk) : SM St unit :=
    match b with Some b => zfree hooks b | None => sret tt end.

  Definition deflateEnd_core (s : deflate_state) : SM St Z :=
    let status := ds_status s in
    try_free (ds_pending_buf_blk s) ;;
    try_free (ds_head_blk s) ;;
    try_free (ds_prev_blk s) ;;
    try_free (ds_window_blk s) ;;
    zfree hooks (ds_self_blk s) ;;
    sret (if Z.eqb status BUSY_STATE then Z_DATA_ERROR else Z_OK).

  Definition deflateEnd_m (s : deflate_state) (zc : ZCall) : SM St ZRet :=
    if deflateStateCheck s then sret (zret0 (zc_strm zc) Z_STREAM_ERROR)
    else do rc <- deflateEnd_core s ; sret (zret0 (zc_strm zc) rc).


  Definition blk_bytes (g : Z -> Z) (n : Z) : arr := arr_init n (fun i => init_u8 g 0 i).
  Definition blk_ush (g : Z -> Z) (n : Z) : arr := arr_init n (fun i => init_u16 g 0 i).

  Definition deflateInit2_m (zc : ZCall) (level method windowBits memLevel strategy : Z)
    : SM St (option deflate_state * ZRet) :=
    let cs := cset_msg (cstrm_of_call zc) MSG_NULL in
    let level := if Z.eqb level Z_DEFAULT_COMPRESSION then 6 else level in
    let '(wrap, windowBits, bad) :=
      if Z.ltb windowBits 0 then (0, - windowBits, Z.ltb windowBits (-15))
      else if Z.ltb 15 windowBits then (2, windowBits - 16, false)
      else (1, windowBits, false) in
    if bad then sret (None, zret_of_cs cs Z_STREAM_ERROR)
    else if (memLevel <? 1) || (MAX_MEM_LEVEL <? memLevel) || negb (method =? Z_DEFLATED)
            || (windowBits <? 8) || (15 <? windowBits) || (level <? 0) || (9 <? level)
            || (strategy <? 0) || (Z_FIXED <? strategy) || ((windowBits =? 8) && negb (wrap =? 1))
    then sret (None, zret_of_cs cs Z_STREAM_ERROR)
    else
      let windowBits := if Z.eqb windowBits 8 then 9 else windowBits in
      do r0 <- zalloc hooks 1 SIZEOF_deflate_state ;
      match r0 with
      | None => sret (None, zret_of_cs cs Z_MEM_ERROR)
      | Some (b0, g0) =>
        let s := ds_of_oracle g0 b0 cs in
        let s := set_status s INIT_STATE in
        let s := set_wrap s wrap in
        let s := set_gzhead s 0 in
        let s := set_w_bits s windowBits in
        let s := set_w_size s (Z.shiftl 1 windowBits) in
        let s := set_w_mask s (ds_w_size s - 1) in
        let s := set_hash_bits s (memLevel + 7) in
        let s := set_hash_size s (Z.shiftl 1 (ds_hash_bits s)) in
        let s := set_hash_mask s (ds_hash_size s - 1) in
        let s := set_hash_shift s ((ds_hash_bits s + MIN_MATCH - 1) / MIN_MATCH) in
        do rw <- zalloc hooks (ds_w_size s) 2 ;
        let s := match rw with
                 | Some (bw, gw) => set_window_blk (set_window s (blk_bytes gw (2 * ds_w_size s))) (Some bw)
                 | None => set_window_blk (set_window s (arr_make 0 0)) None
                 end in
        do rp <- zalloc hooks (ds_w_size s) 2 ;
        let s := match rp with
                 | Some (bp, gp) => set_prev_blk (set_prev s (blk_ush gp (ds_w_size s))) (Some bp)
                 | None => set_prev_blk (set_prev s (arr_make 0 0)) None
                 end in
        do rh <- zalloc hooks (ds_hash_size s) 2 ;
        let s := match rh with
                 | Some (bh, gh) => set_head_blk (set_head s (blk_ush gh (ds_hash_size s))) (Some bh)
                 | None => set_head_blk (set_head s (arr_make 0 0)) None
                 end in
        let s := set_high_water s 0 in
        let s := set_lit_bufsize s (Z.shiftl 1 (memLevel + 6)) in
        do rb <- zalloc hooks (ds_lit_bufsize s) LIT_BUFS ;
        let s := match rb with
                 | Some (bb, gb) => set_pending_buf_blk (set_pending_buf s (blk_bytes gb (ds_lit_bufsize s * 4))) (Some bb)
                 | None => set_pending_buf_blk (set_pending_buf s (arr_make 0 0)) None
                 end in
        let s := set_pending_buf_size s (ds_lit_bufsize s * 4) in
        match ds_window_blk s, ds_prev_blk s, ds_head_blk s, ds_pending_buf_blk s with
        | Some _, Some _, Some _, Some _ =>
            let s := set_sym_end s ((ds_lit_bufsize s - 1) * 3) in
            let s := set_level s level in
            let s := set_strategy s strategy in
            let s := set_method s (wrap8 method) in
            let '(s, rc) := deflateReset s in
            sret (Some s, zret_of_cs (ds_strm s) rc)
        | _, _, _, _ =>
            let s := set_status s FINISH_STATE in
            let s := set_strm s (cset_msg (ds_strm s) (MSG_ERR Z_MEM_ERROR)) in
            do _ <- deflateEnd_core s ;
            sret (None, zret_of_cs (ds_strm s) Z_MEM_ERROR)
        end
      end.
End WithHooks.


Fixpoint setdict_inner (fuel : nat) (s : deflate_state) (str n : Z) : deflate_state * Z :=
  match fuel with
  | O => (s, str)
  | S f =>
      let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) in
      let s := set_ins_h s h in
      let s := set_prev s (arr_set (ds_prev s) (Z.land str (ds_w_mask s)) (arr_get (ds_head s) h)) in
      let s := set_head s (arr_set (ds_head s) h (wrap16 str)) in
      let str := str + 1 in
      let n := n - 1 in
      if negb (Z.eqb n 0) then setdict_inner f s str n else (s, str)
  end.

Fixpoint setdict_outer (fuel : nat) (s : deflate_state) : deflate_state :=
  match fuel with
  | O => s
  | S f =>
      if Z.leb MIN_MATCH (ds_lookahead s) then
        let str := ds_strstart s in
        let n := ds_lookahead s - (MIN_MATCH - 1) in
        let '(s, str) := setdict_inner (Z.to_nat n) s str n in
        let s := set_strstart s str in
        let s := set_lookahead s (MIN_MATCH - 1) in
        let s := fill_window s in
        setdict_outer f s
      else s
  end.

Definition deflateSetDictionary_m (s : deflate_state) (zc : ZCall) (dictionary : list Z)
  : deflate_state * ZRet :=
  let cs := cstrm_of_call zc in
  let s := set_strm s cs in
  let dictLength := zlength dictionary in
  if deflateStateCheck s then (s, zret_of_cs cs Z_STREAM_ERROR)
  else
    let wrap := ds_wrap s in
    if (wrap =? 2) || ((wrap =? 1) && negb (ds_status s =? INIT_STATE)) || negb (ds_lookahead s =? 0)
    then (s, zret_of_cs cs Z_STREAM_ERROR)
    else
      let s := if Z.eqb wrap 1
               then set_strm s (cset_adler (ds_strm s) (adler32_upd (cs_adler (ds_strm s)) dictionary))
               else s in
      let s := set_wrap s 0 in
      let '(s, dict) :=
        if Z.leb (ds_w_size s) dictLength then
          let s := if Z.eqb wrap 0 then
                     let s := clear_hash s in
                     let s := set_strstart s 0 in
                     let s := set_block_start s 0 in
                     set_insert s 0
                   else s in
          (s, zskipn (dictLength - ds_w_size s) dictionary)
        else (s, dictionary) in
      let saved := ds_strm s in
      let s := set_strm s (cset_avail_in (cset_next_in (cset_input saved (arr_of_list dict)) 0) (zlength dict)) in
      let s := fill_window s in
      let s := setdict_outer (Z.to_nat (zlength dict + 2)) s in
      let s := set_strstart s (ds_strstart s + ds_lookahead s) in
      let s := set_block_start s (ds_strstart s) in
      let s := set_insert s (ds_lookahead s) in
      let s := set_lookahead s 0 in
      let s := set_prev_length s (MIN_MATCH - 1) in
      let s := set_match_length s (MIN_MATCH - 1) in
      let s := set_match_available s 0 in
      let st := ds_strm s in
      let st := cset_input (cset_next_in (cset_avail_in st (cs_avail_in saved)) (cs_next_in saved)) (cs_input saved) in
      let s := set_strm s st in
      let s := set_wrap s wrap in
      (s, zret_of_cs (ds_strm s) Z_OK).


Definition deflateBound_m (s : deflate_state) (sourceLen : Z) : Z :=
  let fixedlen := sourceLen + Z.shiftr sourceLen 3 + Z.shiftr sourceLen 8 + Z.shiftr sourceLen 9 + 4 in
  let storelen := sourceLen + Z.shiftr sourceLen 5 + Z.shiftr sourceLen 7 + Z.shiftr sourceLen 11 + 7 in
  if deflateStateCheck s then wrap64 ((if Z.ltb storelen fixedlen then fixedlen else storelen) + 6)
  else
    let wraplen :=
      if Z.eqb (ds_wrap s) 0 then 0
      else if Z.eqb (ds_wrap s) 1 then 6 + (if negb (Z.eqb (ds_strstart s) 0) then 4 else 0)
      else if Z.eqb (ds_wrap s) 2 then 18
      else 6 in
    if negb (Z.eqb (ds_w_bits s) 15) || negb (Z.eqb (ds_hash_bits s) (8 + 7)) then
      wrap64 ((if Z.leb (ds_w_bits s) (ds_hash_bits s) && negb (Z.eqb (ds_level s) 0)
               then fixedlen else storelen) + wraplen)
    else
      wrap64 (sourceLen + Z.shiftr sourceLen 12 + Z.shiftr sourceLen 14 + Z.shiftr sourceLen 25 + 13 - 6 + wraplen).

Definition compressBound_m (sourceLen : Z) : Z :=
  wrap64 (sourceLen + Z.shiftr sourceLen 12 + Z.shiftr sourceLen 14 + Z.shiftr sourceLen 25 + 13).


Definition RANK (f : Z) : Z := f * 2 - (if Z.ltb 4 f then 9 else 0).

Definition err_return (s : deflate_state) (err : Z) : deflate_state * Z :=
  (set_strm s (cset_msg (ds_strm s) (MSG_ERR err)), err).

Definition run_compress_func (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  if Z.eqb (ds_level s) 0 then deflate_stored s flush
  else if Z.eqb (ds_strategy s) Z_HUFFMAN_ONLY then deflate_huff s flush
  else if Z.eqb (ds_strategy s) Z_RLE then deflate_rle s flush
  else if Z.leb (ds_level s) 3 then deflate_fast s flush
  else deflate_slow s flush.

Definition deflate_zlib_header (s : deflate_state) : deflate_state * option Z :=
  let header := Z.shiftl (Z_DEFLATED + Z.shiftl (ds_w_bits s - 8) 4) 8 in
  let level_flags :=
    if Z.leb Z_HUFFMAN_ONLY (ds_strategy s) || Z.ltb (ds_level s) 2 then 0
    else if Z.ltb (ds_level s) 6 then 1
    else if Z.eqb (ds_level s) 6 then 2
    else 3 in
  let header := Z.lor header (Z.shiftl level_flags 6) in
  let header := if negb (Z.eqb (ds_strstart s) 0) then Z.lor header PRESET_DICT else header in
  let header := header + (31 - header mod 31) in
  let s := putShortMSB s header in
  let s :=
    if negb (Z.eqb (ds_strstart s) 0) then
      let adler := cs_adler (ds_strm s) in
      let s := putShortMSB s (wrap32 (Z.shiftr adler 16)) in
      putShortMSB s (Z.land adler 65535)
    else s in
  let s := set_strm s (cset_adler (ds_strm s) adler32_init) in
  let s := set_status s BUSY_STATE in
  let s := flush_pending s in
  if negb (Z.eqb (ds_pending s) 0) then (set_last_flush s (-1), Some Z_OK) else (s, None).

Definition deflate_gzip_header (s : deflate_state) : deflate_state * option Z :=
  let s := set_strm s (cset_adler (ds_strm s) crc32_init) in
  let s := put_byte s 31 in
  let s := put_byte s 139 in
  let s := put_byte s 8 in
  let s := put_byte s 0 in
  let s := put_byte s 0 in
  let s := put_byte s 0 in
  let s := put_byte s 0 in
  let s := put_byte s 0 in
  let s := put_byte s (if Z.eqb (ds_level s) 9 then 2
                       else if Z.leb Z_HUFFMAN_ONLY (ds_strategy s) || Z.ltb (ds_level s) 2 then 4
                       else 0) in
  let s := put_byte s OS_CODE in
  let s := set_status s BUSY_STATE in
  let s := flush_pending s in
  if negb (Z.eqb (ds_pending s) 0) then (set_last_flush s (-1), Some Z_OK) else (s, None).

Definition deflate_trailer (s : deflate_state) : deflate_state * Z :=
  let st := ds_strm s in
  let s :=
    if Z.eqb (ds_wrap s) 2 then
      let a := cs_adler st in let t := cs_total_in st in
      let s := put_byte s (Z.land a 255) in
      let s := put_byte s (Z.land (Z.shiftr a 8) 255) in
      let s := put_byte s (Z.land (Z.shiftr a 16) 255) in
      let s := put_byte s (Z.land (Z.shiftr a 24) 255) in
      let s := put_byte s (Z.land t 255) in
      let s := put_byte s (Z.land (Z.shiftr t 8) 255) in
      let s := put_byte s (Z.land (Z.shiftr t 16) 255) in
      put_byte s (Z.land (Z.shiftr t 24) 255)
    else
      let a := cs_adler st in
      let s := putShortMSB s (wrap32 (Z.shiftr a 16)) in
      putShortMSB s (Z.land a 65535) in
  let s := flush_pending s in
  let s := if Z.ltb 0 (ds_wrap s) then set_wrap s (- ds_wrap s) else s in
  (s, if negb (Z.eqb (ds_pending s) 0) then Z_OK else Z_STREAM_END).

Definition deflate_blocks (s : deflate_state) (flush : Z) : deflate_state * option Z :=
  if negb (Z.eqb (cs_avail_in (ds_strm s)) 0) || negb (Z.eqb (ds_lookahead s) 0)
     || (negb (Z.eqb flush Z_NO_FLUSH) && negb (Z.eqb (ds_status s) FINISH_STATE))
  then
    let '(s, bstate) := run_compress_func s flush in
    let s := if block_state_eqb bstate finish_started || block_state_eqb bstate finish_done
             then set_status s FINISH_STATE else s in
    if block_state_eqb bstate need_more || block_state_eqb bstate finish_started then
      let s := if Z.eqb (cs_avail_out (ds_strm s)) 0 then set_last_flush s (-1) else s in
      (s, Some Z_OK)
    else if block_state_eqb bstate block_done then
      let s :=
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
      let s := flush_pending s in
      if Z.eqb (cs_avail_out (ds_strm s)) 0 then (set_last_flush s (-1), Some Z_OK) else (s, None)
    else (s, None)
  else (s, None).

Definition deflate_core (s : deflate_state) (flush : Z) : deflate_state * Z :=
  if deflateStateCheck s || Z.ltb Z_BLOCK flush || Z.ltb flush 0 then (s, Z_STREAM_ERROR)
  else if Z.eqb (ds_status s) FINISH_STATE && negb (Z.eqb flush Z_FINISH) then err_return s Z_STREAM_ERROR
  else if Z.eqb (cs_avail_out (ds_strm s)) 0 then err_return s Z_BUF_ERROR
  else
    let old_flush := ds_last_flush s in
    let s := set_last_flush s flush in
    let '(s, r) :=
      if negb (Z.eqb (ds_pending s) 0) then
        let s := flush_pending s in
        if Z.eqb (cs_avail_out (ds_strm s)) 0 then (set_last_flush s (-1), Some Z_OK) else (s, None)
      else if Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.leb (RANK flush) (RANK old_flush)
              && negb (Z.eqb flush Z_FINISH)
      then let '(s, rc) := err_return s Z_BUF_ERROR in (s, Some rc)
      else (s, None) in
    match r with Some rc => (s, rc) | None =>
    if Z.eqb (ds_status s) FINISH_STATE && negb (Z.eqb (cs_avail_in (ds_strm s)) 0)
    then err_return s Z_BUF_ERROR
    else
    let s := if Z.eqb (ds_status s) INIT_STATE && Z.eqb (ds_wrap s) 0 then set_status s BUSY_STATE else s in
    let '(s, r) := if Z.eqb (ds_status s) INIT_STATE then deflate_zlib_header s else (s, None) in
    match r with Some rc => (s, rc) | None =>
    let '(s, r) := if Z.eqb (ds_status s) GZIP_STATE then deflate_gzip_header s else (s, None) in
    match r with Some rc => (s, rc) | None =>
    let '(s, r) := deflate_blocks s flush in
    match r with Some rc => (s, rc) | None =>
    if negb (Z.eqb flush Z_FINISH) then (s, Z_OK)
    else if Z.leb (ds_wrap s) 0 then (s, Z_STREAM_END)
    else deflate_trailer s
    end end end end.

Definition deflate_m (s : deflate_state) (zc : ZCall) (flush : Z) : deflate_state * ZRet :=
  let s := set_strm s (cstrm_of_call zc) in
  let '(s, rc) := deflate_core s flush in
  (s, zret_of_cs (ds_strm s) rc).


Record c2st : Type := mkC2 {
  c2_s : deflate_state; c2_z : zstrm; c2_left : Z; c2_sourceLen : Z;
  c2_in_pos : Z; c2_avail_in : Z; c2_avail_out : Z; c2_out_rev : list Z; c2_err : Z }.

Definition C2_MAX : Z := 4294967295.

Definition compress2_body (source : list Z) (x : c2st) : c2st :=
  let '(avail_out, left') :=
    if Z.eqb (c2_avail_out x) 0 then
      let ao := if Z.ltb C2_MAX (c2_left x) then C2_MAX else c2_left x in (ao, c2_left x - ao)
    else (c2_avail_out x, c2_left x) in
  let '(avail_in, sourceLen) :=
    if Z.eqb (c2_avail_in x) 0 then
      let ai := if Z.ltb C2_MAX (c2_sourceLen x) then C2_MAX else c2_sourceLen x in (ai, c2_sourceLen x - ai)
    else (c2_avail_in x, c2_sourceLen x) in
  let zc := mkZCall (zfirstn avail_in (zskipn (c2_in_pos x) source)) avail_out (c2_z x) in
  let '(s, r) := deflate_m (c2_s x) zc (if negb (Z.eqb sourceLen 0) then Z_NO_FLUSH else Z_FINISH) in
  mkC2 s (zr_strm r) left' sourceLen (c2_in_pos x + zr_consumed r) (avail_in - zr_consumed r)
       (avail_out - zlength (zr_output r)) (List.rev_append (zr_output r) (c2_out_rev x)) (zr_rc r).

Fixpoint compress2_loop (fuel : nat) (source : list Z) (x : c2st) : c2st :=
  match fuel with
  | O => x
  | S f =>
      let x := compress2_body source x in
      if Z.eqb (c2_err x) Z_OK then compress2_loop f source x else x
  end.

Section Compress2.
  Context {St : Type}.
  Variable hooks : zhooks St.

  Definition compress2_m (destLen : Z) (source : list Z) (level : Z) : SM St (Z * list Z * Z) :=
    let left0 := destLen in
    do ri <- deflateInit2_m hooks (mkZCall [] 0 zstrm0) level Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY ;
    let '(os, r) := ri in
    match os with
    | None => sret (zr_rc r, [], 0)
    | Some s =>
        let x0 := mkC2 s (zr_strm r) left0 (zlength source) 0 0 0 [] Z_OK in
        let x := compress2_loop (Z.to_nat (destLen + zlength source + 2)) source x0 in
        let destLen' := zs_total_out (c2_z x) in
        do _ <- deflateEnd_m hooks (c2_s x) (mkZCall [] 0 (c2_z x)) ;
        sret ((if Z.eqb (c2_err x) Z_STREAM_END then Z_OK else c2_err x), List.rev_append (c2_out_rev x) [], destLen')
    end.

  Definition compress_m (destLen : Z) (source : list Z) : SM St (Z * list Z * Z) :=
    compress2_m destLen source Z_DEFAULT_COMPRESSION.
End Compress2.


Definition deflate_model : deflate_api deflate_state :=
  mkDeflateApi
    (fun St hooks => @deflateInit2_m St hooks)
    deflateSetDictionary_m
    deflateBound_m
    deflate_m
    (fun St hooks => @deflateEnd_m St hooks)
    compressBound_m
    (fun St hooks => @compress2_m St hooks).
