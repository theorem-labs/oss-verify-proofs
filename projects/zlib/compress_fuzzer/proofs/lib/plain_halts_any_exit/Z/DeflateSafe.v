(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition bytes_okP (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.
Definition zstrm_okP (z : zstrm) : Prop :=
  0 <= zs_total_in z < 2 ^ 64 /\ 0 <= zs_total_out z < 2 ^ 64 /\ 0 <= zs_adler z < 2 ^ 64
  /\ - 2 ^ 31 <= zs_data_type z < 2 ^ 31.

Definition dcall_wf (zc : ZCall) : Prop :=
  zstrm_okP (zc_strm zc) /\ 0 <= zc_avail_out zc < 2 ^ 32 /\ zlength (zc_input zc) < 2 ^ 32 /\ bytes_okP (zc_input zc).

Definition DCH : Type := list (option (blk * (Z -> Z))).
Definition dhooks : zhooks DCH :=
  mkHooks (fun _ _ => fun chs : DCH => match chs with
                                      | [] => MRet (None, [])
                                      | c :: chs' => MRet (c, chs')
                                      end)
          (fun _ => fun chs : DCH => MRet (tt, chs)).
Definition dpure {A} (m : SM DCH A) (chs : DCH) : option A :=
  match m chs with MRet p => Some (fst p) | _ => None end.

Inductive dreach : deflate_state -> Prop :=
| DR_init : forall zc level method wb memlevel strategy chs s zr,
    5 <= memlevel ->
    dpure (deflateInit2_m dhooks zc level method wb memlevel strategy) chs = Some (Some s, zr) -> dreach s
| DR_deflate : forall s zc flush s' zr,
    dreach s -> dcall_wf zc -> 0 <= flush < 16 ->
    deflate_m s zc flush = (s', zr) -> dreach s'
| DR_setdict : forall s zc dict s' zr,
    dreach s -> zstrm_okP (zc_strm zc) -> bytes_okP dict -> 0 < zlength dict < 2 ^ 32 ->
    deflateSetDictionary_m s zc dict = (s', zr) -> dreach s'.

Definition reach (ds : deflate_state) (zc : ZCall) (flush : Z) : Prop :=
  dreach ds /\ dcall_wf zc /\ 0 <= flush < 16.

Definition st4 (st : Z) : Prop := st = INIT_STATE \/ st = GZIP_STATE \/ st = BUSY_STATE \/ st = FINISH_STATE.

Section Obligations.

  Variable SAFEs : deflate_state -> Z -> Prop.
Variable SAFEf : deflate_state -> Z -> Prop.
Variable SAFEw : deflate_state -> Z -> Prop.
  Variable FB : deflate_state -> option Z -> Z -> Z -> Prop.
  Variable WF : deflate_state -> Prop.

Record DOK (X : deflate_state) : Prop := {
  ok_st : st4 (ds_status X);
  ok_wrap : - 2 <= ds_wrap X <= 2;
  ok_lf : - 2 ^ 31 <= ds_last_flush X < 2 ^ 31;
  ok_gzhead : ds_gzhead X = 0;
  ok_level : 0 <= ds_level X <= 9;
  ok_strategy : 0 <= ds_strategy X <= 4;
  ok_wbits : 9 <= ds_w_bits X <= 15;
  ok_pend : 0 <= ds_pending_out X /\ 0 <= ds_pending X /\ ds_pending_out X + ds_pending X <= ds_lit_bufsize X * 4;
  ok_bi : 0 <= ds_bi_valid X <= 16 /\ 0 <= ds_bi_buf X < 2 ^ 16;
  ok_strstart : 0 <= ds_strstart X < 2 ^ 32;
  ok_look : 0 <= ds_lookahead X < 2 ^ 32;
  ok_bs : - 2 ^ 63 <= ds_block_start X < 2 ^ 63;
  ok_ins : 0 <= ds_insert X < 2 ^ 32;
  ok_sn : 0 <= ds_sym_next X < 2 ^ 32;
  ok_ain : 0 <= cs_avail_in (ds_strm X) < 2 ^ 32;
  ok_aout : 0 <= cs_avail_out (ds_strm X) < 2 ^ 32;
  ok_nin : 0 <= cs_next_in (ds_strm X) /\ cs_next_in (ds_strm X) + cs_avail_in (ds_strm X) = arr_len (cs_input (ds_strm X));
  ok_tin : 0 <= cs_total_in (ds_strm X) < 2 ^ 64;
  ok_tout : 0 <= cs_total_out (ds_strm X) < 2 ^ 64;
  ok_adler : 0 <= cs_adler (ds_strm X) < 2 ^ 64;
  ok_dt : - 2 ^ 31 <= cs_data_type (ds_strm X) < 2 ^ 31 }.

Definition fp_ok (X : deflate_state) : Prop :=
  let PBL := ds_lit_bufsize X * 4 in
  BINV PBL X
  /\ (let X1 := tr_flush_bits X in
      0 <= ds_pending X1 < 2 ^ 31 /\ ds_pending X1 <= PBL /\ 0 <= ds_pending_out X1 /\ ds_pending_out X1 + fp_len X1 <= PBL
      /\ 0 <= cs_total_out (ds_strm X1) < 2 ^ 64).

Definition lz_keeps (X X' : deflate_state) : Prop :=
  (ds_w_size X', ds_hash_size X', ds_lit_bufsize X') = (ds_w_size X, ds_hash_size X, ds_lit_bufsize X)
  /\ arr_len (ds_window X') = arr_len (ds_window X) /\ arr_len (ds_prev X') = arr_len (ds_prev X)
  /\ arr_len (ds_head X') = arr_len (ds_head X) /\ arr_len (ds_pending_buf X') = arr_len (ds_pending_buf X)
  /\ cs_input (ds_strm X') = cs_input (ds_strm X)
  /\ Z.of_nat (length (cs_out_rev (ds_strm X'))) + cs_avail_out (ds_strm X')
     = Z.of_nat (length (cs_out_rev (ds_strm X))) + cs_avail_out (ds_strm X)
  /\ 0 <= cs_avail_out (ds_strm X')
  /\ (length (cs_out_rev (ds_strm X)) <= length (cs_out_rev (ds_strm X')))%nat.

Definition fblk_ok (s : deflate_state) (last : Z) : Prop :=
  let PBL := ds_lit_bufsize s * 4 in
  let buf := if Z.leb 0 (ds_block_start s) then Some (wrap32 (ds_block_start s)) else None in
  let len := wrap64 (ds_strstart s - ds_block_start s) in
  FB s buf len last /\ BINV PBL s /\ 0 <= ds_strstart s - ds_block_start s < 2 ^ 32
  /\ - 2 ^ 63 <= ds_block_start s /\ 0 <= ds_strstart s <= 2 * ds_w_size s /\ 0 <= ds_lookahead s <= 2 * ds_w_size s
  /\ (forall j, 0 <= j < 2 * ds_w_size s -> 0 <= arr_get (ds_window s) j < 256)
  /\ let s8 := tr_flush_block s buf len last in
     let s9 := set_block_start s8 (ds_strstart s8) in
     BINV PBL s9 /\ ds_pending (tr_flush_bits s9) <= PBL
     /\ let s10 := tr_flush_bits s9 in
        0 <= ds_pending s10 < 2 ^ 31 /\ 0 <= ds_pending_out s10 /\ ds_pending_out s10 + fp_len s10 <= PBL
        /\ 0 <= cs_total_out (ds_strm s10) < 2 ^ 64
        /\ 0 <= cs_avail_out (ds_strm (flush_block_only s last)) < 2 ^ 32
        /\ lz_keeps s (flush_block_only s last).

Definition hf_fill (s : deflate_state) (flush : Z) : deflate_state * option loop_out :=
  if Z.eqb (ds_lookahead s) 0 then
    let s := fill_window s in
    if Z.eqb (ds_lookahead s) 0 then
      if Z.eqb flush Z_NO_FLUSH then (s, Some (LRet need_more)) else (s, Some LBreak)
    else (s, None)
  else (s, None).

Definition hf_tally (s : deflate_state) : deflate_state * bool :=
  let s := set_match_length s 0 in
  let '(s, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s)) in
  let s := set_lookahead s (ds_lookahead s - 1) in
  let s := set_strstart s (ds_strstart s + 1) in
  (s, bflush).

Definition st_bflush0 (s : deflate_state) (bflush : bool) : deflate_state * loop_out :=
  if bflush then
    let '(s, r) := flush_block s 0 in
    match r with Some bs => (s, LRet bs) | None => (s, LCont) end
  else (s, LCont).

Definition hf_body (s : deflate_state) (flush : Z) : deflate_state * loop_out :=
  let '(s1, e) := hf_fill s flush in
  match e with
  | Some o => (s1, o)
  | None => let '(s2, b) := hf_tally s1 in st_bflush0 s2 b
  end.

Definition hf_tally_ok (s1 : deflate_state) : Prop :=
  DOK s1 /\ 1 <= ds_lookahead s1 /\ ds_strstart s1 + ds_lookahead s1 <= 2 * ds_w_size s1
  /\ 0 <= ds_sym_next s1 /\ ds_sym_next s1 + 3 <= 3 * ds_lit_bufsize s1 /\ 0 <= ds_sym_end s1 < 2 ^ 32
  /\ (forall j, 0 <= j < 2 * ds_w_size s1 -> 0 <= arr_get (ds_window s1) j < 256)
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s1) i < 65536)
  /\ (snd (hf_tally s1) = true -> fblk_ok (fst (hf_tally s1)) 0).

Definition hf_trip_ok (s : deflate_state) (flush : Z) : Prop :=
  DOK s
  /\ (ds_lookahead s = 0 -> fw_wf (ds_w_size s) (ds_hash_size s) s /\ DOK (fill_window s) /\ lz_keeps s (fill_window s))
  /\ (snd (hf_fill s flush) = None -> hf_tally_ok (fst (hf_fill s flush))).

Fixpoint hf_loop_ok (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => False
  | S f => hf_trip_ok s flush
           /\ match snd (hf_body s flush) with
              | LCont => hf_loop_ok f (fst (hf_body s flush)) flush
              | _ => True
              end
  end.

Definition tail0 (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  deflate_tail (set_insert s 0) flush.

Definition tail0_ok (s : deflate_state) (flush : Z) : Prop :=
  let s := set_insert s 0 in
  DOK s
  /\ (flush = Z_FINISH -> fblk_ok s 1)
  /\ (flush <> Z_FINISH -> ds_sym_next s <> 0 -> fblk_ok s 0).

Definition huff_ok (s : deflate_state) (flush : Z) : Prop :=
  hf_loop_ok (lz_fuel s) s flush
  /\ match snd (deflate_huff_loop (lz_fuel s) s flush) with
     | Some _ => True
     | None => tail0_ok (fst (deflate_huff_loop (lz_fuel s) s flush)) flush
     end
  /\ lz_keeps s (fst (deflate_huff s flush)) /\ DOK (fst (deflate_huff s flush)).

Definition rl_fill (s : deflate_state) (flush : Z) : deflate_state * option loop_out :=
  if Z.leb (ds_lookahead s) MAX_MATCH then
    let s := fill_window s in
    if Z.leb (ds_lookahead s) MAX_MATCH && Z.eqb flush Z_NO_FLUSH then (s, Some (LRet need_more))
    else if Z.eqb (ds_lookahead s) 0 then (s, Some LBreak)
    else (s, None)
  else (s, None).

Definition rl_run (s : deflate_state) : deflate_state :=
  let s := set_match_length s 0 in
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
  else s.

Definition rl_tally (s : deflate_state) : deflate_state * bool :=
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
    (s, bflush).

Definition rl_body (s : deflate_state) (flush : Z) : deflate_state * loop_out :=
  let '(s1, e) := rl_fill s flush in
  match e with
  | Some o => (s1, o)
  | None => let '(s3, b) := rl_tally (rl_run s1) in st_bflush0 s3 b
  end.

Definition rl_tally_ok (s2 : deflate_state) : Prop :=
  DOK s2 /\ 1 <= ds_lookahead s2 /\ ds_strstart s2 + ds_lookahead s2 <= 2 * ds_w_size s2
  /\ 0 <= ds_match_length s2 <= ds_lookahead s2 /\ ds_match_length s2 <= MAX_MATCH
  /\ 0 <= ds_sym_next s2 /\ ds_sym_next s2 + 3 <= 3 * ds_lit_bufsize s2 /\ 0 <= ds_sym_end s2 < 2 ^ 32
  /\ (forall j, 0 <= j < 2 * ds_w_size s2 -> 0 <= arr_get (ds_window s2) j < 256)
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s2) i < 65536)
  /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc s2) i < 65536)
  /\ (snd (rl_tally s2) = true -> fblk_ok (fst (rl_tally s2)) 0).

Definition rl_run_ok (s1 : deflate_state) : Prop :=
  DOK s1 /\ 1 <= ds_lookahead s1 /\ ds_strstart s1 + ds_lookahead s1 <= 2 * ds_w_size s1
  /\ (MIN_MATCH <= ds_lookahead s1 -> 0 < ds_strstart s1 -> ds_strstart s1 + MAX_MATCH < 2 * ds_w_size s1)
  /\ (forall j, 0 <= j < 2 * ds_w_size s1 -> 0 <= arr_get (ds_window s1) j < 256).

Definition rl_trip_ok (s : deflate_state) (flush : Z) : Prop :=
  DOK s
  /\ (ds_lookahead s <= MAX_MATCH -> fw_wf (ds_w_size s) (ds_hash_size s) s /\ DOK (fill_window s) /\ lz_keeps s (fill_window s))
  /\ (snd (rl_fill s flush) = None ->
      rl_run_ok (fst (rl_fill s flush)) /\ rl_tally_ok (rl_run (fst (rl_fill s flush)))).

Fixpoint rl_loop_ok (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => False
  | S f => rl_trip_ok s flush
           /\ match snd (rl_body s flush) with
              | LCont => rl_loop_ok f (fst (rl_body s flush)) flush
              | _ => True
              end
  end.

Definition rle_ok (s : deflate_state) (flush : Z) : Prop :=
  rl_loop_ok (lz_fuel s) s flush
  /\ match snd (deflate_rle_loop (lz_fuel s) s flush) with
     | Some _ => True
     | None => tail0_ok (fst (deflate_rle_loop (lz_fuel s) s flush)) flush
     end
  /\ lz_keeps s (fst (deflate_rle s flush)) /\ DOK (fst (deflate_rle s flush)).

Definition blk_keeps (s0 s' : deflate_state) : Prop :=
  (ds_self_blk s', ds_window_blk s', ds_prev_blk s', ds_head_blk s', ds_pending_buf_blk s')
  = (ds_self_blk s0, ds_window_blk s0, ds_prev_blk s0, ds_head_blk s0, ds_pending_buf_blk s0)
  /\ lz_keeps s0 s'.

Definition dpost_ok (s0 s' : deflate_state) (rc : Z) : Prop :=
  let st0 := ds_strm s0 in let st := ds_strm s' in
  WF s' /\ DOK s' /\ blk_keeps s0 s'
  /\ 0 <= cs_next_in st <= arr_len (cs_input st0)
  /\ cs_next_in st + cs_avail_in st = arr_len (cs_input st0)
  /\ Z.of_nat (length (cs_out_rev st)) + cs_avail_out st = Z.of_nat (length (cs_out_rev st0)) + cs_avail_out st0
  /\ 0 <= cs_avail_out st
  /\ Forall (fun b => 0 <= b < 256) (cs_output st)
  /\ - 2 ^ 31 <= rc < 2 ^ 31
  /\ (cs_total_out st = wrap64 (cs_total_out st0 + Z.of_nat (length (cs_out_rev st)) - Z.of_nat (length (cs_out_rev st0)))
      \/ (rc = Z_MEM_ERROR /\ cs_total_out st = cs_total_out st0)).

Definition blocks_call_ok (s : deflate_state) (flush : Z) : Prop :=
  let s' := fst (run_compress_func s flush) in
  lz_keeps s s' /\ DOK s'
  /\ (if Z.eqb (ds_level s) 0 then SAFEs s flush
      else if Z.eqb (ds_strategy s) Z_HUFFMAN_ONLY then huff_ok s flush
      else if Z.eqb (ds_strategy s) Z_RLE then rle_ok s flush
      else if Z.leb (ds_level s) 3 then SAFEf s flush
      else SAFEw s flush).

Definition bdone_st (s : deflate_state) (flush : Z) : deflate_state :=
  if Z.eqb flush Z_PARTIAL_FLUSH then tr_align s
  else if negb (Z.eqb flush Z_BLOCK) then
    let s := tr_stored_block s None 0 0 in
    if Z.eqb flush Z_FULL_FLUSH then
      let s := clear_hash s in
      if Z.eqb (ds_lookahead s) 0 then set_insert (set_block_start (set_strstart s 0) 0) 0 else s
    else s
  else s.

Definition bdone_ok (s : deflate_state) (flush : Z) : Prop :=
  let PBL := ds_lit_bufsize s * 4 in
  DOK s /\ BINV PBL s
  /\ (flush = Z_PARTIAL_FLUSH -> ds_pending (tr_align s) <= PBL)
  /\ (flush <> Z_PARTIAL_FLUSH -> flush <> Z_BLOCK -> ds_pending (tr_stored_block s None 0 0) <= PBL)
  /\ DOK (bdone_st s flush) /\ fp_ok (bdone_st s flush)
  /\ DOK (flush_pending (bdone_st s flush)).

Definition blocks_ok (s0 s : deflate_state) (flush : Z) : Prop :=
  DOK s
  /\ (negb (Z.eqb (cs_avail_in (ds_strm s)) 0) || negb (Z.eqb (ds_lookahead s) 0)
      || (negb (Z.eqb flush Z_NO_FLUSH) && negb (Z.eqb (ds_status s) FINISH_STATE)) = true ->
      blocks_call_ok s flush
      /\ let '(s1, bstate) := run_compress_func s flush in
         let s2 := if block_state_eqb bstate finish_started || block_state_eqb bstate finish_done
                   then set_status s1 FINISH_STATE else s1 in
         DOK s2
         /\ (block_state_eqb bstate need_more || block_state_eqb bstate finish_started = true ->
             dpost_ok s0 (if Z.eqb (cs_avail_out (ds_strm s2)) 0 then set_last_flush s2 (-1) else s2) Z_OK)
         /\ (bstate = block_done ->
             bdone_ok s2 flush
             /\ (Z.eqb (cs_avail_out (ds_strm (flush_pending (bdone_st s2 flush)))) 0 = true ->
                 dpost_ok s0 (set_last_flush (flush_pending (bdone_st s2 flush)) (-1)) Z_OK))).

Definition trailer_st (s : deflate_state) : deflate_state :=
  let st := ds_strm s in
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
    putShortMSB (putShortMSB s (wrap32 (Z.shiftr a 16))) (Z.land a 65535).

Definition trailer_ok (s0 s : deflate_state) : Prop :=
  let PBL := ds_lit_bufsize s * 4 in
  DOK s /\ 0 < ds_wrap s
  /\ ds_pending s + (if Z.eqb (ds_wrap s) 2 then 8 else 4) <= PBL
  /\ DOK (trailer_st s) /\ fp_ok (trailer_st s)
  /\ let s2 := flush_pending (trailer_st s) in
     DOK s2 /\ 0 <= ds_pending s2 < 2 ^ 64 /\ 0 < ds_wrap s2
     /\ dpost_ok s0 (set_wrap s2 (- ds_wrap s2)) (if negb (Z.eqb (ds_pending s2) 0) then Z_OK else Z_STREAM_END).

Definition zhdr_st (s : deflate_state) : deflate_state :=
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
  set_status s BUSY_STATE.

Definition gzhdr_st (s : deflate_state) : deflate_state :=
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
  set_status s BUSY_STATE.

Definition hdr_ok (s0 s : deflate_state) (hst : deflate_state) (room : Z) : Prop :=
  DOK s /\ ds_pending s + room <= ds_lit_bufsize s * 4
  /\ DOK hst /\ fp_ok hst
  /\ let s2 := flush_pending hst in
     DOK s2 /\ 0 <= ds_pending s2 < 2 ^ 64
     /\ (ds_pending s2 <> 0 -> dpost_ok s0 (set_last_flush s2 (-1)) Z_OK).

Definition finish_ok (s0 s : deflate_state) (flush : Z) : Prop :=
  DOK s
  /\ (flush <> Z_FINISH -> dpost_ok s0 s Z_OK)
  /\ (flush = Z_FINISH -> ds_wrap s <= 0 -> dpost_ok s0 s Z_STREAM_END)
  /\ (flush = Z_FINISH -> 0 < ds_wrap s -> trailer_ok s0 s).

Definition body_ok (s0 s : deflate_state) (flush : Z) : Prop :=
  DOK s
  /\ (ds_status s = FINISH_STATE /\ cs_avail_in (ds_strm s) <> 0 ->
      dpost_ok s0 (fst (err_return s Z_BUF_ERROR)) Z_BUF_ERROR)
  /\ (~ (ds_status s = FINISH_STATE /\ cs_avail_in (ds_strm s) <> 0) ->
      let s4 := if Z.eqb (ds_status s) INIT_STATE && Z.eqb (ds_wrap s) 0 then set_status s BUSY_STATE else s in
      DOK s4
      /\ (ds_status s4 = INIT_STATE -> hdr_ok s0 s4 (zhdr_st s4) 6)
      /\ let s5 := if Z.eqb (ds_status s4) INIT_STATE then flush_pending (zhdr_st s4) else s4 in
         ((ds_status s4 = INIT_STATE -> ds_pending s5 = 0) ->
          (ds_status s5 = GZIP_STATE -> hdr_ok s0 s5 (gzhdr_st s5) 10)
          /\ let s6 := if Z.eqb (ds_status s5) GZIP_STATE then flush_pending (gzhdr_st s5) else s5 in
             ((ds_status s5 = GZIP_STATE -> ds_pending s6 = 0) ->
              blocks_ok s0 s6 flush
              /\ (snd (deflate_blocks s6 flush) = None -> finish_ok s0 (fst (deflate_blocks s6 flush)) flush)))).

Definition rank_err (s0 : deflate_state) (flush : Z) : Prop :=
  cs_avail_in (ds_strm s0) = 0 /\ RANK flush <= RANK (ds_last_flush s0) /\ flush <> Z_FINISH.

Definition deflate_safe (ds : deflate_state) (zc : ZCall) (flush : Z) : Prop :=
  let s0 := set_strm ds (cstrm_of_call zc) in
  DOK s0 /\ deflateStateCheck s0 = false /\ - 2 <= ds_last_flush s0 <= 5
  /\
     dpost_ok s0 s0 Z_STREAM_ERROR
  /\ dpost_ok s0 (fst (err_return s0 Z_STREAM_ERROR)) Z_STREAM_ERROR
  /\ dpost_ok s0 (fst (err_return s0 Z_BUF_ERROR)) Z_BUF_ERROR
  /\ (flush <= 5 -> ~ (ds_status s0 = FINISH_STATE /\ flush <> Z_FINISH) -> cs_avail_out (ds_strm s0) <> 0 ->
      let s1 := set_last_flush s0 flush in
      DOK s1
      /\ (ds_pending s1 <> 0 ->
          fp_ok s1
          /\ let s2 := flush_pending s1 in
             DOK s2
             /\ (cs_avail_out (ds_strm s2) = 0 -> dpost_ok s0 (set_last_flush s2 (-1)) Z_OK)
             /\ (cs_avail_out (ds_strm s2) <> 0 -> body_ok s0 s2 flush))
      /\ (ds_pending s1 = 0 ->
          (rank_err s0 flush -> dpost_ok s0 (fst (err_return s1 Z_BUF_ERROR)) Z_BUF_ERROR)
          /\ (~ rank_err s0 flush -> body_ok s0 s1 flush))).

End Obligations.

Lemma hf_body_eq : forall s flush, deflate_huff_body s flush = hf_body s flush.
Proof.
  intros s flush. unfold deflate_huff_body, hf_body, hf_fill, hf_tally, st_bflush0.
  destruct (ds_lookahead s =? 0).
  - destruct (ds_lookahead (fill_window s) =? 0); [destruct (flush =? Z_NO_FLUSH); reflexivity|].
    destruct (tr_tally_lit _ _) as [s2 b]. reflexivity.
  - destruct (tr_tally_lit _ _) as [s2 b]. reflexivity.
Qed.

Lemma rl_body_eq : forall s flush, deflate_rle_body s flush = rl_body s flush.
Proof.
  intros s flush. unfold deflate_rle_body, rl_body, rl_fill, rl_run, rl_tally, st_bflush0.
  destruct (ds_lookahead s <=? MAX_MATCH).
  - destruct (_ && (flush =? Z_NO_FLUSH)); [reflexivity|].
    destruct (ds_lookahead (fill_window s) =? 0); [reflexivity|].
    set (s1 := set_match_length (fill_window s) 0). clearbody s1.
    destruct (_ && _); [destruct (rle_cmpk 3 _ _ _) as [sc ok]; destruct ok|];
      (destruct (MIN_MATCH <=? _); [destruct (tr_tally_dist _ _ _) as [s3 b] | destruct (tr_tally_lit _ _) as [s3 b]]; reflexivity).
  - set (s1 := set_match_length s 0). clearbody s1.
    destruct (_ && _); [destruct (rle_cmpk 3 _ _ _) as [sc ok]; destruct ok|];
      (destruct (MIN_MATCH <=? _); [destruct (tr_tally_dist _ _ _) as [s3 b] | destruct (tr_tally_lit _ _) as [s3 b]]; reflexivity).
Qed.

Lemma deflate_zlib_header_eq : forall s,
  deflate_zlib_header s =
  (let s2 := flush_pending (zhdr_st s) in
   if negb (Z.eqb (ds_pending s2) 0) then (set_last_flush s2 (-1), Some Z_OK) else (s2, None)).
Proof. intros s. reflexivity. Qed.

Lemma deflate_gzip_header_eq : forall s,
  deflate_gzip_header s =
  (let s2 := flush_pending (gzhdr_st s) in
   if negb (Z.eqb (ds_pending s2) 0) then (set_last_flush s2 (-1), Some Z_OK) else (s2, None)).
Proof. intros s. reflexivity. Qed.

Lemma deflate_trailer_eq : forall s,
  deflate_trailer s =
  (let s2 := flush_pending (trailer_st s) in
   let s3 := if Z.ltb 0 (ds_wrap s2) then set_wrap s2 (- ds_wrap s2) else s2 in
   (s3, if negb (Z.eqb (ds_pending s3) 0) then Z_OK else Z_STREAM_END)).
Proof. intros s. reflexivity. Qed.

Lemma hf_loop_ok_S : forall FB f s flush,
  hf_loop_ok FB (S f) s flush
  = (hf_trip_ok FB s flush /\ match snd (hf_body s flush) with LCont => hf_loop_ok FB f (fst (hf_body s flush)) flush | _ => True end).
Proof. reflexivity. Qed.
Lemma rl_loop_ok_S : forall FB f s flush,
  rl_loop_ok FB (S f) s flush
  = (rl_trip_ok FB s flush /\ match snd (rl_body s flush) with LCont => rl_loop_ok FB f (fst (rl_body s flush)) flush | _ => True end).
Proof. reflexivity. Qed.
