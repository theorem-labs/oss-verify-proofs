(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import Prog ZIface InflateState Inftrees InflateFast InflateArms.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.


Definition inflateStateCheck (s : inflate_state) : bool :=
  (is_mode s <? HEAD) || (SYNC <? is_mode s).


Section WithVariant.
  Variable iv : ivariant.

  Definition auxp (f : inflate_state -> inflate_state) (s : inflate_state) : inflate_state :=
    if iv_aux iv then f s else s.

  Definition inflateResetKeep (s : inflate_state) (z : zstrm) : inflate_state * zstrm * Z :=
    if inflateStateCheck s then (s, z, Z_STREAM_ERROR)
    else
      let z := zs_set_total_in 0 (zs_set_total_out 0 z) in
      let s := iset_total s 0 in
      let z := zs_set_msg MSG_NULL z in
      let z := if negb (is_wrap s =? 0) then zs_set_adler (Z.land (is_wrap s) 1) z else z in
      let s := iset_mode s HEAD in
      let s := iset_last s 0 in
      let s := iset_havedict s 0 in
      let s := iset_flags s (-1) in
      let s := auxp (fun s => iset_dmax s 32768) s in
      let s := iset_head s 0 in
      let s := iset_hold s 0 in
      let s := iset_bits s 0 in
      let s := iset_next (iset_distcode (iset_lencode s (CDyn 0)) (CDyn 0)) 0 in
      let s := auxp (fun s => iset_sane s 1) s in
      let s := auxp (fun s => iset_back s (-1)) s in
      (s, z, Z_OK).

  Definition inflateReset (s : inflate_state) (z : zstrm) : inflate_state * zstrm * Z :=
    if inflateStateCheck s then (s, z, Z_STREAM_ERROR)
    else
      let s := iset_wnext (iset_whave (iset_wsize s 0) 0) 0 in
      inflateResetKeep s z.

  Section WithHooks.
    Context {St : Type}.
    Variable hooks : zhooks St.

    Definition inflateReset2 (s : inflate_state) (z : zstrm) (windowBits : Z)
      : SM St (inflate_state * zstrm * Z) :=
      if inflateStateCheck s then sret (s, z, Z_STREAM_ERROR)
      else
        let '(bad, wrap, windowBits) :=
          if windowBits <? 0 then (windowBits <? -15, 0, - windowBits)
          else ((false, Z.shiftr windowBits 4 + 5),
                if windowBits <? 48 then Z.land windowBits 15 else windowBits) in
        if bad then sret (s, z, Z_STREAM_ERROR)
        else if negb (windowBits =? 0) && ((windowBits <? 8) || (15 <? windowBits))
        then sret (s, z, Z_STREAM_ERROR)
        else
          do s <- (match is_window_blk s with
                   | Some b => if negb (is_wbits s =? windowBits)
                               then (zfree hooks b ;; sret (iset_window (iset_window_blk s None) (arr_make 0 0)))
                               else sret s
                   | None => sret s
                   end) ;
          let s := iset_wrap s wrap in
          let s := iset_wbits s windowBits in
          sret (inflateReset s z).


    Definition inflateInit2_m (zc : ZCall) (windowBits : Z) : SM St (option inflate_state * ZRet) :=
      let z := zs_set_msg MSG_NULL (zc_strm zc) in
      do r <- zalloc hooks 1 SIZEOF_inflate_state ;
      match r with
      | None => sret (None, zret0 z Z_MEM_ERROR)
      | Some (b, g) =>
          let s := is_of_oracle (iv_lay iv) g b in
          let s := iset_window (iset_window_blk s None) (arr_make 0 0) in
          let s := iset_mode s HEAD in
          do r2 <- inflateReset2 s z windowBits ;
          let '(s, z, ret) := r2 in
          if negb (ret =? Z_OK) then (zfree hooks b ;; sret (None, zret0 z ret))
          else sret (Some s, zret0 z ret)
      end.


    Definition updatewindow (s : inflate_state) (src : arr) (end_ copy : Z)
      : SM St (option inflate_state) :=
      do so <- (match is_window_blk s with
                | Some _ => sret (Some s)
                | None =>
                    do r <- zalloc hooks (shl32 1 (is_wbits s)) 1 ;
                    sret (match r with
                          | None => None
                          | Some (b, g) =>
                              Some (iset_window (iset_window_blk s (Some b))
                                                (iarr_u8_of g 0 (shl32 1 (is_wbits s))))
                          end)
                end) ;
      match so with
      | None => sret None
      | Some s =>
          let s := if is_wsize s =? 0
                   then iset_whave (iset_wnext (iset_wsize s (shl32 1 (is_wbits s))) 0) 0
                   else s in
          if is_wsize s <=? copy then
            let s := iset_window s (arr_blit (is_window s) 0 src (end_ - is_wsize s) (is_wsize s)) in
            sret (Some (iset_whave (iset_wnext s 0) (is_wsize s)))
          else
            let dist := wrap32 (is_wsize s - is_wnext s) in
            let dist := if copy <? dist then copy else dist in
            let s := iset_window s (arr_blit (is_window s) (is_wnext s) src (end_ - copy) dist) in
            let copy := wrap32 (copy - dist) in
            if negb (copy =? 0) then
              let s := iset_window s (arr_blit (is_window s) 0 src (end_ - copy) copy) in
              sret (Some (iset_whave (iset_wnext s copy) (is_wsize s)))
            else
              let s := iset_wnext s (wrap32 (is_wnext s + dist)) in
              let s := if is_wnext s =? is_wsize s then iset_wnext s 0 else s in
              let s := if is_whave s <? is_wsize s then iset_whave s (wrap32 (is_whave s + dist)) else s in
              sret (Some s)
      end.


    Definition inf_leave (flush : Z) (w : iw) : SM St (inflate_state * ZRet) :=
      let w := RESTORE w in
      let s := w_s w in let c := w_c w in let r := w_r w in
      do so <- (if negb (is_wsize s =? 0) ||
                   (negb (ir_out r =? ic_avail_out c) && (is_mode s <? BAD) &&
                    ((is_mode s <? CHECK) || negb (flush =? Z_FINISH)))
                then updatewindow s (ic_outbuf c) (ic_next_out c) (wrap32 (ir_out r - ic_avail_out c))
                else sret (Some s)) ;
      match so with
      | None => let s := iset_mode s MEM in sret (s, zret_of_icall c Z_MEM_ERROR)
      | Some s =>
          let in_ := wrap32 (ir_in r - ic_avail_in c) in
          let out := wrap32 (ir_out r - ic_avail_out c) in
          let c := icset_total_in c (wrap64 (ic_total_in c + in_)) in
          let c := icset_total_out c (wrap64 (ic_total_out c + out)) in
          let s := iset_total s (wrap64 (is_total s + out)) in
          let '(s, c) :=
            if negb (Z.land (is_wrap s) 4 =? 0) && negb (out =? 0) then
              let v := UPDATE_CHECK_bytes s (is_check s)
                         (arr_slice (ic_outbuf c) (ic_next_out c - out) out) in
              (iset_check s v, icset_adler c v)
            else (s, c) in
          let c := icset_data_type c
                     (is_bits s + (if negb (is_last s =? 0) then 64 else 0) +
                      (if is_mode s =? TYPE then 128 else 0) +
                      (if (is_mode s =? LEN_) || (is_mode s =? COPY_) then 256 else 0)) in
          let ret := if (((in_ =? 0) && (out =? 0)) || (flush =? Z_FINISH)) && (ir_ret r =? Z_OK)
                     then Z_BUF_ERROR else ir_ret r in
          sret (s, zret_of_icall c ret)
      end.

    Definition inflate_m (s : inflate_state) (zc : ZCall) (flush : Z) : SM St (inflate_state * ZRet) :=
      let c := icall_of_zcall zc in
      if inflateStateCheck s then sret (s, zret_of_icall c Z_STREAM_ERROR)
      else
        let s := if is_mode s =? TYPE then iset_mode s TYPEDO else s in
        let w := mkW s c (mkIR 0 0 0 0 0 0 0 0 Z_OK) in
        let w := LOAD w in
        let w := wset_r w (irset_ret (irset_out (irset_in (w_r w) (ir_have (w_r w))) (ir_left (w_r w))) Z_OK) in
        let '(stop, w) := inf_loop iv flush w in
        match stop with
        | SRet rc => sret (w_s w, zret_of_icall (w_c w) rc)
        | SLeave => inf_leave flush w
        end.


    Definition inflateEnd_m (s : inflate_state) (zc : ZCall) : SM St ZRet :=
      if inflateStateCheck s then sret (zret0 (zc_strm zc) Z_STREAM_ERROR)
      else
        (match is_window_blk s with Some b => zfree hooks b | None => sret tt end) ;;
        zfree hooks (is_self_blk s) ;;
        sret (zret0 (zc_strm zc) Z_OK).


    Definition inflateSetDictionary_m (s : inflate_state) (zc : ZCall) (dictionary : list Z)
      : SM St (inflate_state * ZRet) :=
      let z := zc_strm zc in
      if inflateStateCheck s then sret (s, zret0 z Z_STREAM_ERROR)
      else if negb (is_wrap s =? 0) && negb (is_mode s =? DICT) then sret (s, zret0 z Z_STREAM_ERROR)
      else
        let bad := if is_mode s =? DICT then
                     let dictid := iadler32_upd iadler32_init dictionary in
                     negb (dictid =? is_check s)
                   else false in
        if bad then sret (s, zret0 z Z_DATA_ERROR)
        else
          do so <- updatewindow s (arr_of_list dictionary) (zlength dictionary) (zlength dictionary) ;
          match so with
          | None => sret (iset_mode s MEM, zret0 z Z_MEM_ERROR)
          | Some s => sret (iset_havedict s 1, zret0 z Z_OK)
          end.
  End WithHooks.
End WithVariant.

