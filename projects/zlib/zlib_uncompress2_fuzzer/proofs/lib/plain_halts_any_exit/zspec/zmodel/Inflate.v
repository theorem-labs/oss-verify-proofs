(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import Prog ZIface InflateState Inftrees InflateFast InflateArms.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.




Section WithVariant.
  Variable iv : ivariant.




  Section WithHooks.
    Context {St : Type}.
    Variable hooks : zhooks St.





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





  End WithHooks.
End WithVariant.

