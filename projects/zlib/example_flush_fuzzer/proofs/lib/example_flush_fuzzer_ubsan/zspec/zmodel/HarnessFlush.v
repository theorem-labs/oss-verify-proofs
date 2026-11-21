(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Bool String.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface
  DeflateState Deflate InflateState Inflate InflateSync HarnessKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.


Definition test_flush (data : arr) (dataLen : Z) (compr : arr) (comprLen : Z)
  : SM hst (arr * Z) :=
  do zs <- h_zs 0 ;
  let len := wrap32 dataLen in
  do ri <- deflateInit2_m hz_hooks (mkZCall [] 0 zs)
             Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY ;
  let '(os, r) := ri in
  do ret <- check_err (zr_rc r) "deflateInit" ;
  match os, ret with
  | Some s, false =>
      let c := mkCZS 0 3 0 (wrap32 comprLen) (zr_strm r) in
      let '(zc, b1) := cz_call c data in
      let '(s, r1) := deflate_m s zc Z_FULL_FLUSH in
      let '(c, compr, b2) := cz_ret c r1 compr in
      h_bad (b1 || b2) ;;
      do ret <- check_err (zr_rc r1) "deflate flush 1" ;
      if ret then sret (compr, comprLen)
      else
        let compr := arr_set compr 3 (wrap8 (arr_get compr 3 + 1)) in
        do _ <- h_bad (arr_len compr <=? 3) ;
        let c := cz_set_avail_in c (wrap32 (len - 3)) in
        let '(zc, b3) := cz_call c data in
        let '(s, r2) := deflate_m s zc Z_FINISH in
        let '(c, compr, b4) := cz_ret c r2 compr in
        h_bad (b3 || b4) ;;
        do ret <- (if negb (Z.eqb (zr_rc r2) Z_STREAM_END)
                   then check_err (zr_rc r2) "deflate flush 2" else sret false) ;
        if ret then sret (compr, comprLen)
        else
          do re <- deflateEnd_m hz_hooks s (mkZCall [] 0 (cz_z c)) ;
          do ret <- check_err (zr_rc re) "deflateEnd" ;
          if ret then sret (compr, comprLen)
          else sret (compr, zs_total_out (cz_z c))
  | _, _ => sret (compr, comprLen)
  end.


Definition test_sync (compr : arr) (comprLen : Z) (uncompr : arr) (uncomprLen : Z)
  : SM hst arr :=
  do zs <- h_zs 1 ;
  do ri <- inflateInit2_m ivar_ref hz_hooks (mkZCall [] 0 zs) DEF_WBITS ;
  let '(os, r) := ri in
  do ret <- check_err (zr_rc r) "inflateInit" ;
  match os, ret with
  | Some s, false =>
      let c := mkCZS 0 2 0 (wrap32 uncomprLen) (zr_strm r) in
      let '(zc, b1) := cz_call c compr in
      do x <- inflate_m ivar_ref hz_hooks s zc Z_NO_FLUSH ;
      let '(s, r1) := x in
      let '(c, uncompr, b2) := cz_ret c r1 uncompr in
      h_bad (b1 || b2) ;;
      do ret <- check_err (zr_rc r1) "inflate" ;
      if ret then sret uncompr
      else
        let c := cz_set_avail_in c (wrap32 (wrap32 comprLen - 2)) in
        let '(zc, b3) := cz_call c compr in
        let '(s, r2) := inflateSync_m ivar_ref s zc in
        let '(c, uncompr, b4) := cz_ret c r2 uncompr in
        h_bad (b3 || b4) ;;
        do ret <- check_err (zr_rc r2) "inflateSync" ;
        if ret then sret uncompr
        else
          let '(zc, b5) := cz_call c compr in
          do y <- inflate_m ivar_ref hz_hooks s zc Z_FINISH ;
          let '(s, r3) := y in
          let '(c, uncompr, b6) := cz_ret c r3 uncompr in
          h_bad (b5 || b6) ;;
          if negb (Z.eqb (zr_rc r3) Z_DATA_ERROR) && negb (Z.eqb (zr_rc r3) Z_STREAM_END)
          then h_err (str_bytes "inflate should report DATA_ERROR or Z_STREAM_END" ++ [10]) ;;
               sret uncompr
          else
            do re <- inflateEnd_m hz_hooks s (mkZCall [] 0 (cz_z c)) ;
            do _ <- check_err (zr_rc re) "inflateEnd" ;
            sret uncompr
  | _, _ => sret uncompr
  end.

