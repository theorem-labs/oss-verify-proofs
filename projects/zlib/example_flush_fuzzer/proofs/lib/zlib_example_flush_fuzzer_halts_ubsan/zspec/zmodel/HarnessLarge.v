(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Bool String.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface
  DeflateState Deflate DeflateParams InflateState Inflate HarnessKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.


Definition test_large_deflate (compr : arr) (comprLen : Z) (uncompr : arr) (uncomprLen : Z)
           (diff : Z) : SM hst (arr * Z) :=
  do zs <- h_zs 0 ;
  do ri <- deflateInit2_m hz_hooks (mkZCall [] 0 zs)
             Z_BEST_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY ;
  let '(os, r) := ri in
  do ret <- check_err (zr_rc r) "deflateInit" ;
  match os, ret with
  | Some s, false =>
      let c := mkCZS 0 (wrap32 uncomprLen) 0 (wrap32 comprLen) (zr_strm r) in
      let '(zc, b1) := cz_call c uncompr in
      let '(s, r1) := deflate_m s zc Z_NO_FLUSH in
      let '(c, compr, b2) := cz_ret c r1 compr in
      h_bad (b1 || b2) ;;
      do ret <- check_err (zr_rc r1) "deflate large 1" ;
      if ret then sret (compr, diff)
      else if negb (Z.eqb (cz_avail_in c) 0)
      then h_err (str_bytes "deflate not greedy" ++ [10]) ;; sret (compr, diff)
      else
        let '(zc, b3) := cz_call c uncompr in
        let '(s, rp) := deflateParams_m s zc Z_NO_COMPRESSION Z_DEFAULT_STRATEGY in
        let '(c, compr, b4) := cz_ret c rp compr in
        h_bad (b3 || b4) ;;
        let diff := wrap32 (cz_next_out c) in
        let c := cz_set_in c 0 diff in
        let '(zc, b5) := cz_call c compr in
        let '(s, r2) := deflate_m s zc Z_NO_FLUSH in
        let '(c, compr, b6) := cz_ret c r2 compr in
        h_bad (b5 || b6) ;;
        do ret <- check_err (zr_rc r2) "deflate large 2" ;
        if ret then sret (compr, diff)
        else
          let '(zc, b7) := cz_call c compr in
          let '(s, rq) := deflateParams_m s zc Z_BEST_COMPRESSION Z_FILTERED in
          let '(c, compr, b8) := cz_ret c rq compr in
          h_bad (b7 || b8) ;;
          let c := cz_set_in c 0 (wrap32 uncomprLen) in
          let '(zc, b9) := cz_call c uncompr in
          let '(s, r3) := deflate_m s zc Z_NO_FLUSH in
          let '(c, compr, b10) := cz_ret c r3 compr in
          h_bad (b9 || b10) ;;
          do ret <- check_err (zr_rc r3) "deflate large 3" ;
          if ret then sret (compr, diff)
          else
            let '(zc, b11) := cz_call c uncompr in
            let '(s, r4) := deflate_m s zc Z_FINISH in
            let '(c, compr, b12) := cz_ret c r4 compr in
            h_bad (b11 || b12) ;;
            if negb (Z.eqb (zr_rc r4) Z_STREAM_END)
            then h_err (str_bytes "deflate large should report Z_STREAM_END" ++ [10]) ;; sret (compr, diff)
            else
              do re <- deflateEnd_m hz_hooks s (mkZCall [] 0 (cz_z c)) ;
              do _ <- check_err (zr_rc re) "deflateEnd" ;
              sret (compr, diff)
  | _, _ => sret (compr, diff)
  end.


Fixpoint large_inflate_loop (fuel : nat) (s : inflate_state) (c : czs) (compr : arr)
         (uncompr : arr) (uncomprLen : Z) : SM hst (inflate_state * czs * arr * option bool) :=
  match fuel with
  | O => h_bad true ;; sret (s, c, uncompr, None)
  | S f =>
      let c := cz_set_out c 0 (wrap32 uncomprLen) in
      let '(zc, b1) := cz_call c compr in
      do x <- inflate_m ivar_ref hz_hooks s zc Z_NO_FLUSH ;
      let '(s, r) := x in
      let '(c, uncompr, b2) := cz_ret c r uncompr in
      h_bad (b1 || b2) ;;
      if Z.eqb (zr_rc r) Z_STREAM_END then sret (s, c, uncompr, Some false)
      else
        do ret <- check_err (zr_rc r) "large inflate" ;
        if ret then sret (s, c, uncompr, Some true)
        else large_inflate_loop f s c compr uncompr uncomprLen
  end.

Definition test_large_inflate (compr : arr) (comprLen : Z) (uncompr : arr) (uncomprLen : Z)
           (diff : Z) : SM hst arr :=
  do zs <- h_zs 1 ;
  do ri <- inflateInit2_m ivar_ref hz_hooks (mkZCall [] 0 zs) DEF_WBITS ;
  let '(os, r) := ri in
  do ret <- check_err (zr_rc r) "inflateInit" ;
  match os, ret with
  | Some s, false =>
      let c := mkCZS 0 (wrap32 comprLen) 0 0 (zr_strm r) in
      do x <- large_inflate_loop (Z.to_nat (64 * (comprLen + 8))) s c compr uncompr uncomprLen ;
      let '(s, c, uncompr, stop) := x in
      match stop with
      | Some false =>
          do re <- inflateEnd_m hz_hooks s (mkZCall [] 0 (cz_z c)) ;
          do ret <- check_err (zr_rc re) "inflateEnd" ;
          if ret then sret uncompr
          else if negb (Z.eqb (zs_total_out (cz_z c)) (wrap64 (2 * uncomprLen + diff)))
          then h_err (str_bytes "bad large inflate: " ++ zdec (zs_total_out (cz_z c)) ++ [10]) ;;
               sret uncompr
          else sret uncompr
      | _ => sret uncompr
      end
  | _, _ => sret uncompr
  end.

