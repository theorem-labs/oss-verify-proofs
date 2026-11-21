(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Bool String.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface
  DeflateState Deflate InflateState Inflate HarnessKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.

Inductive lexit : Type :=
| LX_cond
| LX_end
| LX_err (rc : Z)
| LX_fuel.


Fixpoint small_deflate_loop (fuel : nat) (s : deflate_state) (c : czs) (data : arr) (len : Z)
         (compr : arr) (comprLen : Z) : SM hst (deflate_state * czs * arr * lexit) :=
  match fuel with
  | O => h_bad true ;; sret (s, c, compr, LX_fuel)
  | S f =>
      if negb (Z.eqb (zs_total_in (cz_z c)) len) && Z.ltb (zs_total_out (cz_z c)) comprLen then
        let c := cz_set_avail_out (cz_set_avail_in c 1) 1 in
        let '(zc, b1) := cz_call c data in
        let '(s, r) := deflate_m s zc Z_NO_FLUSH in
        let '(c, compr, b2) := cz_ret c r compr in
        h_bad (b1 || b2) ;;
        do ret <- check_err (zr_rc r) "deflate small 1" ;
        if ret then sret (s, c, compr, LX_err (zr_rc r))
        else small_deflate_loop f s c data len compr comprLen
      else sret (s, c, compr, LX_cond)
  end.

Fixpoint small_finish_loop (fuel : nat) (s : deflate_state) (c : czs) (data : arr) (compr : arr)
  : SM hst (deflate_state * czs * arr * lexit) :=
  match fuel with
  | O => h_bad true ;; sret (s, c, compr, LX_fuel)
  | S f =>
      let c := cz_set_avail_out c 1 in
      let '(zc, b1) := cz_call c data in
      let '(s, r) := deflate_m s zc Z_FINISH in
      let '(c, compr, b2) := cz_ret c r compr in
      h_bad (b1 || b2) ;;
      if Z.eqb (zr_rc r) Z_STREAM_END then sret (s, c, compr, LX_end)
      else
        do ret <- check_err (zr_rc r) "deflate small 2" ;
        if ret then sret (s, c, compr, LX_err (zr_rc r)) else small_finish_loop f s c data compr
  end.

Definition test_deflate_body (s : deflate_state) (z : zstrm) (data : arr) (len : Z) (compr : arr) (comprLen : Z)
  : SM hst (arr * lexit) :=
  let c := mkCZS 0 0 0 0 z in
  do x <- small_deflate_loop (Z.to_nat (len + comprLen + 2)) s c data len compr comprLen ;
  let '(s, c, compr, stop) := x in
  match stop with
  | LX_cond =>
      do y <- small_finish_loop (Z.to_nat (comprLen + 2)) s c data compr ;
      let '(s, c, compr, stop2) := y in
      match stop2 with
      | LX_end =>
          do re <- deflateEnd_m hz_hooks s (mkZCall [] 0 (cz_z c)) ;
          do ret <- check_err (zr_rc re) "deflateEnd" ;
          sret (compr, if ret then LX_err (zr_rc re) else LX_end)
      | other => sret (compr, other)
      end
  | other => sret (compr, other)
  end.

Definition test_deflate (data : arr) (dataLen : Z) (compr : arr) (comprLen : Z) : SM hst arr :=
  do zs <- h_zs 0 ;
  let len := dataLen in
  do ri <- deflateInit2_m hz_hooks (mkZCall [] 0 zs)
             Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY ;
  let '(os, r) := ri in
  do ret <- check_err (zr_rc r) "deflateInit" ;
  match os, ret with
  | Some s, false => do x <- test_deflate_body s (zr_strm r) data len compr comprLen ; sret (fst x)
  | _, _ => sret compr
  end.


Fixpoint small_inflate_loop (fuel : nat) (s : inflate_state) (c : czs) (compr : arr) (comprLen : Z)
         (uncompr : arr) (uncomprLen : Z) : SM hst (inflate_state * czs * arr * lexit) :=
  match fuel with
  | O => h_bad true ;; sret (s, c, uncompr, LX_fuel)
  | S f =>
      if Z.ltb (zs_total_out (cz_z c)) uncomprLen && Z.ltb (zs_total_in (cz_z c)) comprLen then
        let c := cz_set_avail_out (cz_set_avail_in c 1) 1 in
        let '(zc, b1) := cz_call c compr in
        do x <- inflate_m ivar_ref hz_hooks s zc Z_NO_FLUSH ;
        let '(s, r) := x in
        let '(c, uncompr, b2) := cz_ret c r uncompr in
        h_bad (b1 || b2) ;;
        if Z.eqb (zr_rc r) Z_STREAM_END then sret (s, c, uncompr, LX_end)
        else
          do ret <- check_err (zr_rc r) "inflate" ;
          if ret then sret (s, c, uncompr, LX_err (zr_rc r))
          else small_inflate_loop f s c compr comprLen uncompr uncomprLen
      else sret (s, c, uncompr, LX_cond)
  end.

Definition test_inflate_body (s : inflate_state) (z : zstrm) (data : arr) (dataLen : Z)
           (compr : arr) (comprLen : Z) (uncompr : arr) (uncomprLen : Z) : SM hst (arr * lexit) :=
  let c := mkCZS 0 0 0 0 z in
  do x <- small_inflate_loop (Z.to_nat (uncomprLen + comprLen + 2)) s c compr comprLen uncompr uncomprLen ;
  let '(s, c, uncompr, stop) := x in
  match stop with
  | LX_err _ => sret (uncompr, stop)
  | _ =>
      do re <- inflateEnd_m hz_hooks s (mkZCall [] 0 (cz_z c)) ;
      do ret <- check_err (zr_rc re) "inflateEnd" ;
      if ret then sret (uncompr, stop)
      else if memcmp_ne uncompr data dataLen
           then h_err (str_bytes "bad inflate" ++ [10]) ;; sret (uncompr, stop)
           else sret (uncompr, stop)
  end.

Definition test_inflate (data : arr) (dataLen : Z) (compr : arr) (comprLen : Z)
           (uncompr : arr) (uncomprLen : Z) : SM hst arr :=
  do zs <- h_zs 1 ;
  do ri <- inflateInit2_m ivar_ref hz_hooks (mkZCall [] 0 zs) DEF_WBITS ;
  let '(os, r) := ri in
  do ret <- check_err (zr_rc r) "inflateInit" ;
  match os, ret with
  | Some s, false => do x <- test_inflate_body s (zr_strm r) data dataLen compr comprLen uncompr uncomprLen ; sret (fst x)
  | _, _ => sret uncompr
  end.

