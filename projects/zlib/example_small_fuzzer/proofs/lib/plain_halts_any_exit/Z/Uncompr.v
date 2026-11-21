(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.

Record u2st : Type := mkU2 {
  u2_s : inflate_state; u2_z : zstrm; u2_len : Z; u2_left : Z;
  u2_in_pos : Z; u2_avail_in : Z; u2_avail_out : Z; u2_out_rev : list Z; u2_err : Z }.

Definition U2_MAX : Z := 4294967295.

Section Uncompress2.
  Variable iv : ivariant.
  Context {St : Type}.
  Variable hooks : zhooks St.

  Definition uncompress2_body (source : list Z) (x : u2st) : SM St u2st :=
    let '(avail_out, lft) :=
      if u2_avail_out x =? 0 then
        let ao := if U2_MAX <? u2_left x then U2_MAX else wrap32 (u2_left x) in
        (ao, wrap64 (u2_left x - ao))
      else (u2_avail_out x, u2_left x) in
    let '(avail_in, len) :=
      if u2_avail_in x =? 0 then
        let ai := if U2_MAX <? u2_len x then U2_MAX else wrap32 (u2_len x) in
        (ai, wrap64 (u2_len x - ai))
      else (u2_avail_in x, u2_len x) in
    let zc := mkZCall (zfirstn avail_in (zskipn (u2_in_pos x) source)) avail_out (u2_z x) in
    do r <- inflate_m iv hooks (u2_s x) zc Z_NO_FLUSH ;
    let '(s, zr) := r in
    sret (mkU2 s (zr_strm zr) len lft (u2_in_pos x + zr_consumed zr)
               (wrap32 (avail_in - zr_consumed zr)) (wrap32 (avail_out - zlength (zr_output zr)))
               (List.rev_append (zr_output zr) (u2_out_rev x)) (zr_rc zr)).

  Definition uncompress2_loop (source : list Z) (fuel : Z) (x : u2st) : SM St u2st :=
    sloopZ fuel (fun x => do x' <- uncompress2_body source x ;
                          sret (u2_err x' =? Z_OK, x')) x.

  Definition uncompress2_m (destLen : Z) (source : list Z) (sourceLen : Z)
    : SM St (Z * list Z * Z * Z) :=
    let len := sourceLen in
    let tobuf := destLen =? 0 in
    let left := if tobuf then 1 else destLen in
    let destLen_out := 0 in
    do ri <- inflateInit2_m iv hooks (mkZCall [] 0 zstrm0) DEF_WBITS ;
    let '(os, r) := ri in
    match os with
    | None => sret (zr_rc r, [], destLen_out, sourceLen)
    | Some s =>
        let x0 := mkU2 s (zr_strm r) len left 0 0 0 [] Z_OK in
        do x <- uncompress2_loop source (destLen + sourceLen + 4) x0 ;
        let sourceLen_out := wrap64 (sourceLen - (u2_len x + u2_avail_in x)) in
        let '(destLen_out, lft) :=
          if negb tobuf then (zs_total_out (u2_z x), u2_left x)
          else if negb (zs_total_out (u2_z x) =? 0) && (u2_err x =? Z_BUF_ERROR) then (destLen_out, 1)
          else (destLen_out, u2_left x) in
        do _ <- inflateEnd_m hooks (u2_s x) (mkZCall [] 0 (u2_z x)) ;
        let err := u2_err x in
        let rc := if err =? Z_STREAM_END then Z_OK
                  else if err =? Z_NEED_DICT then Z_DATA_ERROR
                  else if (err =? Z_BUF_ERROR) && negb (wrap64 (lft + u2_avail_out x) =? 0) then Z_DATA_ERROR
                  else err in
        sret (rc, (if tobuf then [] else List.rev_append (u2_out_rev x) []), destLen_out, sourceLen_out)
    end.
End Uncompress2.
