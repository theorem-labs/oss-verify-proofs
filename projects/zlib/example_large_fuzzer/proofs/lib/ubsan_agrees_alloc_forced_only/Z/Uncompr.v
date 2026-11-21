(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
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

    (* zlib 1.4 (uncompr.c 1.4 l.29-82, uncompress2_z and its uLong wrapper):
       - no probe byte: a zero destLen runs inflate with no room (1.3.1 decoded one byte into a local buffer);
       - on an inflateInit failure *destLen is untouched (1.3.1 had already zeroed it when destLen > 0);
       - the result: len := unused input, left := unused room, *sourceLen -= len, *destLen -= left;
       - O7: Z_BUF_ERROR becomes Z_DATA_ERROR iff all input was consumed (1.3.1: iff room was left).
       The NULL-pointer checks (Z_STREAM_ERROR) are outside this list-level model: callers pass real buffers. *)
    let len := sourceLen in
    let left := destLen in

    do ri <- inflateInit2_m iv hooks (mkZCall [] 0 zstrm0) DEF_WBITS ;
    let '(os, r) := ri in
    match os with
    | None => sret (zr_rc r, [], destLen, sourceLen)
    | Some s =>

        let x0 := mkU2 s (zr_strm r) len left 0 0 0 [] Z_OK in
        do x <- uncompress2_loop source (destLen + sourceLen + 4) x0 ;

        let len' := wrap64 (u2_len x + u2_avail_in x) in
        let left' := wrap64 (u2_left x + u2_avail_out x) in
        let sourceLen_out := wrap64 (sourceLen - len') in
        let destLen_out := wrap64 (destLen - left') in

        do _ <- inflateEnd_m hooks (u2_s x) (mkZCall [] 0 (u2_z x)) ;

        let err := u2_err x in
        let rc := if err =? Z_STREAM_END then Z_OK
                  else if err =? Z_NEED_DICT then Z_DATA_ERROR
                  else if (err =? Z_BUF_ERROR) && (len' =? 0) then Z_DATA_ERROR
                  else err in
        sret (rc, List.rev_append (u2_out_rev x) [], destLen_out, sourceLen_out)
    end.
End Uncompress2.
