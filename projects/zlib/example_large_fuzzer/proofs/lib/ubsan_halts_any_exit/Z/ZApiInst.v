(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require ZApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState Inftrees InflateFast InflateArms Inflate HarnessSmall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record dstream : Type := mkDZ { dz_s : deflate_state; dz_z : zstrm }.

Definition dinit0 : option (option deflate_state * ZRet) := dinit_run (dchs (fun _ => g0)) zstrm0.
Definition ds_dummy : deflate_state := ds_of_oracle g0 0%N (cstrm_of_call (zc_none zstrm0)).
Definition ds0 : deflate_state := match dinit0 with Some (Some s, _) => s | _ => ds_dummy end.
Definition dz0 : zstrm := match dinit0 with Some (_, zr) => zr_strm zr | None => zstrm0 end.

Definition zd_init : dstream := mkDZ ds0 dz0.

Definition zd_zcall (d : list Z) (x : dstream) (ain aout : Z) : ZCall :=
  mkZCall (zfirstn ain (zskipn (zs_total_in (dz_z x)) d)) aout (dz_z x).

Definition zd_deflate (d : list Z) (x : dstream) (ain aout flush : Z) : dstream * Z * Z * list Z * Z :=
  let zc := zd_zcall d x ain aout in
  let '(s', zr) := deflate_m (dz_s x) zc flush in
  (mkDZ s' (zr_strm zr), zlength (zc_input zc) - zr_consumed zr, aout - zlength (zr_output zr), zr_output zr, zr_rc zr).

Record istream : Type := mkIZ { iz_s : inflate_state; iz_z : zstrm }.

Definition iinit0 : option (option inflate_state * ZRet) := iinit_run [Some (5%N, g0)] zstrm0.
Definition is_dummy : inflate_state := is_of_oracle (iv_lay ivar_ref) g0 0%N.
Definition is0 : inflate_state := match iinit0 with Some (Some s, _) => s | _ => is_dummy end.
Definition iz0 : zstrm := match iinit0 with Some (_, zr) => zr_strm zr | None => zstrm0 end.

Definition zi_init : istream := mkIZ is0 iz0.

Definition zi_zcall (c : list Z) (x : istream) (ain aout : Z) : ZCall :=
  mkZCall (zfirstn ain (zskipn (zs_total_in (iz_z x)) c)) aout (iz_z x).

Definition wans (ok : bool) : option (blk * (Z -> Z)) := if ok then Some (6%N, g0) else None.

Definition zi_inflate (c : list Z) (x : istream) (ain aout : Z) (ok : bool) : istream * Z * Z * list Z * Z :=
  let zc := zi_zcall c x ain aout in
  let '((s', zr), _) := inflate_p (wans ok) (iz_s x) zc Z_NO_FLUSH in
  (mkIZ s' (zr_strm zr), zlength (zc_input zc) - zr_consumed zr, aout - zlength (zr_output zr), zr_output zr, zr_rc zr).

Definition zi_wants_window (c : list Z) (x : istream) : bool :=
  snd (inflate_p (wans true) (iz_s x) (zi_zcall c x 1 1) Z_NO_FLUSH).

Definition zinst : ZApi.zapi :=
  ZApi.mkZapi dstream istream compressBound_m
    5968 65536 65536 65536 65536 7176 32768
    zd_init (fun x => zs_total_in (dz_z x)) (fun x => zs_total_out (dz_z x)) zd_deflate (fun x => dend_rc (dz_s x))
    zi_init (fun x => zs_total_in (iz_z x)) (fun x => zs_total_out (iz_z x)) zi_wants_window zi_inflate (fun x => iend_rc (iz_s x)).
