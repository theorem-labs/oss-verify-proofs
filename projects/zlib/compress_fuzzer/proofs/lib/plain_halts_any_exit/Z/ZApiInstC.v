(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require ZApiC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState Inftrees InflateFast InflateArms Inflate HarnessSmall ZApiInst HarnessCompress.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition zdc_init (level : Z) : dstream := mkDZ (dsC level) (dzC level).

Definition zdc_deflate (inp : list Z) (x : dstream) (aout flush : Z) : dstream * Z * list Z * Z :=
  let '(s', zr) := deflate_m (dz_s x) (mkZCall inp aout (dz_z x)) flush in
  (mkDZ s' (zr_strm zr), zr_consumed zr, zr_output zr, zr_rc zr).

Definition zic_inflate (inp : list Z) (x : istream) (aout : Z) (ok : bool) : istream * Z * list Z * Z :=
  let '(r, _) := inflate_p (wans ok) (iz_s x) (mkZCall inp aout (iz_z x)) Z_NO_FLUSH in
  let '(s', zr) := r in
  (mkIZ s' (zr_strm zr), zr_consumed zr, zr_output zr, zr_rc zr).

Definition zic_wants_window (inp : list Z) (x : istream) (aout : Z) : bool :=
  snd (inflate_p (wans true) (iz_s x) (mkZCall inp aout (iz_z x)) Z_NO_FLUSH).

Definition zinstC : ZApiC.zapiC :=
  ZApiC.mkZapiC dstream istream compressBound_m
    5968 65536 65536 65536 65536 7176 32768
    zdc_init (fun x => zs_total_out (dz_z x)) zdc_deflate (fun x => dend_rc (dz_s x))
    zi_init (fun x => zs_total_in (iz_z x)) (fun x => zs_total_out (iz_z x)) zic_wants_window zic_inflate (fun x => iend_rc (iz_s x)).
