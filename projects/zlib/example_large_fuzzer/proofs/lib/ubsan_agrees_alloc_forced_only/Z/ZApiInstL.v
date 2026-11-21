(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require ZApiL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateParams.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState Inftrees InflateFast InflateArms Inflate HarnessSmall HarnessLarge ZApiInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dinit9 : option (option deflate_state * ZRet) := dinit9_run (dchs (fun _ => g0)) zstrm0.
Definition ds9 : deflate_state := match dinit9 with Some (Some s, _) => s | _ => ds_dummy end.
Definition dz9 : zstrm := match dinit9 with Some (_, zr) => zr_strm zr | None => zstrm0 end.
Definition zdl_init9 : dstream := mkDZ ds9 dz9.

Definition zdl_deflate (inp : list Z) (x : dstream) (aout flush : Z) : dstream * Z * list Z * Z :=
  let '(s', zr) := deflate_m (dz_s x) (mkZCall inp aout (dz_z x)) flush in
  (mkDZ s' (zr_strm zr), zr_consumed zr, zr_output zr, zr_rc zr).

Definition zdl_params (inp : list Z) (x : dstream) (aout level strategy : Z) : dstream * Z * list Z * Z :=
  let '(s', zr) := deflateParams_m (dz_s x) (mkZCall inp aout (dz_z x)) level strategy in
  (mkDZ s' (zr_strm zr), zr_consumed zr, zr_output zr, zr_rc zr).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zil_inflate (inp : list Z) (x : istream) (aout : Z) (ok : bool) : istream * Z * list Z * Z :=
  let '(r, _) := inflate_p (wans ok) (iz_s x) (mkZCall inp aout (iz_z x)) Z_NO_FLUSH in
  let '(s', zr) := r in
  (mkIZ s' (zr_strm zr), zr_consumed zr, zr_output zr, zr_rc zr).

Definition zil_wants_window (inp : list Z) (x : istream) (aout : Z) : bool :=
  snd (inflate_p (wans true) (iz_s x) (mkZCall inp aout (iz_z x)) Z_NO_FLUSH).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zinstL : ZApiL.zapiL :=
  ZApiL.mkZapiL dstream istream
    5968 65536 65536 65536 65536 7176 32768
    zdl_init9 (fun x => zs_total_out (dz_z x)) zdl_deflate zdl_params (fun x => dend_rc (dz_s x))
    zi_init (fun x => zs_total_in (iz_z x)) (fun x => zs_total_out (iz_z x)) zil_wants_window zil_inflate (fun x => iend_rc (iz_s x)).
