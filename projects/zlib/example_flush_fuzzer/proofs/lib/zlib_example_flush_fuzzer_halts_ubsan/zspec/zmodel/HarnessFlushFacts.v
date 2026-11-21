(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface
  DeflateState DeflateLz DeflateBlk Deflate InflateState Inflate InflateSync HarnessKit HarnessFlush HarnessFacts
  HarnessSmallStages HarnessStmt DeflInitLib HarnessSmallFacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.

Definition cerr (msg : string) (rc : Z) : list hevent :=
  if rc =? Z_OK then [] else [HEerr (check_err_line msg rc)].


Definition tflush_body (s : deflate_state) (z : zstrm) (data : arr) (dataLen : Z) (compr : arr) (comprLen : Z)
  : (arr * Z) * (list hevent * bool) :=
  let len := wrap32 dataLen in
  let c := mkCZS 0 3 0 (wrap32 comprLen) z in
  let '(zc, b1) := cz_call c data in
  let '(s, r1) := deflate_m s zc Z_FULL_FLUSH in
  let '(c, compr, b2) := cz_ret c r1 compr in
  let ev1 := cerr "deflate flush 1" (zr_rc r1) in
  if negb (zr_rc r1 =? Z_OK) then ((compr, comprLen), (ev1, b1 || b2))
  else
    let compr := arr_set compr 3 (wrap8 (arr_get compr 3 + 1)) in
    let b0 := arr_len compr <=? 3 in
    let c := cz_set_avail_in c (wrap32 (len - 3)) in
    let '(zc, b3) := cz_call c data in
    let '(s, r2) := deflate_m s zc Z_FINISH in
    let '(c, compr, b4) := cz_ret c r2 compr in
    let ev2 := if negb (zr_rc r2 =? Z_STREAM_END) then cerr "deflate flush 2" (zr_rc r2) else [] in
    let bad := b1 || b2 || b0 || (b3 || b4) in
    if negb (zr_rc r2 =? Z_STREAM_END) && negb (zr_rc r2 =? Z_OK) then ((compr, comprLen), (ev2 ++ ev1, bad))
    else
      let '(rc3, ev3) := dend_p s in
      let ev4 := cerr "deflateEnd" rc3 in
      if negb (rc3 =? Z_OK) then ((compr, comprLen), (ev4 ++ ev3 ++ ev2 ++ ev1, bad))
      else ((compr, zs_total_out (cz_z c)), (ev4 ++ ev3 ++ ev2 ++ ev1, bad)).

Definition tflush_p (o : horacle) (n : Z) (data : arr) (dataLen : Z) (compr : arr) (comprLen : Z)
  : (arr * Z) * (Z * list hevent * bool) :=
  let zs := ho_zs o 0 in
  let '(res, ne) := dinit_p o n (mkZCall [] 0 zs) Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY in
  let '(os, r) := res in
  let '(n1, evs1) := ne in
  let evs2 := cerr "deflateInit" (zr_rc r) ++ evs1 in
  match os, negb (zr_rc r =? Z_OK) with
  | Some s, false =>
      let '(x, lb) := tflush_body s (zr_strm r) data dataLen compr comprLen in
      (x, (n1, fst lb ++ evs2, snd lb))
  | _, _ => ((compr, comprLen), (n1, evs2, false))
  end.








Definition hstep_n (n : Z) (asked : option Z) : Z := match asked with Some _ => n + 1 | None => n end.
Definition hstep_ev (o : horacle) (n : Z) (asked : option Z) : list hevent :=
  match asked with Some size => [HEmalloc size (hgrant o n)] | None => [] end.

Definition tsync_body (o : horacle) (n : Z) (s : inflate_state) (z : zstrm) (compr : arr) (comprLen : Z) (uncompr : arr) (uncomprLen : Z)
  : arr * (Z * list hevent * bool) :=
  let c := mkCZS 0 2 0 (wrap32 uncomprLen) z in
  let '(zc, b1) := cz_call c compr in
  let '(res1, asked1) := inflate_p ivar_ref (hans o n) s zc Z_NO_FLUSH in
  let '(s, r1) := res1 in
  let n1 := hstep_n n asked1 in let evA := hstep_ev o n asked1 in
  let '(c, uncompr, b2) := cz_ret c r1 uncompr in
  let bad1 := b1 || b2 in
  let ev1 := cerr "inflate" (zr_rc r1) ++ evA in
  if negb (zr_rc r1 =? Z_OK) then (uncompr, (n1, ev1, bad1))
  else
    let c := cz_set_avail_in c (wrap32 (wrap32 comprLen - 2)) in
    let '(zc, b3) := cz_call c compr in
    let '(s, r2) := inflateSync_m ivar_ref s zc in
    let '(c, uncompr, b4) := cz_ret c r2 uncompr in
    let bad2 := bad1 || (b3 || b4) in
    let ev2 := cerr "inflateSync" (zr_rc r2) ++ ev1 in
    if negb (zr_rc r2 =? Z_OK) then (uncompr, (n1, ev2, bad2))
    else
      let '(zc, b5) := cz_call c compr in
      let '(res3, asked3) := inflate_p ivar_ref (hans o n1) s zc Z_FINISH in
      let '(s, r3) := res3 in
      let n2 := hstep_n n1 asked3 in let evB := hstep_ev o n1 asked3 in
      let '(c, uncompr, b6) := cz_ret c r3 uncompr in
      let bad3 := bad2 || (b5 || b6) in
      let ev3 := evB ++ ev2 in
      if negb (zr_rc r3 =? Z_DATA_ERROR) && negb (zr_rc r3 =? Z_STREAM_END)
      then (uncompr, (n2, HEerr (str_bytes "inflate should report DATA_ERROR or Z_STREAM_END" ++ [10]) :: ev3, bad3))
      else
        let '(rcE, evE) := iend_p s in
        (uncompr, (n2, cerr "inflateEnd" rcE ++ evE ++ ev3, bad3)).

Definition tsync_p (o : horacle) (n : Z) (compr : arr) (comprLen : Z) (uncompr : arr) (uncomprLen : Z)
  : arr * (Z * list hevent * bool) :=
  let zs := ho_zs o 1 in
  let ev0 := HEmalloc (mul32 1 SIZEOF_inflate_state) (hgrant o n) in
  match hgrant o n with
  | None => (uncompr, (n + 1, cerr "inflateInit" Z_MEM_ERROR ++ [ev0], false))
  | Some k =>
      let '(s, z) := iinit_state ivar_ref (ho_garb o k) (Z.to_N k) (zs_set_msg MSG_NULL zs) in
      let '(u, t) := tsync_body o (n + 1) s z compr comprLen uncompr uncomprLen in
      let '(ne, b) := t in let '(n2, evs) := ne in
      (u, (n2, evs ++ [ev0], b))
  end.


Ltac close_run := unfold sret; cbn [mbind fst snd]; repeat (rewrite <- app_assoc); cbn [app]; repeat (rewrite <- app_assoc); rewrite ?orb_assoc; reflexivity.



