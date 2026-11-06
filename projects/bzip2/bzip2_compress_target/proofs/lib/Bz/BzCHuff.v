(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition weightof (zz : Z) : Z := Z.land zz 4294967040.   (* [comment removed for export] *)
Definition depthof (zz : Z) : Z := Z.land zz 255.
Definition addweights (zw1 zw2 : Z) : Z :=
  Z.lor (weightof zw1 + weightof zw2) (1 + Z.max (depthof zw1) (depthof zw2)).

(* [comment removed for export] *)
Fixpoint upheap_loop (fuel : nat) (heap weight : zarr) (zz tmp : Z) : zarr * Z :=
  match fuel with
  | O => (heap, zz)
  | S f =>
      if zget weight tmp <? zget weight (zget heap (Z.shiftr zz 1))
      then upheap_loop f (zset heap zz (zget heap (Z.shiftr zz 1))) weight (Z.shiftr zz 1) tmp
      else (heap, zz)
  end.
Definition upheap (heap weight : zarr) (z : Z) : zarr :=
  let tmp := zget heap z in
  let '(h, zz) := upheap_loop 20%nat heap weight z tmp in
  zset h zz tmp.

(* [comment removed for export] *)
Fixpoint downheap_loop (fuel : nat) (heap weight : zarr) (nHeap zz tmp : Z) : zarr * Z :=
  match fuel with
  | O => (heap, zz)
  | S f =>
      let yy := Z.shiftl zz 1 in
      if nHeap <? yy then (heap, zz) else
      let yy := if (yy <? nHeap) && (zget weight (zget heap (yy + 1)) <? zget weight (zget heap yy)) then yy + 1 else yy in
      if zget weight tmp <? zget weight (zget heap yy) then (heap, zz)
      else downheap_loop f (zset heap zz (zget heap yy)) weight nHeap yy tmp
  end.
Definition downheap (heap weight : zarr) (nHeap z : Z) : zarr :=
  let tmp := zget heap z in
  let '(h, zz) := downheap_loop 20%nat heap weight nHeap z tmp in
  zset h zz tmp.

(* [comment removed for export] *)
Fixpoint hm_winit (n : nat) (weight freq : zarr) (fb i : Z) : zarr :=
  match n with
  | O => weight
  | S n' => let fi := zget freq (fb + i) in
            hm_winit n' (zset weight (i + 1) (Z.shiftl (if fi =? 0 then 1 else fi) 8)) freq fb (i + 1)
  end.

(* [comment removed for export] *)
Fixpoint hm_fill (n : nat) (heap weight parent : zarr) (nHeap i : Z) : zarr * zarr * Z :=
  match n with
  | O => (heap, parent, nHeap)
  | S n' =>
      let parent := zset parent i (-1) in
      let nHeap := nHeap + 1 in
      let heap := zset heap nHeap i in
      let heap := upheap heap weight nHeap in
      hm_fill n' heap weight parent nHeap (i + 1)
  end.

(* [comment removed for export] *)
Record hms := HMS { hm_heap : zarr; hm_weight : zarr; hm_parent : zarr; hm_nHeap : Z; hm_nNodes : Z }.
Definition hm_combine_iter (s : hms) : hms :=
  let heap := hm_heap s in let weight := hm_weight s in let nHeap := hm_nHeap s in
  let n1 := zget heap 1 in
  let heap := zset heap 1 (zget heap nHeap) in let nHeap := nHeap - 1 in
  let heap := downheap heap weight nHeap 1 in
  let n2 := zget heap 1 in
  let heap := zset heap 1 (zget heap nHeap) in let nHeap := nHeap - 1 in
  let heap := downheap heap weight nHeap 1 in
  let nNodes := hm_nNodes s + 1 in
  let parent := zset (zset (hm_parent s) n2 nNodes) n1 nNodes in
  let weight := zset weight nNodes (addweights (zget weight n1) (zget weight n2)) in
  let parent := zset parent nNodes (-1) in
  let nHeap := nHeap + 1 in
  let heap := zset heap nHeap nNodes in
  let heap := upheap heap weight nHeap in
  HMS heap weight parent nHeap nNodes.
Fixpoint hm_combine (fuel : nat) (s : hms) : hms :=
  match fuel with
  | O => s
  | S f => if 1 <? hm_nHeap s then hm_combine f (hm_combine_iter s) else s
  end.

(* [comment removed for export] *)
Fixpoint hm_depth (fuel : nat) (parent : zarr) (k j : Z) : Z :=
  match fuel with
  | O => j
  | S f => if 0 <=? zget parent k then hm_depth f parent (zget parent k) (j + 1) else j
  end.
Fixpoint hm_lens (n : nat) (len parent : zarr) (lb maxLen i : Z) (tooLong : bool) : zarr * bool :=
  match n with
  | O => (len, tooLong)
  | S n' => let j := hm_depth 600%nat parent i 0 in
            hm_lens n' (zset len (lb + i - 1) (j mod 256)) parent lb maxLen (i + 1) (tooLong || (maxLen <? j))
  end.

(* [comment removed for export] *)
Fixpoint hm_rescale (n : nat) (weight : zarr) (i : Z) : zarr :=
  match n with
  | O => weight
  | S n' => let j := Z.shiftr (zget weight i) 8 in let j := 1 + j / 2 in
            hm_rescale n' (zset weight i (Z.shiftl j 8)) (i + 1)
  end.

(* [comment removed for export] *)
Record hmst := HMST { hs_len : zarr; hs_heap : zarr; hs_weight : zarr; hs_parent : zarr; hs_done : bool }.
Definition hm_round (alphaSize maxLen lb : Z) (s : hmst) : hmst :=
  let heap := zset (hs_heap s) 0 0 in
  let weight := zset (hs_weight s) 0 0 in
  let parent := zset (hs_parent s) 0 (-2) in
  let '(heap, parent, nHeap) := hm_fill (Z.to_nat alphaSize) heap weight parent 0 1 in
  let c := hm_combine (Z.to_nat alphaSize) (HMS heap weight parent nHeap alphaSize) in
  let '(len, tooLong) := hm_lens (Z.to_nat alphaSize) (hs_len s) (hm_parent c) lb maxLen 1 false in
  if tooLong then HMST len (hm_heap c) (hm_rescale (Z.to_nat alphaSize) (hm_weight c) 1) (hm_parent c) false
  else HMST len (hm_heap c) (hm_weight c) (hm_parent c) true.
Fixpoint hm_rounds (fuel : nat) (alphaSize maxLen lb : Z) (s : hmst) : hmst :=
  match fuel with
  | O => s
  | S f => if hs_done s then s else hm_rounds f alphaSize maxLen lb (hm_round alphaSize maxLen lb s)
  end.

(* [comment removed for export] *)
Definition hbMakeCodeLengths (len freq heap0 weight0 parent0 : zarr) (lb fb alphaSize maxLen : Z) : hmst :=
  let weight := hm_winit (Z.to_nat alphaSize) weight0 freq fb 0 in
  hm_rounds 40%nat alphaSize maxLen lb (HMST len heap0 weight parent0 false).

(* [comment removed for export] *)
Fixpoint ha_inner (k : nat) (code len : zarr) (cb lb n i vec : Z) : zarr * Z :=
  match k with
  | O => (code, vec)
  | S k' => if zget len (lb + i) =? n
            then ha_inner k' (zset code (cb + i) vec) len cb lb n (i + 1) (vec + 1)
            else ha_inner k' code len cb lb n (i + 1) vec
  end.
Fixpoint ha_outer (k : nat) (code len : zarr) (cb lb alphaSize n vec : Z) : zarr * Z :=
  match k with
  | O => (code, vec)
  | S k' => let '(code, vec) := ha_inner (Z.to_nat alphaSize) code len cb lb n 0 vec in
            ha_outer k' code len cb lb alphaSize (n + 1) (Z.shiftl vec 1)
  end.
Definition hbAssignCodes (code len : zarr) (cb lb minLen maxLen alphaSize : Z) : zarr :=
  fst (ha_outer (Z.to_nat (maxLen - minLen + 1)) code len cb lb alphaSize minLen 0).
