(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ONES64 : Z := 0xffffffffffffffff.                (* [comment removed for export] *)
Definition M32    : Z := 0xffffffff.                        (* [comment removed for export] *)
Definition M128   : Z := 0x100000000000000000000000000000000. (* [comment removed for export] *)
Definition SIGN64 : Z := 0x8000000000000000.                (* [comment removed for export] *)

(* [comment removed for export] *)
Definition wrap64 (x : Z) : Z := Z.land x ONES64.
Lemma wrap64_mod : forall x, wrap64 x = x mod 2^64.
Proof. intro x. unfold wrap64. change ONES64 with (Z.ones 64). apply Z.land_ones. lia. Qed.
Lemma wrap64_range : forall x, 0 <= wrap64 x < 2^64.
Proof. intro x. rewrite wrap64_mod. apply Z.mod_pos_bound. lia. Qed.

Definition b2z (b : bool) : Z := if b then 1 else 0.       (* [comment removed for export] *)
Definition lo64 (x : Z) : Z := wrap64 x.                    (* [comment removed for export] *)
Definition hi64 (x : Z) : Z := wrap64 (Z.shiftr x 64).      (* [comment removed for export] *)
Definition mk128 (hi lo : Z) : Z := Z.lor (Z.shiftl hi 64) lo.  (* [comment removed for export] *)
Definition add64 (x y : Z) : Z := wrap64 (x + y).           (* [comment removed for export] *)
Definition sub64 (x y : Z) : Z := wrap64 (x - y).           (* [comment removed for export] *)
Definition mul64 (x y : Z) : Z := wrap64 (x * y).           (* [comment removed for export] *)
Definition mulhu (x y : Z) : Z := Z.shiftr (x * y) 64.      (* [comment removed for export] *)
Definition shl64 (x n : Z) : Z := wrap64 (Z.shiftl x n).    (* [comment removed for export] *)
Notation shr64 := Z.shiftr (only parsing).                  (* [comment removed for export] *)
Definition not64 (x : Z) : Z := Z.lxor x ONES64.            (* [comment removed for export] *)
Notation u64_of_s := wrap64 (only parsing).                 (* [comment removed for export] *)
Definition ltu64 (x y : Z) : Z := b2z (x <? y).             (* [comment removed for export] *)
Definition eqz64 (x : Z) : Z := b2z (x =? 0).               (* [comment removed for export] *)
Definition nez64 (x : Z) : Z := b2z (negb (x =? 0)).        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_neg64 (x : Z) : bool := negb (Z.shiftr x 63 =? 0).
(* [comment removed for export] *)
Definition lt_s64 (a b : Z) : bool := (Z.lxor a SIGN64) <? (Z.lxor b SIGN64).
(* [comment removed for export] *)
Definition sra63 (x : Z) : Z := if is_neg64 x then ONES64 else 0.
Notation smask64 := sra63 (only parsing).
(* [comment removed for export] *)
Definition zext32 (x : Z) : Z := Z.land x M32.
Definition sext32 (x : Z) : Z := sub64 (Z.lxor (Z.land x M32) 0x80000000) 0x80000000.
(* [comment removed for export] *)
Definition srliw (x k : Z) : Z := sext32 (Z.shiftr (Z.land x M32) k).

(* [comment removed for export] *)
Definition MASK48      : Z := 0x0000ffffffffffff.  (* [comment removed for export] *)
Definition MASKLO      : Z := 0xffffffffffffffff.  (* [comment removed for export] *)
Definition ABS_HI      : Z := 0x7fffffffffffffff.
Definition INF_HI      : Z := 0x7fff000000000000.
Definition QUIET_HI    : Z := 0x0000800000000000.  (* [comment removed for export] *)
Definition QNAN_HI     : Z := 0x7fff800000000000.  (* [comment removed for export] *)
Definition IMPLICIT_HI : Z := 0x0001000000000000.  (* [comment removed for export] *)
Definition IMPL3_HI    : Z := 0x0008000000000000.  (* [comment removed for export] *)
Definition SPEC_K      : Z := 0x8001000000000000.  (* [comment removed for export] *)
Definition HALF60      : Z := 0x0800000000000000.  (* [comment removed for export] *)
Definition DQUIET      : Z := 0x0008000000000000.  (* [comment removed for export] *)
Definition C_HW        : Z := 0x7504f33300000000.  (* [comment removed for export] *)
Definition X_ADJ       : Z := 0xffffffffffffc999.  (* [comment removed for export] *)
Definition EXPK        : Z := 0xffffffffffff8001.  (* [comment removed for export] *)
Definition EXPK2       : Z := 0xffffffffffff8002.

(* [comment removed for export] *)
Definition clz64_mirror (x : Z) : Z :=
  let x1 := Z.lor x  (shr64 x 1) in
  let x2 := Z.lor x1 (shr64 x1 2) in
  let x3 := Z.lor x2 (shr64 x2 4) in
  let x4 := Z.lor x3 (shr64 x3 8) in
  let x5 := Z.lor x4 (shr64 x4 16) in
  let x6 := Z.lor x5 (shr64 x5 32) in
  let y  := not64 x6 in
  let c1 := sub64 y (Z.land (shr64 y 1) 0x5555555555555555) in
  let c2 := add64 (Z.land c1 0x3333333333333333) (Z.land (shr64 c1 2) 0x3333333333333333) in
  let c3 := Z.land (add64 c2 (shr64 c2 4)) 0x0f0f0f0f0f0f0f0f in
  let c4 := shr64 (mul64 c3 0x0101010101010101) 56 in
  c4.

(* [comment removed for export] *)
Definition clz32_mirror (r : Z) : Z :=
  let x1 := Z.lor r  (srliw r 1) in
  let x2 := Z.lor x1 (srliw x1 2) in
  let x3 := Z.lor x2 (srliw x2 4) in
  let x4 := Z.lor x3 (srliw x3 8) in
  let x5 := Z.lor x4 (srliw x4 16) in
  let y  := not64 x5 in
  let c1 := sub64 y (Z.land (shr64 y 1) 0x55555555) in
  let c2 := add64 (Z.land c1 0x33333333) (Z.land (shr64 c1 2) 0x33333333) in
  let c3 := Z.land (add64 c2 (shr64 c2 4)) 0x0f0f0f0f in
  let c4 := srliw (mul64 c3 0x01010101) 24 in
  c4.

(* [comment removed for export] *)
Definition clz128_mirror (hi lo : Z) : Z :=
  let hz := b2z (hi =? 0) in
  let word := if hi =? 0 then lo else hi in
  Z.lor (clz64_mirror word) (Z.shiftl hz 6).

(* [comment removed for export] *)
Definition shl128_mirror (hi lo s : Z) : Z * Z :=
  let n := zext32 s in
  let d := sub64 n 64 in
  let nhi := if is_neg64 d
             then Z.lor (shl64 hi (Z.land s 63)) (shr64 (shr64 lo 1) (Z.land (not64 n) 63))
             else shl64 lo (Z.land n 63) in
  let nlo := Z.land (sra63 d) (shl64 lo (Z.land s 63)) in
  (nhi, nlo).

(* [comment removed for export] *)
Definition norm_denormal (sigHi sigLo : Z) : Z * Z * Z :=
  let clz := clz128_mirror sigHi sigLo in
  let sh := sub64 clz 15 in
  let '(hi, lo) := shl128_mirror sigHi sigLo sh in
  (hi, lo, clz).

(* [comment removed for export] *)
Definition normalize_mirror (hi lo : Z) : Z * Z * Z :=
  let '(nhi, nlo, clz) := norm_denormal hi lo in
  (nhi, nlo, sub64 16 clz).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition f128_of_d (dbits : Z) : Z :=
  let aRep := lo64 dbits in
  let aExp := shr64 (shl64 aRep 1) 53 in
  let aSig := shr64 (shl64 aRep 12) 12 in
  let signHi := shl64 (shr64 aRep 63) 63 in
  if negb (aExp =? 0) then
    if negb (aExp =? 2047) then
      let dstExp := add64 aExp 0x3c00 in
      let hi := Z.lor (Z.lor (shl64 dstExp 48) (shr64 aSig 4)) signHi in
      let lo := shl64 aSig 60 in
      mk128 hi lo
    else
      let hi := Z.lor (Z.lor INF_HI (shr64 aSig 4)) signHi in
      let lo := shl64 aSig 60 in
      mk128 hi lo
  else if aSig =? 0 then mk128 (Z.lor (Z.lor (shl64 0 48) 0) signHi) aSig
  else
    let half := shr64 aSig 1 in
    let clz := clz64_mirror aSig in
    let shM64 := sub64 clz 15 in
    let sh := add64 clz 49 in
    let hi0 := if negb (is_neg64 shM64) then shl64 aSig (Z.land shM64 63)
               else shr64 half (Z.land (sext32 (sub64 14 clz)) 63) in
    let dstExp := sub64 0x3c0c clz in
    let lo := Z.land (smask64 shM64) (shl64 aSig (Z.land sh 63)) in
    let sigHi := Z.lxor hi0 IMPLICIT_HI in
    let hi := Z.lor (Z.lor (shl64 dstExp 48) sigHi) signHi in
    mk128 hi lo.

(* [comment removed for export] *)
Definition trunc_round (sig0 roundBits : Z) : Z :=
  if negb (roundBits <? HALF60 + 1) then add64 sig0 1
  else if negb (negb (roundBits =? HALF60)) then add64 (Z.land sig0 1) sig0
  else sig0.

Definition f128_to_d (a : Z) : Z :=
  let a_lo := lo64 a in
  let a_hi := hi64 a in
  let srcExp := shr64 (shl64 a_hi 1) 49 in
  let sigHi := shr64 (shl64 a_hi 16) 16 in
  let candM1 := add64 srcExp 0xffffffffffffc3ff in
  let signHi := shl64 (shr64 a_hi 63) 63 in
  let '(dstExp, dstSigFrac) :=
    if negb (2045 <? candM1) then
      let sig0 := Z.lor (shr64 a_lo 60) (shl64 sigHi 4) in
      let roundBits := shr64 (shl64 a_lo 4) 4 in
      let exp0 := add64 candM1 1 in
      let sig1 := trunc_round sig0 roundBits in
      let carry := shr64 sig1 52 in
      let dstSigFrac := Z.land (sub64 carry 1) sig1 in
      let dstExp := add64 carry exp0 in
      (dstExp, dstSigFrac)
    else
      let isNaN := if Z.lor a_lo sigHi =? 0 then false
                   else negb (negb (srcExp =? 0x7fff)) in
      if isNaN then
        let dstSigFrac := Z.lor (Z.lor (shr64 a_lo 60) DQUIET) (shl64 sigHi 4) in
        let dstExp := 2047 in
        (dstExp, dstSigFrac)
      else if negb (srcExp <=? 0x43fe) then
        let dstSigFrac := 0 in
        let dstExp := 2047 in
        (dstExp, dstSigFrac)
      else
        let expZ := eqz64 srcExp in
        let k := Z.lxor expZ 0x3c01 in
        let shift := sub64 k srcExp in
        if lt_s64 112 shift then (0, 0)
        else
          let expNZ := nez64 srcExp in
          let shNZ0 := Z.lxor k srcExp in
          let negsh := sext32 (sub64 0 shift) in
          let implicit := shl64 expNZ 48 in
          let shNZ := nez64 shNZ0 in
          let nW := sext32 (sub64 128 shift) in
          let t0 := shl64 a_lo (Z.land negsh 63) in
          let sigHi1 := Z.lor sigHi implicit in
          let n := zext32 nW in
          let nM64 := sub64 n 64 in
          let slLo := Z.land (smask64 nM64) t0 in
          let slHi := if negb (is_neg64 nM64) then shl64 a_lo (Z.land n 63)
                      else Z.lor (shl64 sigHi1 (Z.land negsh 63))
                                 (shr64 (shr64 a_lo 1) (Z.land (not64 n) 63)) in
          let stickySrc := Z.lor slLo slHi in
          let m := zext32 shift in
          let sticky0 := nez64 stickySrc in
          let mM64 := sub64 m 64 in
          let sticky := Z.land shNZ sticky0 in
          let srLo := if negb (is_neg64 mM64) then shr64 sigHi1 (Z.land m 63)
                      else Z.lor (shr64 a_lo (Z.land shift 63))
                                 (shl64 (shl64 sigHi1 1) (Z.land (not64 m) 63)) in
          let srHi0 := shr64 sigHi1 (Z.land shift 63) in
          let srHi := Z.land (smask64 mM64) srHi0 in
          let sig0 := Z.lor (shr64 srLo 60) (shl64 srHi 4) in
          let roundBits := Z.lor (shr64 (shl64 srLo 4) 4) sticky in
          let sig1 := trunc_round sig0 roundBits in
          let carry := nez64 (shr64 sig1 52) in
          let dstSigFrac := Z.lxor sig1 (shl64 carry 52) in
          let dstExp := carry in
          (dstExp, dstSigFrac) in
  let bits := Z.lor (Z.lor (shl64 dstExp 52) signHi) dstSigFrac in
  bits.

(* [comment removed for export] *)
Definition f128_le (a b : Z) : Z :=
  let a_lo := lo64 a in
  let a_hi := hi64 a in
  let b_lo := lo64 b in
  let b_hi := hi64 b in
  let aAbsHi := Z.land a_hi ABS_HI in
  let aIsNaN := if aAbsHi =? INF_HI then negb (a_lo =? 0) else INF_HI <? aAbsHi in
  if aIsNaN then 1
  else
  let bAbsHi := Z.land b_hi ABS_HI in
  let bIsNaN := if bAbsHi =? INF_HI then negb (b_lo =? 0) else INF_HI <? bAbsHi in
  if bIsNaN then 1
  else if Z.lor (Z.lor b_lo a_lo) (Z.lor bAbsHi aAbsHi) =? 0 then 0
  else
  let isLess :=
    if negb (is_neg64 (Z.land b_hi a_hi)) then
      (if a_hi =? b_hi then a_lo <? b_lo else lt_s64 a_hi b_hi)
    else
      (if a_hi =? b_hi then b_lo <? a_lo else lt_s64 b_hi a_hi) in
  if isLess then (-1)
  else nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)).

(* [comment removed for export] *)
Definition f128_ge (a b : Z) : Z :=
  let a_lo := lo64 a in
  let a_hi := hi64 a in
  let b_lo := lo64 b in
  let b_hi := hi64 b in
  let aAbsHi := Z.land a_hi ABS_HI in
  let aIsNaN := if aAbsHi =? INF_HI then negb (a_lo =? 0) else INF_HI <? aAbsHi in
  if aIsNaN then (-1)
  else
  let bAbsHi := Z.land b_hi ABS_HI in
  let bIsNaN := if bAbsHi =? INF_HI then negb (b_lo =? 0) else INF_HI <? bAbsHi in
  if bIsNaN then (-1)
  else if Z.lor (Z.lor b_lo a_lo) (Z.lor bAbsHi aAbsHi) =? 0 then 0
  else
  let isLess :=
    if negb (is_neg64 (Z.land b_hi a_hi)) then
      (if a_hi =? b_hi then a_lo <? b_lo else lt_s64 a_hi b_hi)
    else
      (if a_hi =? b_hi then b_lo <? a_lo else lt_s64 b_hi a_hi) in
  if isLess then (-1)
  else nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fixunstfsi_a2 (a_hi a_lo : Z) : Z :=
  if is_neg64 a_hi then 0
  else
  let e := shr64 (shl64 a_hi 1) 49 in
  if e <? 0x3fff then 0
  else
  let t := add64 e 0xffffffffffffbfe1 in
  if negb (0xffffffffffffffe0 <=? t) then 0xffffffffffffffff
  else
  let sigHi := Z.lor (shr64 (shl64 a_hi 16) 16) IMPLICIT_HI in
  let sW := sext32 (sub64 0x406f e) in
  let s := zext32 sW in
  let sM64 := sub64 s 64 in
  if negb (is_neg64 sM64) then shr64 sigHi (Z.land s 63)
  else Z.lor (shr64 a_lo (Z.land sW 63)) (shl64 (shl64 sigHi 1) (Z.land (not64 s) 63)).

(* [comment removed for export] *)
Definition fixunstfsi_a0 (a : Z) : Z :=
  let a_lo := lo64 a in
  let a_hi := hi64 a in
  sext32 (fixunstfsi_a2 a_hi a_lo).

(* [comment removed for export] *)
Definition f128_to_u32 (a : Z) : Z := Z.land (fixunstfsi_a0 a) M32.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition f128_of_u32 (u : Z) : Z :=
  let a0 := sext32 u in
  if a0 =? 0 then mk128 0 a0
  else
  let half := srliw a0 1 in
  let clz := clz32_mirror a0 in
  let aZ := zext32 a0 in
  let e := Z.lxor clz 31 in
  let shW := sext32 (sub64 112 e) in
  let n := zext32 shW in
  let nM64 := sub64 n 64 in
  let hi0 := if negb (is_neg64 nM64) then shl64 aZ (Z.land n 63)
             else shr64 half (Z.land (not64 n) 63) in
  let lo := Z.land (smask64 nM64) (shl64 aZ (Z.land shW 63)) in
  let hi1 := Z.lxor hi0 IMPLICIT_HI in
  let expW := sext32 (sub64 0x401e clz) in
  let hi := add64 hi1 (shl64 expW 48) in
  mk128 hi lo.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition f128_of_i32 (i : Z) : Z :=
  let a0 := sext32 i in
  if a0 =? 0 then mk128 0 a0
  else
  let s := sub64 0 (Z.land (shr64 a0 31) 1) in
  let signPart := Z.land a0 0xffffffff80000000 in
  let absW := sext32 (sub64 (Z.lxor a0 s) s) in
  let half := srliw absW 1 in
  let clz := clz32_mirror absW in
  let signHi := shl64 signPart 32 in
  let e := Z.lxor clz 31 in
  let shW := sext32 (sub64 112 e) in
  let n := zext32 shW in
  let nM64 := sub64 n 64 in
  let aZ := zext32 absW in
  let hi0 := if negb (is_neg64 nM64) then shl64 aZ (Z.land n 63)
             else shr64 half (Z.land (not64 n) 63) in
  let lo := Z.land (smask64 nM64) (shl64 aZ (Z.land shW 63)) in
  let hi1 := Z.lxor hi0 IMPLICIT_HI in
  let expW := sext32 (sub64 0x401e clz) in
  let hi2 := add64 hi1 (shl64 expW 48) in
  let hi := Z.lor hi2 signHi in
  mk128 hi lo.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mul_round (signHi resHi resLo lo_hi lo_lo : Z) : Z :=
  let resHi1 := Z.lor resHi signHi in
  let roundUp := if lo_hi =? SIGN64 then negb (lo_lo =? 0) else is_neg64 lo_hi in
  if roundUp then
    let resLo1 := add64 resLo 1 in
    let resHi2 := add64 resHi1 (eqz64 resLo1) in
    mk128 resHi2 resLo1
  else if Z.lor lo_lo (Z.lxor lo_hi SIGN64) =? 0 then
    let t := add64 resLo (Z.land resLo 1) in
    let resHi2 := add64 resHi1 (ltu64 t resLo) in
    mk128 resHi2 t
  else
    mk128 resHi1 resLo.

(* [comment removed for export] *)
Definition mul_finish (signHi productExponent hi_hi hi_lo lo_hi lo_lo : Z) : Z :=
  if productExponent <=? 0 then
    let shift := sub64 1 (u64_of_s productExponent) in
    if 127 <? shift then mk128 signHi 0
    else
      let n    := add64 (u64_of_s productExponent) 127 in
      let n32  := zext32 n in
      let nM64 := sub64 n32 64 in
      let notn := not64 n32 in
      (* [comment removed for export] *)
      let '(slHi, slLo, hsHi, hsLo) :=
        if is_neg64 nM64
        then (Z.lor (shl64 lo_hi (Z.land n 63)) (shr64 (shr64 lo_lo 1) (Z.land notn 63)),
              shl64 lo_lo (Z.land n 63),
              Z.lor (shl64 hi_hi (Z.land n 63)) (shr64 (shr64 hi_lo 1) (Z.land notn 63)),
              shl64 hi_lo (Z.land n 63))
        else (shl64 lo_lo (Z.land n32 63), 0, shl64 hi_lo (Z.land n32 63), 0) in
      let stickySrc := Z.lor slLo slHi in
      let shift32   := zext32 shift in
      let shiftM64  := sub64 shift32 64 in
      let notshift  := not64 shift32 in
      (* [comment removed for export] *)
      let '(lsLo, lsHi, hrLo, hrHi) :=
        if is_neg64 shiftM64
        then (Z.lor (shr64 lo_lo (Z.land shift 63)) (shl64 (shl64 lo_hi 1) (Z.land notshift 63)),
              shr64 lo_hi (Z.land shift 63),
              Z.lor (shr64 hi_lo (Z.land shift 63)) (shl64 (shl64 hi_hi 1) (Z.land notshift 63)),
              shr64 hi_hi (Z.land shift 63))
        else (shr64 lo_hi (Z.land shift32 63), 0, shr64 hi_hi (Z.land shift32 63), 0) in
      let sticky := nez64 stickySrc in
      let mixLo  := Z.lor hsLo lsLo in
      let lo_hi2 := Z.lor hsHi lsHi in
      let lo_lo2 := Z.lor mixLo sticky in
      mul_round signHi hrHi hrLo lo_hi2 lo_lo2
  else
    let resLo := hi_lo in
    let resHi := Z.lor (shl64 (u64_of_s productExponent) 48) (Z.land hi_hi MASK48) in
    mul_round signHi resHi resLo lo_hi lo_lo.

(* [comment removed for export] *)
Definition mul_core (signHi aExp bExp aSigHi aSigLo bSigHi bSigLo scale : Z) : Z :=
  let bLo15 := shl64 bSigLo 15 in
  let bHi15 := Z.lor (shr64 bSigLo 49) (shl64 bSigHi 15) in
  let A1 := Z.lor (shr64 aSigHi 32) 0x10000 in
  let A2 := zext32 aSigHi in
  let A3 := shr64 aSigLo 32 in
  let A4 := zext32 aSigLo in
  let B1 := Z.lor (shr64 (shl64 bSigHi 15) 32) 0x80000000 in
  let B2 := zext32 bHi15 in
  let B3 := shr64 bLo15 32 in
  let B4 := zext32 bLo15 in
  let expSum := add64 aExp bExp in
  (* [comment removed for export] *)
  let p13 := mul64 B3 A1 in
  let p23 := mul64 B3 A2 in
  let p24 := mul64 B4 A2 in
  let p33 := mul64 B3 A3 in
  let p43 := mul64 B3 A4 in
  let p44 := mul64 B4 A4 in
  let p11 := mul64 B1 A1 in
  let p14 := mul64 B4 A1 in
  let p21 := mul64 B1 A2 in
  let p22 := mul64 B2 A2 in
  let p41 := mul64 B1 A4 in
  let p31 := mul64 B1 A3 in
  let p34 := mul64 B4 A3 in
  let p42 := mul64 B2 A4 in
  let p12 := mul64 B2 A1 in
  let p32 := mul64 B2 A3 in
  (* [comment removed for export] *)
  let s2a := add64 p24 p33 in
  let sum1 := add64 p34 p43 in
  let c2a := ltu64 s2a p24 in
  let sum2 := add64 s2a p42 in
  let s3a := add64 p14 p23 in
  let s4a := add64 p31 p13 in
  let c1 := ltu64 sum1 p34 in
  let c2b := ltu64 sum2 s2a in
  let c3a := ltu64 s3a p14 in
  let s3b := add64 s3a p41 in
  let sum5 := add64 p12 p21 in
  let sum1Shr32 := shr64 sum1 32 in
  let sum1Shl32 := shl64 sum1 32 in
  let c4a := ltu64 s4a p31 in
  let sum4 := add64 s4a p22 in
  let sum2Hi := add64 c2a c2b in
  let c3b := ltu64 s3b s3a in
  let sum3 := add64 s3b p32 in
  let c5 := ltu64 sum5 p12 in
  let c1Shl32 := shl64 c1 32 in
  let lo_lo := add64 sum1Shl32 p44 in
  let sum5Shr32 := shr64 sum5 32 in
  let sum5Shl32 := shl64 sum5 32 in
  let c4b := ltu64 sum4 s4a in
  let hh1 := add64 c4a p11 in
  let c3ab := add64 c3a c3b in
  let c3c := ltu64 sum3 s3b in
  let r0c := ltu64 lo_lo sum1Shl32 in
  let sum1Mid := Z.lor sum1Shr32 c1Shl32 in
  let sum3Shr32 := shr64 sum3 32 in
  let sum3Shl32 := shl64 sum3 32 in
  let c5Shl32 := shl64 c5 32 in
  let hh2 := add64 hh1 c4b in
  let m1 := add64 sum4 sum2Hi in
  let sum3Hi := add64 c3ab c3c in
  let r1a := add64 sum2 sum1Mid in
  let sum5MidHi := Z.lor c5Shl32 sum5Shr32 in
  let cm1 := ltu64 m1 sum4 in
  let m2 := add64 m1 sum5Shl32 in
  let cr1a := ltu64 r1a sum2 in
  let sum3HiShl32 := shl64 sum3Hi 32 in
  let r1 := add64 r1a sum3Shl32 in
  let hh3 := add64 hh2 cm1 in
  let cm2 := ltu64 m2 m1 in
  let cr1b := ltu64 r1 r1a in
  let lo_hi := add64 r1 r0c in
  let sum3Mid := Z.lor sum3Shr32 sum3HiShl32 in
  let hh4 := add64 hh3 sum5MidHi in
  let r1Hi := add64 cr1a cr1b in
  let carry := ltu64 lo_hi r1 in
  let hh5 := add64 hh4 cm2 in
  let m3 := add64 m2 sum3Mid in
  let cm3 := ltu64 m3 m2 in
  let m4 := add64 m3 r1Hi in
  let hh6 := add64 hh5 cm3 in
  let cm4 := ltu64 m4 m3 in
  let hi_lo := add64 m4 carry in
  let hh7 := add64 hh6 cm4 in
  let cm5 := ltu64 hi_lo m4 in
  let hi_hi := add64 hh7 cm5 in
  (* [comment removed for export] *)
  let scaleAdj := scale - 0x3fff in
  let productExponent := expSum + scaleAdj in
  if is_neg64 (shl64 hi_hi 15) then
    let productExponent1 := productExponent + 1 in
    if negb (productExponent1 <? 0x7fff) then mk128 (Z.lor signHi INF_HI) 0
    else mul_finish signHi productExponent1 hi_hi hi_lo lo_hi lo_lo
  else
    let hi_hi1 := Z.lor (shl64 hi_hi 1) (shr64 hi_lo 63) in
    let hi_lo1 := Z.lor (shl64 hi_lo 1) (shr64 lo_hi 63) in
    let lo_hi1 := Z.lor (shl64 lo_hi 1) (shr64 lo_lo 63) in
    let lo_lo1 := shl64 lo_lo 1 in
    if 0x7fff <=? productExponent then mk128 (Z.lor signHi INF_HI) 0
    else mul_finish signHi productExponent hi_hi1 hi_lo1 lo_hi1 lo_lo1.

(* [comment removed for export] *)
Definition f128_mul (a b : Z) : Z :=
  let a_lo := lo64 a in
  let a_hi := hi64 a in
  let b_lo := lo64 b in
  let b_hi := hi64 b in
  (* [comment removed for export] *)
  let aExp := shr64 (shl64 a_hi 1) 49 in
  let bExp := shr64 (shl64 b_hi 1) 49 in
  let signHi := shl64 (shr64 (Z.lxor b_hi a_hi) 63) 63 in
  let aSigHi := Z.land a_hi MASK48 in
  let bSigHi := Z.land b_hi MASK48 in
  let aSigLo := a_lo in
  let bSigLo := b_lo in
  let aExpM := add64 aExp 0xffffffffffff8001 in
  let bExpM := add64 bExp 0xffffffffffff8001 in
  if negb (orb (aExpM <? 0xffffffffffff8002) (bExpM <=? 0xffffffffffff8001))
  then mul_core signHi aExp bExp aSigHi aSigLo bSigHi bSigLo 0
  else
  (* [comment removed for export] *)
  let aAbsHi := Z.land a_hi ABS_HI in
  let aIsNaN := if aAbsHi =? INF_HI then negb (a_lo =? 0) else negb (aAbsHi <? INF_HI) in
  if aIsNaN then mk128 (Z.lor a_hi QUIET_HI) a_lo
  else
  let bAbsHi := Z.land b_hi ABS_HI in
  let bIsNaN := if bAbsHi =? INF_HI then negb (b_lo =? 0) else negb (bAbsHi <? INF_HI) in
  if bIsNaN then mk128 (Z.lor b_hi QUIET_HI) b_lo
  else if Z.lor (Z.lxor aAbsHi INF_HI) a_lo =? 0 then
    (if negb (Z.lor b_lo bAbsHi =? 0) then mk128 (Z.lor signHi INF_HI) 0 else mk128 QNAN_HI 0)
  else if Z.lor (Z.lxor bAbsHi INF_HI) b_lo =? 0 then
    (if negb (Z.lor a_lo aAbsHi =? 0) then mk128 (Z.lor signHi INF_HI) 0 else mk128 QNAN_HI 0)
  else if Z.lor a_lo aAbsHi =? 0 then mk128 signHi 0
  else if Z.lor b_lo bAbsHi =? 0 then mk128 signHi 0
  else
  (* [comment removed for export] *)
  let '(aSigHi1, aSigLo1, scale1) :=
    if shr64 aAbsHi 48 =? 0 then
      let '(naHi, naLo, naClz) := norm_denormal aSigHi aSigLo in
      (naHi, naLo, 16 - naClz)
    else (aSigHi, aSigLo, 0) in
  let '(bSigHi1, bSigLo1, scale2) :=
    if shr64 bAbsHi 48 =? 0 then
      let '(nbHi, nbLo, nbClz) := norm_denormal bSigHi bSigLo in
      (nbHi, nbLo, scale1 - nbClz + 16)
    else (bSigHi, bSigLo, scale1) in
  mul_core signHi aExp bExp aSigHi1 aSigLo1 bSigHi1 bSigLo1 scale2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition align_mirror (aExp bExp bSigHi3 bSigLo3 : Z) : Z * Z :=
  if Z.eqb aExp bExp then (bSigHi3, bSigLo3)
  else
    let align := sub64 aExp bExp in
    if Z.ltb 127 align then (0, 1)
    else
      let n1 := zext32 (sub64 128 align) in
      let d1 := sub64 n1 64 in
      let negal := sext32 (sub64 0 align) in
      let outHi := if is_neg64 d1
                   then Z.lor (shl64 bSigHi3 (Z.land negal 63))
                               (shr64 (shr64 bSigLo3 1) (Z.land (not64 n1) 63))
                   else shl64 bSigLo3 (Z.land n1 63) in
      let outLoRaw := shl64 bSigLo3 (Z.land negal 63) in
      let outLo := Z.land (smask64 d1) outLoRaw in
      let n2 := zext32 align in
      let sticky := b2z (negb (Z.eqb (Z.lor outLo outHi) 0)) in
      let d2 := sub64 n2 64 in
      let newLo := if is_neg64 d2
                   then Z.lor (shr64 bSigLo3 (Z.land align 63))
                               (shl64 (shl64 bSigHi3 1) (Z.land (not64 n2) 63))
                   else shr64 bSigHi3 (Z.land n2 63) in
      let newHi := Z.land (smask64 d2) (shr64 bSigHi3 (Z.land align 63)) in
      let BLo := Z.lor newLo sticky in
      let BHi := newHi in
      (BHi, BLo).

(* [comment removed for export] *)
Definition addsub_mirror (subtraction AHi ALo BHi BLo aExp : Z) : option (Z * Z * Z) :=
  if negb (Z.eqb subtraction 0) then
    if Z.eqb (Z.lor (Z.lxor ALo BLo) (Z.lxor AHi BHi)) 0 then None
    else
      let borrow := b2z (Z.ltb ALo BLo) in
      let SHi := sub64 (sub64 AHi BHi) borrow in
      let SLo := sub64 ALo BLo in
      if Z.eqb (shr64 SHi 51) 0 then
        let clzS := clz128_mirror SHi SLo in
        let shiftS := sub64 clzS 12 in
        let '(SHi, SLo) := shl128_mirror SHi SLo shiftS in
        let aExp := sub64 aExp shiftS in
        Some (SHi, SLo, aExp)
      else Some (SHi, SLo, aExp)
  else
    let SLo := add64 BLo ALo in
    let carry := b2z (Z.ltb SLo BLo) in
    let SHi := add64 (add64 BHi AHi) carry in
    if is_neg64 (shl64 SHi 11) then
      let st := Z.land BLo 1 in
      let SLo := Z.lor (Z.lor (shr64 SLo 1) st) (shl64 SHi 63) in
      let SHi := shr64 SHi 1 in
      let aExp := add64 aExp 1 in
      Some (SHi, SLo, aExp)
    else Some (SHi, SLo, aExp).

(* [comment removed for export] *)
Definition denorm_mirror (SHi SLo aExp : Z) : Z * Z :=
  let shift := sub64 1 aExp in
  let negsh := sext32 (sub64 0 shift) in
  let d3 := sub64 64 shift in
  let t := shl64 SLo (Z.land negsh 63) in
  let outHi := if is_neg64 d3
               then let m := sext32 (sub64 128 shift) in
                    Z.lor (shl64 SHi (Z.land negsh 63)) (shr64 (shr64 SLo 1) (Z.land (not64 m) 63))
               else t in
  let outLo := Z.land (smask64 d3) t in
  let hiSh := shr64 SHi (Z.land shift 63) in
  let n3 := zext32 shift in
  let sticky := b2z (negb (Z.eqb (Z.lor outLo outHi) 0)) in
  let d4 := sub64 n3 64 in
  let mask4 := smask64 d4 in
  let newLo := if is_neg64 d4
               then Z.lor (shr64 SLo (Z.land shift 63)) (shl64 (shl64 SHi 1) (Z.land (not64 n3) 63))
               else shr64 SHi (Z.land n3 63) in
  let SHi := Z.land mask4 hiSh in
  let SLo := Z.lor newLo sticky in
  (SHi, SLo).

(* [comment removed for export] *)
Definition round_mirror (SHi SLo aExp signHi : Z) : Z :=
  let rgs := Z.land SLo 7 in
  let resLo0 := Z.lor (shr64 SLo 3) (shl64 SHi 61) in
  let resHi := Z.lor (Z.lor (shl64 aExp 48) signHi) (Z.land (shr64 SHi 3) MASK48) in
  let resLo := Z.land resLo0 MASKLO in
  let inc := if negb (Z.eqb rgs 4) then b2z (negb (Z.ltb rgs 5)) else Z.land resLo0 1 in
  let sumLo := add64 resLo inc in
  let resHi := add64 resHi (b2z (Z.ltb sumLo resLo)) in
  let resLo := sumLo in
  mk128 resHi resLo.

(* [comment removed for export] *)
Definition add_main (aLo aHi bLo bHi aAbsHi bAbsHi : Z) : Z :=
  let swap := if Z.eqb bAbsHi aAbsHi then Z.ltb aLo bLo else Z.ltb aAbsHi bAbsHi in
  let '(yLo, yHi, xLo, xHi) := if swap then (aLo, aHi, bLo, bHi) else (bLo, bHi, aLo, aHi) in
  let aExp := shr64 (shl64 xHi 1) 49 in
  let bExp := shr64 (shl64 yHi 1) 49 in
  let aSigHi := Z.land xHi MASK48 in
  let aSigLo := xLo in
  let bSigHi := Z.land yHi MASK48 in
  let bSigLo := yLo in
  let '(aSigHi, aSigLo, aExp) :=
      if Z.eqb aExp 0 then normalize_mirror aSigHi aSigLo else (aSigHi, aSigLo, aExp) in
  let '(bSigHi, bSigLo, bExp) :=
      if Z.eqb bExp 0 then normalize_mirror bSigHi bSigLo else (bSigHi, bSigLo, bExp) in
  let subtraction := shr64 (Z.lxor bHi aHi) 63 in
  let aSigHi3 := Z.lor (shl64 aSigHi 3) (shr64 aSigLo 61) in
  let bSigHi3 := Z.lor (shl64 bSigHi 3) (Z.lor (shr64 bSigLo 61) IMPL3_HI) in
  let bSigLo3 := shl64 bSigLo 3 in
  let AHi := Z.lor aSigHi3 IMPL3_HI in
  let ALo := shl64 aSigLo 3 in
  let '(BHi, BLo) := align_mirror aExp bExp bSigHi3 bSigLo3 in
  match addsub_mirror subtraction AHi ALo BHi BLo aExp with
  | None => mk128 0 0
  | Some (SHi, SLo, aExp) =>
      let signHi := shl64 (shr64 xHi 63) 63 in
      if negb (lt_s64 aExp 0x7fff) then mk128 (Z.lor signHi INF_HI) 0
      else
        let '(SHi, SLo, aExp) :=
            if negb (lt_s64 0 aExp)
            then (let '(SHi, SLo) := denorm_mirror SHi SLo aExp in (SHi, SLo, 0))
            else (SHi, SLo, aExp) in
        round_mirror SHi SLo aExp signHi
  end.

(* [comment removed for export] *)
Definition f128_add (a b : Z) : Z :=
  let aLo := lo64 a in
  let aHi := hi64 a in
  let bLo := lo64 b in
  let bHi := hi64 b in
  let aAbsHi := Z.land aHi ABS_HI in
  let bAbsHi := Z.land bHi ABS_HI in
  let aSpecial := if Z.eqb aAbsHi 0 then Z.eqb aLo 0
                  else Z.ltb (add64 aAbsHi SPEC_K) SPEC_K in
  let tb := add64 bAbsHi SPEC_K in
  let bSpecial := if Z.eqb tb SPEC_K then Z.eqb bLo 0
                  else negb (Z.ltb SPEC_K tb) in
  if aSpecial || bSpecial then
    let aIsNaN := if Z.eqb aAbsHi INF_HI then negb (Z.eqb aLo 0)
                  else negb (Z.ltb aAbsHi INF_HI) in
    if aIsNaN then mk128 (Z.lor aHi QUIET_HI) aLo
    else
      let bIsNaN := if Z.eqb bAbsHi INF_HI then negb (Z.eqb bLo 0)
                    else negb (Z.ltb bAbsHi INF_HI) in
      if bIsNaN then mk128 (Z.lor bHi QUIET_HI) bLo
      else if Z.eqb (Z.lor aLo (Z.lxor aAbsHi INF_HI)) 0 then
        let x := Z.lor (Z.lxor bLo aLo) (Z.lxor (Z.lxor bHi aHi) SIGN64) in
        let m := sub64 (b2z (Z.eqb x 0)) 1 in
        let rhi := if negb (Z.eqb x 0) then aHi else QNAN_HI in
        mk128 rhi (Z.land m aLo)
      else if Z.eqb (Z.lor bLo (Z.lxor bAbsHi INF_HI)) 0 then mk128 bHi bLo
      else if Z.eqb (Z.lor aLo aAbsHi) 0 then
        (if negb (Z.eqb (Z.lor bLo bAbsHi) 0) then mk128 bHi bLo
         else mk128 (Z.land bHi aHi) (Z.land bLo aLo))
      else if negb (Z.eqb (Z.lor bLo bAbsHi) 0) then add_main aLo aHi bLo bHi aAbsHi bAbsHi
      else mk128 aHi aLo
  else add_main aLo aHi bLo bHi aAbsHi bAbsHi.

(* [comment removed for export] *)
Definition f128_sub (a b : Z) : Z :=
  let bLo := lo64 b in
  let bHi := hi64 b in
  f128_add a (mk128 (Z.lxor bHi SIGN64) bLo).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition half_iter (x b : Z) : Z :=
  let corr := sub64 0 (mulhu x b) in
  let lo := mul64 corr x in
  let hi := mulhu corr x in
  Z.lor (shr64 lo 63) (shl64 hi 1).

(* [comment removed for export] *)
Definition div_round (signHi absHi absLo rHi rLo bHi bLo : Z) : Z :=
  let odd := Z.land absLo 1 in
  let r3Lo := add64 odd rLo in
  let rc := b2z (Z.ltb r3Lo odd) in
  let r3Hi := add64 rHi rc in
  let gt1 := b2z (if Z.eqb r3Hi bHi then Z.ltb bLo r3Lo else Z.ltb bHi r3Hi) in
  let abs1Lo := add64 absLo gt1 in
  let b2Hi := shl64 bHi 1 in
  let ca := b2z (Z.ltb abs1Lo absLo) in
  let b3Hi0 := mulhu bLo 3 in
  let abs1Hi := add64 absHi ca in
  let b3Hi1 := add64 b3Hi0 bHi in
  let b3Hi := add64 b3Hi1 b2Hi in
  let ltInf1 := b2z (Z.ltb abs1Hi INF_HI) in
  let gt3 := b2z (if Z.eqb r3Hi b3Hi then Z.ltb (add64 (shl64 bLo 1) bLo) r3Lo else Z.ltb b3Hi r3Hi) in
  let inc2 := Z.land ltInf1 gt3 in
  let b5Hi0 := mulhu bLo 5 in
  let b5Hi1 := add64 b5Hi0 bHi in
  let b4Hi := shl64 bHi 2 in
  let abs2Lo := add64 abs1Lo inc2 in
  let cb := b2z (Z.ltb abs2Lo abs1Lo) in
  let abs2Hi := add64 abs1Hi cb in
  let b5Hi := add64 b5Hi1 b4Hi in
  let ltInf2 := b2z (Z.ltb abs2Hi INF_HI) in
  let gt5 := b2z (if Z.eqb r3Hi b5Hi then Z.ltb (add64 (shl64 bLo 2) bLo) r3Lo else Z.ltb b5Hi r3Hi) in
  let inc3 := Z.land ltInf2 gt5 in
  let resLo := add64 abs2Lo inc3 in
  let cc := b2z (Z.ltb resLo abs2Lo) in
  let resHi := Z.lor (add64 abs2Hi cc) signHi in
  mk128 resHi resLo.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition divc_setup (aExp bExp aSigHi aLo bSigHi bLo scale : Z) :=
  let expDiff := aExp - bExp in
  let blo := shl64 bLo 15 in
  let aLoTop := shr64 aLo 63 in
  let a2Lo := shl64 aLo 1 in
  let aHi2n := shl64 aSigHi 1 in
  let aSigHiI := Z.lor aSigHi IMPLICIT_HI in
  let bSigHiI := Z.lor bSigHi IMPLICIT_HI in
  let expM1 := (scale + 0x3ffe) + expDiff in
  let A2 := zext32 (Z.lor aLoTop aHi2n) in
  let A3 := shr64 a2Lo 32 in
  let A4 := Z.land a2Lo 0xfffffffe in
  let b_hw := Z.lor (shr64 bLo 49) (shl64 bSigHiI 15) in
  let aHi2 := shl64 aSigHiI 1 in
  let A1 := shr64 aHi2 32 in
  let x0 := sub64 C_HW b_hw in
  (expM1, blo, b_hw, A1, A2, A3, A4, aSigHiI, bSigHiI, aHi2, aLoTop, a2Lo, x0).

(* [comment removed for export] *)
Definition divc_newton (x0 b_hw : Z) : Z :=
  let x1 := half_iter x0 b_hw in
  let x2 := half_iter x1 b_hw in
  let x3 := half_iter x2 b_hw in
  let x4 := half_iter x3 b_hw in
  sub64 x4 1.

(* [comment removed for export] *)
Definition divc_full (xh b_hw blo : Z) : Z * Z :=
  let pHhi := mulhu b_hw xh in
  let pHlo := mul64 b_hw xh in
  let pLhi := mulhu blo xh in
  let sumlo := add64 pHlo pLhi in
  let c0 := b2z (Z.ltb sumlo pHlo) in
  let lt2 := b2z (Z.ltb sumlo 2) in
  let lo_corr := sub64 1 sumlo in
  let hiP := add64 pHhi c0 in
  let ge2 := Z.lxor lt2 1 in
  let m1lo := mul64 lo_corr xh in
  let m1hi := mulhu lo_corr xh in
  let negHi := add64 hiP ge2 in
  let Blo := Z.lor (shr64 m1lo 63) (shl64 m1hi 1) in
  let Bhi := shr64 m1hi 63 in
  let hi_corr := sub64 0 negHi in
  let m2lo := mul64 xh hi_corr in
  let m2hi := mulhu xh hi_corr in
  let Ahi := Z.lor (shl64 m2hi 1) (shr64 m2lo 63) in
  let Alo := shl64 m2lo 1 in
  let sLo := add64 Alo Blo in
  let sHi := add64 Ahi Bhi in
  let cs1 := b2z (Z.ltb sLo Alo) in
  let x_lo := add64 sLo X_ADJ in
  let sHi1 := add64 sHi cs1 in
  let cs2 := b2z (Z.ltb x_lo sLo) in
  let sHi2 := add64 sHi1 cs2 in
  let x_hi := sub64 sHi2 1 in
  (x_hi, x_lo).

(* [comment removed for export] *)
Definition divc_wide (x_hi x_lo A1 A2 A3 A4 : Z) : Z * Z :=
  let X3 := shr64 x_lo 32 in
  let X4sh := shl64 x_lo 32 in
  let p31 := mul64 X3 A1 in
  let p32 := mul64 X3 A2 in
  let p33 := mul64 X3 A3 in
  let p34 := mul64 X3 A4 in
  let X4 := shr64 X4sh 32 in
  let p42 := mul64 X4 A2 in
  let p41 := mul64 X4 A1 in
  let p43 := mul64 X4 A3 in
  let p44 := mul64 X4 A4 in
  let s2a := add64 p42 p33 in
  let X1 := shr64 x_hi 32 in
  let X2sh := shl64 x_hi 32 in
  let sum1 := add64 p34 p43 in
  let c2a := b2z (Z.ltb s2a p42) in
  let p11 := mul64 X1 A1 in
  let p12 := mul64 A2 X1 in
  let p13 := mul64 A3 X1 in
  let p14 := mul64 A4 X1 in
  let X2 := shr64 X2sh 32 in
  let p22 := mul64 X2 A2 in
  let c1 := b2z (Z.ltb sum1 p34) in
  let sum1Shr32 := shr64 sum1 32 in
  let sum1Shl32 := shl64 sum1 32 in
  let p21 := mul64 X2 A1 in
  let p23 := mul64 X2 A3 in
  let p24 := mul64 X2 A4 in
  let s3a := add64 p41 p14 in
  let c1Shl32 := shl64 c1 32 in
  let lo_lo := add64 sum1Shl32 p44 in
  let s4a := add64 p31 p13 in
  let sum2 := add64 s2a p24 in
  let c3a := b2z (Z.ltb s3a p41) in
  let s3b := add64 s3a p32 in
  let sum5 := add64 p21 p12 in
  let r0c := b2z (Z.ltb lo_lo sum1Shl32) in
  let sum1Mid := Z.lor sum1Shr32 c1Shl32 in
  let c4a := b2z (Z.ltb s4a p31) in
  let sum4 := add64 s4a p22 in
  let c2b := b2z (Z.ltb sum2 s2a) in
  let c3b := b2z (Z.ltb s3b s3a) in
  let sum3 := add64 s3b p23 in
  let c5 := b2z (Z.ltb sum5 p21) in
  let r1a := add64 sum2 sum1Mid in
  let nr0c := not64 r0c in
  let sum5Shr32 := shr64 sum5 32 in
  let sum5Shl32 := shl64 sum5 32 in
  let c4b := b2z (Z.ltb sum4 s4a) in
  let hh1 := add64 c4a p11 in
  let sum2Hi := add64 c2a c2b in
  let c3ab := add64 c3a c3b in
  let c3c := b2z (Z.ltb sum3 s3b) in
  let cr1a := b2z (Z.ltb r1a sum2) in
  let sum3Shr32 := shr64 sum3 32 in
  let sum3Shl32 := shl64 sum3 32 in
  let c5Shl32 := shl64 c5 32 in
  let hh2 := add64 hh1 c4b in
  let m1 := add64 sum4 sum5Shl32 in
  let sum3Hi := add64 c3ab c3c in
  let r1 := add64 r1a sum3Shl32 in
  let sum5MidHi := Z.lor c5Shl32 sum5Shr32 in
  let cm1 := b2z (Z.ltb m1 sum4) in
  let m2 := add64 m1 sum2Hi in
  let sum3HiShl32 := shl64 sum3Hi 32 in
  let cr1b := b2z (Z.ltb r1 r1a) in
  let ltc := b2z (Z.ltb nr0c r1) in
  let eqx := Z.lxor r1 nr0c in
  let hh3 := add64 hh2 sum5MidHi in
  let cm2 := b2z (Z.ltb m2 m1) in
  let r1Hi := add64 cr1a cr1b in
  let neMask := sub64 (b2z (Z.eqb eqx 0)) 1 in
  let sum3Mid := Z.lor sum3Shr32 sum3HiShl32 in
  let hh4 := add64 hh3 cm1 in
  let hh5 := add64 hh4 cm2 in
  let m3 := add64 m2 sum3Mid in
  let carry := Z.land neMask ltc in
  let cm3 := b2z (Z.ltb m3 m2) in
  let m4 := add64 m3 r1Hi in
  let hh6 := add64 hh5 cm3 in
  let cm4 := b2z (Z.ltb m4 m3) in
  let q_lo := add64 m4 carry in
  let hh7 := add64 hh6 cm4 in
  let cm5 := b2z (Z.ltb q_lo m4) in
  let q_hi := add64 hh7 cm5 in
  (q_hi, q_lo).

(* [comment removed for export] *)
Definition divc_tail (signHi expM1 q_hi q_lo aLo aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo : Z) : Z :=
  let topBits := shr64 q_hi 49 in
  let wE0 := expM1 + 1 in
  let '(q1Hi, q1Lo, resHi, resLo, aDHi, aDLo, wE, ovf) :=
    if negb (Z.eqb topBits 0) then
      let q1Lo := Z.lor (shr64 q_lo 1) (shl64 q_hi 63) in
      let q1Hi := shr64 q_hi 1 in
      let aTop := shl64 aLo 48 in
      let pq1 := mul64 q1Hi bLo in
      let pq2 := mul64 q1Lo bSigHiI in
      let pq3 := mulhu q1Lo bLo in
      let d1 := sub64 aTop pq1 in
      let qbLo := mul64 q1Lo bLo in
      let sh := add64 pq3 pq2 in
      let bor := b2z (negb (Z.eqb qbLo 0)) in
      let d2 := sub64 d1 sh in
      let resHi := sub64 d2 bor in
      let resLo := sub64 0 qbLo in
      let aDLo := aLo in
      let aDHi := aSigHiI in
      let wE := wE0 in
      let ovf := negb (Z.ltb wE 0x7fff) in
      (q1Hi, q1Lo, resHi, resLo, aDHi, aDLo, wE, ovf)
    else
      let bit112 := shr64 q_hi 48 in
      let sh := b2z (Z.eqb bit112 0) in
      let q1Hi := Z.lor (shl64 q_hi sh) (shr64 (shr64 q_lo 1) (Z.lxor sh 63)) in
      let q1Lo := shl64 q_lo sh in
      let expSel := if negb (Z.eqb bit112 0) then wE0 else expM1 in
      let aDHi := Z.lor aHi2 aLoTop in
      let aTop := shl64 aLo 49 in
      let pq2 := mul64 q1Lo bSigHiI in
      let pq3 := mulhu q1Lo bLo in
      let pq1 := mul64 q1Hi bLo in
      let sh2 := add64 pq3 pq2 in
      let qbLo := mul64 q1Lo bLo in
      let d1 := sub64 aTop sh2 in
      let bor := b2z (negb (Z.eqb qbLo 0)) in
      let resLo := sub64 0 qbLo in
      let d2 := sub64 d1 pq1 in
      let resHi := sub64 d2 bor in
      let wE := expSel - 1 in
      let aDLo := a2Lo in
      let ovf := Z.leb 0x7fff wE in
      (q1Hi, q1Lo, resHi, resLo, aDHi, aDLo, wE, ovf) in
  if ovf then mk128 (Z.lor signHi INF_HI) 0
  else if negb (Z.leb wE 0) then
    (* [comment removed for export] *)
    let absLo := q1Lo in
    let fracHi := Z.land q1Hi MASK48 in
    let absHi := Z.lor (shl64 (wrap64 wE) 48) fracHi in
    let r2Hi := Z.lor (shl64 resHi 1) (shr64 resLo 63) in
    let r2Lo := shl64 resLo 1 in
    div_round signHi absHi absLo r2Hi r2Lo bSigHiI bLo
  else if Z.leb wE (-113) then mk128 signHi 0
  else
    (* [comment removed for export] *)
    let shiftw := sext32 (sub64 1 (wrap64 wE)) in
    let shift32 := zext32 shiftw in
    let lsh := add64 (wrap64 wE) 112 in
    let absLo := if is_neg64 (sub64 shift32 64)
                 then Z.lor (shr64 q1Lo (Z.land shiftw 63)) (shl64 (shl64 q1Hi 1) (Z.land (not64 shift32) 63))
                 else shr64 q1Hi (Z.land shift32 63) in
    let absHi0 := shr64 q1Hi (Z.land shiftw 63) in
    let maskS := sra63 (sub64 shift32 64) in
    let lsh32 := zext32 lsh in
    let absHi := Z.land maskS absHi0 in
    let aSHi := if is_neg64 (sub64 lsh32 64)
                then Z.lor (shl64 aDHi (Z.land lsh 63)) (shr64 (shr64 aDLo 1) (Z.land (not64 lsh32) 63))
                else shl64 aDLo (Z.land lsh32 63) in
    let aSLo0 := shl64 aDLo (Z.land lsh 63) in
    let maskL := sra63 (sub64 lsh32 64) in
    let pb1 := mul64 bLo absHi in
    let pb2 := mulhu bLo absLo in
    let pb3 := mul64 bSigHiI absLo in
    let aSLo := Z.land maskL aSLo0 in
    let qbLo := mul64 bLo absLo in
    let qh1 := add64 pb2 pb3 in
    let qb2Lo := shl64 qbLo 1 in
    let qbHi := add64 qh1 pb1 in
    let bor := b2z (Z.ltb aSLo qb2Lo) in
    let d1 := sub64 aSHi bor in
    let qb2Hi := Z.lor (shl64 qbHi 1) (shr64 qbLo 63) in
    let r2Hi := sub64 d1 qb2Hi in
    let r2Lo := sub64 aSLo qb2Lo in
    div_round signHi absHi absLo r2Hi r2Lo bSigHiI bLo.

Definition div_core (signHi aExp bExp aSigHi aLo bSigHi bLo scale : Z) : Z :=
  let '(expM1, blo, b_hw, A1, A2, A3, A4, aSigHiI, bSigHiI, aHi2, aLoTop, a2Lo, x0) :=
    divc_setup aExp bExp aSigHi aLo bSigHi bLo scale in
  let xh := divc_newton x0 b_hw in
  let '(x_hi, x_lo) := divc_full xh b_hw blo in
  let '(q_hi, q_lo) := divc_wide x_hi x_lo A1 A2 A3 A4 in
  divc_tail signHi expM1 q_hi q_lo aLo aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo.

(* [comment removed for export] *)
Definition f128_div (a b : Z) : Z :=
  let a_lo := lo64 a in
  let a_hi := hi64 a in
  let b_lo := lo64 b in
  let b_hi := hi64 b in
  (* [comment removed for export] *)
  let aExp := shr64 (shl64 a_hi 1) 49 in
  let bExp := shr64 (shl64 b_hi 1) 49 in
  let signHi := shl64 (shr64 (Z.lxor b_hi a_hi) 63) 63 in
  let aSigHi := Z.land a_hi MASK48 in
  let bSigHi := Z.land b_hi MASK48 in
  let aExpM := add64 aExp EXPK in
  let bExpM := add64 bExp EXPK in
  if negb (orb (Z.ltb aExpM EXPK2) (Z.leb bExpM EXPK))
  then div_core signHi aExp bExp aSigHi a_lo bSigHi b_lo 0
  else
    (* [comment removed for export] *)
    let aAbsHi := Z.land a_hi ABS_HI in
    let aIsNaN := if Z.eqb aAbsHi INF_HI then negb (Z.eqb a_lo 0) else negb (Z.ltb aAbsHi INF_HI) in
    if aIsNaN then mk128 (Z.lor a_hi QUIET_HI) a_lo
    else
    let bAbsHi := Z.land b_hi ABS_HI in
    let bIsNaN := if Z.eqb bAbsHi INF_HI then negb (Z.eqb b_lo 0) else negb (Z.ltb bAbsHi INF_HI) in
    if bIsNaN then mk128 (Z.lor b_hi QUIET_HI) b_lo
    else if Z.eqb (Z.lor (Z.lxor aAbsHi INF_HI) a_lo) 0 then
      (if negb (Z.eqb (Z.lor b_lo (Z.lxor bAbsHi INF_HI)) 0)
       then mk128 (Z.lor signHi INF_HI) 0
       else mk128 QNAN_HI 0)
    else if Z.eqb (Z.lor b_lo (Z.lxor bAbsHi INF_HI)) 0 then mk128 signHi 0
    else if Z.eqb (Z.lor a_lo aAbsHi) 0 then
      (if negb (Z.eqb (Z.lor b_lo bAbsHi) 0) then mk128 signHi 0 else mk128 QNAN_HI 0)
    else if Z.eqb (Z.lor b_lo bAbsHi) 0 then mk128 (Z.lor signHi INF_HI) 0
    else
    (* [comment removed for export] *)
    let '(aSigHi1, aLo1, scale1) :=
      if Z.eqb (shr64 aAbsHi 48) 0 then
        let '(nhi, nlo, nclz) := norm_denormal aSigHi a_lo in (nhi, nlo, 16 - nclz)
      else (aSigHi, a_lo, 0) in
    let '(bSigHi1, bLo1, scale2) :=
      if Z.eqb (shr64 bAbsHi 48) 0 then
        let '(nhi, nlo, nclz) := norm_denormal bSigHi b_lo in (nhi, nlo, (scale1 + nclz) - 16)
      else (bSigHi, b_lo, scale1) in
    div_core signHi aExp bExp aSigHi1 aLo1 bSigHi1 bLo1 scale2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sf_dispatch (op a b : Z) : Z :=
  match op with
  | 0 => f128_of_d a
  | 1 => f128_to_d a
  | 2 => f128_le a b
  | 3 => f128_ge a b
  | 4 => f128_to_u32 a
  | 5 => fixunstfsi_a0 a
  | 6 => f128_of_u32 a
  | 7 => f128_of_i32 a
  | 8 => f128_mul a b
  | 9 => f128_add a b
  | 10 => f128_sub a b
  | _ => f128_div a b
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Example ex_of_d_15 : f128_of_d 0x3ff8000000000000 = 0x3fff8000000000000000000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_of_d_minsub : f128_of_d 0x0000000000000001 = 0x3bcd0000000000000000000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_of_d_maxsub : f128_of_d 0x800fffffffffffff = 0xbc00ffffffffffffe000000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_of_d_snan : f128_of_d 0x7ff0000000000001 = 0x7fff0000000000001000000000000000.  (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ex_to_d_15 : f128_to_d 0x3fff8000000000000000000000000000 = 0x3ff8000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_to_d_tie_even : f128_to_d 0x3fff0000000000000800000000000000 = 0x3ff0000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_to_d_tie_odd : f128_to_d 0x3fff0000000000001800000000000000 = 0x3ff0000000000002.
Proof. vm_compute. reflexivity. Qed.
Example ex_to_d_maxcarry : f128_to_d 0x43fefffffffffffff800000000000000 = 0x7ff0000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_to_d_nan : f128_to_d 0x7fff0000000000123000000000000000 = 0x7ff8000000000123.
Proof. vm_compute. reflexivity. Qed.
Example ex_to_d_halfminsub_sticky : f128_to_d 0x3bcc0000000000000000000000000001 = 0x0000000000000001.
Proof. vm_compute. reflexivity. Qed.
Example ex_to_d_sub_carry : f128_to_d 0x3c00ffffffffffffffffffffffffffff = 0x0010000000000000.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ex_le_lt : f128_le 0x3fff0000000000000000000000000000 0x40000000000000000000000000000000 = -1.
Proof. vm_compute. reflexivity. Qed.
Example ex_le_zero : f128_le 0x80000000000000000000000000000000 0 = 0.
Proof. vm_compute. reflexivity. Qed.
Example ex_le_nan : f128_le 0x7fff8000000000000000000000000000 0 = 1.
Proof. vm_compute. reflexivity. Qed.
Example ex_ge_nan : f128_ge 0 0x7fff0000000000000000000000000001 = -1.
Proof. vm_compute. reflexivity. Qed.
Example ex_ge_neg : f128_ge 0xc0000000000000000000000000000000 0xbfff0000000000000000000000000000 = -1.
Proof. vm_compute. reflexivity. Qed.
Example ex_ge_gt : f128_ge 0x40000000000000000000000000000000 0x3fff0000000000000000000000000000 = 1.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ex_to_u32_trunc : f128_to_u32 0x4000ffffffffffffffffffffffffffff = 3.
Proof. vm_compute. reflexivity. Qed.
Example ex_to_u32_neg : f128_to_u32 0xbfff0000000000000000000000000000 = 0.
Proof. vm_compute. reflexivity. Qed.
Example ex_to_u32_sat : f128_to_u32 0x401f0000000000000000000000000000 = 0xffffffff.
Proof. vm_compute. reflexivity. Qed.
Example ex_to_u32_sat_a0 : fixunstfsi_a0 0x7fff0000000000000000000000000000 = 0xffffffffffffffff.
Proof. vm_compute. reflexivity. Qed.
Example ex_to_u32_max : f128_to_u32 0x401efffffffe00000000000000000000 = 0xffffffff.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ex_of_u32_0 : f128_of_u32 0 = 0.
Proof. vm_compute. reflexivity. Qed.
Example ex_of_u32_max : f128_of_u32 0xffffffff = 0x401efffffffe00000000000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_of_i32_m5 : f128_of_i32 (-5) = 0xc0014000000000000000000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_of_i32_m5_pattern : f128_of_i32 0xfffffffb = f128_of_i32 (-5).      (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.
Example ex_of_i32_min : f128_of_i32 (-2147483648) = 0xc01e0000000000000000000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_of_i32_max : f128_of_i32 2147483647 = 0x401dfffffffc00000000000000000000.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ex_mul_15_15 :
  f128_mul 0x3fff8000000000000000000000000000 0x3fff8000000000000000000000000000
  = 0x40002000000000000000000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_mul_denorm_one : f128_mul 0x1 0x3fff0000000000000000000000000000 = 0x1.
Proof. vm_compute. reflexivity. Qed.
Example ex_mul_inf_zero : f128_mul 0x7fff0000000000000000000000000000 0x0 = 0x7fff8000000000000000000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_mul_round :
  f128_mul 0x3fff0000000000000000000000000001 0x3fff0000000000000000000000000001
  = 0x3fff0000000000000000000000000002.
Proof. vm_compute. reflexivity. Qed.
Example ex_mul_overflow :
  f128_mul 0xfffeffffffffffffffffffffffffffff 0x40000000000000000000000000000000
  = 0xffff0000000000000000000000000000.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ex_add_1_1 :
  f128_add 0x3fff0000000000000000000000000000 0x3fff0000000000000000000000000000
  = 0x40000000000000000000000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_add_tie_odd :
  f128_add 0x3fff0000000000000000000000000001 0x3f8e0000000000000000000000000000
  = 0x3fff0000000000000000000000000002.
Proof. vm_compute. reflexivity. Qed.
Example ex_sub_inf_inf :
  f128_sub 0x7fff0000000000000000000000000000 0x7fff0000000000000000000000000000
  = 0x7fff8000000000000000000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_add_snan :
  f128_add 0x7fff0000000000000000000000000001 0x3fff0000000000000000000000000000
  = 0x7fff8000000000000000000000000001.
Proof. vm_compute. reflexivity. Qed.
Example ex_add_subnormal : f128_add 1 1 = 2.
Proof. vm_compute. reflexivity. Qed.
Example ex_add_zeros : f128_add 0x80000000000000000000000000000000 0 = 0.
Proof. vm_compute. reflexivity. Qed.
Example ex_sub_cancel :
  f128_sub 0x3fff0000000000000000000000000000 0x3f8e0000000000000000000000000000
  = 0x3ffeffffffffffffffffffffffffffff.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ex_div_1_3 :
  f128_div 0x3fff0000000000000000000000000000 0x40008000000000000000000000000000
  = 0x3ffd5555555555555555555555555555.
Proof. vm_compute. reflexivity. Qed.
Example ex_div_u32_1e8 :
  f128_div 0x4019d6f3454000000000000000000000 0x40197d78400000000000000000000000
  = 0x3fff3c0ca4283de1b7eb69451304948f.
Proof. vm_compute. reflexivity. Qed.
Example ex_div_zero_zero : f128_div 0 0x80000000000000000000000000000000 = 0x7fff8000000000000000000000000000.
Proof. vm_compute. reflexivity. Qed.
Example ex_div_minsub_almost2 :   (* [comment removed for export] *)
  f128_div 0x00000000000000000000000000000001 0x3fffffffffffffffffffffffffffffff = 0.
Proof. vm_compute. reflexivity. Qed.
Example ex_div_sub_sub :
  f128_div 0x0000ffffffffffffffffffffffffffff 0x00000000000000000000000000000001
  = 0x406efffffffffffffffffffffffffffe.
Proof. vm_compute. reflexivity. Qed.
