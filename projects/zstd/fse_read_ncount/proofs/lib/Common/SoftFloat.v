(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Definition ONES64 : Z := 0xffffffffffffffff.
Definition M32 : Z := 0xffffffff.
Definition SIGN64 : Z := 0x8000000000000000.
Definition wrap64 (x : Z) : Z := Z.land x ONES64.
Lemma wrap64_mod : forall x, wrap64 x = x mod 2^64.
Proof. intro x. unfold wrap64. change ONES64 with (Z.ones 64). apply Z.land_ones. lia. Qed.
Lemma wrap64_range : forall x, 0 <= wrap64 x < 2^64.
Proof. intro x. rewrite wrap64_mod. apply Z.mod_pos_bound. lia. Qed.
Definition b2z (b : bool) : Z := if b then 1 else 0.
Definition lo64 (x : Z) : Z := wrap64 x.
Definition hi64 (x : Z) : Z := wrap64 (Z.shiftr x 64).
Definition mk128 (hi lo : Z) : Z := Z.lor (Z.shiftl hi 64) lo.
Definition add64 (x y : Z) : Z := wrap64 (x + y).
Definition sub64 (x y : Z) : Z := wrap64 (x - y).
Definition mul64 (x y : Z) : Z := wrap64 (x * y).
Definition mulhu (x y : Z) : Z := Z.shiftr (x * y) 64.
Definition shl64 (x n : Z) : Z := wrap64 (Z.shiftl x n).
Notation shr64 := Z.shiftr (only parsing).
Definition not64 (x : Z) : Z := Z.lxor x ONES64.
Definition ltu64 (x y : Z) : Z := b2z (x <? y).
Definition eqz64 (x : Z) : Z := b2z (x =? 0).
Definition nez64 (x : Z) : Z := b2z (negb (x =? 0)).
Definition is_neg64 (x : Z) : bool := negb (Z.shiftr x 63 =? 0).
Definition lt_s64 (a b : Z) : bool := (Z.lxor a SIGN64) <? (Z.lxor b SIGN64).
Definition sra63 (x : Z) : Z := if is_neg64 x then ONES64 else 0.
Notation smask64 := sra63 (only parsing).
Definition zext32 (x : Z) : Z := Z.land x M32.
Definition sext32 (x : Z) : Z := sub64 (Z.lxor (Z.land x M32) 0x80000000) 0x80000000.
Definition srliw (x k : Z) : Z := sext32 (Z.shiftr (Z.land x M32) k).
Definition MASK48 : Z := 0x0000ffffffffffff.
Definition MASKLO : Z := 0xffffffffffffffff.
Definition ABS_HI : Z := 0x7fffffffffffffff.
Definition INF_HI : Z := 0x7fff000000000000.
Definition QUIET_HI : Z := 0x0000800000000000.
Definition QNAN_HI : Z := 0x7fff800000000000.
Definition IMPLICIT_HI : Z := 0x0001000000000000.
Definition clz64_mirror (x : Z) : Z :=
let x1 := Z.lor x (shr64 x 1) in
let x2 := Z.lor x1 (shr64 x1 2) in
let x3 := Z.lor x2 (shr64 x2 4) in
let x4 := Z.lor x3 (shr64 x3 8) in
let x5 := Z.lor x4 (shr64 x4 16) in
let x6 := Z.lor x5 (shr64 x5 32) in
let y := not64 x6 in
let c1 := sub64 y (Z.land (shr64 y 1) 0x5555555555555555) in
let c2 := add64 (Z.land c1 0x3333333333333333) (Z.land (shr64 c1 2) 0x3333333333333333) in
let c3 := Z.land (add64 c2 (shr64 c2 4)) 0x0f0f0f0f0f0f0f0f in
let c4 := shr64 (mul64 c3 0x0101010101010101) 56 in
c4.
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
