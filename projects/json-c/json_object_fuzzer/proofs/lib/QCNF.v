(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Stdlib Require ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith.
Open Scope Z_scope.

Definition FMT_FP_DEPTH : Z := 4640.
End Mq0.
From Stdlib Require Bool List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ONES64 : Z := 0xffffffffffffffff.
Definition M32    : Z := 0xffffffff.
Definition M128   : Z := 0x100000000000000000000000000000000.
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
Notation u64_of_s := wrap64 (only parsing).
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

Definition MASK48      : Z := 0x0000ffffffffffff.
Definition MASKLO      : Z := 0xffffffffffffffff.
Definition ABS_HI      : Z := 0x7fffffffffffffff.
Definition INF_HI      : Z := 0x7fff000000000000.
Definition QUIET_HI    : Z := 0x0000800000000000.
Definition QNAN_HI     : Z := 0x7fff800000000000.
Definition IMPLICIT_HI : Z := 0x0001000000000000.
Definition IMPL3_HI    : Z := 0x0008000000000000.
Definition SPEC_K      : Z := 0x8001000000000000.
Definition HALF60      : Z := 0x0800000000000000.
Definition DQUIET      : Z := 0x0008000000000000.
Definition C_HW        : Z := 0x7504f33300000000.
Definition X_ADJ       : Z := 0xffffffffffffc999.
Definition EXPK        : Z := 0xffffffffffff8001.
Definition EXPK2       : Z := 0xffffffffffff8002.

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

Definition clz128_mirror (hi lo : Z) : Z :=
let hz := b2z (hi =? 0) in
let word := if hi =? 0 then lo else hi in
Z.lor (clz64_mirror word) (Z.shiftl hz 6).

Definition shl128_mirror (hi lo s : Z) : Z * Z :=
let n := zext32 s in
let d := sub64 n 64 in
let nhi := if is_neg64 d
then Z.lor (shl64 hi (Z.land s 63)) (shr64 (shr64 lo 1) (Z.land (not64 n) 63))
else shl64 lo (Z.land n 63) in
let nlo := Z.land (sra63 d) (shl64 lo (Z.land s 63)) in
(nhi, nlo).

Definition norm_denormal (sigHi sigLo : Z) : Z * Z * Z :=
let clz := clz128_mirror sigHi sigLo in
let sh := sub64 clz 15 in
let '(hi, lo) := shl128_mirror sigHi sigLo sh in
(hi, lo, clz).

Definition normalize_mirror (hi lo : Z) : Z * Z * Z :=
let '(nhi, nlo, clz) := norm_denormal hi lo in
(nhi, nlo, sub64 16 clz).

End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith.
Open Scope Z_scope.

Definition FMT_FP_DEPTH : Z := 4640.
End Mq2.

From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ONES64 : Z := 0xffffffffffffffff.
Definition M32    : Z := 0xffffffff.
Definition M128   : Z := 0x100000000000000000000000000000000.
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
Notation u64_of_s := wrap64 (only parsing).
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

Definition MASK48      : Z := 0x0000ffffffffffff.
Definition MASKLO      : Z := 0xffffffffffffffff.
Definition ABS_HI      : Z := 0x7fffffffffffffff.
Definition INF_HI      : Z := 0x7fff000000000000.
Definition QUIET_HI    : Z := 0x0000800000000000.
Definition QNAN_HI     : Z := 0x7fff800000000000.
Definition IMPLICIT_HI : Z := 0x0001000000000000.
Definition IMPL3_HI    : Z := 0x0008000000000000.
Definition SPEC_K      : Z := 0x8001000000000000.
Definition HALF60      : Z := 0x0800000000000000.
Definition DQUIET      : Z := 0x0008000000000000.
Definition C_HW        : Z := 0x7504f33300000000.
Definition X_ADJ       : Z := 0xffffffffffffc999.
Definition EXPK        : Z := 0xffffffffffff8001.
Definition EXPK2       : Z := 0xffffffffffff8002.

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

Definition clz128_mirror (hi lo : Z) : Z :=
let hz := b2z (hi =? 0) in
let word := if hi =? 0 then lo else hi in
Z.lor (clz64_mirror word) (Z.shiftl hz 6).

Definition shl128_mirror (hi lo s : Z) : Z * Z :=
let n := zext32 s in
let d := sub64 n 64 in
let nhi := if is_neg64 d
then Z.lor (shl64 hi (Z.land s 63)) (shr64 (shr64 lo 1) (Z.land (not64 n) 63))
else shl64 lo (Z.land n 63) in
let nlo := Z.land (sra63 d) (shl64 lo (Z.land s 63)) in
(nhi, nlo).

Definition norm_denormal (sigHi sigLo : Z) : Z * Z * Z :=
let clz := clz128_mirror sigHi sigLo in
let sh := sub64 clz 15 in
let '(hi, lo) := shl128_mirror sigHi sigLo sh in
(hi, lo, clz).

Definition normalize_mirror (hi lo : Z) : Z * Z * Z :=
let '(nhi, nlo, clz) := norm_denormal hi lo in
(nhi, nlo, sub64 16 clz).

