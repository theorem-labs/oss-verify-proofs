(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith Bool List Lia.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.
Import QCiC.Mq1. Import QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation "'let?' x ':=' e 'in' k" :=
(match e with Some x => k | None => None end)
(at level 200, x pattern, e at level 100, k at level 200, only parsing).

Inductive flow (A : Type) : Type := Ret : Z -> flow A | Cont : A -> flow A.
Arguments Ret {A} _. Arguments Cont {A} _.

Definition zsub (l : list Z) (i n : Z) : list Z :=
firstn (Z.to_nat n) (skipn (Z.to_nat i) l).

Fixpoint list_eqb (l1 l2 : list Z) : bool :=
match l1, l2 with
| [], [] => true
| x :: t1, y :: t2 => (x =? y) && list_eqb t1 t2
| _, _ => false
end.

Definition ALT_FORM : Z := 8.
Definition ZERO_PAD : Z := 65536.
Definition LEFT_ADJ : Z := 8192.
Definition PAD_POS  : Z := 1.
Definition MARK_POS : Z := 2048.
Definition INT_MAX  : Z := 2147483647.
Definition INTMAX_MAX : Z := 9223372036854775807.
Definition LDBL_MANT_DIG : Z := 113.
Definition LDBL_MAX_EXP  : Z := 16384.

Definition F128_ZERO    : Z := 0.
Definition F128_SIGNBIT : Z := 0x80000000000000000000000000000000.
Definition K_LDBL_EPSILON : Z := 0x3f8f0000000000000000000000000000.

Definition D_0x1p28  : Z := 0x41b0000000000000.
Definition D_0_5     : Z := 0x3fe0000000000000.
Definition D_1_0     : Z := 0x3ff0000000000000.
Definition D_1_5     : Z := 0x3ff8000000000000.
Definition D_0x1p120 : Z := 0x4770000000000000.

Definition PREFIX_STR : list Z := [45; 48; 88; 43; 48; 88; 32; 48; 88; 45; 48; 120; 43; 48; 120; 32; 48; 120].

Definition PREFIX_D : list Z := [45; 43; 32; 32; 32; 48; 88; 48; 120].

Definition CHR_f : Z := 102.  Definition CHR_g : Z := 103.
Definition CHR_0 : Z := 48.   Definition CHR_dot : Z := 46.
Definition CHR_plus : Z := 43. Definition CHR_minus : Z := 45. Definition CHR_sp : Z := 32.

Definition BIG_FUEL := 130%nat.
Definition DIG_FUEL := 16%nat.
Definition UP_FUEL := 40%nat.
Definition DN_FUEL := 130%nat.
Definition TEN_FUEL := 12%nat.
Definition EPAD_FUEL := 4%nat.
Definition ZFILL_FUEL := 12%nat.
Definition FMT_U_FUEL := 21%nat.
Definition PAD_FUEL := 64%nat.

Definition FREXPL_FUEL := 2%nat.

Definition out (o bytes : list Z) : list Z := o ++ bytes.

Definition pad_loop_body (c : Z) (s : Z * list Z) : Z * list Z :=
let '(l, o) := s in
let o := out o (zrepeat c 256) in
(l - 256, o).

Fixpoint pad_loop (c : Z) (fuel : nat) (s : Z * list Z) {struct fuel} : option (Z * list Z) :=
match fuel with
| O => None
| S fuel' =>
let '(l, o) := s in
if 256 <=? l then pad_loop c fuel' (pad_loop_body c s) else Some s
end.

Definition pad (o : list Z) (c w l fl : Z) : option (list Z) :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l) then Some o
else
let l := w - l in
let? (l, o) := pad_loop c PAD_FUEL (l, o) in
Some (out o (zrepeat c l)).

Definition fmt_u_loop_body (st : Z * Z * list Z) : Z * Z * list Z :=
let '(y, s, b) := st in
let s := s - 1 in
let b := zupd b s (CHR_0 + y mod 10) in
let y := y / 10 in
(y, s, b).

Fixpoint fmt_u_loop (fuel : nat) (st : Z * Z * list Z) {struct fuel} : option (Z * Z * list Z) :=
match fuel with
| O => None
| S fuel' =>
let '(y, s, b) := st in
if negb (y =? 0) then fmt_u_loop fuel' (fmt_u_loop_body st) else Some st
end.

Definition fmt_u (x : Z) (b : list Z) (s : Z) : option (Z * list Z) :=
let? (y, s, b) := fmt_u_loop FMT_U_FUEL (x, s, b) in
Some (s, b).
End Mq0.

From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF.Mq1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation "'let?' x ':=' e 'in' k" :=
(match e with Some x => k | None => None end)
(at level 200, x pattern, e at level 100, k at level 200, only parsing).

Inductive flow (A : Type) : Type := Ret : Z -> flow A | Cont : A -> flow A.
Arguments Ret {A} _. Arguments Cont {A} _.

Definition zsub (l : list Z) (i n : Z) : list Z :=
firstn (Z.to_nat n) (skipn (Z.to_nat i) l).

Fixpoint list_eqb (l1 l2 : list Z) : bool :=
match l1, l2 with
| [], [] => true
| x :: t1, y :: t2 => (x =? y) && list_eqb t1 t2
| _, _ => false
end.

Definition ALT_FORM : Z := 8.
Definition ZERO_PAD : Z := 65536.
Definition LEFT_ADJ : Z := 8192.
Definition PAD_POS  : Z := 1.
Definition MARK_POS : Z := 2048.
Definition INT_MAX  : Z := 2147483647.
Definition INTMAX_MAX : Z := 9223372036854775807.
Definition LDBL_MANT_DIG : Z := 113.
Definition LDBL_MAX_EXP  : Z := 16384.

Definition F128_ZERO    : Z := 0.
Definition F128_SIGNBIT : Z := 0x80000000000000000000000000000000.
Definition K_LDBL_EPSILON : Z := 0x3f8f0000000000000000000000000000.

Definition D_0x1p28  : Z := 0x41b0000000000000.
Definition D_0_5     : Z := 0x3fe0000000000000.
Definition D_1_0     : Z := 0x3ff0000000000000.
Definition D_1_5     : Z := 0x3ff8000000000000.
Definition D_0x1p120 : Z := 0x4770000000000000.

Definition PREFIX_STR : list Z := [45; 48; 88; 43; 48; 88; 32; 48; 88; 45; 48; 120; 43; 48; 120; 32; 48; 120].

Definition PREFIX_D : list Z := [45; 43; 32; 32; 32; 48; 88; 48; 120].

Definition CHR_f : Z := 102.  Definition CHR_g : Z := 103.
Definition CHR_0 : Z := 48.   Definition CHR_dot : Z := 46.
Definition CHR_plus : Z := 43. Definition CHR_minus : Z := 45. Definition CHR_sp : Z := 32.

Definition BIG_FUEL := 130%nat.
Definition DIG_FUEL := 16%nat.
Definition UP_FUEL := 40%nat.
Definition DN_FUEL := 130%nat.
Definition TEN_FUEL := 12%nat.
Definition EPAD_FUEL := 4%nat.
Definition ZFILL_FUEL := 12%nat.
Definition FMT_U_FUEL := 21%nat.
Definition PAD_FUEL := 64%nat.

Definition FREXPL_FUEL := 2%nat.

Definition out (o bytes : list Z) : list Z := o ++ bytes.

Definition pad_loop_body (c : Z) (s : Z * list Z) : Z * list Z :=
let '(l, o) := s in
let o := out o (zrepeat c 256) in
(l - 256, o).

Fixpoint pad_loop (c : Z) (fuel : nat) (s : Z * list Z) {struct fuel} : option (Z * list Z) :=
match fuel with
| O => None
| S fuel' =>
let '(l, o) := s in
if 256 <=? l then pad_loop c fuel' (pad_loop_body c s) else Some s
end.

Definition pad (o : list Z) (c w l fl : Z) : option (list Z) :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l) then Some o
else
let l := w - l in
let? (l, o) := pad_loop c PAD_FUEL (l, o) in
Some (out o (zrepeat c l)).

Definition fmt_u_loop_body (st : Z * Z * list Z) : Z * Z * list Z :=
let '(y, s, b) := st in
let s := s - 1 in
let b := zupd b s (CHR_0 + y mod 10) in
let y := y / 10 in
(y, s, b).

Fixpoint fmt_u_loop (fuel : nat) (st : Z * Z * list Z) {struct fuel} : option (Z * Z * list Z) :=
match fuel with
| O => None
| S fuel' =>
let '(y, s, b) := st in
if negb (y =? 0) then fmt_u_loop fuel' (fmt_u_loop_body st) else Some st
end.

Definition fmt_u (x : Z) (b : list Z) (s : Z) : option (Z * list Z) :=
let? (y, s, b) := fmt_u_loop FMT_U_FUEL (x, s, b) in
Some (s, b).
