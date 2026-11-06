(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import SoftFloat.
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

Definition signbitl (y : Z) : Z := Z.shiftr (hi64 y) 63.

Definition fpclassifyl (y : Z) : Z :=
  let hi := hi64 y in
  let lo := lo64 y in
  let e := Z.land (Z.shiftr hi 48) 0x7fff in
  let mant_hi := Z.land hi 0x0000ffffffffffff in
  if e =? 0 then (if negb (Z.lor lo mant_hi =? 0) then 3 else 2)
  else if e =? 0x7fff then (if negb (Z.lor lo mant_hi =? 0) then 0 else 1)
  else 4.

Fixpoint frexpl (fuel : nat) (x : Z) (e : Z) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      let hi := hi64 x in
      let se := Z.shiftr hi 48 in
      let ee := Z.land se 0x7fff in
      if ee =? 0 then

        if negb (f128_le x F128_ZERO =? 0) then
          let k := f128_of_d D_0x1p120 in
          let? (x, e) := frexpl fuel' (f128_mul x k) e in
          Some (x, e - 120)
        else Some (x, 0)
      else if ee =? 0x7fff then Some (x, e)
      else
        let e := ee - 0x3ffe in

        let hi := Z.lor (Z.lor (Z.land hi 0x8000000000000000) (Z.land hi 0x0000ffffffffffff))
                        0x3ffe000000000000 in
        Some (mk128 hi (lo64 x), e)
  end.

Definition fmt_fp_dig_body (s : list Z * Z * Z) : list Z * Z * Z :=
  let '(big, z, y) := s in
  let zv := f128_to_u32 y in
  let big := zupd big z zv in
  let k1e9 := f128_of_i32 1000000000 in
  let z := z + 1 in
  let zf := f128_of_u32 zv in
  let y := f128_mul k1e9 (f128_sub y zf) in
  (big, z, y).

Fixpoint fmt_fp_dig (fuel : nat) (s : list Z * Z * Z) {struct fuel} : option (list Z * Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      let s := fmt_fp_dig_body s in
      let '(big, z, y) := s in
      if negb (f128_le y F128_ZERO =? 0)
      then fmt_fp_dig fuel' s else Some s
  end.

Definition fmt_fp_strip_body (z : Z) : Z := z - 1.

Fixpoint fmt_fp_strip (fuel : nat) (big : list Z) (a z : Z) {struct fuel} : option Z :=
  match fuel with
  | O => None
  | S fuel' =>
      if (a <? z) && (znth big (z - 1) =? 0)
      then fmt_fp_strip fuel' big a (fmt_fp_strip_body z) else Some z
  end.

Definition fmt_fp_up_inner_body (sh : Z) (s : list Z * Z * Z) : list Z * Z * Z :=
  let '(big, d, carry) := s in
  let x := Z.shiftl (znth big d) sh + carry in
  let big := zupd big d (x mod 1000000000) in
  let carry := u32 (x / 1000000000) in
  (big, d - 1, carry).

Fixpoint fmt_fp_up_inner (sh : Z) (fuel : nat) (a : Z) (s : list Z * Z * Z) {struct fuel}
  : option (list Z * Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      let '(big, d, carry) := s in
      if a <=? d then fmt_fp_up_inner sh fuel' a (fmt_fp_up_inner_body sh s) else Some s
  end.

Definition fmt_fp_up_body (s : list Z * Z * Z * Z) : option (list Z * Z * Z * Z) :=
  let '(big, a, z, e2) := s in
  let carry := 0 in
  let sh := Z.min 29 e2 in
  let? (big, d, carry) := fmt_fp_up_inner sh BIG_FUEL a (big, z - 1, carry) in
  let '(a, big) := if negb (carry =? 0) then (a - 1, zupd big (a - 1) carry)
                   else (a, big) in
  let? z := fmt_fp_strip BIG_FUEL big a z in
  let e2 := e2 - sh in
  Some (big, a, z, e2).

Fixpoint fmt_fp_up (fuel : nat) (s : list Z * Z * Z * Z) {struct fuel}
  : option (list Z * Z * Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      let '(big, a, z, e2) := s in
      if 0 <? e2 then (let? s := fmt_fp_up_body s in fmt_fp_up fuel' s) else Some s
  end.

Definition fmt_fp_dn_inner_body (sh : Z) (s : list Z * Z * Z) : list Z * Z * Z :=
  let '(big, d, carry) := s in
  let rm := Z.land (znth big d) (Z.shiftl 1 sh - 1) in
  let big := zupd big d (u32 (Z.shiftr (znth big d) sh + carry)) in
  let carry := u32 (Z.shiftr 1000000000 sh * rm) in
  (big, d + 1, carry).

Fixpoint fmt_fp_dn_inner (sh : Z) (fuel : nat) (z : Z) (s : list Z * Z * Z) {struct fuel}
  : option (list Z * Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      let '(big, d, carry) := s in
      if d <? z then fmt_fp_dn_inner sh fuel' z (fmt_fp_dn_inner_body sh s) else Some s
  end.

Definition fmt_fp_dn_body (p t r : Z) (s : list Z * Z * Z * Z) : option (list Z * Z * Z * Z) :=
  let '(big, a, z, e2) := s in
  let carry := 0 in
  let sh := Z.min 9 (- e2) in
  let need := 1 + (u32 (p + LDBL_MANT_DIG / 3 + 8)) / 9 in
  let? (big, d, carry) := fmt_fp_dn_inner sh BIG_FUEL z (big, a, carry) in
  let a := if znth big a =? 0 then a + 1 else a in
  let '(big, z) := if negb (carry =? 0) then (zupd big z carry, z + 1)
                   else (big, z) in
  let b := if Z.lor t 32 =? CHR_f then r else a in
  let z := if need <? z - b then b + need else z in
  let e2 := e2 + sh in
  Some (big, a, z, e2).

Fixpoint fmt_fp_dn (fuel : nat) (p t r : Z) (s : list Z * Z * Z * Z) {struct fuel}
  : option (list Z * Z * Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      let '(big, a, z, e2) := s in
      if e2 <? 0 then (let? s := fmt_fp_dn_body p t r s in fmt_fp_dn fuel' p t r s) else Some s
  end.

Definition fmt_fp_cnt_body (s : Z * Z) : Z * Z := let '(i, e) := s in (i * 10, e + 1).

Fixpoint fmt_fp_cnt (fuel : nat) (v : Z) (s : Z * Z) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' => let '(i, e) := s in
               if i <=? v then fmt_fp_cnt fuel' v (fmt_fp_cnt_body s) else Some s
  end.

Definition fmt_fp_powi_body (s : Z * Z) : Z * Z := let '(i, j) := s in (i * 10, j + 1).

Fixpoint fmt_fp_powi (fuel : nat) (s : Z * Z) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' => let '(i, j) := s in
               if j <? 9 then fmt_fp_powi fuel' (fmt_fp_powi_body s) else Some s
  end.

Definition fmt_fp_carry_body (s : list Z * Z * Z) : list Z * Z * Z :=
  let '(big, d, a) := s in
  let big := zupd big d 0 in let d := d - 1 in
  let '(a, big) := if d <? a then (a - 1, zupd big (a - 1) 0) else (a, big) in
  let big := zupd big d (u32 (znth big d + 1)) in
  (big, d, a).

Fixpoint fmt_fp_carry (fuel : nat) (s : list Z * Z * Z) {struct fuel} : option (list Z * Z * Z) :=
  match fuel with
  | O => None
  | S fuel' => let '(big, d, a) := s in
               if 999999999 <? znth big d then fmt_fp_carry fuel' (fmt_fp_carry_body s) else Some s
  end.

Definition fmt_fp_tz_body (s : Z * Z) : Z * Z := let '(i, j) := s in (i * 10, j + 1).

Fixpoint fmt_fp_tz (fuel : nat) (v : Z) (s : Z * Z) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' => let '(i, j) := s in
               if v mod i =? 0 then fmt_fp_tz fuel' v (fmt_fp_tz_body s) else Some s
  end.

Definition fmt_fp_epad_body (s : Z * list Z) : Z * list Z :=
  let '(estr, ebuf0) := s in
  let estr := estr - 1 in (estr, zupd ebuf0 estr CHR_0).

Fixpoint fmt_fp_epad (fuel : nat) (s : Z * list Z) {struct fuel} : option (Z * list Z) :=
  match fuel with
  | O => None
  | S fuel' => let '(estr, ebuf0) := s in
               if 12 - estr <? 2 then fmt_fp_epad fuel' (fmt_fp_epad_body s) else Some s
  end.

Definition fmt_fp_zfill_body (st : Z * list Z) : Z * list Z :=
  let '(s, buf) := st in
  let s := s - 1 in (s, zupd buf s CHR_0).

Fixpoint fmt_fp_zfill (fuel : nat) (st : Z * list Z) {struct fuel} : option (Z * list Z) :=
  match fuel with
  | O => None
  | S fuel' => let '(s, buf) := st in
               if 0 <? s then fmt_fp_zfill fuel' (fmt_fp_zfill_body st) else Some st
  end.

Definition fmt_fp_len (t l e : Z) : option (flow (Z * list Z * Z)) :=
  if Z.lor t 32 =? CHR_f then
    if INT_MAX - l <? e then Some (Ret (-1))
    else Some (Cont ((if 0 <? e then l + e else l), zrepeat 0 12, 12))
  else
    let ebuf0 := zrepeat 0 12 in
    let? (estr, ebuf0) := fmt_u (if e <? 0 then - e else e) ebuf0 12 in
    let? (estr, ebuf0) := fmt_fp_epad EPAD_FUEL (estr, ebuf0) in
    let estr := estr - 1 in
    let ebuf0 := zupd ebuf0 estr (if e <? 0 then CHR_minus else CHR_plus) in
    let estr := estr - 1 in
    let ebuf0 := zupd ebuf0 estr (u8 t) in
    if INT_MAX - l <? 12 - estr then Some (Ret (-1))
    else Some (Cont (l + (12 - estr), ebuf0, estr)).

Definition fmt_fp_fint_body (big : list Z) (a : Z) (st : Z * list Z) : option (Z * list Z) :=
  let '(d, o) := st in
  let buf := zrepeat 0 37 in
  let? (s, buf) := fmt_u (znth big d) buf 9 in
  let? (s, buf) :=
    if negb (d =? a) then fmt_fp_zfill ZFILL_FUEL (s, buf)
    else if s =? 9 then Some (s - 1, zupd buf (s - 1) CHR_0)
    else Some (s, buf) in
  let o := out o (zsub buf s (9 - s)) in
  Some (d + 1, o).

Fixpoint fmt_fp_fint (fuel : nat) (big : list Z) (a r : Z) (st : Z * list Z) {struct fuel}
  : option (Z * list Z) :=
  match fuel with
  | O => None
  | S fuel' => let '(d, o) := st in
               if d <=? r then (let? st := fmt_fp_fint_body big a st in fmt_fp_fint fuel' big a r st)
               else Some st
  end.

Definition fmt_fp_ffrac_body (big : list Z) (st : Z * Z * list Z) : option (Z * Z * list Z) :=
  let '(d, p, o) := st in
  let buf := zrepeat 0 37 in
  let? (s, buf) := fmt_u (znth big d) buf 9 in
  let? (s, buf) := fmt_fp_zfill ZFILL_FUEL (s, buf) in
  let o := out o (zsub buf s (Z.min 9 p)) in
  Some (d + 1, p - 9, o).

Fixpoint fmt_fp_ffrac (fuel : nat) (big : list Z) (z : Z) (st : Z * Z * list Z) {struct fuel}
  : option (Z * Z * list Z) :=
  match fuel with
  | O => None
  | S fuel' => let '(d, p, o) := st in
               if (d <? z) && (0 <? p)
               then (let? st := fmt_fp_ffrac_body big st in fmt_fp_ffrac fuel' big z st)
               else Some st
  end.

Definition fmt_fp_emit_f (o : list Z) (big : list Z) (a r z p fl : Z) : option (list Z) :=
  let a := if r <? a then r else a in
  let? (d, o) := fmt_fp_fint BIG_FUEL big a r (a, o) in
  let o := if negb (p =? 0) || negb (Z.land fl ALT_FORM =? 0) then out o [CHR_dot] else o in
  let? (d, p, o) := fmt_fp_ffrac BIG_FUEL big z (d, p, o) in
  pad o CHR_0 (p + 9) 9 0.

Definition fmt_fp_eloop_body (big : list Z) (a fl : Z) (st : Z * Z * list Z) : option (Z * Z * list Z) :=
  let '(d, p, o) := st in
  let buf := zrepeat 0 37 in
  let? (s, buf) := fmt_u (znth big d) buf 9 in
  let '(s, buf) := if s =? 9 then (s - 1, zupd buf (s - 1) CHR_0) else (s, buf) in
  let? (s, buf, o) :=
    if negb (d =? a) then (let? (s, buf) := fmt_fp_zfill ZFILL_FUEL (s, buf) in Some (s, buf, o))
    else
      (let o := out o (zsub buf s 1) in
       let s := s + 1 in
       let o := if (0 <? p) || negb (Z.land fl ALT_FORM =? 0) then out o [CHR_dot] else o in
       Some (s, buf, o)) in
  let o := out o (zsub buf s (Z.min (9 - s) p)) in
  let p := p - (9 - s) in
  Some (d + 1, p, o).

Fixpoint fmt_fp_eloop (fuel : nat) (big : list Z) (a z fl : Z) (st : Z * Z * list Z) {struct fuel}
  : option (Z * Z * list Z) :=
  match fuel with
  | O => None
  | S fuel' => let '(d, p, o) := st in
               if (d <? z) && (0 <=? p)
               then (let? st := fmt_fp_eloop_body big a fl st in fmt_fp_eloop fuel' big a z fl st)
               else Some st
  end.

Definition fmt_fp_emit_e (o : list Z) (big : list Z) (a z p fl : Z) (ebuf0 : list Z) (estr : Z)
  : option (list Z) :=
  let z := if z <=? a then a + 1 else z in
  let? (d, p, o) := fmt_fp_eloop BIG_FUEL big a z fl (a, p, o) in
  let? o := pad o CHR_0 (p + 18) 18 0 in
  Some (out o (zsub ebuf0 estr (12 - estr))).

Definition fmt_fp (o : list Z) (y w p fl t : Z) : option (list Z * Z) :=
  let big := zrepeat 0 128 in
  let e2 := 0 in
  let prefix := 0 in
  let pl := 1 in
  let '(y, prefix, pl) :=
    if negb (signbitl y =? 0) then (Z.lxor y F128_SIGNBIT, prefix, pl)
    else if negb (Z.land fl MARK_POS =? 0) then (y, prefix + 3, pl)
    else if negb (Z.land fl PAD_POS =? 0) then (y, prefix + 6, pl)
    else (y, prefix + 1, 0) in
  if fpclassifyl y <=? 1 then None
  else

  let? (fr, e2) := frexpl FREXPL_FUEL y e2 in
  let two := f128_of_i32 2 in
  let y := f128_mul fr two in
  let ynz := negb (f128_le y F128_ZERO =? 0) in
  let e2 := if ynz then e2 - 1 else e2 in
  let p := if p <? 0 then 6 else p in
  let '(y, e2) := if ynz
                  then (f128_mul y (f128_of_d D_0x1p28), e2 - 28)
                  else (y, e2) in
  let a := if e2 <? 0 then 0 else 128 - 5 - 1 in
  let r := a in
  let z := a in
  let? (big, z, y) := fmt_fp_dig DIG_FUEL (big, z, y) in
  let? (big, a, z, e2) := fmt_fp_up UP_FUEL (big, a, z, e2) in
  let? (big, a, z, e2) := fmt_fp_dn DN_FUEL p t r (big, a, z, e2) in
  let? e := if a <? z
            then (let? (i, e) := fmt_fp_cnt TEN_FUEL (znth big a) (10, 9 * (r - a)) in Some e)
            else Some 0 in

  let j := p - (if negb (Z.lor t 32 =? CHR_f) then 1 else 0) * e
             - (if (Z.lor t 32 =? CHR_g) && negb (p =? 0) then 1 else 0) in
  let? (big, a, z, e) :=
    if j <? 9 * (z - r - 1) then
      let d := r + 1 + (Z.quot (j + 9 * LDBL_MAX_EXP) 9 - LDBL_MAX_EXP) in
      let j := j + 9 * LDBL_MAX_EXP in
      let j := Z.rem j 9 in
      let? (i, j) := fmt_fp_powi TEN_FUEL (10, j + 1) in
      let x := (znth big d) mod i in
      let? (big, a, d, e) :=
        if negb (x =? 0) || negb (d + 1 =? z) then
          let round := f128_div (f128_of_i32 2) K_LDBL_EPSILON in
          let round :=
            if negb (Z.land (znth big d / i) 1 =? 0)
               || ((i =? 1000000000) && (a <? d) && negb (Z.land (znth big (d - 1)) 1 =? 0))
            then f128_add round (f128_of_i32 2)
            else round in
          let small :=
            if x <? Z.quot i 2 then f128_of_d D_0_5
            else if (x =? Z.quot i 2) && (d + 1 =? z) then f128_of_d D_1_0
            else f128_of_d D_1_5 in
          let '(round, small) :=
            if negb (pl =? 0) && (znth PREFIX_STR prefix =? CHR_minus) then
              let m1 := f128_of_i32 (-1) in
              let round := f128_mul round m1 in
              let small := f128_mul small m1 in
              (round, small)
            else (round, small) in
          let big := zupd big d (znth big d - x) in

          if negb (f128_le (f128_add round small) round =? 0) then
            let big := zupd big d (u32 (znth big d + i)) in
            let? (big, d, a) := fmt_fp_carry BIG_FUEL (big, d, a) in
            let? (i, e) := fmt_fp_cnt TEN_FUEL (znth big a) (10, 9 * (r - a)) in
            Some (big, a, d, e)
          else Some (big, a, d, e)
        else Some (big, a, d, e) in
      let z := if d + 1 <? z then d + 1 else z in
      Some (big, a, z, e)
    else Some (big, a, z, e) in
  let? z := fmt_fp_strip BIG_FUEL big a z in
  let? (p, t) :=
    if Z.lor t 32 =? CHR_g then
      let p := if p =? 0 then p + 1 else p in
      let '(t, p) := if (e <? p) && (-4 <=? e) then (t - 1, p - (e + 1))
                     else (t - 2, p - 1) in
      if Z.land fl ALT_FORM =? 0 then
        let? j := if (a <? z) && negb (znth big (z - 1) =? 0)
                  then (let? (i, j) := fmt_fp_tz TEN_FUEL (znth big (z - 1)) (10, 0) in Some j)
                  else Some 9 in
        let p := if Z.lor t 32 =? CHR_f
                 then Z.min p (Z.max 0 (9 * (z - r - 1) - j))
                 else Z.min p (Z.max 0 (9 * (z - r - 1) + e - j)) in
        Some (p, t)
      else Some (p, t)
    else Some (p, t) in
  let palt := if negb (p =? 0) || negb (Z.land fl ALT_FORM =? 0) then 1 else 0 in
  if INT_MAX - 1 - palt <? p then Some (o, -1) else
  let l := 1 + p + palt in
  let? len := fmt_fp_len t l e in
  match len with
  | Ret v => Some (o, v)
  | Cont (l, ebuf0, estr) =>
  if INT_MAX - pl <? l then Some (o, -1) else
  let? o := pad o CHR_sp w (pl + l) fl in
  let o := out o (zsub PREFIX_STR prefix pl) in
  let? o := pad o CHR_0 w (pl + l) (Z.lxor fl ZERO_PAD) in
  let? o := if Z.lor t 32 =? CHR_f
            then fmt_fp_emit_f o big a r z p fl
            else fmt_fp_emit_e o big a z p fl ebuf0 estr in
  let? o := pad o CHR_sp w (pl + l) (Z.lxor fl LEFT_ADJ) in
  Some (o, Z.max w (pl + l))
  end.

Definition fmt_g (d : Z) (prec : Z) : option (list Z * Z) :=
  let y := f128_of_d d in
  let? (o, l) := fmt_fp [] y 1 prec 0 CHR_g in
  Some (o, if l <? 0 then -1 else zlength o).

Definition fmt_d (x : Z) : option (list Z * Z) :=
  let o := [] in
  let buf := zrepeat 0 24 in
  let z := 24 in
  let prefix := 0 in
  let w := 0 in let p := -1 in let fl := 0 in
  let cnt := 0 in
  let argi := u64 x in
  let pl := 1 in
  let '(argi, prefix, pl) :=
    if INTMAX_MAX <? argi then (u64 (- argi), prefix, pl)
    else if negb (Z.land fl MARK_POS =? 0) then (argi, prefix + 1, pl)
    else if negb (Z.land fl PAD_POS =? 0) then (argi, prefix + 2, pl)
    else (argi, prefix, 0) in
  let? (a, buf) := fmt_u argi buf z in
  let '(a, p) :=
    if (argi =? 0) && (p =? 0) then (z, p)
    else (a, Z.max p (z - a + (if argi =? 0 then 1 else 0))) in
  let p := if p <? z - a then z - a else p in
  if INT_MAX - pl <? p then Some (o, -1) else
  let w := if w <? pl + p then pl + p else w in
  if INT_MAX - cnt <? w then Some (o, -1) else
  let? o := pad o CHR_sp w (pl + p) fl in
  let o := out o (zsub PREFIX_D prefix pl) in
  let? o := pad o CHR_0 w (pl + p) (Z.lxor fl ZERO_PAD) in
  let? o := pad o CHR_0 p (z - a) 0 in
  let o := out o (zsub buf a (z - a)) in
  let? o := pad o CHR_sp w (pl + p) (Z.lxor fl LEFT_ADJ) in
  let l := w in
  let cnt := cnt + l in
  Some (o, cnt).

Example fmt_g_ex1 : fmt_g 0x3fb999999999999a 15 = Some ([48; 46; 49], 3).
Proof. vm_compute. reflexivity. Qed.
Example fmt_g_ex2 :
  fmt_g 0x3fb999999999999a 17
  = Some ([48; 46; 49; 48; 48; 48; 48; 48; 48; 48; 48; 48; 48; 48; 48; 48; 48; 48; 49], 19).
Proof. vm_compute. reflexivity. Qed.

Example fmt_g_ex3 : fmt_g 0x7e37e43c8800759c 15 = Some ([49; 101; 43; 51; 48; 48], 6).
Proof. vm_compute. reflexivity. Qed.
Example fmt_d_ex1 : fmt_d (-2147483648) = Some ([45; 50; 49; 52; 55; 52; 56; 51; 54; 52; 56], 11).
Proof. vm_compute. reflexivity. Qed.
Example fmt_d_ex2 : fmt_d 0 = Some ([48], 1).
Proof. vm_compute. reflexivity. Qed.
