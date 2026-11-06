(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Notation "'let?' x ':=' e 'in' k" :=
  (match e with Some x => k | None => None end)
  (at level 200, x pattern, e at level 100, k at level 200, only parsing).

(* [comment removed for export] *)
Definition ffp_G (o : list Z) (w fl t p prefix pl : Z) (big : list Z) (a r z : Z) : option (list Z * Z) :=
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
      let '(t, p) := if (e <? p) && (-4 <=? e) then (t - 1, p - (e + 1)) else (t - 2, p - 1) in
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

(* [comment removed for export] *)
Definition ffp_R (t p prefix pl : Z) (big : list Z) (a r z e j : Z) : option (list Z * Z * Z * Z) :=
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
    else Some (big, a, z, e).

(* [comment removed for export] *)
Definition ffp_H (o : list Z) (w fl t p prefix pl : Z) (big : list Z) (a r z e : Z) : option (list Z * Z) :=
  let? z := fmt_fp_strip BIG_FUEL big a z in
  let? (p, t) :=
    if Z.lor t 32 =? CHR_g then
      let p := if p =? 0 then p + 1 else p in
      let '(t, p) := if (e <? p) && (-4 <=? e) then (t - 1, p - (e + 1)) else (t - 2, p - 1) in
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

(* [comment removed for export] *)
Definition ffp_e (big : list Z) (a r z : Z) : option Z :=
  if a <? z
  then (let? (i, e) := fmt_fp_cnt TEN_FUEL (znth big a) (10, 9 * (r - a)) in Some e)
  else Some 0.
Definition ffp_j (t p e : Z) : Z :=
  p - (if negb (Z.lor t 32 =? CHR_f) then 1 else 0) * e
    - (if (Z.lor t 32 =? CHR_g) && negb (p =? 0) then 1 else 0).

Lemma ffp_G_eq : forall o w fl t p prefix pl big a r z,
  ffp_G o w fl t p prefix pl big a r z =
  (let? e := ffp_e big a r z in
   let j := ffp_j t p e in
   let? (big, a, z, e) := ffp_R t p prefix pl big a r z e j in
   ffp_H o w fl t p prefix pl big a r z e).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition ffp_F (o : list Z) (w fl t p prefix pl : Z) (big : list Z) (a r z e2 : Z) : option (list Z * Z) :=
  let? (big, a, z, e2) := fmt_fp_dn DN_FUEL p t r (big, a, z, e2) in
  ffp_G o w fl t p prefix pl big a r z.

(* [comment removed for export] *)
Definition ffp_E (o : list Z) (w fl t p prefix pl : Z) (big : list Z) (a r z e2 : Z) : option (list Z * Z) :=
  let? (big, a, z, e2) := fmt_fp_up UP_FUEL (big, a, z, e2) in
  ffp_F o w fl t p prefix pl big a r z e2.

(* [comment removed for export] *)
Definition ffp_D (o : list Z) (w fl t : Z) (y e2 p prefix pl : Z) : option (list Z * Z) :=
  let a := if e2 <? 0 then 0 else 128 - 5 - 1 in
  let r := a in
  let z := a in
  let? (big, z, y) := fmt_fp_dig DIG_FUEL (zrepeat 0 128, z, y) in
  ffp_E o w fl t p prefix pl big a r z e2.

(* [comment removed for export] *)
Definition ffp_C2 (o : list Z) (w fl t : Z) (y e2 p prefix pl : Z) : option (list Z * Z) :=
  let ynz := negb (f128_le y F128_ZERO =? 0) in
  let e2 := if ynz then e2 - 1 else e2 in
  let p := if p <? 0 then 6 else p in
  let '(y, e2) := if ynz then (f128_mul y (f128_of_d D_0x1p28), e2 - 28) else (y, e2) in
  ffp_D o w fl t y e2 p prefix pl.

(* [comment removed for export] *)
Definition ffp_C (o : list Z) (w fl t : Z) (y p prefix pl : Z) : option (list Z * Z) :=
  let? (fr, e2) := frexpl FREXPL_FUEL y 0 in
  let two := f128_of_i32 2 in
  let y := f128_mul fr two in
  ffp_C2 o w fl t y e2 p prefix pl.

(* [comment removed for export] *)
Definition ffp_sign (y fl : Z) : Z * Z * Z :=
  if negb (signbitl y =? 0) then (Z.lxor y F128_SIGNBIT, 0, 1)
  else if negb (Z.land fl MARK_POS =? 0) then (y, 3, 1)
  else if negb (Z.land fl PAD_POS =? 0) then (y, 6, 1)
  else (y, 1, 0).

Lemma fmt_fp_split : forall o y w p fl t,
  fmt_fp o y w p fl t =
    (let '(y, prefix, pl) := ffp_sign y fl in
     if fpclassifyl y <=? 1 then None else ffp_C o w fl t y p prefix pl).
Proof. intros. reflexivity. Qed.
