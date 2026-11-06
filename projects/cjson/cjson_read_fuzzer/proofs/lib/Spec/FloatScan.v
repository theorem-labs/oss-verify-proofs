(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require Bool.
From Stdlib Require Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.Riscv Require Fpu.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
Module DoubleOps.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.Riscv.Fpu LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.

Definition two_p1023 : word := Z_to_bv 64 0x7FE0000000000000.   (* [comment removed for export] *)
Definition two_m969  : word := Z_to_bv 64 0x0360000000000000.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition scalbn_u (n : Z) : word := Z_to_bv 64 (Z.shiftl (1023 + n) 52).

(* [comment removed for export] *)
Definition scalbn_reduce (x : word) (n : Z) : word * Z :=
  if (1023 <? n)%Z then
    let y := fmul_d RNE x two_p1023 in let n := (n - 1023)%Z in
    if (1023 <? n)%Z then
      let y := fmul_d RNE y two_p1023 in let n := (n - 1023)%Z in
      (y, if (1023 <? n)%Z then 1023%Z else n)
    else (y, n)
  else if (n <? -1022)%Z then
    let y := fmul_d RNE x two_m969 in let n := (n + 969)%Z in
    if (n <? -1022)%Z then
      let y := fmul_d RNE y two_m969 in let n := (n + 969)%Z in
      (y, if (n <? -1022)%Z then (-1022)%Z else n)
    else (y, n)
  else (x, n).

Definition scalbn_model (x : word) (n : Z) : word :=
  let (y, n') := scalbn_reduce x n in fmul_d RNE y (scalbn_u n').
End DoubleOps.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Fpu Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat.
Import DoubleOps.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition C_LDBL_MAX : Z := 0x7ffeffffffffffffffffffffffffffff. (* [comment removed for export] *)
Definition C_LDBL_MIN : Z := 0x00010000000000000000000000000000. (* [comment removed for export] *)
Definition C_1E9      : Z := 0x401cdcd6500000000000000000000000. (* [comment removed for export] *)
Definition C_ONE      : Z := 0x3fff0000000000000000000000000000. (* [comment removed for export] *)
Definition C_LDBL_EPS : Z := 0x3f8f0000000000000000000000000000. (* [comment removed for export] *)
Definition C_2P16383  : Z := 0x7ffe0000000000000000000000000000. (* [comment removed for export] *)
Definition C_2PM16269 : Z := 0x00720000000000000000000000000000. (* [comment removed for export] *)
Definition C_2P120    : Z := 0x40770000000000000000000000000000. (* [comment removed for export] *)
Definition C_2PM120   : Z := 0x3f870000000000000000000000000000. (* [comment removed for export] *)
Definition C_INF      : Z := 0x7fff0000000000000000000000000000. (* [comment removed for export] *)
Definition C_NINF     : Z := 0xffff0000000000000000000000000000.
Definition C_NAN      : Z := 0x7fff8000000000000000000000000000. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition D_ZERO : word := Z_to_bv 64 0.                   (* [comment removed for export] *)
Definition D_025  : word := Z_to_bv 64 0x3FD0000000000000.  (* [comment removed for export] *)
Definition D_05   : word := Z_to_bv 64 0x3FE0000000000000.  (* [comment removed for export] *)
Definition D_075  : word := Z_to_bv 64 0x3FE8000000000000.  (* [comment removed for export] *)
Definition D_ONE  : word := Z_to_bv 64 0x3FF0000000000000.  (* [comment removed for export] *)

Definition KMAX : Z := 2048.
Definition MASK : Z := 2047.
Definition LD_B1B_DIG : Z := 4.
Definition LDBL_MANT_DIG_ : Z := 113.
Definition LLONG_MIN_ : Z := - 2^63.
Definition LLONG_MAX_ : Z := 2^63 - 1.
Definition INT_MAX_ : Z := 2^31 - 1.
Definition th_list : list Z := [10384593; 717069655; 257060992; 658440191].   (* [comment removed for export] *)
Definition p10s : list Z := [10; 100; 1000; 10000; 100000; 1000000; 10000000; 100000000].

Definition FUEL_RING : nat := 2050%nat.
Definition FUEL_SCALE : nat := 2000%nat.

(* [comment removed for export] *)
Definition nz (v : Z) : bool := negb (v =? 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record shfile := mkSh {
  sh_buf : list Z;      (* [comment removed for export] *)
  sh_rpos : Z;          (* [comment removed for export] *)
  sh_cnt0 : Z;          (* [comment removed for export] *)
  sh_n : Z;             (* [comment removed for export] *)
  sh_stdio : bool;      (* [comment removed for export] *)
  sh_shlim_neg : bool   (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition sh_getc (f : shfile) : Z * shfile :=
  if negb (sh_stdio f) then
    (znth (sh_buf f) (sh_rpos f),
     mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))
  else if negb (sh_rpos f =? sh_n f) then
    (znth (sh_buf f) (sh_rpos f),
     mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))
  else
    (-1, mkSh (sh_buf f) (sh_rpos f) (sh_cnt0 f) (sh_n f) (sh_stdio f) true).

Definition sh_unget (f : shfile) : shfile :=
  if negb (sh_shlim_neg f)
  then mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)
  else f.

Definition sh_lim0 (f : shfile) : shfile :=
  mkSh (sh_buf f) (sh_rpos f) (sh_rpos f) (sh_n f) (sh_stdio f) false.

Definition sh_cnt (f : shfile) : Z := sh_rpos f - sh_cnt0 f.

(* [comment removed for export] *)
Definition m_isspace (c : Z) : bool := (c =? 32) || (u32 (c - 9) <? 5).
(* [comment removed for export] *)
Definition isdigitc (c : Z) : bool := u32 (c - 48) <? 10.

(* [comment removed for export] *)
Fixpoint fs_unget_loop (fuel : nat) (f : shfile) : shfile :=
  match fuel with O => f | S fu => fs_unget_loop fu (sh_unget f) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition m_scalbn (x : word) (n : Z) : word := scalbn_model x n.

(* [comment removed for export] *)
Definition m_copysignl (x y : Z) : Z :=
  mk128 (Z.lor (Z.land (hi64 x) 0x7fffffffffffffff) (Z.land (hi64 y) 0x8000000000000000)) (lo64 x).

(* [comment removed for export] *)
Definition m_fabsl (x : Z) : Z := mk128 (Z.land (hi64 x) 0x7fffffffffffffff) (lo64 x).

(* [comment removed for export] *)
Definition m_fpclassifyl (x : Z) : Z :=
  let e := Z.land (Z.shiftr (hi64 x) 48) 0x7fff in
  let mhi := Z.land (hi64 x) 0x0000ffffffffffff in
  let mlo := lo64 x in
  if e =? 0 then (if nz (Z.lor mlo mhi) then 3 else 2)
  else if e =? 0x7fff then (if nz (Z.lor mlo mhi) then 0 else 1)
  else 4.

(* [comment removed for export] *)
Definition m_scalbnl (x : Z) (n : Z) : Z :=
  let '(x, n) :=
    if 16383 <? n then
      let x := f128_mul x C_2P16383 in                    (* [comment removed for export] *)
      let n := n - 16383 in
      if 16383 <? n then
        let x := f128_mul x C_2P16383 in                  (* [comment removed for export] *)
        let n := n - 16383 in
        (x, if 16383 <? n then 16383 else n)
      else (x, n)
    else if n <? -16382 then
      let x := f128_mul x C_2PM16269 in                   (* [comment removed for export] *)
      let n := n + (16382 - 113) in
      if n <? -16382 then
        let x := f128_mul x C_2PM16269 in                 (* [comment removed for export] *)
        let n := n + (16382 - 113) in
        (x, if n <? -16382 then -16382 else n)
      else (x, n)
    else (x, n) in
  let u := f128_of_d (bv_unsigned D_ONE) in               (* [comment removed for export] *)
  (* [comment removed for export] *)
  let u := mk128 (Z.lor (Z.land (hi64 u) 0x0000ffffffffffff) (Z.shiftl (Z.land (0x3fff + n) 0xffff) 48)) (lo64 u) in
  f128_mul x u.                                             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fmodl_sub_body (x yhi ylo : Z) (st : Z * Z * Z) : (Z * Z * Z) + Z :=
  let '(xhi, xlo, ex) := st in
  let hi := u64 (xhi - yhi) in
  let lo := u64 (xlo - ylo) in
  let hi := if xlo <? ylo then u64 (hi - 1) else hi in
  if Z.shiftr hi 63 =? 0 then
    if Z.lor hi lo =? 0 then
      inr (let t := f128_of_i32 0 in                        (* [comment removed for export] *)
           f128_mul t x)                                    (* [comment removed for export] *)
    else inl (u64 (2*hi + Z.shiftr lo 63), u64 (2*lo), ex - 1)
  else inl (u64 (2*xhi + Z.shiftr xlo 63), u64 (2*xlo), ex - 1).

Fixpoint fmodl_sub_loop (fuel : nat) (x yhi ylo ey : Z) (st : Z * Z * Z) : option ((Z * Z * Z) + Z) :=
  match fuel with
  | O => None
  | S fu =>
    let '(xhi, xlo, ex) := st in
    if ey <? ex then
      match fmodl_sub_body x yhi ylo st with
      | inl st' => fmodl_sub_loop fu x yhi ylo ey st'
      | inr r => Some (inr r)
      end
    else Some (inl st)
  end.

(* [comment removed for export] *)
Definition fmodl_norm_body (st : Z * Z * Z) : Z * Z * Z :=
  let '(xhi, xlo, ex) := st in (u64 (2*xhi + Z.shiftr xlo 63), u64 (2*xlo), ex - 1).

Fixpoint fmodl_norm_loop (fuel : nat) (st : Z * Z * Z) : option (Z * Z * Z) :=
  match fuel with
  | O => None
  | S fu => let '(xhi, xlo, ex) := st in
            if Z.shiftr xhi 48 =? 0 then fmodl_norm_loop fu (fmodl_norm_body st) else Some st
  end.

Definition m_fmodl (x y : Z) : option Z :=
  let uxhi := hi64 x in let uxlo := lo64 x in
  let uyhi := hi64 y in let uylo := lo64 y in
  let ex := Z.land (Z.shiftr uxhi 48) 0x7fff in
  let ey := Z.land (Z.shiftr uyhi 48) 0x7fff in
  let sx := Z.land (Z.shiftr uxhi 48) 0x8000 in
  (* [comment removed for export] *)
  let t := f128_of_i32 0 in                                 (* [comment removed for export] *)
  if (f128_le y t =? 0)                                     (* [comment removed for export] *)
     || (m_fpclassifyl y =? 0)                              (* [comment removed for export] *)
     || (ex =? 0x7fff) then
    let t := f128_mul x y in                                (* [comment removed for export] *)
    Some (f128_div t t)                                     (* [comment removed for export] *)
  else
  let ux := mk128 (Z.land uxhi 0x7fffffffffffffff) uxlo in
  let uy := mk128 (Z.land uyhi 0x7fffffffffffffff) uylo in
  if f128_le ux uy <=? 0 then                               (* [comment removed for export] *)
    if f128_le ux uy =? 0 then                              (* [comment removed for export] *)
      let t := f128_of_i32 0 in                             (* [comment removed for export] *)
      Some (f128_mul t x)                                   (* [comment removed for export] *)
    else Some x
  else
  (* [comment removed for export] *)
  let '(ux, ex) := if ex =? 0 then
      let ux := f128_mul ux C_2P120 in                      (* [comment removed for export] *)
      (ux, Z.shiftr (hi64 ux) 48 - 120)
    else (ux, ex) in
  let '(uy, ey) := if ey =? 0 then
      let uy := f128_mul uy C_2P120 in                      (* [comment removed for export] *)
      (uy, Z.shiftr (hi64 uy) 48 - 120)
    else (uy, ey) in
  let xhi := Z.lor (Z.land (hi64 ux) 0x0000ffffffffffff) (2^48) in
  let yhi := Z.lor (Z.land (hi64 uy) 0x0000ffffffffffff) (2^48) in
  let xlo := lo64 ux in
  let ylo := lo64 uy in
  (* [comment removed for export] *)
  match fmodl_sub_loop (S (Z.to_nat (ex - ey))) x yhi ylo ey (xhi, xlo, ex) with
  | None => None
  | Some (inr r) => Some r
  | Some (inl (xhi, xlo, ex)) =>
    let hi := u64 (xhi - yhi) in
    let lo := u64 (xlo - ylo) in
    let hi := if xlo <? ylo then u64 (hi - 1) else hi in
    let r :=
      if Z.shiftr hi 63 =? 0 then
        if Z.lor hi lo =? 0 then
          inr (let t := f128_of_i32 0 in                    (* [comment removed for export] *)
               f128_mul t x)                                (* [comment removed for export] *)
        else inl (hi, lo)
      else inl (xhi, xlo) in
    match r with
    | inr v => Some v
    | inl (xhi, xlo) =>
      (* [comment removed for export] *)
      match fmodl_norm_loop 130%nat (xhi, xlo, ex) with
      | None => None
      | Some (xhi, xlo, ex) =>
        (* [comment removed for export] *)
        if ex <=? 0 then
          let ux := mk128 (Z.lor (Z.land xhi 0x0000ffffffffffff) (Z.shiftl (Z.land (Z.lor (ex + 120) sx) 0xffff) 48)) xlo in
          Some (f128_mul ux C_2PM120)                       (* [comment removed for export] *)
        else
          Some (mk128 (Z.lor (Z.land xhi 0x0000ffffffffffff) (Z.shiftl (Z.land (Z.lor ex sx) 0xffff) 48)) xlo)
      end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition scanexp_l1_cond (st : Z * Z * shfile) : bool :=
  let '(x, c, f) := st in isdigitc c && (x <? Z.quot INT_MAX_ 10).
Definition scanexp_l1_body (st : Z * Z * shfile) : Z * Z * shfile :=
  let '(x, c, f) := st in
  let x := 10*x + c - 48 in            (* [comment removed for export] *)
  let '(c, f) := sh_getc f in (x, c, f).
Fixpoint scanexp_l1_loop (fuel : nat) (st : Z * Z * shfile) : option (Z * Z * shfile) :=
  match fuel with
  | O => None
  | S fu => if scanexp_l1_cond st then scanexp_l1_loop fu (scanexp_l1_body st) else Some st
  end.

(* [comment removed for export] *)
Definition scanexp_l2_cond (st : Z * Z * shfile) : bool :=
  let '(y, c, f) := st in isdigitc c && (y <? Z.quot LLONG_MAX_ 100).
Definition scanexp_l2_body (st : Z * Z * shfile) : Z * Z * shfile :=
  let '(y, c, f) := st in
  let y := 10*y + c - 48 in            (* [comment removed for export] *)
  let '(c, f) := sh_getc f in (y, c, f).
Fixpoint scanexp_l2_loop (fuel : nat) (st : Z * Z * shfile) : option (Z * Z * shfile) :=
  match fuel with
  | O => None
  | S fu => if scanexp_l2_cond st then scanexp_l2_loop fu (scanexp_l2_body st) else Some st
  end.

(* [comment removed for export] *)
Definition scanexp_l3_body (st : Z * shfile) : Z * shfile := let '(c, f) := st in sh_getc f.
Fixpoint scanexp_l3_loop (fuel : nat) (st : Z * shfile) : option (Z * shfile) :=
  match fuel with
  | O => None
  | S fu => let '(c, f) := st in if isdigitc c then scanexp_l3_loop fu (scanexp_l3_body st) else Some st
  end.

Definition scanexp (fuelc : nat) (f : shfile) (pok : Z) : option (shfile * Z) :=
  let '(c, f) := sh_getc f in                                          (* [comment removed for export] *)
  let '(neg, c, f) :=
    if (c =? 43) || (c =? 45) then
      let neg := b2z (c =? 45) in
      let '(c, f) := sh_getc f in                                      (* [comment removed for export] *)
      let f := if negb (isdigitc c) && nz pok then sh_unget f else f in   (* [comment removed for export] *)
      (neg, c, f)
    else (0, c, f) in
  if negb (isdigitc c) then
    let f := sh_unget f in                                             (* [comment removed for export] *)
    Some (f, LLONG_MIN_)
  else
  match scanexp_l1_loop fuelc (0, c, f) with
  | None => None
  | Some (x, c, f) =>
  match scanexp_l2_loop fuelc (x, c, f) with
  | None => None
  | Some (y, c, f) =>
  match scanexp_l3_loop fuelc (c, f) with
  | None => None
  | Some (c, f) =>
    let f := sh_unget f in                                             (* [comment removed for export] *)
    Some (f, if nz neg then - y else y)
  end end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition df_lz_body (st : Z * Z * shfile) : Z * Z * shfile :=
  let '(gotdig, c, f) := st in let '(c, f) := sh_getc f in (1, c, f).
Fixpoint df_lz_loop (fuel : nat) (st : Z * Z * shfile) : option (Z * Z * shfile) :=
  match fuel with
  | O => None
  | S fu => let '(gotdig, c, f) := st in if c =? 48 then df_lz_loop fu (df_lz_body st) else Some st
  end.

(* [comment removed for export] *)
Definition df_rz_body (st : Z * Z * Z * shfile) : Z * Z * Z * shfile :=
  let '(gotdig, lrp, c, f) := st in let '(c, f) := sh_getc f in (1, lrp - 1, c, f).
Fixpoint df_rz_loop (fuel : nat) (st : Z * Z * Z * shfile) : option (Z * Z * Z * shfile) :=
  match fuel with
  | O => None
  | S fu => let '(gotdig, lrp, c, f) := st in if c =? 48 then df_rz_loop fu (df_rz_body st) else Some st
  end.

(* [comment removed for export] *)
Record st_dig := mkDL {
  dl_f : shfile; dl_c : Z; dl_j : Z; dl_k : Z; dl_lrp : Z; dl_dc : Z;
  dl_lnz : Z; dl_gotdig : Z; dl_gotrad : Z; dl_x : list Z }.

Definition df_dig_cond (s : st_dig) : bool := isdigitc (dl_c s) || (dl_c s =? 46).

(* [comment removed for export] *)
Definition df_dig_body (s : st_dig) : st_dig + st_dig :=
  let c := dl_c s in
  if c =? 46 then
    if nz (dl_gotrad s) then inr s
    else
      let '(c', f') := sh_getc (dl_f s) in
      inl (mkDL f' c' (dl_j s) (dl_k s) (dl_dc s) (* [comment removed for export] *) (dl_dc s) (dl_lnz s) (dl_gotdig s) 1 (dl_x s))
  else if dl_k s <? KMAX - 3 then
    let dc := dl_dc s + 1 in
    let lnz := if negb (c =? 48) then s32 dc else dl_lnz s in      (* [comment removed for export] *)
    let k := dl_k s in let j := dl_j s in
    let x := if nz j then zupd (dl_x s) k (u32 (znth (dl_x s) k * 10 + c - 48))
             else zupd (dl_x s) k (c - 48) in
    let j := j + 1 in
    let '(k, j) := if j =? 9 then (k + 1, 0) else (k, j) in
    let '(c', f') := sh_getc (dl_f s) in
    inl (mkDL f' c' j k (dl_lrp s) dc lnz 1 (dl_gotrad s) x)
  else
    let dc := dl_dc s + 1 in
    let '(lnz, x) := if negb (c =? 48)
      then ((KMAX - 4) * 9, zupd (dl_x s) (KMAX - 4) (Z.lor (znth (dl_x s) (KMAX - 4)) 1))
      else (dl_lnz s, dl_x s) in
    let '(c', f') := sh_getc (dl_f s) in
    inl (mkDL f' c' (dl_j s) (dl_k s) (dl_lrp s) dc lnz (dl_gotdig s) (dl_gotrad s) x).

Fixpoint df_dig_loop (fuel : nat) (s : st_dig) : option st_dig :=
  match fuel with
  | O => None
  | S fu => if df_dig_cond s then
              match df_dig_body s with inl s' => df_dig_loop fu s' | inr s' => Some s' end
            else Some s
  end.

(* [comment removed for export] *)
Definition df_pad_body (k : Z) (st : Z * list Z) : Z * list Z :=
  let '(j, x) := st in (j + 1, zupd x k (u32 (znth x k * 10))).
Fixpoint df_pad_loop (fuel : nat) (k : Z) (st : Z * list Z) : option (Z * list Z) :=
  match fuel with
  | O => None
  | S fu => let '(j, x) := st in if j <? 9 then df_pad_loop fu k (df_pad_body k st) else Some st
  end.

(* [comment removed for export] *)
Definition df_tz_body (z : Z) : Z := z - 1.
Fixpoint df_tz_loop (fuel : nat) (x : list Z) (z : Z) : option Z :=
  match fuel with
  | O => None
  | S fu => if znth x (z - 1) =? 0 then df_tz_loop fu x (df_tz_body z) else Some z
  end.

(* [comment removed for export] *)
Record st_al := mkAL { al_k : Z; al_a : Z; al_rp : Z; al_carry : Z; al_x : list Z }.
Definition df_al_body (p10 : Z) (s : st_al) : st_al :=
  let k := al_k s in let x := al_x s in
  let tmp := Z.modulo (znth x k) p10 in                   (* [comment removed for export] *)
  let x := zupd x k (u32 (Z.div (znth x k) p10 + al_carry s)) in
  let carry := u32 (Z.div 1000000000 p10 * tmp) in
  let '(a, rp) := if (k =? al_a s) && (znth x k =? 0) then (Z.land (al_a s + 1) MASK, al_rp s - 9) else (al_a s, al_rp s) in
  mkAL (k + 1) a rp carry x.
Fixpoint df_al_loop (fuel : nat) (p10 z : Z) (s : st_al) : option st_al :=
  match fuel with
  | O => None
  | S fu => if negb (al_k s =? z) then df_al_loop fu p10 z (df_al_body p10 s) else Some s
  end.

(* [comment removed for export] *)
Record st_upk := mkUK { uk_k : Z; uk_carry : Z; uk_z : Z; uk_x : list Z }.
Definition df_upk_body (a : Z) (s : st_upk) : st_upk + st_upk :=
  let k := uk_k s in let x := uk_x s in let z := uk_z s in
  let tmp := u64 (Z.shiftl (znth x k) 29 + uk_carry s) in       (* [comment removed for export] *)
  let '(carry, x) :=
    if 1000000000 <? tmp
    then (u32 (Z.div tmp 1000000000), zupd x k (u32 (Z.modulo tmp 1000000000)))
    else (0, zupd x k (u32 tmp)) in
  let z := if (k =? Z.land (z - 1) MASK) && negb (k =? a) && (znth x k =? 0) then k else z in
  let s' := mkUK k carry z x in
  if k =? a then inr s' else inl (mkUK (Z.land (k - 1) MASK) carry z x).
Fixpoint df_upk_loop (fuel : nat) (a : Z) (s : st_upk) : option st_upk :=
  match fuel with
  | O => None
  | S fu => match df_upk_body a s with inl s' => df_upk_loop fu a s' | inr s' => Some s' end
  end.

(* [comment removed for export] *)
Record st_up := mkUS { us_rp : Z; us_a : Z; us_z : Z; us_e2 : Z; us_x : list Z }.
Definition df_up_cond (s : st_up) : bool :=
  (us_rp s <? 9 * LD_B1B_DIG) || ((us_rp s =? 9 * LD_B1B_DIG) && (znth (us_x s) (us_a s) <? znth th_list 0)).
Definition df_up_body (s : st_up) : option st_up :=
  let a := us_a s in
  let e2 := us_e2 s - 29 in
  match df_upk_loop FUEL_RING a (mkUK (Z.land (us_z s - 1) MASK) 0 (us_z s) (us_x s)) with
  | None => None
  | Some (mkUK _ carry z x) =>
    if nz carry then
      let rp := us_rp s + 9 in
      let a := Z.land (a - 1) MASK in
      let '(z, x) := if a =? z then
          let z := Z.land (z - 1) MASK in
          (z, zupd x (Z.land (z - 1) MASK) (Z.lor (znth x (Z.land (z - 1) MASK)) (znth x z)))
        else (z, x) in
      let x := zupd x a carry in
      Some (mkUS rp a z e2 x)
    else Some (mkUS (us_rp s) a z e2 x)
  end.
Fixpoint df_up_loop (fuel : nat) (s : st_up) : option st_up :=
  match fuel with
  | O => None
  | S fu => if df_up_cond s then
              match df_up_body s with None => None | Some s' => df_up_loop fu s' end
            else Some s
  end.

(* [comment removed for export] *)
Definition df_dni_body (a z : Z) (x : list Z) (i : Z) : Z + Z :=
  let k := Z.land (a + i) MASK in
  if (k =? z) || (znth x k <? znth th_list i) then inr LD_B1B_DIG
  else if znth th_list i <? znth x (Z.land (a + i) MASK) then inr i
  else inl (i + 1).
Fixpoint df_dni_loop (fuel : nat) (a z : Z) (x : list Z) (i : Z) : option Z :=
  match fuel with
  | O => None
  | S fu => if i <? LD_B1B_DIG then
              match df_dni_body a z x i with inl i' => df_dni_loop fu a z x i' | inr i' => Some i' end
            else Some i
  end.

(* [comment removed for export] *)
Record st_dnk := mkDK { dk_k : Z; dk_carry : Z; dk_a : Z; dk_i : Z; dk_rp : Z; dk_x : list Z }.
Definition df_dnk_body (z sh : Z) (s : st_dnk) : st_dnk :=
  let k := dk_k s in let x := dk_x s in
  let tmp := Z.land (znth x k) (Z.shiftl 1 sh - 1) in
  let x := zupd x k (u32 (Z.shiftr (znth x k) sh + dk_carry s)) in
  let carry := u32 (Z.shiftr 1000000000 sh * tmp) in
  let '(a, i, rp) := if (k =? dk_a s) && (znth x k =? 0)
    then (Z.land (dk_a s + 1) MASK, dk_i s - 1, dk_rp s - 9) else (dk_a s, dk_i s, dk_rp s) in
  mkDK (Z.land (k + 1) MASK) carry a i rp x.
Fixpoint df_dnk_loop (fuel : nat) (z sh : Z) (s : st_dnk) : option st_dnk :=
  match fuel with
  | O => None
  | S fu => if negb (dk_k s =? z) then df_dnk_loop fu z sh (df_dnk_body z sh s) else Some s
  end.

(* [comment removed for export] *)
Record st_dn := mkDS { ds_rp : Z; ds_a : Z; ds_z : Z; ds_e2 : Z; ds_x : list Z; ds_i : Z }.
Definition df_dn_body (s : st_dn) : option (st_dn + st_dn) :=
  let a := ds_a s in let z := ds_z s in let x := ds_x s in let rp := ds_rp s in
  (* [comment removed for export] *)
  match df_dni_loop 6%nat a z x 0 with
  | None => None
  | Some i =>
    if (i =? LD_B1B_DIG) && (rp =? 9 * LD_B1B_DIG) then Some (inr (mkDS rp a z (ds_e2 s) x i))
    else
      let sh := if 9 + 9 * LD_B1B_DIG <? rp then 9 else 1 in
      let e2 := ds_e2 s + sh in
      match df_dnk_loop FUEL_RING z sh (mkDK a 0 a i rp x) with
      | None => None
      | Some (mkDK _ carry a i rp x) =>
        let '(z, x) :=
          if nz carry then
            if negb (Z.land (z + 1) MASK =? a) then (Z.land (z + 1) MASK, zupd x z carry)
            else (z, zupd x (Z.land (z - 1) MASK) (Z.lor (znth x (Z.land (z - 1) MASK)) 1))
          else (z, x) in
        Some (inl (mkDS rp a z e2 x i))
      end
  end.
Fixpoint df_dn_loop (fuel : nat) (s : st_dn) : option st_dn :=
  match fuel with
  | O => None
  | S fu => match df_dn_body s with
            | None => None
            | Some (inl s') => df_dn_loop fu s'
            | Some (inr s') => Some s'
            end
  end.

(* [comment removed for export] *)
Record st_asm := mkAS { as_i : Z; as_y : Z; as_z : Z; as_x : list Z }.
Definition df_asm_body (a : Z) (s : st_asm) : st_asm :=
  let i := as_i s in
  let '(z, x) :=
    if Z.land (a + i) MASK =? as_z s then
      let z := Z.land (as_z s + 1) MASK in
      (z, if negb (z =? 0) then zupd (as_x s) (z - 1) 0 else as_x s)
    else (as_z s, as_x s) in
  let xf := f128_of_u32 (znth x (Z.land (a + i) MASK)) in   (* [comment removed for export] *)
  let p := f128_mul C_1E9 (as_y s) in                       (* [comment removed for export] *)
  let y := f128_add p xf in                                 (* [comment removed for export] *)
  mkAS (i + 1) y z x.
Fixpoint df_asm_loop (fuel : nat) (a : Z) (s : st_asm) : option st_asm :=
  match fuel with
  | O => None
  | S fu => if as_i s <? LD_B1B_DIG then df_asm_loop fu a (df_asm_body a s) else Some s
  end.

(* [comment removed for export] *)
Definition df_final (a z : Z) (x : list Z) (e2 bits emin sign emax : Z) (frac bias : Z) : option Z :=
  let y := f128_of_i32 0 in                                 (* [comment removed for export] *)
  match df_asm_loop 5%nat a (mkAS 0 y z x) with
  | None => None
  | Some (mkAS i y z x) =>
  let sf := f128_of_i32 sign in                             (* [comment removed for export] *)
  let y := f128_mul y sf in                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  let '(bits, denormal) :=
    if LDBL_MANT_DIG_ + e2 - emin <? bits then
      let bits := LDBL_MANT_DIG_ + e2 - emin in
      ((if bits <? 0 then 0 else bits), 1)
    else (bits, 0) in
  (* [comment removed for export] *)
  let r :=
    if bits <? LDBL_MANT_DIG_ then
      let d := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (2 * LDBL_MANT_DIG_ - bits - 1) in   (* [comment removed for export] *)
      let t := f128_of_d (bv_unsigned d) in                 (* [comment removed for export] *)
      let bias := m_copysignl t y in                        (* [comment removed for export] *)
      let d := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (LDBL_MANT_DIG_ - bits) in           (* [comment removed for export] *)
      let t := f128_of_d (bv_unsigned d) in                 (* [comment removed for export] *)
      match m_fmodl y t with                                (* [comment removed for export] *)
      | None => None
      | Some frac =>
        let y := f128_sub y frac in                         (* [comment removed for export] *)
        let y := f128_add y bias in                         (* [comment removed for export] *)
        Some (y, frac, bias)
      end
    else Some (y, frac, bias) in
  match r with
  | None => None
  | Some (y, frac, bias) =>
  (* [comment removed for export] *)
  let r :=
    if negb (Z.land (a + i) MASK =? z) then
      let t := znth x (Z.land (a + i) MASK) in
      let signd := fcvt_d_w RNE (Z_to_bv 64 sign) in        (* [comment removed for export] *)
      let od :=
        if (t <? 500000000) && (nz t || negb (Z.land (a + i + 1) MASK =? z))
        then Some (fmul_d RNE D_025 signd)                  (* [comment removed for export] *)
        else if 500000000 <? t
        then Some (fmul_d RNE D_075 signd)                  (* [comment removed for export] *)
        else if t =? 500000000 then
          (if Z.land (a + i + 1) MASK =? z
           then Some (fmul_d RNE D_05 signd)                (* [comment removed for export] *)
           else Some (fmul_d RNE D_075 signd))              (* [comment removed for export] *)
        else None in
      let frac := match od with
        | Some d => let e := f128_of_d (bv_unsigned d) in   (* [comment removed for export] *)
                    f128_add frac e                         (* [comment removed for export] *)
        | None => frac end in
      if 2 <=? LDBL_MANT_DIG_ - bits then
        let one := f128_of_i32 1 in                         (* [comment removed for export] *)
        match m_fmodl frac one with                         (* [comment removed for export] *)
        | None => None
        | Some rr =>
          if f128_le rr 0 =? 0                              (* [comment removed for export] *)
          then Some (f128_add frac C_ONE)                   (* [comment removed for export] *)
          else Some frac
        end
      else Some frac
    else Some frac in
  match r with
  | None => None
  | Some frac =>
  let y := f128_add y frac in                               (* [comment removed for export] *)
  let y := f128_sub y bias in                               (* [comment removed for export] *)
  let '(y, e2) :=
    if emax - 5 <? Z.land (u32 (e2 + LDBL_MANT_DIG_)) INT_MAX_ then
      let ay := m_fabsl y in                                (* [comment removed for export] *)
      let two := f128_of_i32 2 in                           (* [comment removed for export] *)
      let lim := f128_div two C_LDBL_EPS in                 (* [comment removed for export] *)
      if 0 <=? f128_ge ay lim then                          (* [comment removed for export] *)
        (* [comment removed for export] *)
        let half := f128_of_d (bv_unsigned D_05) in         (* [comment removed for export] *)
        let y := f128_mul y half in                         (* [comment removed for export] *)
        (y, e2 + 1)
      else (y, e2)
      (* [comment removed for export] *)
    else (y, e2) in
  Some (m_scalbnl y e2)                                     (* [comment removed for export] *)
  end end end.

(* [comment removed for export] *)
Definition decfloat (fuelc : nat) (f : shfile) (c bits emin sign pok : Z) : option (shfile * Z) :=
  let emax := - emin - bits + 3 in
  let zero0 := f128_of_i32 0 in                             (* [comment removed for export] *)
  let frac := zero0 in
  let bias := zero0 in
  (* [comment removed for export] *)
  match df_lz_loop fuelc (0, c, f) with
  | None => None
  | Some (gotdig, c, f) =>
  match (if c =? 46 then
           let '(c, f) := sh_getc f in                      (* [comment removed for export] *)
           match df_rz_loop fuelc (gotdig, 0, c, f) with
           | None => None
           | Some (gotdig, lrp, c, f) => Some (gotdig, 1, lrp, c, f)
           end
         else Some (gotdig, 0, 0, c, f)) with
  | None => None
  | Some (gotdig, gotrad, lrp, c, f) =>
  let x := zupd (zrepeat 0 KMAX) 0 0 in                     (* [comment removed for export] *)
  match df_dig_loop fuelc (mkDL f c 0 0 lrp 0 0 gotdig gotrad x) with
  | None => None
  | Some (mkDL f c j k lrp dc lnz gotdig gotrad x) =>
  let lrp := if nz gotrad then lrp else dc in               (* [comment removed for export] *)
  (* [comment removed for export] *)
  match (if nz gotdig && (Z.lor c 32 =? 101) then
           match scanexp fuelc f pok with                   (* [comment removed for export] *)
           | None => None
           | Some (f, e10) =>
             if e10 =? LLONG_MIN_ then
               if nz pok then Some (inl (sh_unget f, lrp + 0))            (* [comment removed for export] *)
               else Some (inr (sh_lim0 f, f128_of_i32 0))                 (* [comment removed for export] *)
             else Some (inl (f, lrp + e10))
           end
         else Some (inl ((if 0 <=? c then sh_unget f else f), lrp))) with  (* [comment removed for export] *)
  | None => None
  | Some (inr r) => Some r
  | Some (inl (f, lrp)) =>
  if negb (nz gotdig) then
    Some (sh_lim0 f, f128_of_i32 0)                         (* [comment removed for export] *)
  else
  let x0 := znth x 0 in
  (* [comment removed for export] *)
  if x0 =? 0 then
    let t := fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 sign)) D_ZERO in   (* [comment removed for export] *)
    Some (f, f128_of_d (bv_unsigned t))                     (* [comment removed for export] *)
  else
  (* [comment removed for export] *)
  if (lrp =? dc) && (dc <? 10) && ((30 <? bits) || (Z.shiftr x0 bits =? 0)) then
    let sf := f128_of_i32 sign in                           (* [comment removed for export] *)
    let xf := f128_of_u32 x0 in                             (* [comment removed for export] *)
    Some (f, f128_mul sf xf)                                (* [comment removed for export] *)
  else if Z.quot (- emin) 2 <? lrp then
    let sf := f128_of_i32 sign in                           (* [comment removed for export] *)
    let t := f128_mul sf C_LDBL_MAX in                      (* [comment removed for export] *)
    Some (f, f128_mul t C_LDBL_MAX)                         (* [comment removed for export] *)
  else if lrp <? emin - 2 * LDBL_MANT_DIG_ then
    let sf := f128_of_i32 sign in                           (* [comment removed for export] *)
    let t := f128_mul sf C_LDBL_MIN in                      (* [comment removed for export] *)
    Some (f, f128_mul t C_LDBL_MIN)                         (* [comment removed for export] *)
  else
  (* [comment removed for export] *)
  match (if nz j then
           match df_pad_loop 10%nat k (j, x) with
           | None => None
           | Some (j, x) => Some (k + 1, x)                  (* [comment removed for export] *)
           end
         else Some (k, x)) with
  | None => None
  | Some (k, x) =>
  let a := 0 in
  let z := k in
  let e2 := 0 in
  let rp := s32 lrp in                                      (* [comment removed for export] *)
  let x0 := znth x 0 in
  (* [comment removed for export] *)
  match (if (lnz <? 9) && (lnz <=? rp) && (rp <? 18) then
           if rp =? 9 then
             let sf := f128_of_i32 sign in                  (* [comment removed for export] *)
             let xf := f128_of_u32 x0 in                    (* [comment removed for export] *)
             Some (inr (f, f128_mul sf xf))                 (* [comment removed for export] *)
           else if rp <? 9 then
             let sf := f128_of_i32 sign in                  (* [comment removed for export] *)
             let xf := f128_of_u32 x0 in                    (* [comment removed for export] *)
             let t := f128_mul sf xf in                     (* [comment removed for export] *)
             let pf := f128_of_i32 (znth p10s (8 - rp)) in  (* [comment removed for export] *)
             Some (inr (f, f128_div t pf))                  (* [comment removed for export] *)
           else
             let bitlim := bits - 3 * (rp - 9) in
             if (30 <? bitlim) || (Z.shiftr x0 bitlim =? 0) then
               let sf := f128_of_i32 sign in                (* [comment removed for export] *)
               let xf := f128_of_u32 x0 in                  (* [comment removed for export] *)
               let t := f128_mul sf xf in                   (* [comment removed for export] *)
               let pf := f128_of_i32 (znth p10s (rp - 10)) in   (* [comment removed for export] *)
               Some (inr (f, f128_mul t pf))                (* [comment removed for export] *)
             else Some (inl tt)
         else Some (inl tt)) with
  | None => None
  | Some (inr r) => Some r
  | Some (inl _) =>
  (* [comment removed for export] *)
  match df_tz_loop FUEL_RING x z with
  | None => None
  | Some z =>
  (* [comment removed for export] *)
  match (if nz (Z.rem rp 9) then
           let rpm9 := if 0 <=? rp then Z.rem rp 9 else Z.rem rp 9 + 9 in
           let p10 := znth p10s (8 - rpm9) in
           match df_al_loop FUEL_RING p10 z (mkAL a a rp 0 x) with
           | None => None
           | Some (mkAL _ a rp carry x) =>
             let '(z, x) := if nz carry then (z + 1, zupd x z carry) else (z, x) in
             Some (a, z, rp + (9 - rpm9), x)
           end
         else Some (a, z, rp, x)) with
  | None => None
  | Some (a, z, rp, x) =>
  (* [comment removed for export] *)
  match df_up_loop FUEL_SCALE (mkUS rp a z e2 x) with
  | None => None
  | Some (mkUS rp a z e2 x) =>
  (* [comment removed for export] *)
  match df_dn_loop FUEL_SCALE (mkDS rp a z e2 x 0) with
  | None => None
  | Some (mkDS rp a z e2 x i) =>
  match df_final a z x e2 bits emin sign emax frac bias with
  | None => None
  | Some y => Some (f, y)
  end end end end end end end end end end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint fs_ws_loop (fuel : nat) (f : shfile) : option (Z * shfile) :=
  match fuel with
  | O => None
  | S fu => let '(c, f') := sh_getc f in if m_isspace c then fs_ws_loop fu f' else Some (c, f')
  end.

Definition str_infinity : list Z := [105; 110; 102; 105; 110; 105; 116; 121].  (* [comment removed for export] *)
Definition str_nan : list Z := [110; 97; 110].                                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fs_inf_cond (st : Z * Z * shfile) : bool :=
  let '(i, c, f) := st in (i <? 8) && (Z.lor c 32 =? znth str_infinity i).
Definition fs_inf_body (st : Z * Z * shfile) : Z * Z * shfile :=
  let '(i, c, f) := st in
  let '(c, f) := if i <? 7 then sh_getc f else (c, f) in (i + 1, c, f).
Fixpoint fs_inf_loop (fuel : nat) (st : Z * Z * shfile) : option (Z * Z * shfile) :=
  match fuel with
  | O => None
  | S fu => if fs_inf_cond st then fs_inf_loop fu (fs_inf_body st) else Some st
  end.

(* [comment removed for export] *)
Definition fs_nan_cond (st : Z * Z * shfile) : bool :=
  let '(i, c, f) := st in (i <? 3) && (Z.lor c 32 =? znth str_nan i).
Definition fs_nan_body (st : Z * Z * shfile) : Z * Z * shfile :=
  let '(i, c, f) := st in
  let '(c, f) := if i <? 2 then sh_getc f else (c, f) in (i + 1, c, f).
Fixpoint fs_nan_loop (fuel : nat) (st : Z * Z * shfile) : option (Z * Z * shfile) :=
  match fuel with
  | O => None
  | S fu => if fs_nan_cond st then fs_nan_loop fu (fs_nan_body st) else Some st
  end.

(* [comment removed for export] *)
Definition fs_par_body (st : Z * shfile) : (Z * shfile) + (Z * Z * shfile) :=
  let '(i, f) := st in
  let '(c, f) := sh_getc f in
  if (u32 (c - 48) <? 10) || (u32 (c - 65) <? 26) || (u32 (c - 97) <? 26) || (c =? 95)
  then inl (i + 1, f) else inr (i, c, f).
Fixpoint fs_par_loop (fuel : nat) (st : Z * shfile) : option (Z * Z * shfile) :=
  match fuel with
  | O => None
  | S fu => match fs_par_body st with inl st' => fs_par_loop fu st' | inr r => Some r end
  end.

(* [comment removed for export] *)
Definition floatscan (fuelc : nat) (f : shfile) (prec pok : Z) : option (shfile * Z) :=
  match (if prec =? 0 then Some (24, -125 - 24)
         else if prec =? 1 then Some (53, -1021 - 53)
         else if prec =? 2 then Some (113, -16381 - 113)
         else None) with
  | None => Some (f, f128_of_i32 0)                         (* [comment removed for export] *)
  | Some (bits, emin) =>
  match fs_ws_loop fuelc f with                             (* [comment removed for export] *)
  | None => None
  | Some (c, f) =>
  let '(sign, c, f) :=
    if (c =? 43) || (c =? 45) then
      let sign := 1 - 2 * b2z (c =? 45) in
      let '(c, f) := sh_getc f in (sign, c, f)              (* [comment removed for export] *)
    else (1, c, f) in
  match fs_inf_loop 9%nat (0, c, f) with
  | None => None
  | Some (i, c, f) =>
  if (i =? 3) || (i =? 8) || ((3 <? i) && nz pok) then
    let f := if negb (i =? 8) then
               let f := sh_unget f in                       (* [comment removed for export] *)
               if nz pok then fs_unget_loop (Z.to_nat (i - 3)) f else f   (* [comment removed for export] *)
             else f in
    Some (f, if 0 <? sign then C_INF else C_NINF)           (* [comment removed for export] *)
  else
  match (if i =? 0 then fs_nan_loop 4%nat (0, c, f) else Some (i, c, f)) with
  | None => None
  | Some (i, c, f) =>
  if i =? 3 then
    let '(c2, f) := sh_getc f in                            (* [comment removed for export] *)
    if negb (c2 =? 40) then
      Some (sh_unget f, C_NAN)                              (* [comment removed for export] *)
    else
      match fs_par_loop fuelc (1, f) with
      | None => None
      | Some (i, c, f) =>
        if c =? 41 then Some (f, C_NAN)
        else
          let f := sh_unget f in                            (* [comment removed for export] *)
          if negb (nz pok) then
            Some (sh_lim0 f, f128_of_i32 0)                 (* [comment removed for export] *)
          else
            Some (fs_unget_loop (Z.to_nat i) f, C_NAN)      (* [comment removed for export] *)
      end
  else if nz i then
    let f := sh_unget f in                                  (* [comment removed for export] *)
    Some (sh_lim0 f, f128_of_i32 0)                         (* [comment removed for export] *)
  else if c =? 48 then
    let '(c2, f) := sh_getc f in                            (* [comment removed for export] *)
    if Z.lor c2 32 =? 120 then None                         (* [comment removed for export] *)
    else decfloat fuelc (sh_unget f) 48 bits emin sign pok  (* [comment removed for export] *)
  else decfloat fuelc f c bits emin sign pok
  end end end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fuel_of (s : list Z) : nat := S (S (length s)).

(* [comment removed for export] *)
Definition scan_strtod (s : list Z) : option (Z * Z) :=
  let f := mkSh s 0 0 0 false false in                      (* [comment removed for export] *)
  match floatscan (fuel_of s) f 1 1 with                    (* [comment removed for export] *)
  | None => None
  | Some (f, y) => Some (f128_to_d y, sh_cnt f)             (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Fixpoint strlen_loop (fuel : nat) (s : list Z) (n : Z) : option Z :=
  match fuel with
  | O => None
  | S fu => if nz (znth s n) then strlen_loop fu s (n + 1) else Some n
  end.

(* [comment removed for export] *)
Definition scan_sscanf_lg (s : list Z) : option (Z * option Z) :=
  match strlen_loop (fuel_of s) s 0 with
  | None => None
  | Some n =>
  let f := mkSh s 0 0 n true false in                       (* [comment removed for export] *)
  let f := sh_lim0 f in                                     (* [comment removed for export] *)
  match fs_ws_loop (fuel_of s) f with                       (* [comment removed for export] *)
  | None => None
  | Some (_, f) =>
  let f := sh_unget f in                                    (* [comment removed for export] *)
  let f := sh_lim0 f in                                     (* [comment removed for export] *)
  let '(c, f) := sh_getc f in                               (* [comment removed for export] *)
  if c <? 0 then Some (-1, None)                            (* [comment removed for export] *)
  else
  let f := sh_unget f in                                    (* [comment removed for export] *)
  match floatscan (fuel_of s) f 1 0 with                    (* [comment removed for export] *)
  | None => None
  | Some (f, y) =>
    if sh_cnt f =? 0 then Some (0, None)                    (* [comment removed for export] *)
    else Some (1, Some (f128_to_d y))                       (* [comment removed for export] *)
  end end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Example ex_strtod_1_5 : scan_strtod [49; 46; 53; 0] (* [comment removed for export] *) = Some (0x3ff8000000000000, 3).
Proof. vm_compute. reflexivity. Qed.
Example ex_strtod_1e : scan_strtod [49; 101; 43; 0] (* [comment removed for export] *) = Some (0x3ff0000000000000, 1).
Proof. vm_compute. reflexivity. Qed.
Example ex_strtod_dot : scan_strtod [45; 46; 101; 53; 0] (* [comment removed for export] *) = Some (0, 0).
Proof. vm_compute. reflexivity. Qed.
Example ex_strtod_0_1 : scan_strtod [48; 46; 49; 0] (* [comment removed for export] *) = Some (0x3fb999999999999a, 3).
Proof. vm_compute. reflexivity. Qed.
Example ex_strtod_m0 : scan_strtod [45; 48; 0] (* [comment removed for export] *) = Some (0x8000000000000000, 2).
Proof. vm_compute. reflexivity. Qed.
Example ex_strtod_tie : scan_strtod [57; 48; 48; 55; 49; 57; 57; 50; 53; 52; 55; 52; 48; 57; 57; 51; 0] (* [comment removed for export] *) = Some (0x4340000000000000, 16).
Proof. vm_compute. reflexivity. Qed.
Example ex_strtod_sub : scan_strtod [50; 46; 52; 55; 48; 51; 50; 56; 50; 50; 57; 50; 48; 54; 50; 51; 50; 56; 101; 45; 51; 50; 52; 0] (* [comment removed for export] *) = Some (1, 23).
Proof. vm_compute. reflexivity. Qed.
Example ex_strtod_hex : scan_strtod [48; 120; 49; 112; 52; 0] (* [comment removed for export] *) = None.
Proof. vm_compute. reflexivity. Qed.
Example ex_sscanf_1e : scan_sscanf_lg [49; 101; 43; 0] (* [comment removed for export] *) = Some (0, None).
Proof. vm_compute. reflexivity. Qed.
Example ex_sscanf_sp : scan_sscanf_lg [32; 32; 0] (* [comment removed for export] *) = Some (-1, None).
Proof. vm_compute. reflexivity. Qed.
Example ex_sscanf_ok : scan_sscanf_lg [32; 49; 50; 46; 53; 101; 49; 120; 0] (* [comment removed for export] *) = Some (1, Some 0x405f400000000000).
Proof. vm_compute. reflexivity. Qed.
Example ex_sscanf_inf : scan_sscanf_lg [45; 105; 110; 102; 0] (* [comment removed for export] *) = Some (1, Some 0xfff0000000000000).
Proof. vm_compute. reflexivity. Qed.
