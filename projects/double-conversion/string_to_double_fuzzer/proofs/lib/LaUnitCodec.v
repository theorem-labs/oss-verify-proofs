(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From Stdlib Require Import Uint63 PrimString.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LaState LaCheck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LAS LAC.

Module LAUC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition uc_inc (i : int) : int := PrimInt63.sub i 9223372036854775807%uint63.
Fixpoint uc_hex (f : nat) (s : string) (i acc : int) : int * int :=
  match f with
  | O => (acc, i)
  | S f' =>
      let d := PrimInt63.sub (PrimString.get s i) 48%uint63 in
      if PrimInt63.ltb d 16%uint63
      then uc_hex f' s (uc_inc i) (PrimInt63.lor (PrimInt63.lsl acc 4%uint63) d)
      else (acc, i)
  end.
Fixpoint uc_pos (f : nat) (x : int) : positive :=
  match f with
  | O => xH
  | S f' =>
      if PrimInt63.leb x 1%uint63 then xH
      else if PrimInt63.eqb (PrimInt63.land x 1%uint63) 0%uint63 then xO (uc_pos f' (PrimInt63.lsr x 1%uint63))
      else xI (uc_pos f' (PrimInt63.lsr x 1%uint63))
  end.
Definition uc_Zp (x : int) : Z := if PrimInt63.eqb x 0%uint63 then Z0 else Zpos (uc_pos 63 x).
Definition uc_Zn (x : int) : Z := if PrimInt63.eqb x 0%uint63 then Z0 else Zneg (uc_pos 63 x).
Fixpoint uc_nat (f : nat) (x : int) : nat :=
  match f with
  | O => O
  | S f' =>
      if PrimInt63.eqb x 0%uint63 then O
      else let h := uc_nat f' (PrimInt63.lsr x 1%uint63) in
           if PrimInt63.eqb (PrimInt63.land x 1%uint63) 0%uint63 then Nat.add h h else S (Nat.add h h)
  end.
Definition uc_Zsmall (s : string) (i : int) : Z * int :=
  let c := PrimString.get s i in
  let '(v, j) := uc_hex 16 s (uc_inc i) 0%uint63 in
  if PrimInt63.eqb c 45%uint63 then (uc_Zn v, j) else (uc_Zp v, j).
Definition uc_Z (s : string) (i : int) : Z * int :=
  if PrimInt63.eqb (PrimString.get s i) 94%uint63 then
    let '(hi, j) := uc_Zsmall s (uc_inc i) in
    let '(lo, k) := uc_Zsmall s j in
    (Z.add (Z.shiftl hi 60) lo, k)
  else uc_Zsmall s i.
(* [comment removed for export] *)
Definition uc_N (s : string) (i : int) : nat * int :=
  let '(v, j) := uc_hex 16 s (uc_inc i) 0%uint63 in
  ((if PrimInt63.ltb v 16777216%uint63 then uc_nat 63 v else O), j).
Fixpoint uc_list {A : Type} (rd : string -> int -> A * int) (n : nat) (s : string) (i : int) : list A * int :=
  match n with
  | O => (nil, i)
  | S n' => let '(x, j) := rd s i in let '(l, k) := uc_list rd n' s j in (x :: l, k)
  end.
Definition uc_listN {A : Type} (rd : string -> int -> A * int) (s : string) (i : int) : list A * int :=
  let '(n, j) := uc_N s i in uc_list rd n s j.
Definition uc_bool (s : string) (i : int) : bool * int := (PrimInt63.eqb (PrimString.get s i) 35%uint63, uc_inc i).

(* [comment removed for export] *)
Definition uc_pairNZ (s : string) (i : int) : (nat * Z) * int :=
  let '(x, j) := uc_N s i in let '(k, l) := uc_Z s j in ((x, k), l).
Definition uc_lin (s : string) (i : int) : lin * int :=
  let '(c, j) := uc_Z s i in let '(ts, k) := uc_listN uc_pairNZ s j in (Lin c ts, k).
Definition uc_oz (s : string) (i : int) : option Z * int :=
  if PrimInt63.eqb (PrimString.get s i) 33%uint63 then (None, uc_inc i)
  else let '(z, j) := uc_Z s i in (Some z, j).
Definition uc_itv (s : string) (i : int) : itv * int :=
  let '(lo, j) := uc_oz s i in let '(hi, k) := uc_oz s j in (Itv lo hi, k).
Definition uc_cmpk (c : int) : cmpk :=
  if PrimInt63.eqb c 48%uint63 then CK_LTU else if PrimInt63.eqb c 49%uint63 then CK_LT else CK_EQ.
Definition uc_aval (s : string) (i : int) : aval * int :=
  let c := PrimString.get s i in
  let i1 := uc_inc i in
  if PrimInt63.eqb c 33%uint63 then (Top, i1)
  else if PrimInt63.eqb c 36%uint63 then let '(l, j) := uc_lin s i1 in (LV l, j)
  else if PrimInt63.eqb c 37%uint63 then let '(a, j) := uc_lin s i1 in let '(b, k) := uc_lin s j in (XV a b, k)
  else let '(neg, i2) := uc_bool s i1 in
       let k := uc_cmpk (PrimString.get s i2) in
       let '(a, j) := uc_lin s (uc_inc i2) in let '(b, l) := uc_lin s j in (CV neg k a b, l).
Definition uc_pairNI (s : string) (i : int) : (nat * itv) * int :=
  let '(x, j) := uc_N s i in let '(v, k) := uc_itv s j in ((x, v), k).
Definition uc_ctx (s : string) (i : int) : ctx * int :=
  let '(fs, j) := uc_listN uc_lin s i in let '(bs, k) := uc_listN uc_pairNI s j in (Ctx fs bs, k).

(* [comment removed for export] *)
Definition uc_cell (s : string) (i : int) : cell * int :=
  let '(o, j) := uc_Z s i in let '(w, k) := uc_Z s j in let '(v, l) := uc_aval s k in (Cell o w v, l).
Definition uc_oafact (s : string) (i : int) : option afact * int :=
  if PrimInt63.eqb (PrimString.get s i) 33%uint63 then (None, uc_inc i)
  else let '(ln, j) := uc_lin s (uc_inc i) in let '(blo, k) := uc_Z s j in let '(bhi, l) := uc_Z s k in
       let '(fi, m) := uc_itv s l in (Some (AFact ln blo bhi fi), m).
Definition uc_arr (s : string) (i : int) : arr * int :=
  let '(lo, j) := uc_Z s i in let '(hi, k) := uc_Z s j in let '(f, l) := uc_oafact s k in (Arr lo hi f, l).
Definition uc_frame (s : string) (i : int) : frame * int :=
  let '(sy, j) := uc_N s i in let '(cls, k) := uc_Z s j in let '(cs, l) := uc_listN uc_cell s k in let '(ars, m) := uc_listN uc_arr s l in
  let '(sh, n) := uc_listN uc_Z s m in let '(fl, o) := uc_N s n in (Frame sy cls cs ars sh fl, o).
Definition uc_pairZZ (s : string) (i : int) : (Z * Z) * int :=
  let '(a, j) := uc_Z s i in let '(b, k) := uc_Z s j in ((a, b), k).
Definition uc_abs (snap : list (Z * Z)) (s : string) (i : int) : list (Z * Z) * int :=
  let c := PrimString.get s i in
  if PrimInt63.eqb c 33%uint63 then (nil, uc_inc i)
  else if PrimInt63.eqb c 35%uint63 then (snap, uc_inc i)
  else uc_listN uc_pairZZ s i.
Definition uc_pcache (s : string) (i : int) : (lin * Z * sym) * int :=
  let '(o, j) := uc_lin s i in let '(sx, k) := uc_Z s j in let '(x, l) := uc_N s k in ((o, sx, x), l).
Definition uc_pay (s : string) (i : int) : (lin * itv) * int :=
  let '(o, j) := uc_lin s i in let '(v, k) := uc_itv s j in ((o, v), k).

(* [comment removed for export] *)
Definition uc_state (snap : list (Z * Z)) (s : string) (i : int) : astate * int :=
  let '(pc, i1) := uc_Z s i in
  let '(rg, i2) := uc_listN uc_aval s i1 in
  let '(cx, i3) := uc_ctx s i2 in
  let '(nx, i4) := uc_N s i3 in
  let '(stk, i5) := uc_listN uc_cell s i4 in
  let '(ars, i6) := uc_listN uc_arr s i5 in
  let '(ab, i7) := uc_abs snap s i6 in
  let '(pch, i8) := uc_listN uc_pcache s i7 in
  let '(rv, i9) := uc_oz s i8 in
  let '(dp, i10) := uc_N s i9 in
  let '(py, i11) := uc_listN uc_pay s i10 in
  let '(frs, i12) := uc_listN uc_frame s i11 in
  (AS pc rg cx nx stk ars ab pch rv dp py frs, i12).
Definition uc_cert (s : string) (i : int) : (lin * farkas) * int :=
  let '(g, j) := uc_lin s i in let '(d, k) := uc_Z s j in let '(ls, l) := uc_listN uc_Z s k in ((g, Farkas d ls), l).
Definition uc_bind (s : string) (i : int) : (sym * lin) * int :=
  let '(x, j) := uc_N s i in let '(l, k) := uc_lin s j in ((x, l), k).
Definition uc_hint (s : string) (i : int) : arrival_hint * int :=
  let '(src, j) := uc_N s i in let '(p, k) := uc_listN uc_bool s j in
  let '(cs, l) := uc_listN uc_cert s k in let '(bs, m) := uc_listN uc_bind s l in (AH src p cs bs, m).
Definition uc_cut (snap : list (Z * Z)) (s : string) (i : int) : cutpoint * int :=
  let '(pc, j) := uc_Z s i in let '(st, k) := uc_state snap s j in let '(mu, l) := uc_listN uc_lin s k in
  let '(hs, m) := uc_listN uc_hint s l in let '(cd, n) := uc_listN uc_lin s m in (CP pc st mu hs cd, n).

(* [comment removed for export] *)
Definition dec_cuts (snap : list (Z * Z)) (s : string) : list cutpoint := fst (uc_listN (uc_cut snap) s 0%uint63).
End LAUC.
