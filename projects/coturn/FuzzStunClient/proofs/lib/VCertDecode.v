(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From Corelib Require Import PrimInt63 PrimString PrimArray.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs VCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Decoder.
Variable s : PrimString.string.

Let inc (i : int) : int := PrimInt63.add i 1%uint63.

(* [comment removed for export] *)
Definition dz (d : int) : Z :=
  (if PrimInt63.ltb d 22%uint63 then (if PrimInt63.ltb d 11%uint63 then (if PrimInt63.ltb d 5%uint63 then (if PrimInt63.ltb d 2%uint63 then (if PrimInt63.ltb d 1%uint63 then 0 else 1) else (if PrimInt63.ltb d 3%uint63 then 2 else (if PrimInt63.ltb d 4%uint63 then 3 else 4))) else (if PrimInt63.ltb d 8%uint63 then (if PrimInt63.ltb d 6%uint63 then 5 else (if PrimInt63.ltb d 7%uint63 then 6 else 7)) else (if PrimInt63.ltb d 9%uint63 then 8 else (if PrimInt63.ltb d 10%uint63 then 9 else 10)))) else (if PrimInt63.ltb d 16%uint63 then (if PrimInt63.ltb d 13%uint63 then (if PrimInt63.ltb d 12%uint63 then 11 else 12) else (if PrimInt63.ltb d 14%uint63 then 13 else (if PrimInt63.ltb d 15%uint63 then 14 else 15))) else (if PrimInt63.ltb d 19%uint63 then (if PrimInt63.ltb d 17%uint63 then 16 else (if PrimInt63.ltb d 18%uint63 then 17 else 18)) else (if PrimInt63.ltb d 20%uint63 then 19 else (if PrimInt63.ltb d 21%uint63 then 20 else 21))))) else (if PrimInt63.ltb d 33%uint63 then (if PrimInt63.ltb d 27%uint63 then (if PrimInt63.ltb d 24%uint63 then (if PrimInt63.ltb d 23%uint63 then 22 else 23) else (if PrimInt63.ltb d 25%uint63 then 24 else (if PrimInt63.ltb d 26%uint63 then 25 else 26))) else (if PrimInt63.ltb d 30%uint63 then (if PrimInt63.ltb d 28%uint63 then 27 else (if PrimInt63.ltb d 29%uint63 then 28 else 29)) else (if PrimInt63.ltb d 31%uint63 then 30 else (if PrimInt63.ltb d 32%uint63 then 31 else 32)))) else (if PrimInt63.ltb d 39%uint63 then (if PrimInt63.ltb d 36%uint63 then (if PrimInt63.ltb d 34%uint63 then 33 else (if PrimInt63.ltb d 35%uint63 then 34 else 35)) else (if PrimInt63.ltb d 37%uint63 then 36 else (if PrimInt63.ltb d 38%uint63 then 37 else 38))) else (if PrimInt63.ltb d 42%uint63 then (if PrimInt63.ltb d 40%uint63 then 39 else (if PrimInt63.ltb d 41%uint63 then 40 else 41)) else (if PrimInt63.ltb d 43%uint63 then 42 else (if PrimInt63.ltb d 44%uint63 then 43 else 44)))))).

(* [comment removed for export] *)
Fixpoint pvar (fuel : nat) (i : int) (acc : Z) : Z * int :=
  match fuel with
  | O => (acc, i)
  | S f =>
      let d := PrimInt63.sub (PrimString.get s i) 35%uint63 in
      if PrimInt63.ltb d 45%uint63 then (acc * 45 + dz d, inc i)
      else pvar f (inc i) (acc * 45 + dz (PrimInt63.sub d 45%uint63))
  end.

Definition zz (z : Z) : Z := if Z.even z then Z.div2 z else - Z.div2 (z + 1).

Fixpoint pvari (fuel : nat) (i : int) (acc : int) : int * int :=
  match fuel with
  | O => (acc, i)
  | S f =>
      let d := PrimInt63.sub (PrimString.get s i) 35%uint63 in
      if PrimInt63.ltb d 45%uint63 then (PrimInt63.add (PrimInt63.mul acc 45%uint63) d, inc i)
      else pvari f (inc i) (PrimInt63.add (PrimInt63.mul acc 45%uint63) (PrimInt63.sub d 45%uint63))
  end.

(* [comment removed for export] *)
Fixpoint ipos (fuel : nat) (x : int) : positive :=
  match fuel with
  | O => xH
  | S f =>
      if PrimInt63.eqb x 1%uint63 then xH
      else let q := PrimInt63.lsr x 1%uint63 in
           if PrimInt63.eqb (PrimInt63.land x 1%uint63) 0%uint63 then xO (ipos f q) else xI (ipos f q)
  end.
(* [comment removed for export] *)
Definition ZT_N : int := 16384%uint63.
Fixpoint ztab_fill (n : nat) (neg : bool) (i : int) (t : array Z) : array Z :=
  match n with
  | O => t
  | S n' => if PrimInt63.ltb i ZT_N
            then ztab_fill n' neg (PrimInt63.add i 1%uint63)
                           (PrimArray.set t i (if neg then Zneg (ipos 64 i) else Zpos (ipos 64 i)))
            else t
  end.
Definition TAB_FUEL : nat := Nat.mul 128 128.
Definition ZTAB : array Z := ztab_fill TAB_FUEL false 1%uint63 (PrimArray.make ZT_N Z0).
Definition NTAB : array Z := ztab_fill TAB_FUEL true 1%uint63 (PrimArray.make ZT_N Z0).
Definition NT_N : int := 2048%uint63.
Fixpoint nattab_fill (n : nat) (i : int) (prev : nat) (t : array nat) : array nat :=
  match n with
  | O => t
  | S n' => if PrimInt63.ltb i NT_N
            then nattab_fill n' (PrimInt63.add i 1%uint63) (S prev) (PrimArray.set t i (S prev))
            else t
  end.
Definition NATTAB : array nat := nattab_fill TAB_FUEL 1%uint63 O (PrimArray.make NT_N O).

Definition iz (x : int) : Z := if PrimInt63.ltb x ZT_N then PrimArray.get ZTAB x else Zpos (ipos 64 x).
(* [comment removed for export] *)
Definition izz (x : int) : Z :=
  if PrimInt63.eqb (PrimInt63.land x 1%uint63) 0%uint63 then iz (PrimInt63.lsr x 1%uint63)
  else let y := PrimInt63.lsr (PrimInt63.add x 1%uint63) 1%uint63 in
       if PrimInt63.ltb y ZT_N then PrimArray.get NTAB y else Zneg (ipos 64 y).

(* [comment removed for export] *)
Definition pu0 (i : int) : Z * int := let (v, i1) := pvari 16 i 0%uint63 in (iz v, i1).
Definition ps0 (i : int) : Z * int := let (v, i1) := pvari 16 i 0%uint63 in (izz v, i1).
Fixpoint plimbs (n : nat) (i : int) (acc : Z) : Z * int :=
  match n with
  | O => (acc, i)
  | S n' => let (l, i1) := pu0 i in plimbs n' i1 (acc * 4294967296 + l)
  end.
Definition pbig (i : int) : Z * int :=
  let (sg, i1) := pu0 (inc i) in let (n, i2) := pu0 i1 in
  let (v, i3) := plimbs (Z.to_nat n) i2 0 in ((if Z.eqb sg 1 then - v else v), i3).
Definition is_big (i : int) : bool := PrimInt63.eqb (PrimString.get s i) 33%uint63.
Definition pu (i : int) : Z * int := if is_big i then pbig i else pu0 i.
Definition ps (i : int) : Z * int := if is_big i then pbig i else ps0 i.
Definition pn (i : int) : nat * int :=
  if is_big i then let (v, i1) := pu i in (Z.to_nat v, i1)
  else let (x, i1) := pvari 16 i 0%uint63 in
       ((if PrimInt63.ltb x NT_N then PrimArray.get NATTAB x else Z.to_nat (iz x)), i1).
Definition pp (i : int) : positive * int := let (v, i1) := pu i in (Z.to_pos v, i1).

Fixpoint plist {A : Type} (p : int -> A * int) (n : nat) (i : int) : list A * int :=
  match n with
  | O => ([], i)
  | S n' => let (x, i1) := p i in let (t, i2) := plist p n' i1 in (x :: t, i2)
  end.
Definition pnlist {A : Type} (p : int -> A * int) (i : int) : list A * int :=
  let (n, i1) := pn i in plist p n i1.

Definition pterm (i : int) : (sym * Z) * int :=
  let (sy, i1) := pp i in let (k, i2) := ps i1 in ((sy, k), i2).
Definition plin (i : int) : lin * int :=
  let (n, i1) := pn i in let (c, i2) := ps i1 in let (ts, i3) := plist pterm n i2 in (mkLin c ts, i3).

Definition preg (i : int) : (Z * lin) * int :=
  let (r, i1) := pu i in let (e, i2) := plin i1 in ((r, e), i2).
Definition pslot (i : int) : (Z * (Z * lin)) * int :=
  let (o, i1) := ps i in let (w, i2) := pu i1 in let (e, i3) := plin i2 in ((o, (w, e)), i3).
Definition pglob (i : int) : (Z * (Z * lin)) * int :=
  let (a, i1) := pu i in let (w, i2) := pu i1 in let (e, i3) := plin i2 in ((a, (w, e)), i3).
Definition pbox (i : int) : (sym * itv) * int :=
  let (sy, i1) := pp i in let (k, i2) := pu i1 in
  let (lo, i3) := (if Z.odd k then let (v, j) := ps i2 in (Some v, j) else (None, i2)) in
  let (hi, i4) := (if Z.leb 2 k then let (v, j) := ps i3 in (Some v, j) else (None, i3)) in
  ((sy, (lo, hi)), i4).
Definition pcong (i : int) : (sym * (Z * Z)) * int :=
  let (sy, i1) := pp i in let (m, i2) := pu i1 in let (r, i3) := ps i2 in ((sy, (m, r)), i3).
Definition pnul (i : int) : (Z * Z) * int :=
  let (lo, i1) := ps i in let (hi, i2) := ps i1 in ((lo, hi), i2).
Definition pvalset (i : int) : (sym * list Z) * int :=
  let (sy, i1) := pp i in let (vs, i2) := pnlist ps i1 in ((sy, vs), i2).
Definition pkind (i : int) : ckind * int :=
  let (k, i1) := pu i in ((if Z.eqb k 0 then CK_lt else if Z.eqb k 1 then CK_ltu else CK_eq), i1).
Definition pconddef (i : int) : (sym * (ckind * lin * lin)) * int :=
  let (sy, i1) := pp i in let (k, i2) := pkind i1 in let (x, i3) := plin i2 in let (y, i4) := plin i3 in
  ((sy, (k, x, y)), i4).
Definition pmoddef (i : int) : (sym * (lin * Z)) * int :=
  let (sy, i1) := pp i in let (x, i2) := plin i1 in let (m, i3) := pu i2 in ((sy, (x, m)), i3).

Definition pstate (i : int) : cstate * int :=
  let (regs, i1) := pnlist preg i in
  let (slots, i2) := pnlist pslot i1 in
  let (globs, i3) := pnlist pglob i2 in
  let (box, i4) := pnlist pbox i3 in
  let (cong, i5) := pnlist pcong i4 in
  let (cons, i6) := pnlist plin i5 in
  let (nul, i7) := pnlist pnul i6 in
  let (vs, i8) := pnlist pvalset i7 in
  let (cd, i9) := pnlist pconddef i8 in
  let (md, i10) := pnlist pmoddef i9 in
  let (nx, i11) := pp i10 in
  (mkCS regs slots globs box cong cons nul vs cd md nx, i11).

Definition pcut (i : int) : vcut * int :=
  let (pc, i1) := pu i in
  let (ctx, i2) := pnlist pu i1 in
  let (sts, i3) := pnlist pstate i2 in
  let (rks, i4) := pnlist plin i3 in
  (mkCut pc ctx sts rks, i4).

Definition prange (i : int) : (Z * Z) * int :=
  let (a, i1) := ps i in let (b, i2) := ps i1 in ((a, b), i2).
Definition purange (i : int) : (Z * Z) * int :=
  let (a, i1) := pu i in let (b, i2) := pu i1 in ((a, b), i2).
Definition pcall (i : int) : vcall * int :=
  let (pc, i1) := pu i in let (t, i2) := pu i1 in let (v, i3) := pu i2 in (mkCall pc t v, i3).

Definition punit (i : int) : vunit * int :=
  let (entry, i1) := pu i in
  let (vid, i2) := pu i1 in
  let (sp, i3) := ps i2 in
  let (sclo, i4) := pu i3 in
  let (schi, i5) := pu i4 in
  let (pre, i6) := pstate i5 in
  let (cuts, i7) := pnlist pcut i6 in
  let (exits, i8) := pnlist pstate i7 in
  let (ws, i9) := pnlist prange i8 in
  let (wg, i10) := pnlist purange i9 in
  let (er, i11) := pu i10 in
  let (own, i12) := ps i11 in
  let (calls, i13) := pnlist pcall i12 in
  let (fuel, i14) := pu i13 in
  let (rf, i15) := pu i14 in
  let (root, i16) := (if Z.eqb rf 1 then let (r, j) := pu i15 in (Some r, j) else (None, i15)) in
  let (prio, i17) := pu i16 in
  (mkUnit entry vid sp (sclo, schi) pre cuts exits ws wg (Z.eqb er 1) own calls (Z.to_N fuel) root prio, i17).

Definition decode_cert_at (i : int) : vcert * int := pnlist punit i.
End Decoder.

Definition decode_cert (s : PrimString.string) : vcert := fst (decode_cert_at s 0%uint63).
