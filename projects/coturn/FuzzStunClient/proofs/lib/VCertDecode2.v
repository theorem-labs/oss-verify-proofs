(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From Corelib Require Import PrimInt63 PrimString PrimArray.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs VCert VState2 VCert2 VCertDecode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Decoder2.
Variable s : PrimString.string.


(* [comment removed for export] *)
Definition pstate_body (i : int) : (positive -> cstate) * int :=
  let (regs, i1) := pnlist s (preg s) i in
  let (slots, i2) := pnlist s (pslot s) i1 in
  let (globs, i3) := pnlist s (pglob s) i2 in
  let (box, i4) := pnlist s (pbox s) i3 in
  let (cong, i5) := pnlist s (pcong s) i4 in
  let (cons, i6) := pnlist s (plin s) i5 in
  let (nul, i7) := pnlist s (pnul s) i6 in
  let (vs, i8) := pnlist s (pvalset s) i7 in
  let (cd, i9) := pnlist s (pconddef s) i8 in
  let (md, i10) := pnlist s (pmoddef s) i9 in
  ((fun nx => mkCS regs slots globs box cong cons nul vs cd md nx), i10).

Definition pkind (i : int) : skind * int :=
  let (k, i1) := pu s i in
  if Z.eqb k 0 then let (cid, i2) := pu s i1 in let (fl, i3) := pp s i2 in (SK_fake cid fl, i3)
  else if Z.eqb k 1 then (SK_arg, i1)
  else if Z.eqb k 2 then let (ow, i2) := pp s i1 in (SK_flag ow, i2)
  else let (of_, i2) := pp s i1 in (SK_shadow of_, i2).

Definition prgn (i : int) : srgn * int :=
  let (b, i1) := pp s i in
  let (disp, i2) := pu s i1 in
  let (k, i3) := pkind i2 in
  let (lo, i4) := ps s i3 in
  let (hi, i5) := ps s i4 in
  let (w, i6) := pnlist s (prange s) i5 in
  let (cells, i7) := pnlist s (pslot s) i6 in
  let (nul, i8) := pnlist s (prange s) i7 in
  let (hb, i9) := pu s i8 in
  let (b8, i10) := (if Z.eqb hb 1 then let (x, j) := pp s i9 in (Some x, j) else (None, i9)) in
  (mkSR b disp k lo hi w cells nul b8, i10).

Definition pdivdef (i : int) : (sym * (lin * Z)) * int :=
  let (q, i1) := pp s i in let (x, i2) := plin s i1 in let (m, i3) := pu s i2 in ((q, (x, m)), i3).

Definition pstate2 (i : int) : cstate2 * int :=
  let (mk, i1) := pstate_body i in
  let (rg, i2) := pnlist s prgn i1 in
  let (dd, i3) := pnlist s pdivdef i2 in
  let (lv, i4) := pnlist s (pp s) i3 in
  let (nx, i5) := pp s i4 in
  (mkCS2 (mk nx) rg dd lv, i5).

Definition pcut2 (i : int) : vcut2 * int :=
  let (pc, i1) := pu s i in
  let (ctx, i2) := pnlist s (pu s) i1 in
  let (sts, i3) := pnlist s pstate2 i2 in
  let (rks, i4) := pnlist s (plin s) i3 in
  let (tps, i5) := pnlist s (pnlist s (pu s)) i4 in
  (mkCut2 pc ctx sts rks tps, i5).

Definition pwrgn (i : int) : (Z * (Z * Z)) * int :=
  let (a, i1) := pu s i in let (lo, i2) := ps s i1 in let (hi, i3) := ps s i2 in ((a, (lo, hi)), i3).

Definition punit2 (i : int) : vunit2 * int :=
  let (u, i1) := punit s i in
  let (pre, i2) := pstate2 i1 in
  let (cuts, i3) := pnlist s pcut2 i2 in
  let (exits, i4) := pnlist s pstate2 i3 in
  let (wr, i5) := pnlist s pwrgn i4 in
  let (fd, i6) := pu s i5 in
  let (tp, i7) := pnlist s (pu s) i6 in
  (mkUnit2 u pre cuts exits wr fd tp, i7).

Definition decode_cert2_at (i : int) : vcert2 * int := pnlist s punit2 i.
End Decoder2.

Definition decode_cert2 (s : PrimString.string) : vcert2 := fst (decode_cert2_at s 0%uint63).

(* [comment removed for export] *)
Record dict2 := mkDict2 {
  d_regs : array (list (Z * lin)) ; d_slots : array (list (Z * (Z * lin))) ; d_box : array (list (sym * itv)) ;
  d_cons : array (list lin) ; d_rgn : array (list srgn) }.

Section DictDecoder.
Variable s : PrimString.string.

Fixpoint dfill {A : Type} (n : nat) (p : int -> A * int) (a : array A) (k : int) (i : int) : array A * int :=
  match n with
  | O => (a, i)
  | S n' => let (x, i1) := p i in dfill n' p (PrimArray.set a k x) (PrimInt63.add k 1%uint63) i1
  end.

(* [comment removed for export] *)
Definition pdict_tab {A : Type} (p : int -> A * int) (i : int) : array (list A) * int :=
  let (n, i1) := pn s i in
  dfill n (pnlist s p) (PrimArray.make (Uint63.of_Z (Z.of_nat n + 1)) []) 0%uint63 i1.

Definition decode_dict2 : dict2 :=
  let (a1, i1) := pdict_tab (preg s) 0%uint63 in
  let (a2, i2) := pdict_tab (pslot s) i1 in
  let (a3, i3) := pdict_tab (pbox s) i2 in
  let (a4, i4) := pdict_tab (plin s) i3 in
  let (a5, i5) := pdict_tab (prgn s) i4 in
  mkDict2 a1 a2 a3 a4 a5.
End DictDecoder.

Section DecoderD.
Variable s : PrimString.string.
Variable T : dict2.

(* [comment removed for export] *)
Definition pnlist_d {A : Type} (tab : array (list A)) (p : int -> A * int) (i : int) : list A * int :=
  let (h, i1) := pu s i in
  if Z.even h then plist p (Z.to_nat (Z.div2 h)) i1 else (PrimArray.get tab (Uint63.of_Z (Z.div2 h)), i1).

Definition pstate_body_d (i : int) : (positive -> cstate) * int :=
  let (regs, i1) := pnlist_d (d_regs T) (preg s) i in
  let (slots, i2) := pnlist_d (d_slots T) (pslot s) i1 in
  let (globs, i3) := pnlist s (pglob s) i2 in
  let (box, i4) := pnlist_d (d_box T) (pbox s) i3 in
  let (cong, i5) := pnlist s (pcong s) i4 in
  let (cons, i6) := pnlist_d (d_cons T) (plin s) i5 in
  let (nul, i7) := pnlist s (pnul s) i6 in
  let (vs, i8) := pnlist s (pvalset s) i7 in
  let (cd, i9) := pnlist s (pconddef s) i8 in
  let (md, i10) := pnlist s (pmoddef s) i9 in
  ((fun nx => mkCS regs slots globs box cong cons nul vs cd md nx), i10).

Definition pstate2_d (i : int) : cstate2 * int :=
  let (mk, i1) := pstate_body_d i in
  let (rg, i2) := pnlist_d (d_rgn T) (prgn s) i1 in
  let (dd, i3) := pnlist s (pdivdef s) i2 in
  let (lv, i4) := pnlist s (pp s) i3 in
  let (nx, i5) := pp s i4 in
  (mkCS2 (mk nx) rg dd lv, i5).

Definition pcut2_d (i : int) : vcut2 * int :=
  let (pc, i1) := pu s i in
  let (ctx, i2) := pnlist s (pu s) i1 in
  let (sts, i3) := pnlist s pstate2_d i2 in
  let (rks, i4) := pnlist s (plin s) i3 in
  let (tps, i5) := pnlist s (pnlist s (pu s)) i4 in
  (mkCut2 pc ctx sts rks tps, i5).

Definition punit2_d (i : int) : vunit2 * int :=
  let (u, i1) := punit s i in
  let (pre, i2) := pstate2_d i1 in
  let (cuts, i3) := pnlist s pcut2_d i2 in
  let (exits, i4) := pnlist s pstate2_d i3 in
  let (wr, i5) := pnlist s (pwrgn s) i4 in
  let (fd, i6) := pu s i5 in
  let (tp, i7) := pnlist s (pu s) i6 in
  (mkUnit2 u pre cuts exits wr fd tp, i7).
End DecoderD.

Definition decode_cert2_d (T : dict2) (s : PrimString.string) : vcert2 := fst (pnlist s (punit2_d s T) 0%uint63).
