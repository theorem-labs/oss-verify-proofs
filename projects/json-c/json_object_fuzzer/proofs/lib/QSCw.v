(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require G.T_pe.

From Stdlib Require Import ZArith List Lia Bool String Ascii.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq2.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Open Scope mspec_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G Require T_printf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := tt.
End GwI.

Notation parg := G.T_printf.parg.
Notation PA_s := G.T_printf.PA_s.
Notation PA_i := G.T_printf.PA_i.
Notation PA_u := G.T_printf.PA_u.
Notation PA_g := G.T_printf.PA_g.
Notation PA_li := G.T_printf.PA_li.
Notation PA_lu := G.T_printf.PA_lu.

Definition is_digit (c : Z) : bool := (48 <=? c) && (c <=? 57).
Lemma gw_eq_is_digit : @is_digit = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.is_digit) (@is_digit)). Proof. unfold is_digit, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.is_digit; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_is_digit : gw_eqs.

Definition T_PTR : Z := 9.
Lemma gw_eq_T_PTR : @T_PTR = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.T_PTR) (@T_PTR)). Proof. unfold T_PTR, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.T_PTR; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_T_PTR : gw_eqs.  Definition T_INT : Z := 10.  Definition T_UINT : Z := 11.  Definition T_DBL : Z := 25.
Definition T_LONG : Z := 13.
Lemma gw_eq_T_LONG : @T_LONG = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.T_LONG) (@T_LONG)). Proof. unfold T_LONG, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.T_LONG; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_T_LONG : gw_eqs. Definition T_ULONG : Z := 14.

Definition FLAGMASK : Z := 75913.
Lemma gw_eq_FLAGMASK : @FLAGMASK = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FLAGMASK) (@FLAGMASK)). Proof. unfold FLAGMASK, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FLAGMASK; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FLAGMASK : gw_eqs.

Fixpoint digits_aux (fuel : nat) (base : Z) (dig : Z -> Z) (x : Z) (acc : list Z) : list Z :=
match fuel with
| O => acc
| S fuel' => if x =? 0 then acc else digits_aux fuel' base dig (x / base) (dig (x mod base) :: acc)
end.
Lemma gw_eq_digits_aux : @digits_aux = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.digits_aux) (@digits_aux)). Proof. unfold digits_aux, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.digits_aux; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_digits_aux : gw_eqs.

Definition dec_digits (x : Z) : list Z := digits_aux 20 10 (fun v => 48 + v) x [].
Lemma gw_eq_dec_digits : @dec_digits = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.dec_digits) (@dec_digits)). Proof. unfold dec_digits, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.dec_digits; rewrite ?gw_eq_digits_aux; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_dec_digits : gw_eqs.

Definition XDIGITS : list Z := [48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 65; 66; 67; 68; 69; 70].
Lemma gw_eq_XDIGITS : @XDIGITS = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.XDIGITS) (@XDIGITS)). Proof. unfold XDIGITS, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.XDIGITS; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_XDIGITS : gw_eqs.
Definition hex_digits (lower : Z) (x : Z) : list Z := digits_aux 16 16 (fun v => Z.lor (znth XDIGITS v) lower) x [].
Lemma gw_eq_hex_digits : @hex_digits = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.hex_digits) (@hex_digits)). Proof. unfold hex_digits, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.hex_digits; rewrite ?gw_eq_digits_aux, ?gw_eq_XDIGITS; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_hex_digits : gw_eqs.

Fixpoint lit_run (s : list Z) : list Z :=
match s with
| [] => []
| c :: s' => if (c =? 0) || (c =? 37) then [] else c :: lit_run s'
end.
Lemma gw_eq_lit_run : @lit_run = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.lit_run) (@lit_run)). Proof. unfold lit_run, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.lit_run; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_lit_run : gw_eqs.

Definition flag_bit (c : Z) : option Z :=
if (32 <=? c) && (c <? 64) && negb (Z.land FLAGMASK (Z.shiftl 1 (c - 32)) =? 0)
then Some (Z.shiftl 1 (c - 32)) else None.
Lemma gw_eq_flag_bit : @flag_bit = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.flag_bit) (@flag_bit)). Proof. unfold flag_bit, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.flag_bit; rewrite ?gw_eq_FLAGMASK; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_flag_bit : gw_eqs.
Fixpoint parse_flags (s : list Z) (fl : Z) {struct s} : Z * list Z :=
match s with
| [] => (fl, s)
| c :: s' => match flag_bit c with
| Some b => parse_flags s' (Z.lor fl b)
| None => (fl, s)
end
end.
Lemma gw_eq_parse_flags : @parse_flags = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.parse_flags) (@parse_flags)). Proof. unfold parse_flags, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.parse_flags; rewrite ?gw_eq_flag_bit; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_parse_flags : gw_eqs.

Fixpoint getint (s : list Z) (i : Z) {struct s} : option (Z * list Z) :=
match s with
| [] => Some (i, s)
| c :: s' => if is_digit c then
if (214748364 <? i) || (INT_MAX - 10 * i <? c - 48) then None
else getint s' (10 * i + (c - 48))
else Some (i, s)
end.
Lemma gw_eq_getint : @getint = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.getint) (@getint)). Proof. unfold getint, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.getint; rewrite ?gw_eq_is_digit; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_getint : gw_eqs.

Definition conv_type (t : Z) : option Z :=
if t =? 115 then Some T_PTR
else if (t =? 100) || (t =? 105) || (t =? 99) then Some T_INT
else if (t =? 117) || (t =? 120) || (t =? 88) then Some T_UINT
else if (t =? 101) || (t =? 102) || (t =? 103) || (t =? 69) || (t =? 70) || (t =? 71)
then Some T_DBL
else None.
Lemma gw_eq_conv_type : @conv_type = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_type) (@conv_type)). Proof. unfold conv_type, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_type; rewrite ?gw_eq_T_PTR; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_conv_type : gw_eqs.

Definition conv_type_l (t : Z) : option Z :=
if (t =? 100) || (t =? 105) then Some T_LONG else if t =? 117 then Some T_ULONG else None.
Lemma gw_eq_conv_type_l : @conv_type_l = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_type_l) (@conv_type_l)). Proof. unfold conv_type_l, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_type_l; rewrite ?gw_eq_T_LONG; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_conv_type_l : gw_eqs.

Definition tyspec (s : list Z) : option (Z * Z * list Z) :=
match s with
| [] => None
| t :: s4 => if t =? 108 then match s4 with
| [] => None
| t2 :: s5 => let? ty := conv_type_l t2 in Some (ty, t2, s5)
end
else let? ty := conv_type t in Some (ty, t, s4)
end.
Lemma gw_eq_tyspec : @tyspec = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.tyspec) (@tyspec)). Proof. unfold tyspec, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.tyspec; rewrite ?gw_eq_conv_type, ?gw_eq_conv_type_l; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_tyspec : gw_eqs.

Notation dir := G.T_printf.dir.
Notation mkDir := G.T_printf.mkDir.
Notation d_fl := G.T_printf.d_fl.
Notation d_w := G.T_printf.d_w.
Notation d_p := G.T_printf.d_p.
Notation d_xp := G.T_printf.d_xp.
Notation d_t := G.T_printf.d_t.
Notation d_ty := G.T_printf.d_ty.

Definition d_ps (d : dir) : Z := if (d_ty d =? T_LONG) || (d_ty d =? T_ULONG) then 1 else 0.
Lemma gw_eq_d_ps : @d_ps = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.d_ps) (@d_ps)). Proof. unfold d_ps, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.d_ps; rewrite ?gw_eq_T_LONG; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_d_ps : gw_eqs.

Definition dir_ty_ok (d : dir) : Prop :=
(conv_type (d_t d) = Some (d_ty d) /\ d_ps d = 0) \/ (conv_type_l (d_t d) = Some (d_ty d) /\ d_ps d = 1).
Lemma gw_eq_dir_ty_ok : @dir_ty_ok = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.dir_ty_ok) (@dir_ty_ok)). Proof. unfold dir_ty_ok, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.dir_ty_ok; rewrite ?gw_eq_conv_type, ?gw_eq_conv_type_l, ?gw_eq_d_ps; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_dir_ty_ok : gw_eqs.

Definition parse_dir (s : list Z) : option (dir * list Z) :=
let positional := match s with
| c1 :: c2 :: _ => is_digit c1 && (c2 =? 36)
| [c1] => is_digit c1
| [] => false
end in
if positional then None else
let '(fl, s1) := parse_flags s 0 in
match s1 with
| [] => None
| c1 :: _ =>
if c1 =? 42 then None else
let? (w, s2) := getint s1 0 in
match s2 with
| [] => None
| c2 :: s2' =>
let pxs : option (Z * bool * list Z) :=
if c2 =? 46 then
match s2' with
| [] => None
| c3 :: _ => if c3 =? 42 then None
else let? (p, s3) := getint s2' 0 in Some (p, true, s3)
end
else Some (-1, false, s2) in
match pxs with
| None => None
| Some (p, xp, s3) =>
match s3 with
| [] => None
| _ :: _ => let? tys := tyspec s3 in let '(ty, t, s4) := tys in Some (mkDir fl w p xp t ty, s4)
end
end
end
end.
Lemma gw_eq_parse_dir : @parse_dir = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.parse_dir) (@parse_dir)). Proof. unfold parse_dir, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.parse_dir; rewrite ?gw_eq_is_digit, ?gw_eq_parse_flags, ?gw_eq_getint, ?gw_eq_tyspec; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_parse_dir : gw_eqs.

Section PrintfModel.
Context {St : Type}.
Variable OUT : list Z -> M St unit.
Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

Definition mpad (c w l fl : Z) : M St unit :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l) then mret tt
else if 256 <=? w - l then munr
else OUT (zrepeat c (w - l)).
Lemma gw_eq_mpad : @mpad = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.mpad) (@mpad)). Proof. unfold mpad, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.mpad; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_mpad : gw_eqs.

Definition conv_tail (cnt fl w p : Z) (prefix body : list Z) : M St Z :=
let pl := zlength prefix in
let n := zlength body in
let p := Z.max p n in
if INT_MAX - pl <? p then munr else
let w := Z.max w (pl + p) in
if INT_MAX - cnt <? w then munr else
mpad 32 w (pl + p) fl ;;;
OUT prefix ;;;
mpad 48 w (pl + p) (Z.lxor fl ZERO_PAD) ;;;
mpad 48 p n 0 ;;;
OUT body ;;;
mpad 32 w (pl + p) (Z.lxor fl LEFT_ADJ) ;;;
mret (cnt + w).
Lemma gw_eq_conv_tail : @conv_tail = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_tail) (@conv_tail)). Proof. unfold conv_tail, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_tail; rewrite ?gw_eq_mpad; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_conv_tail : gw_eqs.

Definition conv_int (cnt fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) : M St Z :=
if xp && (p <? 0) then munr else
let fl := if xp then Z.land fl (Z.lnot ZERO_PAD) else fl in
if (argi =? 0) && (p =? 0) then conv_tail cnt fl w p prefix []
else conv_tail cnt fl w (Z.max p (zlength body + (if argi =? 0 then 1 else 0))) prefix body.
Lemma gw_eq_conv_int : @conv_int = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_int) (@conv_int)). Proof. unfold conv_int, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_int; rewrite ?gw_eq_conv_tail; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_conv_int : gw_eqs.

Definition conv (cnt : Z) (d : dir) (a : parg) : M St Z :=
let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
let w := d_w d in let p := d_p d in let xp := d_xp d in let t := d_t d in
match a with
| PA_s s =>
if negb (d_ty d =? T_PTR) then munr else

if (p <? 0) && (INT_MAX <=? zlength s) then munr else
let n := if p <? 0 then zlength s else Z.min (zlength s) p in
conv_tail cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
| PA_i i =>
if negb (d_ty d =? T_INT) then munr else
if t =? 99 then
conv_tail cnt (Z.land fl (Z.lnot ZERO_PAD)) w 1 [] [i mod 256]
else
let argi := i mod 2^64 in

let '(argi, prefix) :=
if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
else (argi, []) in
conv_int cnt fl w p xp argi prefix (dec_digits argi)
| PA_li i =>
if negb (d_ty d =? T_LONG) then munr else
let argi := i mod 2^64 in
let '(argi, prefix) :=
if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
else (argi, []) in
conv_int cnt fl w p xp argi prefix (dec_digits argi)
| PA_lu u =>
if negb (d_ty d =? T_ULONG) || negb (t =? 117) then munr else
conv_int cnt fl w p xp u [] (dec_digits u)
| PA_u u =>
if negb (d_ty d =? T_UINT) then munr else
if t =? 117 then conv_int cnt fl w p xp u [] (dec_digits u)
else

let prefix := if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0)
then (if t =? 120 then [48; 120] else [48; 88]) else [] in
conv_int cnt fl w p xp u prefix (hex_digits (Z.land t 32) u)
| PA_g dd =>
if negb (d_ty d =? T_DBL) then munr else
if xp && (p <? 0) then munr else
if (1 <? w) || (2^20 <=? p) then munr else
r <- OUTFP (f128_of_d dd) w p fl t ;;
if (r <? 0) || (INT_MAX - cnt <? r) then munr else mret (cnt + r)
end.
Lemma gw_eq_conv : @conv = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv) (@conv)). Proof. unfold conv, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv; rewrite ?gw_eq_T_PTR, ?gw_eq_T_LONG, ?gw_eq_dec_digits, ?gw_eq_hex_digits, ?gw_eq_conv_tail, ?gw_eq_conv_int; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_conv : gw_eqs.

Fixpoint printf_loop (fuel : nat) (s : list Z) (args : list parg) (cnt : Z) {struct fuel} : M St Z :=
match fuel with
| O => munr
| S fuel' =>
match s with
| [] => munr
| c :: _ =>
if c =? 0 then mret cnt else
let lit := lit_run s in
let l := zlength lit in
let s1 := skipn (Datatypes.length lit) s in
match s1 with
| [] => munr
| c1 :: s2 =>
if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end
then munr
else if 0 <? l then
(if INT_MAX - cnt <? l then munr
else OUT lit ;;; printf_loop fuel' s1 args (cnt + l))
else
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
OUT [] ;;;
cnt' <- conv cnt d a ;;
printf_loop fuel' s3 args' cnt'
| _, _ => munr
end
end
end
end.
Lemma gw_eq_printf_loop : @printf_loop = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_loop) (@printf_loop)). Proof. unfold printf_loop, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_loop; rewrite ?gw_eq_lit_run, ?gw_eq_parse_dir, ?gw_eq_conv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_printf_loop : gw_eqs.

Definition printf_model (fmt : list Z) (args : list parg) : M St Z :=
printf_loop (Datatypes.length fmt) fmt args 0.
Lemma gw_eq_printf_model : @printf_model = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_model) (@printf_model)). Proof. unfold printf_model, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_model; rewrite ?gw_eq_printf_loop; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_printf_model : gw_eqs.
End PrintfModel.
Lemma gw_eq_mpad__2 : @mpad = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.mpad) (@mpad)). Proof. unfold mpad, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.mpad; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_mpad__2 : gw_eqs.
Lemma gw_eq_conv_tail__2 : @conv_tail = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_tail) (@conv_tail)). Proof. unfold conv_tail, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_tail; rewrite ?gw_eq_mpad__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_conv_tail__2 : gw_eqs.
Lemma gw_eq_conv_int__2 : @conv_int = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_int) (@conv_int)). Proof. unfold conv_int, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_int; rewrite ?gw_eq_conv_tail__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_conv_int__2 : gw_eqs.
Lemma gw_eq_conv__2 : @conv = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv) (@conv)). Proof. unfold conv, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv; rewrite ?gw_eq_T_PTR, ?gw_eq_T_LONG, ?gw_eq_dec_digits, ?gw_eq_hex_digits, ?gw_eq_conv_tail__2, ?gw_eq_conv_int__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_conv__2 : gw_eqs.
Lemma gw_eq_printf_loop__2 : @printf_loop = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_loop) (@printf_loop)). Proof. unfold printf_loop, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_loop; rewrite ?gw_eq_lit_run, ?gw_eq_parse_dir, ?gw_eq_conv__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_printf_loop__2 : gw_eqs.
Lemma gw_eq_printf_model__2 : @printf_model = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_model) (@printf_model)). Proof. unfold printf_model, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_model; rewrite ?gw_eq_printf_loop__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_printf_model__2 : gw_eqs.

Arguments mpad {St} OUT _ _ _ _.
Arguments conv_tail {St} OUT _ _ _ _ _ _.
Arguments conv_int {St} OUT _ _ _ _ _ _ _ _.
Arguments conv {St} OUT OUTFP _ _ _.
Arguments printf_loop {St} OUT OUTFP _ _ _ _.
Arguments printf_model {St} OUT OUTFP _ _.

Fixpoint fp_calls (fuel : nat) (s : list Z) (args : list parg) {struct fuel} : list (Z * Z * Z * Z * Z) :=
match fuel with
| O => []
| S fuel' =>
match s with
| [] => []
| c :: _ =>
if c =? 0 then [] else
let lit := lit_run s in
let s1 := skipn (Datatypes.length lit) s in
if 0 <? zlength lit then fp_calls fuel' s1 args
else match s1 with
| _ :: s2 =>
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
match a with
| PA_g dd =>
let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
(f128_of_d dd, d_w d, d_p d, fl, d_t d) :: fp_calls fuel' s3 args'
| _ => fp_calls fuel' s3 args'
end
| _, _ => []
end
| _ => []
end
end
end.
Lemma gw_eq_fp_calls : @fp_calls = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.fp_calls) (@fp_calls)). Proof. unfold fp_calls, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.fp_calls; rewrite ?gw_eq_lit_run, ?gw_eq_parse_dir; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fp_calls : gw_eqs.

Definition pass1_ok (fmt : list Z) : bool :=
let lit := lit_run fmt in
(zlength lit <=? INT_MAX) &&
match skipn (Datatypes.length lit) fmt with
| [] => false
| c1 :: s2 =>
if c1 =? 0 then true
else match s2 with
| [] => false
| c2 :: _ => negb (c2 =? 37) && match parse_dir s2 with Some _ => true | None => false end
end
end.
Lemma gw_eq_pass1_ok : @pass1_ok = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pass1_ok) (@pass1_ok)). Proof. unfold pass1_ok, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pass1_ok; rewrite ?gw_eq_lit_run, ?gw_eq_parse_dir; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_pass1_ok : gw_eqs.

Definition pad_pieces (c w l fl : Z) : option (list (list Z)) :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l) then Some []
else if 256 <=? w - l then None
else Some [zrepeat c (w - l)].
Lemma gw_eq_pad_pieces : @pad_pieces = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pad_pieces) (@pad_pieces)). Proof. unfold pad_pieces, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pad_pieces; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_pad_pieces : gw_eqs.

Definition tail_pieces (cnt fl w p : Z) (prefix body : list Z) : option (list (list Z) * Z) :=
let pl := zlength prefix in
let n := zlength body in
let p := Z.max p n in
if INT_MAX - pl <? p then None else
let w := Z.max w (pl + p) in
if INT_MAX - cnt <? w then None else
let? p1 := pad_pieces 32 w (pl + p) fl in
let? p2 := pad_pieces 48 w (pl + p) (Z.lxor fl ZERO_PAD) in
let? p3 := pad_pieces 48 p n 0 in
let? p4 := pad_pieces 32 w (pl + p) (Z.lxor fl LEFT_ADJ) in
Some (p1 ++ [prefix] ++ p2 ++ p3 ++ [body] ++ p4, cnt + w).
Lemma gw_eq_tail_pieces : @tail_pieces = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.tail_pieces) (@tail_pieces)). Proof. unfold tail_pieces, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.tail_pieces; rewrite ?gw_eq_pad_pieces; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_tail_pieces : gw_eqs.

Definition int_pieces (cnt fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) : option (list (list Z) * Z) :=
if xp && (p <? 0) then None else
let fl := if xp then Z.land fl (Z.lnot ZERO_PAD) else fl in
if (argi =? 0) && (p =? 0) then tail_pieces cnt fl w p prefix []
else tail_pieces cnt fl w (Z.max p (zlength body + (if argi =? 0 then 1 else 0))) prefix body.
Lemma gw_eq_int_pieces : @int_pieces = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.int_pieces) (@int_pieces)). Proof. unfold int_pieces, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.int_pieces; rewrite ?gw_eq_tail_pieces; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_int_pieces : gw_eqs.

Definition conv_pieces (cnt : Z) (d : dir) (a : parg) : option (list (list Z) * Z) :=
let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
let w := d_w d in let p := d_p d in let xp := d_xp d in let t := d_t d in
match a with
| PA_s s =>
if negb (d_ty d =? T_PTR) then None else
if (p <? 0) && (INT_MAX <=? zlength s) then None else
let n := if p <? 0 then zlength s else Z.min (zlength s) p in
tail_pieces cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
| PA_i i =>
if negb (d_ty d =? T_INT) then None else
if t =? 99 then tail_pieces cnt (Z.land fl (Z.lnot ZERO_PAD)) w 1 [] [i mod 256] else
let argi := i mod 2^64 in
let '(argi, prefix) :=
if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
else (argi, []) in
int_pieces cnt fl w p xp argi prefix (dec_digits argi)
| PA_li i =>
if negb (d_ty d =? T_LONG) then None else
let argi := i mod 2^64 in
let '(argi, prefix) :=
if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
else (argi, []) in
int_pieces cnt fl w p xp argi prefix (dec_digits argi)
| PA_lu u =>
if negb (d_ty d =? T_ULONG) || negb (t =? 117) then None else
int_pieces cnt fl w p xp u [] (dec_digits u)
| PA_u u =>
if negb (d_ty d =? T_UINT) then None else
if t =? 117 then int_pieces cnt fl w p xp u [] (dec_digits u)
else
let prefix := if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0)
then (if t =? 120 then [48; 120] else [48; 88]) else [] in
int_pieces cnt fl w p xp u prefix (hex_digits (Z.land t 32) u)
| PA_g _ => None
end.
Lemma gw_eq_conv_pieces : @conv_pieces = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_pieces) (@conv_pieces)). Proof. unfold conv_pieces, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_pieces; rewrite ?gw_eq_T_PTR, ?gw_eq_T_LONG, ?gw_eq_dec_digits, ?gw_eq_hex_digits, ?gw_eq_tail_pieces, ?gw_eq_int_pieces; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_conv_pieces : gw_eqs.

Fixpoint printf_pieces_loop (fuel : nat) (s : list Z) (args : list parg) (cnt : Z) {struct fuel}
: option (list (list Z) * Z) :=
match fuel with
| O => None
| S fuel' =>
match s with
| [] => None
| c :: _ =>
if c =? 0 then Some ([], cnt) else
let lit := lit_run s in
let l := zlength lit in
let s1 := skipn (Datatypes.length lit) s in
match s1 with
| [] => None
| c1 :: s2 =>
if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
else if 0 <? l then
(if INT_MAX - cnt <? l then None
else let? (ps, r) := printf_pieces_loop fuel' s1 args (cnt + l) in Some (lit :: ps, r))
else
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
let? (ps1, cnt') := conv_pieces cnt d a in
let? (ps, r) := printf_pieces_loop fuel' s3 args' cnt' in
Some ([] :: ps1 ++ ps, r)
| _, _ => None
end
end
end
end.
Lemma gw_eq_printf_pieces_loop : @printf_pieces_loop = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_pieces_loop) (@printf_pieces_loop)). Proof. unfold printf_pieces_loop, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_pieces_loop; rewrite ?gw_eq_lit_run, ?gw_eq_parse_dir, ?gw_eq_conv_pieces; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_printf_pieces_loop : gw_eqs.

Definition printf_pieces (fmt : list Z) (args : list parg) : option (list (list Z) * Z) :=
printf_pieces_loop (Datatypes.length fmt) fmt args 0.
Lemma gw_eq_printf_pieces : @printf_pieces = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_pieces) (@printf_pieces)). Proof. unfold printf_pieces, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_pieces; rewrite ?gw_eq_printf_pieces_loop; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_printf_pieces : gw_eqs.

Definition FMT_emit : list Z := [37; 115; 10; 0].
Lemma gw_eq_FMT_emit : @FMT_emit = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_emit) (@FMT_emit)). Proof. unfold FMT_emit, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_emit; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FMT_emit : gw_eqs.
Definition FMT_u04x : list Z := [117; 37; 48; 52; 120; 0].
Lemma gw_eq_FMT_u04x : @FMT_u04x = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_u04x) (@FMT_u04x)). Proof. unfold FMT_u04x, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_u04x; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FMT_u04x : gw_eqs.
Definition FMT_usage : list Z := str "usage: %s INPUT" ++ [10; 0].
Lemma gw_eq_FMT_usage : @FMT_usage = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_usage) (@FMT_usage)). Proof. unfold FMT_usage, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_usage; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FMT_usage : gw_eqs.
Definition FMT_g15 : list Z := [37; 49; 46; 49; 53; 103; 0].
Lemma gw_eq_FMT_g15 : @FMT_g15 = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_g15) (@FMT_g15)). Proof. unfold FMT_g15, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_g15; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FMT_g15 : gw_eqs.
Definition FMT_too_big : list Z := str "cli: input >= %u bytes, refused" ++ [10; 0].
Lemma gw_eq_FMT_too_big : @FMT_too_big = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_too_big) (@FMT_too_big)). Proof. unfold FMT_too_big, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_too_big; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FMT_too_big : gw_eqs.
Definition FMT_g17 : list Z := [37; 49; 46; 49; 55; 103; 0].
Lemma gw_eq_FMT_g17 : @FMT_g17 = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_g17) (@FMT_g17)). Proof. unfold FMT_g17, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_g17; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FMT_g17 : gw_eqs.
Definition FMT_d : list Z := [37; 100; 0].
Lemma gw_eq_FMT_d : @FMT_d = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_d) (@FMT_d)). Proof. unfold FMT_d, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_d; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FMT_d : gw_eqs.
Definition FMT_cannot_open : list Z := str "cli: cannot open %s" ++ [10; 0].
Lemma gw_eq_FMT_cannot_open : @FMT_cannot_open = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_cannot_open) (@FMT_cannot_open)). Proof. unfold FMT_cannot_open, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_cannot_open; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FMT_cannot_open : gw_eqs.
Definition FMT_read_error : list Z := str "cli: read error on %s" ++ [10; 0].
Lemma gw_eq_FMT_read_error : @FMT_read_error = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_read_error) (@FMT_read_error)). Proof. unfold FMT_read_error, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_read_error; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FMT_read_error : gw_eqs.
Definition A_FMT_emit : Z := 0x102a8.
Lemma gw_eq_A_FMT_emit : @A_FMT_emit = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.A_FMT_emit) (@A_FMT_emit)). Proof. unfold A_FMT_emit, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.A_FMT_emit; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_A_FMT_emit : gw_eqs.       Definition A_FMT_u04x : Z := 0x102c3.
Definition A_FMT_usage : Z := 0x102e5.
Lemma gw_eq_A_FMT_usage : @A_FMT_usage = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.A_FMT_usage) (@A_FMT_usage)). Proof. unfold A_FMT_usage, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.A_FMT_usage; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_A_FMT_usage : gw_eqs.      Definition A_FMT_g15 : Z := 0x10316.
Definition A_FMT_too_big : Z := 0x1032a.
Lemma gw_eq_A_FMT_too_big : @A_FMT_too_big = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.A_FMT_too_big) (@A_FMT_too_big)). Proof. unfold A_FMT_too_big, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.A_FMT_too_big; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_A_FMT_too_big : gw_eqs.    Definition A_FMT_g17 : Z := 0x1034b.
Definition A_FMT_d : Z := 0x10352.
Lemma gw_eq_A_FMT_d : @A_FMT_d = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.A_FMT_d) (@A_FMT_d)). Proof. unfold A_FMT_d, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.A_FMT_d; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_A_FMT_d : gw_eqs.          Definition A_FMT_cannot_open : Z := 0x10355.
Definition A_FMT_read_error : Z := 0x1036a.
Lemma gw_eq_A_FMT_read_error : @A_FMT_read_error = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.A_FMT_read_error) (@A_FMT_read_error)). Proof. unfold A_FMT_read_error, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.A_FMT_read_error; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_A_FMT_read_error : gw_eqs.

Example pieces_emit_ex : printf_pieces FMT_emit [PA_s (str "hi")] = Some (pieces_emit (str "hi"), 3).
Proof. rewrite ?gw_eq_printf_pieces, ?gw_eq_FMT_emit; first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_emit_ex) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_emit_ex)]. Qed.
Example pieces_usage_ex : printf_pieces FMT_usage [PA_s (str "prog")] = Some (pieces_usage (str "prog"), 18).
Proof. rewrite ?gw_eq_printf_pieces, ?gw_eq_FMT_usage; first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_usage_ex) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_usage_ex)]. Qed.
Example pieces_cannot_open_ex : printf_pieces FMT_cannot_open [PA_s (str "f")] = Some (pieces_cannot_open (str "f"), 19).
Proof. rewrite ?gw_eq_printf_pieces, ?gw_eq_FMT_cannot_open; first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_cannot_open_ex) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_cannot_open_ex)]. Qed.
Example pieces_read_error_ex : printf_pieces FMT_read_error [PA_s (str "f")] = Some (pieces_read_error (str "f"), 21).
Proof. rewrite ?gw_eq_printf_pieces, ?gw_eq_FMT_read_error; first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_read_error_ex) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_read_error_ex)]. Qed.
Example pieces_too_big_ex : printf_pieces FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof. rewrite ?gw_eq_printf_pieces, ?gw_eq_FMT_too_big; first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_too_big_ex) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_too_big_ex)]. Qed.
Example pieces_d_ex1 : printf_pieces FMT_d [PA_i (-2147483648)] = Some ([[]; [45]; str "2147483648"], 11).
Proof. rewrite ?gw_eq_printf_pieces, ?gw_eq_FMT_d; first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_d_ex1) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_d_ex1)]. Qed.
Example pieces_d_ex2 : printf_pieces FMT_d [PA_i 0] = Some ([[]; []; [48]; []], 1).
Proof. rewrite ?gw_eq_printf_pieces, ?gw_eq_FMT_d; first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_d_ex2) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_d_ex2)]. Qed.
Example pieces_u04x_ex1 : printf_pieces FMT_u04x [PA_u 31] = Some ([[117]; []; []; [48; 48]; [49; 102]], 5).
Proof. rewrite ?gw_eq_printf_pieces, ?gw_eq_FMT_u04x; first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_u04x_ex1) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_u04x_ex1)]. Qed.
Example pieces_u04x_ex2 : printf_pieces FMT_u04x [PA_u 1] = Some ([[117]; []; []; [48; 48; 48]; [49]], 5).
Proof. rewrite ?gw_eq_printf_pieces, ?gw_eq_FMT_u04x; first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_u04x_ex2) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pieces_u04x_ex2)]. Qed.
Example fp_calls_g17_ex : fp_calls 7 FMT_g17 [PA_g 5] = [(f128_of_d 5, 1, 17, 0, 103)].
Proof. rewrite ?gw_eq_fp_calls, ?gw_eq_FMT_g17; first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.fp_calls_g17_ex) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.fp_calls_g17_ex)]. Qed.
Example pass1_ok_ex : map pass1_ok [FMT_emit; FMT_u04x; FMT_usage; FMT_g15; FMT_too_big; FMT_g17; FMT_d; FMT_cannot_open; FMT_read_error]
= repeat true 9.
Proof. rewrite ?gw_eq_pass1_ok, ?gw_eq_FMT_emit, ?gw_eq_FMT_u04x, ?gw_eq_FMT_usage, ?gw_eq_FMT_g15, ?gw_eq_FMT_too_big, ?gw_eq_FMT_g17, ?gw_eq_FMT_d, ?gw_eq_FMT_cannot_open, ?gw_eq_FMT_read_error; first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pass1_ok_ex) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pass1_ok_ex)]. Qed.
