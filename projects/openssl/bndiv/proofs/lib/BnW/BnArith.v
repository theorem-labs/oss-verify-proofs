(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation M64 := 18446744073709551616 (only parsing).

Lemma BW_lit : BW = 18446744073709551616. Proof. reflexivity. Qed.

Ltac case_ltb :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | H : context [Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec a b)
  end; cbn [Z.b2z] in *.

(* [comment removed for export] *)
Lemma adc_carry : forall x y c, 0 <= x < M64 -> 0 <= y < M64 -> 0 <= c <= 1 ->
  Z.b2z ((x + c) mod M64 <? x) + Z.b2z ((x + c + y) mod M64 <? (x + c) mod M64) = (x + y + c) / M64.
Proof. intros x y c Hx Hy Hc. case_ltb; Z.div_mod_to_equations; lia. Qed.

Lemma adc_carry_01 : forall x y c, 0 <= x < M64 -> 0 <= y < M64 -> 0 <= c <= 1 -> 0 <= (x + y + c) / M64 <= 1.
Proof. intros x y c Hx Hy Hc. Z.div_mod_to_equations; lia. Qed.

Lemma adc_limb : forall x y c, (x + c + y) mod M64 = (x + y + c) mod M64.
Proof. intros. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma sbb_borrow : forall x y c, 0 <= x < M64 -> 0 <= y < M64 -> 0 <= c <= 1 ->
  Z.b2z (x <? (x - c) mod M64) + Z.b2z ((x - c) mod M64 <? (x - c - y) mod M64) = (if x - y - c <? 0 then 1 else 0).
Proof. intros x y c Hx Hy Hc. case_ltb; Z.div_mod_to_equations; lia. Qed.

Lemma sbb_limb : forall x y c, (x - c - y) mod M64 = (x - y - c) mod M64.
Proof. intros. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma shl32_shr29 : forall k, 0 <= k < 4294967296 ->
  Z.shiftr ((Z.shiftl k 32) mod M64) 29 = 8 * k.
Proof.
  intros k Hk. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 32) with 4294967296. change (2 ^ 29) with 536870912.
  rewrite Z.mod_small by lia. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma adc_carry' : forall x y c, 0 <= x < M64 -> 0 <= y < M64 -> 0 <= c <= 1 ->
  Z.b2z ((c + x) mod M64 <? c) + Z.b2z ((c + x + y) mod M64 <? (c + x) mod M64) = (x + y + c) / M64.
Proof. intros x y c Hx Hy Hc. case_ltb; Z.div_mod_to_equations; lia. Qed.

(* [comment removed for export] *)
Notation H32 := 4294967296 (only parsing).

Lemma half_split : forall x, 0 <= x < M64 -> exists xl xh, x = xh * H32 + xl /\ 0 <= xl < H32 /\ 0 <= xh < H32 /\
  Z.land x 4294967295 = xl /\ Z.shiftr x 32 = xh /\ x mod H32 = xl /\ x / H32 = xh.
Proof.
  intros x Hx. exists (x mod H32), (x / H32).
  change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 32) with H32.
  repeat split; try reflexivity; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Ltac mul64_solve x w Hx Hw :=
  let xl := fresh "xl" in let xh := fresh "xh" in let wl := fresh "wl" in let wh := fresh "wh" in
  let Ex := fresh "Ex" in let Ew := fresh "Ew" in let Rxl := fresh "Rxl" in let Rxh := fresh "Rxh" in
  let Rwl := fresh "Rwl" in let Rwh := fresh "Rwh" in
  let E1 := fresh "E1" in let E2 := fresh "E2" in let E3 := fresh "E3" in let E4 := fresh "E4" in
  let E5 := fresh "E5" in let E6 := fresh "E6" in let E7 := fresh "E7" in let E8 := fresh "E8" in
  destruct (half_split x Hx) as (xl & xh & Ex & Rxl & Rxh & E1 & E2 & E5 & E6);
  destruct (half_split w Hw) as (wl & wh & Ew & Rwl & Rwh & E7 & E8 & E3 & E4);
  rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8; clear E1 E2 E3 E4 E5 E6 E7 E8;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; change (2 ^ 32) with H32;
  let EP := fresh "EP" in
  assert (EP : x * w = (xh * wh) * (H32 * H32) + (xl * wh + xh * wl) * H32 + xl * wl) by (rewrite Ex, Ew; ring);
  rewrite ?EP; clear EP Ex Ew;
  let B1 := fresh "B" in let B2 := fresh "B" in let B3 := fresh "B" in let B4 := fresh "B" in
  assert (B1 : 0 <= xl * wl <= 4294967295 * 4294967295) by nia;
  assert (B2 : 0 <= xl * wh <= 4294967295 * 4294967295) by nia;
  assert (B3 : 0 <= xh * wl <= 4294967295 * 4294967295) by nia;
  assert (B4 : 0 <= xh * wh <= 4294967295 * 4294967295) by nia;
  let p1 := fresh "p" in let p2 := fresh "p" in let p3 := fresh "p" in let p4 := fresh "p" in
  set (p1 := xl * wl) in *; set (p2 := xl * wh) in *; set (p3 := xh * wl) in *; set (p4 := xh * wh) in *;
  clearbody p1 p2 p3 p4; clear Rxl Rxh Rwl Rwh;
  rewrite ?(Z.mod_small p2), ?(Z.mod_small p3) by lia;
  case_ltb; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Lemma mul64_hi : forall x w c, 0 <= x < M64 -> 0 <= w < M64 -> 0 <= c < M64 ->
  Z.shiftr ((Z.land x 4294967295 * (w / H32) + Z.shiftr x 32 * (w mod H32)) mod M64) 32 +
  (Z.shiftr x 32 * (w / H32) + Z.b2z ((x * w + c) mod M64 <? (x * w) mod M64)) +
  Z.shiftl (Z.b2z ((Z.land x 4294967295 * (w / H32) + Z.shiftr x 32 * (w mod H32)) mod M64 <? (Z.land x 4294967295 * (w / H32)) mod M64)) 32 +
  Z.b2z ((x * w) mod M64 <? (Z.shiftl ((Z.land x 4294967295 * (w / H32) + Z.shiftr x 32 * (w mod H32)) mod M64) 32) mod M64)
  = (x * w + c) / M64.
Proof. intros x w c Hx Hw Hc. mul64_solve x w Hx Hw. Qed.

Lemma mul_hi_range : forall x w c, 0 <= x < M64 -> 0 <= w < M64 -> 0 <= c <= 18446744073709551615 ->
  0 <= (x * w + c) / M64 <= 18446744073709551615.
Proof.
  intros x w c Hx Hw Hc.
  assert (0 <= x * w <= 18446744073709551615 * 18446744073709551615) by nia.
  Z.div_mod_to_equations; lia.
Qed.
