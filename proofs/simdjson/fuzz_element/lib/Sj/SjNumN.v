(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma small_mul_top_nz : forall a y c, 0 < a < 18446744073709551616 -> 0 < y < 18446744073709551616 -> 0 <= c < 18446744073709551616 ->
  (Z.shiftr (a * y) 64 + Z.b2z ((a * y + c) mod 18446744073709551616 <? (a * y) mod 18446744073709551616)) mod 18446744073709551616 = 0 ->
  (a * y + c) mod 18446744073709551616 <> 0.
Proof.
  intros a y c Ha Hy Hc H.
  assert (M1 : 1 <= a * y) by nia.
  assert (M2 : a * y <= 18446744073709551615 * 18446744073709551615) by nia.
  set (M := a * y) in *. clearbody M.
  rewrite Z.shiftr_div_pow2 in H by lia. change (2 ^ 64) with 18446744073709551616 in H.
  destruct (Z.ltb_spec ((M + c) mod 18446744073709551616) (M mod 18446744073709551616)) as [L|L]; cbn [Z.b2z] in H;
    Z.div_mod_to_equations; lia.
Qed.

Lemma shl_top_nz : forall a p sh, 0 < a < 18446744073709551616 -> 1 <= sh <= 63 -> Z.shiftr a ((64 - sh) mod 64) = 0 ->
  (Z.lor (Z.shiftl a (sh mod 64) mod 18446744073709551616) p) mod 18446744073709551616 <> 0.
Proof.
  intros a p sh Ha Hs H.
  rewrite (Z.mod_small sh 64) by lia. rewrite (Z.mod_small (64 - sh) 64) in H by lia.
  rewrite Z.shiftr_div_pow2 in H by lia. rewrite Z.shiftl_mul_pow2 by lia.
  assert (P1 : 0 < 2 ^ (64 - sh)) by (apply Z.pow_pos_nonneg; lia).
  assert (A1 : a < 2 ^ (64 - sh)) by (apply Z.div_small_iff in H; lia).
  assert (P2 : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
  assert (E : 2 ^ (64 - sh) * 2 ^ sh = 18446744073709551616) by (rewrite <- Z.pow_add_r by lia; replace (64 - sh + sh) with 64 by lia; reflexivity).
  assert (X1 : 1 <= a * 2 ^ sh < 18446744073709551616) by nia.
  rewrite (Z.mod_small (a * 2 ^ sh)) by lia.
  change 18446744073709551616 with (2 ^ 64). rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
  intros L. apply Z.lor_eq_0_iff in L. destruct L as [L _]. rewrite Z.land_ones in L by lia. rewrite Z.mod_small in L; change (2 ^ 64) with 18446744073709551616; lia.
Qed.
