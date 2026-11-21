(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma land_m8_64 : forall b, 0 <= b < 18446744073709551616 -> Z.land b 18446744073709551608 = b - b mod 8.
Proof.
  intros b Hb. change 18446744073709551608 with (Z.land (Z.ones 64) (-8)).
  rewrite Z.land_assoc, Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616. rewrite Z.mod_small by lia.
  change (-8) with (Z.lnot 7). rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.
Lemma land7 : forall b, 0 <= b -> Z.land b 7 = b mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma srl_land7 : forall h b, 0 <= h < 18446744073709551616 -> 0 <= b ->
  Z.shiftr (h mod 18446744073709551616) (Z.land b 7 mod 64) = Z.shiftr h (b mod 8).
Proof.
  intros h b Hh Hb. rewrite land7 by lia. rewrite (Z.mod_small h) by lia.
  f_equal. Z.div_mod_to_equations. lia.
Qed.
Lemma srl_land7' : forall h b, 0 <= b -> Z.shiftr h (Z.land b 7 mod 64) = Z.shiftr h (b mod 8).
Proof. intros h b Hb. rewrite land7 by lia. f_equal. Z.div_mod_to_equations. lia. Qed.
Lemma pull_hold : forall h c b, 0 <= b < 64 -> Z.shiftl c (b mod 64) + h = h + c * 2 ^ b.
Proof. intros h c b Hb. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma pow2_le_40 : forall b, 0 <= b <= 40 -> 2 ^ b <= 1099511627776.
Proof. intros. change 1099511627776 with (2 ^ 40). apply Z.pow_le_mono_r; lia. Qed.
