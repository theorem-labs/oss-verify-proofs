(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma lxor_ones64 : forall x, 0 <= x < 18446744073709551616 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx.
  assert (L : Z.land x (Z.lxor x 18446744073709551615) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z.testbit x n) eqn:T; [|reflexivity].
    destruct (Z_lt_le_dec n 64) as [Lt|Ge].
    - change 18446744073709551615 with (Z.ones 64). rewrite Z.ones_spec_low by lia. reflexivity.
    - exfalso. assert (B : Z.testbit x n = false); [|congruence].
      destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). lia. }
  pose proof (Z.add_nocarry_lxor _ _ L) as A.
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in A. lia.
Qed.

Lemma land_7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_ones64_l : forall t, 0 <= t < 18446744073709551616 -> Z.land 18446744073709551615 t = t.
Proof. intros t Ht. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma shr60_small : forall x, 0 <= x < 1152921504606846976 -> Z.shiftr x 60 = 0.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 60) with 1152921504606846976. apply Z.div_small. exact Hx. Qed.
