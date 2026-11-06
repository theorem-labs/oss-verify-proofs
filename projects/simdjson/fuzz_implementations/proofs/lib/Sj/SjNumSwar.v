(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma testbit7_low : forall c k, 0 <= c < 256 -> Z.testbit (c + 256 * k) 7 = (128 <=? c).
Proof.
  intros c k Hc. rewrite Z.testbit_odd, Z.shiftr_div_pow2 by lia. change (2 ^ 7) with 128.
  replace ((c + 256 * k) / 128) with (c / 128 + 2 * k) by (Z.div_mod_to_equations; lia).
  rewrite Z.odd_add_mul_2.
  destruct (Z.leb_spec 128 c).
  - replace (c / 128) with 1 by (Z.div_mod_to_equations; lia). reflexivity.
  - replace (c / 128) with 0 by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma swar_step : forall b w' Dn Mn, 0 <= b < 256 ->
  Z.land ((b + 256 * w') + (207 + 256 * Dn) + 1) (128 + 256 * Mn) = 0 ->
  48 <= b /\ Z.land (w' + Dn + 1) Mn = 0.
Proof.
  intros b w' Dn Mn Hb H.
  assert (T7 : Z.testbit ((b + 256 * w') + (207 + 256 * Dn) + 1) 7 = false).
  { pose proof (f_equal (fun x => Z.testbit x 7) H) as T. cbv beta in T. rewrite Z.land_spec, Z.bits_0 in T.
    rewrite (testbit7_low 128 Mn) in T by lia. change (128 <=? 128) with true in T. rewrite Bool.andb_true_r in T. exact T. }
  assert (B : 48 <= b < 176).
  { destruct (Z_lt_le_dec b 48) as [L|L].
    - replace (b + 256 * w' + (207 + 256 * Dn) + 1) with ((b + 208) + 256 * (w' + Dn)) in T7 by lia.
      rewrite testbit7_low in T7 by lia. destruct (Z.leb_spec 128 (b + 208)); [discriminate | lia].
    - replace (b + 256 * w' + (207 + 256 * Dn) + 1) with ((b - 48) + 256 * (w' + Dn + 1)) in T7 by lia.
      rewrite testbit7_low in T7 by lia. destruct (Z.leb_spec 128 (b - 48)); [discriminate | lia]. }
  split; [lia|].
  pose proof (f_equal (fun x => Z.shiftr x 8) H) as S. cbv beta in S.
  rewrite Z.shiftr_land, Z.shiftr_0_l, !Z.shiftr_div_pow2 in S by lia. change (2 ^ 8) with 256 in S.
  replace ((b + 256 * w' + (207 + 256 * Dn) + 1) / 256) with (w' + Dn + 1) in S by (Z.div_mod_to_equations; lia).
  replace ((128 + 256 * Mn) / 256) with Mn in S by (Z.div_mod_to_equations; lia).
  exact S.
Qed.

Lemma land_mod64 : forall x M, 0 <= M < 2 ^ 64 -> Z.land (x mod 2 ^ 64) M = Z.land x M.
Proof.
  intros x M HM. rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. f_equal.
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. exact HM.
Qed.

Lemma land_lor_0_r : forall x y M, Z.land (Z.lor x y) M = 0 -> Z.land y M = 0.
Proof. intros x y M H. rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H. apply H. Qed.

Lemma swar8_ge48 : forall b0 b1 b2 b3 b4 b5 b6 b7 X,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 ->
  Z.land (Z.lor X (((b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) + 14974415777481871312) mod 2 ^ 64))
         9259542123273814144 = 0 ->
  48 <= b0 /\ 48 <= b1 /\ 48 <= b2 /\ 48 <= b3 /\ 48 <= b4 /\ 48 <= b5 /\ 48 <= b6 /\ 48 <= b7.
Proof.
  intros b0 b1 b2 b3 b4 b5 b6 b7 X H0 H1 H2 H3 H4 H5 H6 H7 H.
  apply land_lor_0_r in H. rewrite land_mod64 in H by lia.
  change 14974415777481871312 with ((207 + 256 * (207 + 256 * (207 + 256 * (207 + 256 * (207 + 256 * (207 + 256 * (207 + 256 * (207 + 256 * 0)))))))) + 1) in H.
  change 9259542123273814144 with (128 + 256 * (128 + 256 * (128 + 256 * (128 + 256 * (128 + 256 * (128 + 256 * (128 + 256 * (128 + 256 * 0)))))))) in H.
  rewrite Z.add_assoc in H.
  apply swar_step in H; [|assumption]. destruct H as [G0 H]. split; [exact G0|].
  apply swar_step in H; [|assumption]. destruct H as [G1 H]. split; [exact G1|].
  apply swar_step in H; [|assumption]. destruct H as [G2 H]. split; [exact G2|].
  apply swar_step in H; [|assumption]. destruct H as [G3 H]. split; [exact G3|].
  apply swar_step in H; [|assumption]. destruct H as [G4 H]. split; [exact G4|].
  apply swar_step in H; [|assumption]. destruct H as [G5 H]. split; [exact G5|].
  apply swar_step in H; [|assumption]. destruct H as [G6 H]. split; [exact G6|].
  replace b7 with (b7 + 256 * 0) in H by lia.
  apply swar_step in H; [|assumption]. destruct H as [G7 H]. exact G7.
Qed.

Lemma lor_disj : forall x y k, 0 <= k -> 0 <= x -> x mod 2 ^ k = 0 -> 0 <= y < 2 ^ k -> Z.lor x y = x + y.
Proof.
  intros x y k Hk Hx Hm Hy.
  assert (L : Z.land x y = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n k) as [Lt|Ge].
    - rewrite <- (Z.mod_pow2_bits_low x k n) by lia. rewrite Hm, Z.bits_0. reflexivity.
    - destruct (Z.eq_dec y 0) as [->|NZ]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
      rewrite (Z.bits_above_log2 y n); [apply Bool.andb_false_r | lia |].
      assert (Z.log2 y < k) by (apply Z.log2_lt_pow2; lia). lia. }
  rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

Definition le4z (b0 b1 b2 b3 : Z) : Z :=
  Z.lor (Z.lor (Z.shiftl b3 24 mod 18446744073709551616) (Z.shiftl b2 16 mod 18446744073709551616))
        (Z.lor (Z.shiftl b1 8 mod 18446744073709551616) b0).

Lemma le4z_eq : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  le4z b0 b1 b2 b3 = b0 + 256 * (b1 + 256 * (b2 + 256 * b3)).
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. unfold le4z.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  rewrite !Z.mod_small by lia.
  rewrite (lor_disj (b1 * 256) b0 8) by (try apply Z.mod_mul; change (2 ^ 8) with 256; lia).
  rewrite (lor_disj (b3 * 16777216) (b2 * 65536) 24)
    by (try (change (2 ^ 24) with 16777216; apply Z.mod_mul); change (2 ^ 24) with 16777216; lia).
  rewrite (lor_disj (b3 * 16777216 + b2 * 65536) (b1 * 256 + b0) 16).
  - lia.
  - lia.
  - lia.
  - change (2 ^ 16) with 65536. replace (b3 * 16777216 + b2 * 65536) with ((b3 * 256 + b2) * 65536) by lia. apply Z.mod_mul. lia.
  - change (2 ^ 16) with 65536. lia.
Qed.

Definition le8z (b0 b1 b2 b3 b4 b5 b6 b7 : Z) : Z :=
  Z.lor (Z.shiftl (le4z b4 b5 b6 b7) 32 mod 18446744073709551616) (le4z b0 b1 b2 b3).

Lemma le8z_eq : forall b0 b1 b2 b3 b4 b5 b6 b7,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 ->
  le8z b0 b1 b2 b3 b4 b5 b6 b7 = b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7)))))).
Proof.
  intros b0 b1 b2 b3 b4 b5 b6 b7 H0 H1 H2 H3 H4 H5 H6 H7. unfold le8z.
  rewrite !le4z_eq by assumption.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite Z.mod_small by lia.
  rewrite (lor_disj _ (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) 32).
  - lia.
  - lia.
  - lia.
  - apply Z.mod_mul. lia.
  - change (2 ^ 32) with 4294967296. lia.
Qed.

Lemma swar8_machine : forall b0 b1 b2 b3 b4 b5 b6 b7 X,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 ->
  Z.land (Z.lor X ((le8z b0 b1 b2 b3 b4 b5 b6 b7 + 14974415777481871312) mod 18446744073709551616)) 9259542123273814144 = 0 ->
  48 <= b0 /\ 48 <= b1 /\ 48 <= b2 /\ 48 <= b3 /\ 48 <= b4 /\ 48 <= b5 /\ 48 <= b6 /\ 48 <= b7.
Proof.
  intros b0 b1 b2 b3 b4 b5 b6 b7 X H0 H1 H2 H3 H4 H5 H6 H7 H.
  rewrite le8z_eq in H by assumption. change 18446744073709551616 with (2 ^ 64) in H.
  eapply swar8_ge48; eassumption.
Qed.

Lemma land_mod_distr : forall a b k, 0 <= k -> Z.land a b mod 2 ^ k = Z.land (a mod 2 ^ k) (b mod 2 ^ k).
Proof.
  intros a b k Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z_lt_le_dec n k) as [Lt|Ge].
  - rewrite !Z.mod_pow2_bits_low by lia. apply Z.land_spec.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma swar4_ge48 : forall b0 b1 b2 b3 hi X, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  Z.land (Z.lor X (((b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * hi))) + 18446744072901087184 + 2147483648) mod 4294967296 - 2147483648)
                   mod 18446744073709551616)) 18446744071570489472 = 0 ->
  48 <= b0 /\ 48 <= b1 /\ 48 <= b2 /\ 48 <= b3.
Proof.
  intros b0 b1 b2 b3 hi X H0 H1 H2 H3 H.
  apply land_lor_0_r in H.
  pose proof (f_equal (fun x => x mod 2 ^ 32) H) as H'. cbv beta in H'. rewrite land_mod_distr in H' by lia.
  change (0 mod 2 ^ 32) with 0 in H'. change (18446744071570489472 mod 2 ^ 32) with 2155905152 in H'. change (2 ^ 32) with 4294967296 in H'.
  set (w := b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * hi)))) in *.
  replace (((w + 18446744072901087184 + 2147483648) mod 4294967296 - 2147483648) mod 18446744073709551616 mod 4294967296)
    with ((w + 3486502864) mod 2 ^ 32) in H' by (change (2 ^ 32) with 4294967296; Z.div_mod_to_equations; lia).
  assert (LM : forall x M, 0 <= M < 2 ^ 32 -> Z.land (x mod 2 ^ 32) M = Z.land x M).
  { intros x M HM. rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. f_equal.
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. exact HM. }
  rewrite LM in H' by lia. unfold w in H'.
  change 3486502864 with ((207 + 256 * (207 + 256 * (207 + 256 * (207 + 256 * 0)))) + 1) in H'.
  change 2155905152 with (128 + 256 * (128 + 256 * (128 + 256 * (128 + 256 * 0)))) in H'.
  rewrite Z.add_assoc in H'.
  apply swar_step in H'; [|assumption]. destruct H' as [G0 H']. split; [exact G0|].
  apply swar_step in H'; [|assumption]. destruct H' as [G1 H']. split; [exact G1|].
  apply swar_step in H'; [|assumption]. destruct H' as [G2 H']. split; [exact G2|].
  apply swar_step in H'; [|assumption]. destruct H' as [G3 H']. exact G3.
Qed.
