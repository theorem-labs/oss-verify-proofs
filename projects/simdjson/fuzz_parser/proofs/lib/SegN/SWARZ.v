(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module SWZ.
Fixpoint lev (bs : list Z) : Z := match bs with [] => 0 | b :: r => b + 256 * lev r end.
Fixpoint rep (c : Z) (n : nat) : Z := match n with O => 0 | S n' => c + 256 * rep c n' end.

Lemma testbit7 : forall x, 0 <= x < 256 -> Z.testbit x 7 = (128 <=? x).
Proof.
  intros x Hx. rewrite Z.testbit_odd. change (Z.shiftr x 7) with (Z.shiftr x 7).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 7) with 128.
  destruct (Z.leb_spec 128 x).
  - replace (x / 128) with 1 by (apply Z.div_unique with (x - 128); lia). reflexivity.
  - replace (x / 128) with 0 by (apply Z.div_unique with x; lia). reflexivity.
Qed.

Lemma mod_split256 : forall s q M, 0 <= s < 256 -> 0 < M -> (s + 256 * q) mod (256 * M) = s + 256 * (q mod M).
Proof.
  intros s q M Hs HM. rewrite Z.mod_eq by lia.
  assert (E : (s + 256 * q) / (256 * M) = q / M).
  { rewrite <- Z.div_div by lia. f_equal. replace (s + 256 * q) with (q * 256 + s) by lia. rewrite Z.div_add_l by lia.
    rewrite (Z.div_small s 256) by lia. lia. }
  rewrite E. rewrite (Z.mod_eq q M) by lia. lia.
Qed.

Lemma mod_low256 : forall x n, (x mod 2 ^ (8 * Z.of_nat (S n))) mod 256 = x mod 256.
Proof.
  intros x n. replace (2 ^ (8 * Z.of_nat (S n))) with (256 * 2 ^ (8 * Z.of_nat n)).
  - rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_nat n)); lia | ].
    exists (2 ^ (8 * Z.of_nat n)). lia.
  - replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia. rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Theorem swar_digits : forall bs, Forall (fun b => 0 <= b <= 255) bs ->
  Z.land (Z.lor ((lev bs + rep 70 (length bs)) mod 2 ^ (8 * Z.of_nat (length bs)))
                ((lev bs - rep 48 (length bs)) mod 2 ^ (8 * Z.of_nat (length bs)))) (rep 128 (length bs)) = 0 ->
  Forall (fun b => 48 <= b <= 57) bs.
Proof.
  induction bs as [|b r IH]; intros HB H; [constructor|].
  apply Forall_cons_iff in HB as [Hb HR]. cbn [length lev rep] in H. set (n := length r) in *.
  set (A := (b + 256 * lev r + (70 + 256 * rep 70 n)) mod 2 ^ (8 * Z.of_nat (S n))) in H.
  set (B := (b + 256 * lev r - (48 + 256 * rep 48 n)) mod 2 ^ (8 * Z.of_nat (S n))) in H.
  assert (HP : 0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
  assert (HS : 2 ^ (8 * Z.of_nat (S n)) = 256 * 2 ^ (8 * Z.of_nat n)).
  { replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  (* [comment removed for export] *)
  assert (T7 : Z.testbit A 7 = false /\ Z.testbit B 7 = false).
  { assert (X : Z.testbit (Z.land (Z.lor A B) (128 + 256 * rep 128 n)) 7 = false) by (rewrite H; reflexivity).
    rewrite Z.land_spec, Z.lor_spec in X.
    assert (K7 : Z.testbit (128 + 256 * rep 128 n) 7 = true).
    { rewrite <- (Z.mod_pow2_bits_low _ 8) by lia. replace (128 + 256 * rep 128 n) with (128 + rep 128 n * 2 ^ 8) by lia.
      rewrite Z_mod_plus_full. reflexivity. }
    rewrite K7, andb_true_r in X. apply orb_false_iff in X. exact X. }
  destruct T7 as [TA TB].
  rewrite <- (Z.mod_pow2_bits_low A 8) in TA by lia. rewrite <- (Z.mod_pow2_bits_low B 8) in TB by lia.
  change (2 ^ 8) with 256 in TA, TB.
  unfold A, B in TA, TB. rewrite mod_low256 in TA, TB.
  rewrite testbit7 in TA by (apply Z.mod_pos_bound; lia). rewrite testbit7 in TB by (apply Z.mod_pos_bound; lia).
  apply Z.leb_gt in TA. apply Z.leb_gt in TB.
  replace (b + 256 * lev r + (70 + 256 * rep 70 n)) with ((b + 70) + lev r * 256 + rep 70 n * 256) in TA by lia.
  replace (b + 256 * lev r - (48 + 256 * rep 48 n)) with ((b - 48) + lev r * 256 - rep 48 n * 256) in TB by lia.
  rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod in TA by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod in TA by lia.
  assert (Hd : 48 <= b <= 57).
  { assert (TB' : (b - 48 + lev r * 256 - rep 48 n * 256) mod 256 = (b - 48) mod 256).
    { replace (b - 48 + lev r * 256 - rep 48 n * 256) with ((b - 48) + (lev r - rep 48 n) * 256) by lia. apply Z_mod_plus_full. }
    rewrite TB' in TB. clear TB'.
    destruct (Z.lt_ge_cases b 48).
    - assert (E : (b - 48) mod 256 = b - 48 + 256) by (symmetry; apply Z.mod_unique with (-1); lia). rewrite E in TB. lia.
    - destruct (Z.lt_ge_cases b 58); [lia|].
      destruct (Z.lt_ge_cases b 186).
      + rewrite (Z.mod_small (b + 70) 256) in TA by lia. lia.
      + rewrite (Z.mod_small (b - 48) 256) in TB by lia. lia. }
  constructor; [exact Hd|]. apply IH; [exact HR|].
  (* [comment removed for export] *)
  assert (EA : A = (b + 70) + 256 * ((lev r + rep 70 n) mod 2 ^ (8 * Z.of_nat n))).
  { unfold A. rewrite HS. replace (b + 256 * lev r + (70 + 256 * rep 70 n)) with ((b + 70) + 256 * (lev r + rep 70 n)) by lia.
    apply mod_split256; lia. }
  assert (EB : B = (b - 48) + 256 * ((lev r - rep 48 n) mod 2 ^ (8 * Z.of_nat n))).
  { unfold B. rewrite HS. replace (b + 256 * lev r - (48 + 256 * rep 48 n)) with ((b - 48) + 256 * (lev r - rep 48 n)) by lia.
    apply mod_split256; lia. }
  assert (SH : Z.shiftr (Z.land (Z.lor A B) (128 + 256 * rep 128 n)) 8 = 0) by (rewrite H; reflexivity).
  rewrite Z.shiftr_land, Z.shiftr_lor in SH. rewrite !Z.shiftr_div_pow2 in SH by lia. change (2 ^ 8) with 256 in SH.
  rewrite EA, EB in SH.
  replace (128 + 256 * rep 128 n) with (128 + rep 128 n * 256) in SH by lia.
  replace (b + 70 + 256 * ((lev r + rep 70 n) mod 2 ^ (8 * Z.of_nat n))) with ((b + 70) + ((lev r + rep 70 n) mod 2 ^ (8 * Z.of_nat n)) * 256) in SH by lia.
  replace (b - 48 + 256 * ((lev r - rep 48 n) mod 2 ^ (8 * Z.of_nat n))) with ((b - 48) + ((lev r - rep 48 n) mod 2 ^ (8 * Z.of_nat n)) * 256) in SH by lia.
  rewrite !Z.div_add in SH by lia. rewrite (Z.div_small (b + 70) 256) in SH by lia. rewrite (Z.div_small (b - 48) 256) in SH by lia.
  rewrite (Z.div_small 128 256) in SH by lia. rewrite !Z.add_0_l in SH. exact SH.
Qed.
End SWZ.
