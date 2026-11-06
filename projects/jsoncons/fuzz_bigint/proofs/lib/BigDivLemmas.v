(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BDV.

Definition MM : Z := 2 ^ 64.

Lemma lor_bound a b n : 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros Hn Ha Hb. split. apply Z.lor_nonneg; lia.
  destruct (Z.eq_dec a 0) as [->|Na]. { rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0) as [->|Nb]. { rewrite Z.lor_0_r. lia. }
  apply Z.log2_lt_cancel. rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_ldiff_same a b : Z.lor a (Z.ldiff b a) = Z.lor a b.
Proof.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec, Z.ldiff_spec.
  destruct (Z.testbit a i), (Z.testbit b i); reflexivity.
Qed.

Lemma lor_ge_l a b : 0 <= a -> 0 <= b -> a <= Z.lor a b.
Proof.
  intros Ha Hb. rewrite <- lor_ldiff_same.
  assert (D: Z.land a (Z.ldiff b a) = 0). { rewrite Z.land_comm. apply Z.land_ldiff. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D.
  pose proof (Z.ldiff_nonneg b a). lia.
Qed.

(* [comment removed for export] *)
Lemma msb_recombine (t z : Z) c :
  2 ^ 63 <= t < MM -> 0 <= z < MM -> 1 <= c <= 63 ->
  2 ^ 63 <= Z.lor t (z / 2 ^ (64 - c)) < MM.
Proof.
  intros Ht Hz Hc. unfold MM in *.
  assert (B: 0 <= z / 2 ^ (64 - c) < 2 ^ 64).
  { split. apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia].
    apply Z.div_lt_upper_bound. apply Z.pow_pos_nonneg; lia.
    assert (2 ^ 64 <= 2 ^ 64 * 2 ^ (64 - c)) by (assert (1 <= 2 ^ (64 - c)) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) || idtac; pose proof (Z.pow_pos_nonneg 2 (64 - c)); lia); nia). lia. }
  pose proof (lor_bound t (z / 2 ^ (64 - c)) 64 ltac:(lia) ltac:(lia) B).
  pose proof (lor_ge_l t (z / 2 ^ (64 - c)) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma msb_recombine_clz (y z c : Z) :
  2 ^ 63 <= y * 2 ^ c < MM -> 0 <= z < MM -> 1 <= c <= 63 ->
  2 ^ 63 <= Z.lor ((y * 2 ^ c) mod MM) (z / 2 ^ (64 - c)) < MM.
Proof. intros Hy Hz Hc. rewrite Z.mod_small by (unfold MM in *; lia). apply msb_recombine; auto. Qed.

(* [comment removed for export] *)
Lemma mul_max_word_2 (d0 d1 : Z) :
  0 <= d1 < d0 -> d0 < MM ->
  (d0 + d1 * MM) * (MM - 1) = (MM - d0) + (d0 - d1 - 1) * MM + d1 * MM ^ 2
  /\ 0 < MM - d0 < MM /\ 0 <= d0 - d1 - 1 < MM.
Proof. intros H1 H2. unfold MM in *. split. ring. lia. Qed.

(* [comment removed for export] *)
Lemma mul_max_word_2_limbs (d0 d1 : Z) :
  0 <= d1 < d0 -> d0 < MM ->
  let P := (d0 + d1 * MM) * (MM - 1) in
  P mod MM = MM - d0 /\ (P / MM) mod MM = d0 - d1 - 1 /\ (P / MM ^ 2) mod MM = d1 /\ P / MM ^ 3 = 0.
Proof.
  intros H1 H2. destruct (mul_max_word_2 d0 d1 H1 H2) as (E & R1 & R2). cbv zeta. rewrite E.
  assert (M0: 0 < MM) by (unfold MM; lia).
  assert (Hd1: 0 <= d1 < MM) by lia.
  replace (MM ^ 2) with (MM * MM) by ring. replace (MM ^ 3) with (MM * MM * MM) by ring.
  repeat split.
  - rewrite <- Z.add_assoc. replace ((d0 - d1 - 1) * MM + d1 * (MM * MM)) with (((d0 - d1 - 1) + d1 * MM) * MM) by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - replace (MM - d0 + (d0 - d1 - 1) * MM + d1 * (MM * MM)) with ((MM - d0) + ((d0 - d1 - 1) + d1 * MM) * MM) by ring.
    rewrite Z.div_add by lia. rewrite (Z.div_small (MM - d0)) by lia. rewrite Z.add_0_l.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - replace (MM - d0 + (d0 - d1 - 1) * MM + d1 * (MM * MM)) with (((MM - d0) + (d0 - d1 - 1) * MM) + d1 * (MM * MM)) by ring.
    rewrite Z.div_add by lia. rewrite (Z.div_small (MM - d0 + (d0 - d1 - 1) * MM)) by nia. rewrite Z.add_0_l. apply Z.mod_small. lia.
  - apply Z.div_small. nia.
Qed.

(* [comment removed for export] *)
Lemma shl2_words (bt bn : Z) :
  1 <= bt < MM -> 0 <= bn < MM ->
  0 <= bt / 2 ^ 62 <= 3
  /\ (bt / 2 ^ 62 = 0 -> 4 <= Z.lor ((bt * 4) mod MM) (bn / 2 ^ 62) < MM).
Proof.
  intros Hb Hn. unfold MM in *. split.
  { split. apply Z.div_pos; lia. assert (bt / 2 ^ 62 < 4) by (apply Z.div_lt_upper_bound; lia). lia. }
  intros Z0.
  assert (Hs: bt < 2 ^ 62). { apply Z.div_small_iff in Z0; lia. }
  rewrite Z.mod_small by lia.
  assert (B: 0 <= bn / 2 ^ 62 < 4). { split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. }
  pose proof (lor_ge_l (bt * 4) (bn / 2 ^ 62) ltac:(lia) ltac:(lia)).
  pose proof (lor_bound (bt * 4) (bn / 2 ^ 62) 64 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

End BDV.
