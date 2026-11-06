(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import SoftFloat.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.
Local Ltac dnia := Z.div_mod_to_equations; nia.

Lemma ones64_eq : ONES64 = 2^64 - 1. Proof. reflexivity. Qed.
Lemma m32_eq : M32 = 2^32 - 1. Proof. reflexivity. Qed.
Lemma mask48_eq : MASK48 = 2^48 - 1. Proof. reflexivity. Qed.
Lemma abs_hi_eq : ABS_HI = 2^63 - 1. Proof. reflexivity. Qed.
Lemma sign64_eq : SIGN64 = 2^63. Proof. reflexivity. Qed.
Lemma inf_hi_eq : INF_HI = 32767 * 2^48. Proof. reflexivity. Qed.
Lemma implicit_hi_eq : IMPLICIT_HI = 2^48. Proof. reflexivity. Qed.
Lemma impl3_hi_eq : IMPL3_HI = 2^51. Proof. reflexivity. Qed.

Lemma land_ones_mod : forall x k, 0 <= k -> Z.land x (2^k - 1) = x mod 2^k.
Proof. intros. rewrite <- Z.land_ones by lia. f_equal. rewrite Z.ones_equiv. rewrite Z.sub_1_r. reflexivity. Qed.

Lemma wrap64_id : forall x, 0 <= x < 2^64 -> wrap64 x = x.
Proof. intros. rewrite wrap64_mod. apply Z.mod_small. lia. Qed.

Lemma shiftr_div : forall x k, 0 <= k -> Z.shiftr x k = x / 2^k.
Proof. intros. apply Z.shiftr_div_pow2. lia. Qed.
Lemma shiftl_mul : forall x k, 0 <= k -> Z.shiftl x k = x * 2^k.
Proof. intros. apply Z.shiftl_mul_pow2. lia. Qed.

Lemma lor_disjoint : forall a b, 0 <= a -> 0 <= b -> Z.land a b = 0 -> Z.lor a b = a + b.
Proof. intros a b Ha Hb H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.

Lemma land_high_low : forall x y k, 0 <= k -> 0 <= x -> 0 <= y < 2^k -> Z.land (x * 2^k) y = 0.
Proof.
  intros x y k Hk Hx Hy. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n k).
  - rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec y 0) as [->|]. { rewrite Z.bits_0. apply Bool.andb_false_r. }
    rewrite (Z.bits_above_log2 y n); [apply Bool.andb_false_r| lia|].
    apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hy)|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma lor_high_low : forall x y k, 0 <= k -> 0 <= x -> 0 <= y < 2^k -> Z.lor (x * 2^k) y = x * 2^k + y.
Proof. intros. apply lor_disjoint; [nia| lia| apply land_high_low; lia]. Qed.

Lemma lor_low_high : forall x y k, 0 <= k -> 0 <= x -> 0 <= y < 2^k -> Z.lor y (x * 2^k) = x * 2^k + y.
Proof. intros. rewrite Z.lor_comm. apply lor_high_low; lia. Qed.

Lemma mk128_val : forall hi lo, 0 <= hi -> 0 <= lo < 2^64 -> mk128 hi lo = hi * 2^64 + lo.
Proof. intros. unfold mk128. rewrite shiftl_mul by lia. apply lor_high_low; lia. Qed.

Lemma lo64_val : forall hi lo, 0 <= lo < 2^64 -> lo64 (hi * 2^64 + lo) = lo.
Proof. intros. unfold lo64. rewrite wrap64_mod. rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia. Qed.

Lemma hi64_val : forall hi lo, 0 <= hi < 2^64 -> 0 <= lo < 2^64 -> hi64 (hi * 2^64 + lo) = hi.
Proof.
  intros. unfold hi64. rewrite wrap64_mod, shiftr_div by lia.
  rewrite Z.add_comm, Z.div_add by lia. rewrite Z.div_small by lia. apply Z.mod_small. lia.
Qed.

Lemma lo64_range : forall x, 0 <= lo64 x < 2^64. Proof. intros. unfold lo64. apply wrap64_range. Qed.
Lemma hi64_range : forall x, 0 <= hi64 x < 2^64. Proof. intros. unfold hi64. apply wrap64_range. Qed.

Definition bits_set (x lo s : Z) : Prop :=
  0 <= x /\ (forall n, lo <= n <= s -> Z.testbit x n = true) /\ (forall n, s < n -> Z.testbit x n = false).

Lemma bits_set_init : forall u s, 0 <= s -> 2^s <= u < 2^(s+1) -> bits_set u s s.
Proof.
  intros u s Hs Hu.
  assert (L : Z.log2 u = s).
  { apply (Z.log2_unique' u s (u - 2^s)); [lia| |lia]. rewrite Z.pow_add_r in Hu by lia. change (2^1) with 2 in Hu. lia. }
  split; [lia|]. split.
  - intros n Hn. replace n with s by lia. rewrite <- L. apply Z.bit_log2. lia.
  - intros n Hn. apply Z.bits_above_log2; lia.
Qed.

Lemma bits_set_step : forall x lo s k, bits_set x lo s -> 0 < k -> (lo = 0 \/ k <= s - lo + 1) -> 0 <= lo ->
  bits_set (Z.lor x (Z.shiftr x k)) (Z.max 0 (lo - k)) s.
Proof.
  intros x lo s k (Hx & H1 & H2) Hk Hkl Hlo. split; [|split].
  - apply Z.lor_nonneg. split; [lia|]. apply Z.shiftr_nonneg. lia.
  - intros n Hn. rewrite Z.lor_spec. rewrite Z.shiftr_spec by lia.
    destruct (Z.lt_ge_cases n lo).
    + rewrite (H1 (n + k)) by lia. apply Bool.orb_true_r.
    + rewrite (H1 n) by lia. reflexivity.
  - intros n Hn. destruct (Z.lt_ge_cases n 0). { apply Z.testbit_neg_r. lia. }
    rewrite Z.lor_spec. rewrite Z.shiftr_spec by lia. rewrite (H2 n) by lia. rewrite (H2 (n + k)) by lia. reflexivity.
Qed.

Lemma bits_set_full : forall x s, 0 <= s -> bits_set x 0 s -> x = 2^(s+1) - 1.
Proof.
  intros x s Hs (Hx & H1 & H2). transitivity (Z.ones (s+1)); [| rewrite Z.ones_equiv; lia].
  apply Z.bits_inj'. intros n Hn.
  destruct (Z.lt_ge_cases s n).
  - rewrite H2 by lia. rewrite Z.ones_spec_high by lia. reflexivity.
  - rewrite H1 by lia. rewrite Z.ones_spec_low by lia. reflexivity.
Qed.

Definition smear64 (x : Z) : Z :=
  let x1 := Z.lor x  (Z.shiftr x 1) in
  let x2 := Z.lor x1 (Z.shiftr x1 2) in
  let x3 := Z.lor x2 (Z.shiftr x2 4) in
  let x4 := Z.lor x3 (Z.shiftr x3 8) in
  let x5 := Z.lor x4 (Z.shiftr x4 16) in
  Z.lor x5 (Z.shiftr x5 32).

Lemma smear64_val : forall u s, 0 <= s <= 63 -> 2^s <= u < 2^(s+1) -> smear64 u = 2^(s+1) - 1.
Proof.
  intros u s Hs Hu. unfold smear64.
  pose proof (bits_set_init u s ltac:(lia) Hu) as B0.
  pose proof (bits_set_step _ _ _ 1 B0 ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
  pose proof (bits_set_step _ _ _ 2 B1 ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
  pose proof (bits_set_step _ _ _ 4 B2 ltac:(lia) ltac:(lia) ltac:(lia)) as B3.
  pose proof (bits_set_step _ _ _ 8 B3 ltac:(lia) ltac:(lia) ltac:(lia)) as B4.
  pose proof (bits_set_step _ _ _ 16 B4 ltac:(lia) ltac:(lia) ltac:(lia)) as B5.
  pose proof (bits_set_step _ _ _ 32 B5 ltac:(lia) ltac:(lia) ltac:(lia)) as B6.
  apply bits_set_full; [lia|].
  replace 0 with (Z.max 0 (Z.max 0 (Z.max 0 (Z.max 0 (Z.max 0 (Z.max 0 (s - 1) - 2) - 4) - 8) - 16) - 32)) at 1 by lia.
  exact B6.
Qed.

Definition smear32 (x : Z) : Z :=
  let x1 := Z.lor x  (Z.shiftr x 1) in
  let x2 := Z.lor x1 (Z.shiftr x1 2) in
  let x3 := Z.lor x2 (Z.shiftr x2 4) in
  let x4 := Z.lor x3 (Z.shiftr x3 8) in
  Z.lor x4 (Z.shiftr x4 16).

Lemma smear32_val : forall u s, 0 <= s <= 31 -> 2^s <= u < 2^(s+1) -> smear32 u = 2^(s+1) - 1.
Proof.
  intros u s Hs Hu. unfold smear32.
  pose proof (bits_set_init u s ltac:(lia) Hu) as B0.
  pose proof (bits_set_step _ _ _ 1 B0 ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
  pose proof (bits_set_step _ _ _ 2 B1 ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
  pose proof (bits_set_step _ _ _ 4 B2 ltac:(lia) ltac:(lia) ltac:(lia)) as B3.
  pose proof (bits_set_step _ _ _ 8 B3 ltac:(lia) ltac:(lia) ltac:(lia)) as B4.
  pose proof (bits_set_step _ _ _ 16 B4 ltac:(lia) ltac:(lia) ltac:(lia)) as B5.
  apply bits_set_full; [lia|].
  replace 0 with (Z.max 0 (Z.max 0 (Z.max 0 (Z.max 0 (Z.max 0 (s - 1) - 2) - 4) - 8) - 16)) at 1 by lia.
  exact B5.
Qed.

Definition pop64 (y : Z) : Z :=
  let c1 := sub64 y (Z.land (Z.shiftr y 1) 0x5555555555555555) in
  let c2 := add64 (Z.land c1 0x3333333333333333) (Z.land (Z.shiftr c1 2) 0x3333333333333333) in
  let c3 := Z.land (add64 c2 (Z.shiftr c2 4)) 0x0f0f0f0f0f0f0f0f in
  Z.shiftr (mul64 c3 0x0101010101010101) 56.

Lemma clz64_mirror_eq : forall x, clz64_mirror x = pop64 (not64 (smear64 x)).
Proof. intros. unfold clz64_mirror, pop64, smear64. cbv zeta. reflexivity. Qed.

Lemma pop64_cases : forall n : nat, (n < 64)%nat -> pop64 (not64 (2^(Z.of_nat n + 1) - 1)) = 63 - Z.of_nat n.
Proof.
  intros n H.
  do 64 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma clz64_mirror_val : forall x s, 0 <= s <= 63 -> 2^s <= x < 2^(s+1) -> clz64_mirror x = 63 - s.
Proof.
  intros x s Hs Hx. rewrite clz64_mirror_eq, (smear64_val x s Hs Hx).
  rewrite <- (Z2Nat.id s) at 1 by lia. rewrite pop64_cases by lia. lia.
Qed.

Lemma clz64_mirror_0 : clz64_mirror 0 = 64.
Proof. vm_compute. reflexivity. Qed.

Definition pop32 (y : Z) : Z :=
  let c1 := sub64 y (Z.land (Z.shiftr y 1) 0x55555555) in
  let c2 := add64 (Z.land c1 0x33333333) (Z.land (Z.shiftr c1 2) 0x33333333) in
  let c3 := Z.land (add64 c2 (Z.shiftr c2 4)) 0x0f0f0f0f in
  srliw (mul64 c3 0x01010101) 24.

Lemma lxor_low_high : forall x y k, 0 <= k -> 0 <= x -> 0 <= y < 2^k -> Z.lxor y (x * 2^k) = x * 2^k + y.
Proof.
  intros. rewrite Z.lxor_comm. rewrite <- Z.add_nocarry_lxor; [lia|]. apply land_high_low; lia.
Qed.
Lemma sext32_small : forall v, 0 <= v < 2^31 -> sext32 v = v.
Proof.
  intros v Hv. unfold sext32, sub64. rewrite m32_eq, land_ones_mod, Z.mod_small by lia.
  change 0x80000000 with (1 * 2^31). rewrite lxor_low_high by lia.
  rewrite wrap64_mod. rewrite Z.mod_small; lia.
Qed.
Lemma sext32_big : forall v, 2^31 <= v < 2^32 -> sext32 v = 2^64 - 2^32 + v.
Proof.
  intros v Hv. unfold sext32, sub64. rewrite m32_eq, land_ones_mod, Z.mod_small by lia.
  change 0x80000000 with (2^31).
  replace (Z.lxor v (2^31)) with (v - 2^31).
  2:{ replace v with (Z.lxor (v - 2^31) (1 * 2^31)) at 2.
      - rewrite Z.lxor_assoc. change (Z.lxor (1 * 2^31) (2^31)) with 0. rewrite Z.lxor_0_r. reflexivity.
      - rewrite lxor_low_high; lia. }
  rewrite wrap64_mod. replace (v - 2^31 - 2^31) with ((2^64 - 2^32 + v) + (-1) * 2^64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma zext32_sext32 : forall u, 0 <= u < 2^32 -> zext32 (sext32 u) = u.
Proof.
  intros u Hu. unfold zext32. rewrite m32_eq, land_ones_mod by lia.
  destruct (Z.lt_ge_cases u (2^31)).
  - rewrite sext32_small by lia. apply Z.mod_small. lia.
  - rewrite sext32_big by lia. replace (2^64 - 2^32 + u) with (u + (2^32 - 1) * 2^32) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma lor_bound : forall a b k, 0 <= k -> 0 <= a < 2^k -> 0 <= b < 2^k -> 0 <= Z.lor a b < 2^k.
Proof.
  intros a b k Hk Ha Hb.
  assert (0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  split; [lia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [->|NZ]; [lia|].
  destruct (Z.eq_dec a 0) as [->|NA]. { rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0) as [->|NB]. { rewrite Z.lor_0_r. lia. }
  apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.
Lemma not64_val : forall x, 0 <= x < 2^64 -> not64 x = 2^64 - 1 - x.
Proof.
  intros x Hx. unfold not64. rewrite ones64_eq.
  change (2^64 - 1) with (Z.ones 64) at 1.
  rewrite <- Z.ldiff_ones_l_low; [|lia|].
  2:{ destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite Z.ldiff_land, Z.land_comm. change (Z.ones 64) with (2^64 - 1). rewrite land_ones_mod by lia.
  rewrite Z.lnot_eq_pred_opp. replace (- x - 1) with ((2^64 - 1 - x) + (-1) * 2^64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Definition smear32w (r : Z) : Z :=
  let x1 := Z.lor r  (srliw r 1) in
  let x2 := Z.lor x1 (srliw x1 2) in
  let x3 := Z.lor x2 (srliw x2 4) in
  let x4 := Z.lor x3 (srliw x3 8) in
  Z.lor x4 (srliw x4 16).

Lemma clz32_mirror_eq : forall r, clz32_mirror r = pop32 (not64 (smear32w r)).
Proof. intros. unfold clz32_mirror, pop32, smear32w. cbv zeta. reflexivity. Qed.

Lemma pow2_ge1 : forall k, 0 <= k -> 1 <= 2^k.
Proof. intros. change 1 with (2^0). apply Z.pow_le_mono_r; lia. Qed.
Lemma pow2_ge2 : forall k, 1 <= k -> 2 <= 2^k.
Proof. intros. change 2 with (2^1). apply Z.pow_le_mono_r; lia. Qed.

Lemma shiftr_bound : forall w k n, 0 <= w < 2^n -> 0 <= k -> 0 <= Z.shiftr w k < 2^n.
Proof.
  intros w k n Hw Hk. rewrite shiftr_div by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. pose proof (pow2_ge1 k Hk). nia.
Qed.

Lemma srliw_hw : forall h w k, 0 <= h -> 0 <= w < 2^32 -> 1 <= k -> srliw (h * 2^32 + w) k = Z.shiftr w k.
Proof.
  intros h w k Hh Hw Hk. unfold srliw. rewrite m32_eq, land_ones_mod by lia.
  rewrite Z.add_comm, Z_mod_plus_full, Z.mod_small by lia.
  apply sext32_small. rewrite shiftr_div by lia.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  pose proof (pow2_ge2 k Hk). nia.
Qed.

Lemma lor_hw : forall h w v, 0 <= h -> 0 <= w < 2^32 -> 0 <= v < 2^32 -> Z.lor (h * 2^32 + w) v = h * 2^32 + Z.lor w v.
Proof.
  intros h w v Hh Hw Hv. rewrite <- (lor_high_low h w 32) by lia. rewrite <- Z.lor_assoc.
  apply lor_high_low; [lia|lia|]. apply lor_bound; lia.
Qed.

Lemma smear32w_val : forall h u, 0 <= h -> 0 <= u < 2^32 -> smear32w (h * 2^32 + u) = h * 2^32 + smear32 u.
Proof.
  intros h u Hh Hu. unfold smear32w, smear32.
  assert (ST : forall w k, 0 <= w < 2^32 -> 1 <= k ->
    Z.lor (h * 2^32 + w) (srliw (h * 2^32 + w) k) = h * 2^32 + Z.lor w (Z.shiftr w k) /\ 0 <= Z.lor w (Z.shiftr w k) < 2^32).
  { intros w k Hw Hk. rewrite srliw_hw by lia. split; [apply lor_hw; try lia|]; [apply shiftr_bound; lia|]. apply lor_bound; [lia|lia|]. apply shiftr_bound; lia. }
  destruct (ST u 1 Hu ltac:(lia)) as [-> B1].
  destruct (ST _ 2 B1 ltac:(lia)) as [-> B2].
  destruct (ST _ 4 B2 ltac:(lia)) as [-> B3].
  destruct (ST _ 8 B3 ltac:(lia)) as [-> B4].
  destruct (ST _ 16 B4 ltac:(lia)) as [-> B5]. reflexivity.
Qed.

Lemma pop32_cases : forall n : nat, (n < 31)%nat -> pop32 (2^64 - 2^(Z.of_nat n + 1)) = 31 - Z.of_nat n.
Proof. intros n H. do 31 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. Qed.
Lemma pop32_0 : pop32 0 = 0. Proof. vm_compute. reflexivity. Qed.

Lemma clz32_mirror_val : forall u s, 0 <= s <= 31 -> 2^s <= u < 2^(s+1) -> clz32_mirror (sext32 u) = 31 - s.
Proof.
  intros u s Hs Hu. rewrite clz32_mirror_eq.
  assert (U32 : u < 2^32). { eapply Z.lt_le_trans; [apply (proj2 Hu)|]. apply Z.pow_le_mono_r; lia. }
  destruct (Z.lt_ge_cases u (2^31)) as [SM|BG].
  - rewrite sext32_small by lia. rewrite <- (Z.add_0_l u) at 1. change 0 with (0 * 2^32) at 1.
    rewrite smear32w_val by lia. rewrite (smear32_val u s) by lia.
    assert (s <> 31). { intros ->. change (2^31) with (2^31) in Hu. lia. }
    assert (2^(s+1) <= 2^31) by (apply Z.pow_le_mono_r; lia).
    rewrite not64_val by lia.
    replace (2 ^ 64 - 1 - (0 * 2 ^ 32 + (2 ^ (s + 1) - 1))) with (2^64 - 2^(Z.of_nat (Z.to_nat s) + 1)) by (rewrite Z2Nat.id; lia).
    rewrite pop32_cases by lia. lia.
  - rewrite sext32_big by lia. replace (2 ^ 64 - 2 ^ 32 + u) with ((2^32 - 1) * 2^32 + u) by lia.
    rewrite smear32w_val by lia.
    assert (s = 31). { destruct (Z.eq_dec s 31); [lia|]. exfalso. assert (2^(s+1) <= 2^31) by (apply Z.pow_le_mono_r; lia). lia. }
    subst s. rewrite (smear32_val u 31) by lia. rewrite not64_val by lia.
    replace (2 ^ 64 - 1 - ((2 ^ 32 - 1) * 2 ^ 32 + (2 ^ (31 + 1) - 1))) with 0 by lia. rewrite pop32_0. reflexivity.
Qed.

Lemma shl64_val : forall x n, 0 <= n -> shl64 x n = (x * 2^n) mod 2^64.
Proof. intros. unfold shl64. rewrite wrap64_mod, shiftl_mul by lia. reflexivity. Qed.
Lemma shl64_small : forall x n, 0 <= n -> 0 <= x -> x * 2^n < 2^64 -> shl64 x n = x * 2^n.
Proof. intros. rewrite shl64_val by lia. apply Z.mod_small. nia. Qed.
Lemma add64_val : forall x y, add64 x y = (x + y) mod 2^64.
Proof. intros. unfold add64. apply wrap64_mod. Qed.
Lemma add64_small : forall x y, 0 <= x + y < 2^64 -> add64 x y = x + y.
Proof. intros. rewrite add64_val. apply Z.mod_small. lia. Qed.
Lemma sub64_val : forall x y, sub64 x y = (x - y) mod 2^64.
Proof. intros. unfold sub64. apply wrap64_mod. Qed.
Lemma sub64_small : forall x y, 0 <= x - y < 2^64 -> sub64 x y = x - y.
Proof. intros. rewrite sub64_val. apply Z.mod_small. lia. Qed.
Lemma sub64_neg : forall x y, - 2^64 <= x - y < 0 -> sub64 x y = x - y + 2^64.
Proof.
  intros. rewrite sub64_val. replace (x - y) with ((x - y + 2^64) + (-1) * 2^64) at 1 by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma mul64_val : forall x y, mul64 x y = (x * y) mod 2^64.
Proof. intros. unfold mul64. apply wrap64_mod. Qed.
Lemma mul64_small : forall x y, 0 <= x -> 0 <= y -> x * y < 2^64 -> mul64 x y = x * y.
Proof. intros. rewrite mul64_val. apply Z.mod_small. nia. Qed.
Lemma is_neg64_val : forall x, 0 <= x < 2^64 -> is_neg64 x = (2^63 <=? x).
Proof.
  intros x Hx. unfold is_neg64. rewrite shiftr_div by lia.
  destruct (Z.leb_spec (2^63) x).
  - assert (E : x / 2^63 = 1) by (symmetry; apply Z.div_unique with (r := x - 2^63); lia). rewrite E. reflexivity.
  - rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma land63 : forall x, Z.land x 63 = x mod 64.
Proof. intros. change 63 with (2^6 - 1). rewrite land_ones_mod by lia. reflexivity. Qed.
Lemma land_m32 : forall x, Z.land x M32 = x mod 2^32.
Proof. intros. rewrite m32_eq. apply land_ones_mod. lia. Qed.
Lemma land_mask48 : forall x, Z.land x MASK48 = x mod 2^48.
Proof. intros. rewrite mask48_eq. apply land_ones_mod. lia. Qed.
Lemma land_abs : forall x, Z.land x ABS_HI = x mod 2^63.
Proof. intros. rewrite abs_hi_eq. apply land_ones_mod. lia. Qed.
Lemma zext32_val : forall x, zext32 x = x mod 2^32.
Proof. intros. unfold zext32. apply land_m32. Qed.
Lemma b2z_val : forall b, b2z b = if b then 1 else 0. Proof. reflexivity. Qed.
Lemma smask64_val : forall x, 0 <= x < 2^64 -> sra63 x = if 2^63 <=? x then ONES64 else 0.
Proof. intros. unfold sra63. rewrite is_neg64_val by lia. reflexivity. Qed.

Lemma testbit_true_iff : forall x k, 0 <= k -> Z.testbit x k = true <-> (x / 2^k) mod 2 = 1.
Proof. intros. apply Z.testbit_true. lia. Qed.
Lemma testbit_false_iff : forall x k, 0 <= k -> Z.testbit x k = false <-> (x / 2^k) mod 2 = 0.
Proof. intros. apply Z.testbit_false. lia. Qed.

Lemma lxor_bit_clear : forall y k, 0 <= k -> 0 <= y -> (y / 2^k) mod 2 = 0 -> Z.lxor y (2^k) = y + 2^k.
Proof.
  intros y k Hk Hy Hb. rewrite <- Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec n k) as [->|].
  - rewrite (proj2 (testbit_false_iff y k Hk) Hb). reflexivity.
  - rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r.
Qed.

Lemma lxor_bit_set : forall x k, 0 <= k -> 2^k <= x -> (x / 2^k) mod 2 = 1 -> Z.lxor x (2^k) = x - 2^k.
Proof.
  intros x k Hk Hx Hb.
  assert (E : Z.lxor (x - 2^k) (2^k) = x).
  { rewrite lxor_bit_clear; try lia.
    replace (x - 2^k) with (x + (-1) * 2^k) by lia. rewrite Z.div_add by lia.
    replace (x / 2^k + -1) with (x / 2^k - 1) by lia. rewrite Zminus_mod, Hb. reflexivity. }
  rewrite <- E at 1. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity.
Qed.

Definition f128_pack (s E T : Z) : Z := s * 2^127 + E * 2^112 + T.

Record packed (s E T : Z) : Prop :=
  { pk_s : 0 <= s <= 1; pk_E : 0 <= E <= 32767; pk_T : 0 <= T < 2^112 }.

Lemma f128_pack_range : forall s E T, packed s E T -> 0 <= f128_pack s E T < 2^128.
Proof. intros s E T [Hs HE HT]. unfold f128_pack. lia. Qed.

Lemma f128_pack_hi : forall s E T, packed s E T ->
  hi64 (f128_pack s E T) = s * 2^63 + E * 2^48 + T / 2^64.
Proof.
  intros s E T [Hs HE HT]. unfold f128_pack.
  replace (s * 2 ^ 127 + E * 2 ^ 112 + T) with ((s * 2^63 + E * 2^48 + T / 2^64) * 2^64 + T mod 2^64).
  2:{ pose proof (Z.div_mod T (2^64) ltac:(lia)). lia. }
  apply hi64_val; [| apply Z.mod_pos_bound; lia].
  pose proof (Z.div_lt_upper_bound T (2^64) (2^48) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos T (2^64)). lia.
Qed.

Lemma f128_pack_lo : forall s E T, packed s E T -> lo64 (f128_pack s E T) = T mod 2^64.
Proof.
  intros s E T [Hs HE HT]. unfold f128_pack.
  replace (s * 2 ^ 127 + E * 2 ^ 112 + T) with ((s * 2^63 + E * 2^48 + T / 2^64) * 2^64 + T mod 2^64).
  2:{ pose proof (Z.div_mod T (2^64) ltac:(lia)). lia. }
  apply lo64_val. apply Z.mod_pos_bound; lia.
Qed.

Lemma hiword_exp : forall s E th, 0 <= s <= 1 -> 0 <= E <= 32767 -> 0 <= th < 2^48 ->
  Z.shiftr (shl64 (s * 2^63 + E * 2^48 + th) 1) 49 = E.
Proof.
  intros. rewrite shl64_val, shiftr_div by lia.
  replace ((s * 2 ^ 63 + E * 2 ^ 48 + th) * 2 ^ 1) with ((E * 2^49 + th * 2) + s * 2^64) by lia.
  rewrite Z_mod_plus_full, Z.mod_small by lia.
  symmetry. apply Z.div_unique with (r := th * 2); lia.
Qed.
Lemma hiword_frac : forall s E th, 0 <= s <= 1 -> 0 <= E <= 32767 -> 0 <= th < 2^48 ->
  Z.land (s * 2^63 + E * 2^48 + th) MASK48 = th.
Proof.
  intros. rewrite land_mask48. replace (s * 2 ^ 63 + E * 2 ^ 48 + th) with (th + (s * 2^15 + E) * 2^48) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma hiword_sign : forall s E th, 0 <= s <= 1 -> 0 <= E <= 32767 -> 0 <= th < 2^48 ->
  Z.shiftr (s * 2^63 + E * 2^48 + th) 63 = s.
Proof.
  intros. rewrite shiftr_div by lia. symmetry. apply Z.div_unique with (r := E * 2^48 + th); lia.
Qed.
Lemma hiword_abs : forall s E th, 0 <= s <= 1 -> 0 <= E <= 32767 -> 0 <= th < 2^48 ->
  Z.land (s * 2^63 + E * 2^48 + th) ABS_HI = E * 2^48 + th.
Proof.
  intros. rewrite land_abs. replace (s * 2 ^ 63 + E * 2 ^ 48 + th) with ((E * 2^48 + th) + s * 2^63) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma hiword_expfield : forall s E th, 0 <= s <= 1 -> 0 <= E <= 32767 -> 0 <= th < 2^48 ->
  Z.land (Z.shiftr (s * 2^63 + E * 2^48 + th) 48) 32767 = E.
Proof.
  intros. rewrite shiftr_div by lia. change 32767 with (2^15 - 1). rewrite land_ones_mod by lia.
  replace ((s * 2 ^ 63 + E * 2 ^ 48 + th) / 2^48) with (E + s * 2^15).
  2:{ apply Z.div_unique with (r := th); lia. }
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma T_split : forall T, 0 <= T < 2^112 -> 0 <= T / 2^64 < 2^48 /\ 0 <= T mod 2^64 < 2^64 /\ T = (T / 2^64) * 2^64 + T mod 2^64.
Proof.
  intros T HT. split; [split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]|].
  split; [apply Z.mod_pos_bound; lia|]. pose proof (Z.div_mod T (2^64)); lia.
Qed.

Section Dword.
  Variables sd Ed Td : Z.
  Hypothesis Hsd : 0 <= sd <= 1.
  Hypothesis HEd : 0 <= Ed <= 2047.
  Hypothesis HTd : 0 <= Td < 2^52.
  Let D := sd * 2^63 + Ed * 2^52 + Td.

  Lemma dword_range : 0 <= D < 2^64. Proof. subst D. lia. Qed.
  Lemma dword_lo64 : lo64 D = D. Proof. unfold lo64. apply wrap64_id. apply dword_range. Qed.
  Lemma dword_exp : Z.shiftr (shl64 D 1) 53 = Ed.
  Proof.
    subst D. rewrite shl64_val, shiftr_div by lia.
    replace ((sd * 2 ^ 63 + Ed * 2 ^ 52 + Td) * 2 ^ 1) with ((Ed * 2^53 + Td * 2) + sd * 2^64) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by lia. symmetry. apply Z.div_unique with (r := Td * 2); lia.
  Qed.
  Lemma dword_sig : Z.shiftr (shl64 D 12) 12 = Td.
  Proof.
    subst D. rewrite shl64_val, shiftr_div by lia.
    replace ((sd * 2 ^ 63 + Ed * 2 ^ 52 + Td) * 2 ^ 12) with (Td * 2^12 + (sd * 2^11 + Ed) * 2^64) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by lia. symmetry. apply Z.div_unique with (r := 0); lia.
  Qed.
  Lemma dword_sign : shl64 (Z.shiftr D 63) 63 = sd * 2^63.
  Proof.
    subst D. rewrite shiftr_div by lia.
    replace ((sd * 2 ^ 63 + Ed * 2 ^ 52 + Td) / 2 ^ 63) with sd.
    2:{ apply Z.div_unique with (r := Ed * 2^52 + Td); lia. }
    apply shl64_small; lia.
  Qed.
End Dword.

Lemma f128_of_d_normal : forall sd Ed Td, 0 <= sd <= 1 -> 1 <= Ed <= 2046 -> 0 <= Td < 2^52 ->
  f128_of_d (sd * 2^63 + Ed * 2^52 + Td) = f128_pack sd (Ed + 15360) (Td * 2^60).
Proof.
  intros sd Ed Td Hsd HEd HTd. unfold f128_of_d.
  rewrite dword_lo64 by lia. rewrite dword_exp, dword_sig, dword_sign by lia. cbv zeta.
  replace (negb (Ed =? 0)) with true by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; lia).
  replace (negb (Ed =? 2047)) with true by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; lia).
  rewrite add64_small by lia. change 0x3c00 with 15360.
  rewrite (shl64_small (Ed + 15360) 48) by lia. rewrite shiftr_div by lia.
  rewrite (lor_high_low (Ed + 15360) (Td / 2^4) 48); [|lia|lia|].
  2:{ split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  rewrite lor_low_high; [|lia|lia|].
  2:{ pose proof (Z.div_lt_upper_bound Td (2^4) (2^48) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos Td (2^4)). lia. }
  rewrite shl64_val by lia.
  rewrite mk128_val; [| pose proof (Z.div_pos Td (2^4)); lia | apply Z.mod_pos_bound; lia].
  unfold f128_pack.
  pose proof (Z.div_mod Td (2^4) ltac:(lia)).
  pose proof (Z.mod_pos_bound Td (2^4) ltac:(lia)).
  replace ((Td * 2^60) mod 2^64) with ((Td mod 2^4) * 2^60).
  2:{ rewrite H at 2. replace ((2 ^ 4 * (Td / 2 ^ 4) + Td mod 2 ^ 4) * 2 ^ 60) with ((Td mod 2^4) * 2^60 + (Td / 2^4) * 2^64) by lia.
      rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
  lia.
Qed.

Lemma f128_of_d_infnan : forall sd Td, 0 <= sd <= 1 -> 0 <= Td < 2^52 ->
  f128_of_d (sd * 2^63 + 2047 * 2^52 + Td) = f128_pack sd 32767 (Td * 2^60).
Proof.
  intros sd Td Hsd HTd. unfold f128_of_d.
  rewrite dword_lo64 by lia. rewrite dword_exp, dword_sig, dword_sign by lia. cbv zeta.
  change (negb (2047 =? 0)) with true. change (negb (2047 =? 2047)) with false. cbv iota.
  rewrite shiftr_div by lia. rewrite inf_hi_eq.
  rewrite (lor_high_low 32767 (Td / 2^4) 48); [|lia|lia|].
  2:{ split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  rewrite lor_low_high; [|lia|lia|].
  2:{ pose proof (Z.div_lt_upper_bound Td (2^4) (2^48) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos Td (2^4)). lia. }
  rewrite shl64_val by lia.
  rewrite mk128_val; [| pose proof (Z.div_pos Td (2^4)); lia | apply Z.mod_pos_bound; lia].
  unfold f128_pack.
  pose proof (Z.div_mod Td (2^4) ltac:(lia)).
  pose proof (Z.mod_pos_bound Td (2^4) ltac:(lia)).
  replace ((Td * 2^60) mod 2^64) with ((Td mod 2^4) * 2^60).
  2:{ rewrite H at 2. replace ((2 ^ 4 * (Td / 2 ^ 4) + Td mod 2 ^ 4) * 2 ^ 60) with ((Td mod 2^4) * 2^60 + (Td / 2^4) * 2^64) by lia.
      rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
  lia.
Qed.

Lemma f128_of_d_zero : forall sd, 0 <= sd <= 1 -> f128_of_d (sd * 2^63) = f128_pack sd 0 0.
Proof.
  intros sd Hsd. unfold f128_of_d.
  replace (sd * 2^63) with (sd * 2^63 + 0 * 2^52 + 0) by lia.
  rewrite dword_lo64 by lia. rewrite dword_exp, dword_sig, dword_sign by lia. cbv zeta.
  cbn [Z.eqb negb]. rewrite (shl64_small 0 48) by lia. rewrite !Z.lor_0_l.
  rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.

Lemma pow2_split : forall a b, 0 <= a -> 0 <= b -> 2^(a + b) = 2^a * 2^b.
Proof. intros. apply Z.pow_add_r; lia. Qed.

Lemma f128_of_d_subnormal : forall sd Td L, 0 <= sd <= 1 -> 0 <= L <= 51 -> 2^L <= Td < 2^(L+1) ->
  f128_of_d (sd * 2^63 + Td) = f128_pack sd (15309 + L) (Td * 2^(112 - L) - 2^112).
Proof.
  intros sd Td L Hsd HL HTd.
  assert (T52 : Td < 2^52). { eapply Z.lt_le_trans; [apply (proj2 HTd)|]. apply Z.pow_le_mono_r; lia. }
  assert (Tpos : 0 < Td). { pose proof (pow2_ge1 L ltac:(lia)). lia. }
  unfold f128_of_d.
  replace (sd * 2^63 + Td) with (sd * 2^63 + 0 * 2^52 + Td) by lia.
  rewrite dword_lo64 by lia. rewrite dword_exp, dword_sig, dword_sign by lia. cbv zeta.
  change (negb (0 =? 0)) with false. cbv iota.
  replace (Td =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (clz64_mirror_val Td L) by lia.
  change 0x3c0c with 15372. rewrite (sub64_small 15372) by lia.
  replace (15372 - (63 - L)) with (15309 + L) by lia.
  rewrite (shl64_small (15309 + L) 48) by lia.
  rewrite implicit_hi_eq.
  destruct (Z.le_gt_cases L 48) as [LA|LB].
  -
    rewrite (sub64_small (63 - L) 15) by lia.
    rewrite is_neg64_val by lia.
    replace (2 ^ 63 <=? 63 - L - 15) with false by (symmetry; apply Z.leb_gt; lia). cbn [negb].
    rewrite land63. rewrite (Z.mod_small (63 - L - 15) 64) by lia.
    replace (63 - L - 15) with (48 - L) by lia.
    assert (P1 : 2^(48 - L) * 2^(L + 1) = 2^49) by (rewrite <- pow2_split by lia; f_equal; lia).
    assert (P0 : 2^(48 - L) * 2^L = 2^48) by (rewrite <- pow2_split by lia; f_equal; lia).
    assert (Ppos : 0 < 2^(48 - L)) by (apply Z.pow_pos_nonneg; lia).
    assert (HB : 2^48 <= Td * 2^(48 - L) < 2^49) by nia.
    rewrite (shl64_small Td (48 - L)) by lia.
    rewrite smask64_val by lia.
    replace (2 ^ 63 <=? 48 - L) with false by (symmetry; apply Z.leb_gt; lia). rewrite Z.land_0_l.
    rewrite lxor_bit_set; [|lia|lia|].
    2:{ replace (Td * 2 ^ (48 - L) / 2 ^ 48) with 1; [reflexivity|]. apply Z.div_unique with (r := Td * 2^(48-L) - 2^48); lia. }
    rewrite (lor_high_low (15309 + L) (Td * 2 ^ (48 - L) - 2 ^ 48) 48) by lia.
    rewrite lor_low_high by lia.
    rewrite mk128_val by lia. unfold f128_pack.
    assert (P2 : 2^(112 - L) = 2^(48 - L) * 2^64) by (rewrite <- pow2_split by lia; f_equal; lia).
    rewrite P2. nia.
  -
    rewrite (sub64_neg (63 - L) 15) by lia.
    rewrite is_neg64_val by lia.
    replace (2 ^ 63 <=? 63 - L - 15 + 2 ^ 64) with true by (symmetry; apply Z.leb_le; lia). cbn [negb].
    rewrite (sub64_small 14) by lia. rewrite sext32_small by lia. rewrite land63, (Z.mod_small (14 - (63 - L))) by lia.
    rewrite smask64_val by lia.
    replace (2 ^ 63 <=? 63 - L - 15 + 2 ^ 64) with true by (symmetry; apply Z.leb_le; lia).
    rewrite (add64_small (63 - L) 49) by lia. rewrite land63, (Z.mod_small (63 - L + 49)) by lia.
    rewrite ones64_eq, Z.land_comm, land_ones_mod by lia.
    rewrite !shiftr_div by lia. rewrite shl64_val by lia. rewrite Z.mod_mod by lia.
    replace (14 - (63 - L)) with (L - 49) by lia. replace (63 - L + 49) with (112 - L) by lia.
    assert (HL3 : L = 49 \/ L = 50 \/ L = 51) by lia.
    destruct HL3 as [-> | [-> | ->]].
    + change (2^(49-49)) with 1. change (2^(112-49)) with (2^63). change (2^(49+1)) with (2^50) in HTd. change (2^49) with 562949953421312 in *.
      rewrite Z.div_1_r. change (2^1) with 2.
      rewrite lxor_bit_set by dlia.
      rewrite (lor_high_low (15309 + 49) _ 48) by dlia. rewrite lor_low_high by dlia.
      rewrite mk128_val by dlia. unfold f128_pack. dlia.
    + change (2^(50-49)) with 2. change (2^(112-50)) with (2^62). change (2^(50+1)) with (2^51) in HTd. change (2^50) with 1125899906842624 in *.
      change (2^1) with 2.
      rewrite lxor_bit_set by dlia.
      rewrite (lor_high_low (15309 + 50) _ 48) by dlia. rewrite lor_low_high by dlia.
      rewrite mk128_val by dlia. unfold f128_pack. dlia.
    + change (2^(51-49)) with 4. change (2^(112-51)) with (2^61). change (2^(51+1)) with (2^52) in HTd. change (2^51) with 2251799813685248 in *.
      change (2^1) with 2.
      rewrite lxor_bit_set by dlia.
      rewrite (lor_high_low (15309 + 51) _ 48) by dlia. rewrite lor_low_high by dlia.
      rewrite mk128_val by dlia. unfold f128_pack. dlia.
Qed.

Lemma lor_eq0_iff : forall a b, 0 <= a -> 0 <= b -> Z.lor a b = 0 <-> a = 0 /\ b = 0.
Proof.
  intros a b Ha Hb. split.
  - intros H. apply Z.lor_eq_0_iff in H. exact H.
  - intros [-> ->]. reflexivity.
Qed.

Lemma lor_eqb0 : forall a b, 0 <= a -> 0 <= b -> (Z.lor a b =? 0) = ((a =? 0) && (b =? 0)).
Proof.
  intros a b Ha Hb. destruct (Z.eqb_spec (Z.lor a b) 0) as [E|NE].
  - apply (lor_eq0_iff a b Ha Hb) in E. destruct E as [-> ->]. reflexivity.
  - symmetry. apply Bool.andb_false_iff.
    destruct (Z.eqb_spec a 0) as [->|]; [|left; reflexivity]. right. apply Z.eqb_neq. intros ->. apply NE. reflexivity.
Qed.

Lemma lt_s64_val : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  lt_s64 a b = ((if 2^63 <=? a then a - 2^64 else a) <? (if 2^63 <=? b then b - 2^64 else b)).
Proof.
  intros a b Ha Hb. unfold lt_s64. rewrite sign64_eq.
  assert (X : forall x, 0 <= x < 2^64 -> Z.lxor x (2^63) = if 2^63 <=? x then x - 2^63 else x + 2^63).
  { intros x Hx. destruct (Z.leb_spec (2^63) x).
    - apply lxor_bit_set; [lia|lia|]. replace (x / 2^63) with 1; [reflexivity|]. apply Z.div_unique with (r := x - 2^63); lia.
    - apply lxor_bit_clear; [lia|lia|]. rewrite Z.div_small by lia. reflexivity. }
  rewrite !X by lia.
  destruct (Z.leb_spec (2^63) a); destruct (Z.leb_spec (2^63) b);
    apply Bool.eq_true_iff_eq; rewrite !Z.ltb_lt; lia.
Qed.

Lemma f128_le_zero_zero : forall s, 0 <= s <= 1 -> f128_le (f128_pack s 0 0) 0 = 0.
Proof.
  intros s Hs. unfold f128_le.
  rewrite f128_pack_hi, f128_pack_lo by (constructor; lia).
  change (lo64 0) with 0. change (hi64 0) with 0.
  change (0 / 2^64) with 0. change (0 mod 2^64) with 0.
  rewrite (hiword_abs s 0 0) by lia. change (0 * 2^48 + 0) with 0.
  rewrite inf_hi_eq. cbn -[Z.add Z.mul Z.pow]. reflexivity.
Qed.

Lemma f128_le_pos_zero : forall E T, packed 0 E T -> E <= 32766 -> (E <> 0 \/ T <> 0) ->
  f128_le (f128_pack 0 E T) 0 = 1.
Proof.
  intros E T PK HE NZ. destruct PK as [_ HE' HT].
  pose proof (T_split T HT) as (Hth & Htl & ET).
  unfold f128_le.
  rewrite f128_pack_hi, f128_pack_lo by (constructor; lia).
  change (lo64 0) with 0. change (hi64 0) with 0.
  rewrite (hiword_abs 0 E (T / 2^64)) by lia.
  change (Z.land 0 ABS_HI) with 0.
  change (if 0 =? INF_HI then negb (0 =? 0) else INF_HI <? 0) with false.
  rewrite inf_hi_eq.
  replace (E * 2 ^ 48 + T / 2 ^ 64 =? 32767 * 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (32767 * 2 ^ 48 <? E * 2 ^ 48 + T / 2 ^ 64) with false by (symmetry; apply Z.ltb_ge; lia).
  cbv iota.
  rewrite !Z.lor_0_l. rewrite lor_eqb0 by lia.
  replace ((T mod 2 ^ 64 =? 0) && (E * 2 ^ 48 + T / 2 ^ 64 =? 0)) with false.
  2:{ symmetry. apply Bool.andb_false_iff. destruct (Z.eq_dec (T mod 2^64) 0); [right| left]; apply Z.eqb_neq; lia. }
  rewrite Z.land_0_l. change (negb (is_neg64 0)) with true.
  rewrite !Z.lxor_0_r.
  destruct (Z.eqb_spec (0 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64) 0) as [E0|E0].
  - replace (T mod 2^64 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold nez64. rewrite b2z_val, lor_eqb0 by lia.
    replace (T mod 2^64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - rewrite lt_s64_val by lia.
    replace (2 ^ 63 <=? 0 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64) with false by (symmetry; apply Z.leb_gt; lia).
    change (2^63 <=? 0) with false.
    cbv iota.
    replace (0 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold nez64. rewrite b2z_val, lor_eqb0 by lia.
    replace (0 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma f128_le_neg_zero : forall E T, packed 1 E T -> E <= 32766 -> (E <> 0 \/ T <> 0) ->
  f128_le (f128_pack 1 E T) 0 = -1.
Proof.
  intros E T PK HE NZ. destruct PK as [_ HE' HT].
  pose proof (T_split T HT) as (Hth & Htl & ET).
  unfold f128_le.
  rewrite f128_pack_hi, f128_pack_lo by (constructor; lia).
  change (lo64 0) with 0. change (hi64 0) with 0.
  rewrite (hiword_abs 1 E (T / 2^64)) by lia.
  change (Z.land 0 ABS_HI) with 0.
  change (if 0 =? INF_HI then negb (0 =? 0) else INF_HI <? 0) with false.
  rewrite inf_hi_eq.
  replace (E * 2 ^ 48 + T / 2 ^ 64 =? 32767 * 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (32767 * 2 ^ 48 <? E * 2 ^ 48 + T / 2 ^ 64) with false by (symmetry; apply Z.ltb_ge; lia).
  cbv iota.
  rewrite !Z.lor_0_l. rewrite lor_eqb0 by lia.
  replace ((T mod 2 ^ 64 =? 0) && (E * 2 ^ 48 + T / 2 ^ 64 =? 0)) with false.
  2:{ symmetry. apply Bool.andb_false_iff. destruct (Z.eq_dec (T mod 2^64) 0); [right| left]; apply Z.eqb_neq; lia. }
  rewrite Z.land_0_l. change (negb (is_neg64 0)) with true.
  replace (1 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv iota.
  rewrite lt_s64_val by lia.
  replace (2 ^ 63 <=? 1 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64) with true by (symmetry; apply Z.leb_le; lia).
  change (2^63 <=? 0) with false. cbv iota.
  replace (1 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64 - 2^64 <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma hiword_frac16 : forall s E th, 0 <= s <= 1 -> 0 <= E <= 32767 -> 0 <= th < 2^48 ->
  Z.shiftr (shl64 (s * 2^63 + E * 2^48 + th) 16) 16 = th.
Proof.
  intros. rewrite shl64_val, shiftr_div by lia.
  replace ((s * 2 ^ 63 + E * 2 ^ 48 + th) * 2 ^ 16) with (th * 2^16 + (s * 2^15 + E) * 2^64) by lia.
  rewrite Z_mod_plus_full, Z.mod_small by lia. symmetry. apply Z.div_unique with (r := 0); lia.
Qed.

Lemma f128_to_u32_small : forall s E T, packed s E T -> E < 16383 -> f128_to_u32 (f128_pack s E T) = 0.
Proof.
  intros s E T PK HE. destruct PK as [Hs HE' HT]. pose proof (T_split T HT) as (Hth & Htl & ET).
  unfold f128_to_u32, fixunstfsi_a0, fixunstfsi_a2.
  rewrite f128_pack_hi, f128_pack_lo by (constructor; lia).
  rewrite hiword_exp by lia.
  replace (E <? 0x3fff) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (is_neg64 _); reflexivity.
Qed.

Lemma f128_to_u32_val : forall E T, packed 0 E T -> 16383 <= E <= 16414 ->
  f128_to_u32 (f128_pack 0 E T) = (2^112 + T) / 2^(16495 - E).
Proof.
  intros E T PK HE. destruct PK as [_ HE' HT]. pose proof (T_split T HT) as (Hth & Htl & ET).
  unfold f128_to_u32, fixunstfsi_a0, fixunstfsi_a2.
  rewrite f128_pack_hi, f128_pack_lo by (constructor; lia).
  rewrite is_neg64_val by lia.
  replace (2 ^ 63 <=? 0 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite hiword_exp by lia.
  replace (E <? 0x3fff) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite add64_val. change 0xffffffffffffbfe1 with (2^64 - 16415).
  replace ((E + (2 ^ 64 - 16415)) mod 2 ^ 64) with (E + (2^64 - 16415)) by (symmetry; apply Z.mod_small; lia).
  replace (0xffffffffffffffe0 <=? E + (2 ^ 64 - 16415)) with true by (symmetry; apply Z.leb_le; lia). cbn [negb].
  rewrite hiword_frac16 by lia. rewrite implicit_hi_eq.
  replace (2^48) with (1 * 2^48) at 1 by lia. rewrite lor_low_high by lia.
  change 0x406f with 16495. rewrite (sub64_small 16495 E) by lia. rewrite (sext32_small (16495 - E)) by lia.
  rewrite zext32_val, (Z.mod_small (16495 - E)) by lia.
  rewrite (sub64_small (16495 - E) 64) by lia. rewrite is_neg64_val by lia.
  replace (2 ^ 63 <=? 16495 - E - 64) with false by (symmetry; apply Z.leb_gt; lia). cbn [negb].
  rewrite land63. replace ((16495 - E) mod 64) with (16495 - E - 64) by (apply Z.mod_unique with (q := 1); lia).
  rewrite shiftr_div by lia.
  assert (PP : 0 < 2 ^ (16495 - E - 64)) by (apply Z.pow_pos_nonneg; lia).
  assert (R : 0 <= (1 * 2 ^ 48 + T / 2 ^ 64) / 2 ^ (16495 - E - 64) < 2^32).
  { split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|].
    assert (2^17 <= 2^(16495 - E - 64)) by (apply Z.pow_le_mono_r; lia). nia. }
  rewrite land_m32.
  assert (EQ : (1 * 2 ^ 48 + T / 2 ^ 64) / 2 ^ (16495 - E - 64) = (2 ^ 112 + T) / 2 ^ (16495 - E)).
  { rewrite ET at 2. replace (16495 - E) with (64 + (16495 - E - 64)) at 2 by lia.
    rewrite pow2_split by lia. rewrite <- Z.div_div by lia.
    f_equal. apply Z.div_unique with (r := T mod 2^64); lia. }
  rewrite <- EQ.
  destruct (Z.lt_ge_cases ((1 * 2 ^ 48 + T / 2 ^ 64) / 2 ^ (16495 - E - 64)) (2^31)).
  - rewrite sext32_small by lia. apply Z.mod_small. lia.
  - rewrite sext32_big by lia.
    replace (2 ^ 64 - 2 ^ 32 + (1 * 2 ^ 48 + T / 2 ^ 64) / 2 ^ (16495 - E - 64))
      with ((1 * 2 ^ 48 + T / 2 ^ 64) / 2 ^ (16495 - E - 64) + (2^32 - 1) * 2^32) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma lxor_31 : forall c, 0 <= c <= 31 -> Z.lxor c 31 = 31 - c.
Proof.
  intros c Hc. rewrite <- (Z2Nat.id c) by lia.
  assert (L : (Z.to_nat c < 32)%nat) by lia. revert L. generalize (Z.to_nat c) as n. intros n L.
  do 32 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma sext32_u_nonzero : forall u, 0 < u < 2^32 -> (sext32 u =? 0) = false.
Proof.
  intros u Hu. apply Z.eqb_neq. destruct (Z.lt_ge_cases u (2^31)).
  - rewrite sext32_small; lia. - rewrite sext32_big; lia.
Qed.

Lemma sext32_hw : forall u, 0 <= u < 2^32 -> exists h, 0 <= h /\ sext32 u = h * 2^32 + u.
Proof.
  intros u Hu. destruct (Z.lt_ge_cases u (2^31)).
  - exists 0. rewrite sext32_small; lia.
  - exists (2^32 - 1). rewrite sext32_big; lia.
Qed.

Lemma f128_of_u32_zero : f128_of_u32 0 = f128_pack 0 0 0.
Proof. reflexivity. Qed.

Lemma f128_of_u32_val : forall u L, 0 <= L <= 31 -> 2^L <= u < 2^(L+1) ->
  f128_of_u32 u = f128_pack 0 (16383 + L) (u * 2^(112 - L) - 2^112).
Proof.
  intros u L HL Hu.
  assert (U32 : u < 2^32). { eapply Z.lt_le_trans; [apply (proj2 Hu)|]. apply Z.pow_le_mono_r; lia. }
  assert (Upos : 0 < u). { pose proof (pow2_ge1 L ltac:(lia)). lia. }
  unfold f128_of_u32.
  rewrite sext32_u_nonzero by lia.
  rewrite (clz32_mirror_val u L) by lia.
  rewrite (zext32_sext32 u) by lia.
  rewrite lxor_31 by lia. replace (31 - (31 - L)) with L by lia.
  rewrite (sub64_small 112 L) by lia. rewrite (sext32_small (112 - L)) by lia.
  rewrite zext32_val, (Z.mod_small (112 - L)) by lia.
  rewrite (sub64_small (112 - L) 64) by lia.
  rewrite is_neg64_val by lia.
  replace (2 ^ 63 <=? 112 - L - 64) with false by (symmetry; apply Z.leb_gt; lia). cbn [negb].
  rewrite land63. replace ((112 - L) mod 64) with (48 - L) by (apply Z.mod_unique with (q := 1); lia).
  assert (P1 : 2^(48 - L) * 2^(L + 1) = 2^49) by (rewrite <- pow2_split by lia; f_equal; lia).
  assert (P0 : 2^(48 - L) * 2^L = 2^48) by (rewrite <- pow2_split by lia; f_equal; lia).
  assert (Ppos : 0 < 2^(48 - L)) by (apply Z.pow_pos_nonneg; lia).
  assert (HB : 2^48 <= u * 2^(48 - L) < 2^49) by nia.
  rewrite (shl64_small u (48 - L)) by lia.
  rewrite smask64_val by lia.
  replace (2 ^ 63 <=? 112 - L - 64) with false by (symmetry; apply Z.leb_gt; lia). rewrite Z.land_0_l.
  rewrite implicit_hi_eq. rewrite lxor_bit_set; [|lia|lia|].
  2:{ replace (u * 2 ^ (48 - L) / 2 ^ 48) with 1; [reflexivity|]. apply Z.div_unique with (r := u * 2^(48-L) - 2^48); lia. }
  rewrite (sub64_small 16414) by lia. rewrite sext32_small by lia.
  replace (16414 - (31 - L)) with (16383 + L) by lia.
  rewrite (shl64_small (16383 + L) 48) by lia.
  rewrite add64_small by lia.
  rewrite mk128_val by lia. unfold f128_pack.
  assert (P2 : 2^(112 - L) = 2^(48 - L) * 2^64) by (rewrite <- pow2_split by lia; f_equal; lia).
  rewrite P2. nia.
Qed.

Lemma lxor_eqb0 : forall a b, (Z.lxor a b =? 0) = (a =? b).
Proof.
  intros a b. destruct (Z.eqb_spec a b) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.eqb_neq. intros H. apply Z.lxor_eq in H. exact (NE H).
Qed.
