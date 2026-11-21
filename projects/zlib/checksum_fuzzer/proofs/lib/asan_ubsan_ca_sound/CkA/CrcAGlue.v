(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.cks Require Import CkTables CkModel CkXt CkMultmodp CkMathCrc.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Lemma swrap32_eq : forall x, bv_swrap 32 x = (x + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.

Lemma wrap32_eq : forall x, bv_wrap 32 x = x mod 2^32.
Proof. reflexivity. Qed.

Lemma swrap32_range : forall x, -2^31 <= bv_swrap 32 x < 2^31.
Proof. intros x. rewrite swrap32_eq. pose proof (Z.mod_pos_bound (x + 2^31) (2^32) ltac:(lia)). lia. Qed.

Lemma swrap32_mod32 : forall x, (bv_swrap 32 x) mod 2^32 = x mod 2^32.
Proof. intros x. rewrite swrap32_eq. Z.div_mod_to_equations. lia. Qed.

Lemma swrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x H. rewrite swrap32_eq. Z.div_mod_to_equations. lia. Qed.

Lemma mod64_mod32 : forall x, (x mod 2^64) mod 2^32 = x mod 2^32.
Proof. intros x. Z.div_mod_to_equations. lia. Qed.

Lemma swrap32_mod64_mod32 : forall x, ((bv_swrap 32 x) mod 2^64) mod 2^32 = x mod 2^32.
Proof. intros x. rewrite mod64_mod32. apply swrap32_mod32. Qed.

Lemma swrap32_mod64_zero : forall x, (bv_swrap 32 x) mod 2^64 = 0 <-> x mod 2^32 = 0.
Proof.
  intros x. pose proof (swrap32_range x) as R. pose proof (swrap32_mod32 x) as E.
  split; intros H.
  - rewrite <- E. assert (bv_swrap 32 x = 0) by (Z.div_mod_to_equations; lia). rewrite H0. reflexivity.
  - assert (bv_swrap 32 x = 0) by (Z.div_mod_to_equations; lia). rewrite H0. reflexivity.
Qed.

Lemma mod32_land : forall a, a mod 2^32 = Z.land a (Z.ones 32).
Proof. intros a. rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_mod32 : forall a b, (Z.land a b) mod 2^32 = Z.land (a mod 2^32) (b mod 2^32).
Proof.
  intros a b. rewrite !mod32_land. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit (Z.ones 32) n); reflexivity.
Qed.

Lemma lxor_mod32 : forall a b, (Z.lxor a b) mod 2^32 = Z.lxor (a mod 2^32) (b mod 2^32).
Proof.
  intros a b. rewrite !mod32_land. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit (Z.ones 32) n); reflexivity.
Qed.

Lemma testbit_mod32 : forall a i, 0 <= i < 32 -> Z.testbit (a mod 2^32) i = Z.testbit a i.
Proof. intros a i Hi. apply Z.mod_pow2_bits_low. lia. Qed.

Lemma land_pow2_l : forall a i, 0 <= i -> Z.land (2 ^ i) a = if Z.testbit a i then 2 ^ i else 0.
Proof.
  intros a i Hi. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec i n) as [<-|Hne].
  - destruct (Z.testbit a i) eqn:E; [rewrite Z.pow2_bits_true by lia; reflexivity | rewrite Z.bits_0; reflexivity].
  - cbn [andb]. destruct (Z.testbit a i); [rewrite Z.pow2_bits_false by lia | rewrite Z.bits_0]; reflexivity.
Qed.

Lemma land_ones_l : forall a i, 0 <= i -> Z.land (2 ^ i - 1) a = a mod 2 ^ i.
Proof.
  intros a i Hi. rewrite Z.land_comm. replace (2 ^ i - 1) with (Z.ones i) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  apply Z.land_ones. lia.
Qed.

Lemma mod_mod_pow2 : forall a i j, 0 <= i <= j -> (a mod 2 ^ j) mod 2 ^ i = a mod 2 ^ i.
Proof.
  intros a i j Hij. pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) ltac:(lia)).
  pose proof (Z.pow_pos_nonneg 2 (j - i) ltac:(lia) ltac:(lia)).
  replace (2 ^ j) with (2 ^ i * 2 ^ (j - i)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma mod_pow2_succ : forall a j, 0 <= j ->
  a mod 2 ^ (j + 1) = (if Z.testbit a j then 2 ^ j else 0) + a mod 2 ^ j.
Proof.
  intros a j Hj. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj).
  replace (j + 1) with (Z.succ j) by lia. rewrite Z.pow_succ_r by lia.
  rewrite Z.mul_comm, Z.rem_mul_r by lia. rewrite <- Z.testbit_spec' by lia.
  destruct (Z.testbit a j); cbn [Z.b2z]; lia.
Qed.

Lemma pow2_le_31 : forall i, 0 <= i <= 31 -> 0 < 2 ^ i <= 2^31.
Proof. intros i Hi. split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]. Qed.


Lemma mm_loop_unfold : forall i a b p,
  mm_loop i a b p =
  (let hit := Z.testbit a (Z.of_nat i) in
   let p' := if hit then Z.lxor p b else p in
   if hit && (a mod 2 ^ (Z.of_nat i) =? 0) then p'
   else match i with O => p' | S i' => mm_loop i' a (bstep b) p' end).
Proof. intros [|i] a b p; reflexivity. Qed.

Lemma mm_loop_skip : forall i a b p,
  Z.testbit a (Z.of_nat (S i)) = false ->
  mm_loop (S i) a b p = mm_loop i a (bstep b) p.
Proof. intros i a b p Ht. rewrite mm_loop_unfold. rewrite Ht. reflexivity. Qed.

Lemma mm_loop_exit : forall i a b p,
  Z.testbit a (Z.of_nat i) = true -> a mod 2 ^ (Z.of_nat i) = 0 ->
  mm_loop i a b p = Z.lxor p b.
Proof.
  intros i a b p Ht Hm. rewrite mm_loop_unfold. rewrite Ht. cbn [andb].
  rewrite (proj2 (Z.eqb_eq _ _) Hm). reflexivity.
Qed.

Lemma mm_loop_go : forall i a b p,
  Z.testbit a (Z.of_nat (S i)) = true -> a mod 2 ^ (Z.of_nat (S i)) <> 0 ->
  mm_loop (S i) a b p = mm_loop i a (bstep b) (Z.lxor p b).
Proof.
  intros i a b p Ht Hm. rewrite mm_loop_unfold. rewrite Ht. cbn [andb].
  rewrite (proj2 (Z.eqb_neq _ _) Hm). reflexivity.
Qed.

Lemma mm_loop_low32 : forall i a a' b p, (i <= 31)%nat -> a mod 2^32 = a' mod 2^32 ->
  mm_loop i a b p = mm_loop i a' b p.
Proof.
  induction i as [|i IH]; intros a a' b p Hi Haa'; rewrite !mm_loop_unfold; cbv zeta.
  - rewrite <- (testbit_mod32 a), <- (testbit_mod32 a') by lia. rewrite Haa'.
    change (2 ^ Z.of_nat 0) with 1. rewrite !Z.mod_1_r. reflexivity.
  - rewrite <- (testbit_mod32 a), <- (testbit_mod32 a') by lia. rewrite Haa'.
    replace (a mod 2 ^ Z.of_nat (S i)) with (a' mod 2 ^ Z.of_nat (S i)).
    + rewrite (IH a a') by (lia || assumption). reflexivity.
    + rewrite <- (mod_mod_pow2 a (Z.of_nat (S i)) 32), <- (mod_mod_pow2 a' (Z.of_nat (S i)) 32) by lia.
      rewrite Haa'. reflexivity.
Qed.


Notation POLYSX := (18446744073402876704) (only parsing).
Notation MINIT  := (18446744071562067968) (only parsing).

Lemma MINIT_mod32 : MINIT mod 2^32 = 2 ^ 31.
Proof. reflexivity. Qed.

Lemma and_m_low : forall m a i, 0 <= i < 32 -> m mod 2^32 = 2 ^ i ->
  (Z.land m a) mod 2^32 = if Z.testbit a i then 2 ^ i else 0.
Proof. intros m a i Hi Hm. rewrite land_mod32, Hm, land_pow2_l, testbit_mod32 by lia. reflexivity. Qed.

Lemma and_m1_low : forall m a i, 0 <= i < 32 -> m mod 2^32 = 2 ^ i ->
  (Z.land (m + -1) a) mod 2^32 = a mod 2 ^ i.
Proof.
  intros m a i Hi Hm. rewrite land_mod32.
  pose proof (pow2_le_31 i ltac:(lia)) as P.
  assert (E : (m + -1) mod 2^32 = 2 ^ i - 1).
  { change (2^31) with 2147483648 in P. Z.div_mod_to_equations. lia. }
  rewrite E, land_ones_l by lia. apply mod_mod_pow2. lia.
Qed.

Lemma and_m1_low' : forall m a i, 0 <= i < 32 -> m mod 2^32 = 2 ^ i ->
  (Z.land ((m + -1) mod 2^64) a) mod 2^32 = a mod 2 ^ i.
Proof.
  intros m a i Hi Hm. rewrite <- (and_m1_low m a i Hi Hm). rewrite !land_mod32, mod64_mod32. reflexivity.
Qed.

Lemma mm_test_hit : forall m a i, 0 <= i < 32 -> m mod 2^32 = 2 ^ i ->
  (bv_swrap 32 (Z.land m a + 0) mod 2^64 = 0 <-> Z.testbit a i = false).
Proof.
  intros m a i Hi Hm. rewrite swrap32_mod64_zero, Z.add_0_r, (and_m_low m a i Hi Hm).
  pose proof (pow2_le_31 i ltac:(lia)). destruct (Z.testbit a i); split; intros; try reflexivity; try discriminate; lia.
Qed.

Lemma mm_test_low : forall m a i, 0 <= i < 32 -> m mod 2^32 = 2 ^ i ->
  (bv_swrap 32 (Z.land (m + -1) a + 0) mod 2^64 = 0 <-> a mod 2 ^ i = 0).
Proof. intros m a i Hi Hm. rewrite swrap32_mod64_zero, Z.add_0_r, (and_m1_low m a i Hi Hm). reflexivity. Qed.

Lemma mm_test_low' : forall m a i, 0 <= i < 32 -> m mod 2^32 = 2 ^ i ->
  (bv_swrap 32 (Z.land ((m + -1) mod 2^64) a + 0) mod 2^64 = 0 <-> a mod 2 ^ i = 0).
Proof. intros m a i Hi Hm. rewrite swrap32_mod64_zero, Z.add_0_r, (and_m1_low' m a i Hi Hm). reflexivity. Qed.

Lemma mm_shift_m : forall m i, 0 <= i < 31 -> m mod 2^32 = 2 ^ (i + 1) ->
  bv_swrap 32 (bv_wrap 32 m ≫ 1) = 2 ^ i.
Proof.
  intros m i Hi Hm. rewrite wrap32_eq, Hm, Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  rewrite Z.pow_add_r by lia. change (2^1) with 2. rewrite Z.div_mul by lia.
  apply swrap32_small. pose proof (pow2_le_31 i ltac:(lia)). assert (2 ^ i <= 2 ^ 30) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma sra63_odd : forall b, bv_signed (Z_to_bv 64 (b ≪ 63)) ≫ 63 mod 2^64 = if Z.odd b then 2^64 - 1 else 0.
Proof.
  intros b. rewrite Z_to_bv_signed, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2) with (2^63). change (2 ^ Z.of_N 64) with (2^64).
  pose proof (Z.div_mod b 2 ltac:(lia)) as D. rewrite (Zmod_odd b) in D.
  destruct (Z.odd b) eqn:O.
  - replace (b * 2 ^ 63 + 2 ^ 63) with ((b / 2 + 1) * 2^64) by lia. rewrite Z.mod_mul by lia. reflexivity.
  - replace (b * 2 ^ 63 + 2 ^ 63) with (2^63 + (b / 2) * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma odd_mod32 : forall b, Z.odd (b mod 2^32) = Z.odd b.
Proof. intros b. rewrite <- !Z.bit0_odd. apply testbit_mod32. lia. Qed.

Lemma shiftr1_mod32_range : forall b, 0 <= (b mod 2^32) ≫ 1 < 2^31.
Proof. intros b. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.

Lemma lxor_range64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lxor a b < 2^64.
Proof.
  intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NZ]; [lia|].
  apply Z.log2_lt_pow2; [pose proof (proj2 (Z.lxor_nonneg a b) ltac:(lia)); lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt; (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]) || idtac.
  - apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lxor_range32 : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 -> 0 <= Z.lxor a b < 2^32.
Proof.
  intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NZ]; [lia|].
  apply Z.log2_lt_pow2; [pose proof (proj2 (Z.lxor_nonneg a b) ltac:(lia)); lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Definition mm_bnext (b : Z) : Z :=
  Z.lxor (bv_swrap 32 (bv_wrap 32 b ≫ 1) mod 18446744073709551616)
         (Z.land (bv_signed (Z_to_bv 64 (b ≪ 63)) ≫ 63 mod 18446744073709551616) POLYSX).

Lemma mm_bnext_eq : forall b,
  mm_bnext b = Z.lxor ((b mod 2^32) ≫ 1) (if Z.odd b then POLYSX else 0).
Proof.
  intros b. unfold mm_bnext. change 18446744073709551616 with (2^64). rewrite sra63_odd, wrap32_eq.
  pose proof (shiftr1_mod32_range b) as R.
  rewrite swrap32_small by lia. rewrite Z.mod_small by lia.
  destruct (Z.odd b); [reflexivity | rewrite Z.land_0_l; reflexivity].
Qed.

Lemma mm_bnext_range : forall b, 0 <= mm_bnext b < 2^64.
Proof.
  intros b. rewrite mm_bnext_eq. pose proof (shiftr1_mod32_range b) as R.
  apply lxor_range64; [lia|]. destruct (Z.odd b); lia.
Qed.

Lemma mm_bnext_mod32 : forall b, (mm_bnext b) mod 2^32 = bstep (b mod 2^32).
Proof.
  intros b. rewrite mm_bnext_eq, lxor_mod32. unfold bstep. rewrite odd_mod32.
  pose proof (shiftr1_mod32_range b) as R. rewrite (Z.mod_small (_ ≫ 1)) by lia.
  destruct (Z.odd b); [reflexivity | rewrite Z.mod_0_l by lia; rewrite Z.lxor_0_r; reflexivity].
Qed.

Lemma POLY_range : 0 <= POLY < 2^32.
Proof. unfold POLY. lia. Qed.

Lemma bstep_range : forall b, 0 <= b < 2^32 -> 0 <= bstep b < 2^32.
Proof.
  intros b Hb. unfold bstep.
  assert (Hs : 0 <= b ≫ 1 < 2^31) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  destruct (Z.odd b); [|lia]. apply lxor_range32; [lia| apply POLY_range].
Qed.

Lemma mm_loop_range : forall i a b p, 0 <= b < 2^32 -> 0 <= p < 2^32 -> 0 <= mm_loop i a b p < 2^32.
Proof.
  induction i as [|i IH]; intros a b p Hb Hp; rewrite mm_loop_unfold; cbv zeta.
  - pose proof (lxor_range32 p b Hp Hb).
    destruct (Z.testbit a (Z.of_nat 0)); cbn [andb]; [destruct (a mod 2 ^ Z.of_nat 0 =? 0)|]; lia.
  - pose proof (lxor_range32 p b Hp Hb). pose proof (bstep_range b Hb).
    destruct (Z.testbit a (Z.of_nat (S i))); cbn [andb]; [destruct (a mod 2 ^ Z.of_nat (S i) =? 0)|]; try lia;
    apply IH; lia.
Qed.

Lemma multmodp_range : forall a b, 0 <= b < 2^32 -> 0 <= multmodp a b < 2^32.
Proof. intros. unfold multmodp. apply mm_loop_range; lia. Qed.

Lemma land_M32 : forall c, Z.land c M32 = c mod 2^32.
Proof. intros. unfold M32. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.


Definition sxz (x : Z) : Z := bv_swrap 32 x mod 18446744073709551616.

Lemma sxz_range : forall x, 0 <= sxz x < 2^64.
Proof. intros x. unfold sxz. apply Z.mod_pos_bound. lia. Qed.

Lemma sxz_mod32 : forall x, sxz x mod 2^32 = x mod 2^32.
Proof. intros x. unfold sxz. change 18446744073709551616 with (2^64). apply swrap32_mod64_mod32. Qed.

Lemma sxz_cases : forall x, 0 <= x < 2^32 ->
  (x < 2^31 /\ sxz x = x) \/ (2^31 <= x /\ sxz x = x + (2^64 - 2^32)).
Proof.
  intros x Hx. unfold sxz. rewrite swrap32_eq. change 18446744073709551616 with (2^64).
  destruct (Z.lt_ge_cases x (2^31)); [left|right]; (split; [lia|]); Z.div_mod_to_equations; lia.
Qed.

Lemma sxz_small : forall x, 0 <= x < 2^31 -> sxz x = x.
Proof. intros x Hx. destruct (sxz_cases x ltac:(lia)) as [[_ E]|[C _]]; [exact E| lia]. Qed.

Lemma sxz_mod_pow2 : forall x i, 0 <= i <= 32 -> sxz x mod 2 ^ i = x mod 2 ^ i.
Proof.
  intros x i Hi. rewrite <- (mod_mod_pow2 (sxz x) i 32), <- (mod_mod_pow2 x i 32) by lia.
  rewrite sxz_mod32. reflexivity.
Qed.

Lemma sxz_testbit_low : forall x i, 0 <= i < 32 -> Z.testbit (sxz x) i = Z.testbit x i.
Proof. intros x i Hi. rewrite <- (testbit_mod32 (sxz x)), <- (testbit_mod32 x) by lia. rewrite sxz_mod32. reflexivity. Qed.

Lemma testbit_high : forall k x n, 0 <= x < 2 ^ k -> 0 <= k <= n -> Z.testbit x n = false.
Proof.
  intros k x n Hx Hk. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma testbit31_hi : forall w, 2^31 <= w < 2^32 -> Z.testbit w 31 = true.
Proof.
  intros w Hw. pose proof (Z.testbit_spec' w 31 ltac:(lia)) as T.
  replace (w / 2 ^ 31) with 1 in T by (Z.div_mod_to_equations; lia).
  destruct (Z.testbit w 31); [reflexivity | discriminate T].
Qed.

Lemma sxz_testbit : forall w n, 0 <= w < 2^32 -> 0 <= n ->
  Z.testbit (sxz w) n = if n <? 32 then Z.testbit w n else if n <? 64 then Z.testbit w 31 else false.
Proof.
  intros w n Hw Hn. destruct (Z.ltb_spec n 32) as [L|L]; [apply sxz_testbit_low; lia|].
  destruct (sxz_cases w Hw) as [[C E]|[C E]]; rewrite E.
  - rewrite (testbit_high 32 w n) by lia. rewrite (testbit_high 31 w 31) by lia. destruct (n <? 64); reflexivity.
  - rewrite testbit31_hi by lia.
    replace n with ((n - 32) + 32) at 1 by lia. rewrite <- Z.div_pow2_bits by lia.
    replace ((w + (2 ^ 64 - 2 ^ 32)) / 2 ^ 32) with (Z.ones 32) by (change (Z.ones 32) with (2^32 - 1); Z.div_mod_to_equations; lia).
    rewrite Z.testbit_ones_nonneg by lia.
    destruct (Z.ltb_spec n 64), (Z.ltb_spec (n - 32) 32); try reflexivity; lia.
Qed.

Lemma lxor_sxz : forall u v, 0 <= u < 2^32 -> 0 <= v < 2^32 -> Z.lxor (sxz u) (sxz v) = sxz (Z.lxor u v).
Proof.
  intros u v Hu Hv. pose proof (lxor_range32 u v Hu Hv) as Huv.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec, !sxz_testbit by lia.
  destruct (n <? 32); [symmetry; apply Z.lxor_spec|].
  destruct (n <? 64); [symmetry; apply Z.lxor_spec | reflexivity].
Qed.

Definition sxc (x : Z) : Prop := x = sxz (x mod 2^32).

Lemma sxc_sxz : forall x, sxc (sxz x).
Proof.
  intros x. unfold sxc. rewrite sxz_mod32. unfold sxz. change 18446744073709551616 with (2^64).
  f_equal. rewrite !swrap32_eq. f_equal. Z.div_mod_to_equations. lia.
Qed.

Lemma sxc_lxor : forall a b, sxc a -> sxc b -> sxc (Z.lxor a b).
Proof.
  intros a b Ha Hb. unfold sxc in *. rewrite Ha, Hb at 1.
  rewrite lxor_sxz by (apply Z.mod_pos_bound; lia). rewrite lxor_mod32. reflexivity.
Qed.

Lemma sxc_0 : sxc 0. Proof. reflexivity. Qed.
Lemma sxc_MINIT : sxc MINIT. Proof. reflexivity. Qed.
Lemma sxc_POLYSX : sxc POLYSX. Proof. reflexivity. Qed.

Lemma sxc_bnext : forall b, sxc (mm_bnext b).
Proof.
  intros b. rewrite mm_bnext_eq. apply sxc_lxor.
  - pose proof (shiftr1_mod32_range b) as R. unfold sxc. rewrite (Z.mod_small ((b mod 2^32) ≫ 1) (2^32)) by lia. symmetry. apply sxz_small. lia.
  - destruct (Z.odd b); [apply sxc_POLYSX| apply sxc_0].
Qed.


Definition m_ok (m : Z) (i : nat) : Prop := m = 2 ^ Z.of_nat i \/ (m = MINIT /\ i = 31%nat).

Lemma m_ok_low32 : forall m i, (i <= 31)%nat -> m_ok m i -> m mod 2^32 = 2 ^ Z.of_nat i.
Proof.
  intros m i Hi [->|[-> ->]]; [|reflexivity]. pose proof (pow2_le_31 (Z.of_nat i) ltac:(lia)). apply Z.mod_small. lia.
Qed.

Lemma m_ok_range : forall m i, (i <= 31)%nat -> m_ok m i -> 0 <= m < 2^64.
Proof. intros m i Hi [->|[-> ->]]; [|lia]. pose proof (pow2_le_31 (Z.of_nat i) ltac:(lia)). lia. Qed.

Lemma testbit_MINIT : forall n, 0 <= n -> Z.testbit MINIT n = (31 <=? n) && (n <? 64).
Proof.
  intros n Hn. change MINIT with (Z.shiftl (Z.ones 33) 31).
  destruct (Z.leb_spec 31 n) as [L|L]; cbn [andb].
  - rewrite Z.shiftl_spec by lia. rewrite Z.testbit_ones_nonneg by lia.
    destruct (Z.ltb_spec (n - 31) 33), (Z.ltb_spec n 64); try reflexivity; lia.
  - rewrite Z.shiftl_spec by lia. apply Z.testbit_neg_r. lia.
Qed.

Lemma land_MINIT_sxz : forall a, 0 <= a < 2^32 -> (Z.land MINIT (sxz a) = 0 <-> Z.testbit a 31 = false).
Proof.
  intros a Ha. split; intros H.
  - assert (T : Z.testbit (Z.land MINIT (sxz a)) 31 = false) by (rewrite H; apply Z.bits_0).
    rewrite Z.land_spec, testbit_MINIT, sxz_testbit_low in T by lia. exact T.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, testbit_MINIT, sxz_testbit by lia.
    destruct (Z.leb_spec 31 n), (Z.ltb_spec n 64); cbn [andb]; try reflexivity.
    destruct (Z.ltb_spec n 32); [|exact H]. replace n with 31 by lia. exact H.
Qed.

Lemma mm64_test_hit : forall m a i, (i <= 31)%nat -> 0 <= a < 2^32 -> m_ok m i ->
  (Z.land m (sxz a) = 0 <-> Z.testbit a (Z.of_nat i) = false).
Proof.
  intros m a i Hi Ha [->|[-> ->]]; [|apply land_MINIT_sxz; exact Ha].
  rewrite land_pow2_l, sxz_testbit_low by lia. pose proof (pow2_le_31 (Z.of_nat i) ltac:(lia)).
  destruct (Z.testbit a (Z.of_nat i)); split; intros; try reflexivity; try discriminate; lia.
Qed.

Lemma m_ok_m1 : forall m i, (i <= 31)%nat -> m_ok m i ->
  bv_swrap 32 (m + -1) mod 18446744073709551616 = 2 ^ Z.of_nat i - 1.
Proof.
  intros m i Hi [->|[-> ->]]; [|reflexivity]. pose proof (pow2_le_31 (Z.of_nat i) ltac:(lia)).
  rewrite swrap32_small by lia. apply Z.mod_small. lia.
Qed.

Lemma mm64_test_low : forall m a i, (i <= 31)%nat -> m_ok m i ->
  (Z.land (bv_swrap 32 (m + -1) mod 18446744073709551616) (sxz a) = 0 <-> a mod 2 ^ Z.of_nat i = 0).
Proof. intros m a i Hi Hm. rewrite (m_ok_m1 m i Hi Hm), land_ones_l, sxz_mod_pow2 by lia. reflexivity. Qed.

Lemma m_ok_shift : forall m i, (i < 31)%nat -> m_ok m (S i) -> m_ok (bv_swrap 32 (bv_wrap 32 m ≫ 1)) i.
Proof.
  intros m i Hi Hm. left. apply mm_shift_m; [lia|].
  replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia. apply m_ok_low32; [lia| exact Hm].
Qed.


Lemma xp_0 : xp 0 = X0.
Proof. reflexivity. Qed.

Lemma x2n_loop_xp : forall f n k e, 0 <= k -> exists e', x2n_loop f n k (xp e) = xp e'.
Proof.
  induction f as [|f IH]; intros n k e Hk; cbn [x2n_loop].
  - exists e. reflexivity.
  - destruct (n =? 0); [exists e; reflexivity|].
    destruct (Z.odd n).
    + pose proof (Z.mod_pos_bound k 32 ltac:(lia)) as Hm.
      replace (k mod 32) with (Z.of_nat (Z.to_nat (k mod 32))) by lia.
      rewrite x2n_xp by lia. rewrite multmodp_xp_xp. apply IH. lia.
    + apply IH. lia.
Qed.

Lemma x2nmodp_nz_any : forall n k, 0 <= k -> x2nmodp n k mod 2 ^ 32 <> 0.
Proof.
  intros n k Hk. unfold x2nmodp. rewrite <- xp_0.
  destruct (x2n_loop_xp 64 n k 0 Hk) as [e' ->].
  pose proof (xp_range e'). pose proof (xp_nz e'). rewrite Z.mod_small by lia. lia.
Qed.

Lemma x2nmodp_range : forall n k, 0 <= x2nmodp n k < 2^32.
Proof. intros. apply x2nmodp_range_any. Qed.


Lemma crc_idx_form : forall b c, 0 <= b < 256 -> Z.lxor b (Z.land c 255) = Z.land (Z.lxor b c) 255.
Proof.
  intros b c Hb. apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, !Z.land_spec, Z.lxor_spec.
  destruct (Z.ltb_spec n 8) as [L|L].
  - replace (Z.testbit 255 n) with true; [rewrite !andb_true_r; reflexivity|].
    symmetry. change 255 with (Z.ones 8). apply Z.ones_spec_low. lia.
  - replace (Z.testbit 255 n) with false; [|symmetry; change 255 with (Z.ones 8); apply Z.ones_spec_high; lia].
    rewrite !andb_false_r, (testbit_high 8 b n) by lia. reflexivity.
Qed.

Lemma land255_range : forall x, 0 <= Z.land x 255 < 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma shiftr8_range32 : forall c, 0 <= c < 2^32 -> 0 <= c ≫ 8 < 2^24.
Proof. intros c Hc. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.

Lemma crc_byte_range : forall c b, 0 <= c < 2^32 -> 0 <= crc_byte c b < 2^32.
Proof.
  intros c b Hc. unfold crc_byte. apply lxor_range32.
  - pose proof (shiftr8_range32 c Hc). lia.
  - apply CkMathCrc.ctab_range.
Qed.

Lemma crc_bytes_range : forall bs c, 0 <= c < 2^32 -> 0 <= crc_bytes c bs < 2^32.
Proof.
  induction bs as [|b bs IH]; intros c Hc; [exact Hc|].
  rewrite crc_bytes_cons. apply IH. apply crc_byte_range. exact Hc.
Qed.
