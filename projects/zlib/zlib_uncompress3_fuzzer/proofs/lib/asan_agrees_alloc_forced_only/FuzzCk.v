(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only Require Import PropExec FuzzZ.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


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

Lemma POLY_range : 0 <= POLY < two32.
Proof. unfold POLY. lia. Qed.

Lemma bstep_range : forall b, 0 <= b < two32 -> 0 <= bstep b < two32.
Proof.
  intros b Hb. unfold bstep.
  pose proof (shiftr_range b 1 31 ltac:(lia) ltac:(lia) ltac:(change (2 ^ (31 + 1)) with two32; lia)) as Hs.
  change (2 ^ 31) with 2147483648 in Hs.
  destruct (Z.odd b); [|lia].
  pose proof (lxor_range32 (Z.shiftr b 1) POLY ltac:(lia) POLY_range). lia.
Qed.

Lemma mm_loop_range : forall i a b p, 0 <= b < two32 -> 0 <= p < two32 -> 0 <= mm_loop i a b p < two32.
Proof.
  induction i as [|i IH]; intros a b p Hb Hp; rewrite mm_loop_unfold; cbv zeta.
  - pose proof (lxor_range32 p b Hp Hb).
    destruct (Z.testbit a (Z.of_nat 0)); cbn [andb]; [destruct (a mod 2 ^ Z.of_nat 0 =? 0)|]; lia.
  - pose proof (lxor_range32 p b Hp Hb). pose proof (bstep_range b Hb).
    destruct (Z.testbit a (Z.of_nat (S i))); cbn [andb]; [destruct (a mod 2 ^ Z.of_nat (S i) =? 0)|]; try lia;
    apply IH; lia.
Qed.

Lemma multmodp_range : forall a b, 0 <= b < two32 -> 0 <= multmodp a b < two32.
Proof. intros. unfold multmodp. apply mm_loop_range; lia. Qed.


Lemma testbit_mod32 : forall a i, 0 <= i < 32 -> Z.testbit (a mod two32) i = Z.testbit a i.
Proof. intros a i Hi. change two32 with (2 ^ 32). apply Z.mod_pow2_bits_low. lia. Qed.

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

Lemma and_m_low : forall m a i, 0 <= i < 32 -> m mod two32 = 2 ^ i ->
  (Z.land m a) mod two32 = if Z.testbit a i then 2 ^ i else 0.
Proof.
  intros m a i Hi Hm. rewrite <- land_mod32, Hm, land_pow2_l, testbit_mod32 by lia. reflexivity.
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

Lemma and_m1_low : forall m a i, 0 <= i < 32 -> 0 <= m -> m mod two32 = 2 ^ i ->
  (Z.land (m - 1) a) mod two32 = a mod 2 ^ i.
Proof.
  intros m a i Hi Hm0 Hm. rewrite <- land_mod32.
  pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) ltac:(lia)).
  assert (2 ^ i <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). change (2 ^ 31) with 2147483648 in *.
  assert (E : (m - 1) mod two32 = 2 ^ i - 1).
  { rewrite <- Zminus_mod_idemp_l, Hm. apply Z.mod_small. lia. }
  rewrite E, land_ones_l by lia. change two32 with (2 ^ 32). apply mod_mod_pow2. lia.
Qed.

Lemma sx32_zero_iff : forall x, 0 <= x < two32 -> (sx32 x =? 0) = (x =? 0).
Proof.
  intros x Hx. unfold sx32. destruct (Z.ltb_spec x 2147483648); [reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ 0)) by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

Definition POLYSX : Z := 18446744073402876704.

Lemma odd_mod32 : forall b, Z.odd (b mod two32) = Z.odd b.
Proof.
  intros b. rewrite <- !Z.bit0_odd. apply testbit_mod32. lia.
Qed.

Lemma bstep_machine : forall breg, 0 <= breg ->
  (Z.lxor (Z.shiftr (breg mod two32) 1) (Z.land (if Z.odd breg then ONES64 else 0) POLYSX)) mod two32
  = bstep (breg mod two32).
Proof.
  intros breg Hb. unfold bstep. rewrite odd_mod32.
  pose proof (mod32_range breg) as Hr.
  pose proof (shiftr_range (breg mod two32) 1 31 ltac:(lia) ltac:(lia) ltac:(change (2 ^ (31 + 1)) with two32; lia)) as Hs.
  change (2 ^ 31) with 2147483648 in Hs.
  destruct (Z.odd breg).
  - rewrite <- lxor_mod32. rewrite (Z.mod_small (Z.shiftr _ 1)) by lia.
    replace (Z.land ONES64 POLYSX mod two32) with POLY by reflexivity. reflexivity.
  - rewrite Z.land_0_l, Z.lxor_0_r. apply Z.mod_small. lia.
Qed.

Lemma mm_loop_low32 : forall i a a' b p, (i <= 31)%nat -> a mod two32 = a' mod two32 ->
  mm_loop i a b p = mm_loop i a' b p.
Proof.
  induction i as [|i IH]; intros a a' b p Hi Haa'; rewrite !mm_loop_unfold; cbv zeta.
  - rewrite <- (testbit_mod32 a), <- (testbit_mod32 a') by lia. rewrite Haa'.
    change (2 ^ Z.of_nat 0) with 1. rewrite !Z.mod_1_r. reflexivity.
  - rewrite <- (testbit_mod32 a), <- (testbit_mod32 a') by lia. rewrite Haa'.
    replace (a mod 2 ^ Z.of_nat (S i)) with (a' mod 2 ^ Z.of_nat (S i)).
    + rewrite (IH a a') by (lia || assumption). reflexivity.
    + change two32 with (2 ^ 32) in Haa'.
      rewrite <- (mod_mod_pow2 a (Z.of_nat (S i)) 32), <- (mod_mod_pow2 a' (Z.of_nat (S i)) 32) by lia.
      rewrite Haa'. reflexivity.
Qed.

Lemma testbit_sx32 : forall x i, 0 <= x < two32 -> 0 <= i < 32 -> Z.testbit (sx32 x) i = Z.testbit x i.
Proof.
  intros x i Hx Hi. rewrite <- (testbit_mod32 (sx32 x)) by lia. rewrite sx32_mod32 by lia. reflexivity.
Qed.

Lemma sx32_mod_pow2 : forall x i, 0 <= x < two32 -> 0 <= i <= 32 -> (sx32 x) mod 2 ^ i = x mod 2 ^ i.
Proof.
  intros x i Hx Hi. rewrite <- (mod_mod_pow2 (sx32 x) i 32) by lia. change (2 ^ 32) with two32.
  rewrite sx32_mod32 by lia. reflexivity.
Qed.

Definition MINIT : Z := 18446744071562067968.

Lemma MINIT_mod32 : MINIT mod two32 = 2 ^ 31.
Proof. reflexivity. Qed.

Lemma and_m_sx32 : forall m x i, 0 <= x < two32 -> (i <= 31)%nat ->
  (m = 2 ^ Z.of_nat i \/ (m = MINIT /\ i = 31%nat)) ->
  (Z.land m (sx32 x) =? 0) = negb (Z.testbit x (Z.of_nat i)).
Proof.
  intros m x i Hx Hi Hm. destruct Hm as [-> | [-> ->]].
  - rewrite land_pow2_l, testbit_sx32 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat i) ltac:(lia) ltac:(lia)).
    destruct (Z.testbit x (Z.of_nat i)); [apply Z.eqb_neq; lia | reflexivity].
  - change (Z.of_nat 31) with 31.
    assert (Hb : Z.testbit x 31 = negb (x <? 2147483648)).
    { pose proof (Z.testbit_spec' x 31 ltac:(lia)) as T. change (2 ^ 31) with 2147483648 in T.
      destruct (Z.ltb_spec x 2147483648).
      - rewrite Z.div_small in T by lia. destruct (Z.testbit x 31); [discriminate T | reflexivity].
      - replace (x / 2147483648) with 1 in T by (apply (Z.div_unique x 2147483648 1 (x - 2147483648)); lia).
        destruct (Z.testbit x 31); [reflexivity | discriminate T]. }
    rewrite Hb. unfold sx32. destruct (Z.ltb_spec x 2147483648); cbn [negb].
    + apply Z.eqb_eq. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.ltb_spec n 31).
      * replace MINIT with (8589934591 * 2 ^ 31) by reflexivity. rewrite Z.mul_pow2_bits by lia.
        rewrite (Z.testbit_neg_r _ (n - 31)) by lia. reflexivity.
      * rewrite (Z_testbit_high 31 x n) by (try lia; change (2 ^ 31) with 2147483648; lia). apply andb_false_r.
    + assert (Hb2 : Z.testbit x 31 = true) by (rewrite Hb; destruct (Z.ltb_spec x 2147483648); [lia|reflexivity]).
      apply Z.eqb_neq. intros E.
      assert (T : Z.testbit (Z.land MINIT (x + 18446744069414584320)) 31 = true).
      { rewrite Z.land_spec. replace MINIT with (8589934591 * 2 ^ 31) by reflexivity.
        rewrite Z.mul_pow2_bits by lia. change (Z.testbit 8589934591 (31 - 31)) with true. cbn [andb].
        rewrite <- (Z.mod_pow2_bits_low _ 32) by lia.
        replace ((x + 18446744069414584320) mod 2 ^ 32) with x.
        - exact Hb2.
        - change (2 ^ 32) with two32. replace (x + 18446744069414584320) with (x + 4294967295 * two32) by lia.
          rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
      rewrite E, Z.bits_0 in T. discriminate T.
Qed.

Lemma m1_sx32 : forall m i, (i <= 31)%nat -> (m = 2 ^ Z.of_nat i \/ (m = MINIT /\ i = 31%nat)) ->
  sx32 ((m - 1) mod two32) = 2 ^ Z.of_nat i - 1.
Proof.
  intros m i Hi Hm. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat i) ltac:(lia) ltac:(lia)).
  assert (2 ^ Z.of_nat i <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). change (2 ^ 31) with 2147483648 in *.
  destruct Hm as [-> | [-> ->]].
  - rewrite Z.mod_small by lia. apply sx32_small. lia.
  - reflexivity.
Qed.

Lemma m_low32 : forall m i, (i <= 31)%nat -> (m = 2 ^ Z.of_nat i \/ (m = MINIT /\ i = 31%nat)) ->
  m mod two32 = 2 ^ Z.of_nat i.
Proof.
  intros m i Hi Hm. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat i) ltac:(lia) ltac:(lia)).
  assert (2 ^ Z.of_nat i <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). change (2 ^ 31) with 2147483648 in *.
  destruct Hm as [-> | [-> ->]]; [apply Z.mod_small; lia | reflexivity].
Qed.

Lemma m_range : forall m i, (i <= 31)%nat -> (m = 2 ^ Z.of_nat i \/ (m = MINIT /\ i = 31%nat)) -> 0 <= m < two64.
Proof.
  intros m i Hi Hm. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat i) ltac:(lia) ltac:(lia)).
  assert (2 ^ Z.of_nat i <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). change (2 ^ 31) with 2147483648 in *.
  destruct Hm as [-> | [-> ->]]; [lia | unfold MINIT; lia].
Qed.

Lemma testbit31_hi : forall w, 2147483648 <= w < two32 -> Z.testbit w 31 = true.
Proof.
  intros w Hw. pose proof (Z.testbit_spec' w 31 ltac:(lia)) as T. change (2 ^ 31) with 2147483648 in T.
  replace (w / 2147483648) with 1 in T by (apply (Z.div_unique w 2147483648 1 (w - 2147483648)); lia).
  destruct (Z.testbit w 31); [reflexivity | discriminate T].
Qed.

Lemma sx32_testbit : forall w n, 0 <= w < two32 -> 0 <= n ->
  Z.testbit (sx32 w) n = if n <? 32 then Z.testbit w n else if n <? 64 then Z.testbit w 31 else false.
Proof.
  intros w n Hw Hn. unfold sx32. destruct (Z.ltb_spec w 2147483648).
  - destruct (Z.ltb_spec n 32); [reflexivity|].
    rewrite (Z_testbit_high 32 w n) by (try lia; change (2 ^ 32) with two32; lia).
    rewrite (Z_testbit_high 31 w 31) by (try lia; change (2 ^ 31) with 2147483648; lia).
    destruct (n <? 64); reflexivity.
  - destruct (Z.ltb_spec n 32).
    + rewrite <- (Z.mod_pow2_bits_low _ 32 n) by lia. f_equal.
      change (2 ^ 32) with two32. replace (w + 18446744069414584320) with (w + 4294967295 * two32) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    + rewrite testbit31_hi by lia.
      replace n with ((n - 32) + 32) at 1 by lia. rewrite <- Z.div_pow2_bits by lia.
      replace ((w + 18446744069414584320) / 2 ^ 32) with (Z.ones 32).
      * rewrite Z.testbit_ones_nonneg by lia.
        destruct (Z.ltb_spec n 64), (Z.ltb_spec (n - 32) 32); try reflexivity; lia.
      * change (Z.ones 32) with 4294967295. change (2 ^ 32) with two32.
        apply (Z.div_unique _ two32 4294967295 w); lia.
Qed.

Lemma lxor_sx32 : forall u v, 0 <= u < two32 -> 0 <= v < two32 -> Z.lxor (sx32 u) (sx32 v) = sx32 (Z.lxor u v).
Proof.
  intros u v Hu Hv. pose proof (lxor_range32 u v Hu Hv) as Huv.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec, !sx32_testbit by lia.
  destruct (n <? 32); [symmetry; apply Z.lxor_spec|].
  destruct (n <? 64); [symmetry; apply Z.lxor_spec | reflexivity].
Qed.

Lemma sx32_0 : sx32 0 = 0.
Proof. reflexivity. Qed.

Lemma sx32_X0 : sx32 X0 = MINIT.
Proof. reflexivity. Qed.

Lemma POLYSX_sx : POLYSX = sx32 POLY.
Proof. reflexivity. Qed.

Lemma bstep_machine_sx : forall b, 0 <= b < two32 ->
  Z.lxor (Z.shiftr (sx32 b mod two32) 1) (Z.land (if Z.odd (sx32 b) then ONES64 else 0) POLYSX) = sx32 (bstep b).
Proof.
  intros b Hb. rewrite sx32_mod32 by lia.
  replace (Z.odd (sx32 b)) with (Z.odd b) by (rewrite <- (odd_mod32 (sx32 b)), sx32_mod32 by lia; reflexivity).
  pose proof (shiftr_range b 1 31 ltac:(lia) ltac:(lia) ltac:(change (2 ^ (31 + 1)) with two32; lia)) as Hs.
  change (2 ^ 31) with 2147483648 in Hs.
  unfold bstep. destruct (Z.odd b).
  - replace (Z.land ONES64 POLYSX) with (sx32 POLY) by reflexivity.
    rewrite <- (sx32_small (Z.shiftr b 1)) at 1 by lia. apply lxor_sx32; [lia | apply POLY_range].
  - rewrite Z.land_0_l, Z.lxor_0_r. symmetry. apply sx32_small. lia.
Qed.

Lemma X0_range : 0 <= X0 < two32.
Proof. unfold X0. lia. Qed.

Lemma x2n_loop_range : forall f n k p, 0 <= p < two32 -> 0 <= x2n_loop f n k p < two32.
Proof.
  induction f as [|f IH]; intros n k p Hp; cbn [x2n_loop]; [lia|].
  destruct (n =? 0); [lia|]. apply IH. destruct (Z.odd n); [apply multmodp_range|]; lia.
Qed.

Lemma lxor_low32 : forall c p, (Z.lxor c p) mod two32 = Z.lxor (c mod two32) (p mod two32).
Proof. intros. symmetry. apply lxor_mod32. Qed.

Lemma land_M32 : forall c, Z.land c M32 = c mod two32.
Proof. intros. unfold M32. symmetry. apply mod32_land. Qed.
