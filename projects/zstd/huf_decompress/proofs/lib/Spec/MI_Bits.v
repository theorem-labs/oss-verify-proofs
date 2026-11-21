(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (11 recorded proofs replaced by written proofs (land_opp_odd, land_opp_even, lowbit_pow2 and 8 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Malloc MI_Arith.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Bits () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z4predC47Corelib4Init9Datatypes4negbK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z>testbit_even_0C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z=testbit_odd_0C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init5Logic6eq_symK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC46Stdlib4Bool4Bool;andb_negb_rC56Stdlib6ZArith6BinInt1ZAtestbit_even_succC56Stdlib6ZArith6BinInt1Z@testbit_odd_succC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z8bits_oppC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic3and00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums1N01I47Corelib4Init5Logic5False00K46Stdlib9micromega7EnvRing5PExpr06C46Stdlib6ZArith4Wf_Z9Zlt_0_indC56Stdlib6ZArith6BinInt1Z;Even_or_OddC56Stdlib6ZArith6BinInt1Z4EvenC56Stdlib6ZArith6BinInt1Z3OddI47Corelib4Init5Logic2or00K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z9pow_add_rc59OSSVerify5KrLib4Spec7MI_Bits=land_opp_evenC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib4Spec7MI_Bits<land_opp_oddC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z:ltb_irreflC56Stdlib6ZArith6BinInt1Z<testbit_onesC56Stdlib6ZArith6BinInt1Z:ones_equivc59OSSVerify5KrLib4Spec7MI_Bits;lowbit_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z9log2_pow2c59OSSVerify5KrLib4Spec7MI_Bits=land_opp_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow2_bits_trueC47Corelib4Init9Datatypes9andb_propC47Corelib4Init5Logic7and_indC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z3lorC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool;orb_false_rC46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z8lor_specC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z8lxor_lorc59OSSVerify5KrLib4Spec7MI_Bits=sub_bit_ldiffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Bits>lowbit_nonzeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Bits>lowbit_testbitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Bits:ctz32_pow2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Bits?testbit_sub_bitC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec8MI_Arith@bits_below_boundC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Local Open Scope Z_scope.

Lemma land_opp_odd a : Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma land_opp_even a : Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (- a).
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite !Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

Lemma lowbit_pow2 : forall m, 0 < m -> exists k, 0 <= k /\ Z.land m (- m) = 2 ^ k /\ 2 ^ k <= m.
Proof.
  intros m Hm.
  pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
  cbv beta in G. apply G; [|lia|lia]. clear G m Hm.
  intros x IH Hx0 Hx.
  destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
  - destruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L).
    exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
  - exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed.

Lemma land_opp_pow2 k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
  intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
  subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.

Lemma lowbit_nonzero m : 0 < m -> exists k, 0 <= k /\ lowbit m = 2 ^ k /\ 2 ^ k <= m.
Proof. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.

Lemma ctz32_pow2 k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.

Lemma lowbit_testbit : forall v k, 0 <= k -> lowbit v = 2 ^ k -> Z.testbit v k = true.
Proof.
  intros v k Hk E. unfold lowbit in E.
  assert (T : Z.testbit (Z.land v (- v)) k = true) by (rewrite E; apply Z.pow2_bits_true; lia).
  rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

(* [comment removed for export] *)
Lemma sub_bit_ldiff f i : 0 <= f -> 0 <= i -> Z.testbit f i = true -> f - 2 ^ i = Z.ldiff f (2 ^ i).
Proof.
  intros Hf Hi Hb.
  assert (E : f = Z.lor (Z.ldiff f (2 ^ i)) (2 ^ i)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, Z.ldiff_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec i n) as [<-|NE]; [rewrite Hb; reflexivity|]. cbn. rewrite Bool.andb_true_r, Bool.orb_false_r. reflexivity. }
  assert (D : Z.land (Z.ldiff f (2 ^ i)) (2 ^ i) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec i n); cbn; [rewrite Bool.andb_false_r| rewrite Bool.andb_false_r]; reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ D) as A. rewrite (Z.lxor_lor _ _ D) in A. rewrite <- E in A. lia.
Qed.

Lemma testbit_sub_bit f i j : 0 <= f -> 0 <= i -> 0 <= j -> Z.testbit f i = true ->
  Z.testbit (f - 2 ^ i) j = Z.testbit f j && negb (i =? j).
Proof.
  intros Hf Hi Hj Hb. rewrite (sub_bit_ldiff f i Hf Hi Hb), Z.ldiff_spec, Z.pow2_bits_eqb by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lowbit_idiom m : 0 < m ->
  exists k, 0 <= k /\ lowbit m = 2 ^ k /\ ctz32 (lowbit m) = k /\ Z.testbit m k = true
    /\ 0 <= m - lowbit m /\ (forall j, 0 <= j -> Z.testbit (m - lowbit m) j = Z.testbit m j && negb (k =? j)).
Proof.
  intros Hm. destruct (lowbit_nonzero m Hm) as (k & Hk & E & L). exists k.
  pose proof (lowbit_testbit m k Hk E) as Tb.
  split; [exact Hk|]. split; [exact E|]. split; [rewrite E; apply ctz32_pow2; exact Hk|]. split; [exact Tb|].
  rewrite E. split; [lia|]. intros j Hj. apply testbit_sub_bit; auto; lia.
Qed.

(* [comment removed for export] *)
Lemma mask_below m n : 0 <= m -> 0 <= n -> (forall i, 0 <= i -> Z.testbit m i = true -> i <= n) -> m < 2 ^ (n + 1).
Proof. intros Hm Hn H. apply bits_below_bound; [lia| lia|]. intros i Hi Hb. pose proof (H i Hi Hb). lia. Qed.
