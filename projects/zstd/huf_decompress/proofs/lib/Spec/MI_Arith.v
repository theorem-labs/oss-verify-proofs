(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (8 recorded proofs replaced by written proofs (size_classes_length, size_classes_bounds, size_class_bound and 5 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Malloc.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Arith () := "K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4list00I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C47Corelib4Init5Logic6eq_indI47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I46Stdlib5Lists4List6Exists00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc<size_classesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_InC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltc59OSSVerify5KrLib4Spec8MI_ArithCsize_classes_boundsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib4Spec8MI_ArithCsize_classes_lengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z=ones_spec_lowC56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z:ones_equivC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z>pow2_bits_trueC47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z?pow2_bits_falseC59OSSVerify5KrLib4Spec6Malloc3bitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_le_pow2C56Stdlib6ZArith6BinInt1Z8bit_log2C56Stdlib6ZArith6BinInt1Z;log2_nonnegC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2K47Corelib4Init9Datatypes4bool02".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma size_classes_length : length size_classes = 48%nat.
Proof. reflexivity. Qed.

Lemma size_classes_bounds : Forall (fun x => 1 <= x <= 8191) size_classes.
Proof.
  apply Forall_forall. intros x Hx. unfold size_classes in Hx.
  repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx.
Qed.

Lemma size_class_bound sc : 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros H. unfold size_class.
  apply (Forall_forall (fun x => 1 <= x <= 8191) size_classes); [apply size_classes_bounds|].
  apply nth_In. rewrite size_classes_length. lia.
Qed.

(* [comment removed for export] *)
Lemma mask_upto_nonneg k : 0 <= k -> 0 <= mask_upto k.
Proof. intros. unfold mask_upto. assert (0 < 2 ^ (k + 1)) by (apply Z.pow_pos_nonneg; lia). lia. Qed.

Lemma testbit_mask_upto k i : 0 <= k -> 0 <= i -> Z.testbit (mask_upto k) i = (i <=? k).
Proof.
  intros Hk Hi. unfold mask_upto. replace (2 ^ (k + 1) - 1) with (Z.pred (2 ^ (k + 1))) by lia.
  rewrite <- Z.ones_equiv. destruct (Z.leb_spec i k).
  - apply Z.ones_spec_low. lia.
  - apply Z.ones_spec_high. lia.
Qed.

Lemma testbit_bit i j : 0 <= i -> 0 <= j -> Z.testbit (bit i) j = (i =? j).
Proof.
  intros Hi Hj. unfold bit. destruct (Z.eqb_spec i j) as [<-|NE].
  - apply Z.pow2_bits_true. exact Hi.
  - apply Z.pow2_bits_false. lia.
Qed.

Lemma bits_below_bound n a : 0 <= a -> 0 <= n -> (forall i, 0 <= i -> Z.testbit a i = true -> i < n) -> a < 2 ^ n.
Proof.
  intros Ha Hn Hb. destruct (Z.lt_ge_cases a (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
  assert (Hl : n <= Z.log2 a) by (apply Z.log2_le_pow2; lia).
  assert (Ht : Z.testbit a (Z.log2 a) = true) by (apply Z.bit_log2; lia).
  specialize (Hb (Z.log2 a) ltac:(apply Z.log2_nonneg) Ht). lia.
Qed.

Lemma testbit_false_above n a i : 0 <= a < 2 ^ n -> n <= i -> Z.testbit a i = false.
Proof.
  intros Ha Hi. destruct (Z.eq_dec a 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
  apply (Z.lt_le_trans _ (2 ^ n)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
