(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (29 recorded proofs replaced by written proofs (Zrange_forallb, digit_testb, digit_test and 26 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FmtFp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Printf_zfacts () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallI47Corelib4Init9Datatypes4list00C47Corelib5Lists7ListDef3mapI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega6VarMap1t01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib5Lists4List8map_consC46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib6Common<Printf_model8is_digitC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool3eqbc59OSSVerify5KrLib5Plain=Printf_zfacts>Zrange_forallbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=Printf_zfacts;digit_testbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9leb_spec0I47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7compareC47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03C47Corelib4Init9Datatypes4andbC47Corelib7Classes9Morphisms?eq_proper_proxyC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismK46Stdlib9micromega5Tauto8GFormula09C47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses=iff_ReflexiveC56Stdlib6ZArith6BinInt1Z3ltbc59OSSVerify5KrLib5Plain=Printf_zfacts8sp_testbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0c59OSSVerify5KrLib5Plain=Printf_zfacts5flagwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib6Common<Printf_model8flag_bitC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5Plain=Printf_zfacts:flag_nonebC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specK47Corelib4Init9Datatypes6option01C57Corelib7BinNums6IntDef1Z4landc59OSSVerify5KrLib5Plain=Printf_zfacts:flag_somebC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib7Program6Basics4implC56Stdlib6ZArith6BinInt1Z6shiftlC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib6Common<Printf_model8FLAGMASKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z7lor_0_lC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z9log2_pow2C56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib6Common<Printf_model;parse_flagsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc59OSSVerify5KrLib5Plain=Printf_zfacts>flag_bit_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=Printf_zfacts9flag_someC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=Printf_zfacts;lor_bound17C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib6Common<Printf_model6getintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z6ltb_gec59OSSVerify5KrLib5Plain=Printf_zfacts;digit_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4xorbC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC46Stdlib4Bool4Bool;andb_true_rC46Stdlib4Bool4Bool;xorb_true_rC56Stdlib6ZArith6BinInt1Z=ones_spec_lowC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C46Stdlib4Bool4Bool<andb_false_rC46Stdlib4Bool4Bool<xorb_false_rC56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z9lnot_specC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9lxor_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z4predK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z:shiftl_1_lC59OSSVerify5KrLib6Common<Printf_model9parse_dirC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model3d_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_xpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model3d_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model9conv_typeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model3dir01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_flC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C59OSSVerify5KrLib6Common<Printf_model4d_tyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model3d_wC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model3dir00C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib4Bool4Bool<orb_true_iffK46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto4kind02C59OSSVerify5KrLib6Common<Printf_model5T_PTRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model5T_INTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model6T_UINTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model5T_DBLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim4znthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=Printf_zfacts7STATES0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=Printf_zfacts;nzmask_bitsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegC56Stdlib6ZArith8Zbitwise1Z?sub_land_same_l".
Import ListNotations.
Open Scope Z_scope.

Lemma Zrange_forallb : forall (P : Z -> bool) (lo : Z) (n : nat),
  forallb P (map (fun k => lo + Z.of_nat k) (seq 0 n)) = true ->
  forall c, lo <= c < lo + Z.of_nat n -> P c = true.
Proof.
  intros P lo n H c Hc. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat (c - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Notation M64 := 18446744073709551615.

(* [comment removed for export] *)
Lemma digit_testb : forall c, 0 <= c < 0 + Z.of_nat 256 ->
  Bool.eqb (Z.land (c + -48) M64 <=? 9) (is_digit c) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma digit_test : forall c, 0 <= c < 256 -> (Z.land (c + -48) M64 <= 9 <-> is_digit c = true).
Proof.
  intros c Hc. pose proof (digit_testb c ltac:(cbn; lia)) as E.
  destruct (Z.leb_spec0 (Z.land (c + -48) M64) 9); destruct (is_digit c); cbn in E; try discriminate.
  all: split; intros; first [reflexivity | assumption | discriminate | lia].
Qed.
Lemma digit_range : forall c, is_digit c = true <-> 48 <= c <= 57.
Proof. intros c. unfold is_digit. rewrite andb_true_iff, !Z.leb_le. lia. Qed.

(* [comment removed for export] *)
Lemma sp_testb : forall c, 0 <= c < 0 + Z.of_nat 256 ->
  Bool.eqb (Z.land (c + -32) M64 <? 32) ((32 <=? c) && (c <? 64)) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma sp_test : forall c, 0 <= c < 256 -> (Z.land (c + -32) M64 < 32 <-> 32 <= c < 64).
Proof.
  intros c Hc. pose proof (sp_testb c ltac:(cbn; lia)) as E.
  destruct (Z.ltb_spec0 (Z.land (c + -32) M64) 32); destruct (Z.leb_spec0 32 c); destruct (Z.ltb_spec0 c 64); cbn in E; try discriminate; lia.
Qed.

(* [comment removed for export] *)
Definition flagw (c : Z) : Z := Z.land (bv_swrap 32 (Z.shiftl 1 ((c + -32) mod 32))) M64.

Lemma flag_noneb : forall c, 32 <= c < 32 + Z.of_nat 32 ->
  Bool.eqb (Z.land (flagw c) 75913 =? 0) (match flag_bit c with None => true | Some _ => false end) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma flag_none : forall c, 32 <= c < 64 -> (Z.land (flagw c) 75913 = 0 <-> flag_bit c = None).
Proof.
  intros c Hc. pose proof (flag_noneb c ltac:(cbn; lia)) as E.
  destruct (Z.eqb_spec (Z.land (flagw c) 75913) 0); destruct (flag_bit c); cbn in E; try discriminate.
  all: split; intros; first [reflexivity | assumption | discriminate | congruence | lia].
Qed.
Lemma flag_someb : forall c, 32 <= c < 32 + Z.of_nat 32 ->
  match flag_bit c with None => true | Some b => (flagw c =? b) && (0 <=? b) && (b <? 131072) end = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma flag_some : forall c b, 32 <= c < 64 -> flag_bit c = Some b -> flagw c = b /\ 0 <= b < 131072.
Proof.
  intros c b Hc Hb. pose proof (flag_someb c ltac:(cbn; lia)) as E. rewrite Hb in E.
  rewrite !andb_true_iff in E. destruct E as [[E1 E2] E3]. apply Z.eqb_eq in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3. lia.
Qed.
Lemma flag_bit_range : forall c, flag_bit c <> None -> 32 <= c < 64.
Proof.
  intros c H. unfold flag_bit in H.
  destruct (Z.leb_spec0 32 c); destruct (Z.ltb_spec0 c 64); cbn in H; try lia; exfalso; apply H; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lor_bound17 : forall a b, 0 <= a < 131072 -> 0 <= b < 131072 -> 0 <= Z.lor a b < 131072.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  change 131072 with (2^17) in *.
  destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|]; [rewrite Z.lor_0_r; lia|].
  apply Z.log2_lt_cancel. rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Lemma parse_flags_cons_some : forall c s fl b, flag_bit c = Some b -> parse_flags (c :: s) fl = parse_flags s (Z.lor fl b).
Proof. intros c s fl b H. cbn. rewrite H. reflexivity. Qed.
Lemma parse_flags_cons_none : forall c s fl, flag_bit c = None -> parse_flags (c :: s) fl = (fl, c :: s).
Proof. intros c s fl H. cbn. rewrite H. reflexivity. Qed.
Lemma parse_flags_range : forall s fl, 0 <= fl < 131072 -> 0 <= fst (parse_flags s fl) < 131072.
Proof.
  induction s as [|c s IH]; intros fl Hfl; cbn; [exact Hfl|].
  destruct (flag_bit c) as [b|] eqn:E; [|exact Hfl].
  apply IH. pose proof (flag_some c b (flag_bit_range c ltac:(congruence)) E) as [_ Hb]. apply lor_bound17; lia.
Qed.

(* [comment removed for export] *)
Lemma getint_cons_digit : forall c s i, is_digit c = true ->
  getint (c :: s) i = if (214748364 <? i) || (INT_MAX - 10 * i <? c - 48) then None else getint s (10 * i + (c - 48)).
Proof. intros c s i H. cbn [getint]. rewrite H. reflexivity. Qed.
Lemma getint_cons_nondigit : forall c s i, is_digit c = false -> getint (c :: s) i = Some (i, c :: s).
Proof. intros c s i H. cbn [getint]. rewrite H. reflexivity. Qed.
Lemma getint_some_range : forall s i w s', 0 <= i <= INT_MAX -> getint s i = Some (w, s') -> 0 <= w <= INT_MAX.
Proof.
  induction s as [|c s IH]; intros i w s' Hi H; cbn [getint] in H.
  - inversion H; subst. exact Hi.
  - destruct (is_digit c) eqn:D.
    + destruct (214748364 <? i) eqn:E1; [discriminate|]. destruct (INT_MAX - 10 * i <? c - 48) eqn:E2; [discriminate|]. cbn in H.
      apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. apply digit_range in D. unfold INT_MAX in *. eapply IH; [|exact H]. lia.
    + inversion H; subst. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma lxor_imax : forall x, 0 <= x <= 2147483647 -> Z.lxor x 2147483647 = 2147483647 - x.
Proof.
  intros x Hx. change 2147483647 with (Z.ones 31).
  assert (E : Z.lxor x (Z.ones 31) = (Z.lnot x) mod 2^31).
  { rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases i 31).
    - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
      destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 31; [apply Z.log2_lt_pow2; cbn in *; lia|lia]. }
  rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2^31)) with (2^31 - 1).
  replace (Z.lnot x) with (-x - 1) by (unfold Z.lnot; lia).
  rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by (cbn in *; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma parse_dir_shape : forall s d rest, parse_dir s = Some (d, rest) ->
  match s with c0 :: c0b :: _ => is_digit c0 && (c0b =? 36) = false | [c0] => is_digit c0 = false | [] => True end /\
  let (fl, s1) := parse_flags s 0 in
  d_fl d = fl /\
  exists c1 s1b, s1 = c1 :: s1b /\ c1 <> 42 /\
  exists s2, getint s1 0 = Some (d_w d, s2) /\
  exists c2 s2b, s2 = c2 :: s2b /\
  ( (c2 <> 46 /\ d_p d = -1 /\ d_xp d = false /\ d_t d = c2 /\ rest = s2b /\ conv_type c2 = Some (d_ty d))
  \/ (c2 = 46 /\ d_xp d = true /\ exists c3 s3b, s2b = c3 :: s3b /\ c3 <> 42 /\
      exists s3, getint s2b 0 = Some (d_p d, s3) /\ s3 = d_t d :: rest /\ conv_type (d_t d) = Some (d_ty d)) ).
Proof.
  intros s d rest H. unfold parse_dir in H.
  split. { destruct s as [|c0 [|c0b s0]]; try exact I. { destruct (is_digit c0); [discriminate|reflexivity]. } destruct (is_digit c0 && (c0b =? 36)); [discriminate|reflexivity]. }
  match type of H with (if ?pp then None else _) = _ => destruct pp; [discriminate|] end.
  destruct (parse_flags s 0) as [fl s1].
  destruct s1 as [|c1 s1b]; [discriminate|].
  destruct (Z.eqb_spec c1 42) as [E42|N42]; [discriminate|].
  destruct (getint (c1 :: s1b) 0) as [[w s2]|] eqn:G; [|discriminate].
  destruct s2 as [|c2 s2b]; [discriminate|].
  destruct (Z.eqb_spec c2 46) as [E46|N46].
  - destruct s2b as [|c3 s3b]; [discriminate|]. destruct (Z.eqb_spec c3 42) as [E42'|N42']; [discriminate|].
    destruct (getint (c3 :: s3b) 0) as [[p s3]|] eqn:G2; [|discriminate].
    destruct s3 as [|t s4]; [discriminate|]. destruct (conv_type t) as [ty|] eqn:CT; [|discriminate].
    injection H as <- <-. cbn. split; [reflexivity|]. exists c1, s1b. split; [reflexivity|]. split; [exact N42|].
    exists (c2 :: c3 :: s3b). split; [first [reflexivity | exact G]|]. exists c2, (c3 :: s3b). split; [reflexivity|].
    right. split; [exact E46|]. split; [reflexivity|]. exists c3, s3b. split; [reflexivity|]. split; [exact N42'|].
    exists (t :: s4). split; [first [reflexivity | exact G2]|]. split; first [reflexivity | exact CT].
  - destruct (conv_type c2) as [ty|] eqn:CT; [|discriminate]. injection H as <- <-. cbn.
    split; [reflexivity|]. exists c1, s1b. split; [reflexivity|]. split; [exact N42|].
    exists (c2 :: s2b). split; [first [reflexivity | exact G]|]. exists c2, s2b. split; [reflexivity|].
    left. split; [exact N46|]. repeat split; first [reflexivity | exact CT].
Qed.

(* [comment removed for export] *)
Lemma parse_flags_suffix : forall s acc fl s1, parse_flags s acc = (fl, s1) -> exists n, s1 = skipn n s /\ (n <= length s)%nat.
Proof.
  induction s as [|c s IH]; intros acc fl s1 H; cbn in H.
  - injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
  - destruct (flag_bit c) as [b|].
    + destruct (IH _ _ _ H) as (n & -> & Hn). exists (S n). split; [reflexivity | cbn; lia].
    + injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
Qed.
Lemma getint_suffix : forall s acc w s1, getint s acc = Some (w, s1) -> exists n, s1 = skipn n s /\ (n <= length s)%nat.
Proof.
  induction s as [|c s IH]; intros acc w s1 H; cbn [getint] in H.
  - injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
  - destruct (is_digit c).
    + destruct (_ || _); [discriminate|]. destruct (IH _ _ _ H) as (n & -> & Hn). exists (S n). split; [reflexivity | cbn; lia].
    + injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)
Definition STATES0 : list Z :=
  [25; 0; 11; 0; 25; 25; 25; 0; 0; 0; 0; 5; 0; 0; 0; 0; 0; 0; 9; 0; 0; 0; 0; 11; 0; 0; 0; 0; 0; 0; 0; 0; 25; 0; 10; 10; 25; 25; 25; 3; 10; 7; 0; 1; 27; 9; 11; 24; 0; 0; 9; 6; 11; 0; 0; 11; 0; 6].
Lemma conv_type_range : forall t ty, conv_type t = Some ty -> 65 <= t <= 122.
Proof.
  intros t ty H. unfold conv_type in H.
  repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?; [try (injection H as <-)|] end; try discriminate;
  repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] end; try lia.
Qed.
Lemma states0_conv : forall t ty, conv_type t = Some ty -> znth STATES0 (t - 65) = ty.
Proof.
  intros t ty H. unfold conv_type in H.
  repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?; [injection H as <-|] end; try discriminate;
  repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E; subst; reflexivity | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] end.
Qed.
(* [comment removed for export] *)
Definition conv_target (t : Z) : Z :=
  if t =? 115 then 0x207cc
  else if (t =? 100) || (t =? 105) then 0x20784
  else if t =? 117 then 0x208bc
  else if (t =? 120) || (t =? 88) then 0x20934
  else 0x20734.

Lemma conv_type_ty : forall t ty, conv_type t = Some ty -> ty = 9 \/ ty = 10 \/ ty = 11 \/ ty = 25.
Proof.
  intros t ty H. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in H.
  repeat match type of H with (if ?c then _ else _) = _ => destruct c; [injection H as <-; lia|] end. discriminate.
Qed.

Lemma land_M64_neg : forall x, - 2^64 <= x < 0 -> Z.land x 18446744073709551615 = x + 2^64.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma nzmask_bits : forall n, 0 <= n < 0 + Z.of_nat 64 -> Bool.eqb (Z.testbit 18446744073709486079 n) (negb (Z.testbit 65536 n)) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma nzmask_eq : forall fl, 0 <= fl < 131072 -> Z.land fl 18446744073709486079 = Z.land fl (Z.lnot 65536).
Proof.
  intros fl Hfl. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases n 64).
  - pose proof (nzmask_bits n ltac:(cbn; lia)) as E. destruct (Z.testbit 18446744073709486079 n), (Z.testbit 65536 n); cbn in E; try discriminate; reflexivity.
  - replace (Z.testbit fl n) with false; [reflexivity|]. symmetry.
    destruct (Z.eq_dec fl 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
    apply Z.lt_le_trans with 17%Z; [apply Z.log2_lt_pow2; cbn in *; lia|lia].
Qed.
Lemma land_bound : forall a m, 0 <= a -> 0 <= m -> 0 <= Z.land a m <= a.
Proof.
  intros a m Ha Hm. split; [apply Z.land_nonneg; left; exact Ha|].
  pose proof (Z.sub_land_same_l a m) as E.
  assert (0 <= Z.land a (Z.lnot m))%Z by (apply Z.land_nonneg; left; exact Ha).
  lia.
Qed.
