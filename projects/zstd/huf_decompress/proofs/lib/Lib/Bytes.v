(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (21 recorded proofs replaced by written proofs (le_val_range, split_mod, testbit_split and 18 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Bytes () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib3Lib5Bytes8bytes_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Bytes6le_valC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indI47Corelib5Lists7ListDef6Forall00C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z:pow_succ_rC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1N01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7add_0_lC56Stdlib6ZArith6BinInt1Z9div_smallK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_addC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z9rem_mul_rK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC47Corelib4Init5Logic3notK46Stdlib9micromega7EnvRing5PExpr04C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z=div_pow2_bitsC56Stdlib6ZArith6BinInt1Z;le_gt_casesI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z9pow_neg_rC56Stdlib6ZArith6BinInt1Z;land_nonnegC56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z8land_0_lC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z9log2_landC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC47Corelib4Init5Logic5proj2K47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula09I47Corelib4Init9Datatypes:comparison00C56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z<lor_eq_0_iffC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorK47Corelib7Numbers7BinNums1N02c59OSSVerify5KrLib3Lib5Bytes<land_lt_pow2C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z9land_specc59OSSVerify5KrLib3Lib5Bytes=testbit_splitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9bits_inj'c59OSSVerify5KrLib3Lib5Bytes;lor_lt_pow2C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z8lor_specK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6eqb_eqI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04I47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqK47Corelib4Init5Logic2ex01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib5Lists4List8map_consc59OSSVerify5KrLib3Lib5Bytes4onesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Bytes5highsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01c59OSSVerify5KrLib3Lib5Bytes:land_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Bytes9split_modC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c59OSSVerify5KrLib3Lib5Bytes:byte_fact1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Bytes:lnot_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Bytes7ONES64bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Bytes8HIGHS64bC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z;lt_ge_casesc59OSSVerify5KrLib3Lib5BytesBtestbit_high_falseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4lxorC47Corelib4Init9Datatypes4xorbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool;andb_true_rC46Stdlib4Bool4Bool;xorb_true_rC56Stdlib6ZArith6BinInt1Z=ones_spec_lowC46Stdlib4Bool4Bool<andb_false_rC46Stdlib4Bool4Bool<xorb_false_rC56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z9lnot_specC56Stdlib6ZArith6BinInt1Z9lxor_specC56Stdlib6ZArith6BinInt1Z9land_onesc59OSSVerify5KrLib3Lib5Bytes<le_val_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Bytes;haszero_iffC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffc59OSSVerify5KrLib3Lib5Bytes?land_mod_pow2_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Bytes:lnot_mod64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Bytes6ones_8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Bytes7highs_8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4predc59OSSVerify5KrLib3Lib5Bytes>demorgan_highsC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveC56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z8lxor_lorC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib5Lists7ListDef6Forall01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK47Corelib5Lists7ListDef6Forall02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_Zc59OSSVerify5KrLib3Lib5Bytes<bytes_ok_mapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Bytes?lor_shiftl8_addC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions7bv_wrapC46Stdlib5Lists4List:length_mapC45stdpp9bitvector;definitions=bv_wrap_smallc59OSSVerify5KrLib3Lib5BytesDbytes_le_to_Z_le_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitions:bv_extractC45stdpp9bitvector;definitionsCbv_extract_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions5bv_eqI47Corelib7Numbers7BinNums1N00".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint le_val (bs : list Z) : Z :=
  match bs with [] => 0 | b :: bs' => b + 256 * le_val bs' end.
Fixpoint ones (n : nat) : Z := match n with O => 0 | S n' => 1 + 256 * ones n' end.
Definition highs (n : nat) : Z := 128 * ones n.
Definition bytes_ok (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.

Lemma le_val_range : forall bs, bytes_ok bs -> 0 <= le_val bs < 256 ^ Z.of_nat (length bs).
Proof.
  induction bs as [|b bs IH]; intros H; cbn [le_val length]; [lia|].
  inversion H; subst. specialize (IH ltac:(assumption)).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma split_mod : forall x y M, 0 <= x < 256 -> 0 < M -> (x + 256 * y) mod (256 * M) = x + 256 * (y mod M).
Proof.
  intros x y M Hx HM. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia.
  rewrite Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.

Lemma testbit_split : forall x y i, 0 <= x < 256 -> 0 <= i ->
  Z.testbit (x + 256 * y) i = if i <? 8 then Z.testbit x i else Z.testbit y (i - 8).
Proof.
  intros x y i Hx Hi. destruct (Z.ltb_spec0 i 8).
  - rewrite <- (Z.mod_pow2_bits_low _ 8) by lia. change (2^8) with 256.
    rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia. reflexivity.
  - replace i with ((i - 8) + 8) at 1 by lia. rewrite <- Z.div_pow2_bits by lia. change (2^8) with 256.
    rewrite (Z.mul_comm 256 y), Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.

Lemma land_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b -> 0 <= Z.land a b < 2^n.
Proof.
  intros a b n Ha Hb.
  assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  pose proof (Z.land_nonneg a b) as Hnn. split; [lia|].
  destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]. { apply Z.pow_pos_nonneg; lia. }
  destruct (Z.eq_dec a 0) as [->|Haz]. { rewrite Z.land_0_l. apply Z.pow_pos_nonneg; lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.land a b) n ltac:(lia))).
  pose proof (Z.log2_land a b ltac:(lia) Hb). assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma lor_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros a b n Ha Hb.
  assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  pose proof (Z.lor_nonneg a b) as Hnn. split; [lia|].
  destruct (Z.eq_dec a 0) as [->|]. { rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0) as [->|]. { rewrite Z.lor_0_r. lia. }
  assert (Hp : 0 < Z.lor a b). { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n Hp)). rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 ->
  Z.land (x + 256 * y) (x' + 256 * y') = Z.land x x' + 256 * Z.land y y'.
Proof.
  intros x y x' y' Hx Hx'.
  pose proof (land_lt_pow2 x x' 8 ltac:(cbn; lia) ltac:(lia)) as Hl. change (2^8) with 256 in Hl.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !testbit_split by lia.
  destruct (i <? 8); rewrite Z.land_spec; reflexivity.
Qed.

Lemma lor_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 ->
  Z.lor (x + 256 * y) (x' + 256 * y') = Z.lor x x' + 256 * Z.lor y y'.
Proof.
  intros x y x' y' Hx Hx'.
  pose proof (lor_lt_pow2 x x' 8 ltac:(cbn; lia) ltac:(cbn; lia)) as Hl. change (2^8) with 256 in Hl.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, !testbit_split by lia.
  destruct (i <? 8); rewrite Z.lor_spec; reflexivity.
Qed.

Lemma lnot_split : forall b w, Z.lnot (b + 256 * w) = (255 - b) + 256 * Z.lnot w.
Proof. intros. unfold Z.lnot. lia. Qed.

(* [comment removed for export] *)
Lemma byte_fact1 : forall b, 1 <= b < 256 -> Z.land (Z.land (b - 1) (255 - b)) 128 = 0.
Proof.
  intros b Hb.
  assert (C : forallb (fun b => Z.land (Z.land (b - 1) (255 - b)) 128 =? 0) (map Z.of_nat (seq 1 255)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. apply Z.eqb_eq, C. apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.

Theorem haszero_iff : forall bs, bytes_ok bs ->
  let n := length bs in let w := le_val bs in
  Z.land (Z.land ((w - ones n) mod 256 ^ Z.of_nat n) (Z.lnot w)) (highs n) <> 0 <-> In 0 bs.
Proof.
  induction bs as [|b bs IH]; intros H; cbn [length le_val ones highs].
  - cbn. split; [|intros []]. intros C; apply C. reflexivity.
  - inversion H as [|b' bs' Hb Hbs]; subst. specialize (IH Hbs). cbn zeta in IH.
    unfold highs in *. cbn [ones].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (Z.pow_pos_nonneg 256 (Z.of_nat (length bs)) ltac:(lia) ltac:(lia)) as HM.
    rewrite lnot_split.
    replace (128 * (1 + 256 * ones (length bs))) with (128 + 256 * (128 * ones (length bs))) by lia.
    destruct (Z.eq_dec b 0) as [->|Hb0].
    + replace (0 + 256 * le_val bs - (1 + 256 * ones (length bs))) with (255 + 256 * (le_val bs - ones (length bs) - 1)) by lia.
      rewrite split_mod by lia. rewrite land_split by lia. change (Z.land 255 (255 - 0)) with 255.
      rewrite land_split by lia. change (Z.land 255 128) with 128.
      split; [intros; left; reflexivity| intros _]. lia.
    + replace (b + 256 * le_val bs - (1 + 256 * ones (length bs))) with ((b - 1) + 256 * (le_val bs - ones (length bs))) by lia.
      rewrite split_mod by lia.
      rewrite land_split by lia.
      rewrite land_split. 2:{ pose proof (land_lt_pow2 (b-1) (255-b) 8 ltac:(cbn; lia) ltac:(lia)). cbn in *. lia. }
      2:{ lia. }
      rewrite byte_fact1 by lia.
      split.
      * intros Hnz. right. apply IH. lia.
      * intros [Hz|Hin]; [lia|]. apply IH in Hin. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ONES64b  : Z := 0x0101010101010101.
Definition HIGHS64b : Z := 0x8080808080808080.

Lemma ones_8 : ones 8 = ONES64b.
Proof.
ltac2:(KReplay.run1 (kr_t_Bytes ()) [] "p;2g008Tj20Tg00T[g01`a'0o"). Qed.
Lemma highs_8 : highs 8 = HIGHS64b.
Proof.
ltac2:(KReplay.run1 (kr_t_Bytes ()) [] "p;2g008Tj20Tg00T[g01aW'0o"). Qed.

Lemma testbit_high_false : forall x n i, 0 <= x < 2^n -> 0 <= n <= i -> Z.testbit x i = false.
Proof.
  intros x n i Hx Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with n; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma land_mod_pow2_r : forall a b n, 0 <= a < 2^n -> 0 <= n -> Z.land a (b mod 2^n) = Z.land a b.
Proof.
  intros a b n Ha Hn. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i n).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite (testbit_high_false a n i) by lia. reflexivity.
Qed.

Lemma lnot_mod64 : forall w, 0 <= w < 2^64 -> Z.lxor w 18446744073709551615 = (Z.lnot w) mod 2^64.
Proof.
  intros w Hw. change 18446744073709551615 with (Z.ones 64). rewrite <- Z.land_ones by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
    destruct (Z.eq_dec w 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.

(* [comment removed for export] *)
Theorem haszero64_gcc : forall bs, bytes_ok bs -> length bs = 8%nat ->
  let w := le_val bs in
  Z.land (Z.land ((w + 18374403900871474943) mod 18446744073709551616) (Z.lxor w 18446744073709551615)) 9259542123273814144 = 0
  <-> ~ In 0 bs.
Proof.
  intros bs Hok Hlen w. change 18446744073709551616 with (2^64).
  pose proof (le_val_range bs Hok) as Hw. rewrite Hlen in Hw. change (256 ^ Z.of_nat 8) with (2^64) in Hw.
  pose proof (haszero_iff bs Hok) as HZ. rewrite Hlen in HZ. cbn zeta in HZ. fold w in HZ, Hw.
  change (256 ^ Z.of_nat 8) with (2^64) in HZ. rewrite ones_8, highs_8 in HZ. unfold ONES64b, HIGHS64b in HZ.
  replace ((w + 18374403900871474943) mod 2 ^ 64) with ((w - 72340172838076673) mod 2^64).
  2:{ replace (w + 18374403900871474943) with ((w - 72340172838076673) + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity. }
  rewrite lnot_mod64 by lia. rewrite land_mod_pow2_r by (try lia; apply Z.mod_pos_bound; lia).
  (* [comment removed for export] *)
  destruct HZ as [HZ1 HZ2]. split.
  - intros E I. apply HZ2 in I. apply I. exact E.
  - intros NI. match goal with |- ?x = 0 => destruct (Z.eq_dec x 0) as [E|NE] end; [assumption|].
    exfalso. apply NI. apply HZ1. exact NE.
Qed.

(* [comment removed for export] *)
Lemma demorgan_highs : forall D w H, 0 <= D < 2^64 -> 0 <= w < 2^64 -> 0 <= H < 2^64 ->
  Z.land (Z.lor (Z.lxor D 18446744073709551615) w) H = H <-> Z.land (Z.land D (Z.lnot w)) H = 0.
Proof.
  intros D w H HD Hw HH. change 18446744073709551615 with (Z.ones 64).
  assert (HI : forall x, 0 <= x < 2^64 -> forall i, 64 <= i -> Z.testbit x i = false).
  { intros x Hx i Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia]. }
  split; intros E; apply Z.bits_inj'; intros i Hi.
  - rewrite Z.bits_0, !Z.land_spec, Z.lnot_spec by lia.
    apply (f_equal (fun x => Z.testbit x i)) in E. rewrite Z.land_spec, Z.lor_spec, Z.lxor_spec in E.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.ones_spec_low in E by lia.
      destruct (Z.testbit D i), (Z.testbit w i), (Z.testbit H i); cbn in *; congruence.
    + rewrite (HI D) by lia. reflexivity.
  - apply (f_equal (fun x => Z.testbit x i)) in E. rewrite Z.bits_0, !Z.land_spec, Z.lnot_spec in E by lia.
    rewrite Z.land_spec, Z.lor_spec, Z.lxor_spec.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.ones_spec_low by lia.
      destruct (Z.testbit D i), (Z.testbit w i), (Z.testbit H i); cbn in *; congruence.
    + rewrite (HI H) by lia. apply andb_false_r.
Qed.

Theorem haszero64_clang : forall bs, bytes_ok bs -> length bs = 8%nat ->
  let w := le_val bs in
  Z.land (Z.lor ((72340172838076672 - w) mod 18446744073709551616) w) 9259542123273814144 = 9259542123273814144
  <-> ~ In 0 bs.
Proof.
  intros bs Hok Hlen w. change 18446744073709551616 with (2^64).
  pose proof (le_val_range bs Hok) as Hw. rewrite Hlen in Hw. change (256 ^ Z.of_nat 8) with (2^64) in Hw.
  pose proof (haszero_iff bs Hok) as HZ. rewrite Hlen in HZ. cbn zeta in HZ. fold w in HZ, Hw.
  change (256 ^ Z.of_nat 8) with (2^64) in HZ. rewrite ones_8, highs_8 in HZ. unfold ONES64b, HIGHS64b in HZ.
  set (D := (w - 72340172838076673) mod 2 ^ 64) in HZ.
  assert (HD : 0 <= D < 2^64) by (apply Z.mod_pos_bound; lia).
  replace ((72340172838076672 - w) mod 2 ^ 64) with (Z.lxor D 18446744073709551615).
  2:{ rewrite lnot_mod64 by lia. unfold Z.lnot. subst D. Z.div_mod_to_equations. lia. }
  rewrite demorgan_highs by lia.
  (* [comment removed for export] *)
  destruct HZ as [HZ1 HZ2]. split.
  - intros E I. apply HZ2 in I. apply I. exact E.
  - intros NI. match goal with |- ?x = 0 => destruct (Z.eq_dec x 0) as [E|NE] end; [assumption|].
    exfalso. apply NI. apply HZ1. exact NE.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lor_shiftl8_add : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (Z.shiftl y 8) = x + 256 * y.
Proof.
  intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
  rewrite <- Z.lxor_lor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
       replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
       destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
       rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
       destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia]. }
  symmetry. replace (256 * y) with (y * 256) by lia. apply Z.add_nocarry_lxor.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
  destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
  rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
  destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma bytes_ok_map : forall bs : list byte, bytes_ok (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
Qed.

Lemma bytes_le_to_Z_le_val : forall bs : list byte, bytes_le_to_Z bs = le_val (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z le_val map]; [reflexivity|].
  rewrite IH. apply lor_shiftl8_add.
  - pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
  - pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)). lia.
Qed.

(* [comment removed for export] *)
Lemma load8_le_val : forall bs : list byte, length bs = 8%nat ->
  bv_unsigned (bv_extract 0 64 (le_bytes_to_word bs)) = le_val (map bv_unsigned bs).
Proof.
  intros bs Hlen. unfold le_bytes_to_word. rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
  rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr. rewrite length_map, Hlen in Hr.
  change (256 ^ Z.of_nat 8) with (2^64) in Hr.
  rewrite (bv_wrap_small 64 (le_val _)) by (change (bv_modulus 64) with (2^64); lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64); lia.
Qed.

Lemma In0_map_unsigned : forall bs : list byte, In 0 (map bv_unsigned bs) <-> In (Z_to_bv 8 0) bs.
Proof.
  intros bs. rewrite in_map_iff. split.
  - intros (b & Hb & Hin). replace (Z_to_bv 8 0) with b; [exact Hin|]. apply bv_eq. rewrite Hb. reflexivity.
  - intros Hin. exists (Z_to_bv 8 0). split; [reflexivity|exact Hin].
Qed.
