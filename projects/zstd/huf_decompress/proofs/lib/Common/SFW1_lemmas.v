(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (79 recorded proofs replaced by written proofs (zb_land_pow2_bit0, zb_lxor_pow2, zb_lxor_b31 and 76 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Export SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_SFW1_lemmas () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z7testbitK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic3notC46Stdlib4Bool4Bool<andb_false_rK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z<testbit_trueC47Corelib4Init5Logic5proj1C47Corelib4Init9Datatypes4xorbC56Stdlib6ZArith6BinInt1Z>pow2_bits_trueC56Stdlib6ZArith6BinInt1Z9lxor_specc59OSSVerify5KrLib6Common;SFW1_lemmasAzb_land_pow2_bit0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z:lxor_assocC56Stdlib6ZArith6BinInt1Z>lxor_nilpotentC56Stdlib6ZArith6BinInt1Z8lxor_0_rK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z=testbit_falseK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib6Common;SFW1_lemmas<zb_lxor_pow2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions8bv_swrapc59OSSVerify5KrLib6Common;SFW1_lemmas:swrap32_eqC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega:ZMicromega;ZArithProof04C59OSSVerify5KrLib3Lib7ZBridge<zb_land_maskC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib6Common9SoftFloat6wrap64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat:wrap64_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6sext32C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00c59OSSVerify5KrLib6Common;SFW1_lemmas9sext32_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SFModel8land_W64C1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib7ZBridge>Z_to_bv_land64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmasCland_swrap32_sext32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC56Stdlib6ZArith6BinInt1Z7mod_modC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z9rem_mul_rc59OSSVerify5KrLib6Common;SFW1_lemmas<sext32_mod32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6zext32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas9zext32_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas:sext32_lowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrK46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c59OSSVerify5KrLib6Common;SFW1_lemmas<sext32_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5srliwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat3M32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8le_transc59OSSVerify5KrLib6Common;SFW1_lemmas=swrap32_smallC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapc59OSSVerify5KrLib6Common;SFW1_lemmas<bv_wrap32_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas?land_mask_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z9pow_add_rc59OSSVerify5KrLib6Common;SFW1_lemmas;zb_lxor_b31C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib6Common9SoftFloat5not64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5sub64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5add64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5mul64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas<sext32_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat<clz32_mirrorC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_dividec59OSSVerify5KrLib6Common;SFW1_lemmas:land63_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas>land63_congr32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas>gcc_sext_low32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas=zext32_sext32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge<zb_lxor_onesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?mul_mod_distr_rC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2c59OSSVerify5KrLib6Common;SFW1_lemmas;shl48_congrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z9leb_spec0C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib7ZBridge9zb_signedC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z9lt_succ_rC56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1Z;le_antisymmC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z?shiftl_spec_lowC46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z=ones_spec_lowC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z?bits_above_log2C56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z;shiftr_specC56Stdlib6ZArith6BinInt1Z@shiftl_spec_highC59OSSVerify5KrLib3Lib7ZBridge:zb_shr_shlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmasAland_signmask_shlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge7zr_wordC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge5inr64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas;srai63_wordC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8sub_diagc59OSSVerify5KrLib6Common;SFW1_lemmas=land_signmaskC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9lxor_commC59OSSVerify5KrLib6Common7SFModel6land_1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat<wrap64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat<clz64_mirrorC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_1_rC56Stdlib6ZArith6BinInt1Z7mul_0_rc59OSSVerify5KrLib6Common;SFW1_lemmas<zb_land_pow2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_commC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z8lor_specC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z;lxor_nonnegC56Stdlib6ZArith6BinInt1Z=lxor_eq_0_iffC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC46Stdlib4Bool4Bool>eq_true_iff_eqC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC59OSSVerify5KrLib6Common9SoftFloat4lo64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_addC59OSSVerify5KrLib6Common9SoftFloat4hi64C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib6Common9SoftFloat5shl64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat;trunc_roundC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib6Common9SoftFloat5eqz64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6lt_s64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat8is_neg64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5nez64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5sra63C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas9to_d_coreC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas9to_d_packC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas:hi64_wordsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas:lo64_wordsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat9f128_to_dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6DQUIETC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas;to_d_pack_gC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas9signbit63C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;SFW1_lemmas?f128_to_d_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SFModel>land_even_maskC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3b2zc59OSSVerify5KrLib6Common;SFW1_lemmas>land_W64_smallC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison03C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z7div_div".
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zb_land_pow2_bit0 : forall x k, 0 <= k -> Z.testbit x k = false -> Z.land x (2^k) = 0.
Proof.
  intros x k Hk Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity| apply Bool.andb_false_r].
Qed.

(* [comment removed for export] *)
Lemma zb_lxor_pow2 : forall x k, 0 <= k ->
  Z.lxor x (2^k) = x + 2^k - 2 * 2^k * ((x / 2^k) mod 2).
Proof.
  intros x k Hk.
  destruct (Z.testbit x k) eqn:Hb.
  - pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm.
    set (y := Z.lxor x (2^k)).
    assert (Hy : Z.testbit y k = false).
    { subst y. rewrite Z.lxor_spec, Hb, Z.pow2_bits_true by lia. reflexivity. }
    assert (E : Z.lxor y (2^k) = y + 2^k).
    { symmetry. apply Z.add_nocarry_lxor. apply zb_land_pow2_bit0; assumption. }
    subst y. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r in E. lia.
  - pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm.
    rewrite <- Z.add_nocarry_lxor by (apply zb_land_pow2_bit0; assumption). lia.
Qed.

(* [comment removed for export] *)
Lemma zb_lxor_b31 : forall x, Z.lxor x 2147483648 = x + 2147483648 - 4294967296 * ((x / 2147483648) mod 2).
Proof. intros x. change 2147483648 with (2^31). rewrite zb_lxor_pow2 by lia. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_wrap32_eq : forall z, bv_wrap 32 z = z mod 4294967296.
Proof. reflexivity. Qed.

Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.

Lemma swrap32_small : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

Lemma sext32_eq : forall z, sext32 z = ((z + 2147483648) mod 4294967296 - 2147483648) mod 18446744073709551616.
Proof.
  intros z. unfold sext32, sub64, M32. rewrite wrap64_mod. change (2^64) with 18446744073709551616. f_equal.
  change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. change 2147483648 with (2^31).
  rewrite zb_lxor_pow2 by lia. change 4294967296 with (2^32).
  Z.div_mod_to_equations. nia.
Qed.

Lemma land_swrap32_sext32 : forall z, Z.land (bv_swrap 32 z) 18446744073709551615 = sext32 z.
Proof. intros z. rewrite land_W64, sext32_eq, swrap32_eq. reflexivity. Qed.

Lemma mod_swrap32_sext32 : forall z, (bv_swrap 32 z) mod 18446744073709551616 = sext32 z.
Proof. intros z. rewrite sext32_eq, swrap32_eq. reflexivity. Qed.

Lemma Z_to_bv_swrap32 : forall z, Z_to_bv 64 (bv_swrap 32 z) = Z_to_bv 64 (sext32 z).
Proof. intros z. rewrite <- land_swrap32_sext32. symmetry. apply Z_to_bv_land64. Qed.

Lemma sext32_range : forall z, 0 <= sext32 z < 18446744073709551616.
Proof. intros z. rewrite sext32_eq. apply Z.mod_pos_bound. lia. Qed.

Lemma sext32_small : forall z, 0 <= z < 2147483648 -> sext32 z = z.
Proof. intros z Hz. rewrite sext32_eq. rewrite (Z.mod_small (z + _)) by lia. rewrite Z.mod_small by lia. lia. Qed.

Lemma sext32_mod32 : forall z, sext32 (z mod 4294967296) = sext32 z.
Proof.
  intros z. rewrite !sext32_eq. f_equal. f_equal.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma sext32_land64 : forall z, sext32 (Z.land z 18446744073709551615) = sext32 z.
Proof.
  intros z. rewrite land_W64, <- (sext32_mod32 (z mod 2^64)), <- (sext32_mod32 z). f_equal.
  change (2^64) with (4294967296 * 4294967296). rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma sext32_landM32 : forall z, sext32 (Z.land z 4294967295) = sext32 z.
Proof.
  intros z. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. apply sext32_mod32.
Qed.

(* [comment removed for export] *)
Lemma sext32_low : forall z, (sext32 z) mod 4294967296 = z mod 4294967296.
Proof.
  intros z. rewrite sext32_eq. change 18446744073709551616 with (4294967296 * 4294967296).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma zext32_eq : forall z, zext32 z = z mod 4294967296.
Proof. intros z. unfold zext32, M32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma zext32_small : forall z, 0 <= z < 4294967296 -> zext32 z = z.
Proof. intros z Hz. rewrite zext32_eq. apply Z.mod_small. lia. Qed.

Lemma zext32_sext32 : forall z, zext32 (sext32 z) = z mod 4294967296.
Proof. intros z. rewrite zext32_eq. apply sext32_low. Qed.

(* [comment removed for export] *)
Lemma srliw_pos : forall x k, 0 < k -> srliw x k = Z.shiftr (x mod 4294967296) k.
Proof.
  intros x k Hk. unfold srliw. unfold M32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia.
  change (2^32) with 4294967296.
  apply sext32_small. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
  rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
  apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
  assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma walk_srliw : forall x k, 0 < k -> 0 <= x ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 x) k) = Z.shiftr (x mod 4294967296) k.
Proof.
  intros x k Hk Hx. rewrite bv_wrap32_eq. apply swrap32_small.
  pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
  rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.le_trans with 0; [lia|]. apply Z.div_pos; lia. }
  apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
  assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_mask_small : forall x k, 0 <= k -> 0 <= x < 2^k -> Z.land x (2^k - 1) = x.
Proof. intros x k Hk Hx. rewrite zb_land_mask by lia. apply Z.mod_small. lia. Qed.

Lemma land_W64_small : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (2^64 - 1). apply land_mask_small; [lia|]. change (2^64) with 18446744073709551616. lia. Qed.

Lemma land_M32_small : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (2^32 - 1). apply land_mask_small; [lia|]. change (2^32) with 4294967296. lia. Qed.

Lemma land63_small : forall x, 0 <= x < 64 -> Z.land x 63 = x.
Proof. intros x Hx. change 63 with (2^6 - 1). apply land_mask_small; [lia|]. change (2^6) with 64. lia. Qed.

Lemma land63_64_128 : forall x, 64 <= x < 128 -> Z.land x 63 = x - 64.
Proof.
  intros x Hx. change 63 with (2^6 - 1). rewrite zb_land_mask by lia. change (2^6) with 64.
  rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma shiftr63_small : forall x, 0 <= x < 9223372036854775808 -> Z.shiftr x 63 = 0.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. change (2^63) with 9223372036854775808. lia. Qed.

Lemma shiftr_bound : forall x k, 0 <= x < 18446744073709551616 -> 0 <= k <= 64 ->
  0 <= Z.shiftr x k < 2^(64 - k).
Proof.
  intros x k Hx Hk. rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (64 - k)) with 64 by lia.
  change (2^64) with 18446744073709551616. lia.
Qed.

(* [comment removed for export] *)
Lemma sext32_gcc : forall v, sext32 (Z.lxor v 2147483648 - 2147483648) = sext32 v.
Proof.
  intros v. rewrite <- (sext32_mod32 (Z.lxor v _ - _)), <- (sext32_mod32 v). f_equal.
  rewrite zb_lxor_b31. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma gcc_sext_low32 : forall v, (Z.lxor v 2147483648 - 2147483648) mod 4294967296 = v mod 4294967296.
Proof. intros v. rewrite zb_lxor_b31. Z.div_mod_to_equations. lia. Qed.

Lemma gcc_sext_low6 : forall v, Z.land (Z.lxor v 2147483648 - 2147483648) 63 = Z.land v 63.
Proof.
  intros v. change 63 with (2^6 - 1). rewrite !zb_land_mask by lia. rewrite zb_lxor_b31.
  change (2^6) with 64. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma gcc_sext_small : forall v, 0 <= v < 2147483648 ->
  Z.land (Z.lxor v 2147483648 - 2147483648) 18446744073709551615 = v.
Proof.
  intros v Hv. rewrite zb_lxor_b31, (Z.div_small v) by lia. change (0 mod 2) with 0.
  rewrite land_W64. rewrite Z.mod_small; lia.
Qed.

Lemma shiftr_mod32_bound : forall x k, 0 < k -> 0 <= Z.shiftr (x mod 4294967296) k < 2147483648.
Proof.
  intros x k Hk. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
  rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
  apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
  assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma lxor31_sub_small : forall v, 0 <= v < 2147483648 -> Z.lxor v 2147483648 - 2147483648 = v.
Proof. intros v Hv. rewrite zb_lxor_b31, (Z.div_small v) by lia. change (0 mod 2) with 0. lia. Qed.

(* [comment removed for export] *)
Ltac fix32 :=
  repeat first
  [ rewrite walk_srliw by (first [lia | zrange_nonneg])
  | match goal with
    | |- context [Z.lxor (Z.shiftr (?x mod 4294967296) ?k) 2147483648 - 2147483648] =>
        rewrite (lxor31_sub_small (Z.shiftr (x mod 4294967296) k)) by (apply shiftr_mod32_bound; lia)
    | |- context [Z.land (Z.lxor (Z.shiftr (?x mod 4294967296) ?k) 2147483648 - 2147483648) 18446744073709551615] =>
        rewrite (gcc_sext_small (Z.shiftr (x mod 4294967296) k)) by (apply shiftr_mod32_bound; lia)
    end ].
Ltac wstep := zstep; fix32.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma clz32_mirror_range : forall r, 0 <= clz32_mirror r < 18446744073709551616.
Proof. intros r. unfold clz32_mirror. cbv zeta. unfold srliw at 1. apply sext32_range. Qed.

(* [comment removed for export] *)
Lemma land63_mod : forall x, Z.land x 63 = x mod 64.
Proof. intros. change 63 with (2^6 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma land63_congr32 : forall x y, x mod 4294967296 = y mod 4294967296 -> Z.land x 63 = Z.land y 63.
Proof.
  intros x y H. rewrite !land63_mod.
  rewrite <- (Z.mod_mod_divide x 4294967296 64), <- (Z.mod_mod_divide y 4294967296 64) by (exists 67108864; reflexivity).
  now rewrite H.
Qed.

Lemma land63_sext32 : forall x, Z.land (sext32 x) 63 = Z.land x 63.
Proof. intros. apply land63_congr32. apply sext32_low. Qed.

Lemma land63_zext32 : forall x, Z.land (zext32 x) 63 = Z.land x 63.
Proof. intros. apply land63_congr32. rewrite zext32_eq. apply Z.mod_mod. lia. Qed.

Lemma land63_gcc : forall x,
  Z.land (Z.land (Z.lxor x 2147483648 - 2147483648) 18446744073709551615) 63 = Z.land x 63.
Proof.
  intros. apply land63_congr32. rewrite land_W64. change (2^64) with 18446744073709551616.
  rewrite Z.mod_mod_divide by (exists 4294967296; reflexivity).
  apply gcc_sext_low32.
Qed.

Lemma landM32_gcc : forall x,
  Z.land (Z.land (Z.lxor x 2147483648 - 2147483648) 18446744073709551615) 4294967295 = zext32 (sext32 x).
Proof.
  intros. rewrite zext32_sext32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask, land_W64 by lia.
  change (2^32) with 4294967296. change (2^64) with 18446744073709551616.
  rewrite Z.mod_mod_divide by (exists 4294967296; reflexivity).
  apply gcc_sext_low32.
Qed.

(* [comment removed for export] *)
Lemma land63_not_congr : forall x y, 0 <= x < 18446744073709551616 -> 0 <= y < 18446744073709551616 ->
  x mod 4294967296 = y mod 4294967296 ->
  Z.land (Z.lxor x 18446744073709551615) 63 = Z.land (Z.lxor y 18446744073709551615) 63.
Proof.
  intros x y Hx Hy H. rewrite !zb_lxor_ones by lia. apply land63_congr32.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma shl48_congr : forall x y, x mod 4294967296 = y mod 4294967296 ->
  Z.land (Z.shiftl x 48) 18446744073709551615 = Z.land (Z.shiftl y 48) 18446744073709551615.
Proof.
  intros x y H. rewrite !land_W64, !Z.shiftl_mul_pow2 by lia.
  change (2^64) with (65536 * 2^48). rewrite !Z.mul_mod_distr_r by lia. f_equal.
  rewrite <- (Z.mod_mod_divide x 4294967296 65536), <- (Z.mod_mod_divide y 4294967296 65536) by (exists 65536; reflexivity).
  now rewrite H.
Qed.

Lemma shl48_sext32 : forall x,
  Z.land (Z.shiftl (sext32 x) 48) 18446744073709551615 = Z.land (Z.shiftl x 48) 18446744073709551615.
Proof. intros. apply shl48_congr. apply sext32_low. Qed.

(* [comment removed for export] *)
Lemma srai63_word : forall x, 0 <= x < 18446744073709551616 ->
  Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 x)) 63) = Z_to_bv 64 (if 9223372036854775808 <=? x then 18446744073709551615 else 0).
Proof.
  intros x Hx. rewrite zb_signed, unsigned_lit by (change (2^64) with 18446744073709551616; lia).
  change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616.
  destruct (Z.ltb_spec0 x 9223372036854775808); destruct (Z.leb_spec0 9223372036854775808 x); try (exfalso; lia).
  - rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
  - apply Z_to_bv_eqm. rewrite Z.shiftr_div_pow2 by lia. change (2^63) with 9223372036854775808.
    Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma half_land : forall x, 0 <= x -> Z.land (Z.shiftr x 1) 2147483647 = Z.shiftr (x mod 4294967296) 1.
Proof.
  intros x Hx. change 2147483647 with (2^31 - 1). rewrite zb_land_mask, !Z.shiftr_div_pow2 by lia.
  change (2^31) with 2147483648. change (2^1) with 2. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac name_as_by_tac X e tac :=
  set (X := e) in *;
  let RX := fresh "R" X in
  assert (RX : 0 <= X < 18446744073709551616) by (subst X; tac).
Tactic Notation "name_as_by" ident(X) constr(e) tactic3(tac) := name_as_by_tac X e tac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sext32_cases : forall u, 0 <= sext32 u < 2147483648 \/ 18446744071562067968 <= sext32 u < 18446744073709551616.
Proof. intros u. rewrite sext32_eq. Z.div_mod_to_equations. lia. Qed.

Lemma shiftr_const : forall x k c, 0 <= k -> c * 2^k <= x < (c + 1) * 2^k -> Z.shiftr x k = c.
Proof.
  intros x k c Hk Hx. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  apply Z.le_antisymm.
  - apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_comm. lia.
  - apply Z.div_le_lower_bound; [lia|]. rewrite Z.mul_comm. lia.
Qed.

(* [comment removed for export] *)
Lemma land_signmask_shl : forall x, 0 <= x < 18446744073709551616 ->
  Z.land x 18446744071562067968 = Z.shiftl (Z.shiftr x 31) 31.
Proof.
  intros x Hx. change 18446744071562067968 with (Z.shiftl (Z.ones 33) 31).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 31).
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 31 + 31) with i by lia.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry.
      destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [|lia].
      apply Z.log2_lt_pow2; [lia|]. change (2^64) with 18446744073709551616. lia.
Qed.

Lemma land_signmask : forall x, 0 <= x < 18446744073709551616 ->
  Z.land x 18446744071562067968 = x - x mod 2147483648.
Proof.
  intros x Hx. rewrite land_signmask_shl, zb_shr_shl by lia. reflexivity.
Qed.

Lemma srai63_var : forall a : bv 64,
  Z_to_bv 64 (Z.shiftr (bv_signed a) 63) = Z_to_bv 64 (if 9223372036854775808 <=? bv_unsigned a then 18446744073709551615 else 0).
Proof.
  intros a. rewrite <- srai63_word by (pose proof (zr_word a) as H; unfold inr64 in H; change (2^64) with 18446744073709551616 in H; lia).
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma signhi_pos : forall x, 0 <= x < 2147483648 ->
  Z.land (Z.shiftl (Z.land x 18446744071562067968) 32) 18446744073709551615 = 0.
Proof.
  intros x Hx. rewrite land_signmask, Z.mod_small by lia. rewrite Z.sub_diag. reflexivity.
Qed.

Lemma signhi_neg : forall x, 18446744071562067968 <= x < 18446744073709551616 ->
  Z.land (Z.shiftl (Z.land x 18446744071562067968) 32) 18446744073709551615 = 9223372036854775808.
Proof.
  intros x Hx. rewrite land_signmask by lia.
  replace (x - x mod 2147483648) with 18446744071562067968 by (Z.div_mod_to_equations; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma negabs_model : forall x, 0 <= x < 18446744073709551616 ->
  Z.land (Z.lxor x 18446744073709551615 - 18446744073709551615) 18446744073709551615 = (18446744073709551616 - x) mod 18446744073709551616.
Proof.
  intros x Hx. rewrite zb_lxor_ones, land_W64 by lia. change (2^64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

Lemma negabs_code : forall x, 0 <= x < 18446744073709551616 ->
  Z.lxor 18446744073709551615 x + 1 = 18446744073709551616 - x.
Proof. intros x Hx. rewrite Z.lxor_comm, zb_lxor_ones by lia. lia. Qed.

(* [comment removed for export] *)
Lemma sraiw31_word : forall x, 0 <= x < 18446744073709551616 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 x) 31)) =
  Z_to_bv 64 (Z.land (0 - Z.land (Z.shiftr x 31) 1) 18446744073709551615).
Proof.
  intros x Hx. apply Z_to_bv_eqm. rewrite land_W64, !swrap32_eq, land_1, !Z.shiftr_div_pow2 by lia.
  change (2^31)%Z with 2147483648%Z. change (2^64)%Z with 18446744073709551616%Z.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac model_reg_w_tac n X mexpr :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
        by (rewrite ?srliw_pos by lia; first [ f_equal; zeq | rewrite Z_to_bv_land64; f_equal; zeq ]);
      set (X := mexpr) in *;
      let RX := fresh "R" X in
      assert (RX : 0 <= X < 18446744073709551616) by (subst X; rewrite ?srliw_pos by lia; zrange)
  | _ => fail "model_reg_w: register" n "holds" w
  end.
Tactic Notation "model_reg_w" constr(n) ident(X) constr(mexpr) := model_reg_w_tac n X mexpr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma clz64_mirror_range : forall x, 0 <= clz64_mirror x < 18446744073709551616.
Proof.
  intros x. unfold clz64_mirror. cbv zeta. unfold mul64.
  match goal with |- context [Z.shiftr (wrap64 ?p) 56] =>
    pose proof (wrap64_range p) as Hr; rewrite (Z.shiftr_div_pow2 (wrap64 p)) by lia end.
  change (2^64) with 18446744073709551616 in Hr.
  split. { apply Z.div_pos; lia. } apply Z.div_lt_upper_bound; lia.
Qed.

(* [comment removed for export] *)
Lemma zb_land_pow2 : forall x k, 0 <= k -> Z.land x (2^k) = 2^k * ((x / 2^k) mod 2).
Proof.
  intros x k Hk. destruct (Z.testbit x k) eqn:Hb.
  - pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm, Z.mul_1_r.
    apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity | apply Bool.andb_false_r].
  - pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm, Z.mul_0_r.
    apply zb_land_pow2_bit0; assumption.
Qed.

(* [comment removed for export] *)
Lemma signbit63 : forall x, 0 <= x < 18446744073709551616 ->
  Z.land (Z.shiftl (Z.shiftr x 63) 63) 18446744073709551615 = Z.land 9223372036854775808 x.
Proof.
  intros x Hx. rewrite zb_shr_shl, land_W64 by lia. rewrite Z.land_comm.
  change 9223372036854775808 with (2^63). rewrite zb_land_pow2 by lia.
  change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma lor_rot_asx : forall a s x, Z.lor (Z.lor a s) x = Z.lor (Z.lor x a) s.
Proof.
  intros. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
  destruct (Z.testbit a i), (Z.testbit s i), (Z.testbit x i); reflexivity.
Qed.
Lemma lor_rot_dsg : forall d s g, Z.lor (Z.lor d s) g = Z.lor (Z.lor d g) s.
Proof.
  intros. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
  destruct (Z.testbit d i), (Z.testbit s i), (Z.testbit g i); reflexivity.
Qed.

(* [comment removed for export] *)
Ltac reg_rewrite n lem :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      let e' := fresh "e" in let E := fresh "E" in
      remember e as e' eqn:E in |- *;
      rewrite lem in E; subst e'
  end.

(* [comment removed for export] *)
Lemma sra63_leb : forall x, 0 <= x < 18446744073709551616 ->
  (if negb (Z.shiftr x 63 =? 0) then 18446744073709551615 else 0) =
  (if 9223372036854775808 <=? x then 18446744073709551615 else 0).
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2^63) with 9223372036854775808.
  destruct (Z.leb_spec0 9223372036854775808 x).
  - rewrite (proj2 (Z.eqb_neq _ _)); [reflexivity|]. Z.div_mod_to_equations. lia.
  - rewrite Z.div_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ltb1_eqb0 : forall x, 0 <= x -> (x <? 1) = (x =? 0).
Proof. intros x Hx. destruct (Z.ltb_spec0 x 1); destruct (Z.eqb_spec x 0); try reflexivity; exfalso; lia. Qed.

Lemma sext32_congr : forall x y, x mod 4294967296 = y mod 4294967296 -> sext32 x = sext32 y.
Proof. intros x y H. rewrite <- (sext32_mod32 x), <- (sext32_mod32 y), H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nez_sub_lxor : forall a b, 0 <= a < 18446744073709551616 -> 0 <= b < 18446744073709551616 ->
  (0 <? Z.land (a - b) 18446744073709551615) = (0 <? Z.lxor b a).
Proof.
  intros a b Ha Hb. rewrite land_W64. change (2^64) with 18446744073709551616.
  assert (Hn : 0 <= Z.lxor b a) by (apply Z.lxor_nonneg; split; intros; lia).
  destruct (Z.eq_dec a b) as [->|Hne].
  - rewrite Z.sub_diag, Z.lxor_nilpotent. reflexivity.
  - assert (Z.lxor b a <> 0) by (intros E; apply (proj1 (Z.lxor_eq_0_iff b a)) in E; lia).
    apply eq_true_iff_eq. rewrite !Z.ltb_lt. split; intros _; [lia|]. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma land63_lxor63 : forall x, Z.land (Z.lxor x 63) 63 = Z.land (Z.lxor x 18446744073709551615) 63.
Proof.
  intros x. change 63 with (Z.ones 6). change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, !Z.lxor_spec.
  destruct (Z.lt_ge_cases i 6).
  - rewrite !Z.ones_spec_low by lia. reflexivity.
  - rewrite (Z.ones_spec_high 6) by lia. rewrite !Bool.andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exp0_gcc : forall s, Z_to_bv 64 (s + -15360) =
  Z_to_bv 64 (Z.land (Z.land (s + 18446744073709536255) 18446744073709551615 + 1) 18446744073709551615).
Proof.
  intros s. apply Z_to_bv_eqm. rewrite !land_W64. change (2^64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition to_d_pack (dE dS a_hi : Z) : Z := Z.lor (Z.lor (shl64 dE 52) (shl64 (shr64 a_hi 63) 63)) dS.

Definition to_d_normD (sig1 exp0 : Z) : Z * Z :=
  let carry := shr64 sig1 52 in (add64 carry exp0, Z.land (sub64 carry 1) sig1).

Definition to_d_normal (a_lo sigHi candM1 : Z) : Z * Z :=
  let sig0 := Z.lor (shr64 a_lo 60) (shl64 sigHi 4) in
  let roundBits := shr64 (shl64 a_lo 4) 4 in
  let exp0 := add64 candM1 1 in
  let sig1 := trunc_round sig0 roundBits in
  to_d_normD sig1 exp0.

Definition to_d_subD (sig1 : Z) : Z * Z :=
  let carry := nez64 (shr64 sig1 52) in (carry, Z.lxor sig1 (shl64 carry 52)).

Definition to_d_subC (srLo sigHi1 shift mM64 sticky : Z) : Z * Z :=
  let srHi0 := shr64 sigHi1 (Z.land shift 63) in
  let srHi := Z.land (sra63 mM64) srHi0 in
  let sig0 := Z.lor (shr64 srLo 60) (shl64 srHi 4) in
  let roundBits := Z.lor (shr64 (shl64 srLo 4) 4) sticky in
  let sig1 := trunc_round sig0 roundBits in
  to_d_subD sig1.

Definition to_d_subB (a_lo sigHi1 shift shNZ slLo slHi : Z) : Z * Z :=
  let stickySrc := Z.lor slLo slHi in
  let m := zext32 shift in
  let sticky0 := nez64 stickySrc in
  let mM64 := sub64 m 64 in
  let sticky := Z.land shNZ sticky0 in
  let srLo := if negb (is_neg64 mM64) then shr64 sigHi1 (Z.land m 63)
              else Z.lor (shr64 a_lo (Z.land shift 63)) (shl64 (shl64 sigHi1 1) (Z.land (not64 m) 63)) in
  to_d_subC srLo sigHi1 shift mM64 sticky.

Definition to_d_subA (a_lo sigHi srcExp k shift : Z) : Z * Z :=
  let expNZ := nez64 srcExp in
  let shNZ0 := Z.lxor k srcExp in
  let negsh := sext32 (sub64 0 shift) in
  let implicit := shl64 expNZ 48 in
  let shNZ := nez64 shNZ0 in
  let nW := sext32 (sub64 128 shift) in
  let t0 := shl64 a_lo (Z.land negsh 63) in
  let sigHi1 := Z.lor sigHi implicit in
  let n := zext32 nW in
  let nM64 := sub64 n 64 in
  let slLo := Z.land (sra63 nM64) t0 in
  let slHi := if negb (is_neg64 nM64) then shl64 a_lo (Z.land n 63)
              else Z.lor (shl64 sigHi1 (Z.land negsh 63)) (shr64 (shr64 a_lo 1) (Z.land (not64 n) 63)) in
  to_d_subB a_lo sigHi1 shift shNZ slLo slHi.

Definition to_d_range (a_lo sigHi srcExp : Z) : Z * Z :=
  if negb (srcExp <=? 0x43fe) then (2047, 0)
  else
    let expZ := eqz64 srcExp in
    let k := Z.lxor expZ 0x3c01 in
    let shift := sub64 k srcExp in
    if lt_s64 112 shift then (0, 0)
    else to_d_subA a_lo sigHi srcExp k shift.

Definition to_d_core (a_lo a_hi : Z) : Z * Z :=
  let srcExp := shr64 (shl64 a_hi 1) 49 in
  let sigHi := shr64 (shl64 a_hi 16) 16 in
  let candM1 := add64 srcExp 0xffffffffffffc3ff in
  if negb (2045 <? candM1) then to_d_normal a_lo sigHi candM1
  else
    let isNaN := if Z.lor a_lo sigHi =? 0 then false else negb (negb (srcExp =? 0x7fff)) in
    if isNaN then (2047, Z.lor (Z.lor (shr64 a_lo 60) DQUIET) (shl64 sigHi 4))
    else to_d_range a_lo sigHi srcExp.

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
  intros lo hi H. unfold lo64. rewrite wrap64_mod.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
  intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
  rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

Lemma f128_to_d_split : forall a_lo a_hi, (0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z ->
  f128_to_d (a_lo + 2^64 * a_hi) = (let '(dE, dS) := to_d_core a_lo a_hi in to_d_pack dE dS a_hi).
Proof. intros. unfold f128_to_d. rewrite lo64_words, hi64_words by lia. reflexivity. Qed.


(* [comment removed for export] *)
Definition to_d_pack_g (dE dS sgn : Z) : Z := Z.lor (shl64 dE 52) (Z.lor dS sgn).

Lemma f128_to_d_split_g : forall a_lo a_hi, (0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z ->
  f128_to_d (a_lo + 2^64 * a_hi) =
  (let '(dE, dS) := to_d_core a_lo a_hi in to_d_pack_g dE dS (Z.land a_hi 9223372036854775808)).
Proof.
  intros a_lo a_hi Hl Hh. rewrite f128_to_d_split by assumption.
  destruct (to_d_core a_lo a_hi) as [dE dS]. unfold to_d_pack, to_d_pack_g.
  unfold shl64 at 2. rewrite wrap64_mod. change (2^64) with 18446744073709551616.
  rewrite <- land_W64, signbit63 by (change (2^64) with 18446744073709551616 in Hh; lia).
  rewrite (Z.land_comm 9223372036854775808 a_hi).
  apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
  destruct (Z.testbit (shl64 dE 52) i), (Z.testbit dS i), (Z.testbit (Z.land a_hi 9223372036854775808) i); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma round_even_g : forall x, 0 <= x ->
  Z_to_bv 64 (Z.land (Z.land (x + 1) 18446744073709551615) 18446744073709551614) =
  Z_to_bv 64 (Z.land (Z.land x 1 + x) 18446744073709551615).
Proof.
  intros x Hx. apply Z_to_bv_eqm. rewrite land_even_mask, !land_W64, !land_1.
  change (2^64) with 18446744073709551616.
  rewrite (Z.mod_mod_divide (x + 1) 18446744073709551616 2) by (exists 9223372036854775808; reflexivity).
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma to_d_shift_facts : forall srcExp, 0 <= srcExp <= 15360 ->
  Z.lxor (Z.land (Z.lxor (Z.b2z (srcExp =? 0)) 15361 - srcExp) 18446744073709551615) 9223372036854775808
    <= 9223372036854775920 ->
  Z.b2z (srcExp =? 0) = 0 /\ Z.land (Z.lxor (Z.b2z (srcExp =? 0)) 15361 - srcExp) 18446744073709551615 = 15361 - srcExp
  /\ 1 <= 15361 - srcExp <= 112.
Proof.
  intros srcExp Hs. destruct (Z.eqb_spec srcExp 0) as [E|E].
  - subst srcExp. intros K. exfalso. apply K. vm_compute. reflexivity.
  - cbn [Z.b2z]. change (Z.lxor 0 15361) with 15361.
    rewrite land_W64_small by lia. change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2 by lia.
    rewrite (Z.div_small (15361 - srcExp)) by lia. change (2^63) with 9223372036854775808. change (0 mod 2) with 0. lia.
Qed.

(* [comment removed for export] *)
Lemma lxor1_b2z : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. intros [|]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma landM32_swrap_land64 : forall x,
  Z.land (Z.land (bv_swrap 32 x) 18446744073709551615) 4294967295 = Z.land (Z.land x 18446744073709551615) 4294967295.
Proof.
  intros x. rewrite land_swrap32_sext32. change 4294967295 with (2^32 - 1). rewrite !zb_land_mask, land_W64 by lia.
  change (2^32) with 4294967296. rewrite sext32_low. change (2^64) with 18446744073709551616.
  rewrite Z.mod_mod_divide by (exists 4294967296; reflexivity). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shl13_shr16 : forall x, 0 <= x < 18446744073709551616 ->
  Z.shiftr (Z.land (Z.shiftl x 13) 18446744073709551615) 16 = Z.land (Z.shiftr x 3) 281474976710655.
Proof.
  intros x Hx. rewrite land_W64, Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change 281474976710655 with (2^48 - 1). rewrite zb_land_mask by lia.
  change (2^64) with (2251799813685248 * 8192). change (2^13) with 8192. change (2^16) with (8192 * 8).
  change (2^3) with 8. change (2^48) with 281474976710656.
  rewrite Z.mul_mod_distr_r by lia.
  rewrite <- Z.div_div, Z.div_mul by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lor_rot_bsa : forall b s a, Z.lor (Z.lor b s) a = Z.lor (Z.lor a s) b.
Proof.
  intros. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
  destruct (Z.testbit b i), (Z.testbit s i), (Z.testbit a i); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma b2z_ltb1 : forall b, (Z.b2z b <? 1) = negb b.
Proof. intros [|]; reflexivity. Qed.

Lemma signbit63' : forall x, 0 <= x < 18446744073709551616 ->
  Z.land (Z.shiftl (Z.shiftr x 63) 63) 18446744073709551615 = Z.land x 9223372036854775808.
Proof. intros. rewrite signbit63 by assumption. apply Z.land_comm. Qed.
