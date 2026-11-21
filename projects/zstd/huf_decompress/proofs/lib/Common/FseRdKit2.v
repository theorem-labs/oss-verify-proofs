(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (23 recorded proofs replaced by written proofs (land_mod_pow2, lor_mod_pow2, land_compl and 20 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_FseRdKit2 () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z4landK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic2eq00C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z9land_specK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1ZBmod_pow2_bits_highC56Stdlib6ZArith6BinInt1Z9bits_inj'K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z3lorC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z8lor_specC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4predK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z:ones_equivC56Stdlib6ZArith6BinInt1Z5ldiffC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z=ones_spec_lowC59OSSVerify5KrLib3Lib5BytesBtestbit_high_falseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1ZAsub_nocarry_ldiffC47Corelib4Init5Logic6eq_indK46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec9FseNCount7ctz_auxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib4Spec9FseLemmas6pow2_SC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8div2_oddC56Stdlib6ZArith6BinInt1Z4div2C56Stdlib6ZArith6BinInt1Z3oddC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec9FseLemmas8pow2_posC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr03C47Corelib7Classes?RelationClasses=eq_TransitiveC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z7land_wdC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=testbit_odd_0C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z@testbit_odd_succc59OSSVerify5KrLib6Common9FseRdKit2:land_complC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib4Spec9FseLemmas:ctz_aux_leC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z;shiftl_landC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring=ring_sub_compI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z8div2_divC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrC46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib7Numbers7BinNums1N01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00c59OSSVerify5KrLib6Common9FseRdKit26db_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib6Common8FseRdKit8all_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8FseRdKit;brute_rangeC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib4Spec9FseNCount5not32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas?repeats_arg_modC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib6Common9FseRdKit2>ctzv_arg_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common9FseRdKit2;lowbit_landC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common9FseRdKit24ctzvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common9FseRdKit2;ctzv_lowbitC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02C59OSSVerify5KrLib3Lib5Bytes<land_lt_pow2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZApow_lt_mono_r_iffK47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec9FseNCount3res00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK59OSSVerify5KrLib4Spec9FseNCount3res03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4bindC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec9FseNCount3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas6u32_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount:repeats_ofC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec9FseNCount3res01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC59OSSVerify5KrLib6Common8FseRdKitAswrap32_u32_mod32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z9mod_smallC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC59OSSVerify5KrLib3Lib7ZBridge<zb_lxor_onesC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib6Common9FseRdKit2<lor_mod_pow2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z7mod_0_lC46Stdlib6ZArith4Zdiv:Zminus_modC56Stdlib6ZArith6BinInt1Z7mod_modC59OSSVerify5KrLib6Common:FseWalkKit:swrap32_eqC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_dividec59OSSVerify5KrLib6Common9FseRdKit2=land_mod_pow2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common9FseRdKit2:ctzv_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrc59OSSVerify5KrLib6Common9FseRdKit2Adb_table_ok_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:FseWalkKit=swrap32_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C46Stdlib6ZArith4ZdivAZmult_mod_idemp_rC46Stdlib6ZArith4Zdiv9Zmult_modC45stdpp9bitvector;definitions7bv_wrapC59OSSVerify5KrLib6Common:FseWalkKit9wrap32_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib5Lists7ListDef3nthc59OSSVerify5KrLib6Common9FseRdKit28DB_TABLEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount8readLE32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4ZnthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8FseRdKit4le32C1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib4Spec9FseNCount5shr32C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z<pos_div_euclC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC59OSSVerify5KrLib4Spec9FseLemmas7land_31C1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3mulC47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib3Mem:length_le2C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib6Common:FseWalkKit4u16sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount;zero_prefixC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulc59OSSVerify5KrLib6Common9FseRdKit28le2_zeroC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCountAread_ncount_body8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount7ZlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00K59OSSVerify5KrLib4Spec9FseNCount3res02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount;r_remainingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount9r_charnumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount:r_bitCountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4r_ncC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4r_ipC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common9FseRdKit25rd_s0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8FseRdKit=readLE32_le32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specC59OSSVerify5KrLib4Spec9FseLemmas8shr32_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas7land_15C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C57Corelib7BinNums6PosDef3Pos4landC56Stdlib6ZArith6BinInt1Z4of_NC57Corelib7BinNums6PosDef3Pos6pred_NC57Corelib7BinNums6NatDef1N5ldiffC57Corelib7BinNums6NatDef1N3lorC57Corelib7BinNums6NatDef1N8succ_posK59OSSVerify5KrLib4Spec9FseNCount3res04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec9FseNCount6rstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount5rloopC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I59OSSVerify5KrLib4Spec9FseNCount6rstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCountIFSE_TABLELOG_ABSOLUTE_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount@FSE_MIN_TABLELOGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCountLZSTD_error_tableLog_tooLargeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCountNZSTD_error_corruption_detectedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCountRZSTD_error_maxSymbolValue_tooSmallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas9all_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8FseRdKit:le32_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC59OSSVerify5KrLib4Spec<FseReadSound3CTLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<FseReadSound3POSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<FseReadSound3pwsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;FseReaderRTBzero_prefix_lengthC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init5Peano2ltC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC56Stdlib6ZArith6BinInt1Z8max_specC59OSSVerify5KrLib4Spec;FseReaderRT?zero_prefix_nthC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6ltb_geC59OSSVerify5KrLib4Spec9FseNCount4wsumC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List8firstn_0C59OSSVerify5KrLib4Spec9FseNCount;r_thresholdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount8r_nbBitsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec9FseNCount;r_bitStreamC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith6BinInt1Z7mod_mulC59OSSVerify5KrLib6Common8FseRdKit@lor_add_disjointC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_commC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib6Common8FseRdKit8byte_litC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_mod_pow2 : forall a b n, 0 <= n -> (Z.land a b) mod 2^n = Z.land (a mod 2^n) (b mod 2^n).
Proof.
  intros a b n Hn. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z_lt_le_dec i n).
  - rewrite !Z.mod_pow2_bits_low by lia. apply Z.land_spec.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lor_mod_pow2 : forall a b n, 0 <= n -> (Z.lor a b) mod 2^n = Z.lor (a mod 2^n) (b mod 2^n).
Proof.
  intros a b n Hn. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z_lt_le_dec i n).
  - rewrite !Z.mod_pow2_bits_low by lia. apply Z.lor_spec.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_compl : forall a m, 0 <= m -> 0 <= a < 2^m -> Z.land a (2^m - 1 - a) = 0.
Proof.
  intros a m Hm Ha.
  assert (E : 2^m - 1 - a = Z.ldiff (Z.ones m) a).
  { rewrite <- Z.sub_nocarry_ldiff.
    - rewrite Z.ones_equiv. lia.
    - apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
      destruct (Z_lt_le_dec i m).
      + rewrite Z.ones_spec_low by lia. apply andb_false_r.
      + rewrite (testbit_high_false a m i) by lia. reflexivity. }
  rewrite E. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0.
  destruct (Z.testbit a i); cbn; [apply andb_false_r| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma lowbit_land : forall (f : nat) v, 0 < v < 2^(Z.of_nat f) -> Z.land v (2^(Z.of_nat f) - v) = 2^(ctz_aux f v).
Proof.
  induction f as [|f IH]; intros v Hv.
  - cbn in Hv. lia.
  - rewrite Nat2Z.inj_succ in *. unfold Z.succ in *. rewrite (pow2_S (Z.of_nat f)) in * by lia.
    cbn [ctz_aux].
    pose proof (Z.div2_odd v) as DO. set (a := Z.div2 v) in *.
    assert (P0 : 0 < 2 ^ Z.of_nat f) by (apply pow2_pos; lia).
    destruct (Z.odd v) eqn:EO; cbn [Z.b2z] in DO.
    + (* [comment removed for export] *)
      assert (Q : 0 <= a < 2 ^ Z.of_nat f) by lia.
      rewrite DO at 1 2.
      replace (2 * 2 ^ Z.of_nat f - (2 * a + 1)) with (2 * (2 ^ Z.of_nat f - 1 - a) + 1) by lia.
      change (2 ^ 0) with 1.
      apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
      destruct (Z.eq_dec i 0) as [->|N].
      * rewrite !Z.testbit_odd_0. reflexivity.
      * replace i with (Z.succ (i - 1)) by lia. rewrite !Z.testbit_odd_succ by lia.
        rewrite <- Z.land_spec, (land_compl a (Z.of_nat f)) by lia. rewrite Z.bits_0.
        change 1 with (2 * 0 + 1). rewrite Z.testbit_odd_succ by lia. rewrite Z.bits_0. reflexivity.
    + rewrite Z.add_0_r in DO.
      assert (Q : 0 < a < 2 ^ Z.of_nat f) by lia.
      rewrite DO at 1 2.
      replace (2 * 2 ^ Z.of_nat f - 2 * a) with (2 * (2 ^ Z.of_nat f - a)) by lia.
      replace (2 * a) with (Z.shiftl a 1) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^1) with 2; lia).
      replace (2 * (2 ^ Z.of_nat f - a)) with (Z.shiftl (2 ^ Z.of_nat f - a) 1) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^1) with 2; lia).
      rewrite <- Z.shiftl_land. rewrite (IH a Q). rewrite Z.shiftl_mul_pow2 by lia.
      pose proof (ctz_aux_le f a). rewrite Z.pow_add_r by lia. change (2^1) with 2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ctzv (bs : Z) : Z := ctz_aux 32 (Z.lor (not32 bs) (2^31)).
Definition db_idx (k : Z) : Z := ((2^k * 125613361) mod 2^32) / 2^27.
Definition DB_TABLE : list Z :=
  [0; 1; 28; 2; 29; 14; 24; 3; 30; 22; 20; 15; 25; 17; 4; 8; 31; 27; 13; 23; 21; 19; 16; 7; 26; 12; 18; 6; 11; 5; 10; 9].

Lemma db_table_ok_range : forall k, 0 <= k < 32 -> 0 <= db_idx k < 32.
Proof.
  intros k Hk.
  pose proof (brute_range (fun k0 => (0 <=? db_idx k0) && (db_idx k0 <? 32)) 0 32 ltac:(vm_compute; reflexivity) k ltac:(lia)) as H.
  cbv beta in H. apply andb_true_iff in H. destruct H as [H0 H1]. apply Z.leb_le in H0. apply Z.ltb_lt in H1. lia.
Qed.

Lemma ctzv_arg_range : forall bs, 0 <= bs < 2^32 -> 0 < Z.lor (not32 bs) (2^31) < 2^32.
Proof. intros bs Hb. exact (proj2 (repeats_arg_mod bs 0 Hb ltac:(lia))). Qed.

Lemma ctzv_lowbit : forall bs, 0 <= bs < 2^32 ->
  Z.land (Z.lor (not32 bs) (2^31)) (2^32 - Z.lor (not32 bs) (2^31)) = 2^(ctzv bs).
Proof. intros bs Hb. exact (lowbit_land 32 _ (ctzv_arg_range bs Hb)). Qed.

Lemma ctzv_range : forall bs, 0 <= bs < 2^32 -> 0 <= ctzv bs <= 31.
Proof.
  intros bs Hb. pose proof (ctz_aux_le 32 (Z.lor (not32 bs) (2^31))) as L. fold (ctzv bs) in L. split; [lia|].
  pose proof (ctzv_arg_range bs Hb) as R. pose proof (ctzv_lowbit bs Hb) as E.
  pose proof (land_lt_pow2 (Z.lor (not32 bs) (2^31)) (2^32 - Z.lor (not32 bs) (2^31)) 32 ltac:(lia) ltac:(lia)) as B.
  rewrite E in B. destruct B as [_ B]. apply Z.pow_lt_mono_r_iff in B; lia.
Qed.

Lemma repeats_of_ctzv : forall bs, 0 <= bs < 2^32 -> repeats_of bs = Ok (ctzv bs / 2).
Proof.
  intros bs Hb. unfold repeats_of, ctz32. pose proof (ctzv_arg_range bs Hb) as R.
  rewrite u32_id by lia. replace (Z.lor (not32 bs) (2 ^ 31) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ctz_index_form : forall bs, 0 <= bs < 2^32 ->
  bv_swrap 32
    (bv_wrap 32
       ((Z.land (Z.lor (Z.lxor (bv_swrap 32 bs mod 18446744073709551616) 18446744073709551615) 18446744071562067968)
                (bv_swrap 32 (0 - Z.lor (Z.lxor (bv_swrap 32 bs mod 18446744073709551616) 18446744073709551615) 18446744071562067968)
                 mod 18446744073709551616) * 125613361) mod 18446744073709551616) ≫ 27)
  = db_idx (ctzv bs).
Proof.
  intros bs Hb.
  set (X := bv_swrap 32 bs mod 18446744073709551616).
  assert (RX : 0 <= X < 2^64) by (subst X; apply Z.mod_pos_bound; lia).
  assert (EX : X mod 2^32 = bs) by (subst X; apply swrap32_u32_mod32; lia).
  set (A := Z.lor (Z.lxor X 18446744073709551615) 18446744071562067968).
  set (v := Z.lor (not32 bs) (2^31)).
  pose proof (ctzv_arg_range bs Hb) as Rv. fold v in Rv.
  assert (EA : A mod 2^32 = v).
  { subst A v. rewrite lor_mod_pow2 by lia. f_equal.
    rewrite zb_lxor_ones by lia. unfold not32. rewrite <- EX.
    pose proof (Z.div_mod X (2^32) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound X (2^32) ltac:(lia)) as MB.
    replace (18446744073709551615 - X) with ((2^32 - 1 - X mod 2^32) + (2^32 - 1 - X / 2^32) * 2^32) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  set (B := bv_swrap 32 (0 - A) mod 18446744073709551616).
  assert (EB : B mod 2^32 = 2^32 - v).
  { subst B. change 18446744073709551616 with (2^64).
    rewrite (Z.mod_mod_divide _ (2^64) (2^32)) by (exists (2^32); reflexivity).
    rewrite swrap32_eq. change 4294967296 with (2^32). change 2147483648 with (2^31).
    rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
    replace (0 - A + 2^31 - 2^31) with (0 - A) by lia.
    rewrite Zminus_mod, EA, Z.mod_0_l by lia.
    replace (0 - v) with ((2^32 - v) + (-1) * 2^32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (EY : (Z.land A B) mod 2^32 = 2^(ctzv bs)).
  { rewrite land_mod_pow2 by lia. rewrite EA, EB. apply ctzv_lowbit. exact Hb. }
  pose proof (ctzv_range bs Hb) as Rk.
  rewrite wrap32_eq. change 4294967296 with (2^32). change 18446744073709551616 with (2^64).
  rewrite (Z.mod_mod_divide _ (2^64) (2^32)) by (exists (2^32); reflexivity).
  rewrite Zmult_mod, EY. rewrite <- Zmult_mod_idemp_r. rewrite Z.mod_mod by lia. rewrite Zmult_mod_idemp_r.
  rewrite Z.shiftr_div_pow2 by lia. fold (db_idx (ctzv bs)).
  apply swrap32_small. pose proof (db_table_ok_range (ctzv bs) ltac:(lia)). lia.
Qed.

Lemma db_table_ok : forall k, 0 <= k < 32 -> 0 <= db_idx k < 32 /\ nth (Z.to_nat (db_idx k)) DB_TABLE 0 = k.
Proof.
  intros k Hk.
  pose proof (brute_range (fun k0 => (0 <=? db_idx k0) && (db_idx k0 <? 32) && (nth (Z.to_nat (db_idx k0)) DB_TABLE 0 =? k0)) 0 32
                ltac:(vm_compute; reflexivity) k ltac:(lia)) as H.
  cbv beta in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma readLE32_inv : forall buf ip w, readLE32 buf ip = Ok w -> 0 <= ip /\ ip + 4 <= zlen buf /\ w = le32 buf ip.
Proof.
  intros buf ip w E. unfold readLE32, FseNCount.Zlength in E.
  destruct ((0 <=? ip) && (ip + 4 <=? zlen buf)) eqn:B; [|discriminate].
  apply andb_true_iff in B. destruct B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
  injection E as <-. unfold le32. auto.
Qed.

Lemma shr32_inv : forall w n v, shr32 w n = Ok v -> 0 <= n < 32 /\ v = w / 2^n.
Proof.
  intros w n v E. unfold shr32 in E. destruct ((0 <=? n) && (n <? 32)) eqn:B; [|discriminate].
  apply andb_true_iff in B. destruct B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
  injection E as <-. auto.
Qed.

Lemma shr_range : forall w n, 0 <= w < 2^32 -> 0 <= n -> 0 <= w / 2^n < 2^32.
Proof.
  intros w n Hw Hn. pose proof (pow2_pos n Hn). split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Lemma land31_mod : forall x, Z.land x 31 = x mod 32.
Proof. exact land_31. Qed.

(* [comment removed for export] *)
Lemma ctz_masks : forall k, 0 <= k < 32 -> k ≫ 1 = k / 2 /\ Z.land k 254 = 2 * (k / 2) /\ Z.land k 30 = 2 * (k / 2).
Proof.
  intros k Hk.
  pose proof (brute_range (fun k0 => (k0 ≫ 1 =? k0 / 2) && (Z.land k0 254 =? 2 * (k0 / 2)) && (Z.land k0 30 =? 2 * (k0 / 2))) 0 32
                ltac:(vm_compute; reflexivity) k ltac:(lia)) as H.
  cbv beta in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
  apply Z.eqb_eq in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

Lemma wrap32_swrap32_u32 : forall bs, 0 <= bs < 2^32 -> bv_wrap 32 (bv_swrap 32 bs mod 18446744073709551616) = bs.
Proof. intros bs Hb. rewrite wrap32_eq. change 4294967296 with (2^32). apply swrap32_u32_mod32. exact Hb. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma le2_zero : le2 (Z_to_bv 64 0) = [Z_to_bv 8 0; Z_to_bv 8 0].
Proof. reflexivity. Qed.

Lemma u16s_zero_prefix : forall n (l : list Z), (n <= length l)%nat ->
  repeat (Z_to_bv 8 0) (2 * n) ++ skipn (2 * n) (u16s (map (Z_to_bv 64) l)) = u16s (map (Z_to_bv 64) (zero_prefix n l)).
Proof.
  induction n as [|n IH]; intros l Hl.
  - cbn [Nat.mul repeat app skipn zero_prefix]. destruct l; reflexivity.
  - destruct l as [|a l]; [cbn in Hl; lia|].
    replace (2 * S n)%nat with (S (S (2 * n))) by lia.
    cbn [repeat app zero_prefix map u16s]. rewrite le2_zero. cbn [app].
    pose proof (length_le2 (Z_to_bv 64 a)) as L2.
    destruct (le2 (Z_to_bv 64 a)) as [|b0 [|b1 [|b2 r]]]; cbn in L2; try lia.
    cbn [app skipn]. rewrite IH by (cbn in Hl; lia). reflexivity.
Qed.


(* [comment removed for export] *)
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply swrap32_small. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rd_s0 (buf : list Z) (msv1 : Z) (nc0 : list Z) : rstate :=
  let w := le32 buf 0 in let x := Z.land w 15 in
  FseNCount.mkR (zero_prefix (Z.to_nat msv1) nc0) 0 (w / 2^4) 4 0 (2^(x + 5) + 1) (2^(x + 5)) (x + 5 + 1) false.

Lemma read_body8_inv : forall buf msv1 nc0 rt msv tlr n, 8 <= zlen buf ->
  read_ncount_body8 buf msv1 nc0 = Ok (rt, msv, tlr, n) ->
  msv1 <= zlen nc0 /\ Z.land (le32 buf 0) 15 <= 10 /\ tlr = Z.land (le32 buf 0) 15 + 5 /\
  exists sF, rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 nc0) = Ok sF
     /\ r_remaining sF = 1 /\ r_charnum sF <= msv1 /\ r_bitCount sF <= 32
     /\ rt = r_nc sF /\ msv = r_charnum sF - 1 /\ n = r_ip sF + (r_bitCount sF + 7) / 8.
Proof.
  intros buf msv1 nc0 rt msv tlr n H8 E. unfold read_ncount_body8, assert in E.
  destruct (Z.leb_spec msv1 (FseNCount.Zlength nc0)) as [L|L]; cbv iota in E; cbn [bind] in E. 2:{ discriminate E. }
  rewrite (readLE32_le32 buf 0) in E by lia. cbn [bind] in E.
  unfold FSE_MIN_TABLELOG, FSE_TABLELOG_ABSOLUTE_MAX in E.
  set (x := Z.land (le32 buf 0) 15) in *.
  destruct (Z.ltb_spec 15 (x + 5)) as [B|B]; cbv iota in E; [discriminate E|].
  rewrite shr32_ok in E by lia. cbn [bind] in E.
  assert (X0 : 0 <= x) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
  replace ((0 <=? x + 5) && (x + 5 <? 31)) with true in E by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  cbn [bind] in E.
  assert (ES0 : rd_s0 buf msv1 nc0 = FseNCount.mkR (zero_prefix (Z.to_nat msv1) nc0) 0 (le32 buf 0 / 2 ^ 4) 4 0 (2 ^ (x + 5) + 1) (2 ^ (x + 5)) (x + 5 + 1) false)
    by reflexivity.
  rewrite <- ES0 in E.
  destruct (rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 nc0)) as [sF| | |] eqn:RL; cbn [bind] in E; try discriminate E.
  destruct (Z.eqb_spec (r_remaining sF) 1) as [E1|N1]; cbn [negb] in E; cbv iota in E; [|discriminate E].
  destruct (Z.ltb_spec msv1 (r_charnum sF)) as [B2|B2]; cbv iota in E; [discriminate E|].
  destruct (Z.ltb_spec 32 (r_bitCount sF)) as [B3|B3]; cbv iota in E; [discriminate E|].
  injection E as <- <- <- <-.
  unfold FseNCount.Zlength in L. split; [exact L|]. split; [lia|]. split; [reflexivity|].
  exists sF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; auto.
Qed.

Lemma rd_s0_inv : forall buf msv1 nc0, all_bytes buf -> 8 <= zlen buf -> 1 <= msv1 <= zlen nc0 -> Z.land (le32 buf 0) 15 <= 10 ->
  CTL msv1 nc0 (Z.land (le32 buf 0) 15 + 5) (rd_s0 buf msv1 nc0) /\ POS buf (rd_s0 buf msv1 nc0) /\ r_bitCount (rd_s0 buf msv1 nc0) < 32.
Proof.
  intros buf msv1 nc0 HB H8 Hm HX. unfold rd_s0. cbv zeta.
  set (x := Z.land (le32 buf 0) 15) in *.
  assert (X0 : 0 <= x) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
  pose proof (le32_range buf 0 HB) as RW.
  assert (P2 : 2 ^ (x + 5 + 1) = 2 * 2 ^ (x + 5)) by (apply pow2_S; lia).
  assert (P5 : 32 <= 2 ^ (x + 5)) by (change 32 with (2^5); apply Z.pow_le_mono_r; lia).
  split; [|split].
  - unfold CTL. cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0].
    split; [apply zero_prefix_length|]. split; [lia|].
    split. { intros i Hi. unfold Znth. rewrite zero_prefix_nth. replace (Z.to_nat i <? Z.to_nat msv1)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
    split. { intros i Hi. unfold Znth. rewrite zero_prefix_nth. replace (Z.to_nat i <? Z.to_nat msv1)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity. }
    split. { f_equal. lia. } split; [lia|]. split; [lia|]. split; [lia|].
    intros _. split; [intros; lia|]. unfold pws. change (Z.to_nat 0) with 0%nat. rewrite firstn_O. cbn [wsum]. lia.
  - unfold POS. cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0].
    assert (0 <= le32 buf 0 / 2^4 < 2^32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    unfold FseNCount.Zlength. repeat split; lia.
  - cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma le32_lbu_raw : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 b3) ≪ 24 mod 18446744073709551616)
               (bv_unsigned (Z_to_bv 8 b2) ≪ 16 mod 18446744073709551616))
        (Z.lor (bv_unsigned (Z_to_bv 8 b1) ≪ 8 mod 18446744073709551616) (bv_unsigned (Z_to_bv 8 b0)))
  = b0 + 2^8 * b1 + 2^16 * b2 + 2^24 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  rewrite !byte_lit by assumption. rewrite !Z.shiftl_mul_pow2 by lia.
  change 18446744073709551616 with (2^64).
  rewrite (Z.mod_small (b3 * 2^24)) by lia. rewrite (Z.mod_small (b2 * 2^16)) by lia. rewrite (Z.mod_small (b1 * 2^8)) by lia.
  rewrite (Z.lor_comm (b1 * 2^8) b0). rewrite (lor_add_disjoint b0 (b1 * 2^8) 8) by (try lia; apply Z.mod_mul; lia).
  rewrite (Z.lor_comm (b3 * 2^24) (b2 * 2^16)).
  rewrite (lor_add_disjoint (b2 * 2^16) (b3 * 2^24) 24) by (try lia; apply Z.mod_mul; lia).
  rewrite Z.lor_comm. rewrite (lor_add_disjoint (b0 + b1 * 2^8) (b2 * 2^16 + b3 * 2^24) 16).
  - lia.
  - lia.
  - lia.
  - replace (b2 * 2^16 + b3 * 2^24) with ((b2 + b3 * 2^8) * 2^16) by lia. apply Z.mod_mul. lia.
Qed.
