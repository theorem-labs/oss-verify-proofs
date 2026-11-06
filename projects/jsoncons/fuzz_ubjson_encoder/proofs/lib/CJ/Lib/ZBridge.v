(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ZBridge () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge5inr64C13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C56Stdlib6NArith6BinNat1N2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z4of_NK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;lt_le_transK47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat3N2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z;land_nonnegI47Corelib4Init5Logic2or00C47Corelib4Init5Logic3iffK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z8land_0_lC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z9log2_landC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula09K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge9zr_land_lC13~~~C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z?bits_above_log2C47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool<andb_false_rC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge9zr_land_rC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge=land_mask_modC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec;Z_lor_rangeC13~~~C56Stdlib6ZArith6BinInt1Z3lorC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec<Z_lxor_rangeC13~~~C56Stdlib6ZArith6BinInt1Z4lxorC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec>Z_shiftr_rangeC13~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z;le_lt_transC56Stdlib6ZArith6BinInt1Z3b2zC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes:comparison01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z=testbit_falseC56Stdlib6ZArith6BinInt1Z9div_smallC46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z>pow2_bits_trueC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC56Stdlib6ZArith6BinInt1Z3addc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeBzb_land_pow2_smallC13~~~C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z9mod_smallc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeBzb_lxor_pow2_smallC13~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC56Stdlib6ZArith6BinInt1Z7lxor_wdC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z8lxor_0_rC56Stdlib6ZArith6BinInt1Z>lxor_nilpotentC56Stdlib6ZArith6BinInt1Z:lxor_assocC56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes7reflect00C45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib7Classes?RelationClasses?Equivalence_PERC46Stdlib4Bool4Bool>eq_true_iff_eqc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge<zb_lxor_signC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge9zb_signedC13~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms<PER_morphismC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes9MorphismsBsubrelation_properK46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveK46Stdlib9micromega5Tauto4kind02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_sltuC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge;bv_lts_lxorC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_sltC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_sltiuC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_sltiC13~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z:shiftl_1_lC56Stdlib6ZArith6BinInt1Z9land_onesc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge<zb_land_maskC13~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z?mul_mod_distr_rC56Stdlib6ZArith6BinInt1Z7div_modC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z<lor_eq_0_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z=lxor_eq_0_iffC56Stdlib6ZArith6BinInt1Z@land_lor_distr_lC56Stdlib6ZArith6BinInt1Z=add_lnot_diagC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z3oppC47Corelib4Init9Datatypes4xorbC46Stdlib4Bool4Bool;xorb_true_rC56Stdlib6ZArith6BinInt1Z=ones_spec_lowC46Stdlib4Bool4Bool<xorb_false_rC56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z9lnot_specC56Stdlib6ZArith6BinInt1Z9lxor_specK46Stdlib9micromega7EnvRing5PExpr06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MStateAunsigned_lit_wrapC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MStateCZ_to_bv_bv_unsignedC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeAunsigned_lit_landC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge:zb_shl_shrC13~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z8eqb_specc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge=Z_to_bv_mod64C13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inr64 (e : Z) : Prop := (0 <= e < 2^64)%Z.

Lemma zr_word : forall x : word, inr64 (bv_unsigned x).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01Hh11xp;1p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9g003<j10Tg003aj19Tg004?j13Tg004bj22Tg005Uj21Tg006?j28Tg006[j17Tg007Dj24Tg007`j25Tg008;j16Tg009J#0#0#0#0#0#0#9R0#3f0R1,20g009o1101R2'8%70,42'5P1f1,10#6eb0W1o"). Qed.
Lemma zr_bv : forall n (x : bv n), (n <= 64)%N -> inr64 (bv_unsigned x).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h06__sat1h14__x1h23Hn0h37__arithh44__ffh54__p1h66__sat0h78__varmaph85__with94cstrh:2Hah;4__x2h<1Hh=2Hnh>1nh?1xp;1p;2p;4p;3p;5p;<p;7p;6p;8g004?j1aTg003<j13Tg003aj1JTg00:MR0j2=Tg004bj2`Tg005Uj2<Tg006[j1ITg007Dj21Tg007`j29Tg00:ij1BTg00;Gj24Tg00;dR1j12Tg006?R2j28Tg00<Bj27Tg00<\j4UTg00=Cj1QTg00=fj2NTg00>Nj3MTg00?2j2LTg00?Sj1KTg00@3j1HTg00@Sj2?Tg00A1j1GTg00AOj1FTg00B:j2:Tg00B]j2@Tg00C@j46Tg00Ckj1ETg00DMj2DTg00Doj2OTg00E[j3PTg00F5j3CTg00FTj4RTg00GFj1STg00Gdj4_Tg00HBj5^Tg00Hij5]Tg00INj4WTg008;j1XTg00Iil<YTg00JNj7ZTg00K2j6[Tg00KVj7\Tg00L:j8TTg009oR3f0R4'8p=0g00L^R5g00M<R6P0P1P2g00MZf5R2f4R1f3R0f2R7f1R8P4M<Yp=VP8g00N:R9g00NYR:P:g00O9R;P4g00OYFZp=5P8P9P:P:P;P4E[p=>P7P9P:P:P;P8P4F\p=AP0P9P:P:P;P7P8P4GTp=;%a4g009JR9#3R<#3#3#3#3#3R=#JR>,=81`781<78R?#0%I7,1?'91<07R?#0%B<R@%B=R='4RA,1?1=0>%20RB/8=RCP0PB176BP>P=176=EVP8CUR>PC%Q1RD%21#0RE%22,N@RF113@RGf6RH#2#0f7#2RI,4@,13[[RJ%0@RKg00P9RLf8RM#2RN=M@8UW:RO14@NRN#0\L^:KRKP8g00PU1L3@'7PGeO1RL%0I113N[RNp-0RIg00Q;RP#KRQ%HPRP1?68RR%G6RS%F6RTP61:63RUg00QgRV1@69R9C6,5TRW1>T05AT%E:R:PWC;1DT;R;P4P7g00RNRWg00RnR0'71O47=PW0dAC638CRR3b4b7b8X16W5%04/98%08[^16^5IP4f9R0/<MRM%20R0,4@RW'1PMPHO3b3b0b6b0b9b2P?14@BPAP>PCPDPEPFPJPOPKPLPNPQPPP61?67P8%S6RAC_PSPT1>T1P6P9g00SNR11@6<C6,5TR<5ATP:P<C;P;P3b4b7b8X16X;6X5I1148,971187[^16^;6^5IP4%0MPWPMPHO4b3b0b6b0b9b2P@PBP=P>PCPDPEPFPJPOPKPLPNPQPPPAPSP6PUP11:6@C6,5TP;P3b4b7b8PGP4b3b0b6b0b9b2P>PCPDPEPFPJPOPKPLPNPQPPPRPSPTP6P9PV1:6=C6,5TRTP:PTC;P;P3b4b7b8X16184=188=[^16P4P0P2O2b3b0b6b0b9b2D^D]CW%X?eb<W=W?X>5o"). Qed.
Lemma zr_lit : forall z, (0 <= z < 2^64)%Z -> inr64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01zp;2p;1g006?j25Tg003<j10Tg00:ij11Tg00;Gj22Tg007Dj24Tg007`j23Tg00M<g009of0R0'5g009J#0R1#1%01#0#0#0#0#1'2,40'3P0UW0o"). Qed.
Lemma zr_mod64 : forall e, inr64 (e mod 2^64).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h02Hah16__sat1h27__arithh34__ffh46__sat0h58__varmaph65__with71ep;1p;2p;3p;4p;7g003<j10Tg00:ij12Tg00;Gj2=Tg00=fj26Tg007Dj25Tg006?j21Tg00>Nj3>Tg00?2j2<Tg00<Bj23Tg00?Sj1:Tg00@3j17Tg00GFj18Tg00A1j19Tg00AOj1JTg00B:j24Tg003aj1ITg00T5j3HTg00C@j4GTg00JNj7ETg00DMj2?Tg00Doj2@Tg00E[j3ATg00F5j3BTg00FTj4CTg00TXj3DTg00U?j2;Tg008;j1FTg00M<R0f0R1g009J#0R2#2R3%02#0#0#0#0R2#2R4'=R51634g009oR6/53R711641565R8[R9[1163R:g00P9R;f1R<9>34UW01165\;^0:P<g00PU1<63'3P7eO1P9g00Q;R9#:%79%80%90%J0R9g00N:g00NYR7P7g00O9R7P01406g00SN1403%I25H0CGg00OYFE1?97P1f2R7g00RNR9g00RnR2'31@17=A92dAB06<CCb3b5b6P8P1b2b1b4b13D1;15#FeW7o"). Qed.
Lemma zr_mod : forall e k, (0 <= k <= 64)%Z -> inr64 (e mod 2^k).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h06__sat1h14__p1h24__x1h37__arithh44__ffh56__sat0h66__sat2h78__varmaph85__with92Hah:4__x2h;1Hh<2Hkh=1eh>1kp;1p;2p;4p;3p;5p;7p;6p;8g003<j13Tg00:ij1>Tg006?j27Tg007`j24Tg00;Gj21Tg00?Sj1OTg00@3j1HTg00GFj1GTg00A1j1ETg00AOj1DTg00B:j2:Tg00C@j46Tg00DMj2WTg00<Bj2@Tg00Doj2VTg00E[j3UTg00F5j3TTg00FTj4NTg007Dj22Tg00@Sj2?Tg00B]j2=Tg00Ckj1FTg00=fj4Ij2CTg00TXj3JTg00U?j25Tg00U_j2KTg00>Nj3LTg00?2j2MTg00Gdj4BTg00HBj5PTg00Hij5QTg00INj4ATg008;j1RTg00JNj7STg00K2j6ZTg00KVj7YTg00L:j8XTg009oR0f0R1'7p=0f1R2g00N:R3g00NYR4P4g00O9R5P1g00OYFSp=8P2P3P4P4P5P1EZp=<f2R6P3P4P4P5P2P1FYp=9f3R7P3P4P4P5P6P2P1GXp=;g00M<R3%01R8g009JR9#3R:#3#3#3#3#3#>R;,71R<'4%>:R=/12R>P=P2g00Q;R?#OR@%H?R?%G3RA%E3RB%D3RCP31:30RDg00SNRE1:3=C6'81WC5R5P1P6g00RNRFg00RnRG'@1V16=UFGdAT302CNRGb4b7b8120=RFP1b3RHp-0RIP@P?1?32RJPBPCP3PDg00QgRD1=39R9C6,8CRK1<C7RL59C%F4R4PKC;P5PGb4b7b8X23W1RK1482%02[^23^1IR8P1176;P6P2O3b3CI5J6156>RM#012M>'411=6R>,57RN#011=;RO,2N1K7>RP%0711=7#0f5RQf4RR,1='5#0[[RS1C=7R7%0R11=Q,20[\FRT%0=RUg00P9RVf6RW=L=2UW9RX11=WRY#0\V^9URUP2g00PU1M0='@PFeO1RF%0Q120Y[RYPKP8P1f8f7R8,1=RK'5R0/2KP0PQO3b3b0b5b0b6PNP>POPPPSP7PTPXPUPFPYP@P?P31?36P2PACBPBPC1<CRP3P9PE1=3:C6,8CR:59CP4P:C;P5PGb4b7b8X23X:3X1I1212,461226[^23^:3^1IP1%00PKP0PQO4b3b0b5b0b6P=P6P;PPPSP7PTPXPUPFPYPHb0b5b0b6PPPSP7PTPXPUPFPYP@P?PJPBPCP3P9PD1:3;C6,8CRD99CLP4PDC;P5PGb4b7b8X23X1I142<172;[^23^1IP1%08P8PWO3b3b0b5b0b6DPDQCAb;%RMeW<X>3W=o"). Qed.
Lemma zr_mod_any : forall e p, (0 < p <= 2^64)%Z -> inr64 (e mod p).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h06__sat1h14__x1h22Hah37__arithh44__ffh54__p1h66__sat0h78__varmaph85__with94__x2h:1Hh;2Hph<6__sat2h=1eh>1pp;2p;1p;3p;6p;4p;7p;8g007Dj21Tg003<j13Tg00:ij1>Tg00;Gj2FTg006?j27Tg007`j24Tg00=fj2UTg00>Nj3MTg00?2j2GTg00<Bj2=Tg00?Sj1DTg00@3j1CTg00@Sj2BTg00A1j1ZTg00AOj1VTg00B:j2ATg00B]j2@Tg00K2j6TTg00Ckj1OTg00DMj2NTg00Doj2LTg00E[j3KTg00F5j3JTg00FTj4HTg00TXj3ITg00U?j2:Tg00U_j2ETg00VPj19Tg00Voj2<Tg00WXj3?Tg00XAj2PTg00Xmj3QTg00GFj1RTg00Gdj4STg00C@j48Tg003aj1]Tg00T5j3\Tg008;j1[Tg00JNj7YTg00KVj7WTg00L:j8XTg009oR0f0R1'7p=0g00M<R2f1R3g00SNP1C8p=6P3g00N:R4g00NYR5P5g00O9R6P1g00OYFYp=2f2R7P4P5P5P6P3P1FWp=5f3R8P4P5P5P6P7P3P1GXp=;1101R9g009JR:#3R;#>R<%3;#3#3#3#3R=#>R>'FR?,71'41U<>R@110<RA%0>110?[RB[RC%0<RDg00P9REAM<>3UW2R>%0?\E^2DRDP3g00PU1G0<'=PAeO1RAPBp-0REg00Q;RF#DRG%CFRH1B23%Z2RI%V2RJ1A20RK1@2:R:'6,2JRLPJP4P5P5P6P8ET55J%O5R5PLC;1NJ6R6P1P7g00RNRLg00RnR4'=1L17=KL4dAJ203CHR4b4b7b8X12W514931103[^12^5EP1f5RE/7?PEf4R9O3b3b0b6b09I731:73RL#011L3'41E87%08R81:E9#0\8[P@PCP>PDPAPBg00YMRB#9RA#9#9,<21<2A1<2B5?25?2g00Yl'P=QFGPHP21B27P3%R2CSPIPJP2PKg00QgRIP:C8,2JRH1@2;R;,6:,2J55JP5PJ16K;,2JP2P;PI1A2<%]=5\2R=C8,2J55JP516:=,2J95JHC;C;P6P4b4b7b8X12X92%011113'41107177?'4%07117?'4[[^12^92P1f7R1f8/:1PEf6O4b3b0b6b0b<b:%[LeW;X>2X=2o"). Qed.
Lemma zr_land_l : forall a b, inr64 a -> (0 <= b)%Z -> inr64 (Z.land a b).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h04__x1h16__sat1h24__x2h34__x3h47__arithh54__ffh68__varmaph75__with81ah92Hah:6__sat2h;1bh<2H0h=6__sat0h>1Hh?3Ha'h@2HnhA3HnzhB4__p1hC6__sat3hD4__x4hE1ei001ehF1si011shG2z0hH2H1hI3HazhJ2HbhK1zhL2z1i021np;1p;2p;3p;4p;6p;:p;7p;8g008;j1NTg003<j18Tg00:ij1QTg00;Gj2HTg007Dj20Tg00ZXj21Tg00[6j2fTg00[[j27Tg00\5j2:Tg00=fj2`Tg00>Nj3]Tg00?2j2\Tg00<Bj2YTg00?Sj1tTg00@3j1qTg00@Sj2GTg00Gdj4CTg00A1j1kTg00AOj1jTg00B:j2KTg00B]j2;Tg00\Nj1STg00Ckj1cTg00DMj2bTg00Doj2aTg00E[j39Tg00F5j3_Tg00FTj4^Tg00]3j2PTg00]Sj16Tg00]lR0j2OTg00GFj1[Tg003aj1ZTg00T5j3uTg00^Lj6Xl:rTg006?j2<Tg00^jj1sTg00_Lj14Tg00_jj3pTg00`Pj4mTg00a3j2LTg00aPj2lTg007`R1j2DTg00VPj1ETg00Voj2?Tg00WXj3FTg00XAj2UTg00Xmj3TTg00K2j6iTg00INj4hTg00C@j4ITg00JNj7gTg00b2j7nTg00bVj7oTg00L:j8MTg00c:j6eTg00KVj7dTg009oR2f0R3'<p=2g00M<R4f1R5g00QgP3CIp==P5g00N:R6g00NYR7P7g00O9R8P3g00OYFgp=3f2R9P6P7P7P8P5P3Fnp=JP9P6P7P7P8P5P3Fop=Rf6R:P6P7P7P8f5R;f4R<f3R=P6P7P7P8P9P5P3GMGMp=AA9432p=5P4P5g00SNP3CIp=@P4P5g00c^P3CIp=BP5P6P7P7P8P3Eep=WP=P6P7P7P8P9P5P3GMp=>P9P6P7P7P8P5P3Fdp=V%N5P1%29R>g009JR?#8R@#QRA%8@RB#8#8#8#8RC#QRD'HRE,0911<=#N\>P3%2<RF10;E%2;f7RG/f:11G:RH#2%2G%2:'7':f8RI/1GRJ#210JE1`ADRK102ARL%2D102ERM[RN[RO%2ARPg00P9RQA]AD5UW9RR%2E\Q^9PRPP5g00PU1\2A'YPLeO1RLPNg00Q;RQ#tRS%qQRTP41G49RUP51G4=RVCCRW%k4RX%j4RY1K42RZ1;4?R['=,3YR\1;4@,=Z,3YR]%S?R?,;4R^,=Z,3YR_5JY5RYR`%c7RaPYP_PaP\FA1bY8RbP3P9g00RNRcg00RnRd'Y1a39=9cddA_425C^Rdb5b6b7X04X24X34%23Rc%25Re/7>':%2=RfP>[[^04^24^34P3f;Rgf<Rh11hgP<P;O5b4b1b=b11PJ2%5JRJ%6J'OP0f9RJ/1I#5Ri%6if:Ri/1JRj/0EP3%5jRjP4P2103ERkXK4RlPKPOPRPPPLPNPSPT%[4RmPX1K4A%ZC5u4RC,@Z,3YPbPdb5b6b7PMP3b4b1b=b1Rn11giP3EXWEP3O1%6j1Pg2%5gRj%6j'OP0%5hR0%60f=R0/1h/0EP3%50R0P4P2105ERjf@Ri,19#2%2i,7>':fARo,1=#5#6fBRp,1</0E]A]@]?^9cX841<22REf?Rq,12#2%2q,7E':112i#5#6P4P2PlPn112o%soEXWAW@X?MW9f>RMP3PJPIP:P=M:rWEP3O1%601025R0P11HA5,09%4=/09Rn[Rl%49/051HA9,0=RE[Rr1HA=,0<\nAp953RnP3n2001000000120000000UX;4X84Pr\0^;4^84P311qMRAPDPKPOPRPPPLPNPSPTPWPXPY1B[Z,3Y,WYRsPaPYP`PaPYP_Pa1@Z[,3YR`C>FAPbPdb5b6b7X04X24X34%53g00dERt[Ru17>fRf,:e102=\F[[^04^24^34P3PpfCR>11>pPIPgPhO6b4b1b=b1PqPMPKPOPRPPPLPNPSPT1G45RgPXPYP\PaP\C>PbPdb5b6b7X04Pe\c^04P3P>PMO2b4b1b=b1PICm%4A%4q%4M'L'<P1PlPr%4</0=\EPnP5n2001000000120000000V0X;4X84Pl\0^;4^84P3PoPD%4oR0%4iRl'lRn100l1L0lRE=940'D1<l0A94El'D'7RE%4p/L0R0P4PKPOPRPPPLPNPSPTPWPXPYPsPaPY1B^Z,3Y,WYPaPYAJY\]9RY_PaPYP]PaPYP\PaP`C>FAFAPbPdb5b6b7X04X24X34%5=Pt[1:Ff102;\F\F[[\u^04^24^34P3fGRufFRF'1R2PFPuPJPhPqPiPpO8b4b:b1b:bGb<PnPEP0P4PKPOPRPPPLPNPSPTPgPXPY1@[C,3YRCPaPCC>PbPdb5b6b7X04Pj\k^04P3PuPoO2b4b:b1b:bGb<O4b<10lDPnPEP0P4PKPOPRPPPLPNp-0RNg00YMRL#ERP#ERR#ERO#E,?41?4O1?4R1?4P1?4L5F45F45F4RL5F4g00YlRP'U1ULP=TQS5TQPTP4P4PUP<1G4<CCP5P4PVP<PmCCCCPXPYPYP6P7P7P8P:Ei1;4BRB%S@,;4R@'B,3Y5VY%8?,;4R?/=@,3Y1BB?,3Y5VY5JYPaPY1K4DR?,@@,3YPaPY1=[B,3YPa1@[?,3YC>FAPbPdb5b6b7X04X24X34XD4WBA9459,D<1<=9A945='D'710=DRD1<9=PD[[[^04^24^34^D4^BNP3%4uRu%4FRF'0PFPuP<%42P;P:PGO8b4bCb:bCbLbHb<b>O4b>WIP3O1n200110100021110011102bFWAP3O1n200110100021110011102bFChb@%NHeWJW?W9P5P3O2n2001000000121000000W>X;4X84o"). Qed.
Lemma zr_land_r : forall a b, (0 <= a)%Z -> inr64 b -> inr64 (Z.land a b).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01ah11bh21zp;2p;1p;4p;6g006?j25Tg008;j11Tg00ZXj20Tg00dbj42Tg00f5j24Tg00^Lj63Tg00M<R0g009of1R1'5%11P0f2R2f3R3'0f0R4#1X20P2P3P4P1C210321432E3UUX10W0o"). Qed.
(* [comment removed for export] *)
Lemma land_mask_mod : forall e m, (0 <= m < 2^64)%Z -> Z.land e m = Z.land (e mod 2^64) m.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h06__sat1h14__x1h21bh34__p1h47__arithh54__ffh66__sat0h78__varmaph85__with92Hmh:1Hh;2H0h<2Hah=1ah>1mh?2Hih@1ei001ehA2e0hB1ihC1ni011nhD1ohE1si021sp;1p;2p;3p;4p;6p;7p;5p;8g003<j16Tg00:ij1FTg00;Gj2BTg007Dj21Tg007`R0j2;Tg00ZXj2<Tg00U?j23Tg00fXj20Tg00g9j22Tg00gWj2KTg006?j28Tg00[[R1j2kTg00<Bj2?Tg00=fj2fTg00>Nj3\Tg00?2j2ZTg00?Sj1YTg00@3j1XTg00@Sj2VTg00A1j1UTg00AOj1TTg00B]j2STg00B:j2DTg00Ckj1RTg00DMj2PTg00Doj2OTg00E[j34Tg00F5j3MTg00FTj4LTg00h<j4NTg00^Lj6=j7iTg00]3j2QTg00]Sj1ETg00]lR2j2JTg00hgj1jTg00C@j4ATg00K2j6hTg00_Lj1@Tg00_jj3eTg00c:j6bTg003aj1`Tg00T5j3[Tg00Hij5]Tg00iGj4^Tg00j0j4_Tg00jLj1HTg00jlj6aTg00kHj3GTg00kkj3cTg00JNj7dTg00L:j8WTg00KVj7gTg009oR3f0R4'8p=:g00RNR5f1R6;44p=5g00M<R7P6g00SNP4CAp=CP6g00N:R8g00NYR9P9g00O9R:P4g00OYFdp=7f3R;P8P9P9P:f2R<P6P4GWp=9A4743p=>P<P8P9P9P:P6P4Fgp=I%:4R=g009JR>#6R?#FR@%6?#6#6#6#6R?#FRA'BRB,14RC';RD1<<613<B/<6P5f4RE/0610;6RF'2f5RG/3B/<E/0<,54X25P513EBRH/06/2F10G<10E<'2/54X251K6A116ARF18A6RI'kP111<A18A<f6R1/0;10G;RJ'2131B/0;/2J'5P411;AP5f7RJ/0ERKf8RL/0GRM10JGRN'2124N'5X25101ERO,2K,?513JB/0EPJPAPE1f@ARK113@RP%:A113BRQ[RR[RS%:@RTg00P9RUA\@A6UW<RV%:B\U^<TRTP6g00PU1Z3@'?PPeO1RPPRg00Q;RU#YRW%XURU1V76RX%U7RY%T7RZ1S7>R>1D7AR['C,7ZR\%R9R]P\C91PZ:R\P4P<g00RnR^,?51O4<=45^dAM736CLR^b5b7b8X17114APF[^17P4PLPEO2b4b0b6b0CNE=W:P4O118A;P5POg00lNRF1Q13%>1R_%E_'JP2%>JR2%E210L1=45FP4%>LR2P7P3f9R_,06=45F^9DX>71833/;Q%jLW9P_P4PLFiWAP4O1%E2P_PJPKPSPVPTPPPRp-0R2PWPUPXPYPZP71D73RQg00QgRDP>CA,7ZR`PZP8P9P9P:P;EhRa5IZRbP]P`C9P\P^b5b7b8X17W31;=6%:6R`[^17^32P4f=Rc/1BPcf<O3b4b0b6b0%@_PAPJ1136RdP01B@6,1<%@;/1<[R0%@</161B@<,1;Re[%@E/1;\eAe<64P6n2001000000120000000UX27X=7P0\d^27^=7P4f:PAPKPSPVPTPPPRPWPUPXPYPZPZP8P9P9P:P7P>g00c^PQCA,7ZEbP]PZPbP]1CQ>,7ZC9C9P\P^b5b7b8X17X32%>4g00dE[1;`<113<[[^17^32P4f>R</1BP<PGPcO4b4b0b6b0PKPSPVPTPPPRPWPUPXPYPZ1D7@%`?5[7,C>,7ZR?9IZaP]P?C9P\P^b5b7b8X17X321;6C116B[^17^32P4%:<P<PcO3b4b0b6b0O4b;PKPSPVPTPPPRPWPUPXPYPZP7P[PDP>CA,7ZRZP]PZC9P\P^b5b7b8X1718A4PI[^17P4f;PJO2b4b0b6b0D]C^WCP4O1n200110200021010011101bEC_A45FOP5PF10_1/2413_B/01R1/24'5X25P5PF121F,54X25P5PFA45F4X251?5F13LB/0GRG/2F%HGE=12MF%HME=PNP4Eab;W:P4O1n200100000021100011000bD1<H;/06AGH;6E=1<E;/06AGE;6E=X?=XB73cW9X>7X@7o"). Qed.
Lemma zr_land_lit : forall e m, (0 <= m < 2^64)%Z -> inr64 (Z.land e m).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h02Hah16__sat1h21ah31bh41Hh52Hmh67__arithh74__ffh86__sat0h98__varmaph:5__with;1eh<1mh=1zp;1p;2p;3p;4p;7p;6g003<j11Tg00:ij15Tg00;Gj2;Tg007Dj22Tg007`R0j2NTg00U?j23Tg00ZXj26Tg008;j1=Tg00TXj3<Tg00=fj2:Tg00>Nj38Tg00?2j29Tg00<Bj27Tg00?Sj1PTg00@3j1OTg00GFj1MTg00A1j1CTg00AOj1BTg00B:j24Tg003aj1@Tg00T5j3ATg00C@j4?Tg00JNj7>Tg00DMj2DTg00Doj2ETg00E[j3FTg00F5j3GTg00FTj4HTg00lnj4ITg00nAj3JTg00^Lj6KTg006?j2LTg009oR1f0R2'Lp=0g00M<R3%02g009J#1R4#5R5%14#1#1#1#1R4#5R6';R7,22'NP3f2R8/37R9f1R:'6%=2X=3P9P:1212R9P0138:R0#0R;120:f3R0/38#0A<8:2P:n2001000000120000000UX33X23P;\9^33^23P2P0P71:561215R0%061217R9[R;[%05R<g00P9R=A856:UW0%07\=^0<P:g00PU1915'7P0eO1P;g00Q;R;#P%O;%M3%C3%B3R;g00N:g00NYR0P0g00O9R0P31431g00SN1435%@45A3C?g00OYF>1D;0P2P8g00RNR0g00RnR;'71E28=F0;dAG31:CHb7b9b:P9P2b6b1b8b1O3b4P2CI168:AJ8:2EKW5X<3W;o"). Qed.
Lemma zr_lor : forall a b, inr64 a -> inr64 b -> inr64 (Z.lor a b).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h06__sat1h12Hah27__arithh36__sat0h44__x1h52Hbh64__ffh78__varmaph85__with91ah:1bp;1p;2p;3p;4p;7p;8g008;j19Tg003<j10Tg00:ij14Tg00=fj2=Tg007Dj22Tg006?j21Tg00;Gj2JTg00>Nj3ATg00?2j2?Tg00<Bj26Tg00?Sj1<Tg00@3j1;Tg00@Sj2:Tg00A1j1PTg00AOj1OTg00B:j28Tg00B]j2NTg00C@j47Tg003aj1ITg00T5j3HTg00KVj7BTg00Ckj1@Tg00L:j8CTg00DMj2DTg00Doj2ETg00E[j3FTg00F5j3GTg00FTj4>Tg007`j25Tg00oXj4KTg010gj2LTg00JNj7MTf1R0g00N:R1g00NYR2P2g00O9R3f0R4g00OYFMp=3g00M<R5%90R6f3R7f2R8g009JR9#0R:#4R;%0:#0#0#0#0R:#4R<'=R=g009oR>/2;R?11><1J;<R@,2>[RA[RB11>;RCg00P9RDAA;<0UW1R<11>@\D^1CRCP0g00PU1?>;'6P?eO1R?PAg00Q;RD#<%;D1:50%P5%O5RDP1P2P2P3PDP1P2P2P3P5185>g00Qg1N59R9C7,3DP5P9g00SN185;%I:5H5C7,3DFBR:%@2P:GC1DD3P4P8g00RNRDg00RnR3'61E48=FD3dAG5>0C>b6b7b8X45R311>4124@'511>0120@'5[^45R@P4f7f5O2b2b0b3b0P=PBP<PCP?PAP3P@P4f6f4O2b2b0b3b0CK1L78#9eX56W1X:5W9o"). Qed.
Lemma zr_lxor : forall a b, inr64 a -> inr64 b -> inr64 (Z.lxor a b).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h06__sat1h12Hah27__arithh36__sat0h44__x1h52Hbh64__ffh78__varmaph85__with91ah:1bp;1p;2p;3p;4p;7p;8g008;j19Tg003<j10Tg00:ij14Tg00=fj2=Tg007Dj22Tg006?j21Tg00;Gj2JTg00>Nj3ATg00?2j2?Tg00<Bj26Tg00?Sj1<Tg00@3j1;Tg00@Sj2:Tg00A1j1PTg00AOj1OTg00B:j28Tg00B]j2NTg00C@j47Tg003aj1ITg00T5j3HTg00KVj7BTg00Ckj1@Tg00L:j8CTg00DMj2DTg00Doj2ETg00E[j3FTg00F5j3GTg00FTj4>Tg007`j25Tg011Dj4KTg012Tj2LTg00JNj7MTf1R0g00N:R1g00NYR2P2g00O9R3f0R4g00OYFMp=3g00M<R5%90R6f3R7f2R8g009JR9#0R:#4R;%0:#0#0#0#0R:#4R<'=R=g009oR>/2;R?11><1J;<R@,2>[RA[RB11>;RCg00P9RDAA;<0UW1R<11>@\D^1CRCP0g00PU1?>;'6P?eO1R?PAg00Q;RD#<%;D1:50%P5%O5RDP1P2P2P3PDP1P2P2P3P5185>g00Qg1N59R9C7,3DP5P9g00SN185;%I:5H5C7,3DFBR:%@2P:GC1DD3P4P8g00RNRDg00RnR3'61E48=FD3dAG5>0C>b6b7b8X45R311>4124@'511>0120@'5[^45R@P4f7f5O2b2b0b3b0P=PBP<PCP?PAP3P@P4f6f4O2b2b0b3b0CK1L78#9eX56W1X:5W9o"). Qed.
Lemma zr_shiftr : forall a k, inr64 a -> (0 <= k)%Z -> inr64 (Z.shiftr a k).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h06__sat1h14__x1h22Hah37__arithh44__ffh56__sat0h68__varmaph75__with82Hkh91ah:1kp;1p;2p;3p;4p;7p;8g008;j1:Tg006?j21Tg003<j10Tg00:ij19Tg00=fj2QTg007Dj22Tg00;Gj2JTg00>Nj3BTg00?2j2@Tg00<Bj25Tg00?Sj1>Tg00@3j1<Tg00@Sj2;Tg00A1j1PTg00AOj1OTg00B:j23Tg00B]j2LTg00C@j47Tg003aj1ITg00T5j3HTg00KVj7CTg00Ckj1ATg00DMj2DTg00Doj2ETg00E[j3FTg00F5j3GTg00FTj4?Tg007`j26Tg0132j4KTg014Dj2=Tg00JNj7MTg00L:j8NTf1R0g00N:R1g00NYR2P2g00O9R3f0R4g00OYFMp=4f3R5P1P2P2P3f2R6P0P4GNp=8g00M<R7%:0g009oR8/10R9P5P6g009JR:#0R;#9R<%0;#0#0#0#0R;#9R='QR>128<R?118=1J<=R@,28[RA[RB118<RCg00P9RDAB<=0UW2R=118@\D^2CRCP0g00PU1@8<'5P?eO1R?PAg00Q;RD#>RE%<DRD1;70RF%P7RG%O7RHPHP1P2P2P3P71378g00Qg1L7:R:C7,4HR1P7P:g00SN137<%I;5H7C7,4HFCR;%A2R2P;C81DH3R3P4P6g00RNR;g00RnR<'51E46=F;<dAG780C?R<b4b6b7X171184R8124@'6120@,69[^17P4f7f5O2b3b0b5b0P>PBP=PCP?PAPEPDPFPGPHP1P2P1C8P3P<b4b6b7X17P9\8^17P4f6f4O2b3b0b5b0CK1=56#:eW8W2X:7W9o"). Qed.
Lemma zr_div : forall a k, inr64 a -> (0 < k)%Z -> inr64 (a / k).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h06__sat1h14__x1h27__arithh34__ffh46__sat0h58__varmaph65__with72Hah84__x2h91Hh:3Ha'h;2Hkh<1ah=1kp;1p;2p;3p;4p;5p;7p;8g008;j1=Tg003<j10Tg00:ij19Tg00;Gj2VTg007Dj26Tg014dj2>Tg00=fj2HTg00>Nj3GTg00?2j2FTg00<Bj2ATg00?Sj1dTg00@3j1[Tg00@Sj2CTg00A1j1UTg00AOj1TTg00B:j2@Tg00B]j2?Tg00Ckj1OTg00DMj2NTg00Doj2MTg00E[j3LTg00F5j3KTg00FTj4ITg015Aj4JTg00VPj1:Tg00Voj27Tg015bj3<Tg016Kj2QTg00WXj3ETg00XAj2RTg00Xmj3STg00GFj1cTg00Gdj4bTg0174j5aTg003aj1ZTg00T5j3YTg017Xj3XTg018;j2WTg006?j2BTg018Xj5\Tg019Dj5]Tg00INj4^Tg00C@j4DTg00JNj7_Tg00L:j8`Tg009oR0f0R1'Bp=2%01#0#0#0p=e1601p=5g00M<R2f1R3g00QgP1CDp=8P3g00N:R4g00NYR5P5g00O9R6P1g00OYF_p=3f3R7P4P5P5P6f2R8P3P1G`p=1P2P3g00SNP1CDp=;%01#0p=P%01#0#0#0#0#0#0#0p=4%=3g007`%28R9g009JR:#0R;#9R<%0;#eR=#9R>'VR?,68%58R@f4RA/>7#=[P1%2Af5RB/6?%5Bf7RCf6RD'>RE#216E?PCPD1H<>RF%5<RG%2>%5?[RH[RI%2<RJg00P9RKAG<>3UW7R>%2?\KRK^7JRLP3g00PU1F0<'APGeO1RGPHg00Q;RM#dRN%[MRO1C23RP%U2RQ%T2RR1@20RS1?2:R:'8,3RRT%O5RUPTC11NR6RVP1P8g00RNRWg00RnRX'A1M18=LWXdAK203CIR0b3b5b6X12%21%23[^12P1f;RXPDO2b2b0b4b0PFPIP>PLPGPHPNPOPPPQPR1;S:,3RRWPUPWC1PVP0b3b5b6X12%51%53[^12P1f:RWPAO2b2b0b4b0RYCJPEPCP?PCPDPCPYPFPIP>PLPGPHg00YMRY#:RC#:RZ#:,72172Y5<2%P=#4#4#4#4#4#4#4#9,Q2172C172Z5<25<25E2g00Yl'R=SMNPOP21C28P3%c2CbPQPRPR1@2<R<,8S,3RPUPRPRP4P5P5P6DaPU%Z=9Y2<R<,8S,3RC1C1PUPR1?2;R;,;S,3RPUPRPTPUAX2;:,8:,3RC1C1C1PVP0b3b5b6X12X82PK\J1WA7,B7\9\@[^12^82P1PWPXP8PAPDO5b2b0b4b0D\PFPIP>PLPGPHPNPOPPPQPR1;:<,3RRRPUPRC1PVP0b3b5b6X12161?163?[^12P1PXPBO2b2b0b4b0D]C^%=EeW;W:W7P3P1O2n2001000000121000000W9X=2X<2o"). Qed.
Lemma zr_b2z : forall b, inr64 (Z.b2z b).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01Hh12H0h23Heqh31eh41bi001bi011cp;1p;3p;6p;2p;4g019ij11Tg008;j12Tg00E[j30Tg00jlj63Tg01:Fj26Tg00<Bj25Tg00INj44Tg00RNR0P0f0R0#1#2P0g00PUR1g01:eR2g01;KR330R4g00dER5[A0122R6P0P4P1P2P1p-0R7P0P5g00P9R8P5n011010003000000X31g01<1R9P3P0E3P51650R:b1b2X041512R2C4g00Rn#1#2eg01<MR4=013R;P5[P6P0P;P1P4P1P7P0P8P5P5n011010003000000X31P9P3P0E3P5P:b1b2X0;P2C4g00lN#1#2en0110000020000W4o"). Qed.
Lemma zr_ite : forall (b : bool) x y, inr64 x -> inr64 y -> inr64 (if b then x else y).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01xh11yh21Hh32H0h41bi001bp;1g008;j10Tg00RNR0P0g00M<R1f1R2#0R3P0P1f4f3f2n0110000020000#0\3[^11]0f0R0P2X33X23X11X01P0X33X23X11X01n0110000020000W4o"). Qed.

Lemma inr64_unsigned_lit : forall e, inr64 e -> bv_unsigned (Z_to_bv 64 e) = e.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01Hh11ep;1p;2g008;j11Tg01=3j20Tg00M<f0R0#1f1/00W0W1o"). Qed.

Ltac is_Zlit_zb a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

(* [comment removed for export] *)
Ltac slim := repeat match goal with x := _ : Z |- _ => clearbody x end.
Ltac flia := first [ assumption | slim; lia | lia ].

(* [comment removed for export] *)
Ltac zrange :=
  lazymatch goal with
  | |- inr64 ?e =>
      lazymatch e with
      | bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
      | Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
                              | apply zr_land_l; [zrange | zrange_nonneg] | apply zr_land_r; [zrange_nonneg | zrange] ]
      | Z.lor _ _ => apply zr_lor; [zrange | zrange]
      | Z.lxor _ _ => apply zr_lxor; [zrange | zrange]
      | Z.shiftr _ _ => apply zr_shiftr; [zrange | flia]
      | Z.modulo _ (2^64)%Z => apply zr_mod64
      | Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
      | Z.div _ _ => apply zr_div; [zrange | flia]
      | Z.b2z _ => apply zr_b2z
      | (if _ then _ else _) => apply zr_ite; [zrange | zrange]
      | _ => first [ apply zr_lit; flia
                   | is_var e; progress (unfold e); zrange ]   (* [comment removed for export] *)
      end
  | |- (0 <= ?e < _)%Z => change (inr64 e); zrange
  end
with zrange_nonneg :=
  lazymatch goal with
  | |- (0 <= ?e)%Z =>
      first [ apply (proj1 (A:=(0 <= e)%Z) (B:=(e < 2^64)%Z)); change (inr64 e); zrange
            | apply Z.land_nonneg; left; zrange_nonneg
            | apply Z.lor_nonneg; split; zrange_nonneg
            | apply Z.lxor_nonneg; split; zrange_nonneg   (* [comment removed for export] *)
            | apply Z.shiftr_nonneg; zrange_nonneg
            | apply Z.shiftl_nonneg; zrange_nonneg
            | flia
            | is_var e; progress (unfold e); zrange_nonneg ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_bv_mod64 : forall e, Z_to_bv 64 (e mod 2^64) = Z_to_bv 64 e.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h02Hah16__sat1h22b1h32b2h41nh51zh61Hh77__arithh84__ffh96__sat0h:8__varmaph;5__with<1ep;1p;3p;2p;4p;7p;6g004?j13Tg00E[j30Tg005Uj21Tg01>Hj3@Tg003<j12Tg003aj1OTg00:ij1;Tg00;Gj2DTg00U?j29Tg01>lj24Tg01?Rj25Tg00=fj2>Tg007Dj2:Tg006?j26Tg00>Nj3QTg00?2j2PTg00<Bj2=Tg00?Sj1NTg00@3j1MTg00GFj1LTg00A1j1KTg00AOj1HTg00B:j27Tg00T5j3CTg00C@j4ETg00JNj7BTg00c:j6FTg00DMj2GTg00Doj2ATg00F5j3ITg00FTj4JTg01@8j3?Tg01@Yj28Tg00^Lj6<Tg00M<R0g00L^R1f0R2#3R3f1R4#3R5g007`f2R6#3?042f3R7/161174500R8[11641162500%37?064[R9f4#3?076\8A@642P2n2001000000120000000W3W2W4P9^35^23^41P2g009J#2R1#2#2#2#2#2R3#OR5%;1R1%;3R3'DR9,94R8,45R71454R:P01558R;1456,159002X50P01554R<1969,55=002X501>13g009oR=/:1R>16=31:=9[R?[16=1R@g00P9RAAQ134UW016=9\A^0@P4g00PU1P=1'=P>eO1P?g00Q;R?#N%M?%L0%K0%H0R?g00N:R>g00NYR@P@g00O9RAP?P>P@P@PAP01701=C05g00c^170=CEg00OYFBEF1G?AP2P6g00RNRAg00RnR?'=1A26=0A?dAI0=4CJb8b:b;A009=g00dE[P2b7b1b9b19?49A00;<e115:1854E<11571858E<O4b6W<o"). Qed.


(* [comment removed for export] *)
Lemma zb_land_pow2_small : forall y k, (0 <= y < 2^k)%Z -> (0 <= k)%Z -> Z.land y (2^k) = 0%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h06__sat1h12Hah24__x1h31bh47__arithh56__sat0h64__x2h71Hh82Hih94__ffh:8__varmaph;5__with<1yh=1ah>1ih?1ni001nh@1xhA2HkhB3HnehC2HyhD1ei011ehE1khF1si021shG1zp;1p;2p;3p;4p;7p;6p;8g003<j1sTg00:ij1YTg00;Gj21Tg007Dj24Tg007`R0j2BTg00ZXj2JTg00fXj20Tg00g9j25Tg00E[j36Tg00]3j2NTg00]Sj19Tg00]lR1j2rTg014dj2?Tg00U?j2CTg01AHj3^Tg00=fj2ATg00>Nj3DTg00?2j2ZTg00<Bj2>Tg00?Sj1WTg00@3j1VTg00@Sj2FTg00A1j1UTg00AOj1TTg00B:j2OTg00B]j2ETg00C@j4<Tg00Ckj1MTg00DMj2LTg00Doj2PTg00F5j3QTg00FTj4KTg00GFj1RTg00Gdj4STg00KVj7qTg01Aoj3pTg00^Lj68j7hTg01BRj1oTg01C1j2nTg01CYj2:Tg01D6j2fTg00VPj1ITg00Voj2HTg01DWj1aTg01E5j2`Tg01EVj3_Tg00WXj3bTg00XAj2cTg00Xmj3dTg00j0j4eTg00jLj1]Tg00jlj6\Tg01F?j3gTg00hgj1[Tg00kHj3iTg00kkj3jTg006?j2kTg00JNj7lTg00L:j8mTg00c:j6XTg009oR2f0R3'kp=3g00M<R4f1R5;63p=7g00RNR6g00lNR7763p=2A6432p=@P5g00N:R8g00NYR9P9g00O9R:P3g00OYFlp==f3R;P8P9P9P:f2R<P5P3Gmp=;P5P8P9P9P:P3EXp=G%35R=g009JR>#sR?#YR@/13,45'B11@<RA,J;%33RBP6f5RC/05f4RD,1@RE/05'5102<9663X36P6P7f6RF/0<11@C/0<'5=663X361N5D175DRG%9G'rP117<CR1%91f7R1/0;11@F/0;'5#2P317;FRGP4P1f:RH/05f9RI,1@RJ/05'5#2^8BX>4%31P6g00RnRK10HI/53#2X36P6f8RL,0IRM%23X36P010<5#21?;A/C@#@RA[11@5,?</C@#@10;<#2[RN10D;#2\AA^<53P3n2001000000120000000VBX?4X=4PN\B^?4^=4P3PHPI1A@IRN142@RA%3Hf;RO,1@RP,42[RQ[RR%3@RSg00P9RTf<RU=D@5UW1RV11@URW#3\T^1SRXP5g00PU1Z2@'>PAeO1RY%3O142W[RWg00Q;RZ#WR[%VZR\1F45%U4R]%T4R^P41O42g00Qg1E4>R_C<,=^R`%M9RaP`C;1L^:RbP3P<1>6K1P3<=66KdAQ425CKRcb9b:b;X24RdP=\B^24ReP3f=RfPOO2b4b0b5b0P4P21C3@#@XG41>421?HJPNPRPVPXPYPWP[P\P41F4<P5%R4CSRWP]P^P^P8P9P9P:P`P4P_g00SN1E4?R?C<,=^FqR:PaP:C;PbPcb9b:b;X24X641435,BB145<,B=[^24^64P311@ff>PUO3b4b0b5b09pHJE8O4b715MK%oME811@L/0L1A@LRM%3I11@HRK,42[Rf\ARBAD@O5VTX1SR:%3P\T^1SRPPYPQPdPeP3PUPHO2b4b0b5b0,nLE8W8PDP3P;FhWDP3O1%9GP61:1DRG10ICR9/53#2X36P6PGP7P01:53#217<5#9R0[1753R8#91:<5#2[RX1:;<#2\01f53P3n2001000000120000000X<4X@4PX^<4^@4P3PLPCPMPBP:PPPYPQg00YMRQ#I#I,H4%a>,`41H4Q5_45b4g00Yl'c=dZ[P\PWP]P^P4P?g00c^R]P_C<,=^,G^PaP^P`PaP4P_P]P?C<,=^,G^C;C;PbPcb9b:b;X24X64g00dERc\817<;Pc[\=[^24^64P3PIPUPCPHO4b4b0b5b0O3b7CeA667GP6P710HF/53#2X36%]91:LCP3E\b711@1/0D1A@1%3L142J[\AAD@H5VTX1S%3K\T^1SPYPfPdPeP3POPIO2b4b0b5b09g1DE8WBP3O1n200110200021110111100bF1025%[5E81JCE/05AiCE5E8W8X>47j2XA=WCXE4X<4o"). Qed.
Lemma zb_lxor_pow2_small : forall y k, (0 <= y < 2^k)%Z -> (0 <= k)%Z -> Z.lxor y (2^k) = (y + 2^k)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01kh11yp;2p;1p;4p;3g006?j2:Tg003<j19Tg00:ij12Tg00;Gj20Tg007Dj28Tg007`j27Tg01Ffj23Tg012Tj24Tg01GCj45Tg01H_j36Tg00j0j41Tg00M<R0g009of1R1':R2g009J#9#2R3f0R4'0,81'7P0f3R5f2R6,03R3'31453P5P6P1P4C59653C1V2UX00W1o"). Qed.

Lemma zb_lxor_sign : forall x, (0 <= x < 2^64)%Z -> Z.lxor x (2^63) = ((x + 2^63) mod 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h06__sat1h16__sat3h24__x1h37__arithh44__ffh54__p1h66__sat0h76__sat2h88__varmaph95__with:4__x2h;5heq_yh<1zh=2Hah>1Hh?2H0h@1xhA2HxhB5lemmahC1ohD1yp;1p;2p;3p;4p;6p;9p;7p;8g003<j1:Tg00:ij1ETg00;Gj2MTg007Dj26Tg007`j28Tg00\Nj1=Tg00gWj2fTg006?j2FTg00[[R0j2`Tg012Tj23Tg01Ffj21Tg00U?j27Tg00<Bj29Tg00=fj2XTg00>Nj3WTg00?2j2yTg00?Sj1tTg00@3j1pTg00@Sj2TTg00A1j1gTg00AOj1eTg00B]j2UTg00B:j2BTg003aj1QTg00T5j3PTg00Ckj1_Tg01IIj3HTg00DMj2^Tg00Doj2]Tg00E[j3Gj1sTg00F5j3\Tg00FTj4[Tg01Ilj3ZTg00GFj1|Tg01JOj4YTg01Kkj2<Tg01DWj1{Tg01E5j2zTg00VPj1KTg00Voj2ATg01EVj3VTg00WXj3>Tg00XAj2ITg00Xmj3LTg00Gdj4xTg01LHj3wTg01Lkj1rTg01M[j1oTg01NJj6nTg01O5j2RTg01Oaj6hTg01PBl9iTg017Xj3jTg018;j2kTg00c:j6lTg01Q<j4mTg00jlj6OTg01Q]j1dTg01R?j1qTg00^Lj6STg01Rgj3cTg00C@j4JTg00JNj7bTg00K2j6uTg00KVj7vTg00L:j8aTg009oR1f0R2'Fp=2g00M<R3f1R4;G2p=0P3P4g00SNP2CJp=DP4g00N:R5g00NYR6P6g00O9R7P2g00OYFbp=4P3P4g00QgP2CJp=@P4P5P6P6P7P2Eup=Nf2R8P5P6P6P7P4P2Fvp=?f3R9P5P6P6P7P8P4P2Gap=5P3f4R:P9P8P4P2ESp=;P3P4g00c^P2CJp=C%22g009JR;#:R<#ER=%:<#:#:#:#:R>#ER?'MR@,62'8%=;#=#=#=#=RA#ERB,M=RC,f4164C1FC4'`P0168CR01FC8RD139C119C/7@'0P2169CRE11:CRFf5RG/1CRH/7@,02X<3PF10H2X<3193F17F@1X=BRH161=RI%2BRJ161C[RK[RL%2=RMg00P9RNAW=B4UW=RO%2C\N^=MRP1X=?RQ%2?161@[RR\IRSAW=?4VNX=MR?%2@\N^=MRMP4g00PU1y1='9PIeRIO1RNPRP:PIO1RIPKp-0RTg00Q;RU#tRV%pURW1T34RX%g3RY%e3RZ1U3;R[1B3=R=%QA5P3RA'D,4ZR\%_6R]PZ1B31R^/@[,4ZR_1NZ95?ZR`P]AH3[ARa,@^,4Z%Q>9P3=R=,Da,4Z5?ZC5C51^Z7R>P2P8g00RNRbg00RnRc'91]28=GbcdA\314C[Rcb4b8b9X23W5162CRb%24/88Rd118CRe#216e@'8[[^23^5TP2f;Rf/6@Pff7Rgf:RhO4Rib3b1b0b6b0b7b19ZF@D;13:CP:PBPHPLPOPPPQPSP?PMPNPRPIPKPVPWPXPYPZP\P]PZP`P]A?Z_\R\C5C5P>Pcb4b8b9X23X5T%28/80\d\b^23^5TPib3b1b0b6b0b7b1PHPLPOPPPQPSP?PMPNPRPIPKPVPW%|3RiPY1B3B,@^,4ZP>Pcb4b8b9PJP2b3b1b0b6b0b7b1RJCYD;W>P2O11FC91<:CP31<GCRb,93102bRbePbPHPLPOPPPQPSP?PMPNPRPIPK%{;,z3Rbg00YMRd#KR0,A3R`5V31A3dRd5>3g00YlRF'I=LUVPWP31T38P4PiCxRjPYPZ1U3<R<=w3A,C[,4ZRkP]1Ca<,4ZC5P>Pcb4b8b9X23X:31<4C,02Rl114CRm/08[^23^:3P2f=Rnf8PgO3b3b1b0b6b0b7b1b;112CRo/0GP3Pm132C17o@'0X@3134CRG/0mP3%s3Rp%r313eC138CRq/3CPePqP3Pp%o3PqPeP2EnPCPC1R3CEh11eCRe/7@RqPq1R3qM9iWBP4PBf6RB/<CRp,93104pRpeRrPpPHPLPOPPPQPSP?PMPNPRPIPK%K0R0#K,A3RsA>3`d5>3/IFAV3bs1A30=>3d5>3/IF=LUV5LURUPWPjPYPZPkP]PZ1@A<,4ZRFP]PZ1NZ:1D<=,4Z5?ZR<P]P\C5C5C5P>Pcb4b8b9X23X:3X5T169@R\,8:R:%29Rd/8E[\D\l^23^:3^5TP2f>RE#2PEf9R0PgPhPnO6b3b1b0b6b0b7b1b;PrPpPJb;CY13CCRJ,34102qX<3RnP3P11382/0qX<3P4PnPrPpPHPLPOPPPQPSP?PMPNPRPIPKPVPWPXPY%E;R;,B3=j3=9H3[AH3aA'C,4ZP>Pcb4b8b9X231k;@Ra,1211oC'0^23P2P0O1b3b1b0b6b0b7b1b;114a11mC'0P3118aRa172@,09X<3178@Rm1092X<3R9P8P91938Pm1<gCRm,93108mRmeR9PmPHPLPOPPPQPSP?PMPNPRPIPKPUPWPjPYPZPkP]PZPFP]PZP<P]1D[=,4Z9?Z_C5C5C5P>Pcb4b8b9X23X:3X5T18d\\:\D\l^23^:3^5TP2f?RT#2PTPhPgPfPEO6b3b1b0b6b0b7b1b;9Z8@D;17a@P8P;P@P9PmPHPLPOPPPQPSP?PMPNPRPIPKPVPWPiPYPZP5P6P6P71C=^,4ZElP>Pcb4b8b9AG3@1g00dE[P2b3b1b0b6b0b7b1b;CmD;PeP2EOb?1341%d4D;PJ%qCES13GCAc4CCD;O2PBP2EOb?bDW>P2O1n200100000021100011000bCWAX@3o"). Qed.

(* [comment removed for export] *)
Lemma zb_signed : forall x : word,
  bv_signed x = (if bv_unsigned x <? 2^63 then bv_unsigned x else bv_unsigned x - 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h06__sat1h16__sat3h24__x1h37__arithh44__ffh56__sat0h68__varmaph75__with82Hah94__p1h:6__sat2h;1zh<2Hrh=1bi001bh>1li011lh?1ni021nh@1ri031rhA1xp;1p;2p;3p;4p;6p;7p;8g003<j15Tg003aj1LTg004?j1\Tg004bj2STg005Uj24Tg006[j1`Tg007Dj20Tg007`j29Tg00:ij1@Tg00\Nj18Tg00;Gj2DTg01SKj2PTg01Snj2OTg01TKR0j2mTg01Ffj26Tg00U?j2JTg01Kkj23Tg00=fj2NTg00>Nj3MTg00?2j2]Tg00<Bj2GTg00?Sj1[Tg00@3j1ZTg00@Sj2YTg00A1j1XTg00AOj1WTg00B]j2VTg00B:j2BTg00T5j3FTg01IIj3ETg01LHj3=Tg00DMj2RTg00Doj2QTg00E[j3?Tg00F5j3TTg00FTj4UTg00Ckj1nTg00K2j6lTg01Ilj3KTg00^Lj6HTg00]Sj1kTg01DWj1hTg018;j2gTg017Xj3fTg00GFj1cTg01Q<j4bTg00jlj6aTg01Tnj2dTg006?j2eTg00C@j4ATg00JNj7_Tg00KVj7iTg00L:j8^Tg00c:j6jTg009oR1f0R2'ep=2g00M<R3f1R4;?2p=7P3P4g00c^P2CAp=CP4g00N:R5g00NYR6P6g00O9R7P2g00OYF_p=1P3P4g00SNP2CAp=<P3P4g00QgP2CAp=>f2R8P5P6P6P7P4P2Fip=;f3R9P5P6P6P7P8P4P2G^p=:P4P5P6P6P7P2Ejp=Ig009JR:#5R;#5#5#5#5#5R<#LR=#\1S=214=2R>#2%`=,0>'914=4R>%@;R;%8:#8#8#8#8R?#@R@'DRA'P10>A1O>ARB'm14=8/OAg00RNRCP014=9/0Af5,4=R0/6ARD%@<R<,D;RE'JRF/3APCP3P4P0130En0100000020000'7P4f4R0,4=/0ARGP3PD132ARHf6,4=RI'7X;31N;@RJ101;RK%2@101A[RL[RM%2;RNg00P9ROAM;@4UW8R@%2A\O^8NRP1N;<RQ%2<101E[RR\KRSAM;<4VOX8NR<%2E\O^8NRNP4g00PU1]1;'GPKeRKO1ROPRP0PKO1RKPLg00Q;R0#[RT%Z0R01Y34RU%X3RV%W3RW1V3:RX1B3;R;%L?5F3R?5E3RY==3?/CX'11RW7RZP2P8g00RnR[,GC1Q28=?C[dAT314CUR[b4b6b7X23162AR\/3A/72^23P2f<,4=R]O1R^b3b1b0b5b0b:b1PFPJPMP@PPPQPSP<PNPOPRPKPLp-0R_PTP0PUPVPW1<X?,1WR`%n6RaPW1B31Rb/>X,1WPWP5P6P6P7P9ElR95;WPa1>bY,1WAF3;=R;,<Y,1W5;WC:C:PZP[b4b6b7X23W9102AR7%24/98168AR6#2106E'9[[^23^9_P210]EP]f7R5f;RcO4b3b1b0b5b0b:b19KDEEHW>P2O1%kGP3%h:R:/gERG,6DRd/JERe13IE,7HX;3RHP3PdPHPJPMP@PPPQPSP<PNPOPRPKPLPTP0PUPV1B3:=f3;9E3YRY==3?A=3X;'C,1WPZP[b4b6b7X2316\G/3A132E'7^23P^b3b1b0b5b0b:b1PePJPMP@PPPQPSP<PNPOPRPKPLPTP0PUPVPW1IW`PaPW1<X;,1W9;W9Pa1>bY,1W1<Y;,1W5;WC:C:PZP[b4b6b7X23X9_g00dERY\7104E,98166GRG#210GE'9[[^23^9_P2%2]P]P5PcO4b3b1b0b5b0b:b19KdEEHPFPDP:PEPQPSP<PNPOPRPTP0%c3PV1C;b,1W,IWPZP[b4b6b7A?3E1PY[P2b3b0b5b0CbEaW?P2O1n10210010300021110111102b=b@1d=4PCP3PBP>13>En0100000020000'7eb<WAo"). Qed.

Lemma bv_eqb_Z : forall x y : word, bv_eqb x y = (bv_unsigned x =? bv_unsigned y)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01xh11yp;1p;2g003<j10Tg003aj15Tg004?j12Tg005Uj21Tg01CYj24Tg00<Bj23Tg009J#0#0#0#0#0#0#5R0#2R1g00RNf1,10f0,10'4'3X11W0o"). Qed.
Lemma bv_ltu_Z : forall x y : word, bv_ltu x y = (bv_unsigned x <? bv_unsigned y)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01xh11yp;1p;2g003<j10Tg003aj15Tg004?j12Tg005Uj21Tg01Snj24Tg00<Bj23Tg009J#0#0#0#0#0#0#5R0#2R1g00RNf1,10f0,10'4'3X11W0o"). Qed.

Lemma bv_lts_lxor : forall x y : word,
  bv_lts x y = (Z.lxor (bv_unsigned x) (2^63) <? Z.lxor (bv_unsigned y) (2^63))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h06__sat1h16__sat3h26__sat2h34__x1h41zh57__arithh66__sat0h76__sat4h84__ffh98__varmaph:5__with;4__x2h<5lemmah=2Hah>4__p1h?1bi001bh@1ri011rhA1li021lhB1ni031nhC2HxhD2HyhE2l0hF2n0hG1xhH1yp%0p&0p;1p;2p;3p;4p;6p;9p;7p;8g003<j1?Tg003aj1dTg004?j1uTg005Uj23Tg00:ij1RTg00\Nj1CTg00;Gj2aTg01Snj20Tg01Kkj24Tg01Tnj2ZTg012Tj2ETg004bj2jTg006[k104Tg007Dj21Tg007`j2>Tg01Ffj22Tg00U?j27Tg01SKj2_Tg01TKR0j2^Tg01O5j2DTg01UVj2=Tg01V6j3oTg00=fj2YTg00>Nj3XTg00?2j2nTg00<Bj2WTg00?Sj1mTg00@3j1lTg00@Sj2UTg00GFj1kTg00Gdj4iTg00A1j1hTg00AOj1gTg00B]j2fTg00B:j2STg00T5j3eTg01IIj3OTg00DMk203Tg00Dok202Tg00F5k301Tg00FTj4|Tg01Vhj3KTg00Ckj1{Tg00K2j6zTg00]Sj1`Tg01DWj1yTg018;j2xTg01LHj3TTg017Xj3wTg00C@j4PTg00E[j3BTg01Q<j4JTg00jlj6GTg01WJj2]Tg01X`j1\Tg01Z3j3tTg006?j2sTg00\5R1j2VTg01PBl9vTg01Z`j7rTg00JNj7bTg00bVj7qTg00KVj7pTg00L:j8}Tg01Ilj3~Tg00^Lj6cTg00c:k600Tg00RNR2f1R3f0R43Bp=8g009oR5/s4p=6f2R610345B2p=<g00RnR79B261134'Vp=:AB247p=9p-0R8P1g01[[f5R9f4R:f3R;P6P3P4M9vp=LP8P1P:P;P6P3P4Frp=FP6g00N:R<g00NYR=P=g00O9R>g00M<R?P3g00SNP4CPg00OYR@Fbp=5P6P<P=P=P>P3P4Fqp=I1134,V6p=MP?P3g00QgP4CPp=QP3P<P=P=P>P4P@Fbp=NP6P<P=P=P>P3P4Fpp=AP;P<P=P=P>P6P3P4G}p=@P?f6R@P9P:P;A~634Ecp=;P3P<P=P=P>P4J00p=[P?P:P;P6P3P4Ecp=Hg009JRA#?RB#?#?#?#?#?RC#dRD#uS00Q00P2P?13D3RE%RBRF%CA#C#C#C#CRG#RRH'aRI'0PE%RCRC,aFRJ,4En01000000200001ZD3S01,0413D6RK/EIRL1EEIS02'0RM'8X4?P2P?13D4RN/0IPN14NJn0100000020000P2P?10KIPK14KJn0100000020000S03/04/8MX4?1jD3RM%6E&04D,1E'>REPMPE13D;RE/2I/7JP2P?13D:RM/0IROPM14MJn0100000020000P2P?10EIRPPE14EJn0100000020000S04'0RQ1EEIRR7<4X4?12KI/7J12MI/7J=<Q4X4?1_EI11EI/^PPOP2P013D9/1IP2P?P3f7S05,3DRO14OJn0100000020000P2P?13D@R@/0IRPP@14@Jn0100000020000'012OI/7J12@I/7J3<P311@IRQ1_@IS061^QPS0710OIS08P2P0f8,3D/1IS09f;S0:,3DRPP2P?P3f:,3DRM14MJRSn0100000020000S0;'012PIRT/7JRU12MIRV/7JRW'0S0<'8P3f9,3D/1IRXPTf<,3DRY/0PRZ104UR['8X4?PV12YIR\/04R],8ZX4?10PMR^10TVR_A:^PM%9Z11YPRZP410\T#9R^P^1D8^ELW<1=PMA:_TVg01\L9o81R1PZP^11\TP4DFW<1=TV1YFHR^115FRZ%6H115I[R_[R`%6FRag00P9RbAXFH3UW=RH%6I\b^=aRc1YFCRd%6C115J[Re\ZRfAXFC3VbX=aRC%6J\b^=aRaP3g00PU1n5F'WPZeRZO1RbPeP:PZO1RZP_g00Q;Rg#mRh%lgRgP?1U?6P3%k?S0=CiRi%h?Rj%g?Rk1f?ARl1f?BRB55k1S?FRF%dG5e?RG9O?lRmAO?BGRn55k3I203k>RoP4P61W2720246#9dB01?53C|R7b8b9b:X3?X;?1143124IRp123IRq3M^3?^;?P4fA,3DRrfB,3DRsO2Rtb5b7b2b0b2b1b7O2O23KPWPVPJP^P`PHPcPdPfPCPaPbPePZP_PhPg1U?3S0>PjPkA5klGRG%{=RuPk1S?5Rv/Ql,NkS0?PkP<P=P=P>P;EzR;5AkPu1Qvm,NkAe?FDRF95km5AkC@C@PoP7b8b9b:X3?X>8R>114IR=%63S0@/>6126IR<#611<J'>[[^3?^>8RwP411rJPrQ05f?S0AO4b5S0Bb7b2b0b2b1b7F;PUPTPJP^P`PHPcPdPfPCPaPbPePZP_P>PwP411sJPsQ0:f@S0CO4b5S0Db7b2b0b2b1b7F;WEP4O1%`XS0EPT14PJRw,0YR>/8[X4?P?%yARA/xJRx,2VRy/7JRz18>]X4?R]PyP]10PSR]10TyR{A:]PS%9>11YwR>P412TxR],0\#9R|P|1D8|ELW<1=PSA:{TyP1P>P|11\]P4DFW<1=TyP^P`PHPcPdPfPCPaPbPePZP_PhPgPiPjAT?BFR|95kl1S?A=w?FR>9O?nR{95km5IkPoP7b8b9b:X3?X;?143JR},1412qxR~7Mp^3?^;?Ptb5b1b0b6b0b2b1O2O23KPzPyPJP^P`PHPcPdPfPCPaPbPePZP_PhPgQ0>PjPk1[kGPuPkA5klFRG9Ak;PuAO?m>R>,Qv,NkA5k>F5AkC@C@PoP7b8b9b:X3?X>8Rmg00dER;\=113JR=,>612<xR<#611<J'>[[^3?^>8R<P4%6rPrQ05Q0AO4b5Rrb1b0b6b0b2b1F;PWPVPAPJP^P`PHPcPdPfPCPaPbPePZP_PhPgQ0=PjP?PFg00c^PvCP,Nk,[kPoP7b8b9b:AB?J5P;[P4b5R;b1b0b6b0b2b1R5CJEGPUPTPJP^P`PHPcPdPfPCPaPbPePZP_Q0Db1b0b6b0b2b1F;WBP4O1n10210010100021110211103b?b@WAP4O1%`QQ06Q07Q08P2P0Q09Q0;,0wQ0<'8P3PV14YJRY/0PR017\J;<4X4?P?17]JR2A<04TX4?RQP]PQ10wMRQ10]VRvA:QwM%9011YPRPP412\xR\/0T#9R0P01D80ELW<1=wMA:v]VP1PPP011\TP4DFW<1=]VP^P`PHPcPdPfPCPaPbPePZP_PhPgPiPjAT?lFRF=5kBA5k>n5IkPoP7b8b9b:X3?X;?144JRn/1312pxRx;Mq^3?^;?Ptb5b1b0b6b0b2b1O2O23KP2P]PJP^P`PHPcPdPfPCPaPbPePZP_PmP<P4%6sPsQ0:Q0CO4b5Rsb1b0b6b0b2b1F;PUPTPAPJP5CJEGPWPVPJP^P`PHPcPdPfPCPaPbPePZP_Q0Bb1b0b6b0b2b1F;XAXP4O1Q0EP?P210YwRX/8[X4?R[P]P[P?PzA<X\4X4?R[PyP[10wSR[10]yR5A:[wS%9X11YwRYP410\]#9RXPX1D8XELW<1=wSA:5]yP1PYPX11\]P4DFW<1=]yP^P`PHPcPdPfPCPaPbPePZP_PhPgPiPjA5kF|A5k>{5IkPoP7b8b9b:X3?X;?11n}?Mx~^3?^;?Ptb5b1b0b6b0b2b1O2O23KPzPyPJP^P`PHPcPdPfPCPaPbPePZP_Prb7b2b0b2b1b7F;PWPVPAPJPdPfPCPaPbPeP;b0b6b0R;CJEGP2P]PJP^P`PHPcPdPfPCPaPbPePZP_Psb7b2b0b2b1b7F;PUPTPAPJP;CJEGWFP4O1n10210010100021110211103b?b@WBP4O1n10210010100021110211103b?b@PLPdPfPCPaPbPePhPgQ0>PjPkQ0?=AkGRGPuPGC@PoP7b8b9b:X3?R7%64114J'>Q0@/>=[^3?R?P4P@P:O2b5b0b6b0,]KDHPRPdPfPCPaPbPeP7P?P4POP9O2b5b0b6b0,]EDHQ04Q03'0?<RLebDbC1ZD4%\4DHQ01%\3DHAtD34Q021ENI3<eWHWGo"). Qed.

(* [comment removed for export] *)
Lemma bv_lts_zero_r : forall x : word, bv_lts x (Z_to_bv 64 0) = (2^63 <=? bv_unsigned x)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h02Hah14__p1h26__sat1h36__sat3h44__x1h55lemmah67__arithh74__ffh86__sat0h96__sat2h:8__varmaph;5__with<2Hxh=1bi001bh>1li011lh?1ni021nh@1ri031rhA1xhB1zp;1p;2p;3p;7p;4p;6p;9p;8g003<j16Tg003aj1NTg004?j1\Tg005Uj23Tg00:ij1BTg00\Nj18Tg00;Gj2JTg01Snj21Tg01Kkj2>Tg01>lj2YTg01Tnj2CTg01]>j2:Tg00E[j3?Tg004bj2qTg006[j1oTg007Dj20Tg007`j2ATg01SKj2aTg01TKR0j2`Tg00\5R1j29Tg01O5j2[Tg01UVj2FTg006?j2<Tg01V6j3ZTg01Z`j7ETg01][j2XTg00=fj2KTg00>Nj3DTg00?2j2WTg00<Bj2MTg00?Sj1VTg00@3j1UTg00@Sj2TTg00A1j1QTg00AOj1RTg00B]j2STg00B:j2PTg00T5j3OTg00Ckj1pTg00C@j4@Tg00K2j6nTg00DMj2jTg00Doj2iTg00F5j3fTg00FTj4eTg01Vhj3ITg00]Sj1bTg00c:j6cTg01LHj3dTg01X`j1_Tg00^Lj6gTg01Z3j3hTg01PBl9^Tg00JNj7kTg00KVj7lTg00bVj7]Tg00L:j8mTg009oR2f0R3'<p=2g00RNR4g00RnR57?3p=41032p=5p-0R6P1g01[[f5R7f4R8f3R9f2R:f1R;P3M9^p=Gg00M<R<P;g00SNP3C@p=;P;g00N:R=g00NYR>P>g00O9R?P3g00OYFkp=7P:P=P>P>P?P;P3Flp=LP:P=P>P>P?P;P3F]p=HP9P=P>P>P?P:P;P3Gmp==g009JR@#6RA#6#6#6#6#6RB#NRC#\P<P4P<13C3RD%BARA%8@#8#8#8#8RE#BRF'JRG'1PD%BBRB,JARH,>Dn01000000200001YC2RI,CC,1313C;RJ,:G5?4XB<1qC3%2D%oC,0D'A1aJG10JG11JG'`13C:/1GP4P013C9/0GP4P<P;13C7R71>7HR0n0100000020000/121:G7RJ5?4P;13C8/0GRK1172RL%4L%57'9f6,3CRL/12#4%5LRMP31:GL#4RNPN1[6NROEGW51F72%4J1<G7'9RPP6P1g01\L9Z61RQPMPN1<GLRMP3FEW51XG7R71KAFRR102ARS%2F102G[RT[RU%2ARVg00P9RWADAF;UW0RF%2G\W^0VRX1KABRY%2B102H[RZ\SR[ADAB;VWX0VRB%2H\W^0VRVP;g00PU1W2A'MPSeRSO1RWPZP8PSO1RSPTg00Q;R8#VR\%U8R81T<;R]%Q<R^%R<R_1S<@R@1P<ARA%NE5O<RE';,7_R`%p>RaP_P<1P<2Rbg00QgRcP@C@,7_P_P=P>P>P?P9EnR95L_Pa1;@b,7_P<PEPcP@C@,7_Rc5H_C=C=1j_?REP3P:1M451i3:#4dAf<2;CeR5b7b:b;X4<X16103GRd%2;/A:%5:1<G:Re'9[[^4<^16P3f<,3CRf/0HPff7Rgf;RhO4b6b3b2b8b2b9b3O2O27IJW>P3O1%bK1102RK%4K%50'91>LHRL/12#4%5LRLP3PNPNPOEGW51F02P6P1PQPLPNPMP3FEX5PP7PRPUPFPXPYP[PBPVPWPZPSPTP\P8P]P^P_P_P=P>P>P?P`EcPaP_AO<ACRA,;@,7_9L_9PaAd<@A/;b,7_=H_cC=C=PEP5b7b:b;X4<X16g00dE\d10;H,A:1>:H#5/9e[[^4<^16P3%2fPfPgPhO4b6b3b2b8b2b9b3O2O27IJW?P3O1n10210010300021110111102b=b@b<1CC3%_3EgAhC3I1:GD5?4eWAo"). Qed.
(* [comment removed for export] *)
Lemma bv_lts_zero_l : forall x : word,
  bv_lts (Z_to_bv 64 0) x = ((0 <? bv_unsigned x) && (bv_unsigned x <? 2^63))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h05lemmah12Hah26__sat1h34__x1h47__arithh54__ffh64__p1h74__p2h86__sat0h96__sat3h:8__varmaph;5__with<1xh=1Ah>1Bh?2Hxh@6__sat2hA1bi001bhB1li011lhC1ni021nhD1ri031rhE1yhF1zp&0p;1p;2p;3p;4p;8p;6p;=p;5p;9p;7g003<j18Tg003ak101Tg004?j1bTg005Uj23Tg00:ij1CTg00\Nj1<Tg00;Gj2HTg01Snj2;Tg01Kkj2=Tg01>lj2ZTg01Tnj2FTg00g9j25Tg00E[j39Tg004bj2~Tg006[j1pTg007Dj27Tg007`j21Tg01SKj2fTg01TKR0j2dTg00\5R1j2:Tg01V6j3_Tg01^;j2PTg01^\j4>Tg01_Cj3YTg001?j4XTg01_lj2WTg01`YR2j2VTg01a7j4UTg01aYj8MTg01bLj3TTg01cBj4DTg01d5j6LTg01dgl=STg01UVj2OTg00=fj2ETg00>Nj3RTg00?2k200Tg00<Bj2QTg00?Sj1}Tg00@3j1|Tg00@Sj2zTg00A1j1xTg00AOj1wTg00B:j2NTg00B]j2oTg0174j5mTg00DMj2lTg00Doj2kTg00F5j3eTg00FTj4gTg01Vhj3GTg00]Sj1hTg01O5j2iTg01PBl9jTg00T5j3cTg00Ckj1nTg01LHj3aTg01eVj5`Tg00L:j8qTg01X`j1rTg00^Lj6sTg01Z3j3tTg006?j2^Tg01Z`j7uTg00C@j4vTg00JNj7]Tg01f:j6\Tg00KVj7yTg00bVj7[Tg00K2j6{Tg009oR3f0R4';p=61^34p=4g00RNR5g00RnR6794p=2p-0R7P1f4R8f3R9f2R:f1R;P4Fup=?1734p=0g00M<R<P;g00SNP4Cvp=BP;g00N:R=g00NYR>P>g00O9R?P4g00OYR@F]p=@P:P=P>P>P;P4E\p=KP:P=P>P>P?P;P4Fyp=AP:P=P>P>P?P;P4F[p=IP;P=P>P>P?P4E{p=Jg009JRA#8RB#8#8#8#8#8RC$01RD#bP<P5P<13D4RE%CBRB%<A#<#<#<#<#CRF'HRG';RHPE%CCRC,HBRI,=En01000000200001ZD3RJ,FD/;413D;RK#61;KGRL'5595XF<1~D4%4E%pD,7E'11fKG17KG/dL13D:/;GP5P013D9/7GP5P<P;f5,3DR01=0IRLn0100000020000#6%60RK/5;595P;13D8/7GRM15K6RN%2N%2KRNA9566RO'1':g01\L9_71RPf6,3DRQ#6RR#2RS15R6#211SORTP4D?W01PK6%00,:NRUP7^>7RV^=7P7P7\7P1P7P7P1P1C>RWC>P1AY71PP7PVP1P7P7P1P7P7P7P2CXR2C>RXC>P@P7PVP1P11W71RVPWPXP7P7P1P1PVP1P2P7P11V4;XE7X<7g01f^CUGMGMPS%0QR2P4PT112OPSP2P4POPOP7P1g01gT9T71RTPOCDELM=SW01O30R01EBF%0BRV%4F%0G[RX[%4BRWg00P9R@ARBF;UW1%4G\@^1W1EBCRG%4C%0I[RF\VRYARBC;V@X1WRC%4I\@^1WRWP;g00PU2003B'QPVeRVO1R@PFP8PVO1PXg00Q;RX#}RV%|XRX1z<;RZ%x<R[%w<R\1N<3R]1o<ARA'B,@\R^P\P=P>P>g01hDR_DmR`=K\`9A\^3I1l\?R^P4P:1Q561k4:#2dAe<3;CgR:b5b:b;X3<%04Ra11aO':^3<P4f<,3DO1b4b9b2b8b2b@b9O2O25GKWBP4O1%hM%6LRMg00lNRa,5KRO%2OA95a6R6,1N':PP1=QIRQ#6#2RN15Ra#211S6RRP4D?W01PKa%2M%0L':P7P1g01[[PN%0QRQP4PRPR1i7RM9jW01O3LPPPQPR1126PSP2P4P6P6P7P1PTP6CDELD?X0UP0PGPYPCPWP@PFPVPXPZP[P\P=P>P>P?1J\91N<B=c<DRB,BA,@\5A\%n>Aa<AB,B],@\1J\8P\P=P>P>P_D`=K\`5A\5I\GqP^P:b5b:b;X3<X67X77174I,1;1=;I#01196':[^3<^67^77P4f9,3DR7#0%47P7f8O4b4b2b8b2O2O2O23GWCP4O1n10210010300021110111102bAbDb?1FD4%r4EsAtDJ4%6E/5H595eW<o"). Qed.

(* [comment removed for export] *)
Lemma v_sltu_b2z : forall x y : word, v_sltu x y = Z_to_bv 64 (Z.b2z (bv_unsigned x <? bv_unsigned y)%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bh11xh21yp;1p;2p;3g003<j11Tg003aj1:Tg004?j17Tg005Uj25Tg01Snj29Tg00:ij18Tg01>lj20Tg019ij12Tg00E[j33Tg00<Bj24Tg01hdj26Tg009JR0#1#1#1#1#1#1#:R1#7R2f1R3,51f0R4,51'9R5g00RNR6P6P6P2P4%80,01g009o,01n0100000020000%24,01532P4g00Rn#2,01,42g00lN#2,01,42n0110000020000b01634%25,01532eX22W1o"). Qed.
Lemma v_slt_b2z : forall x y : word,
  v_slt x y = Z_to_bv 64 (Z.b2z (Z.lxor (bv_unsigned x) (2^63) <? Z.lxor (bv_unsigned y) (2^63))%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bh11xh21yp;1p;2p;3p;6g003<j11Tg003aj1@Tg004?j1:Tg005Uj26Tg00:ij17Tg00\Nj12Tg00;Gj2;Tg012Tj24Tg01Snj29Tg01>lj20Tg019ij13Tg00E[j35Tg00<Bj28Tg01Z3j3?Tg01inj2>Tg00^Lj6=Tg01kCj2<Tg009JR0#1R1#1#1#1#1#1#@R2#:R3g00RNR4f1R5,62%71%20#2#2#2#2#7';R1'4R6f0R7,62/41'9R8P4P3P7%70,02g009o,02n0100000020000R0f2,62/41/96#3,02553X04P8P4P4%37,029530P7g00Rn#3,02,83g00lN#3,02,83n0110000020000b0A?2571>57E=1<57%38,02553eX23W1o"). Qed.
Lemma v_sltiu_b2z : forall (x : word) imm, v_sltiu x imm = Z_to_bv 64 (Z.b2z (bv_unsigned x <? bv_wrap 64 imm)%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bh13immh21xp;1p;2p;3g003<j11Tg003aj1;Tg004?j16Tg005Uj25Tg01?Rj2:Tg01Snj29Tg00:ij17Tg01>lj20Tg019ij12Tg00E[j33Tg00<Bj24Tg01lLj28Tg009JR0#1#1#1#1#1#1#;R1#6R2g00M<f1R3,51f0R4,:1'9R5g00RNR6P6P6P2P4%70,01g009o,01n0100000020000%24,01532P4g00Rn#2,01,42g00lN#2,01,42n0110000020000b01834%25,01532eW1W2o"). Qed.
Lemma v_slti_b2z : forall (x : word) imm,
  v_slti x imm = Z_to_bv 64 (Z.b2z (Z.lxor (bv_unsigned x) (2^63) <? imm + 2^63)%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h04__x1h14__p1h26__sat1h36__sat2h47__arithh54__ffh66__sat3h76__sat4h88__varmaph95__with:4__x2h;1bi001bh<1ri011rh=2Hah>6__sat0h?1zh@1li021lhA2l0hB1ni031nhC2n0hD2HxhE3immhF2l1hG2n1hH1xp%0p;1p;2p;3p;4p;6p;7p;8g003<j1;Tg003aj1UTg004?j1bTg005Uj24Tg00:ij1FTg00\Nj1?Tg00;Gj2STg01Snj22Tg01Kkj2:Tg01>lj2HTg012Tj2NTg01Ffj21Tg00E[j33Tg004bj2uTg006[j1oTg007Dj20Tg007`j29Tg00U?j2ITg01SKj2=Tg01TKR0j2@Tg00<Bj2DTg00]Sj1>Tg00=fj2QTg00>Nj3PTg00?2j2^Tg00?Sj1]Tg00@3j1\Tg00@Sj2OTg00GFj1[Tg00Gdj4ZTg00A1j1YTg00AOj1XTg00B]j2MTg00B:j2KTg00T5j3RTg01IIj3GTg00Ckj1vTg00DMj2tTg00Doj2sTg00F5j3rTg00FTj4pTg01:Fj2BTg01Ilj3TTg00^Lj6ETg01DWj1nTg018;j2mTg017Xj3iTg01LHj3hTg00C@j4JTg01Q<j4fTg00jlj6eTg01WJj2gTg01Tnj2dTg01X`j1jTg01mWj2kTg019ij1cTg006?j2lTg00JNj7VTg00c:j6aTg00K2j6`Tg00L:j8qTg00KVj7_Tf1R1f0R2#c'Hp=7g009oR3/l2p=6f2R4g00N:R5g00NYR6P6g00O9R7g00M<R8P1g00SNP2CJg00OYR9FVp=8P1P5P6P6P7P2Eap=<P1P5P6P6P7P2E`p=Wf3R:P5P6P6P7P4P1P2Gqp=5P8P1g00QgP2CJp=LP1P5P6P6P7P2P9FVp=CP4P5P6P6P7P1P2F_p=Ag009JR5#;R9#;#;#;#;#;R;#UR<#bR=P8g00RNR>P814<1R?%F9R@%?5#?#?#?#?RA#FRB'SRC'2P?%F;R;,S@RD,:?n0100000020000P>P=1221%F5,H<RE1H<3RFn010000002000014<4RG/NCS00111CRH'2,7<53=X?81u<1%6?%o<,0?'9P811GC/IDP>P=P>P814<:RI/2CRJPI1:IDn0100000020000/24PEPFn0100000020000114CRI,22,7<53=X?81=GC10GC12GC'@PJP>P0f4RJ,4</0CP>P=P>P8P1f6RK,4<RL1:LDRMn0100000020000f5RN'2PEPFn010000002000011LCRO/IDS0111NC'2,7<53=P114<N/0CRPP8POP>P=f7RQ,4<S02/2KRRPEPFn010000002000011KC,22,7<S0353=X?81=LN10LN12LN'@PRP>P0f8RR,4<S04/0QP>P=P1PEPFn0100000020000S05f:RS,4</1CRTf9RU/1CRV'2RW,7<53=P114<URU/0RRX1=TVS0610TV/@WS07f;RW,4</1CRY11SCRS'2S08P>P0f<RZ,4</1CR[11WCR\'0S0917<1R]93=ES0:P1f=,4<R^/1CR_11ZCRZ'0R`g00RnRa,7<Rb,D=S0;WFP2O1%>`Rcg00lN,7<Rd93=ES0<1Q@BRe103@Rf%6B103C[Rg[Rh%6@Rig00P9RjAP@B1UW=RB%6C\j^=iRk1Q@;Rl%6;103D[Rm\fRnAP@;1VjX=iR;%6D\j^=iRiP1g00PU1^3@'DPfeRfO1RjPmPJPfO1RfPgp-0Rog00Q;Rp#]Rq%\pRpP81O84P1%[8S0=CZRr%Y8Rs%X8Rt1M85Ru1K8@R@%UA5R8RA5G8Rv1M89R9=G8ARw58tS0>,<t%v6R6PtA8tu9RxP61WtJRyC5C51tt7R7P2P41D>a1s24=3>adAr831CpRab5b8b9X08X:8W1112CRz/0HR{g00dER|[1014R}PJ[[^08^:8^1oP2P|fDfE,4<PQPWO5R~b4b7b3b2b3b6b7'BWBP2O1n10210010100021010211103b;b<WAP2O1%>XQ06Q07Q08P>P0Q09A3=F]S09P1A3=FbRbPePhPBPkPlPnP;PiPjPmPfPgPqPpPrPsPtQ0>P6Pt1<txP6PyC5C5P7Pab5b8b9X08X:8X1oP|\}PJ[\{^08^:8^1oP~b4b7b3b2b3b6b7'BXA`P2O11D=dRdXCcP2O1n10210010100021110210103b;b<WBP2O1n10210010100021110211103b;b<Q01PePhPBPkPlPnP;PiPjPmPfPgPqPp1O81RcPsPtA8tuARAP6Pt1K83R`/Lu,CtR{1Wt:R:5AtP61L`v,CtAR8@<R@98tv5AtC5C5P7Pab5b8b9X08X1o102CR}%61Rx/94%6I10ID'9[[^08^1oP210^DP^PQPWO4b4b6b2b>b2b3b69TODEEW@P2O1%>PP8%n5R5/mDRP,1OR]/IDRXP>P=Q02/:D/2KRKPEPFn0100000020000Q0353=X?8RFP8P]PF1=MN10MN12MN'@PKP>P0Q04/:D/0QQ0511TPRT/2VRK,7<53=P11:UD/0RRR1=TVRU10TV/@KRK11YP/2SRSP>P011[P/0\R\Q0:P111_P/0ZRZQ0;WAP2O1%>ZR_Q0<PePhPBPkPlPnP;PiPjPmPfPgPqPpPrPsPt1K85=i8@9G8vRv=8twRw,<tP6PtAh8u@=8t9R9P6PyC5C5P7Pab5b8b9X08X:8X1o11zP/0HRHP|[1:1D/04R[PJ[[^08^:8^1oP~b4b7b3b2b3b6b7'BWCP2O1n10210010100021010211103b;b<W@P2O1%>RPUPKPSP>P0P\Q09P1PePhPBPkPlPnP;PiPjPmPfPgPqPpPrPsPtPwP6Pt1<t9P6PyC5C5P7Pab5b8b9X08X:8X1oP|\[PJ[\H^08^:8^1oP~b4b7b3b2b3b6b7,BbX@ZP2O1PdXG_P2O1n10210010100021110210103b;b<WCP2O1n10210010100021110211103b;b<PXPePhPBPkPlPnP;PiPjPmPfPgPqPpPcPsPt1<tAP6PtA8tu@Ru9At:P61L`v,CtA8tv@5AtC5C5P7Pab5b8b9X08X1oP|\}101DR},9411IPRP#610PD'9[[^08^1oP2%6^P^PQPWO4b4b6b2b>b2b3b69T]DEEQ01POP5PDPlPnP;PiPjPmPqPpQ0=PsP8P@g00c^P`CJ,Ct,<tP7Pab5b8b9A38D3P|[P2b4b2b>b2CfEeWBP2O1n10210010100021110211103b;b<Q00PlPnP;PiPjPmPqPpPcPsPtAAt{uRuP6PuC5P7Pab5b8b9X08%62102D'919x}[^08P2PLPJO2b4b2b>b2,gGEEbD1d<1%j1EE1k121N?C/2z,7<53=eXE8WHo"). Qed.

(* [comment removed for export] *)
Lemma zb_b2z_if : forall b, Z.b2z b = (if b then 1 else 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bp;1p;3p;2g019ij13Tg00:ij12Tg00E[j31Tg00<Bj20Tg00RNR0P0g00M<R1f0R2#3P0P1P2g009J#2R0g009oR3n011000002000031P210101013n0110000020000W0o"). Qed.
Lemma zb_b2z_nonzero : forall b, Z.b2z b <> 0%Z <-> b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01Hh13Heqh22H0h32H1h41eh51bi001bi011zp;1p;3p;2p;4p;6g019ij12Tg00]Sj13Tg00E[j30Tg00\5j24Tg00:ij1:Tg00<Bj28Tg00j0j49Tg00jlj66Tg01:Fj27Tg00INj45Tg00M<R0f0R1g009oR230p=1g00RNR3P3%21#1#3g00RnR49031'4P1g009J#:R5#1R6g00dER7[R8A0344R9[P8\91834X08P0P5P2P1C9A0025P0P2P0p-0R8P1g00P9R:P7P7n011010003001000010000X40g01<1R;P5P1E6P71771R5b3b1X26X09C5%24#1#3/49eA0022R9P7[R6g00lNR<=034R=[P6\=1802P9f1R2P1O1,7=b1X06P2P=P3P<P3P8P1P7P:n0110000020000X43P;P4P1E6P7P5b3b1X29X0=C5%2<#1#3/4=en0110000020000W5o"). Qed.
Lemma zb_b2z_zero : forall b, Z.b2z b = 0%Z <-> b = false.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01Hh12H0h23Heqh31eh41bi001bi011zp;1p;3p;2p;4p;6g019ij13Tg00E[j30Tg00\5j22Tg00:ij19Tg00j0j48Tg00jlj67Tg01:Fj24Tg00INj45Tg00<Bj26Tg00M<R0f0R1g009oR230p=1g00RNR3P3%31#1g00lNR49031'2P1g009J#9R5#1R6g00RnR7=034R8[P6\8P0P5P2P1C8A0025P0P2P0p-0R9P1g00P9R:g00dER;P;n011010003001000010000X30g01<1R<P5P1E7P;1481b1b2X06P1P8P3P7P3P9P1P:P;n0110000020000X33P<P4P1E7P;1461b1b2X08C5%37#1/28eA0022R8A0344R7[P8\71634X081602X07C5%34#1/27en0110000020000W4o"). Qed.
Lemma zb_b2z_eqb0 : forall b, (Z.b2z b =? 0)%Z = negb b.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bp;1p;2p;3g019ij14Tg01CYj23Tg01naj10Tg00E[j32Tg00<Bj21Tg00RNR0P0f0R1#4g009o'3%01520P1g00Rn#0,10g00lN#0,10n0110000020000W0o"). Qed.
Lemma zb_b2z_range : forall b, (0 <= Z.b2z b <= 1)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01Hh12H0h23Heqh31eh41bi001bi011cp;1p;2p;3p;6p;4g019ij12Tg006?j20Tg00:ij16Tg007`j21Tg00E[j35Tg00jlj64Tg01:Fj27Tg00INj43Tg00RNR0P0g009oR0f0R1#2R2'0g009J#6R3,02'1P1g00PUR2g01:eR4g01;KR535R6g00dER7[R8g01<MR9=525R:P7[R;P1P6P2P4P2p-0R4P1P7g00P9R<P7n011010003000000X32g01<1R=P5P1E4P71771R>b1b2X06R6P1P:P2P9P2P4P1P<P7P7n011010003000000X32P=P5P1E4P7P>b1b2X0:R:C3g00Rn#2R>,0010>3'1eP;P8P:P6C3g00lN#2R6,001063'1en0110000020000W4o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zb_land_mask : forall x k, (0 <= k)%Z -> Z.land x (2^k - 1) = (x mod 2^k)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__x1h11zh27__arithh34__ffh48__varmaph55__with61kh71xp;2p;1p;3p;6p;4p;7p;8g006?j22Tg01o?j1NTg00ZXj20Tg003<j1;Tg00:ij17Tg00;Gj24Tg01Kkj23Tg00E[j31Tg01o]j16Tg00<Bj25Tg020;j2:Tg020[j18Tg00^Lj69Tg00U?j2MTg00?Sj1LTg00@3j1KTg00@Sj2FTg00A1j1ETg00AOj1CTg00B:j2@Tg00B]j2ATg00C@j4BTg00JNj7?Tg00Ckj1>Tg00L:j8DTg00DMj2=Tg00Doj2GTg00F5j3HTg00FTj4<Tg021?j3ITg00jlj6JTg00M<R0g009oR1f0R2'2R3P0f2R4f1R5#N'0R6f3R7g009JR8#;#7R9/44%78R:'3'0R;=102X10P01495R9%62,07910;X10%69,04,501::5%85E9139:,04=106e1M49g00Q;R9#L%K91F05%E0%C0R9g00N:R6g00NYR:P:g00O9R;P9P6P:P:P;P01@01g00Qg1A08CBg00OYF?R8%>:P8GD1=9;P2P4g00RNR;g00RnR9'51G24=1;9dAH015C<b3b4b5X001215\3^00P2P4P5O2b29I45EJUX60W7o"). Qed.
Lemma zb_land_mask_l : forall x k, (0 <= k)%Z -> Z.land (2^k - 1) x = (x mod 2^k)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01kh11xh21zp;2p;1p;3p;6g006?j2:Tg003<j19Tg00:ij11Tg00;Gj22Tg01Kkj28Tg00ZXj20Tg00U?j27Tg00E[j34Tg021bj35Tg00f5j26Tg00^Lj63Tg00M<R0g009of0R1':P0f2R2g009JR3#9#1R4f1R5'2%13'8R3'0f31242'79401X20A525110321632E3UX00W1o"). Qed.

Lemma zb_shiftl_mul : forall x k, (0 <= k)%Z -> Z.shiftl x k = (x * 2^k)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01kh11xp;2p;3g006?j21Tg0238j30Tg00M<R0g009of0R1'1f2f1;01UX00W1o"). Qed.
Lemma zb_shiftr_div : forall x k, (0 <= k)%Z -> Z.shiftr x k = (x / 2^k)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01kh11xp;2p;3g006?j21Tg023aj30Tg00M<R0g009of0R1'1f2f1;01UX00W1o"). Qed.

(* [comment removed for export] *)
Lemma zb_shl_shr : forall x k, (0 <= x)%Z -> (0 < k < 64)%Z ->
  Z.shiftr ((Z.shiftl x k) mod 2^64) k = (x mod 2^(64 - k))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__x1h14__p1h27__arithh34__ffh48__varmaph55__with61zh72Hah86__sat1h94__x2h:6__sat0h;1Hh<2Hkh=2Hxh>1kh?1xp;1p;2p;3p;4p;8p;5p;6p;7g003<j17Tg00:ij1ETg007Dj2:Tg007`j2;Tg00;Gj20j1jTg018;j28Tg00U?j29Tg014Dj2FTg01Kkj24Tg014dj2@Tg01Ffj2NTg00<Bj2BTg00?Sj1]Tg00@3j1[Tg00@Sj2LTg00A1j1YTg00AOj1WTg00B:j2ITg00B]j2HTg01LHj3GTg01IIj3VTg00C@j4?Tg00DMj2UTg00Doj2TTg00E[j3ATg00F5j3STg00FTj4RTg024Jj8QTg00Ckj1PTg024gj5OTg00jlj6MTg00=fj2JTg00>Nj3KTg00?2j2iTg00GFj1hTg00Gdj4gTg00\Nj1fTg00c:j6eTg025Jj3bTg025kj5\Tg00^Lj6CTg023aj3^Tg020;j2_Tg0238j3`Tg006?j2aTg00JNj7ZTg00K2j6cTg00KVj7dTg00L:j8XTg009oR0f0R1'ap=31:01p=1g00M<R2f1R3;A1p=6P3g00N:R4g00NYR5P5g00O9R6P1g00OYFZp=2P3P4P5P5P6P1Ecp=DP2P3g00SNP1C?p=<f2R7P4P5P5P6P3P1Fdp=>P2P3g00QgP1C?p==f3R8P4P5P5P6P7P3P1GXp=5%33R9%13R:g009JR;#7R<#7#7#7#7#7#ER=,:3';P2%E<R</07R>,88R?10<=R@,91/F8f4RA14=8RB,0<RC'9RD'6X62P219?@R?/@>161DX62P214=7RE/N7RF,0<161@X62P2P2%j<RGPGPFP=P2\2/BGg00Q;RG#]RF%[GRG1L23RH%Y2RI%W2RJP21I2=RK1H2;RL5G2RM=V2Lg00c^RNPKC?'21UJ6ROP1P7g00RNRPg00RnRQ'B1T17=APQdAS203CRRQb3b4b5X0214=1/N1/6=^02P1P8O1b2GQ10<E/8>R>P<PEP7p-0REPFPGPHPIPJ1DJ8RP1<LK,2J5>J%P5RR1I20RS/=M,2JC5POPQb3b4b5X02W11:1=,;314=3#3RM[^02^1EP1%18P8P3O3b2PFPGPHPIPJ1<SL,2JRH=>JPPR1=SL,2JC5POPQb3b4b5X02X1E%11/;3P9[^02^1EP11:8=P8P3O3b2RPDOEM16>@P210<8R>,8CRTf5RU10<ARV'8/91/@V14=ARW,0<,9URX'6X62P218D>1@1V/6XX621J<8%1<RX%3A10<U#1[[%3<RVg00P9RYf6RZ=K<3UW710<ZR[#3\Y^7VP3g00PU1i0<'BPXeO1R\%3U%1[[PFPGP2%h2P31L27CgR[PIPJPJ%f;,H2R;,=S,2JPRPHC5PRPJ1<S;,2J1DJAR]5>JPRPJP4P5P5P6P2PLPNPSC?,2JEeRNC5C5POPQb3b4b5X02X92X1EP:\9%17/;8AA270g00dE[R0[[^02^92^1EP1f7R9/:=P910<9P3PUO5b2b8b:b8RL9bD>18A>/9TPAPCP>1J<B%3W14=URW,0<#1[\X14=ZRZ=K<3VYX7V10<ZRZ#3\Y^7VP\%3W%1Z[PFPGP[PIPJPJAG2K;,=S,2JPRPHC5PRPJ1<;K,2J9>J]PRPNC5C5POPQb3b4b5X02X92X1EP:\M1:7=,;8P0[[^02^92^1EP1%19P914=9,0<P3PUO5b2b8b:b8PLD\ECP@P1EMb;1F?7A^?7PEC1_87A`87PECW<W=X>2X?2o"). Qed.
(* [comment removed for export] *)
Lemma zb_shr_shl : forall x k, (0 <= x)%Z -> (0 <= k)%Z ->
  Z.shiftl (Z.shiftr x k) k = (x - x mod 2^k)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__x1h12Hah26__sat1h34__x2h47__arithh54__ffh68__varmaph75__with86__sat0h94__x3h:4__x4h;4__x5h<1zh=1Hh>2Hkh?2Hxh@6__sat2hA6__sat3hB1khC1xp;2p;1p;3p;4p;6p;7p;8g014Dj2jTg003<j1@Tg00:ij1MTg00;Gj23Tg018;j26Tg00U?j29Tg01Kkj2?Tg00E[j35Tg014dj2=Tg00=fj2BTg00>Nj3ATg00?2j2iTg00<Bj2ETg00?Sj1`Tg00@3j1[Tg00GFj1YTg00@Sj2:Tg00Gdj4;Tg00A1j1VTg00AOj1UTg00B:j2STg00\Nj1CTg00B]j27Tg00Ckj1RTg00C@j48Tg00c:j6LTg00DMj2NTg00Doj2OTg00F5j3KTg00FTj4PTg026Tj3QTg01Ffj2GTg00U_j3JTg0275j3TTg01DWj1hTg01E5j2gTg00VPj1ITg00Voj2HTg01EVj3fTg00WXj3eTg00XAj2_Tg00Xmj3\Tg017Xj3FTg01IIj3ZTg01LHj3]Tg023aj3^Tg00^Lj6DTg020;j2aTg0238j3bTg006?j2XTg007Dj2cTg00JNj7dTg00L:j8WTg009oR0f0R1'Xp=01c01p=4g00M<R2f1R3g00QgP1C8p=>P3g00N:R4g00NYR5P5g00O9R6P1g00OYFdp=2f3R7P4P5P5P6f2R8P3P1GWp=1P2P3g00c^P1C8p=<%03R9P21j78R:g009JR;#@R<#MR=/38R>'6f4R?13=7R@,9?'?RA9521X<2P21=7>RB161@=52AX<21B=8%4=RA%0713=?RC#4[[%0=RDg00P9REf5RF=A=3UW113=FRG#0\E^1DP3g00PU1i0='EPAeO1RH%0?RI%4G[g00Q;RJ#`RK%[JRLP2%Y2RMP31:28C;%V2RN%U2ROPO1S20RP%C;,72RQ'>,2ORR%R5RSP2PPg00SNRT172;RUC8,2OC1PSPOPRPSPOP4P5P5P61<UP,2OELC1C11NO6R6P1P8g00RNR5g00RnR4'E1O18=554dAK203CPR4b5b6b7X02X32%43\9%08A5280g00dE[[[^02^32P1f6R013=0P3P?O4b4b2b8b29Q7>16>B197>'G9527AJ?@8%0@19FC#0[ATFC7%0C1=0G#0[1B=F%00RGf7RC,3=#4[\Af8RA=A=3VEX1D13=ARA#0\E^1DPH%0C%4A[%h;,g2g00YMR;#I#I,H25f21H2;5e2g00Yl'_=\JKPLP2P21:2?P8PMC;P3P21:2FP7PMC;C;PNPOPO%C<,72,>P,2ORMPSP2PPPT172<RTC8,2OC1PSPOAF2TU%@<,72R<5Z2,<Q,2OPSPOPMPSAF2UTA]2Q<'<,2OC1C1C1P6P4b5b6b7X02X32X92X:2X;2%48\I1683/G?9527167?1?F0552\G[[^02^32^92^:2^;2P1f9RGf:RF13=GRG'9PFPG1=FGP3P0PCO8b4b2b8b2b@bAb=P:PKPL1:23PNPO1>PU,2OROPSPOC1P6P4b5b6b7X02%01P9[^02P1P7P3O2b4R39^78ED1a:8Ab:83EDX>9W?XB2XC2o"). Qed.

Lemma zb_lor_eq0 : forall a b, (Z.lor a b = 0)%Z <-> (a = 0 /\ b = 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01ah11bp;2g027fj20Tg00M<R0f1f0'0X10W0o"). Qed.
Lemma zb_lor_eqb0 : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (Z.lor a b =? 0)%Z = ((a =? 0) && (b =? 0))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h05lemmah11Bh22Hah32Hbh41ah51bp;2p;3p;9p;4p;6p;;p;7g006?j2FTg010gj2:Tg01CYj22Tg00g9j27Tg007`R0j23Tg00\5R1j24Tg01V6j3?Tg01^;j2=Tg01O5j2<Tg01PBl9;Tg028Lj26Tg01bLj3ETg01cBj49Tg01d5R2j6DTg01^\j4CTg028ll;BTg027fj2@Tg01Vhj3ATg00E[j38Tg01Z`j7>Tg00RNf0R3g00Rn38p=0p-0R4P1f4R5f3R6f2R7f1R8P3F>p=5g00M<R9g009oR:783p=11F:8R81:67R;/2:R<126:R=127:R>'7R?%0?%0=R?%0>R@'3'4g01\L9?41RA1:56RB/2:#0RC125:RD/7=#0%0DRD/3?REP3D5W01==>%0<%1;'4P4P1g01[[PC%1BRBP3PEPE1<4EM9;W016;:%16R;,4?PAPBPE%15R5/3?REPDP5P3P?P?P4P1g01gT9E41RDP?C9EDD5W0166:%17,4@PAPBPE135;P4P4^14P1P4P4P1P1CCP0P2P5P4P1PDP5C9P?P;P3M;BD5W0167:1@67O2O2O2O23AX38W2X59X49o"). Qed.
Lemma zb_lxor_eq0 : forall a b, (Z.lxor a b = 0)%Z <-> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01ah11bp;2g029gj20Tg00M<R0f1f0'0X10W0o"). Qed.
Lemma zb_lxor_eqb0 : forall a b, (Z.lxor a b =? 0)%Z = (a =? b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h05lemmah11ah21bp;2p;3p;9p;7g012Tj24Tg01CYj22Tg00E[j30Tg00\5R0j25Tg01O5j2;Tg01PBl9:Tg028Lj23Tg01V6j38Tg01Z`j77Tg029gj26Tg01Vhj39Tg00RNf0R1g00Rn30p=1g00M<R2f1R3/41R4g009oR5'2R61231R7%16A0245'5p-0R6P0g01[[f2R8/43R9/25#1A0295R9P11283#1R:P:1;6:M9:W01345%17A0231'5P6P0g01\L9860P9P:A0283P1F7W013311631O2O239X22W1o"). Qed.
Lemma zb_land_lor_distr_l : forall a b m, Z.land (Z.lor a b) m = Z.lor (Z.land a m) (Z.land b m).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01ah11bh21mp;3g02:Nj30Tg00M<R0f2f1f030X20X10W0o"). Qed.

(* [comment removed for export] *)
Lemma zb_lxor_ones : forall x, (0 <= x < 2^64)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h06__sat2h14__x1h26__sat1h37__arithh44__ffh58__varmaph65__with71bh84__p1h96__sat0h:1zh;1Hh<2H0h=2Hxh>2Hah?4__x2h@1ahA1xhB1EhC2H1hD2HihE1ei001ehF1ihG1ni011nhH1ohI1si021sp&0p;1p;2p;3p;4p;6p;8p;5p;7g003<j1BTg00:ij1OTg00;Gj2STg007Dj20Tg007`R0j2:Tg02;8j1zTg02;_j17Tg01Ffj2?Tg02<=j1ETg01o?j1]Tg00ZXj2LTg012Tj2TTg00fXj21Tg02<Zj2=Tg00g9j29Tg01naj1HTg00gWj2yTg006?j2>Tg00[[R1j2sTg00<Bj2NTg01BRj1kTg02=8j1iTg00=fj2gTg00>Nj3fTg00?2j2eTg00?Sj1cTg00@3j1bTg00@Sj2VTg00A1j1_Tg00AOj1^Tg00B]j2UTg00B:j2GTg00Ckj1\Tg00DMk20ETg00Dok20DTg00E[j3ATg00F5k30CTg00FTk40BTg02=Wk30ATg00^Lj6<k805Tg00]3k20<Tg00]Sj1QTg00]lR2k20;Tg00hgk10:Tg00K2k604Tg00_Lj1ITg00_jk303Tg003aj1xTg00T5j3wTg00Hij5vTg00iGj4uTg00jLj1rTg02>>j1pTg02>^j3oTg02?Fj3nTg00kHj3mTg02?ij3lTg00kkj3qTg00U?j2;Tg00GFj1tTg021?j3jTg00jlj6PTg01Kkj26Tg01o]j1hTg00U_j2YTg01DWj1{Tg01E5j2|Tg00VPj1}Tg00Voj2XTg01EVj3~Tg00WXk300Tg00XAk201Tg00Xmj3dTg00Gdk402Tg01IIj3ZTg02@Lj2[Tg01LHj3MTg018;k206Tg017Xk307Tg01Ilk308Tg01Q<k409Tg020;j2aTg020[j1`Tg00C@j4RTg00JNk70=Tg00KVk70>Tg00L:k80?Tg00c:k60@Tg009oR3f0R4'>p=4g00M<R5f1R6;A4p=2g00RNR7?A64p=8P7f4R8f3R9f2R:P6P4E<p=@P5P6g00SNP4CRp=KP6g00N:R;g00NYR<P<g00O9R=P4g00OYK0=p=3P5P6g00QgP4CRp=JP:P;P<P<P=P6P4K0>p=CP9P;P<P<P=P:P6P4L0?p=5AA543p=DP5P6g00c^P4CRp=FP6P;P<P<P=P4J0@p=W%44R>g009JR?#BR@#ORA%B@#B#B#B#BRB#ORC'SRD,04RE':RF%z6%76,?6%O?RG#ERH'2RIP5%7:RJ%]CRK'LRL1T9KRM/24X:51T:KRN1186RO11K6RP'=f5RQ#7RR/LK/1:,84X77%78RS/16RT/9P11Q:11K:RP'=RU/84X77%HO194P,8UX771y6C106C1>C6RU'sP110:CR11>C:f6RP/19RO11K9RV'=%HO/9V'8P4109CP7g00RnRVf8RO/1QRW/=4%HWRX/94'8X77RYf7RZ/18R[#HR\19XV,84X77P\18X4X771N7\19\V%k\D@1=[V%i[D@11K8R]1gACR^103AR_%4CR`103DRa[Rb[Rc%4ARdg00P9ReAfAC6UW>Rf%4DRg\e^>dRdP6g00PU1e3A'NP_eR_O1RePbg00Q;Rh#cRi%bhRj1V56Rk%_5Rl%^5Rm1U5?Rn1G5CRo'K,3mRp%\<RqPm1G53Rr/Jn,3mRsPqACmspC5C520Em=RpP4P:1N7V20D4:=A7VdB0C536H0BRVb4b5b6X15104C%46Rt%4:/:1[[^15P4POP8PZO3b3b0b2b0:0AC8E<W<P4O11>C9P7g00lNR1PYP[19X1,84X77P7P118W4X7720<Z3%DZRW%QW+0;P2%DOR2%Q2f9R2/1P=A71P4%D2RWP5P3f:RX,1:=A71^;I^=FXA51>33/:a%73,?3/2H&0:2W;W=PXP4P2POL05WEP4O1%QWPXPZP^PcPfPdPePbp-0RWPiPjPkPlPmPmP;P<P<P=P9J04R=9CmsR<PqPsC5PpPVb4b5b6X15W81:>6Pt[^15^8WP4f>R;/0DP;f=O3b3b0b2b0%IXPCPZ1036RXP01SA6,0:%I9/0:[R0%I:/061SA:,09Ra[%I8/09\aB03:64P6n2001000000120000000UX75X@5P0\X^75^@5P4f;RXPCP^PcPfPdPePbPiPjPkPlPm1Fnr,3m,WmPqPmP<Pq1Krn,3mC5C5PpPVb4b5b6X15X8W%D4g00dER<[1:t:103:[[^15^8WP4f?R3/0DP3PQP;O4b3b0b2b0P^PcPfPdPePbPiPjPkPlPm1G5A%xB5w5RB,Kn,3mRA9Cm=PqPAC5PpPVb4b5b6X15X8W1:6E106D[^15^8WP4%43P3P;O3b3b0b2b0O4bCP^PcPfPdPePbPiPjPkPlPm1Jon,3mR;PqP;C5PpPVb4b5b6X151>C4R3PU[^15P4PXPZO2b3b0b2b0DvCuWGP4O1n200110200021010011101bI19\1%r\E<1=[1%p[D@P]P^PcPfPdPePbPiPjPkPlPmP;Pq1Jro,3mRo=Cm;C5PpPVb4b5b6X151:`U\3^15P4POP8O2b3b0b2b09oC8E<W<P4O1n200100000021100011000bHPTP^PcPfPdPePbPiPjPkPlPmPsPqPsC5PpPVb4b5b6X15Pt\>^15P4PQP8O2b3b2b9b29n86D@1LSK/16AmSK6D@1T8K/16Al8K6D@XD>XF57qL1;JDRLP^PcPfPdPePbPiPj%t5RePlPoPpPVb4b5b6P`P4b3b2b9b29jJCEP12NLP5%79RL/;DRN16K8,24X:5P5PD1;SD%h4/68'2X:5P^PcPfPd1YRD%4R%7Z/;D#4\g[P:P_O1R_Pb%{?,|5g00YMR?#},X55~51X5?6005g00Yl+01=dhiPjP51V5:P6PeH02PlPm1U5@R@9Z5n1G5GRh,[5'F,3mPq1[5n=M5hR?/F@,3mC5PpPVb4b5b6X15X?51?46/2H%E6/6GR6/2:[^15^?5P4%7OR:POPPO3b3b0b9b2b0%E9/6G/2LP5%E8/6GR81;4D16DGRL/6QRQ'2X:5P5206GDRH,?8R@/;DRZ124QX:5RQP5P@PQP^PcPfPd%7PRP/YDRQ%4P1;:D#4\g[RgP_PbPiPjPkPlB075hB9Z5?R?AM5Bh=M5n'F,3mPpPVb4b5b6X15%E4/6G/?H16L4'2^15P4P2O1b3b0b9b2b0PZP^PcPfPdPQPgP_PbPiPjPkPlPmACmsAPq1Jr?,3m1K?B,3m5CmC5PpPVb4b5b6X151?6HRH#410HD':\F^15P4P2POO2b3b0b9b2b0:08@DE<1;8DP8PGPDP^PcPfPdPQPgP_PbPiPjPePl1FBr,3m,WmPpPVb4b5b6%DDP<[P4b3b0b9b2b0H09EPPSP4EPb<1aGC%`CE<16K9,2NePMP4E<bBb;W=XA5o"). Qed.

Ltac mlia := Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zb_fold_lits :=
  repeat match goal with
  | |- context [Z.shiftr ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
  | |- context [Z.shiftl ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  | |- context [Z.lxor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
  | |- context [Z.modulo ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
  | |- context [Z.pow ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.pow a b) in change (Z.pow a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [bv_wrap ?n ?z] => is_Zlit_zb z; let v := eval vm_compute in (bv_wrap n z) in
        replace (bv_wrap n z) with v by (vm_compute; reflexivity)
  | |- context [Z_to_bv 64 ?z] => is_Zlit_zb z;      (* [comment removed for export] *)
        lazymatch eval vm_compute in (Z.leb 18446744073709551616 z) with true => idtac end;
        let v := eval vm_compute in (z mod 18446744073709551616)%Z in
        replace (Z_to_bv 64 z) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
  end.

(* [comment removed for export] *)
Lemma unsigned_lit_land : forall e, bv_unsigned (Z_to_bv 64 e) = Z.land e 18446744073709551615.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h07__arithh14__ffh28__varmaph35__with41eh51zp;1p;2p;3p;4p;7p;6g003<j12Tg00:ij13Tg00;Gj2>Tg00U?j27Tg00\Nj10Tg00ZXj24Tg00E[j36Tg01o?j18Tg00?Sj19Tg00@3j1:Tg00GFj1OTg00A1j1NTg00AOj1MTg00B:j25Tg00C@j4HTg00JNj7ETg00DMj2@Tg00<Bj2ATg00Doj2BTg00F5j3=Tg00FTj4CTg006?j2DTg021?j3<Tg00j0j4FTg003aj1GTg01>lj2;Tg005Uj2JTg02@oj1KTg00^Lj6LTf0R0#0#0p=I%00#0#0#0p=?%00#0#0#0#0#0#0#0p=1g00M<R1P1g009JR2#2R3#3%23#2#2#2#2R3#3R4'>,70R5f1R6%02#I#?#1#1#1#1#1#1#1#3'49610X51P1%84,40P5g00Q;R5#9%:5%O1%N1%M1R5g00N:g00NYR2P2g00O9R2P1g009oR7,51g00Qg1514CHg00OYFE1@52P0f2R2g00RNR5g00RnR8'A1B02=658dA=176CCb1b2b31D74P0b09<04CF%G3R31;30'J%K0ELW4o"). Qed.
Lemma Z_to_bv_land64 : forall e, Z_to_bv 64 (Z.land e 18446744073709551615) = Z_to_bv 64 e.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01eh11zp;1p;2p;3p;6g003<j12Tg003aj1>Tg01>lj23Tg005Uj24Tg004?j1=Tg00E[j3:Tg02BIj17Tg00\Nj10Tg00:ij18Tg00ZXj29Tg02Cej1<Tg00jlj6;Tf0R0#0#0p=5%00#0#0#0p=6%00#0#0#0#0#0#0#0p=1g00M<R1P1g009JR2#2#2#2#2#2#2#>R31330R4'4%=3f1,337:4X11%74%02#5#6#1#1#1#1#1#1#1#8,90%<0E;W0o"). Qed.
Lemma zb_shl_shr_land : forall x k, (0 <= x)%Z -> (0 < k < 64)%Z ->
  Z.shiftr (Z.land (Z.shiftl x k) 18446744073709551615) k = Z.land x (2^(64 - k) - 1).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with54__p1h61zh72Hkh82Hxh91kh:1xp;2p;1p;3p;6p;4p;7p;8g006?j24Tg007Dj21Tg003<j10Tg00:ij18Tg007`j2<Tg020;j2RTg00;Gj26Tg00U?j2>Tg014Dj2=Tg01Kkj23Tg00ZXj29Tg00E[j3:Tg00<Bj2BTg00?Sj1YTg00@3j1VTg00@Sj2UTg00A1j1QTg00AOj1OTg00K2j6NTg00B]j2LTg00B:j2@Tg00C@j45Tg00Ckj1ITg01LHj3HTg00DMj2GTg00Doj2JTg00F5j3KTg00FTj4FTg021bj3ETg00jlj6MTg02E@j4DTg00^Lj6ATg01o?j1PTg00GFj1CTg021?j3STg00JNj7TTg00KVj7XTg00L:j8WTf1R0g00N:R1g00NYR2P2g00O9R3f0R4g00OYFTp=2f2R5P1P2P2P3P0P4FXp=?g00M<R6P0g00QgP4C5p=7f3R7P1P2P2P3P5P0P4GWp=;g009oR8/40R91180g009JR:#0R;#0#0#0#0#0#8R<,10'<R=P61R75R>%8;R;/6<'>R?1=47f4R@13<7,6;%8:RA'3'9RB5:6X66P613<5RC,6;R;,>7RDA:64BX66RBP613;A,97R;PB1B6;PDp-0RDg00Q;R;#YRB%V;R;1U60RA%Q6RE%O6RFPFP1P2P2P3P7ENP61L6:R:g00SNR11@6<RGC5,2FRH5?F%I2R21@68RIAH6G:'7,2FC;1GF3R3P4P5g00RNRJg00RnRK'B1J45=:JKdAK680CFRKb2b3b4X06W5114<RJ,<013<0,48[^06^5DP41187P7P0O3b19E7CEM1=?5P7P5PBP;PAPEPF17I:,2FR?P2P?C;P3PKb2b3b4X061484P9[^06P4P@P5O2b1PBP;PAPEPFP6PIP1P:C5,2F=?FHRHP2PHC;P3PKb2b3b4X061184/<JP=[^06P4P7P0O2b1CDEA%P<,9>PBP;%C6PE17IG,2FP3PKb2b3b4148<P4b19S><EAW7W8X96X:6o"). Qed.

Ltac zs_wrap e := rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H := rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms :=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
      rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])   (* [comment removed for export] *)
  end.
Ltac zs_idioms_in H :=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
      rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.
(* [comment removed for export] *)
Ltac zs_wrap_land e := rewrite (unsigned_lit_land e).
Ltac zs_wrap_land_in e H := rewrite (unsigned_lit_land e) in H.
Ltac zs_idioms_land :=
  match goal with
  | |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_land_in H :=
  match type of H with
  | context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zsimp_slt :=
  (lazymatch goal with |- context [v_sltu] => rewrite ?v_sltu_b2z | _ => idtac end);
  (lazymatch goal with |- context [v_slt] => rewrite ?v_slt_b2z | _ => idtac end);
  (lazymatch goal with |- context [v_sltiu] => rewrite ?v_sltiu_b2z | _ => idtac end);
  (lazymatch goal with |- context [v_slti] => rewrite ?v_slti_b2z | _ => idtac end).
Ltac zsimp :=
  zsimp_slt;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.

Ltac zb_fold_lits_in H :=
  repeat match type of H with
  | context [Z.shiftr ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v in H
  | context [Z.shiftl ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v in H
  | context [Z.land ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v in H
  | context [Z.lor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v in H
  | context [Z.lxor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H
  | context [Z.pow ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.pow a b) in change (Z.pow a b) with v in H
  | context [Z.sub ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v in H
  | context [bv_wrap ?n ?z] => is_Zlit_zb z; let v := eval vm_compute in (bv_wrap n z) in
        replace (bv_wrap n z) with v in H by (vm_compute; reflexivity)
  end.

Ltac zsimp_in H :=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.

(* [comment removed for export] *)
Ltac decide_tests :=
  repeat match goal with
  | |- context [Z.eqb ?x ?y] =>
      first [ rewrite (proj2 (Z.eqb_eq x y)) by mlia | rewrite (proj2 (Z.eqb_neq x y)) by mlia ]
  | |- context [Z.ltb ?x ?y] =>
      first [ rewrite (proj2 (Z.ltb_lt x y)) by mlia | rewrite (proj2 (Z.ltb_ge x y)) by mlia ]
  | |- context [Z.leb ?x ?y] =>
      first [ rewrite (proj2 (Z.leb_le x y)) by mlia | rewrite (proj2 (Z.leb_gt x y)) by mlia ]
  end; cbn [andb orb negb].

(* [comment removed for export] *)
Lemma b2z_word_nez : forall b, negb (bv_eqb (Z_to_bv 64 (Z.b2z b)) (Z_to_bv 64 0)) = b.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bp;1p;2p;3g003<j10Tg003aj17Tg019ij13Tg01>lj21Tg02FTj36Tg01naj15Tg00E[j34Tg00<Bj22Tg00RNR0P0g009J#0#0#0#0#0#0#7R1f0R2#3,11g009o,1136#5=402P2g00Rn,20g00lN,20n0110000020000W0o"). Qed.
Lemma b2z_word_eqz : forall b, bv_eqb (Z_to_bv 64 (Z.b2z b)) (Z_to_bv 64 0) = negb b.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bp;1p;2p;3g003<j10Tg003aj17Tg019ij14Tg01>lj22Tg02FTj36Tg01naj11Tg00E[j35Tg00<Bj23Tg00RNR0P0g009J#0#0#0#0#0#0#7R1f0R2#4,21g009o,2136%12550P2g00Rn#1,30g00lN#1,30n0110000020000W0o"). Qed.

(* [comment removed for export] *)
Ltac zr_pose e := let H := fresh "R" in assert (H : inr64 e) by zrange; unfold inr64 in H.

(* [comment removed for export] *)
Ltac zb_masks :=
  repeat match goal with
  | |- context [Z.land ?x ?m] =>
      is_Zlit_zb m;
      let k := eval vm_compute in (Z.log2 (m + 1)) in
      let m' := eval vm_compute in (2 ^ k - 1)%Z in
      constr_eq m m';
      let p := eval vm_compute in (2 ^ k)%Z in
      replace (Z.land x m) with (x mod p)%Z by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
  | H : context [Z.land ?x ?m] |- _ =>
      is_Zlit_zb m;
      let k := eval vm_compute in (Z.log2 (m + 1)) in
      let m' := eval vm_compute in (2 ^ k - 1)%Z in
      constr_eq m m';
      let p := eval vm_compute in (2 ^ k)%Z in
      replace (Z.land x m) with (x mod p)%Z in H by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
  end.

(* [comment removed for export] *)
Ltac pose_word_ranges :=
  repeat match goal with
  | |- context [bv_unsigned ?x] =>
      lazymatch goal with
      | _ : (0 <= bv_unsigned x < _)%Z |- _ => fail
      | _ => pose proof (zr_word x : (0 <= bv_unsigned x < 2^64)%Z)
      end
  | _ : context [bv_unsigned ?x] |- _ =>
      lazymatch goal with
      | _ : (0 <= bv_unsigned x < _)%Z |- _ => fail
      | _ => pose proof (zr_word x : (0 <= bv_unsigned x < 2^64)%Z)
      end
  end.

(* [comment removed for export] *)
Ltac zb_bits_norm :=
  intros;
  rewrite ?Z.land_lor_distr_l in *;
  rewrite ?Z.lor_eq_0_iff in *;
  rewrite ?zb_lxor_eq0 in *;
  zb_masks;
  rewrite ?Z.shiftr_div_pow2 in * by lia;
  zb_fold_lits.

Ltac blia := zb_bits_norm; pose_word_ranges; mlia.

(* [comment removed for export] *)
Ltac decide_tests_b :=
  repeat match goal with
  | |- context [Z.eqb ?x ?y] =>
      first [ rewrite (proj2 (Z.eqb_eq x y)) by blia | rewrite (proj2 (Z.eqb_neq x y)) by blia ]
  | |- context [Z.ltb ?x ?y] =>
      first [ rewrite (proj2 (Z.ltb_lt x y)) by blia | rewrite (proj2 (Z.ltb_ge x y)) by blia ]
  | |- context [Z.leb ?x ?y] =>
      first [ rewrite (proj2 (Z.leb_le x y)) by blia | rewrite (proj2 (Z.leb_gt x y)) by blia ]
  end; cbn [andb orb negb].

Lemma zb_negb_eqb0 : forall x, (0 <= x)%Z -> negb (x =? 0)%Z = (0 <? x)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h04__p1h14__x1h21bi001bh31ri011rh47__arithh54__ffh68__varmaph75__with81li021lh91ni031nh:2Hxh;1ei041eh<2n0h=1xp;2p;1p;3p;4p;6p;7p;8g006?j2=Tg02GAj2QTg01CYj2<Tg01TKR0j2?Tg01naj15Tg01Snj2:Tg00E[j30Tg01SKj2DTg007Dj22Tg00?Sj1CTg00@3j1ATg00@Sj2@Tg00A1j1PTg00AOj1OTg00B:j2NTg00B]j2KTg00C@j46Tg00Ckj1JTg00K2j6ITg00DMj2FTg00<Bj29Tg00Doj2ETg00F5j3GTg00FTj4HTg01:Fj28Tg00]Sj1;Tg00JNj7BTg00L:j8LTg00c:j6MTg00M<R1f0R2g009oR330p=7f1R4g00N:R5g00NYR6P6g00O9R7P2g00OYFBp=4f3R8P5P6P6P7f2R9P4P2GLp=1g00RNR:g00RnR;702p=3P4P5P6P6P7P2EMp=>1=321Q43%74R<1<43'?1<93P:P0%78%54f5R=,:3R>50:P4f4R?#7R@1D3=RA123=/?>R>f6,:3RBP:P0f7,23RC%5;RD=0:4P4f8,23REg00lNRF=0:;p-0RGg00Q;RH#CRI%AHRH1@14RJ%P1RK%O1RLP11N13RMg00SNg009J,K1RNC6,4LRO%J6RPPLP1PNg00c^PMC6,4LRQPPPLP5P6P6P7P8EIR6C1C11FL7R7P2P919:;R51E29#3dAG134CHRRb5b6b7X11W01232RSP8\<[^11^0GP2g00dER8f:RTP4P=O4b4'8%3DeW8P2O1%;ERU19:FA0:DFeW9P2O1n10210010100021010210103b2b3W;P2O1%;@PAP>PBP:P0PC%5FRC=0:4P4P5%3CeX8EP2O1A0:;FPIPHPJPKPL1>LOPPPL1>LQPPPLP1PMg00QgPNC6,4LPPP6C1C1C1P7PRb5b6b7X11X0GP8\SP8\<1=39P?[[[^11^0GP2P8PTP4P=f9O5b4'8A0:CFeX<UP2O1n10210010100021010210103b2b3W9P2O1n10210010100021010410103b2b3W:X=1o"). Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_eqm : forall e1 e2, (e1 mod 2^64 = e2 mod 2^64)%Z -> Z_to_bv 64 e1 = Z_to_bv 64 e2.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01bh11Hh22e1h32e2h41zp;1p;2p;3p;6g003<j11Tg00:ij16Tg00;Gj29Tg00U?j22Tg00E[j33Tg003aj1;Tg004?j1:Tg01>lj20Tg00<Bj28Tg00^Lj67Tg02Gcj14Tg00jlj65Tg00M<R0f1R1g009J#1R2#6%12#1#1#1#1R2#6'9R3'2R4f0R5/23530%;2R2#:R6f2R7/23R8,02R91027R:9365X06P61024R;f3/23,02=365X06P0P41025=369X40186;P8P5E71021%41E5P:%47E5W1X30W2o"). Qed.

Ltac word_eq_tac :=
  first [ exact eq_refl
        | f_equal; lia
        | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
        | apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ].
