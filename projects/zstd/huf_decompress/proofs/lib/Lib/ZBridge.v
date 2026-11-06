(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ZBridge () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00c59OSSVerify5KrLib3Lib7ZBridge5inr64C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C56Stdlib6NArith6BinNat1N2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z4of_NK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;lt_le_transK47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat3N2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z;land_nonnegI47Corelib4Init5Logic2or00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z8land_0_lC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z9log2_landC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula09K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00c59OSSVerify5KrLib3Lib7ZBridge9zr_land_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z?bits_above_log2C47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool<andb_false_rC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib3Lib7ZBridge9zr_land_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib7ZBridge=land_mask_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec;Z_lor_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib3Lib8PropExec<Z_lxor_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC59OSSVerify5KrLib3Lib8PropExec>Z_shiftr_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z;le_lt_transC56Stdlib6ZArith6BinInt1Z3b2zC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes:comparison01C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z=testbit_falseC56Stdlib6ZArith6BinInt1Z9div_smallC46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z>pow2_bits_trueC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC56Stdlib6ZArith6BinInt1Z3addc59OSSVerify5KrLib3Lib7ZBridgeBzb_land_pow2_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z9mod_smallc59OSSVerify5KrLib3Lib7ZBridgeBzb_lxor_pow2_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC56Stdlib6ZArith6BinInt1Z7lxor_wdC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z8lxor_0_rC56Stdlib6ZArith6BinInt1Z>lxor_nilpotentC56Stdlib6ZArith6BinInt1Z:lxor_assocC56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes7reflect00C45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib7Classes?RelationClasses?Equivalence_PERC46Stdlib4Bool4Bool>eq_true_iff_eqc59OSSVerify5KrLib3Lib7ZBridge<zb_lxor_signC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib7ZBridge9zb_signedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms<PER_morphismC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes9MorphismsBsubrelation_properK46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveK46Stdlib9micromega5Tauto4kind02C59OSSVerify5KrLib3Lib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib7ZBridge;bv_lts_lxorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_sltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_sltiC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z:shiftl_1_lC56Stdlib6ZArith6BinInt1Z9land_onesc59OSSVerify5KrLib3Lib7ZBridge<zb_land_maskC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z?mul_mod_distr_rC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z<lor_eq_0_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z=lxor_eq_0_iffC56Stdlib6ZArith6BinInt1Z@land_lor_distr_lC56Stdlib6ZArith6BinInt1Z=add_lnot_diagC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z3oppC47Corelib4Init9Datatypes4xorbC46Stdlib4Bool4Bool;xorb_true_rC56Stdlib6ZArith6BinInt1Z=ones_spec_lowC46Stdlib4Bool4Bool<xorb_false_rC56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z9lnot_specC56Stdlib6ZArith6BinInt1Z9lxor_specK46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib3Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib7ZBridge:zb_shl_shrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z8eqb_specc59OSSVerify5KrLib3Lib7ZBridge=Z_to_bv_mod64C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inr64 (e : Z) : Prop := (0 <= e < 2^64)%Z.

Lemma zr_word : forall x : word, inr64 (bv_unsigned x).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01Hh11xp;1p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9g003<j10Tg003aj19Tg004?j13Tg004bj22Tg005Uj21Tg006?j28Tg006[j17Tg007Dj24Tg007`j25Tg008;j16Tg0091#0#0#0#0#0#0#9R0#3f0R1,20g009V1101R2'8%70,42'5P1f1,10#6eb0W1o"). Qed.
Lemma zr_bv : forall n (x : bv n), (n <= 64)%N -> inr64 (bv_unsigned x).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__x1h13Hn0h27__arithh34__ffh44__p1h58__varmaph65__with74cstrh84__x2h91Hh:2Hnh;1nh<1xp;1p;2p;4p;3p;5p;<p;7p;6p;8g004?j1^Tg003<j11Tg003aj1JTg00:4R0j2BTg004bj2]Tg005Uj2:Tg006[j1ITg007Dj20Tg007`j29Tg00:Pj1ATg00:nj28Tg00;KR1j1;Tg006?R2j23Tg00;ij2<Tg00<Cj4RTg00<jj1QTg00=Mj1NTg00=mj1LTg00>Mj2?Tg00>kj1KTg00?Ij1HTg00@4j27Tg00@Wj2>Tg00A:j44Tg00Aej1GTg00BGj2FTg00Bij2ETg00CUj3MTg00Coj3DTg00DNj4OTg00E@j1PTg00E^j4CTg00F<j5STg00Fcj5TTg00GHj4\Tg008;j1[Tg00Gcl<ZTg00HHj7VTg00Hlj6WTg00IPj7XTg00J4j8YTg009VR3f0R4'3p=2g00JXR5g00K6R6P0P1P2g00KTf5R2f4R1f3R0f2R7f1R8P4M<Zp=UP8g00L4R9g00LSR:P:g00M3R;P4g00MSFVp=5P8P9P:P:P;P4EWp==P7P9P:P:P;P8P4FXp=@P0P9P:P:P;P7P8P4GYp=6%^4g0091R9#1R<#1#1#1#1#1R=#JR>,B81]781:78R?#2%I7,0?'91:07R?#2%A<R@%A=R='8RA,0?1B0>%;0RB/3=RCP0PB1<6BP>P=1<6=EUP8CRR>PC%Q1RD%;1#2REp-0RFg00N3RG#NRH%LGRG1?68RI%K6RJ%H6RKP61763RLg00N_RM1>69R9C4,5KRN1=K05@K%G:R:PNC61FK;R;P4P7g00OFRNg00OfRO'<1E47=MNOdAD638COROb3b5b6X06W4%24/98%28[^06^4FP4f6RN/:2R2%;NRN,8@RP'0P2P0O3b2b7b1P?18@BPAP>PCPDPEPHPGP61?67P8%P6RACCPJPK1=K1P6P9g00PFR11>6<C4,5KR<5@KP:P<C6P;POb3b5b6X06X86X4F1048,971087[^06^86^4FP4%22PPP2P0O4b2b7b1P@PBP=P>PCPDPEPHPGPAPJP6PLP1176@C4,5KP;POb3b5b6103@P4b2b7b1P>PCPDPEPHPGPIPJPKP6P9PM176=C4,5KRKP:PKC6P;POb3b5b6X06134=138=[^06P4PNP7O2b2b7b1DSDTC\%[?eb9W:W<X;5o"). Qed.
Lemma zr_lit : forall z, (0 <= z < 2^64)%Z -> inr64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01zp;2p;1g006?j25Tg003<j10Tg00:Pj11Tg00:nj22Tg007Dj24Tg007`j23Tg00K6g009Vf0R0'5g0091#0R1#1%01#0#0#0#0#1'2,40'3P0UW0o"). Qed.
Lemma zr_mod64 : forall e, inr64 (e mod 2^64).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h07__arithh14__ffh28__varmaph35__with41ep;1p;2p;3p;4p;7g003<j10Tg00:Pj12Tg00:nj24Tg00=Mj13Tg00=mj1FTg00E@j1;Tg00>kj1:Tg00?Ij15Tg00@4j21Tg003aj16Tg00Pmj37Tg00A:j48Tg00HHj79Tg00BGj2ETg00;ij2DTg00Bij2CTg00CUj3<Tg00Coj3=Tg00DNj4>Tg007Dj2?Tg00QPj3@Tg00R7j2ATg008;j1BTg00K6R0f0R1g0091#0R2#2R3%02#0#0#0#0R2#2'4R4g00N3R5#3%F5%;0%:0%50R5g00L4g00LSR6P6g00M3R6P0g009VR7,10g00PF1103%62570C8g00MSF91E56P1f2R6g00OFR5g00OfR2'D1C16=<52df19=07C>b1b2b31?74P1b03@1A14#BeW4o"). Qed.
Lemma zr_mod : forall e k, (0 <= k <= 64)%Z -> inr64 (e mod 2^k).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__p1h14__x1h27__arithh34__ffh48__varmaph55__with64__x2h71Hh82Hkh91eh:1kp;1p;2p;4p;3p;5p;7p;6p;8g003<j12Tg00:Pj1>Tg006?j24Tg007`j23Tg00:nj25Tg00=Mj1LTg00=mj1FTg00E@j1ETg00>kj1DTg00?Ij1CTg00@4j2;Tg00A:j46Tg00BGj2VTg00;ij2UTg00Bij2TTg00CUj3STg00Coj3QTg00DNj4KTg007Dj21Tg00>Mj2?Tg00@Wj2<Tg00Aej1GTg00RWj4HTg00QPj3ITg00R7j2:Tg00E^j4JTg00F<j5BTg00Fcj5MTg00GHj4NTg008;j1ATg00HHj7OTg00Hlj6PTg00IPj7@Tg00J4j8RTg009VR0f0R1'4p=0f1R2g00L4R3g00LSR4P4g00M3R5P1g00MSFOp=7P2P3P4P4P5P1EPp==f2R6P3P4P4P5P2P1F@p=8f3R7P3P4P4P5P6P2P1GRp=9g00K6R3%01R8g0091R9#2R:#2#2#2#2#2#>R;,41R<'3%>:R=/52R>P=P2g00N3R?#LR@%F?R?%E3RA%D3RB%C3RCP31;30RDg00PFRE1;3=C6'71VC5R5P1P6g00OFRFg00OfRG'U1T16=SFGdAQ302CKRGb3b4b5110=P1b2R0p-0RFP@P?1?32RHPBPCP3PDg00N_RD1<39R9C6,7CRI1=C7RJ58C%G4R4PIC9P5PGb3b4b5X13W0RI1382%02[^13^0FR8P1146;P6P2O3b2CH5I61:6>RK#011K>'315=6R>,:7RL#015=;RM,1LPIP8P1f4R815=7RI':RN/1IPNP2O3b2PLP>PMP@P?P31?36P2PACJPBPC1=C8P3P9PE1<3:C6,7CR:58CP4P:C9P5PGb3b4b5X13X63X0F1112,361126[^13^63^0FP1%0NPIPNP2O4b2P=P6P;P0P@P?PHPBPCP3P9PD1;3;C6,7CRD98CJP4PDC9P5PGb3b4b5X13X0F132<142;[^13^0FP1%07P7P6O3b2DBDMCNb7%AKeW8X:3W9o"). Qed.
Lemma zr_mod_any : forall e p, (0 < p <= 2^64)%Z -> inr64 (e mod p).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__p1h14__x1h27__arithh34__ffh48__varmaph55__with64__x2h71Hh82Hph91eh:1pp;2p;1p;3p;4p;7p;6p;8g007Dj21Tg003<j10Tg00:Pj1>Tg00:nj2ETg006?j24Tg007`j22Tg00=Mj1VTg00=mj1KTg00>Mj2<Tg00>kj1FTg00?Ij1DTg00@4j2:Tg00@Wj2?Tg00Aej1WTg00BGj2UTg00;ij2TTg00Bij2QTg00CUj3JTg00Coj3ITg00DNj4HTg00QPj3GTg00R7j2=Tg00S?j1;Tg00S^j26Tg00TGj3@Tg00U0j2LTg00U\j3MTg00E@j1NTg00E^j4OTg00A:j47Tg003aj1CTg00Pmj3PTg008;j1BTg00HHj7RTg00Hlj6STg00IPj7YTg00J4j8XTg00K6R0f1R1g00PFf0R2C7p=9P1g00L4R3g00LSR4P4g00M3R5P2g00MSFRp=3P1P3P4P4P5P2ESp=Af2R6P3P4P4P5P1P2FYp=5f3R7P3P4P4P5P6P1P2GXp=8g009VR3/12R8g0091R9#0R:#>R;%0:#0#0#0#0R<#>'ER=,42'2p-0R>g00N3R?#VR@%K?RA1<01%F0RB%D0RC1:03RD1?09R9'9,3CRE1AC755C%W4R4PEC81UC5R5P2P6g00OFREg00OfRF'T1Q26=JEFdAI031CHRFb3b4b5X10W012811131[^10^0>P2146=R8P6P1O3b29G611=61RE,4311E1'2g00V<RG#;RH#;,60160H160G5@05@0g00V['L=M?@PAP01<06P1%N0COPBPCP0PDg00N_RDP9C7,3CRB1?0:R:,99,3C55CP4PCf4RA,ACP0P:PD1:0;%C<5P0R<C7,3C55CP4199<,3C95CBC8C8P5PFb3b4b5X10X60X0>14321121'212781436116='2[[^10^60^0>P21137P71=A7P1P6O5b2b7%BEeW8X:0X90o"). Qed.
Lemma zr_land_l : forall a b, inr64 a -> (0 <= b)%Z -> inr64 (Z.land a b).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with71ah82Hah96__sat1h:1bh;2H0h<1Hh=3Ha'h>2Hnh?3Hnzh@4__p1hA6__sat0hB6__sat2hC4__x4hD1ei001ehE1si011shF2z0hG2H1hH3HazhI2HbhJ1zhK2z1i021np;1p;2p;3p;4p;6p;:p;7p;8g008;j1NTg003<j18Tg00:Pj1QTg00:nj2HTg007Dj20Tg00WGj21Tg00Wej2fTg00XJj27Tg00Xdj2:Tg00RWj2`Tg00Y=j3]Tg00Yaj2\Tg00;ij2YTg00=Mj1tTg00=mj1qTg00>Mj2GTg00E^j4CTg00>kj1kTg00?Ij1jTg00@4j2KTg00@Wj2;Tg00ZBj1STg00Aej1cTg00BGj2bTg00Bij2aTg00CUj39Tg00Coj3_Tg00DNj4^Tg00Zgj2PTg00[Gj16Tg00[`R0j2OTg00E@j1[Tg003aj1ZTg00Pmj3uTg00\@j6Xl:rTg006?j2<Tg00\^j1sTg00]@j14Tg00]^j3pTg00^Dj4mTg00^gj2LTg00_Dj2lTg007`R1j2DTg00S?j1ETg00S^j2?Tg00TGj3FTg00U0j2UTg00U\j3TTg00Hlj6iTg00GHj4hTg00A:j4ITg00HHj7gTg00_fj7nTg00`Jj7oTg00J4j8MTg00`nj6eTg00IPj7dTg009VR2f0R3'<p=2g00K6R4f1R5g00N_P3CIp==P5g00L4R6g00LSR7P7g00M3R8P3g00MSFgp=3f2R9P6P7P7P8P5P3Fnp=JP9P6P7P7P8P5P3Fop=Rf6R:P6P7P7P8f5R;f4R<f3R=P6P7P7P8P9P5P3GMGMp=AA9432p=5P4P5g00PFP3CIp=@P4P5g00aRP3CIp=BP5P6P7P7P8P3Eep=WP=P6P7P7P8P9P5P3GMp=>P9P6P7P7P8P5P3Fdp=V%N5P1%29R>g0091R?#8R@#QRA%8@RB#8#8#8#8RC#QRD'HRE,0911<=#N\>P3%2<RF10;E%2;f7RG/f:11G:RH#2%2G%2:'7':f8RI/1GRG#210GE1`ADRJ102ARK%2D102ERL[RM[RN%2AROg00b9RPA]AD5UW8RQ%2E\P^8OROP5g00bU1\2A'YPKeO1RKPMg00N3RP#tRR%qPRSP41G49RTP51G4=RUCCRV%k4RW%j4RX1K42RY1;4?RZ'=,3XR[1;4@,=Y,3XR\%S?R?,;4R],=Y,3XR^5JX5RXR_%c7R`PXP^P`P[FA1bX8RaP3P9g00OFRbg00OfRc'Y1a39=9bcdA_425C^Rcb4b5b6X04X14X24%23Rb%25Rd/7>':%2=ReP>[[^04^14^24P3f;Rff<Rg11gfP<P;O5b3b9bAb91PG2%5GRG%6G'OP0f9RG/1I#5Rh%6hf:Rh/1GRi/0EP3%5iRiP4P2103ERjXJ4RkPRPS%[4RlPW1K4A%ZC5u4RC,@Y,3XPaPcb4b5b6PLP3b3Rm11fhP3EXWDP3O1%6i1Pf2%5fRi%6i'OP0%5gR0%60f=R0/1g/0EP3%50R0P4P2105ERif@Rh,19#2%2h,7>':fARn,1=#5#6fBRo,1</0E]?]>]=^8bX741<22REf?Rp,12#2%2p,7E':112h#5#6P4P2PkPm112n%snEXW?W>X=LW8f>RLP3PGPIP:P=M:rWDP3O1%601025R0P11HA5,09%4=/09Rm[Rk%49/051HA9,0=RE[Rq1HA=,0<\mAp953RmP3n2001000000120000000UX:4X74Pq\0^:4^74P311pLRAPDPJPNPQPOPKPMPRPSPVPWPX1BZY,3X,WXRrP`PXP_P`PXP^P`1@YZ,3XR_C>FAPaPcb4b5b6X04X14X24%53g00c;Rs[Rt17>eRe,:d102=\F[[^04^14^24P3PofCR>11>oPIPfPgO6b3b9bAb9PpPLPRPS1G45RuPWPXP[P`P[C>PaPcb4b5b6X04Pd\b^04P3PhPfO2b3PICm%4A%4p%4L'L'<P1PkPq%4</0=\EPmP5n2001000000120000000V0X:4X74Pk\0^:4^74P3PnPD%4nRn%4hR0'lRk10n01Ln0Rm=94n'D1<0nA94m0'D'7Rm%4o/LnRnP4PJPNPQPOPKPMPRPSPVPWPXPrP`PX1B]Y,3X,WXP`PXAJX[\9RX^P`PXP\P`PXP[P`P_C>FAFAPaPcb4b5b6X04X14X24%5=Ps[1:Fe102;\F\F[[\t^04^14^24P3fGRtfFRF'1PFPtPGPgPpPhPoO8b3bBb9bBbFb;PkPmPnP4PRPSPuPWPX1@ZC,3XRCP`PCC>PaPcb4b5b6X04Pi\j^04P3fDRjPLO2b3bFb;O4b;100DPkPmPnP4p-0Rng00V<Rm#ERk#ER0#ERL#E,?41?4L1?401?4k1?4m5F45F45F4Rm5F4g00V[Rk'U1Umk=TPR5TPPSP4P4PTP<1G4<CCP5P4PUP<PlCCCCPWPXPXP6P7P7P8P:Ei1;4BRB%S@,;4R@'B,3X5VX%8?,;4R?/=@,3X1BB?,3X5VX5JXP`PX1K4DR?,@@,3XP`PX1=ZB,3XP`1@Z?,3XC>FAPaPcb4b5b6X04X14X24XC4W@A9459,D<1<=9A945='D'710=DRD1<9=PD[[[^04^14^24^C4^@nP3%4jRn%4>RD'0PDPnP511j>#4P9P=P<O8b3bKbGb;b<O4b<WHP3O1n200110100021110011102bEW?P3O1n200110100021010011102bEChb>%NHeWIW=W8P5P3O2n2001000000121000000W<X:4X74o"). Qed.
Lemma zr_land_r : forall a b, (0 <= a)%Z -> inr64 b -> inr64 (Z.land a b).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01ah11bh21zp;2p;1p;4p;6g006?j25Tg008;j11Tg00WGj20Tg00cXj42Tg00dRj24Tg00\@j63Tg00K6R0g009Vf1R1'5%11P0f2R2f3R3'0f0R4#1X20P2P3P4P1C210321432E3UUX10W0o"). Qed.
(* [comment removed for export] *)
Lemma land_mask_mod : forall e m, (0 <= m < 2^64)%Z -> Z.land e m = Z.land (e mod 2^64) m.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h04__x1h11bh24__p1h37__arithh44__ffh58__varmaph65__with72Hmh81Hh92H0h:2Hah;6__sat1h<1ah=1mh>2Hih?6__sat0h@1ei001ehA2e0hB1ihC1ni011nhD1ohE1si021sp;1p;2p;3p;4p;6p;7p;5p;8g003<j15Tg00:Pj1FTg00:nj2BTg007Dj21Tg007`R0j2<Tg00WGj2=Tg00R7j24Tg00e5j20Tg00eVj22Tg00f4j2KTg006?j28Tg00XJR1j2kTg00;ij2@Tg00=Mj1cTg00=mj1[Tg00>Mj2YTg00>kj1XTg00?Ij1WTg00@Wj2UTg00@4j2ETg00Aej1STg00BGj2RTg00Bij2QTg00CUj33Tg00Coj3OTg00DNj4NTg00fYj4MTg00\@j6;j7TTg00Zgj2LTg00[Gj1CTg00[`R2j2PTg00gDj1JTg00A:j4?Tg00Hlj6jTg00]@j1ATg00]^j3iTg00RWj2hTg00Y=j3gTg00Yaj2bTg00`nj6`Tg003aj1\Tg00Pmj3ZTg00Fcj5]Tg00gdj4^Tg00hMj4_Tg00hij1GTg00iIj6aTg00iej3HTg00jHj3dTg00HHj7eTg00J4j8VTg00IPj7fTg009VR3f0R4'8p=7g00OFR5f1R6;34p=6g00K6R7P6g00PFP4C?p=DP6g00L4R8g00LSR9P9g00M3R:P4g00MSFep=9f3R;P8P9P9P:f2R<P6P4GVp=:A3743p=>P<P8P9P9P:P6P4Ffp=I%74R=g0091R>#5R?#FR@%5?#5#5#5#5R?#FRA'BRB,14RC'<RD1=<614<B/=6P5f4RE/0610;6RF'2f5RG/4B/=E/0<,64X15P514EBRH/06/2F10G<10E<'2/64X151K6A116ARF18A6RI'kP111<A18A<f6R1/0;10G;RJ'2141B/0;/2J'6P411;AP5f7RJ/0ERKf8RL/0GRM10JGRN'2124N'6X15101ERO,2K,@514JB/0EPJPAPEg00N3RK#cRP%[KRK1Y76RQ%X7RR%W7RS1U7>R>1E7ART'D,9SRU%S9RVPUC:1RS:RUP4P<g00OfRW,@51Q4<=35WdAO736CNRWb4b5b6X07114APF[^07P4PGP6O2b3CME;W8P4O118A;P5POg00jkRF1L13%>1RX%CX'PP2%>JR2%C210L1=35FP4%>LR2P7P3f9RX,06=35F^7DX=71833113BRD'<%JLW7PXP4PLFTWAP4O1%C2PXPJp-0R2PPPKPQPRPSP71E73RYg00N_RZP>C?,9SR[PSP8P9P9P:P;EjR\5ISR]PVP[C:PUPWb4b5b6X07W21<=6%76R[[^07^22P4f:R^/1BP^PXO3b3%AXPAPJ1136RJP01B@6,1<%A;/1<[R0%A</161B@<,1;R_[%AE/1;\_Ai<64P6n2001000000120000000UX17X<7P0\J^17^<7P4P^PA1h@A113@RJ%7APD[RD[%7@R0g00b9R_Ag@A6UW:%7B\_^:0P6g00bU1b3@'@PJeO1PDPPPKPQPRPSPSP8P9P9P:P7P>g00aRPYC?,9SE`PVPSP]PV1DY>,9SC:C:PUPWb4b5b6X07X22%>4g00c;[1<[<113<[[^07^22P4f>R</1BP<PGf=O4b3b;b?b;PPPKPQPRPS1E7@%\?5Z7,D>,9SR?9IS\PVP?C:PUPWb4b5b6X07X221<6C116B[^07^22P4f;R2#7P2P^O3b3O4b9PPPKPQPRPSP7PTPZP>C?,9SRSPVPSC:PUPWb4b5b6X0718A4PI[^07P4PLPEO2b3D]C^WCP4O1n200110200021010011101bEC_A35FOP5PF10X1/2414XB/01R1/24'6X15P5PF121F,64X15P5PFA35F4X151@5F14LB/0GRG/2F%GGE;12MF%GME;PNP4Eab9W8P4O1n200100000021000011000bD1=H;/06AHH;6E;1=E;/06AHE;6E;X>=XB73dW7X=7X@7o"). Qed.
Lemma zr_land_lit : forall e m, (0 <= m < 2^64)%Z -> inr64 (Z.land e m).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01ah11bh21Hh32Hmh47__arithh54__ffh68__varmaph75__with81eh91mh:1zp;2p;1p;3p;4p;7p;6g006?j23Tg003<j10Tg00:Pj15Tg00:nj27Tg007Dj21Tg007`R0j2JTg00R7j22Tg00WGj24Tg008;j1<Tg00QPj3;Tg00=Mj18Tg00=mj19Tg00E@j1:Tg00>kj1LTg00?Ij1KTg00@4j26Tg003aj1ITg00Pmj3CTg00A:j4BTg00HHj7?Tg00BGj2@Tg00;ij2ATg00Bij2>Tg00CUj3=Tg00Coj3DTg00DNj4ETg00kKj4FTg00lEj3GTg00\@j6HTg00K6R1g009VR2f0R3'3g0091#0R4#5R5%04#0#0#0#0R4#5'7R6,13'JP1f2R7/26R8f1R9'4%<3X:1P8P91123R8P01279R0,32R:1109f3R0/27,32A;793P9n2001000000120000000UX11X01P:\8^11^01P3P0P6g00N3R0#8%90%:1%L1%K1R0g00L4g00LSR8P8g00M3R8P11612g00PF1615%I45C1CBg00MSF?1@08P3P7g00OFR8g00OfR0'A1>37==80dAD129CEb5b6b71126P3b4O3b2P3CF1479AG793EHW3X91W8o"). Qed.
Lemma zr_lor : forall a b, inr64 a -> inr64 b -> inr64 (Z.lor a b).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h07__arithh14__x1h22Hah32Hbh44__ffh58__varmaph65__with71ah81bp;1p;2p;4p;3p;7p;8g008;j18Tg00=Mj1MTg00=mj1>Tg00>Mj29Tg00>kj1LTg00?Ij1GTg00@4j26Tg00@Wj2=Tg00A:j41Tg003<j10Tg00:Pj14Tg003aj1:Tg00Pmj3KTg00IPj7JTg00Aej1HTg00J4j8FTg00BGj2ETg00;ij2CTg00Bij2?Tg00CUj3@Tg00Coj3ATg00DNj4BTg006?j23Tg00:nj2DTg007Dj22Tg007`j27Tg00mCj4<Tg00n@j2;Tg00HHj7ITf1R0g00L4R1g00LSR2P2g00M3R3f0R4g00MSFIp=5g00K6R5%80R6f3R7f2R8g00N3R9#M%>91950%L5%G5R9P1P2P2P3P9P1P2P2P3P5g009VR1,65g00N_g0091R:,=5R;C1,59P5P;g00PF%0:R:#4R;,65%0:#0#0#0#0R:#:5K5C1,59FJR<%H2P<GF1E93P4P8g00OFR9g00OfR3'C1?48=@93dAA510CBb4b5b6X15R31314%4:,D;R;,24'71310120;'7[^15R;P4f4P8O2b0P3P;P4P7P0O2b0C<1;78#8eX36W2X85W7o"). Qed.
Lemma zr_lxor : forall a b, inr64 a -> inr64 b -> inr64 (Z.lxor a b).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h07__arithh14__x1h22Hah32Hbh44__ffh58__varmaph65__with71ah81bp;1p;2p;4p;3p;7p;8g008;j18Tg00=Mj1MTg00=mj1>Tg00>Mj29Tg00>kj1LTg00?Ij1GTg00@4j26Tg00@Wj2=Tg00A:j41Tg003<j10Tg00:Pj14Tg003aj1:Tg00Pmj3KTg00IPj7JTg00Aej1HTg00J4j8FTg00BGj2ETg00;ij2CTg00Bij2?Tg00CUj3@Tg00Coj3ATg00DNj4BTg006?j23Tg00:nj2DTg007Dj22Tg007`j27Tg00n]j4<Tg00o[j2;Tg00HHj7ITf1R0g00L4R1g00LSR2P2g00M3R3f0R4g00MSFIp=5g00K6R5%80R6f3R7f2R8g00N3R9#M%>91950%L5%G5R9P1P2P2P3P9P1P2P2P3P5g009VR1,65g00N_g0091R:,=5R;C1,59P5P;g00PF%0:R:#4R;,65%0:#0#0#0#0R:#:5K5C1,59FJR<%H2P<GF1E93P4P8g00OFR9g00OfR3'C1?48=@93dAA510CBb4b5b6X15R31314%4:,D;R;,24'71310120;'7[^15R;P4f4P8O2b0P3P;P4P7P0O2b0C<1;78#8eX36W2X85W7o"). Qed.
Lemma zr_shiftr : forall a k, inr64 a -> (0 <= k)%Z -> inr64 (Z.shiftr a k).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with52Hah62Hkh71ah81kp;1p;2p;4p;3p;7p;8g008;j15Tg006?j29Tg00=Mj1>Tg00=mj1:Tg00>Mj2NTg00>kj1GTg00?Ij1?Tg00@4j26Tg00@Wj2<Tg00A:j42Tg003<j10Tg00:Pj14Tg003aj1MTg00Pmj3LTg00IPj7KTg00Aej1FTg00BGj2ETg00;ij2@Tg00Bij2ATg00CUj3BTg00Coj3=Tg00DNj4CTg00:nj2DTg007Dj27Tg007`j28Tg0109j4HTg0119j2;Tg00HHj7ITg00J4j8JTf1R0g00L4R1g00LSR2P2g00M3R3f0R4g00MSFIp=1f3R5P1P2P2P3f2R6P0P4GJp=3g00K6R7%50g009VR8/90R9P5P6g00N3R:#>R;%::R:1N70R<%G7R=%?7R>P>P1P2P2P3P71678g00N_g0091R1,<7R?C2,1>R@P7P?g00PF%01R1#4R?,67%01#0#0#0#0R1#M5L7C2,1>FKRA%F2R2PAC31E>3R3P4P6g00OFRAg00OfRB'@1A46=BABdA=780CCRBb2b3b4X071984R8%41,D?R?,74'8170?,89[^07P4f4P6O2b1P;P:P<P=P>P@P2P@C3P3PBb2b3b4X07P9\8^07P4P5P0O2b1CH1;56#5eW6W5X87W7o"). Qed.
Lemma zr_div : forall a k, inr64 a -> (0 < k)%Z -> inr64 (a / k).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with52Hah66__sat1h74__x2h81Hh93Ha'h:2Hkh;6__sat0h<1ah=1kp;1p;2p;3p;4p;5p;7p;8g008;j1=Tg003<j10Tg00:Pj19Tg00:nj2YTg007Dj26Tg011Yj2>Tg00=Mj1HTg00=mj1GTg00>Mj2BTg00>kj1ETg00?Ij1dTg00@4j2CTg00@Wj2@Tg00Aej1VTg00BGj2UTg00;ij2?Tg00Bij2PTg00CUj3OTg00Coj3NTg00DNj4MTg0126j4LTg00RWj2ITg00Y=j3JTg00Yaj2KTg00S?j1;Tg00S^j27Tg012Wj3<Tg013@j2QTg00TGj3RTg00U0j2STg00U\j3TTg00E@j1cTg00E^j4bTg013ij5aTg003aj1_Tg00Pmj3^Tg014Mj3\Tg0150j2ZTg006?j2ATg015Mj5[Tg0169j5XTg00GHj4]Tg00A:j4DTg00HHj7WTg00J4j8`Tg009VR0f0R1'Ap=1%01#0#0#0p=e1601p=5g00K6R2f1R3g00N_P1CDp=8P3g00L4R4g00LSR5P5g00M3R6P1g00MSFWp=3f3R7P4P5P5P6f2R8P3P1G`p=2P2P3g00PFP1CDp=:%01#0p=F%01#0#0#0#0#0#0#0p=4%=3g007`%18R9g0091R:#0R;#9R<%0;#eR=#9R>'YR?,68%58R@f4RA/>7#=[P1%1Af5RB/6?%5Bf7RBf6RC'>RD#116D?PBPCg00N3RE#HRF%GERG1B23RH%E2RI%d2RJ1C20RK1@2:R:'8,3JRL%V5RMPLC21UJ6RNP1P8g00OFROg00OfRP'?1P18=OOPdAN203CMRPb2b3b4X02%11%13[^02P1f8ROP7O2b1PFPGPHPIPJ1:K:,3JRQPMPQC2PNPPb2b3b4X02%51%53[^02P1PBP3O2b1RQCLPDPBP?PBPCPBPQ1I<>%5<RQ%1>%5?[RB[%1<RRg00b9RSAJ<>3UW5%1?\SRS^5RP3g00bU1K0<'?PQeO1PBg00V<RB#;RQ#;R0#;,72172B5<2%F=#4#4#4#4#4#4#4#9,Q2172Q17205<25<25R2g00V['S=TEFPGP21B28P3%c2CbPIPJPJ1C2<R<,8K,3JPMPJPJP4P5P5P6DaPM%_=9^2<R<,8K,3JC2C2PMPJ1@2;R;,:K,3JPMPJPLPMA\2;:,8:,3JC2C2C2PNPPb2b3b4X02X72PS\R1ZA7,A7\9\@[^02^72P1f:f;P8PAPCO5b1b6b;b6D[PFPGPHPIPJ1::<,3JRJPMPJC2PNPPb2b3b4X02161?163?[^02P1POP8O2b1DXC]%=DeW:W9W5P3P1O2n2001000000121000000W8X=2X<2o"). Qed.
Lemma zr_b2z : forall b, inr64 (Z.b2z b).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01Hh12H0h23Heqh31eh41bi001bi011cp;1p;3p;6p;2p;4g016^j11Tg008;j12Tg00CUj30Tg00iIj63Tg017;j26Tg00;ij25Tg00GHj44Tg00OFR0P0f0R0#1#2P0g00bUR1g017ZR2g018@R330R4g00c;R5[A0122R6P0P4P1P2P1p-0R7P0P5g00b9R8P5n011010003000000X31g018fR9P3P0E3P51650R:b1b2X041512R2C4g00Of#1#2eg019BR4=013R;P5[P6P0P;P1P4P1P7P0P8P5P5n011010003000000X31P9P3P0E3P5P:b1b2X0;P2C4g00jk#1#2en0110000020000W4o"). Qed.
Lemma zr_ite : forall (b : bool) x y, inr64 x -> inr64 y -> inr64 (if b then x else y).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01xh11yh21Hh32H0h41bi001bp;1g008;j10Tg00OFR0P0g00K6R1f1R2#0R3P0P1f4f3f2n0110000020000#0\3[^11]0f0R0P2X33X23X11X01P0X33X23X11X01n0110000020000W4o"). Qed.

Lemma inr64_unsigned_lit : forall e, inr64 e -> bv_unsigned (Z_to_bv 64 e) = e.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01Hh11ep;1p;2g008;j11Tg019hj20Tg00K6f0R0#1f1/00W0W1o"). Qed.

Ltac is_Zlit_zb a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

(* [comment removed for export] *)
Ltac slim := repeat match goal with x := _ : Z |- _ => clearbody x end.
(* [comment removed for export] *)
Ltac sassumption := match goal with H : ?T |- ?T => exact H end.
Ltac flia := first [ sassumption | slim; lia | lia | assumption ].

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
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h02b1h12b2h21nh31zh41Hh57__arithh64__ffh78__varmaph85__with91ep;1p;3p;2p;4p;7p;6g004?j13Tg00CUj30Tg005Uj21Tg01:dj3=Tg003<j12Tg003aj1ITg00:Pj18Tg00:nj2@Tg00R7j26Tg01;Hj25Tg01;nj24Tg00=Mj1<Tg00=mj1;Tg00E@j1LTg00>kj1KTg00?Ij1JTg00@4j2:Tg00Pmj3HTg00A:j4GTg00HHj7CTg00`nj6BTg00BGj2ATg00;ij2?Tg00Bij2DTg00Coj3ETg00DNj4>Tg01<Tj3FTg01=5j29Tg00\@j67Tg00K6R0g00JXR1f0R2#3R3f1R4#3R5g007`f2R6#3?042f3R7/161174500R8[11641162500%37?064[R9f4#3?076\8A=642P2n2001000000120000000W1W0W2P9^15^03^21P2g0091#2R1#2#2#2#2#2R3#IR5%81R1%83'@R3,64R9,55R81554R7P01459R:1556,159002X30P01454R;1663,45=002X30g00N3R<#<%;<%L0%K0%J0R<g00L4R=g00LSR>P>g00M3R?P<P=P>P>P?P01:01=H05g00aRg009VR1,:0CGg00MSFCEB1A<?P2P6g00OFR?g00OfR<'?1D26=0?<dAE014C>b6b7b8A0031g00c;[P2b59F43A00:;e11571954E711581959E7O4b4W9o"). Qed.


(* [comment removed for export] *)
Lemma zb_land_pow2_small : forall y k, (0 <= y < 2^k)%Z -> (0 <= k)%Z -> Z.land y (2^k) = 0%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h04__x1h11bh27__arithh34__x2h41Hh52Hih64__ffh78__varmaph85__with91yh:2Hah;6__sat1h<1ah=1ih>1ni001nh?1xh@2HkhA3HnehB2HyhC6__sat0hD1ei011ehE1khF1si021shG1zp;1p;2p;3p;4p;7p;6p;8g003<j1sTg00:Pj1WTg00:nj22Tg007Dj26Tg007`R0j2@Tg00WGj2GTg00e5j20Tg00eVj23Tg00CUj35Tg00Zgj2LTg00[Gj19Tg00[`R1j2rTg011Yj2ATg00R7j2BTg01=dj3\Tg00=Mj1[Tg00=mj1YTg00>Mj2HTg00>kj1VTg00?Ij1TTg00@4j2STg00@Wj2CTg00A:j4=Tg00Aej1OTg00BGj2NTg00;ij2>Tg00Bij2KTg00Coj3MTg00DNj4JTg00E@j1PTg00E^j4QTg00IPj7ITg01>Kj3RTg00\@j67j7oTg01>nj1qTg01?Mj2pTg01@5j2:Tg01@Rj2lTg00RWj2kTg00Y=j3dTg00Yaj2cTg00S?j1FTg00S^j2ETg01A3j1_Tg01AQj2^Tg01B2j3]Tg00TGj3`Tg00U0j2aTg00U\j3bTg00hMj4eTg00hij1ZTg00iIj6fTg01B[j3gTg00gDj1hTg00iej3iTg00jHj3jTg006?j2XTg00HHj7mTg00J4j8nTg00`nj6UTg009VR2f0R3'Xp=4g00K6R4f1R5;53p=8g00OFR6g00jkR7753p=1A5432p=?P5g00L4R8g00LSR9P9g00M3R:P3g00MSFmp=;f3R;P8P9P9P:f2R<P5P3Gnp=<P5P8P9P9P:P3EUp=D%45R=g0091R>#sR?#WR@/23,65'@12@<RA,G;%43RBP6f5RC/05f4RD,2@RE/05'3102<9563X16P6P7f6RF/0<12@C/0<'3=563X161L5D185DRG%9G'rP118<CR1%91f7R1/0;12@F/0;'3#1P318;FRGP4P1f:RH/05f9RI,2@RJ/05'3#1^5BX=4%41P6g00OfRK10HI/33#1X16P6f8RL,0IRM%13X16P010<5#11A;A/B@#?RA[12@5,A</B@#?10;<#1[RN10D;#1\AA\<53P3n2001000000120000000VBX>4X<4PN\B^>4^<4P3PHPIg00N3RN#[RA%YNRO1H45%V4RP%T4RQP41S42g00N_1C4>RRC=,;QRS%O9RTPSC<1NQ:RUP3P<1>6K1K3<=56KdAM425CJRVb6b7b8X04RWP=\B^04RXP3PHPLO2b2P4P21B3@#?XG41>421AHJPAPOP41H4<P5%P4CQRYPPPQPQP8P9P9P:PSP4PRg00PF1C4?R?C=,;QFIR:PTP:C<PUPVb6b7b8X04X341635,@B165<,@=[^04^34P312@HRBf;R:PIO3b29RHJE7O4b413MK%qME712@L/0LPWPXP3PIP1O2b2,pLE7W5PDP3P;FoWDP3O1%9GP61:1DRG10ICRM/33#1X16P6PGP7P01:53#118<5#9R0[1853RK#91:<5#1[RJ1:;<#1\01l53P3n2001000000120000000X94X?4PJ^94^?4P3PLPC1k@L162@RJ%4I162B[[%4@RBg00b9R0Ad@:5UW:12@:R:#4\0^:BP5g00bU1c2@'>PJeO1%4H162:[g00V<R:#F#F,E4%_>,^41E4:5]45`4g00V['a=bNAPOPYPPPQP4P?g00aRRPPRC=,;Q,DQPTPQPSPTP4PRPPP?C=,;Q,DQC<C<PUPVb6b7b8X04X34g00c;RV\K18<;PV[\=[^04^34P3PIf<PCPHO4b2b;bCb;O3b4CeA567GP6P710HF/33#1X16%ZM1:LCP3Efb412@1/0DPWPXP3PLPFO2b29g1DE7WAP3O1n200110200021110111100bF1025%h5E71GCE/05AiCE5E7W5X=47j2X@=WBXE4X94o"). Qed.
Lemma zb_lxor_pow2_small : forall y k, (0 <= y < 2^k)%Z -> (0 <= k)%Z -> Z.lxor y (2^k) = (y + 2^k)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01kh11yp;2p;1p;4p;3g006?j2:Tg003<j19Tg00:Pj12Tg00:nj20Tg007Dj28Tg007`j27Tg01CBj23Tg00o[j24Tg01C_j45Tg01Dbj36Tg00hMj41Tg00K6R0g009Vf1R1':R2g0091#9#2R3f0R4'0,81'7P0f3R5f2R6,03R3'31453P5P6P1P4C59653C1V2UX00W1o"). Qed.

Lemma zb_lxor_sign : forall x, (0 <= x < 2^64)%Z -> Z.lxor x (2^63) = ((x + 2^63) mod 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__x1h17__arithh24__ffh34__p1h48__varmaph55__with64__x2h75heq_yh81zh91Hh:2H0h;1xh<2Hxh=5lemmah>1oh?1yp;1p;2p;3p;4p;6p;9p;7p;8g003<j1;Tg00:Pj1DTg00:nj2NTg007Dj27Tg007`j28Tg00ZBj1<Tg00f4j2cTg006?j2@Tg00XJR0j2^Tg00o[j21Tg01CBj22Tg00R7j26Tg00;ij29Tg00=Mj1wTg00=mj1vTg00>Mj2UTg00>kj1oTg00?Ij1gTg00@Wj2QTg00@4j2BTg003aj1RTg00Pmj3VTg00Aej1_Tg01ELj3HTg00BGj2]Tg00Bij2\Tg00CUj3Gj1qTg00Coj3[Tg00DNj4ZTg01Eoj3MTg00E@j1YTg01FRj4XTg01GUj2>Tg01A3j1yTg01AQj2xTg00S?j1LTg00S^j2CTg01B2j3WTg00TGj3=Tg00U0j2KTg00U\j3JTg00E^j4uTg01H2j3tTg01HUj1pTg01IEj1nTg01J4j6lTg01J_j2STg01KKj6fTg01Kll9hTg014Mj3iTg0150j2eTg00`nj6jTg01Lfj4kTg00iIj6TTg01MGj1dTg01Mij1mTg00\@j6PTg01NQj3bTg00A:j4ITg00HHj7aTg00Hlj6rTg00IPj7sTg00J4j8`Tg009VR1f0R2'@p=5g00K6R3f1R4;G2p=0P3P4g00PFP2CIp=FP4g00L4R5g00LSR6P6g00M3R7P2g00MSFap=3P3P4g00N_P2CIp=EP4P5P6P6P7P2Erp=Of2R8P5P6P6P7P4P2Fsp=?f3R9P5P6P6P7P8P4P2G`p=4P3f4R:P9P8P4P2EPp=:P3P4g00aRP2CIp=A%52g0091R;#;R<#DR=%;<#;#;#;#;R>#D'NR?,72'8%<;#<#<#<#<R@#DRA,N=RB,c4174B1@B4'^P0178BR01@B8RC119B129B/6?'0P2179BRD12:BREf5RF/2BRG/6?,02X83PE10G2X83193E16E?p-0RGg00N3RH#wRI%vHRJ1U34RK%o3RL%g3RM1Q3;RN1B3=R=%R@5V3R@'F,3MRO%_6RPPM1B31RQ/EN,3MRR1OM95?MRSPPAH3N@RT,EQ,3M%R>9V3=R=,FT,3M5?MC4C41]M7R>P2P8g00OFRUg00OfRV'91\28=GUVdA[314CZRVb2b4b5X03W3172BRU%54/88RW128BRX#517X?'8[[^03^3GP217F?PFP4P:O4RYb19ME?D:11:BP:PAPIPJPKPLPMPOPPPMPSPPA?MROROC4C4P>PVb2b4b5X03X3G%58/80\W\U^03^3GPYb1PIPJ%Y3RYPL1B3A,EQ,3MP>PVb2b4b5%5AP2b1RUCXD:W9P2O11@B91>:BP31>FBRW,93102WRWePW%y;,x3RWg00V<R0#LRS,C3RE5W31C30R05=3g00V[RZ'K=JHIPJP31U38P4PYCuR[PLPM1Q3<R<=t3@,AN,3MR\PP1AT<,3MC4P>PVb2b4b5X03X631>4B,02R]124BR^/08[^03^63P2f7R_P8P4O3b1b7122BR`/0FP3P^112B16`?'0X;3114BRa/0^P3%q3Rb%p311XB118BRc/1BPXPcP3Pb%n3PcPXP2ElPBPB1S3BEf12XBRX/6?RcPc1S3cM9hW=P4PAf6RA/>BRb,93104bRbeRdPb%LSRS#L,C3ReA=3E05=3/KZAW3We1C3S==305=3/KZ=JHI5JHRHPJP[PLPMP\PPPM1E@<,3MRZPPPM1OM:1F<=,3M5?MR<PPPOC4C4C4P>PVb2b4b5X03X63X3G179?RO,8:R0%59RS/8D[\C\]^03^63^3GP2f8RD#5PDP9P4P:P_O6b1b7PdPbPUb7CX11BBRU,14102cX83ReP3P11182/0cX83P4PePdPbPIPJPKPL%D;R;,B3=i3=9H3NAH3T@'A,3MP>PVb2b4b5X031e;?RT,2212`B'0^03P2P9O1b1b7124T12^B'0P3128TRT162?,09X83168?R^1092X83R9P8P91938P^1>_BR_,93108_R_eR^P_PHPJP[PLPMP\PPPMPZPPPMP<PP1FN=,3M9?MRC4C4C4P>PVb2b4b5X03X63X3G18SO\0\C\]^03^63^3GP2f9RG#5PGP:P4PFPDO6b1b79M8?D:16T?P8P;P?P^P_PIPJPYPLPMP5P6P6P71A=Q,3MEjP>PVb2b4b5AG3?1g00c;[P2b1b7CkD:PXP2ETb:1141%d4D:PU%mBEP11aBAb4BBD:O2PAP2ETb:b?W9P2O1n200100000021100011000b>W<X;3o"). Qed.

(* [comment removed for export] *)
Lemma zb_signed : forall x : word,
  bv_signed x = (if bv_unsigned x <? 2^63 then bv_unsigned x else bv_unsigned x - 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with52Hah64__p1h76__sat1h86__sat3h91zh:2Hrh;6__sat0h<6__sat2h=1bi001bh>1li011lh?1ni021nh@1ri031rhA1xp;1p;2p;3p;4p;6p;7p;8g003<j16Tg003aj1HTg004?j1ZTg004bj2VTg005Uj23Tg006[j1^Tg007Dj20Tg007`j28Tg00:Pj1?Tg00ZBj19Tg00:nj2DTg01O5j2PTg01OXj2OTg01P5R0j2mTg01CBj25Tg00R7j2JTg01GUj24Tg00=Mj1]Tg00=mj1\Tg00>Mj2[Tg00>kj1YTg00?Ij1XTg00@Wj2WTg00@4j2BTg00Pmj3GTg01ELj3FTg01H2j3@Tg00BGj2UTg00;ij2ETg00Bij2TTg00CUj3=Tg00Coj3RTg00DNj4QTg00Aej1STg00Hlj6nTg01Eoj3LTg00\@j6MTg00[Gj1lTg01A3j1kTg0150j2jTg014Mj3eTg00RWj2KTg00Y=j3ITg00Yaj2aTg00E@j1`Tg01Lfj4bTg00iIj6_Tg01PXj2cTg006?j2dTg00A:j4CTg00HHj7fTg00IPj7gTg00J4j8hTg00`nj6iTg009VR1f0R2'dp=1g00K6R3f1R4;=2p=7P3P4g00aRP2CCp=AP4g00L4R5g00LSR6P6g00M3R7P2g00MSFfp=2P3P4g00PFP2CCp=<P3P4g00N_P2CCp=>f2R8P5P6P6P7P4P2Fgp=:f3R9P5P6P6P7P8P4P2Ghp=;P4P5P6P6P7P2Eip=Ng0091R:#6R;#6#6#6#6#6R<#HR=#Z1V=213=2R>#1%^=,0>'813=4R>%?;R;%9:#9#9#9#9R?#?R@'DRA'P10>A1O>ARB'm13=8/OAg00OFRCP013=9/0Af5R0,3=RD/5ARE%?<R<,D;RF'JRG/4APCP3P4PD14DFn0100000020000'7P4f4RD,3=/0ARHP3PE142ARIf6,3=RJ'7X93g00N3RK#]RL%\KRK1[34RM%Y3RN%X3RO1W3:RP1B3;RQ%H?5G3R?5F3RR=@3?/AP'21UO7RSP2P8g00OfRT,EC1T28==CTdAR314CQRTb2b3b4X03152ARU/4A/72^03P2PJO1RVb1PGp-0RWPLPKPMPNPO1<P?,2ORX%S6RYPO1B31RZ/>P,2OPOP5P6P6P7P9EnR95:OPY1>ZR,2OAG3Q=RQ,<R,2O5:OC;C;PSPTb2b3b4X03W6102AR7%14/88158AR6#1106F'8[[^03^6WP210JFPJP4P0O4b19LEFEMW>P2O1%lHP3%k:R:/jFRH,5ER0/JFR514JF,7IX93RIP3P0PIPLPKPMPN1B3:=e3Q9F3RRR=@3?A@3PQ'A,2OPSPTb2b3b4X0315UH/4A142F'7^03PVb1P51K;@101;R5%1@101A[RV[%1;RUg00b9R?AI;@4UW5%1A\?^5U1K;<%1<101F[RA\5AI;<4V?X5U%1F\?^5UP4g00bU1a1;'EP5eR5O1PAPDP5O1PVPLPKPMPNPO1NOXPYPO1<PQ,2O9:O9PY1>ZR,2O1<RQ,2O5:OC;C;PSPTb2b3b4X03X6Wg00c;RR\7104F,88156HRH#110HF'8[[^03^6WP2f<,3=RW#1PWf7f;O4b1b8b7b;b7b<b89L0FEMPGPEP:PFPLPK%`3PN1AQZ,2O,NOPSPTb2b3b4A=3F1PR[P2b1CbE_W?P2O1n10210010300021110111102b=b@1c=4PCP3PBP>14>Fn0100000020000'7eb:WAo"). Qed.

Lemma bv_eqb_Z : forall x y : word, bv_eqb x y = (bv_unsigned x =? bv_unsigned y)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01xh11yp;1p;2g003<j10Tg003aj15Tg004?j12Tg005Uj21Tg01@5j24Tg00;ij23Tg0091#0#0#0#0#0#0#5R0#2R1g00OFf1,10f0,10'4'3X11W0o"). Qed.
Lemma bv_ltu_Z : forall x y : word, bv_ltu x y = (bv_unsigned x <? bv_unsigned y)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01xh11yp;1p;2g003<j10Tg003aj15Tg004?j12Tg005Uj21Tg01OXj24Tg00;ij23Tg0091#0#0#0#0#0#0#5R0#2R1g00OFf1,10f0,10'4'3X11W0o"). Qed.

Lemma bv_lts_lxor : forall x y : word,
  bv_lts x y = (Z.lxor (bv_unsigned x) (2^63) <? Z.lxor (bv_unsigned y) (2^63))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h04__x1h11zh27__arithh34__ffh48__varmaph55__with64__x2h75lemmah86__sat1h96__sat2h:6__sat3h;2Hah<4__p1h=6__sat4h>1bi001bh?1ri011rh@6__sat0hA1li021lhB1ni031nhC2HxhD2HyhE2l0hF2n0hG1xhH1yp%0p&0p;1p;2p;3p;4p;6p;9p;7p;8g003<j1?Tg003aj1dTg004?j1sTg005Uj23Tg00:Pj1RTg00ZBj1DTg00:nj2`Tg01OXj20Tg01GUj24Tg01PXj2WTg00o[j2ETg004bj2fTg006[k102Tg007Dj21Tg007`j2>Tg01CBj22Tg00R7j28Tg01O5j2^Tg01P5R0j2]Tg01J_j2FTg01Q@j2=Tg01Q`j3mTg00=Mj1lTg00=mj1kTg00>Mj2UTg00E@j1jTg00E^j4iTg00>kj1hTg00?Ij1gTg00@Wj2TTg00@4j2OTg00Pmj3STg01ELj3NTg00BGk203Tg00;ij2eTg00Bik201Tg00Cok300Tg00DNj4{Tg01RRj3HTg00Aej1zTg00Hlj6yTg01Eoj3@Tg00[Gj1bTg01A3j1wTg0150j2vTg01H2j3_Tg014Mj3uTg00RWj2VTg00Y=j3YTg00Yaj2tTg00A:j4PTg00CUj3CTg01Lfj4\Tg00iIj6LTg01S4j2[Tg01T1j1XTg01Tkj3rTg006?j2qTg00XdR1j2aTg01Kll9xTg01UXj7pTg00HHj7cTg00`Jj7oTg00IPj7nTg00J4j8|Tg00\@j6}Tg00`nj6~Tg00OFR2f1R3f0R43Cp=:g009VR5/q4p=5f2R610345C2p=<g00OfR79C261134'ap=;AC247p=9p-0R8P1g01VSf5R9f4R:f3R;P6P3P4M9xp=IP8P1P:P;P6P3P4Fpp=GP6g00L4R<g00LSR=P=g00M3R>g00K6R?P3g00PFP4CPg00MSR@Fcp=7P6P<P=P=P>P3P4Fop=M1134,a6p=KP?P3g00N_P4CPp=QP3P<P=P=P>P4P@Fcp=JP6P<P=P=P>P3P4Fnp=AP;P<P=P=P>P6P3P4G|p=BP?P:P;P6P3P4E}p=6P3P<P=P=P>P4E~p=Zg0091R@#?RA#?#?#?#?#?RB#dRC#sS00Q00P2P?13C3RD%RARE%D@#D#D#D#DRF#RRG'`RH'0PD%RBRB,`ERI,4Dn01000000200001WC3S01,0413C6RJ/EHRK1EDHS02'0RL':X1?P2P?13C4RM/0HPM14MIn0100000020000P2P?10JHPJ14JIn0100000020000S03/04/:LX1?1fC3RL%5D&02C,1D'>RDPLPD13C;RD/2H/8IP2P?13C:RL/0HRNPL14LIn0100000020000P2P?10DHROPD14DIn0100000020000S04'0RP1EDHRQ7<4X1?12JH/8I12LH/8I=<P4X1?1^DH11DH/]OPNP2P013C9/1HP2P?P3f7S05,3CRN14NIn0100000020000P2P?f6,3CRO/0HRPPO14OIn0100000020000'012NH/8I12OH/8I3<P311OHRR1^OHS061]RPS0710NHS08P2P0f8,3C/1HS09f;S0:,3CRNP2P?P3f:RP,3CRO14OIRSn0100000020000RT'012NHRU/8IRV12OHRW/8IRX'0RY':P3f9RZ,3C/1HR[PUf<,3CR\/0NR]104VR^':X1?PW12\HR_/04R`,:]X1?10NORa10UWRbA;aNO%9]11\NR]P410_U#9RaPa1F8aEIW71=NOA;bUWg01WD9m81R1P]Pa11_UP4DGW71=UWg00N3Ra#lR]%kaRaP?1U?6P3%j?S0;CiRb%h?Rc%g?Rd1T?@Re1T?ARA57d1O?ERf%dF5S?RF9N?eRgAN?AFRh57d3M203d>RiP4P61e2720146#9dB00?53C{R7b3b4b5X0?X6?1143124HRj123HRk3K^0?^6?P4PNP\O2Rlb2O2O23HPXP]Pa1U?3S0<PcPdA7deFRF%z=RmPd1O?5Rn/Qe,JdS0=PdP<P=P=P>P;EyR;5AdPm1Qng,JdAS?fCRf97dg5AdCBCBPiP7b3b4b5X0?X<8R>114HR=%53S0>/>6126HR<#511<I'>[[^0?^<8RoP411NIPNP3PZO4b29@WIS0?D6PVP>PoP411\IP\P9PPO4b29@UIS0@D6WEP4O1%b[RPPU14NIR9,0\Ro/:^X1?P?%w@R@/vIR>,2WRZ/8IRp1:o`X1?R`PZP`10NSR`10UZRqA;`NS%9o11\9RoP412U>R`,0_#9RrPr1F8rEIW71=NSA;qUZP1PoPr11_`P4DGW71=UZP]PaPbPcA_?AfRr97de1O?@=u?fRo9N?hRq97dg5MdPiP7b3b4b5X0?X6?143IRs,1412k>Rt7Kj^0?^6?Plb2O2O23HPp1VEGRu115ERv%5G115H[Rw[Rx%5ERyg00b9RzAYEG3UW;RG%5H\z^;yR{1VEBR|%5B115I[R}\vR~AYEB3VzX;yRB%5I\z^;yRyP3g00bU1t5E'ePveRvO1REP}P:PvO1RvPwP]PaQ0<PcPd1ZdFPmPdA7defRF9Ad;PmAN?goRo,Qn,JdA7dof5AdCBCBPiP7b3b4b5X0?X<8Rgg00c;R;\=113IR=,>612<>R<#511<I'>[[^0?^<8R<P4fA,3CR:#5P:Q05f?O4b2R:b:b8b@b8b9b:9@ZID6PXPWP@PIP]PaQ0;PcP?Pfg00aRPnCP,Jd,ZdPiP7b3b4b5AC?I5P;[P4b2R;C\R5ELPVQ0@D6WBP4O1n10210010100021110211103b>b?WAP4O1%bRQ06Q07Q08P2P0Q09109T/:YP3PW14\IR\/0NRY18_I;<4X1?P?18`IRTA<Y4UX1?R0P`P0109OR010`WR2A;09O%9Y11\NRNP412_>R_/0U#9RYPY1F8YEIW71=9OA;2`WP1PNPY11_UP4DGW71=`WP]PaPbPcA_?efRf=7dAA7doh5MdPiP7b3b4b5X0?X6?144IRh/1312j>R>;Kk^0?^6?Plb2O2O23HPTPuPxPGP{P|P~PBPyPEP}PvPwPgP<P4fB,3CR<#5P<Q0:f@O4b2R<b:b8b@b8b9b:9@`ID6PVPUP@PIP;C\R;ELPXQ0?D6XA[P4O1P?PT10\9R[/:^X1?R^P`P^P?PpA<[_4X1?R^PZP^109SR^10`ZR@A;^9S%9[11\9R\P410_`#9R[P[1F8[EIW71=9SA;@`ZP1P\P[11_`P4DGW71=`ZP]PaPbPcA7dfrA7doq5MdPiP7b3b4b5X0?X6?11hs?K>t^0?^6?Plb2O2O23HPpPuPxPGP{P|P~PBPyPEP}PvPwP:b=b9b8b9b:b=9@ZID6PXP5ELPTPuPxPGP{P|P~PBPyPEP}PvPwP<b=b9b8b9b:b=9@`ID6PVP;ELXFPP4O1n10210010100021110211103b>b?WBP4O1n10210010100021110211103b>b?PKP]PaQ0<PcPdQ0==AdFRFPmPFCBPiP7b3b4b5X0?R7%54114I'>Q0>/>=[^0?R?P4PDP3O2b2,[JD6PQP7P?P4PLP6O2b2,[DD6Q04Q03'0?<QKebDbC1WC4%X4D6Q01%X3D6ArC34Q021EMH3<eWHWGo"). Qed.

(* [comment removed for export] *)
Lemma bv_lts_zero_r : forall x : word, bv_lts x (Z_to_bv 64 0) = (2^63 <=? bv_unsigned x)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h02Hah14__p1h24__x1h35lemmah47__arithh54__ffh66__sat1h76__sat3h88__varmaph95__with:2Hxh;6__sat0h<6__sat2h=1bi001bh>1li011lh?1ni021nh@1ri031rhA1xhB1zp;1p;2p;3p;7p;4p;6p;9p;8g003<j17Tg003aj1PTg004?j1[Tg005Uj23Tg00:Pj1BTg00ZBj19Tg00:nj2JTg01OXj21Tg01GUj2>Tg01;Hj2XTg01PXj2ETg01X6j2?Tg00CUj3:Tg004bj2qTg006[j1nTg007Dj20Tg007`j2ATg01O5j2`Tg01P5R0j2_Tg00XdR1j28Tg01J_j2ZTg01Q@j2GTg006?j2;Tg01Q`j3YTg01UXj7FTg01XSj2WTg00=Mj1VTg00=mj1UTg00>Mj2TTg00>kj1STg00?Ij1RTg00@Wj2QTg00@4j2DTg00Pmj3CTg00Aej1pTg00A:j4@Tg00Hlj6oTg00BGj2mTg00;ij2MTg00Bij2kTg00Coj3cTg00DNj4bTg01RRj3LTg00[Gj1aTg00RWj2KTg00Y=j3OTg00Yaj2dTg00`nj6eTg01H2j3fTg01T1j1^Tg00\@j6gTg01Tkj3hTg01Kll9]Tg00HHj7iTg00IPj7jTg00`Jj7\Tg00J4j8lTg009VR2f0R3';p=2g00OFR4g00OfR57:3p=41032p=6p-0R6P1g01VSf5R7f4R8f3R9f2R:f1R;P3M9]p=Ig00K6R<P;g00PFP3C@p==P;g00L4R=g00LSR>P>g00M3R?P3g00MSFip=5P:P=P>P>P?P;P3Fjp=NP:P=P>P>P?P;P3F\p=HP9P=P>P>P?P:P;P3Glp=<g0091R@#7RA#7#7#7#7#7RB#PRC#[P<P4P<13C3RD%BARA%9@#9#9#9#9RE#BRF'JRG'1PD%BBRB,JARH,>Dn01000000200001XC2RI,EC,1313C;RJ,?G5:4XB<1qC3%2D%nC,0D'A1`JG10JG11JG'_13C:/1GP4P013C9/0GP4P<P;13C7R01>0HRJn0100000020000/121?G0RK5:4P;13C8/0GRL1102RM%4M%60'8f6,3CRM/12#4%6MRNP31?GM#4ROPO1Z6ORPEIW31G02%4K1;G0'8RQP6P1g01WD9Y61RRPNPO1;GMRNP3FFW31WG0R0g00N3RS#VRT%USRS1T<;RU%S<RV%R<RW1Q<@R@1D<ARX%PE5C<RE'=,5WRY%p>RZPWP<1D<2R[g00N_R\P@C@,5WPWP=P>P>P?P9EoR95NWPZ1=@[,5WP<PEP\P@C@,5WR\5HWC<C<1mW?REP3P:1M451k3:#4dAc<2;CbR5b5b8b9X2<X16103GR]%2;/A:%6:1;G:R^'8[[^2<^16P310MHPMP;P7O4b4O2O27LKW>P3O1%aL11J2RL%4L%6J'81>MHRM/12#4%6MRMP3POPOPPEIW31GJ2P6P1PRPMPOPNP3FFX3QP01KAF102AR0%2F102G[RQ[%2ARNg00b9ROAOAF;UW0%2G\O^0N1KAB%2B102H[RF\0AOAB;VOX0N%2H\O^0NP;g00bU1d2A'MP0eR0O1PFP8P0O1PQPTPSPUPVPWPWP=P>P>P?PYEePZPWAC<XCRX,=@,5W9NW9PZAf<@X/=[,5W=HW\C<C<PEP5b5b8b9X2<X16g00c;\]10;H,A:1>:H#6/8^[[^2<^16P3f<,3CR6#2P6f7f;O4b4b7b6b;b6b<b7O2O27LKW?P3O1n10210010300021110111102b=b@b:1EC3%^3EgAhC3I1?GD5:4eWAo"). Qed.
(* [comment removed for export] *)
Lemma bv_lts_zero_l : forall x : word,
  bv_lts (Z_to_bv 64 0) x = ((0 <? bv_unsigned x) && (bv_unsigned x <? 2^63))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h05lemmah14__x1h27__arithh34__ffh44__p1h54__p2h68__varmaph75__with81xh91Ah:1Bh;2Hxh<1bi001bh=1li011lh>1ni021nh?1ri031rh@1yhA1zp;1p;2p;3p;4p;8p;6p;=p;5p;9p;7g003<j16Tg003aj1|Tg004?j1^Tg005Uj22Tg00:Pj1BTg00ZBj1:Tg00:nj2ITg01OXj2;Tg01GUj2=Tg01;Hj2XTg01PXj2ETg00eVj24Tg00CUj39Tg004bj2xTg006?j2MTg006[j1jTg007Dj28Tg007`j20Tg01O5j2bTg01P5R0j2`Tg00XdR1j25Tg01Q`j3[Tg01Y3j2GTg01YTj4<Tg01Z;j3WTg001?j4VTg01Zdj2UTg01[QR2j2STg01[oj4RTg01\Qj8LTg01]Dj3QTg01^:j4CTg01^mj6DTg01__l=PTg01Q@j2FTg00=Mj1TTg00=mj1{Tg00>Mj2zTg00>kj1yTg00?Ij1wTg00@4j2OTg00@Wj2tTg013ij5oTg00BGj2iTg00;ij2hTg00Bij2eTg00Coj3cTg00DNj4dTg01RRj3HTg00[Gj1aTg01J_j2fTg01Kll9gTg00Pmj3kTg00Aej1lTg01H2j3_Tg01`Nj5mTg00J4j8nTg01T1j1]Tg00\@j6\Tg01Tkj3pTg01UXj7qTg00A:j4rTg00HHj7sTg01a2j6ZTg00IPj7uTg00`Jj7vTg00Hlj6YTg009VR3f0R4';p=3g00OFR5g00OfR6794p=1p-0R7P1f4R8f3R9f2R:f1R;P4Fqp=A1834p=7g00K6R<P;g00PFP4Crp=>P;g00L4R=g00LSR>P>g00M3R?P4g00MSR@Fsp=?P:P=P>P>P;P4EZp=KP:P=P>P>P?P;P4Fup=@P:P=P>P>P?P;P4Fvp=JP;P=P>P>P?P4EYp=Ng0091RA#6RB#6#6#6#6#6RC#|RD#^P<P5P<12D4RE%BBRB%:A#:#:#:#:#B'IRF';RGPE%BC,IBRC,=En01000000200001XD3RH,ED/;412D;RI#31;IFRJ'4595XA<1xD41M3E%jD,8E'01bIF18IF/`J12D:/;FP5P012D9/8FP5P<P;f5R0,2DRJ1=JCRIn0100000020000#3%3JRK/4;595P;12D8/8FRF14K6RL%1L%1KRLA9566RM'0'5g01WD9[71RNf6,2DRO#3RP#1RQ14P6#110QMRRP4DAW01GK6%7J,5LRSP7^:7RT^97P7P7\7P1P7P7P1P1C<RUC<P1AW71NP7PTP1P7P7P1P7P7P7P2CVR2C<RVC<P@P7PTP1P11U71RTPUPVP7P7P1P1PTP1P2P7P11S4;X@7X87g01aVCRGLGLPQ%7OR2P4PR102MPQP2P4PMPMP7P1g01bL9Q71RRPMCCEDM=PW01F3JRJg00N3RT#TRV%{TRT1z<;RU%y<R@%w<RW1O<3RX1t<ARA'>,?WRYPWP=P>P>g01c<RZDoR[=KW[9@WY3J1iW?RYP4P:1h561e4:#1dAc<3;CdR:b3b6b7X1<%74R\10\M'5^1<P4POO1b2O2O25HKW=P4O1%aF%3IRFg00jkR\,4KRM%1MA95\6R6,0L'5PN1=OCRL#3#1RM14P\#110Q6RPP4DAW01GK\%1F%7I'5P7P1g01VSPM%7LRLP4PPPP1f7PM9gW01F3IPNPLPP1026PQP2P4P6P6P7P1PRP6CCEDDAX0SPJPVPTPUP@PWP=P>P>P?1NW91O<B=k<DRB,>A,?W5@W%l>A_<AB,>X,?W1NW8PWP=P>P>PZDm=KW[5@W5JWGnPYP:b3b6b7X1<X47X57184C,0;1=;C#71096'5[^1<^47^57P4P21M3OPOP0O4b2O2O2O23HW>P4O1n10210010300021110111102b<b?b;1ED4%]4E\ApDH4%3E/4G595eW8o"). Qed.

(* [comment removed for export] *)
Lemma v_sltu_b2z : forall x y : word, v_sltu x y = Z_to_bv 64 (Z.b2z (bv_unsigned x <? bv_unsigned y)%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bh11xh21yp;1p;2p;3g003<j11Tg003aj1:Tg004?j17Tg005Uj25Tg01OXj29Tg00:Pj18Tg01;Hj20Tg016^j12Tg00CUj33Tg00;ij24Tg01c\j26Tg0091R0#1#1#1#1#1#1#:R1#7R2f1R3,51f0R4,51'9R5g00OFR6P6P6P2P4%80,01g009V,01n0100000020000%24,01532P4g00Of#2,01,42g00jk#2,01,42n0110000020000b01634%25,01532eX22W1o"). Qed.
Lemma v_slt_b2z : forall x y : word,
  v_slt x y = Z_to_bv 64 (Z.b2z (Z.lxor (bv_unsigned x) (2^63) <? Z.lxor (bv_unsigned y) (2^63))%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bh11xh21yp;1p;2p;3p;6g003<j11Tg003aj1@Tg004?j1:Tg005Uj26Tg00:Pj17Tg00ZBj12Tg00:nj2;Tg00o[j24Tg01OXj29Tg01;Hj20Tg016^j13Tg00CUj35Tg00;ij28Tg01Tkj3?Tg01dTj2>Tg00\@j6=Tg01ePj2<Tg0091R0#1R1#1#1#1#1#1#@R2#:R3g00OFR4f1R5,62%71%20#2#2#2#2#7';R1'4R6f0R7,62/41'9R8P4P3P7%70,02g009V,02n0100000020000R0f2,62/41/96#3,02553X04P8P4P4%37,029530P7g00Of#3,02,83g00jk#3,02,83n0110000020000b0A?2571>57E=1<57%38,02553eX23W1o"). Qed.
Lemma v_sltiu_b2z : forall (x : word) imm, v_sltiu x imm = Z_to_bv 64 (Z.b2z (bv_unsigned x <? bv_wrap 64 imm)%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bh13immh21xp;1p;2p;3g003<j11Tg003aj1;Tg004?j16Tg005Uj25Tg01;nj2:Tg01OXj29Tg00:Pj17Tg01;Hj20Tg016^j12Tg00CUj33Tg00;ij24Tg01fGj28Tg0091R0#1#1#1#1#1#1#;R1#6R2g00K6f1R3,51f0R4,:1'9R5g00OFR6P6P6P2P4%70,01g009V,01n0100000020000%24,01532P4g00Of#2,01,42g00jk#2,01,42n0110000020000b01834%25,01532eW1W2o"). Qed.
Lemma v_slti_b2z : forall (x : word) imm,
  v_slti x imm = Z_to_bv 64 (Z.b2z (Z.lxor (bv_unsigned x) (2^63) <? imm + 2^63)%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h04__x1h14__p1h26__sat2h37__arithh44__ffh56__sat4h68__varmaph75__with84__x2h91bi001bh:1ri011rh;6__sat1h<6__sat3h=2Hah>1zh?1li021lh@2l0hA1ni031nhB2n0hC2HxhD6__sat0hE3immhF2l1hG2n1hH1xp%0p;1p;2p;3p;4p;6p;7p;8g003<j1;Tg003aj1UTg004?j1bTg005Uj24Tg00:Pj1FTg00ZBj1?Tg00:nj2STg01OXj22Tg01GUj2:Tg01;Hj2HTg00o[j2NTg01CBj21Tg00CUj33Tg004bj2uTg006[j1oTg007Dj20Tg007`j29Tg00R7j2ITg01O5j2=Tg01P5R0j2@Tg00;ij2DTg00[Gj1>Tg00RWj2QTg00Y=j3PTg00Yaj2^Tg00=Mj1]Tg00=mj1\Tg00>Mj2OTg00E@j1[Tg00E^j4ZTg00>kj1YTg00?Ij1XTg00@Wj2MTg00@4j2KTg00Pmj3RTg01ELj3GTg00Aej1vTg00BGj2tTg00Bij2sTg00Coj3rTg00DNj4pTg017;j2BTg01Eoj3TTg00\@j6ETg01A3j1nTg0150j2mTg014Mj3iTg01H2j3hTg00A:j4JTg01Lfj4fTg00iIj6eTg01S4j2gTg01PXj2dTg01T1j1jTg01g@j2kTg016^j1cTg006?j2lTg00HHj7VTg00`nj6aTg00Hlj6`Tg00J4j8qTg00IPj7_Tf1R1f0R2#c'Hp=7g009VR3/l2p=6f2R4g00L4R5g00LSR6P6g00M3R7g00K6R8P1g00PFP2CJg00MSR9FVp=8P1P5P6P6P7P2Eap=<P1P5P6P6P7P2E`p=Wf3R:P5P6P6P7P4P1P2Gqp=5P8P1g00N_P2CJp=LP1P5P6P6P7P2P9FVp=CP4P5P6P6P7P1P2F_p=Ag0091R5#;R9#;#;#;#;#;R;#UR<#bR=P8g00OFR>P814<1R?%F9R@%?5#?#?#?#?RA#FRB'SRC'2P?%F;R;,S@RD,:?n0100000020000P>P=1221%F5,H<RE1H<3RFn010000002000014<4RG/NCS00111CRH'2,7<53=X>81u<1%6?%o<,0?'9P811GC/IDP>P=P>P814<:RI/2CRJPI1:IDn0100000020000/24PEPFn0100000020000114CRK,22,7<53=X>81=GC10GC12GC'@PJP>P0f4RJ,4</0CP>P=P>P8P1f6RL,4<RM1:MDRNn0100000020000f5RO'2PEPFn010000002000011MCRP/IDS0111OC'2,7<53=P114<O/0CS02P8PPP>P=f7RQ,4<RR/2LRSPEPFn010000002000011LC,22,7<S0353=X>81=MO10MO12MO'@PSP>P0f8RS,4<S04/0QP>P=P1PEPFn0100000020000S05f:RM,4</1CRTf9RU/1CRV'2RW,7<53=P114<URU/0SRX1=TVS0610TV/@WS07f;RW,4</1CRY11MCRM'2S08P>P0f<RZ,4</1CR[11WCR\'0S0917<1R]93=ES0:P1f=,4<R^/1CR_11ZCRZ'0R`g00OfRa,7<Rb,D=S0;WFP2O1%>`Rcg00jk,7<Rd93=ES0<1Q@BRe103@Rf%6B103C[Rg[Rh%6@Rig00b9RjAP@B1UW=RB%6C\j^=iRk1Q@;Rl%6;103D[Rm\fRnAP@;1VjX=iR;%6D\j^=iRiP1g00bU1^3@'DPfeRfO1RjPmPJPfO1RfPgp-0Rog00N3Rp#]Rq%\pRpP81O84P1%[8S0=CZRr%Y8Rs%X8Rt1M85Ru1K8@R@%UA5R8RA5G8Rv1M89R9=G8ARw58tS0>,<t%v6R6PtA8tu9RxP61WtJRyC5C51tt7R7P2P41D>a1s24=3>adAr831CpRab4b6b7X08X88W1112CRz/0HR{g00c;R|[1014R}PJ[[^08^88^1oP2P|fDfE,4<PQPWO5R~b3b5b2b;b2b<b5'BWAP2O1n10210010100021010211103b9b:W@P2O1%>XQ06Q07Q08P>P0Q09A3=F]S09P1A3=FbRbPePhPBPkPlPnP;PiPjPmPfPgPqPpPrPsPtQ0>P6Pt1<txP6PyC5C5P7Pab4b6b7X08X88X1oP|\}PJ[\{^08^88^1oP~b3b5b2b;b2b<b5'BX@`P2O11D=dS0>XBcP2O1n10210010100021110210103b9b:WAP2O1n10210010100021110211103b9b:Q01PqPp1O81RcPsPtA8tuARAP6Pt1K83Rd/Lu,CtR`1Wt:R:5AtP61Ldv,CtAR8@<R@98tv5AtC5C5P7Pab4b6b7X08X1o102CR{%61R}/94%6K10KD'9[[^08^1oP210RDPRP1POO4b39TPDEEW?P2O1Q02#>P8%n5R5/mDRx,1PR]/IDRXP>P=1:RD/2LRLPEPFn0100000020000Q0353=X>8RFP8P]PF1=NO10NO12NO'@PLP>P0Q04/:D/0QQ0511TxRT/2VRL,7<53=P11:UD/0SRS1=TVRU10TV/@LRL11Yx/2MRMP>P011[x/0\R\Q0:P111_x/0ZRZQ0;W@P2O1%>ZR_Q0<PePhPBPkPlPnP;PiPjPmPfPgPqPpPrPsPt1K85=i8@9G8vRv=8twRw,<tP6PtAh8u@=8t9R9P6PyC5C5P7Pab4b6b7X08X88X1o11zx/0HRHP|[1:1D/04R[PJ[[^08^88^1oP~b3b5b2b;b2b<b5'BWBP2O1n10210010100021010211103b9b:W?P2O1%>SPUPLPMP>P0P\Q09P1PePhPBPkPlPnP;PiPjPmPfPgPqPpPrPsPtPwP6Pt1<t9P6PyC5C5P7Pab4b6b7X08X88X1oP|\[PJ[\H^08^88^1oP~b3b5b2b;b2b<b5,BbX?ZP2O1Q0>XG_P2O1n10210010100021110210103b9b:WBP2O1n10210010100021110211103b9b:PXPePhPBPkPlPnP;PiPjPmPfPgPqPpPcPsPt1<tAP6PtA8tu@Ru9At:P61Ldv,CtA8tv@5AtC5C5P7Pab4b6b7X08X1oP|\{101DR{,9411KxRx#610xD'9[[^08^1oP2%6^P^PQPWO4b3b<b;bDb;b2b<9T]DEEQ01PPP5PDPqPpQ0=PsP8P@g00aRPdCJ,Ct,<tP7Pab4b6b7A38D3P|[P2b3CfEeWAP2O1n10210010100021110211103b9b:Q00PqPpPcPsPtAAt`uRuP6PuC5P7Pab4b6b7X08%62102D'919}{[^08P2PIP1O2b3,gGEEbC1d<1%j1EE1k121N?C/2z,7<53=eXE8WHo"). Qed.

(* [comment removed for export] *)
Lemma zb_b2z_if : forall b, Z.b2z b = (if b then 1 else 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bp;1p;3p;2g016^j13Tg00:Pj12Tg00CUj31Tg00;ij20Tg00OFR0P0g00K6R1f0R2#3P0P1P2g0091#2R0g009VR3n011000002000031P210101013n0110000020000W0o"). Qed.
Lemma zb_b2z_nonzero : forall b, Z.b2z b <> 0%Z <-> b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01Hh13Heqh22H0h32H1h41eh51bi001bi011zp;1p;3p;2p;4p;6g016^j12Tg00[Gj13Tg00CUj30Tg00Xdj24Tg00:Pj1:Tg00;ij28Tg00hMj49Tg00iIj66Tg017;j27Tg00GHj45Tg00K6R0f0R1g009VR230p=1g00OFR3P3%21#1#3g00OfR49031'4P1g0091#:R5#1R6g00c;R7[R8A0344R9[P8\91834X08P0P5P2P1C9A0025P0P2P0p-0R8P1g00b9R:P7P7n011010003001000010000X40g018fR;P5P1E6P71771R5b3b1X26X09C5%24#1#3/49eA0022R9P7[R6g00jkR<=034R=[P6\=1802P9f1R2P1O1,7=b1X06P2P=P3P<P3P8P1P7P:n0110000020000X43P;P4P1E6P7P5b3b1X29X0=C5%2<#1#3/4=en0110000020000W5o"). Qed.
Lemma zb_b2z_zero : forall b, Z.b2z b = 0%Z <-> b = false.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01Hh12H0h23Heqh31eh41bi001bi011zp;1p;3p;2p;4p;6g016^j13Tg00CUj30Tg00Xdj22Tg00:Pj19Tg00hMj48Tg00iIj67Tg017;j24Tg00GHj45Tg00;ij26Tg00K6R0f0R1g009VR230p=1g00OFR3P3%31#1g00jkR49031'2P1g0091#9R5#1R6g00OfR7=034R8[P6\8P0P5P2P1C8A0025P0P2P0p-0R9P1g00b9R:g00c;R;P;n011010003001000010000X30g018fR<P5P1E7P;1481b1b2X06P1P8P3P7P3P9P1P:P;n0110000020000X33P<P4P1E7P;1461b1b2X08C5%37#1/28eA0022R8A0344R7[P8\71634X081602X07C5%34#1/27en0110000020000W4o"). Qed.
Lemma zb_b2z_eqb0 : forall b, (Z.b2z b =? 0)%Z = negb b.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bp;1p;2p;3g016^j14Tg01@5j23Tg01h8j10Tg00CUj32Tg00;ij21Tg00OFR0P0f0R1#4g009V'3%01520P1g00Of#0,10g00jk#0,10n0110000020000W0o"). Qed.
Lemma zb_b2z_range : forall b, (0 <= Z.b2z b <= 1)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01Hh12H0h23Heqh31eh41bi001bi011cp;1p;2p;3p;6p;4g016^j12Tg006?j20Tg00:Pj16Tg007`j21Tg00CUj35Tg00iIj64Tg017;j27Tg00GHj43Tg00OFR0P0g009VR0f0R1#2R2'0g0091#6R3,02'1P1g00bUR2g017ZR4g018@R535R6g00c;R7[R8g019BR9=525R:P7[R;P1P6P2P4P2p-0R4P1P7g00b9R<P7n011010003000000X32g018fR=P5P1E4P71771R>b1b2X06R6P1P:P2P9P2P4P1P<P7P7n011010003000000X32P=P5P1E4P7P>b1b2X0:R:C3g00Of#2R>,0010>3'1eP;P8P:P6C3g00jk#2R6,001063'1en0110000020000W4o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zb_land_mask : forall x k, (0 <= k)%Z -> Z.land x (2^k - 1) = (x mod 2^k)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__x1h11zh27__arithh34__ffh48__varmaph55__with61kh71xp;2p;1p;3p;6p;4p;7p;8g006?j22Tg01hVj1NTg00WGj20Tg003<j1;Tg00:Pj17Tg00:nj24Tg01GUj23Tg00CUj31Tg01i4j16Tg00;ij25Tg01iRj2:Tg01j2j18Tg00\@j69Tg00R7j2MTg00=Mj1LTg00=mj1KTg00>Mj2FTg00>kj1ETg00?Ij1CTg00@4j2@Tg00@Wj2ATg00A:j4BTg00HHj7?Tg00Aej1>Tg00J4j8DTg00BGj2=Tg00Bij2GTg00Coj3HTg00DNj4<Tg01jVj3ITg00iIj6JTg00K6R0g009VR1f0R2'2R3P0f2R4f1R5#N'0R6f3R7g0091R8#;#7R9/44%78R:'3'0R;=102X10P01495R9%62,07910;X10%69,04,501::5%85E9139:,04=106e1M49g00N3R9#L%K91F05%E0%C0R9g00L4R6g00LSR:P:g00M3R;P9P6P:P:P;P01@01g00N_1A08CBg00MSF?R8%>:P8GD1=9;P2P4g00OFR;g00OfR9'51G24=1;9dAH015C<b3b4b5X001215\3^00P2P4P5O2b29I45EJUX60W7o"). Qed.
Lemma zb_land_mask_l : forall x k, (0 <= k)%Z -> Z.land (2^k - 1) x = (x mod 2^k)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01kh11xh21zp;2p;1p;3p;6g006?j2:Tg003<j19Tg00:Pj11Tg00:nj22Tg01GUj28Tg00WGj20Tg00R7j27Tg00CUj34Tg01k9j35Tg00dRj26Tg00\@j63Tg00K6R0g009Vf0R1':P0f2R2g0091R3#9#1R4f1R5'2%13'8R3'0f31242'79401X20A525110321632E3UX00W1o"). Qed.

Lemma zb_shiftl_mul : forall x k, (0 <= k)%Z -> Z.shiftl x k = (x * 2^k)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01kh11xp;2p;3g006?j21Tg01l6j30Tg00K6R0g009Vf0R1'1f2f1;01UX00W1o"). Qed.
Lemma zb_shiftr_div : forall x k, (0 <= k)%Z -> Z.shiftr x k = (x / 2^k)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01kh11xp;2p;3g006?j21Tg01l_j30Tg00K6R0g009Vf0R1'1f2f1;01UX00W1o"). Qed.

(* [comment removed for export] *)
Lemma zb_shl_shr : forall x k, (0 <= x)%Z -> (0 < k < 64)%Z ->
  Z.shiftr ((Z.shiftl x k) mod 2^64) k = (x mod 2^(64 - k))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__x1h14__p1h27__arithh34__ffh48__varmaph55__with61zh72Hah86__sat1h94__x2h:6__sat0h;1Hh<2Hkh=2Hxh>1kh?1xp;1p;2p;3p;4p;8p;5p;6p;7g003<j17Tg00:Pj1ETg007Dj2:Tg007`j2;Tg00:nj20j1jTg0150j28Tg00R7j29Tg0119j2FTg01GUj24Tg011Yj2@Tg01CBj2NTg00;ij2BTg00=Mj1]Tg00=mj1[Tg00>Mj2LTg00>kj1YTg00?Ij1WTg00@4j2ITg00@Wj2HTg01H2j3GTg01ELj3VTg00A:j4?Tg00BGj2UTg00Bij2TTg00CUj3ATg00Coj3STg00DNj4RTg01mHj8QTg00Aej1PTg01mej5OTg00iIj6MTg00RWj2JTg00Y=j3KTg00Yaj2iTg00E@j1hTg00E^j4gTg00ZBj1fTg00`nj6eTg01nHj3bTg01nij5\Tg00\@j6CTg01l_j3^Tg01iRj2_Tg01l6j3`Tg006?j2aTg00HHj7ZTg00Hlj6cTg00IPj7dTg00J4j8XTg009VR0f0R1'ap=31:01p=1g00K6R2f1R3;A1p=6P3g00L4R4g00LSR5P5g00M3R6P1g00MSFZp=2P3P4P5P5P6P1Ecp=DP2P3g00PFP1C?p=<f2R7P4P5P5P6P3P1Fdp=>P2P3g00N_P1C?p==f3R8P4P5P5P6P7P3P1GXp=5%33R9%13R:g0091R;#7R<#7#7#7#7#7#ER=,:3';P2%E<R</07R>,88R?10<=R@,91/F8f4RA14=8RB,0<RC'9RD'6X62P219?@R?/@>161DX62P214=7RE/N7RF,0<161@X62P2P2%j<RGPGPFP=P2\2/BGg00N3RG#]RF%[GRG1L23RH%Y2RI%W2RJP21I2=RK1H2;RL5G2RM=V2Lg00aRRNPKC?'21UJ6ROP1P7g00OFRPg00OfRQ'B1T17=APQdAS203CRRQb3b4b5X0214=1/N1/6=^02P1P8O1b2GQ10<E/8>R>P<PEP7p-0REPFPGPHPIPJ1DJ8RP1<LK,2J5>J%P5RR1I20RS/=M,2JC5POPQb3b4b5X02W11:1=,;314=3#3RM[^02^1EP1%18P8P3O3b2PFPGPHPIPJ1<SL,2JRH=>JPPR1=SL,2JC5POPQb3b4b5X02X1E%11/;3P9[^02^1EP11:8=P8P3O3b2RPDOEM16>@P210<8R>,8CRTf5RU10<ARV'8/91/@V14=ARW,0<,9URX'6X62P218D>1@1V/6XX621J<8%1<RX%3A10<U#1[[%3<RVg00b9RYf6RZ=K<3UW710<ZR[#3\Y^7VP3g00bU1i0<'BPXeO1R\%3U%1[[PFPGP2%h2P31L27CgR[PIPJPJ%f;,H2R;,=S,2JPRPHC5PRPJ1<S;,2J1DJAR]5>JPRPJP4P5P5P6P2PLPNPSC?,2JEeRNC5C5POPQb3b4b5X02X92X1EP:\9%17/;8AA270g00c;[R0[[^02^92^1EP1f7R9/:=P910<9P3PUO5b2b8b:b8RL9bD>18A>/9TPAPCP>1J<B%3W14=URW,0<#1[\X14=ZRZ=K<3VYX7V10<ZRZ#3\Y^7VP\%3W%1Z[PFPGP[PIPJPJAG2K;,=S,2JPRPHC5PRPJ1<;K,2J9>J]PRPNC5C5POPQb3b4b5X02X92X1EP:\M1:7=,;8P0[[^02^92^1EP1%19P914=9,0<P3PUO5b2b8b:b8PLD\ECP@P1EMb;1F?7A^?7PEC1_87A`87PECW<W=X>2X?2o"). Qed.
(* [comment removed for export] *)
Lemma zb_shr_shl : forall x k, (0 <= x)%Z -> (0 <= k)%Z ->
  Z.shiftl (Z.shiftr x k) k = (x - x mod 2^k)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with62Hah76__sat1h84__x3h94__x4h:1zh;1Hh<2Hkh=2Hxh>6__sat0h?1kh@1xp;2p;1p;3p;4p;6p;7p;8g0119j2fTg003<j1=Tg00:Pj1HTg00:nj24Tg0150j23Tg00R7j2<Tg01GUj2>Tg00CUj30Tg011Yj2BTg00RWj2GTg007Dj29Tg00Y=j3ETg00Yaj2eTg00;ij2ATg00=Mj1YTg00=mj1XTg00E@j1VTg00>Mj28Tg00E^j4;Tg00>kj1UTg00?Ij1TTg00@4j2LTg00ZBj1KTg00@Wj26Tg00A:j47Tg00Aej1JTg00`nj6ITg00BGj2MTg00Bij2NTg00Coj3OTg00DNj4FTg01oRj3PTg01CBj2?Tg01A3j1QTg01AQj2RTg00S?j1STg00S^j2DTg01B2j3dTg00TGj3cTg00U0j2^Tg00U\j3]Tg014Mj3CTg01ELj3ZTg01H2j3[Tg01l_j3\Tg00\@j6@Tg01iRj2WTg01l6j3_Tg006?j2`Tg00HHj7aTg00J4j8bTg009VR0f0R1'`p=1f1R2g00L4R3g00LSR4P4g00M3R5P1g00MSFap=2f3R6P3P4P4P5f2R7P2P1Gbp=5g00K6R8P2g00aRP1C7p=:%12R9P81f67R:g0091R;#=R<#HR=/47R>'3f4R?14=6R@,<?'>RA9081X:8P81B6>RB131@=08AX:81G=7190=RA%1614=?R@,90[[%1=RCg00b9RDf5RE=E=2UW614=ERF#1\D^6CP2g00bU1e0='APAeO1%1?190F[g00N3RF#YRA%XFRCP8%V8RDP21887C;%U8RG%T8RHPHP81L80RIg00N_RJ%K;,68RKC7,2HRL%J4RMP8PIg00PF168;RNC7,2HC5PMPHPLPMPHP3P4P4P51:NI,2HEIC5C51MH5R5P1P7g00OFR4g00OfR3'A1N17=043dAO802CFR3b3b4b5X08X181902\9%17A0870g00c;[[[^08^18P1f6R014=0P2P?O4b2b7b>b79P6>13>B1<6>'?9086%Q;,R8g00V<R;#S,D85d81D8;5c8g00V['^=]FAPCP8P8188?P7PDC;P21886C;PGPH168<RD=C8N%=<,68R<5Z8,:K,2HPMAC8NDA[8K<':,2HC5P5P3b3b4b5X08X18X88X981321/?6908713271>6?508[^08^18^88^98P11<E@PEP@1BE@P2O5b2b;P:PAPC1882PGPHP8PIPJPNC7,2HRHPMPHC5P5P3b3b4b5X08%11P9[^08P1P6P2O2b2R29\67E@1W:7A_:72E@X<9W=X?8X@8o"). Qed.

Lemma zb_lor_eq0 : forall a b, (Z.lor a b = 0)%Z <-> (a = 0 /\ b = 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01ah11bp;2g0203j20Tg00K6R0f1f0'0X10W0o"). Qed.
Lemma zb_lor_eqb0 : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (Z.lor a b =? 0)%Z = ((a =? 0) && (b =? 0))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h05lemmah11Bh22Hah32Hbh41ah51bp;2p;3p;9p;4p;6p;;p;7g006?j2FTg00n@j2:Tg01@5j22Tg00eVj27Tg007`R0j23Tg00XdR1j24Tg01Q`j3?Tg01Y3j2=Tg01J_j2<Tg01Kll9;Tg020Yj26Tg01]Dj3ETg01^:j49Tg01^mR2j6DTg01YTj4CTg0219l;BTg0203j2@Tg01RRj3ATg00CUj38Tg01UXj7>Tg00OFf0R3g00Of38p=0p-0R4P1f4R5f3R6f2R7f1R8P3F>p=5g00K6R9g009VR:783p=11F:8R81:67R;/2:R<126:R=127:R>'7R?%0?%0=R?%0>R@'3'4g01WD9?41RA1:56RB/2:#0RC125:RD/7=#0%0DRD/3?REP3D5W01==>%0<%1;'4P4P1g01VSPC%1BRBP3PEPE1<4EM9;W016;:%16R;,4?PAPBPE%15R5/3?REPDP5P3P?P?P4P1g01bL9E41RDP?C9EDD5W0166:%17,4@PAPBPE135;P4P4^14P1P4P4P1P1CCP0P2P5P4P1PDP5C9P?P;P3M;BD5W0167:1@67O2O2O2O23AX38W2X59X49o"). Qed.
Lemma zb_lxor_eq0 : forall a b, (Z.lxor a b = 0)%Z <-> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01ah11bp;2g0224j20Tg00K6R0f1f0'0X10W0o"). Qed.
Lemma zb_lxor_eqb0 : forall a b, (Z.lxor a b =? 0)%Z = (a =? b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h05lemmah11ah21bp;2p;3p;9p;7g00o[j24Tg01@5j22Tg00CUj30Tg00XdR0j25Tg01J_j2;Tg01Kll9:Tg020Yj23Tg01Q`j38Tg01UXj77Tg0224j26Tg01RRj39Tg00OFf0R1g00Of30p=1g00K6R2f1R3/41R4g009VR5'2R61231R7%16A0245'5p-0R6P0g01VSf2R8/43R9/25#1A0295R9P11283#1R:P:1;6:M9:W01345%17A0231'5P6P0g01WD9860P9P:A0283P1F7W013311631O2O239X22W1o"). Qed.
Lemma zb_land_lor_distr_l : forall a b m, Z.land (Z.lor a b) m = Z.lor (Z.land a m) (Z.land b m).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01ah11bh21mp;3g022[j30Tg00K6R0f2f1f030X20X10W0o"). Qed.

(* [comment removed for export] *)
Lemma zb_lxor_ones : forall x, (0 <= x < 2^64)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with51bh64__p1h71zh81Hh92H0h:2Hxh;2Hah<6__sat2h=4__x2h>1ah?1xh@1EhA2H1hB2HihC6__sat1hD1ei001ehE1ihF1ni011nhG1ohH1si021sp&0p;1p;2p;3p;4p;6p;8p;5p;7g003<j1CTg00:Pj1OTg00:nj2QTg007Dj20Tg007`R0j29Tg023Ej1xTg023lj1ATg01CBj2=Tg024Jj1DTg01hVj1]Tg00WGj2LTg00o[j2TTg00e5j21Tg024gj2BTg00eVj27Tg01h8j1ITg00f4j2wTg006?j2?Tg00XJR1j2pTg00;ij2NTg01>nj1iTg025Ej1gTg00=Mj1eTg00=mj1dTg00>Mj2VTg00>kj1bTg00?Ij1aTg00@Wj2UTg00@4j2KTg00Aej1\Tg00BGj2[Tg00Bik20DTg00CUj3@Tg00Cok30CTg00DNk40BTg025dk30ATg00\@j6:k80;Tg00Zgk20>Tg00[Gj1RTg00[`R2k20=Tg00gDk10<Tg00Hlk605Tg00]@j1JTg00]^k304Tg00RWk203Tg00Y=k302Tg00Yak201Tg003aj1vTg00Pmj3uTg00Fcj5tTg00gdj4rTg00hij1oTg026Kj1nTg026kj3mTg027Sj3lTg00iej3kTg0286j3jTg00jHj3qTg00R7j2>Tg00E@j1sTg01jVj3hTg00iIj6PTg01GUj25Tg01i4j1fTg01A3j1yTg01AQj2zTg00S?j1{Tg00S^j2XTg01B2j3|Tg00TGj3}Tg00U0j2~Tg00U\k300Tg00E^j4cTg01ELj3YTg028Yj2ZTg01H2j3MTg0150k206Tg014Mk307Tg01Eok308Tg01Lfk409Tg01iRk20:Tg01j2j1`Tg00A:j4STg00HHj7_Tg00IPj7^Tg00J4k80?Tg00`nk60@Tg009VR3f0R4'?p=8g00K6R5f1R6;@4p=2g00OFR7?@64p=6P7f4R8f3R9f2R:P6P4E:p=<P5P6g00PFP4CSp=HP6g00L4R;g00LSR<P<g00M3R=P4g00MSF_p=3P5P6g00N_P4CSp=GP:P;P<P<P=P6P4F^p=;P9P;P<P<P=P:P6P4L0?p=4A@543p=FP5P6g00aRP4CSp=EP6P;P<P<P=P4J0@p=W%84R>g0091R?#CR@#ORA%C@#C#C#C#CRB#ORC'QRD,04RE'9RF%x6%A6,=6%O?RG#DRH'2RIP5%A:RJ%]CRK'LRL1T9KRM/24X751T:KRN1186RO11K6RP'Bf5RQ#A/LK/1:,64X57%A8RR/16RS/7P11Q:11K:RP'BRT/64X57%IO174P,6TX571w6C106C1?C6RT'pP110:CR11?C:f6RP/19RO11K9RU'B%IO/7U'6P4109CP7g00OfRUf8RO/1QRV/B4%IVRW/74'6X57RXf7RY/18RZ#IR[17WU,64X57P[16W4X571N7[17[U%i[D<1BZU%gZD<11K8R\g00N3R]#eR^%d]R_1V56R`%b5Ra%a5Rb1U5?Rc1K5CRd'H,3bRe%\<RfPb1K53Rg/Gc,3bRhPfA;bheC4C41[b=ReP4P:1N7U20D4:=@7UdB0C536H0BRUb2b3b4X05104C%86Ri%8:/91[[^05P4PQP6P8O3b1:0AC8E:W9P4O11?C9P7g00jkR1PXPZ17W1,64X57P7P116V4X5720>Y3%FYRV%RV+0=P2%FOR2%R2f9R2/1P=@71P4%F2RPP5P3f:RV,1:=@71^8I^:FX?51?33103DRI'9%A3,=3/2H&0<2W8W:PVP4P2POL0;WDP4O1%RPPVPYp-0RPP^P_P`PaPbPbP;P<P<P=P9J05R=9;bhR<PfPhC4PePUb2b3b4X05W619>6Pi[^05^6PP4f;R;/0DP;PVO3b1%JVPCPY1036RYP01QA6,0:%J9/0:[R0%J:/061QA:,09RV[%J8/09\VB04:64P6n2001000000120000000UX55X>5P0\Y^55^>5P4P;PC203AC103ARY%8CR0PI[RI[%8ARVg00b9R2B02AC6UW;%8D\2^;VP6g00bU2013A'NPYeO1PIP^P_P`PaPb1Ecg,3b,WbPfPbP<Pf1Hgc,3bC4C4PePUb2b3b4X05X6P%F4g00c;R<[19i:103:[[^05^6PP4f?R3/0DP3PQf>O4b1b<bCb<P^P_P`PaPb1K5A%vB5u5RB,Hc,3bRA9;b=PfPAC4PePUb2b3b4X05X6P196E106D[^05^6PP4f<RP#8PPP;O3b1O4bAP^P_P`PaPb1Gdc,3bR;PfP;C4PePUb2b3b4X051?C4RPPT[^05P4POP8O2b1DtCrWFP4O1n200110200021010011101bH17[1%o[E:1BZ1%nZD<P\P^P_P`PaPbP;Pf1Ggd,3bRd=;b;C4PePUb2b3b4X05190T\P^05P4PQP6O2b19mC8E:W9P4O1n200100000021100011000bGPSP^P_P`PaPbPhPfPhC4PePUb2b3b4X05Pi\>^05P4P:P6O2b19l86D<1LRK/16AkRK6D<1T8K/16Aj8K6D<XB>XE57qL1>JDRLP^P_%s5R>PaPdPePUb2b3b4P0P4b19hJCEP12NLP5%A9RL/>DRN15K8,24X75P5PD1>RD%f4/58'2X75%y?,z5g00V<R?#{,X55|51X5?5}5g00V['~>00]^P_P51V5:P6P>CcPaPb1U5@R@9Y5c1K5GR],Z5'E,3bPf1Z5c=M5]R?/E@,3bC4PePUb2b3b4X05X=51=46/2H%D6/5GR6/2:[^05^=5P4PRP8P:O3b1%D9/5G/2LP5%D8/5GRL1>4D15DGR:/5QRH'2X75P5206GDR@,=LRJ/>DR0124HX75RHP5PJPHP^P_P`PaB075]B9Y5?R?AM5B]=M5c'E,3bPePUb2b3b4X05%D4/5G/=@15:4'2^05P4PQO1b1P0P^P_P`PaPbA;bhAPf1Gg?,3b1H?B,3b5;bC4PePUb2b3b4X051=6@R@#810@D'9\F^05P4PQP8O2b1:08JDE:1>LDPLPGPDP^P_P>Pa1EBg,3b,WbPePUb2b3b4%FDP<[P4b1H09EPPRP4EPb920:GC%`CE:15K9,2NePMP4E:b@b8W:X?5o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h07__arithh14__ffh28__varmaph35__with41eh51zp;1p;2p;3p;4p;7p;6g003<j12Tg00:Pj13Tg00:nj2>Tg00R7j27Tg00ZBj10Tg00WGj24Tg00CUj36Tg01hVj18Tg00=Mj19Tg00=mj1:Tg00E@j1OTg00>kj1NTg00?Ij1MTg00@4j25Tg00A:j4HTg00HHj7ETg00BGj2@Tg00;ij2ATg00Bij2BTg00Coj3=Tg00DNj4CTg006?j2DTg01jVj3<Tg00hMj4FTg003aj1GTg01;Hj2;Tg005Uj2JTg029<j1KTg00\@j6LTf0R0#0#0p=I%00#0#0#0p=?%00#0#0#0#0#0#0#0p=1g00K6R1P1g0091R2#2R3#3%23#2#2#2#2R3#3R4'>,70R5f1R6%02#I#?#1#1#1#1#1#1#1#3'49610X51P1%84,40P5g00N3R5#9%:5%O1%N1%M1R5g00L4g00LSR2P2g00M3R2P1g009VR7,51g00N_1514CHg00MSFE1@52P0f2R2g00OFR5g00OfR8'A1B02=658dA=176CCb1b2b31D74P0b09<04CF%G3R31;30'J%K0ELW4o"). Qed.
Lemma Z_to_bv_land64 : forall e, Z_to_bv 64 (Z.land e 18446744073709551615) = Z_to_bv 64 e.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01eh11zp;1p;2p;3p;6g003<j12Tg003aj1>Tg01;Hj23Tg005Uj24Tg004?j1=Tg00CUj3:Tg02:=j17Tg00ZBj10Tg00:Pj18Tg00WGj29Tg02;@j1<Tg00iIj6;Tf0R0#0#0p=5%00#0#0#0p=6%00#0#0#0#0#0#0#0p=1g00K6R1P1g0091R2#2#2#2#2#2#2#>R31330R4'4%=3f1,337:4X11%74%02#5#6#1#1#1#1#1#1#1#8,90%<0E;W0o"). Qed.
Lemma zb_shl_shr_land : forall x k, (0 <= x)%Z -> (0 < k < 64)%Z ->
  Z.shiftr (Z.land (Z.shiftl x k) 18446744073709551615) k = Z.land x (2^(64 - k) - 1).
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with54__p1h61zh72Hkh82Hxh91kh:1xp;2p;1p;3p;6p;4p;7p;8g006?j24Tg007Dj21Tg003<j10Tg00:Pj18Tg007`j2<Tg01iRj2RTg00:nj26Tg00R7j2>Tg0119j2=Tg01GUj23Tg00WGj29Tg00CUj3:Tg00;ij2BTg00=Mj1YTg00=mj1VTg00>Mj2UTg00>kj1QTg00?Ij1OTg00Hlj6NTg00@Wj2LTg00@4j2@Tg00A:j45Tg00Aej1ITg01H2j3HTg00BGj2GTg00Bij2JTg00Coj3KTg00DNj4FTg01k9j3ETg00iIj6MTg02<Bj4DTg00\@j6ATg01hVj1PTg00E@j1CTg01jVj3STg00HHj7TTg00IPj7XTg00J4j8WTf1R0g00L4R1g00LSR2P2g00M3R3f0R4g00MSFTp=2f2R5P1P2P2P3P0P4FXp=?g00K6R6P0g00N_P4C5p=7f3R7P1P2P2P3P5P0P4GWp=;g009VR8/40R91180g0091R:#0R;#0#0#0#0#0#8R<,10'<R=P61R75R>%8;R;/6<'>R?1=47f4R@13<7,6;%8:RA'3'9RB5:6X66P613<5RC,6;R;,>7RDA:64BX66RBP613;A,97R;PB1B6;PDp-0RDg00N3R;#YRB%V;R;1U60RA%Q6RE%O6RFPFP1P2P2P3P7ENP61L6:R:g00PFR11@6<RGC5,2FRH5?F%I2R21@68RIAH6G:'7,2FC;1GF3R3P4P5g00OFRJg00OfRK'B1J45=:JKdAK680CFRKb2b3b4X06W5114<RJ,<013<0,48[^06^5DP41187P7P0O3b19E7CEM1=?5P7P5PBP;PAPEPF17I:,2FR?P2P?C;P3PKb2b3b4X061484P9[^06P4P@P5O2b1PBP;PAPEPFP6PIP1P:C5,2F=?FHRHP2PHC;P3PKb2b3b4X061184/<JP=[^06P4P7P0O2b1CDEA%P<,9>PBP;%C6PE17IG,2FP3PKb2b3b4148<P4b19S><EAW7W8X96X:6o"). Qed.

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
Ltac nc_delta_zxb := lazymatch goal with |- ?G => let G' := eval cbv delta [zxb] in G in lazymatch G' with G => idtac | _ => change_no_check G' end end.
Ltac zsimp :=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  nc_delta_zxb;
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
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bp;1p;2p;3g003<j10Tg003aj17Tg016^j13Tg01;Hj21Tg02==j36Tg01h8j15Tg00CUj34Tg00;ij22Tg00OFR0P0g0091#0#0#0#0#0#0#7R1f0R2#3,11g009V,1136#5=402P2g00Of,20g00jk,20n0110000020000W0o"). Qed.
Lemma b2z_word_eqz : forall b, bv_eqb (Z_to_bv 64 (Z.b2z b)) (Z_to_bv 64 0) = negb b.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h01bi001bp;1p;2p;3g003<j10Tg003aj17Tg016^j14Tg01;Hj22Tg02==j36Tg01h8j11Tg00CUj35Tg00;ij23Tg00OFR0P0g0091#0#0#0#0#0#0#7R1f0R2#4,21g009V,2136%12550P2g00Of#1,30g00jk#1,30n0110000020000W0o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "p'0h04__p1h14__x1h21bi001bh31ri011rh47__arithh54__ffh68__varmaph75__with81li021lh91ni031nh:2Hxh;1ei041eh<2n0h=1xp;2p;1p;3p;4p;6p;7p;8g006?j2=Tg02=jj2QTg01@5j2<Tg01P5R0j2?Tg01h8j15Tg01OXj2:Tg00CUj30Tg01O5j2DTg007Dj22Tg00=Mj1CTg00=mj1ATg00>Mj2@Tg00>kj1PTg00?Ij1OTg00@4j2NTg00@Wj2KTg00A:j46Tg00Aej1JTg00Hlj6ITg00BGj2FTg00;ij29Tg00Bij2ETg00Coj3GTg00DNj4HTg017;j28Tg00[Gj1;Tg00HHj7BTg00J4j8LTg00`nj6MTg00K6R1f0R2g009VR330p=7f1R4g00L4R5g00LSR6P6g00M3R7P2g00MSFBp=4f3R8P5P6P6P7f2R9P4P2GLp=1g00OFR:g00OfR;702p=3P4P5P6P6P7P2EMp=>1=321Q43%74R<1<43'?1<93P:P0%78%54f5R=,:3R>50:P4f4R?#7R@1D3=RA123=/?>R>f6,:3RBP:P0f7,23RC%5;RD=0:4P4f8,23REg00jkRF=0:;p-0RGg00N3RH#CRI%AHRH1@14RJ%P1RK%O1RLP11N13RMg00PFg0091,K1RNC6,4LRO%J6RPPLP1PNg00aRPMC6,4LRQPPPLP5P6P6P7P8EIR6C1C11FL7R7P2P919:;R51E29#3dAG134CHRRb5b6b7X11W01232RSP8\<[^11^0GP2g00c;R8f:RTP4P=O4b4'8%3DeW8P2O1%;ERU19:FA0:DFeW9P2O1n10210010100021010210103b2b3W;P2O1%;@PAP>PBP:P0PC%5FRC=0:4P4P5%3CeX8EP2O1A0:;FPIPHPJPKPL1>LOPPPL1>LQPPPLP1PMg00N_PNC6,4LPPP6C1C1C1P7PRb5b6b7X11X0GP8\SP8\<1=39P?[[[^11^0GP2P8PTP4P=f9O5b4'8A0:CFeX<UP2O1n10210010100021010210103b2b3W9P2O1n10210010100021010410103b2b3W:X=1o"). Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_eqm : forall e1 e2, (e1 mod 2^64 = e2 mod 2^64)%Z -> Z_to_bv 64 e1 = Z_to_bv 64 e2.
Proof.
ltac2:(KReplay.run1 (kr_t_ZBridge ()) [] "h01bh11Hh22e1h32e2h41zp;1p;2p;3p;6g003<j11Tg00:Pj16Tg00:nj29Tg00R7j22Tg00CUj33Tg003aj1;Tg004?j1:Tg01;Hj20Tg00;ij28Tg00\@j67Tg02>Lj14Tg00iIj65Tg00K6R0f1R1g0091#1R2#6%12#1#1#1#1R2#6'9R3'2R4f0R5/23530%;2R2#:R6f2R7/23R8,02R91027R:9365X06P61024R;f3/23,02=365X06P0P41025=369X40186;P8P5E71021%41E5P:%47E5W1X30W2o"). Qed.

Ltac word_eq_tac :=
  first [ exact eq_refl
        | f_equal; lia
        | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
        | apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ].
