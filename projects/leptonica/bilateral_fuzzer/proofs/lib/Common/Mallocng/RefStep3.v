(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib RefMemcpyLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RefStep3 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00I59OSSVerify5KrLib6Common9PureModel7md_pure00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith8Zbitwise1Z<add_lor_landC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC46Stdlib6ZArith:ZArith_dec8Z_lt_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z?shiftl_spec_lowK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib6Common8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib6Common8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib6Common8PropExecDbytes_le_to_Z_nonnegC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC45stdpp9bitvector;definitions@Z_to_bv_unsignedC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7add_0_lC56Stdlib6ZArith6BinInt1Z9div_smallC46Stdlib6ZArith4Zdiv?Z_div_plus_fullC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c69OSSVerify5KrLib6Common8Mallocng8RefStep3@lor_shiftl_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indI47Corelib7Numbers7BinNums1N00c69OSSVerify5KrLib6Common8Mallocng8RefStep3BZ_to_le_bytes_to_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree6le_valC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib6Common8Mallocng;MallocShape8le_val_uC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Common8PropExec4c_eqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC59OSSVerify5KrLib6Common8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC69OSSVerify5KrLib6Common8Mallocng:MallocTree6acc_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool<orb_true_iffC69OSSVerify5KrLib6Common8Mallocng:MallocTree5ms_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC69OSSVerify5KrLib6Common8Mallocng:MallocTree5ms_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init9Datatypes9andb_propI69OSSVerify5KrLib6Common8Mallocng:MallocTree6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:ShapeNodesFZ_to_bv_small_unsignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbc69OSSVerify5KrLib6Common8Mallocng8RefStep35u_Z64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9MallocOps3is0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z;shiftr_landC56Stdlib6ZArith6BinInt1Z3oddC56Stdlib6ZArith6BinInt1Z8bit0_oddC59OSSVerify5KrLib6Common8PropExec6v_andiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec<Z_land_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng8RefStep35is0_uC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng8RefStep36c_eq_uC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions>bv_swrap_smallC45stdpp9bitvector;definitions=bv_wrap_smallC59OSSVerify5KrLib6Common8PropExec7v_srliwC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng8RefStep3:land2_evenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib6ZArith4Zdiv8Zmod_oddc69OSSVerify5KrLib6Common8Mallocng8RefStep3:land2_halfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng8RefStep38u_srliw1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng8RefStep3:ceq0_andi2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng8RefStep39is0_andi1C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z:shiftl_0_lC59OSSVerify5KrLib6Common8PropExec7v_slliwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:shiftr_0_lC56Stdlib6ZArith6BinInt1Z7mul_0_rC59OSSVerify5KrLib6Common8PropExec5v_mulC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_srliC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC69OSSVerify5KrLib6Common8Mallocng9RefPieces6halveFC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib6Common8Mallocng9RefPieces8halveF_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9RefPieces8halveF_OC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC69OSSVerify5KrLib6Common8Mallocng9RefPieces7shrinkFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9RefPieces9shrinkF_OC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9RefPieces9shrinkF_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorc69OSSVerify5KrLib6Common8Mallocng8RefStep37c_ltu_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_andC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic6eq_symC45stdpp9bitvector;definitions7bv_divuC56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z;le_lt_transK47Corelib4Init5Logic3and01C45stdpp9bitvector;definitions@bv_divu_unsignedC4ELinuxProcessSemantics5Riscv3Sem7mul_divC69OSSVerify5KrLib6Common8Mallocng9MallocOps6v_divuC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9MallocOps3wm1C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr0BK47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01c69OSSVerify5KrLib6Common8Mallocng8RefStep3:m_divu_totC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC59OSSVerify5KrLib6Common8PropExec<step_mul_genC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5instr00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC69OSSVerify5KrLib6Common8Mallocng7RefStep8reg_enumC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib6Common8Mallocng7RefStep4wregC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng7RefStep8wreg_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng8RefStep35NONCSC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation "'zpc+' base off" :=
  (ltac:(let v := eval vm_compute in (bv_unsigned base + off)%Z in exact (Z_to_bv 64 v)))
  (at level 10, base constr at level 9, off constr at level 9, only parsing).
Notation "'pc+' base off" :=
  (ltac:(let v := eval vm_compute in (bv_unsigned base + off)%Z in
         exact (@BV 64 v ltac:(vm_compute; exact I))))
  (at level 10, base constr at level 9, off constr at level 9, only parsing).

Section Gen.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma rz_msteps_p : forall segs ms ms' md T,
  md_pure md -> msteps segs ms ms' -> realizes segs (mkCfg ms' md) T -> realizes segs (mkCfg ms md) T.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) ["Gen"] "p'0h01Hh12H0h22Hhh32Hlh42Hmh53Hmsh61Th72mdh82msh93ms'h:4segsi009mp_haltedi017mp_lazyi026mp_matp;1p;3p;2p;9p-1R0p10000p4p710p9P0p1000\p4p710p8p10013p4p7210p1001_p4p710p8g002=j12Tg002]R0j1@Tg003\j35Tg004Wj23Tg005Lj34Tg006Kj10Tg0070j1<Tg007Nj1;Tg0081j1:Tg008Sj18Tg009Jj17Tg009lj31Tg00:Fj29Tg00:fj1?Tg00;^j16Tg00<>j1>Tg00=>l9=Tg00><#2g00?;R1g00@Bg00A8f1R2#@P0f2R0f6R3f5R4f4R535f7R61345f3R734f8R81364;45[[f0R9g00B1#0#0#0#0#0#0#<#;R:#:%84%7:3119::R4#2%?3%6431%2:%>6%6:31f;R:f:R6f9R435f<R31364;48f=P3P:P6P4P5P7P2P9M9=W0W5W4W3W2P0P2P9O3n101000000130100101102W1W6W7X91W8W:o"). Qed.

Lemma lor_shiftl_small : forall a y k, 0 <= k -> 0 <= a < 2^k -> 0 <= y ->
  Z.lor a (Z.shiftl y k) = a + y * 2^k.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) ["Gen"] "p'0h06__sat1h14__x1h24__x2h32Hah41ah52H0h67__arithh76__sat0h82H1h94__ffh:8__varmaph;5__with<1bh=1Hh>2Hlh?4__x3h@4__x4hA2HihB2HkhC2HyhD2HzhE1ihF1khG1si001shH1yhI1zi011li021np;1p;2p;3p;4p;7p;6p;8g006Kj1qTg00BVj1_Tg00C4j23Tg00CQj21Tg00CmR0j2GTg00DHj25Tg00Dhj2=Tg00EEj29Tg009lj34Tg00Ebj2YTg00FJj2<Tg00Fhj22Tg00GIj2;Tg00Ggj2nTg00HKj1HTg00HdR1j2gTg00IDj1cTg00Idj2CTg00JLj3@Tg00;^j1^Tg002=j1]Tg00K0j2DTg00KNj1\Tg00Klj4ATg00LJj1[Tg00Lhj1ZTg00MSj2?Tg00N6j4:Tg009Jj1XTg00Naj2WTg00OCj2KTg00O]j2VTg00PIj3UTg00Phj4TTg00QZj4STg00RCj2pTg00Rfj7oTg00SJj2ITg00Sfj6mTg00TJj6kTg00UMj1iTg00Umj3hTg001_j6QTg00VPj3fTg00W3j1PTg00WRj2ETg00X;j1eTg00XYj2dTg00Y:j3MTg00Ycj3>Tg00ZLj2NTg00[8j3OTg00[Xj1LTg00\=j3RTg00\`j2bTg00]=j3aTg00]fj6jTg00^Bj7`Tg00^fj8lTg00_JR2f0R3'Ip=0g00_hR4g00`HR5743p=F1123p=8f1R6g00`hR7g00aGR8P8g00agR9P3g00bGF`p=6f3R:P7P8P8P9f2R;P6P3Glp=7P4P5P:P;P6P3EQp=Jg00bgR<P6g00cEP3C:p=B%03R=%0:R>g00B1R?#qR@#_RA/36,1:'GP<f4RB/5:RCf6RDf5RE/5BRF'=19D354<XI<1YEC1=EC1<EC'919EC54<1<DFRFP4f8RC/26f7RG/5DRH/26';122;9443X<4f9RI/2;15CG/2;';=443X<41n6D116DRJ%HJ'gP111;GR1%H1f:R1/2:15ICRJ/2:';#FP311:CRKf<RL/2E/;3#FX<4f;RM/2BRN#c151I/2BP1PIPB1CAIRO%8ARP%0113AMRQ#8[[RR%0ARSg00clRTA@AL6UW3RU13ALRV#0\T^3SRWP0f=RX#0RY11XQRQ11GLPIf?RZ#0R[f@R\f>R],3A'1R^PDP3PZO2X4PR_13A\#8^4PR`g00dHRa#^Rb%]aRcP<1D<;RdP6%\<ReCARf%[<Rg%Z<RhP<1?<?Rig00e4Rj1?<@R@C:,6hRk%X8RlPkC71Wh9RmP3P;g00e[Rn,K41V3;=44ndAU<26CTRnb9b:b;X1<X2<1136Ro116;[^1<^2<P3fARpPLPCO3b6b0W8W5P6P3O2n2001000000120000000b7b0CSCJW>P3O1%HK15M1/2E,;3#FX<41K45PNPIPMPBPOPRPUPWP0PYPQ%0LPIP_P`PbPc1D<6PgPhP<1p<2RNg00f;R5PiC:,6hR4PlP4C7PmPnb9b:b;X1<RK%06Rq\=^1<RrP3PpP\O2b6b0X8^X5[P6P3O2n2001000000120000000b7b0POPRPUPWP0PYPQ%0]11]V'GPIP_P`PbPcPfPgPhPkPlPhP4PlPhP7P8P8P9P4PkFoC7C7PmPnb9b:b;X1<X2<%0;11;:'G\q\o^1<^2<P313ApfCP;P:O4b6b0X8^X5[P6P3O2n2001000000120000000b7b0POPRPUPWP0PYPQ1ILGPIP_P`PbPcPfPgPhPhP7P8P8P9P<P@PjPiC:,6hEmPlP<PiP5P@C:,6hC7PmPnb9b:b;X1<X2<1163g00fb[1I6;[^1<^2<P3PLPpPCO3b6b0X8^X5[P6P3O2n2001000000120000000b7b0EkCJW>P3O1n200110000021110111102bG1226%i6CJ1<CH/26AhCH6EQXA=XE<7f2A4<F21CAE%0DRF13AGR=#8[\PA@AC6VTX3S13ACRH#0\T^3SP0%0IR[11I=1=1J191J54<PE%0M13A1RJ,1LPDP3PMO2X4P%8V^4Pg00g?RV#PRL#P,E<R=%e?,d<R^1E<LRL5M<1E<VRV5><5><g00g^Rp'NAM<^=A><LV5></Np=Oab5OaPcP<PdP6P<PeP:1D<BCACAPgPh%L?R?#L,?<Rg/BN,6hPlPhAR<ig1?<?9R<@R@'B,6hPl1Bi@,6hC7C7PmPnb9b:b;X1<X2<X?<X@<A4<:2196B19;:54<19:B94<;[[^1<^2<^?<^@<P315]XR],<ZP]PZ1=Z]PCPIO6b6b0W8W5P6P3O2n2001000000121000000b7b0bDb=13A:,bB1CA:%0B13AERE#8[\PA@AD6VTX3S13AD#0\T^3SP0%0G11GEPFP:111HPDP3PIO2X4P%8J^4PPKPrP3PMP1O2b6b0W5X=[P6P3O2n2001000000120000000b7b09aB:EjXC>W3WBXF<XH<X4<o"). Qed.

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) ["Gen"] "h01Hh12H0h27__arithh34__ffh48__varmaph55__with64__x1h71zh86__sat0h96__sat1h:2bsh;2Hah<2b1h=2b2h>1nh?2Hbh@2HrhA2IHhB1bp;1p;2p;3p;4p;7p;8p;6p;5g006Kj14Tg0070j1qTg007Nj16Tg002=j1DTg00hJj2>Tg00hjj17Tg00igj25Tg009lj31Tg00;^j1ETg00OCj2?Tg00jdj1QTg00kaj20Tg00BVj1BTg00CQj23Tg00CmR0j2=Tg00lKj1bTg00C4j2_Tg00\`j2JTg00EEj29Tg00mTj2ATg00n:j2LTg00[8j3@j2Fj1YTg00nZj3XTg00o>j2WTg00odj2GTg00Idj2VTg00JLj3UTg00K0j2TTg00LJj1PTg00Lhj1OTg00MSj2NTg00RCj2<Tg00N6j4:Tg009Jj1MTg010Dj3RTg00Rfj7STg00Naj2pTg00O]j2oTg00PIj3nTg00Phj4mTg010gj3kTg011Jj3gTg011oj2fTg012^j8ITg013;j2HTg013Xj1aTg0149j3`Tg001_j6KTg00HKj1cTg00KNj1^Tg00Sfj6dTg014\j4eTg015Aj3]Tg00DHj2\Tg00Dhj2hTg015jj6[Tg0178j5iTg00SJj2jTg00^Bj7ZTg00^fj8lTg00_JR1f0R2'jp=2f1R3g00`hR4g00aGR5P5g00agR6P2g00bGFZp=;f3R7P4P5P5P6f2R8P3P2Glp=Cg00bgR9f4R:P7P8P3P2EKp=8g00B1R;#4R<#4#4R=#qR>#6R?#DR@P?1>?2%72'5=1@2RAX:@%E?,?@%Q810>8RB#2%4=#4#4#4#4#BRC,3B'=%b8%78#210>:RB%77RD%B<R<%B=R='_RE'J'9RF1A>21>?:RG1L2='55@?f5RH=@?:51@X79P@P@1A>FRI,F?1F?:1>?71LF=RJ'5P7P?P@\@RK%Y?RLPLPIP:PK\?/?Lg017ZRL%62RK%63RIP0%68?13210781073519RM[10831082519%67?183[RN%6:?178\MAX832P2n2001000000120000000W=W<W>PN^=I^<K^>LP2P>10>HRL%7:RK/JE'9RI,A>RNPH1W>IRMf6,0>RO9192X79RP1GLEPP1V<=RP131<%2=RQ131E[[RR%2<RSg00clRTAU<=3UW;RU%2E\T^;SRSP0f7,0>RT#2RV13TCRWf8RX,0>RY#2RZ13YE'=P:f9,0>RY#2f:,0>/3Cg00dHR[#ER\%D[R[1T93R]%P9R^%O9R_P91N9;R;g00e4R`1<9CC:,;_%M5RaP_P91<91Rbg00f;RcP;C:,;_RdPaP_P4P5P5P6PdP9P;P`1<9<=R9>R<C:,;_FSCCCC1p_6R`P2P8g00_hR;g00e[Re'?1o28=1;edAn913CmReb3b4b5X69R;132C%23Rf%28138E'=[[^69RgP2f<,0>P3P8O3b2W1W0P3P2O2n2001000000121000000b8b99kLE1GIEAgLKED8A19MLe10>N1f>ID8O4b0GI1HFERI15G2=1@:X79RN1HBERM/9DPNP9P1192K,5G=1@:X79PDPNP8191D%aDD8PMPPPRPUPSP0%2ORM13OCRO13TE,=VP713YCRYP;PgP2f;,0>P3P8O3b2W1X0ZP3P2O2n2001000000121000000b8b9R>9`BEEKPIPBPDPEPPPRPUPSP0PMPOA19E1RE#cP7P\P[%^9R7P^P_P4P5P5P6P9P<g00cEPbC:,;_EdP`Peb3b4b5g00fb\EP2b2X1YX0ZP3P2O2n2001000000120000000b8b9CeD8PJP0%2BRJ13BCRCPQP3P\P[P7P^P9PbPc1<9=C:,;_P`Peb3b4b5PQP2b2X1WX0MP3P2O2n2001000000120000000RQ9]F=D8GI1\D=,hBPBPDP=PQP>P0PJPC%2KP3P\P[P]P^P_PdPaPdCCP`Peb3b4b5X69%22Pf[^69P2%7XPHO2b2X1WX0MP3P2O2n2001000000120000000E[D8b@b?A@?83R8,>?%78'5=1@8eXAAX:@XB?P2DiW:o"). Qed.

Lemma w2l_le_val : forall bs : list byte, length bs = 8%nat -> word_to_le_bytes 8 (le_val bs) = bs.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) ["Gen"] "h01nh14Hlenh25Hlen0h37__arithh44__ffh58__varmaph65__with72bsh84cstrh91xh:1yh;1zp;1p;2p;3p;6p;<p;4p;7g006Kj12Tg0070j1>Tg007Nj1GTg002=j17Tg00hJj25Tg00W3j11Tg009lj30j1:Tg00hjj18Tg00igj2<Tg0188j1CTg00]fj66Tg019Hj1@Tg00kaj2?Tg01:NR0j2=Tg00BVj1WTg00SJR1j2;Tg00OCj24Tg01:hR2j13Tg01;Hj2UTg01;kj3TTg01<Hl<9Tg01<mj4FTg01=Tj1ETg00;^j1DTg00KNj1HTg00LJj1ITg00Lhj1JTg00RCj2KTg00N6j4LTg00^Bj7BTg00Naj2ATg00O]j2MTg00PIj3NTg00Phj4OTg01>9j4PTg001_j6QTg01>dj2RTg01?mj2STg01A5R3g00bgR4P0P2P1g01ATf5f4f3f2R1f1R0f0R5M<9p=Vg00B1#2#2#2R6#>#GR7#7R81575g00g?#1#1#1#1#1#1#1#1R9503P4%801<95=081X;4P31570R:%81,<5=081X03%C0P9P5E6%26#2#2#>%@0R;'?P3P91=59X031=99%W6R6/;6R<P9P61446R=P9P6P=EVA03:9%3:R>=046R?P3P4%:3P2%:4%30%35504A03051U053TX:3X93P:P>144>P9P6P=M<9P5CFP?1571R7#Eg00_JR?%37';g00dHR7#D%77%H4%I4%J4R7g00`hg00aGR=P=g00agR=P41K46R6g00f;P6CLg00bGFB1A7=P5P1g00_hR=g00e[R7'41M51=0=7dAN4?0COb4b5b6P<P5b3b8b2CPP:P5EQ,R0E61S9;=080eW1W7o"). Qed.

Lemma b_cases : forall b : bool, b = true \/ b = false.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) ["Gen"] "p'0h01bi001bp;3p;2g009lj30Tg01B6j24Tg00OCj21Tg01BPj32Tg01Bjj33Tg00_hR0P0f0R1g00e[R2500g00`HR39001'4P1A0022A0023110232A0032A0033110333n0110000020000W0o"). Qed.

Lemma c_eq_eq : forall a b : word, c_eq a b = true -> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) ["Gen"] "h01ah11bh21Hh32H0p;1p;2p;3g006Kj10Tg0070j17Tg007Nj16Tg01CDj24Tg01D=j33Tg009lj31Tg01Djj35Tg00_hf0R0g00e[31p=2g00B1#0#0#0#0#0#0#7R1#6R2f1R3/40#2g00CmA3130#2f2R4=123[R5A1230A3143#2R6[f3R7=124R8\6A5130P3n2001000000120000000X12X02P5^12^02P0P7P4P3O3P8P0b2b3W2X12W0o"). Qed.

Lemma c_ltu_lt : forall a b : word, c_ltu a b = true -> bv_unsigned a < bv_unsigned b.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) ["Gen"] "h01Hh11mh21nh32H0h41ah51bp;1p;2p;3g006Kj10Tg0070j19Tg007Nj18Tg01E_j25Tg01FYj24Tg00CQj21Tg01G6j27Tg00kaj23Tg009lj36Tg00_hf0R0g00e[36p=2g00B1#0#0#0#0#0#0#9R1#8R2f1R3/50#2g00bgR4g00Cm1430#2f2R5/13[R611301453#2R7[f3R8/15\71730P3n2001000000120000000X14W2P6^14^24P01318R81315R5P3O31185P0b0b3W0X52W4o"). Qed.

Lemma acc_ok_cases : forall s (a : word) n, acc_ok s a n = true ->
  bv_unsigned a + n <= ms_lo s \/ (ms_hi s <= bv_unsigned a /\ bv_unsigned a + n <= 2^64).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) ["Gen"] "h01Hh11nh22H0h32H1h42H2h52Hah64__x1h74__x2h84__x3h92b1h:2b2h;1mh<7__arithh=4__ffh>6__sat3h?6__sat4h@8__varmaphA5__withB1ahC1sp;1p;3p;2p;4p;7p;8g006Kj17Tg0070j1aTg007Nj1STg01GVj3HTg01H\j2@Tg01B6R0j29Tg01I9j2RTg00kaj22Tg00EEj23Tg01IYj18Tg01J^j24Tg01K;j15Tg00BVj1CTg00C4j2^Tg00GIj2<Tg00SJj20Tg00CmR1j2:Tg01L@j2WTg01BPj3VTg01L`j3UTg00Idj2QTg00CQj2>Tg00JLj3PTg00;^j1MTg002=j1LTg00K0j2=Tg00Klj4ITg00LJj1JTg00Lhj1KTg00MSj2;Tg00[Xj1GTg00\=j3NTg00RCj2FTg010Dj3OTg00N6j4?Tg009Jj1ETg00Rfj7TTg00Naj2`Tg00OCj2_Tg00O]j2]Tg00PIj3\Tg00Phj4ZTg01Bjj3YTg009lj3ATg00^Bj7[Tg00^fj8XTg00_hR2f0R3g00e[R43Ap=1f1R5/43=A24p=6P5g00`hR6g00aGR7P7g00agR8P3g00bGF[p=Bf3R9P6P7P7P8f2R:P5P3GXp=Dg01MCg00B1R;#7R<#7#7#7#7#7R=#aR>#Sg00bgR?AH:53#1P11@53#1%1:R@%15RA'9[RB%13,9A1@:5#1RA[%19/9@\A1R53P5n2001000000120000000X:2X92PB^:2^92P312>9RB/3:RAf4R@#8'4RC%5@/4B%C<RB%C=R='^RD,4A'<RAP5O3%1C%1A'9P012>@R0/39RAf5RC#8'6%5C/4014AD'<#112>CRA/3@R0f6RE#8RF'0%5ERG/0A100D':'9P3160F12>ERF/3CRHf7RI#8'0RJ%5IRK/0F10HD':RLP1165310:5[RM105316:5RN[109:\N1W53P5n2001000000120000000X;?X1?RNPM^;?^1?RMP312>IRO/3EREf8RP#8RQP5O310EQP3b0b23VW0P3O114GA140D'<#114KFRK14HDRH;U3%1K%1H':P1%5P/6O16EDf9RE#512>PRP'013PI/0D':P3f:RP#512>E'612>P/3E/6DPNPMP3f=RE#5RPf<,2>RIP:O310PIPNPMP3f>,2>/3EREPDP9O310ED1QB=g00_JRE/>B10E=1>ED[[10EBRMg00clRNAPB=5UW510ED\N^5Mg00dHRM#M%LMP?1=?:P51=?9CI%J?%K?RMP?1;?<R<%G;,;?5N?g00f;RN1F?B=O?>C?,BMRB%E7R=PMP?1;?;PNP<C?,BMR<P=PMP6P7P7P8P<PBFTCDCD1`M8P3P:1_241]3:#1dA\?E5CZb=b@bAX6?X7?X8?135:/0D105:10:9139@/0D':[[^6?^7?^8?P3fAfB,2>fC#5P9PCO5b<b>b?b4b0b3b0W4W3P5P3O2n2001000000121000000b09YJLW0P3O1n200100000021000011000b0b2W0W1WBWCo"). Qed.
End Gen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_Z64 : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h02Hzh11zp;2p;1g00SJj26Tg006Kj10Tg00BVj11Tg00C4j22Tg00CQj25Tg00Cmj24Tg01NKj23Tg00bgg00_Jf0R0'6g00B1#0R1#1%01#0#0#0#0#1'2,50'4f1/30W0W1o"). Qed.

Lemma is0_u : forall v : word, MallocOps.is0 v = (bv_unsigned v =? 0).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__with71vh81zp;1p;2p;3p;4p;7p;6g006Kj10Tg0070j1PTg007Nj1ATg00kaj23Tg01OXj22Tg009lj34Tg00OCj27Tg00mTj2@Tg00BVj18Tg00Idj2>Tg00CQj2:Tg00SJj21Tg00C4j2;Tg00JLj3OTg00;^j1NTg002=j1MTg00KNj1LTg00LJj1KTg00Lhj1ETg00RCj29Tg00N6j46Tg010Dj3BTg00Rfj7CTg00Naj2DTg00O]j2?Tg00PIj3FTg00Phj4GTg00Cmj2HTg01P5j2ITg001_j6JTg01Q8j1=Tg00^Bj7<Tf1R0g00`hR1g00aGR2P2g00agR3f0R4g00bGF<p=5g00B1#0R5#0#0#0#0#0R6#PR7#Ag00bgR8g00_JR9g00_hR:1370R;/2412;934X881374/29R;,7:1@79,37%85R5%86R6'>1:9511961;56R<,:9R=[[1195R>g00clR?AO560UW0119<\?^0>g00dHR>#N%M>%L8%K8%E8R>P1P2P2P3P81989R2g00f;P2C6,5>P8P2g00e41985=B87C6,5>FC1D>3P4f2R>g00e[R3,7:1?4>=4:3dAF890CGb2b5b61199/H=P4b1b3b4,I9EJ%=4=4:;eW7o"). Qed.

Lemma c_eq_u : forall a b : word, c_eq a b = (bv_unsigned a =? bv_unsigned b).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h01ah11bp;1p;2g006Kj10Tg0070j15Tg007Nj12Tg00kaj21Tg01OXj24Tg00OCj23Tg00B1#0#0#0#0#0#0#5R0#2R1g00_hf1,10f0,10'4'3X11W0o"). Qed.

Lemma c_ltu_u : forall a b : word, c_ltu a b = (bv_unsigned a <? bv_unsigned b).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h01ah11bp;1p;2g006Kj10Tg0070j15Tg007Nj12Tg00kaj21Tg01FYj24Tg00OCj23Tg00B1#0#0#0#0#0#0#5R0#2R1g00_hf1,10f0,10'4'3X11W0o"). Qed.

Lemma land_1 : forall z, 0 <= z -> Z.land z 1 = z mod 2.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h01zh12Hzh27__arithh34__ffh48__varmaph55__witp;2p;1p;3p;4p;7p;6g00SJj21Tg006Kj1FTg00BVj14Tg00C4j26Tg00odj20Tg009lj32Tg00OCj23Tg01R:j1=Tg00FJj2;Tg00;^j1:Tg002=j17Tg00KNj18Tg00LJj19Tg00Lhj1ETg00RCj25Tg00N6j4DTg00^Bj7CTg00Naj2BTg00O]j2?Tg00PIj3>Tg00Phj4@Tg01RXj3ATg001_j6<Tg00bgR0g00_JR1f0R2'1P0f1R3g00B1R4#F#4R5%44R4'6'0f2R6/059202X001035,30%=4,;3g00dHR5#:%75%80%90%E0R5g00`hg00aGR7P7g00agR7P01501g00f;1504CDg00bGFC1B57P2P6g00_hR7g00e[R5'31?26=275dA>013C@b3b4b51114P2b29A34E<W1W0o"). Qed.

Lemma land2_half : forall z, 0 <= z -> Z.land (z / 2) 1 = Z.land z 2 / 2.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h01zh12Hzh27__arithh34__ffh48__varmaph55__witp;2p;1p;3p;6p;4p;7g00SJj28Tg00BVj19Tg00n:j21Tg00FJj20Tg006Kj1HTg00C4j2DTg013;j23Tg009lj32Tg00OCj25Tg01S;j3=Tg001_j6<Tg00;^j1;Tg002=j1:Tg00KNj1GTg00LJj1FTg00Lhj1ETg00RCj27Tg00N6j4CTg00^Bj7BTg00Naj2?Tg00O]j2@Tg00PIj3ATg00Phj4>Tg015Aj34Tg00]fj66Tg00bgR0g00_JR1f0R2'8P0f1R3g00B1R4#9R5'1R61025f2R7%H4#9R4'01D45R8'3520X00P01034R9/15R:1175/05=202X00R;P01145,06R6P;1506P:A=345E<1398g00dHR4#;%:4%G0%F0%E0R4g00`hg00aGR:P:g00agR:P01701g00f;1705CCg00bGFB1?4:P2P7g00_hR:g00e[R4'51@27=2:4dAA013C>b3b4b51815P2b2R29495E61338A4352E6W1W0o"). Qed.

Lemma land2_even : forall z, Z.odd (Z.land z 2) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h01bh11zp;1p;2p;3p;6g006Kj1;Tg00BVj1:Tg00FJj22Tg00Fhj20Tg009lj39Tg00GIj27Tg00IDj13Tg00Umj34Tg001_j65Tg01S`j16Tg01T=j11Tg00]fj68Tg00bgg00_hR0f0R1g00B1#;#:R2'2R3g00_JR4'0R5g00`H9901X00R6P01014R01024'7P6%30P5A4124E5%63%13E8W1o"). Qed.

Lemma is0_andi1 : forall x : word, MallocOps.is0 (v_andi x 1) = (Z.land (bv_unsigned x) 1 =? 0).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h01Hh12H0h27__arithh36__sat1h42Hah54__ffh66__sat0h78__varmaph85__with94__x1h:2H1h;2H2h<6__sat2h=1bh>1xh?1zp;1p;2p;3p;4p;7p;6p;8g006Kj15Tg0070j1\Tg007Nj1FTg00BVj18Tg01T_j2[Tg00kaj22Tg00FJj23Tg009lj37Tg01UZj1CTg00C4j2@Tg00CQj21Tg00CmR0j26Tg00Idj2UTg00JLj3TTg00;^j1RTg002=j1QTg00K0j2LTg00LJj1KTg00Lhj1JTg00MSj2HTg00RCj2:Tg010Dj3ETg00N6j4;Tg009Jj1DTg00Rfj7GTg00Naj2ITg00OCj2=Tg00O]j2BTg00PIj3ATg00Phj4MTg00KNj1NTg01VXj4OTg00mTj2PTg01P5j2?Tg001_j6>Tg01Q8j1STg01WYj1ZTg01OXj2YTg00SJj2XTg00^Bj7VTg00^fj8WTf0R1g00_JR2'Yp=41X21p=0f1R3g00`hR4g00aGR5P5g00agR6P1g00bGFVp=9f3R7P4P5P5P6f2R8P3P1GWp=<g00B1R9#5R:#5#5#5#5#5R;#\R<#Fg00_hR=%89R>,[1R?,2<#4R@12<3RA/3>RB#497=1X==%C112<1RC#0%8:R:%8;R;'@RD,1C'6PAP>1U:;RA112:%0;112D[[RE%0:RFg00clRGAT:;3UW4R;%0D\G^4FRFP012<7R7#0RG117DRHf4,2<RI#011ID'6P8f5RJ,2<RK#0RLf6RM,2<RN/1DROg00bgRPg00dHRQ#RRR%QQRQ1LP3%KPRS%JPRTPP1HP9R9g00e41:P:=EP<C;,9TR:%D5RUPTPP1:P2RVg00f;RWP9C;,9TR9PUPTP4P5P5P6P9P:FGC<C<1IT6R6P1P8g00e[R:,==1B18=7=:dAAP23CMR2b5b7b8W9R:111D%03%08118D'6[[^9PR9P1f8,2<R5P3P8O3b2W1W0P3P1O2n2001000000121000000b6b3PAPEP;PFP0PGPH%0>RHP8PRPQ%NPPSPPPVPW1:P>C;,9TP6P2b5b7b8PHP1b2X1OX0LP3P1O2n2001000000120000000b6b3CO%0B11BD'6PP12<8/3>RB%41137>#457=X?P%4B,==1P<B,2<PAPEP;PFP013I>RI#011ID13K>RK#011KD'6P813N>#0f7RN,2</3>/1DP0%05115Df9,2</3>R5#0115D'6PNf:,2<#0f;,2</1DP:P9P1f=,2</3>PJPMO3b2W;W0P3P1O2n2001000000121000000W:W1P3P1O2n2001000000121000000b3b<,?BE>b1b013C>#497=@e%S?%Z?E>W>o"). Qed.

Lemma ceq0_andi2 : forall x : word, c_eq (v_andi x 2) (Z_to_bv 64 0) = (Z.land (bv_unsigned x) 2 =? 0).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h01Hh12H0h27__arithh36__sat1h44__ffh58__varmaph65__with72H1h82H2h92Hah:6__sat0h;6__sat2h<4__x1h=1zh>1bh?1xp;1p;2p;3p;4p;6p;7p;8g006Kj16Tg0070j1]Tg007Nj1KTg00BVj1<Tg01T_j2\Tg00kaj20Tg00mTj2?Tg01OXj25Tg00FJj23Tg009lj38Tg01UZj1GTg00C4j2DTg00CQj22Tg00CmR0j24Tg00Idj2VTg00JLj3UTg00;^j1TTg002=j1STg00K0j2OTg00LJj1NTg00Lhj1LTg00MSj2JTg00RCj2>Tg010Dj3ITg00N6j49Tg009Jj1HTg00Naj2FTg00OCj2ATg00O]j2MTg00PIj3ETg00Phj4PTg00KNj1QTg01VXj4RTg00SJj2BTg01P5j2CTg001_j6;Tg01CDj2[Tg01X\j2ZTg00^Bj7WTg00Rfj7XTg00^fj8YTg00_JR1f0R2'Bp=1f1R3g00`hR4g00aGR5P5g00agR6P2g00bGFWp=7g00bgR7P3g00f;P2C9p=:f2R8P4P5P5P6P3P2FXp==f3R9P4P5P5P6P8P3P2GYp=@g00B1R4#6R:#6#6#6#6#6R;#]R<#Kg00_hR=%<:R:,\2R>,0<1?<1R?,0<R@'5RA10<3RB/3:RC/5198=2X>=%G210<2RD#1%<;R;,D:RE,2D'4PBP:1V:;RB121:%1;121ERF[[RG%1:RHg00clRIAU:;3UW9R;%1E\I^9HRIP010<9R9#1RJ129ERKf4,0<RL#112LE'4P8f5RM,0<RN#1ROf6RP,0<RQ/2ERRg00dHRS#TRT%SSRS1O73%N7RU%L7RVP71J74R4g00e4RW1>7:RX=I7<RYC9,7VRZ%H5R5PV1>71R[/:4,7VR4P5A=V4ZC@C@1FV6R6P2P8g00e[R4,A=1M28=8=4dAE713CPR4b4b5b6X<7RZ122E%13%18128E'4[[^<7R5P2f8,0<R\P3P8O3b2W1W0P3P2O2n2001000000121000000b:b3PBPGP;PIP0PJPKPHP8PTPS%Q7RKPU1:[X,7VP6P4b4b5b6PHP2b2X1RX0OP3P2O2n2001000000120000000b:b3CR%1C12CE'4P710<8/3:RC152@139:R9/51RO58=X=7P7P11592=8=OX=715C1,A=P@PBPGP;PIP013L:RL#1R@12LERL1B11/4FRFP813Q:#1RQf7RO,0</3:/2ER9P0%1\RR12\ER\PFPOf:,0<#1RHf;,0</2ERXPTPSPKPU1:[[,7VP7P[PWPYC9,7V5=VP6P4b4b5b6PFP2b2W8W0P3P2O2n2001000000120000000W7W1P3P2O2n2001000000121000000b3b;,C1E;1?<C,0<PBPGP;PIP0P@PL13N:RN#112NE'4P8P0PRP\f9,0</3:R\#112\E'4POPZP5P2f=,0</3:PMPPO3b2X8XX0HP3P2O2n2001000000121000000X79X1QP3P2O2n2001000000121000000b3b;,CCE;b1b013D:/5198=Ae1[>?1Z>?E;W?o"). Qed.

Lemma u_srliw1 : forall x : word, bv_unsigned x < 2^31 -> bv_unsigned (v_srliw x 1) = bv_unsigned x / 2.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h02Hah16__sat0h24__x1h31Hh42H0h57__arithh64__ffh74__p1h86__sat1h96__sat2h:6__sat3h;8__varmaph<5__with=4__x2h>4__x3h?6__sat4h@1zhA2H1hB2H2hC2H3hD2H4hE2H5hF1qhG1rhH2HxhI6__sat5hJ1xp%0p;1p;2p;3p;4p;6p;7p;8g006Kj18Tg0070j1OTg007Nj1cTg00kaj22Tg00BVj1;Tg00[Xj1@Tg00C4j2BTg00CQj20Tg01UZj1^Tg00CmR0j25Tg00n:j2PTg01Y`j2FTg00mTj2NTg013;j27Tg00Idj2KTg00JLj3JTg01ZGj2pTg01[8j2gTg009lj3CTg00HKj1dTg00\`j2QTg00odj29Tg00EEj2RTg01[Yj2]Tg01\@j2\Tg00SJj2?Tg01\gj2[Tg01]Mj2ZTg00W3j1>Tg00WRj2=Tg00X;j1YTg00XYj2XTg00Y:j3WTg01^3j2VTg01^\j3UTg00Ycj3ETg00ZLj2STg00;^j1TTg00[8j3}Tg002=j1|Tg00K0j2GTg00Klj4{Tg00LJj1zTg00Lhj1yTg00RCj2LTg009Jj1rTg00MSj2HTg01_Ej6qTg00N6j4ATg00Sfj6oTg01_ij3nTg00\=j3fTg010Dj3ITg00Naj2hTg00OCj2eTg00O]j2iTg00PIj3jTg00Phj4kTg01P5j2lTg01`Lj1mTg01`ij2bTg01aLj3aTg001_j6MTg00KNj1`Tg015Aj3sTg00o>j2tTg01b9j3_Tg01bej2uTg00^Bj7vTg00Rfj7wTg00^fj8xTg00_JR1f0R2'?p=1g00bgR3f1R4;C2p=6P3P4g00e4P2CAp=<P4g00`hR5g00aGR6P6g00agR7P2g00bGFvp=4P3P4g00f;P2CAp=:f2R8P5P6P6P7P4P2Fwp=Df3R9P5P6P6P7P8P4P2Gxp=3g00B1R:#8R;#8#8#8#8R<#8R=#OR>#c12>2%;;R?%@:R@#@#@#@RA#;RB'BRC'0%^412>4RD#1%;=R=,B?RE,0D'5P312>8RD%O<RF%;:RG,P2'F,N>,2>12>9/7?RH'6X@3P31B?G,7D1FF2,N>,2>/6HX@3P317D?RI1N>2,2>/6HX@31K?=RH101?RJ%1=101E[[RK%1?RLg00clRMAJ?=4UW0R=%1E\M^0LRN1K?BRO%1B101C[\JRPAJ?B4VMX0LRB%1C\M^0LRQf6RR,2>RS/p?S00%1SS01f8,2>RT/7?RU#1\L[RVf7RW,2>/g?RXAC3?1RY#d1Q?U19T?'R,6T[RU1]T?RZf9,2>R[/9?R\#110\?'5\JR\1\[?R]10?1f:,2>R^/9?R_,0?1?_1'5[R_1[^?R`f;Ra,2>Rb/7?=C31\YRc1Zb?Rdf<Re,2>Rf/9?/6f\YRg17f?RfP3f=,2>S02/9?RhP3P0f>,2>Ri#1Rj10iERi%18Rk108E'5Pef@,2>#1RlfA,2>/0ERmPaP4O1Rn%1R\LRop-0Rpg00dHRqg00g?Rr#>Rs#>#>Rt#>,=3%Y:,X31=3t5W31=3s1V3?1=3r5U35E35E35E3g00g^'S%TqRr3}Rs%|qRqP31G38P41G39C{Rt%z3Ru%y3RvPv1L31Rw1L3?Rx'<,4v%r6Ry1H3@R@,:w,4vPvP5P6P6P7f5Eq5DvC3RzPyPvPvPvP5P6P6P7P3Pxg00cER6PwCA,4vEoPyP31H3;R;P61H3:R:9n3x=f3@CA,4vC3R@PyPvPv1:wx,4vPy1:w:,4vR6C3R5PyPv%OA9I3xRA,<;,4vR;PyAI3x>,<:,4v9Dv6C3C3C3C31hv7R7P2P8g00_hR{g00e[R|'e1i28=C{|dAj314CkR|b6b;b<X23X=3X>3W7%19R{f4R}'5\JR~g00fb\Y1Q?8/R},69[R9P{\LR{10}CRY%1}10}E'5[[[[^23^=3^>3^7pP210R?PRfD,2>PWPaPeP4fCO8Rab5b1WEW3P4P2O2n2001000000121000000bGbFbDbCbBbAb4b1b8b9b:b?,lI1FFIPOPPPBPQPHPKP=PNQ00PVPXPUPZP\P]P_P`PcPdPgPfP3PhP3P0PjPi%mCRi/?8108C'5PePnPoPsPqPtPuPvPzPyPvP@PyPvP5PyPvP;Py1b3A/::,4v1<:A,4vRA5DvC3C3C3C3P7P|b6b;b<X23X=3X>3X7p1?i}/5Y\Y\{\9\~^23^=3^>3^7pPab5b1XEmX3lP4P2O2n2001000000121000000bGbFbDbCbBbAb4b1b8b9b:b?9aFIEM1PDGPHPKP=PNPOPPPBPQP0Q0110SE%1GRSP}%1TR}10[EPrPq%`3Pu1L3G,:w,4vP7P|b6b;b<PSP2b5W4W3P4P2O2n2001000000120000000b1b8b9b:9sDGEM1tFD%;<R<,K?%1<1B?<RS,01[\JAJ?<4VMX0L%1S\M^0LPHPKP=PNPOPPPBPQP0P}10TE%1[10[S'5PR%1^10bEPrPq1G34PuPvP6PyPvPAPyAI3xF,<:,4v9Dv6C3C3P7P|b6b;b<X23%12104C108S,5k[[^23P2Q02P8PeO3b5W4W3P4P2O2n2001000000121000000b1b8b9b:b?bI9_FDEM1u8G,2>/6Ieb3WHWJo"). Qed.

Lemma andi2_srliw : forall x : word, bv_unsigned x < 2^31 ->
  MallocOps.is0 (v_andi (v_srliw x 1) 1) = c_eq (v_andi x 2) (Z_to_bv 64 0).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "p'0h01Hh12E3h26__sat8h34__x1h42H0h57__arithh64__ffh76__sat4h88__varmaph95__with:2H1h;2E2h<4__p1h=6__sat9h>1bi001bh?2H2h@2H3hA2H4hB2H5hC2H6hD2H7hE6__sat5hF6__sat6hG6__sat7hH5heq_whI1qhJ1rhK2HahL2H8hM6__sat1hN6__sat2hO6__sat3hP1whQ1xhR1zhS1EhT3H10hU2H9hV2HehW4__p2hX4__x2hY4__x3hZ1mh[1ni011nh\1yh]2E1h^3H11h_4Hoddh`2Hrha2Hxhb3Hx0hc1ei021ehd1si031sp%0p&0p;1p;2p;3p;4p;6p;7p;8g006Kj1FTg0070j1lTg007Nk101Tg00kaj23Tg00BVj1XTg00[Xj1WTg00C4j2iTg00CQj21Tg01bej2eTg00FJj29Tg01T_j2YTg00mTj2nTg01CDj2kTg013;j24Tg01UZk10<Tg01cak103Tg01S`j1GTg00Idj2hTg00JLj3gTg00;^j1~Tg002=j1{Tg00K0j2fTg00LJj1wTg00Lhj1vTg00RCj2]Tg00MSj2_Tg009Jj1oTg010Dj3dTg00Naj2mTg00OCj2>Tg00O]k20BTg00PIk30ATg00Phk40@Tg00KNk10?Tg01VXk40>Tg01dik20=Tg00HKj1<Tg00HdR0k20;Tg01OXj2UTg001_j6KTg00]fj6VTg01eIj2jTg009lj3=Tg01ehk209Tg01fHk208Tg01ZGj2TTg01[8j2Sk300Tg00\`j2DTg00odj26Tg00EEj2BTg01[Yj2Rj3}Tg01\@j2QTg00SJj2HTg00CmR1j2JTg01\gj2NTg01]Mj2PTg01fij2[Tg00W3j1ATg00WRj2OTg01^3j2zTg01^\j3yTg00Ycj3^Tg00ZLj2xTg00[8j3|Tg00Klj4\Tg01_ik302Tg00\=j3uTg01gZk104Tg01h8k205Tg01i@j2tTg01jFk106Tg01Q8k107Tg01kNj1sTg00N6j4`Tg00^Bk70:Tg00Rfj7rTg00^fj8aTg00Sfj6qTg01_Ej6pTf0R2g00_JR3'Up=5g00_hR4f1R5;=2p=:1H32p=0f2R61152'Jp=;g00`HR79=42p=?g00bgR8P5g00f;P2C`p=ZP5g00`hR9g00aGR:P:g00agR;P2g00bGK0:p=7P8P5g00e4P2C`p=MP6P9P:P:P;P5P2Frp=cf6R<P9P:P:P;f5R=f4R>f3R?P9P:P:P;P6P5P2GaGap=Cg00e[R@9=42p=LA=823p=8A=852p=2P8P5g00cEP2C`p=@P5P9P:P:P;P2Eqp=IP5P9P:P:P;P2Epp=bP?P9P:P:P;P6P5P2Gap=Eg00B1R9#FRA#FS00#F#F#F#FRB#lRC$0113C2%XARD%W9#W#W#WRE#XRF'iRG'1P4%X9RH,e5S01,3CS02/9H#51Y6D1nC3S03'k,:2X>4P413C5RI/9D#51e6H,3C/9H#5/:2X>4P814ID192H#513C6RJ/9DRK#5':XR8&0<5%0I%XBRB,iDRL7;IP814KD%52RI13C?RM/9DRN#5':XR8&03J%GK#?PMPD1hDBRM113DRK%0B113L[[RO%0DRPg00clRQAgDB5UWKRB%0L\Q^KPRR1hDFRS%0F113G[\KRTAgDF5VQXKPRF%0G\Q^KPRUP1f7RV,3CRW#0S0411WLRWf8RX,3CRY#0S05?;YLP=f9RY,3CS06#0RZf:R[,3C/1LR\g00dHR]#~R^%{]R_1f85S07%w8R`%v8Ra1]83Rb1_89R9'Z,7aRc%o:R:Pa1]8DRd%lE5d8,M9,7aP:Ad8dC,M9,7a9cacFC1ma;R;P2P61>4@RE20B26#LdB0A835H0@Reb6b8b9X38%02S08115G%06RG?;6L[[^38P2f<,3CP6f;RfO3b5W4W0P5P2O2n2001000000121000000bMbNbOb7PMPOPBPRPSPTPFPUP1Q04PWPPP=P^P_&0?8RWP`1Zbd,7aP;Peb6b8b9PPP2b5X4\X0ZP5P2O2n2001000000120000000bMbNbOb7H0>%0N?;NL13C>/9DP820=23%82RN%<N+0;P0%85R0%<0146D#5%56':P2%86RZP8P3142D#5/:IXP81U33,>4P?P2EKWSP2O1%<Z12?HRIP8P>%G2#?XP8P<PHP2EV%GHR\#?P4P\P4p-0R\P2PQg00fbRQn0110000020000Xc4g01lUP7P2EVPQ1jQ2b0bVW]%<IRIePI14>D#5P41>42S0914=D#5/:2P414VD#5/:2%5XRI,:5];P514<D#5S0:#L%5VS0;P4Q091:I2S0<P4%5[/:2S0=A=4@5]1P5%5YRI#LS0>PEW1%?IS0?P11U52RI#L1265RE[Rg1252Rh1U65Ri#LRj[12?6Rk\j20952P5n2001000000120000000XZ8X[8S0@Pg^Z8^[8S0AP214fDRgP3P>O3S0B%8gS0CP1%?I%<E[RE%<h%?iRi[%<k\i20852P5n2001000000120000000X\8XQ8S0DPE^\8^Q8S0EP2f=REP3P?O3S0F%8ES0G#<A=4@7f>REfCRi,3C/9DRk,>812EkS0HeS0IQ0Hf?Rk/TDS0J%0kS0KfARh/4D#0\P[S0LPMPOPBPRPSPTPFPUfDRI/SDS0M%8DRg#<RjfERl14lD,DD16lD'B'2[S0N1RlDS0OfFRm/6DRn#0S0P?;nD\KS0Q1QmDS0R11D3RnfGRo/6DRp,1D1Hp3'J[S0S1NoDS0TfHRq/4DS0U#8\gS0V1PqDS0WfIRr/6DRs/2r\gS0X14rDS0YP8fJRt/6DRuP8P1fKRv#0S0Z11vLS0[PjfLRwfMRx#0S0\fNRy/1LS0]P1fTS0^,3CRz#0S0_11zLS0`PjfRRzfVS0a,3CS0b#0S0cfWR{,3C/1LS0dPiP=O1S0e%0[\PS0fP^P_PWP`1@db,7a,IaS0gP;Peb6b8b9PQ\gS0hP2b5b2WDWCP5P2O2n2001000000120000000WBWAP5P2O2n2001000000120000000bJbIb@b?b:b4b0b7bEbFbGb2bH800D14ED,DD16ED'B,2E13CI/9DR[,>812k[R[eP[f@R[/[D%0[fBR|/6D#0\P[1ThD%0hS0i14iD#0\P[PMPOPBPRPSPTPFPU1SmD14oDS0j,DD/Bp,2o\j1RoD16qDRp#0?;pD\K1QqD11Ds1Hs3'J\n1NrD14tD#8\g1PtD16vDS0k/2v\g14vDRmP816wDR}P8P1Q0\11xLPKPyfOR~#0fPS0l/1LP1Q0cQ0b/1LPKQ0^fXS0b,3C#0fYS0m,3C/1LQ0eQ0fPlP<O1Q0fP^P_PWP`1Mbd,7aS0nP;Peb6b8b9PKP2b5b=b2WLWDP5P2O2n2001000000120000000WCWBP5P2O2n2001000000120000000bJbIbAb@b?b:b4b7bEbFbGb2b=bH9}kD16kDS0o#0Q0o;;D13Cl/9DS0o,>8Q0o,2[S0oeQ0o1[hDQ0i16iD#0\P[1T|D%0|14ID#0\P[PMPOPBPRPSPTPFPU1SoDQ0U,DD/Bp,2q\j1RqD%0s?;sD\K1QrD11Du1Hu3'J\n1NtD%8m\g1PvD12}w\g14wDP816xDRsP8P1Q08112DS0U12~5PE11?DS0iP1%0z11zLfSRp/2=PpQ0^#0fURp/1LS0^P1f[,3CS0o#0Q0o/1L12{YQ0mf]RY,3C#0f^,3CS0o/1LS0pPoP=O1S0q%0E\PREPrP<O1S0rPEg00g?#A#AS0s#AS0t#A#ARr#A,O81O8r1z8DQ0t,O85y8Q0s,O85^85^85^8g00g^'x=|]^P_P8P81f8?P6PWC\P5PWC\P`PaPaQ0nP:1ba=1_8ARA/Md,7a5caCEP:PaPaQ0gP:Q00,_8R]:028d=u8A,@9,7aCEP:Pa1@9b,7a,IaRdP:Pa1@]b,7aP:Pa1]8HR],@9,7a,IaP:PaPdP:PaPcP:1ba<CEFCFCFCP;Peb6b8b9X38XX8XY8X<\XW\A;>6D\KQ0h1DD>/B?,26[PQ\ZRZ%8=Rd12>HPQ[PQ\d%0<Pf[[[[[[[^38^X8^Y8^<\^W\P212YkQ0KP[PkPYPIPlP~fQRkQ0mfZPXO<b5b=b2WTWUP5P2O2n2001000000121000000WLWDP5P2O2n2001000000121000000WCX4GP5P2O2n2001000000121000000bJbIbBbAb@b?b:b7bEbFbGb2b=bH16[D,2[P816hD12|2XR8P2P4P8%GhPHP3n0100000020000R[&04hEV12h[P4%G|P4P8P2PHP3n0100000020000,2iX>4P2P7PIEV%8|13Cq/9DRq,>812iqRqePq1[ID%0IQ0P\P[1TlD%0lQ0j#0\P[PMPOPBPRPSPTPFPU1StD1DDmQ0k'B,2v\j1RvD%0}?;}D\K1QwD11Ds1Hs3'J\n1NxD14yD#8\g1PyD16~D/2~\g14~DP8Q0l/6DP8P1Q08Q0UPQPhQ0iP1%0pQ0^PQQ0a%0{Q0b/1LP1Q0o#0Q0pPQf\R{f`Rh,3C#0fa,3C/1LQ0qPEQ0rPEP^P_P8Q07P5PWC\RWP`Pa1@Ab,7aREP:Pa1IaER~P:Pa1@A],7a,IaP:PaP~P:Pa1ZbA,7aP:1ba?CEFCRAFCP;Peb6b8b9X38X<\PQ\0126HPQ[%8?PQ[%0>P<[[[[\N^38^<\P2PQPhPxPzP{PYPXO7b5b=b2W^WTP5P2O2n2001000000121000000WUWLP5P2O2n2001000000121000000WDX4GP5P2O2n2001000000121000000bJbIbCbBbAb@b?b7bEbFbGb2b=bHb:b:b:b4b0'jb1b0b;b0W1n0110000020001P2O1b1b>W;Q0:#?Q0;P4Q09Q0<P4Q0=A=475]1P5Q0>Q0DQ0EQ0BQ0C#<Q0@Q0AQ0FQ0GQ0IQ0HQ0JQ0LPMPOPBPRPSPTPFPUQ0MQ0NQ0OQ0QQ0RQ0SQ0TQ0VQ0WQ0XQ0YP8PuP8P1Q0ZQ0[A=47@R@PwQ0\Q0]P1Q0_Q0`P@PzQ0cQ0dQ0eQ0fP^P_PWP`PaPEP:PACEP;Peb6b8b9X38X<\125HPQ[%0?P=[\Z[\N^38^<\P2P@PpPoPkPzPVO6b5b2WDWCP5P2O2n2001000000121000000WBWAP5P2O2n2001000000121000000bJbIb@b?b:b4b0b7bEbFbGb2bHb1b0b;b0W1Q0?1>47W1n0110000020100P2O1b1b>W;n0110000020101P2O1b;b>b_WSP2O1n200110300021010211101bdbPb`bV14JD/9HPMPOPBPRPSPTPFPUP113C<R<#011<LQ04P>Q05Q06/1LP^P_Q07P`PaPcP:PcCEP;Peb6b8b9X38Q08%05[^38P213CfP6O2b5W4W0P5P2O2n2001000000120000000bMbNbOb7-05JEKbbQ021t52EK1Y5DQ03'k&065EKQ01/YH$07Q01#sEKWaWQo"). Qed.

Lemma u_slliw2_0 : forall x : word, bv_unsigned x = 0 -> bv_unsigned (v_slliw x 2) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h02Hah11zh27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__with82Hxh91xp;1p;2p;3p;4p;7p;6g006Kj12Tg0070j1<Tg007Nj1OTg00kaj21Tg00BVj1;Tg00DHj2CTg01Y`j2:Tg00mTj29Tg00Idj2>Tg00CQj27Tg00SJj20Tg00C4j2DTg00JLj3ETg00;^j1WTg002=j1VTg00KNj1UTg00LJj1TTg00Lhj1QTg00RCj2BTg00N6j46Tg010Dj3ATg00Naj2NTg00OCj2MTg00O]j2LTg009lj3?Tg00PIj3KTg00Phj4JTg00Cmj2=Tg01P5j2ITg00[Xj14Tg01`ij2HTg01`Lj1GTg01aLj3PTg01m1j1FTg01mUj2RTg00^Bj7STg00Rfj7YTg001_j6XTg00bgR0f0R1g00_JR23?p=3f1R3g00`hR4g00aGR5P5g00agR6P1g00bGFSp=5f2R7P4P5P5P6P3P1FYp=@P0P2f3P7P3P1EXp=8g00B1R5#2R4#2#2#2#2R8#2R9#<R:#O11:1#3%<8R8%;4R4,C1':,9:,1:#3X101:81,9:,1:#3X1019:1,1:#3X10%;9R9,>41724R;10291D49R<,72R=[[1024R>g00clR?AE493UW0102<\?^0>g00dHR<#WR9%V<R<%U0R@%T0RA%Q0RBP01B02RCg00f;RDPCC6,5BP0PCg00e4RE1B04RF=A0:C6,5B3@1NB6R6P1P7g00_hRGg00e[RH'M1L17=?GHdAK023CJRHb3b6b71022/==P1b2b4b5,I21:82%45#4#4#4R5#;R=,>4102=1D4=RG,72R7[\;AE4=3V?X0>102G\?^0>P9P<P@PAP0%<59A0FRF,H0PDPCC6,5BP0PCPEPFC6,5B5@BP6PHb3b6b7%GG/02/=7P1b2b4b59P82C81C24%F4C811:3P1C81R34,1:#3eW8W9o"). Qed.

Lemma u_srli_mul_0 : forall (s x : word) k, 0 <= k -> bv_unsigned x = 0 -> bv_unsigned (v_srli (v_mul s x) k) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h01zh12Hah22Hkh32Hxh47__arithh54__ffh66__sat0h76__sat1h88__varmaph95__with:1kh;1sh<1xp;1p;2p;3p;4p;7p;6g006Kj11Tg0070j1VTg007Nj1GTg00SJj24Tg00kaj20Tg00\`j2;Tg00mTj22Tg00n:j25Tg00BVj1<Tg00Idj2ATg00CQj2=Tg00C4j2>Tg00JLj3UTg00;^j1TTg002=j1STg00KNj1NTg00LJj1MTg00Lhj1KTg00RCj29Tg00N6j48Tg010Dj3FTg00Rfj7ETg00Naj2DTg00OCj2CTg00O]j2HTg009lj37Tg00PIj3BTg00Phj4ITg00Cmj2JTg01P5j2@Tg01nQj1LTg01o5j1?Tg01oVj2OTg020Pj2PTg00^Bj7QTg001_j6RTg00bgR0f0R1g00_JR237p=3f1R3g00`hR4g00aGR5P5g00agR6P1g00bGFQp=:P0P2f3R7f2R8P3P1ERp=6g00B1#1R9#1#1#1#1#1R:#VR;#GR<142110;8#3f5,0;/;1,2;,0;/57,2;,0;#3X0012;1,0;R=/57,2;,0;#3X001517,2;,0;#3X00%3=X00%<9R9%<:R:'A1=29142:1>9:R=,=2R>[[1429R?g00clR@AU9:3UW1142=\@^1?g00dHR?#T%S?%N0%M0%K0R?P4P5P5P6P01902R5g00f;P5C8,:?P0P5g00e41909=F0;C8,:?FE1D?6P1P8g00_hR?g00e[R6'C1H18=7?6dAB023CIb5b8b91422/J>P1b4b6b7,@2R>1528%L8C612;2,0;P>C6f4R>,0;R3/;2%?3C610;7P1C61O>7/P8,0;#3eW3W2X:0X<<W;o"). Qed.

Lemma u_lbu : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h04__x1h11Hh22H0h32Hah47__arithh54__ffh68__varmaph75__with82Hbh96__sat0h:6__sat1h;1bh<1zp;1p;2p;4p;3p;7p;6p;8g006Kj13Tg0070j1:Tg007Nj1BTg021Kj2>Tg00kaj22Tg022>j1ITg00CQj20Tg00CmR0j27Tg00BVj19Tg00;^j1=Tg002=j1<Tg00K0j2;Tg00LJj1UTg00Lhj1TTg00MSj2STg00RCj28Tg00N6j46Tg009Jj1HTg00Naj2ETg00OCj2ATg00O]j2CTg009lj3DTg00PIj3@Tg00Phj4FTg00mTj2GTg00Idj2?Tg00C4j2JTg00JLj3KTg010Dj3LTg00Rfj7MTg01P5j2NTg001_j6OTg00SJj2PTg00^Bj7QTg00^fj8RTg00_JR1f0R2'Pp=1f1R3g00`hR4g00aGR5P5g00agR6P2g00bGFQp=5f3R7P4P5P5P6f2R8P3P2GRp=4g00B1R9#3R:#3#3R;#:R<#B1><212<2R=#1%I<,0='7g00bgR=12<3R>%3;#3#3R;#3#3#9R?,02R@X<=P0%1>10>?12<8/0?P212<7R7#1RAf4,2<RB/0?g00dHRC#=RD%<CRC1;=3RE%U=RF%T=RGP=1S=9R9g00e4RH18=?C6,5GRI%H5RJPIC41EG6RKP2P8g00_hRLg00e[RM'A1C28=DLMdA@=13CFRMb5b6b7X0=103?\@^0=P2f6,2<RLP3O2b4W2W1P3P2O2n2001000000120000000%:;RN1GN>'2%9:R:%9;R;'?101:%1;1J:;RO,01[[%1:RPg00clRQAK:;3UW3%1O\Q^3PP0PA107?%1B10BO'7P8f5,2<#110L?PDPCPEPFPGPIPJPGP=18=1g00f;P9C6,5GR1PJPGP4P5P5P6P1P=P9PH18=:=L=NC6,5GFMC4C4PKPMb5b6b7X0=%13%18108O'7[\@^0=P2f8,2<P3P8O3b4W2W1P3P2O2n2001000000121000000b9b:,N>EOb8W;o"). Qed.

(* [comment removed for export] *)
Lemma halveF_odd : forall usage k x, MallocOps.is0 (v_andi x 1) = false -> halveF usage k x = x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "p'0h01xh11Hh21bh31kh42k0h55usagei001np;1p;2p;3p;6g006Kj10Tg0070j1?Tg007Nj1<Tg00BVj14Tg01T_j29Tg01Q8j16Tg009lj31Tg022gj32Tg00OCj2;Tg023lj13Tg01mUj27Tg01E_j28Tg01bej25Tg001_j6:Tg00W3j1>Tg024Jj3=Tg00B1R0#0R1#0#0#0#0#0#?#<R2g01A5R3P3g00_hR4f0R5%40R0'9#6g00`HR631R7f4f2R8f1R932=129[^02P51;29R:X17X02P2P4P21990#6R;#3P9P4P2f5R<%41R1,79'8#3P9159092<8n0100000020000n0100000020000A1258X22P4P6P4P2%35P8P4P2f6R61781'8#3P8f31580526n0100000020000n0100000020000=128X24P:P;P5E:%>8=2<9A=<89E:X17X02X33P5O1n0110000020010100W4W5o"). Qed.

Lemma halveF_le : forall usage k x, bv_unsigned x < 2^31 -> bv_unsigned (halveF usage k x) <= bv_unsigned x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "p'0h06__sat1h14__x1h27__arithh32Hah44__p1h54__x2h64__x3h74__x4h82H0h94__ffh:6__sat0h;8__varmaph<5__with=1bi001bh>1kh?1xh@2H1hA2H2hB2H3hC2H4hD2H5hE2H6hF2HxhG2IHhH6__sat2hI6__sat3hJ6__sat4hK6__sat5hL4__x5hM1qhN1rhO1HhP5usagep%0p&0p;1p;2p;3p;4p;6p;7p;8g006Kj1?Tg0070j1aTg007Nj1oTg00kaj20Tg00BVj1ITg00[Xj1CTg00C4j2XTg00CQj22Tg022gj38Tg00SJj25Tg00Idj2RTg00JLj3QTg00;^k102Tg002=k101Tg00K0j2FTg00LJj1zTg00Lhj1yTg00MSj2ATg00Naj2qTg00OCj2nTg00O]j2mTg009lj3MTg00PIj3kTg00Phj4iTg025Qj2hTg001_j6STg01T_j2gTg01Q8j1fTg023lj1DTg01mUj2KTg01E_j2OTg01bej29Tg01i@j2eTg013;j2<Tg01UZj1dTg00CmR0j2:Tg01ZGj2cTg01[8j2bTg00HKk100Tg00\`j2HTg00odj2;Tg00EEj2GTg01[Yj2`Tg01\@j2_Tg01\gj2^Tg01]Mj2]Tg00W3j1@Tg00WRj2>Tg00X;j1xTg00XYj2wTg00Y:j3[Tg01^3j2tTg01^\j3LTg00ZLj2ZTg00[8j3YTg00KNj1rTg00Klj4ETg00RCj2UTg009Jj1pTg00Sfj6sTg01_ij3TTg00\=j3\Tg010Dj3lTg024Jj3uTg026Xj4vTg00N6j4JTg00^Bj7jTg00Ycj3{Tg01_Ej6|Tg00Rfj7}Tg00^fj8~Tg00_JR1f0R2'5p=1g00bgR3f1R4g00f;P2CJp==P4g00`hR5g00aGR6P6g00agR7P2g00bGFjp=3AM342p=6AM321p=PA{342p=7P3P4g00e4P2CJp=NP4P5P6P6P7P2E|p=Wf2R8P5P6P6P7P4P2F}p=Vf3R9P5P6P6P7P8P4P2G~p=4P3P4g00cEP2CJp=Bg00B1R:#?R;#?R<#?#?#?#?R=#aR>#oR?g01A5R@10>2RA%I;RB%C:RC#C#C#CRD#IRE'XRF'2RGf4RH?884,0>10>4'5[^??RIX>@P?P410>8,5AX=?RA1RBERJ121BRK%1E121F[[RL%1BRMg00clRNAQBE4UW3RE%1F\N^3MROg00dHRP$02RQ&01PRR1F34%z3RS%y3RT1A3:RU/=U'31qT7RVP2P8g00_hRWg00e[RX'n1m28=MWXdAk314CiRXb9b;b<X13RY1522^13RZP210>HR[O1b2b:b0g00g?R\=8941h94ESXFGX??P?PWP?%I:R],g4#f#DR^P4PWP?f5R_1K4B'O#DP4194]98_9n0100000020000n0100000020000PAP^PWPWPWP?P2P9PWP?f7R^1K9B'O#DP9199]RA98^_n0100000020000n0100000020000,0>10>9R`'5P2PJPLPEPOPYPZP210>_O1b2b:b0f6Ra1K8B'O#DPWPWPWP?P2PHf819H]78an0100000020000,0>/5[P2PJPLPEPOPYPZP210>aO1b2b:b01e9810>A1<`B'6%dH%1[%I=R=,XBR`,2[':Pa19_]R[PJPLPEPO1RB=S00%1=121`[\KS01AQB=4VNX3MS02%1`\N^3MS03f9RN,0>R=/cB%1=f;R=,0>RA/<BRZ#1\M[f:,0>RY/bB%PBRW$00Rb1HBZ1;AB'G,6A[1`ABf<RZ,0>Rc/;BRd#112dB':\K1_cB12B1Ref=S04,0>Rf/;BRg,2B15g1':[1^fBf>,0>Rh/<B#P\W1]hBf?,0>Ri/;B/6i\W1<iBRjP3f@,0>Rk/;BRlP3P0fA,0>Rm#112m`fBRn/9],0>/2FPZfCRo,0>Rp#1fDS05,0>Rq/2`P=P4O1S06%1a\MS07p-0Rr%@\Rs#@Rt#@Ru#@Rv,>3Rw%x:,w3R:1>3uRu5[31t3BRx1>3t5L3Rt1>3sRs1>3\9L3xR\'7'7'7'7g00g^Ry'Z=YPQPRP3P31F3HP8%r3S08CERzP41F39CEPSPTPT1U31R{1U3BR|'N,3TR}%p6R~1A3<R<,={,3T1WTa5VTC4P~PTPTPTP5P6P6P71B|{,3TEsR7P~1A3;R61A3CRC9T3|=\3<'B,3TC4P~PT1BUC,3TP~PT%aD9l3|RD,N6,3TP~1NUD,3TC4C4C4C4PVPXb9b;b<X13X53X63X73W4%1H/:_\Kg00fb\WRD1HBH/G_,69[168H12HFRFPF[[[[^13^53^63^73^4rP212aBRFPaP^fGR8,0>198],0>P=PZPofFO9b2b0WEW8P4P2O2n2001000000121000000bNbMbDbCbBbAb@b0bHbIbJbKO2A8N^[,0>10>['5Q00Q01Q02Q03PJPLPEPO1cYB%1Y1<cBRY#1\M[1bAB1HBY/Gd,6c\b1`cB%1g12gB':\K1_fB1;hBRf,2B15f1':\e1^hB%Pj\W1]iB16lk\W1<kBP31;mBP3P010>nR0#1120`fER019o]588,0>/5pQ04%1q10>0/2`Q06Q07%@v,>3A[3:wAL3xs/7\,7t,7u'7'7/Zy=YPQPRP3PzP4P31F3_P9Q08CECEPSPTPTP}P~%C;,A3R;,={,3T1WT^5VTC4P~PTPTP7P~AT3|<=\3;,B6,3TC4P~PT1={6,3TP~PT1BC<,3TP~PT1=UC,3TP~1=U6,3TC4C4C4C4C4PVPXb9b;b<X13X53X63X73XL3X4r%1_/:a\K1HB_/Ga,69\D%1916_a15Ha15_a[[[[[^13^53^63^73^L3^4rP2PFPaP^fHR^/9]R],0>10>^fLfJ;8],0>P=PZP9Q05PnO;b2b0WEW8P4P2O2n2001000000121000000bNbMbDbCbBbAb@b0bHbIbJbKbGb8bOn0110000020001b=n0110000020001b=%@9=8_4Au_94ESXFGX??XGIX>@P2CvW>WPo"). Qed.

Lemma shrinkF_le : forall size k x, bv_unsigned x < 2^31 -> bv_unsigned (shrinkF size k x) <= bv_unsigned x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "p'0h06__sat1h14__x1h22Hah37__arithh44__p1h54__x2h64__x3h74__x4h82H0h94__ffh:8__varmaph;5__with<1kh=1xh>2H1h?2H2h@2H3hA2H4hB2H5hC2H6hD2HxhE2IHhF6__sat0hG6__sat2hH6__sat3hI6__sat4hJ6__sat5hK4__x5hL1bi001bhM1qhN1rhO1HhP4sizep%0p&0p;1p;2p;3p;4p;6p;7p;8g006Kj19Tg0070j1`Tg007Nj1nTg00kaj20Tg00BVj1DTg00[Xj1ATg00C4j2XTg00CQj22Tg0279j3:Tg00SJj25Tg00Idj2OTg00JLj3NTg00;^k100Tg002=j1}Tg00K0j2FTg00LJj1yTg00Lhj1vTg00MSj2BTg00Naj2oTg00OCj2mTg00O]j2kTg009lj3ITg00PIj3iTg00Phj4gTg028?j2fTg001_j6QTg01oVj2eTg020Pj2dTg01Q8j1cTg01bej28Tg01i@j2bTg013;j2?Tg01UZj1aTg00CmR0j2;Tg01ZGj2STg01[8j2TTg00HKj1~Tg00\`j2HTg00odj2<Tg00EEj2GTg01[Yj2_Tg01\@j2^Tg01\gj2]Tg01]Mj2\Tg00W3j1>Tg00WRj2=Tg00X;j1xTg00XYj2uTg00Y:j3[Tg01^3j2tTg01^\j3JTg00ZLj2YTg00[8j3WTg00KNj1qTg00Klj4ETg00RCj2VTg009Jj1pTg00Sfj6lTg01_ij3ZTg00\=j3PTg010Dj3rTg029Gj3sTg026Xj4jTg00N6j4LTg00^Bj7wTg00Ycj3hTg01_Ej6zTg00Rfj7{Tg00^fj8|Tg00_JR1f0R2'5p=1g00bgR3f1R4g00f;P2CLp=@P4g00`hR5g00aGR6P6g00agR7P2g00bGFwp=3AI342p=6AI321p=MAh342p=7P3P4g00e4P2CLp=KP4P5P6P6P7P2Ezp=Uf2R8P5P6P6P7P4P2F{p=Rf3R9P5P6P6P7P8P4P2G|p=4P3P4g00cEP2CLp=Cg00B1R:#9R;#9R<#9#9#9#9R=#`R>#nR?g01A5R@10>2RA%D;RB%A:RC#A#A#ARD#DRE'XRF'2RGf4RH?:84,0>10>4'5[^=?RIX<@P?P410>8RJ,5AXL?RA1OBERK121BRL%1E121F[[RM%1BRNg00clROANBE4UW2RE%1F\O^2NRPg00dHRQ$00RR%}QRS1F34%y3RT%v3RU1B3:RV/@V'31oU7RWP2P8g00_hRXg00e[RY'm1k28=IXYdAi314CgRYb9b:b;X13RZ1522^13R[P210>HO1b3bFb0g00g?R\=:941f94EQXDGX=?P?PXP?f5R]/e4%A;R^#9#9#D'd#cR_P4%D:R`,849:]9n0100000020000PAP_PXPXPXP?P2P9f7RX189`7:]n0100000020000,0>10>9R_'5P2PKPMPEPPPZP[P210>]O1b3bFb01b84188`,0>1?JB'6%a9%1_%D=R=,XBRJ,2_';P]18H`R_PKPMPEPP1OB=S00%1=121J[\LS01ANB=4VOX2NS02%1J\O^2NS03f8RO,0>R=/SB%1=f:,0>R=/?BR[#1\N[f9,0>RZ/TB%MBRA#~Ra1HB[1<=B'G,6=[1_=Bf;R[,0>Rb/<BRc#112cB';\L1^bB12B1Rdf<Re,0>Rf/<BRg,2B15g1';[1]fBf=S04,0>Rh/?B#M\A1\hBf>,0>Ri/<B/6i\A1?iBRjP3f?,0>Rk/<BRlP3P0f@,0>Rm#112mJfARn/8`,0>/2FPefBRo,0>Rp#1fCRq,0>Rr/2JP[P4O1S05f6Rs#1\NS06p-0Rt%>\Ru#>Rv#>Rw#>Rx,=3Ry%x:,u3R:1=3wRw5[31t3BRz1=3v5J3Rv1=3uRu1=3\9J3zR\'7'7'7'7g00g^R{'Y=WQRPSP3P31F3HP8%q3S07CES08P41F39CEPTPUPU1V31R|1V3BR}'K,3US09%p6R~1B3<R<,@|,3U1UUs5RUC4P~PUPUPUP5P6P6P71C}|,3UElR7P~1B3;R;1B3CRC9Z3}=P3<'C,3UC4P~PU1CVC,3UP~PU%`D9r3}RD,K;,3UP~1KVD,3UC4C4C4C4PWPYb9b:b;X13X53X63X73W4%1H/;]\Lg00fb\ARD1HBH/G],69[168H12HFRFPF[[[[^13^53^63^73^4tP212sBRFPsPXfFR8,0>188`,0>P[PePqfEO9b3b0WCW8P4P2O2n2001000000121000000bNbMbBbAb@b?b>b0bGbHbIbJO2A:Os_,0>10>_'5Q00Q01Q02Q03PKPMPEPP1SZB%1Z1?bBRZ#1\N[1T=B1HBZ/Gc,6b\a1_bB%1g12gB';\L1^fB1<hBRf,2B15f1';\d1]hB%Mj\A1\iB16lk\A1?kBP31<mBP3P010>nRn#112nJfDRn18o`5:8,0>/5pQ04%1r10>n/2JQ05Q06%>x,=3A[3:yAJ3zu/7\,7v,7w'7'7/Y{=WQRPSP3Q08P4P31F3]P9Q07CECEPTPUPUQ09P~1B3^R^,@|,3U1UUX5RUC4P~PUPUP7P~AZ3}<=P3^,C;,3UC4P~PU1@|;,3UP~PU1CC<,3UP~PU1@VC,3UP~1@V;,3UC4C4C4C4C4PWPYb9b:b;X13X53X63X73XK3X4t%1]/;s\L1HB]/Gs,69\D%1916]s15Hs15]s[[[[[^13^53^63^73^K3^4tP2PFPsPXfGRX/8`R`,0>10>XfKfI;:`,0>P[PeP9PnPoO;b3b0WCW8P4P2O2n2001000000121000000bNbMbBbAb@b?b>b0bGbHbIbJbEb8bOn0110000020001bL%>9=:]4As]94EQXDGX=?XEIX<@P2CjW<WPo"). Qed.

(* [comment removed for export] *)
Lemma nosmall_word : forall b : word,
  negb (c_ltu b (Z_to_bv 64 100)) = negb (c_eq (v_xori (v_sltiu b 100) 1) (Z_to_bv 64 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "p'0h01zh17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__with71bi001bh82Hah92b0p;1p;2p;3p;4p;6p;7g006Kj12Tg0070j1_Tg007Nj1WTg00kaj21Tg00[Xj1KTg00BVj1>Tg00mTj24Tg01FYj2;Tg023lj10Tg02:Oj2HTg02;Kj2GTg01CDj2ITg01OXj2<Tg02<Fj2:Tg009lj38Tg00OCj2DTg00Idj2YTg00CQj2=Tg00SJj26Tg00C4j2XTg00JLj3VTg00;^j1UTg002=j1TTg00KNj1STg00LJj1RTg00Lhj1QTg00RCj2?Tg010Dj3NTg00Naj2MTg00O]j2OTg00PIj3PTg00Phj4LTg00Cmj2BTg01P5j2CTg001_j69Tg01X\j2^Tg01E_j2]Tg02<dj2\Tg00N6j4JTg00^Bj7ZTg00Rfj7[Tg00_hR0f1R1f0R238p=3g00_JR3,<2p=7g00bgR4P1g00f;P2CJp=@P1g00`hR5g00aGR6P6g00agR7P2g00bGFZp=5P4P1g00e4P2CJp=Ef2R8P5P6P6P7P1P2F[p=AP4P3f3P8P1P2E9p=Fg00B1R6#2R5#2#2#2#2#2R9#_R:#WR;P011:2R<%K6#2#2#K#2#2#>R=,4:R>,1:R?';R@%02RA1H1=%>6R6'G14:3RB'I#0'3X70P01H2=/G6RC,1:11:BRD'<RE11:1RF/;?#0/3AX70P4P=1;F2#0P0P;1;F=RF14:6RGPBn0100000020000,1:/:6,4:,1:RH/<D#0'3X04%0F1<H2#0'3X041;<=P0P0P0P;P2PGPBn0100000020000,1:/:6,4:,1:#7#0,3AP2P4P6g00`HRA1:26,4:,1:#7#0R;580X04%72#0R<980AX041<33#0,D0PD%>5R5%>9R9'YRH1=3516391X59RF,=3RI[[RJ1635RKg00clRLAV591UW8R9163F\L^8KRKg00dHRL#URM%TLRL%S4RN%R4RO%Q4RP1?43RQ/@Q,5P1?45=N4:R5,EQ,5P3A1MP7R7P2P8g00e[RR,D01O28=80RdAP431CLR1b2b5b61633/BIP2b1b3b4,C3RICF11:GRGPHPJP9PKPMPLPNPO1?46R8,@Q,5P1E85,5P5APP7P1b2b5b616361=6F'BP2b1b3b4,C6R8E9%0R1:G6,4:,1:#7#0'3eA80R;X04P4P6A80R<X04%76#0,D0PGP8E9PDPICF%0A1:D6,4:,1:#7#0'3en0110000020101b9PDPICFP?PHPJP9PKPMPLPNPO1?4=R4,@Q,5P1E45,5P5APP7P1b2b5b6163=1==F'BP2b1b3b4,C=E9%0@%0E'3e1ICB1^CBE91]2>1\2>E9W7o"). Qed.

(* [comment removed for export] *)
Lemma and_seqz_sltu : forall x y z : word,
  c_eq (v_and (v_sltiu x 1) (v_sltu y z)) (Z_to_bv 64 0)
  = negb (c_eq x (Z_to_bv 64 0) && c_ltu y z).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "p'0h01bi001bh11Eh22H0h31xh41yh51zh61Hh72Hah87__arithh94__ffh:6__sat0h;6__sat1h<8__varmaph=5__with>4__x1h?1mh@1np;1p;2p;3p;6p;4p;7p;8g006Kj1;Tg0070j1oTg007Nj1^Tg00BVj1FTg02:Oj2RTg02=ij2NTg02>dj2LTg00kaj20Tg00mTj26Tg01OXj23Tg01CDj2GTg01E_j2DTg01FYj22Tg00FJj2=Tg01UZj1lTg00C4j2fTg00CQj2<Tg00CmR0j2MTg009lj31Tg01ehj2]Tg001_j6?Tg00HKj1CTg01fHj2\Tg00SJj29Tg02?^j2[Tg00Idj2ZTg00JLj3YTg00;^j1XTg002=j1WTg00K0j2VTg00LJj1UTg00Lhj1TTg00MSj2STg00RCj2ITg00N6j4ETg00Sfj6nTg009Jj1mTg00Naj2kTg00OCj2PTg00O]j2iTg00PIj3hTg00Phj4gTg02@>j4eTg00]fj6bTg00KNj1aTg010Dj3cTg00Rfj7dTg01P5j2`Tg01X\j2KTg00GIj2QTg023lj1JTg00^Bj7_Tg00^fj8jTg00_hR1f2R2f1R3f0R4'Q#J31p=5g00_JR5/94p=71345p=41P14p=:A1134p=Ag00e[R69114p=@g00`HR79114p=8P3g00`hR8g00aGR9P9g00agR:P4g00bGF_p=>g00bgR;P3g00f;P4CEp=Hf3R<P8P9P9P:P2P3P4Gjp=O1Q34#Jp=Bg00B1R=#;R>#;#;#;#;#;R?#oR@#^RAP1%F=RB,R21N34'LRC,0@16@5RD,0@RE'3RF1G<D1D23RG554X01P110@2RH/3ERI1R<B1N23'L,0@/3E?54GX01P;P5P1PA10@<RJ/2BRK16@BRLPDn0100000020000,0@P1PAPGPLPDn0100000020000,0@'=,6@,0@/3413J4;5GX5;%l2%7H%F>R>%F?R?'fRG,<H'M%4JRJP1%:4f4RH,0@RM#4RN/A4P1f6,0@#4/A4f7,0@RO/2B,A3]1P3f5RP,0@#4RQ#@P01334RR#@A1;23RS[RTA1;34RU1323RV#@RW[A1;<2RX\W1]34P3n2001000000120000000X?;X@;PT^?;^@;P4POP5P3O3RTA1;O5ROP;P5124B9116X5;125B#:f8RW,0@RYP4E?b1b2W1%8QP0%8R%CS[RS%CU%8VRV[%CX\V1\34P3n2001000000120000000X4;X3;PS^4;^3;PT%COP112YBP7P01234#81932RY[19431223#8[RO12<2#8\Y1[34P4n2001000000120000000X4;X3;PO^4;^3;P4f9,0@PB1Z>?RO1<5>%7?1<5GRY[[RT%7>RSg00clRVAY>?3UW7R?%7G\V^7SRSP0f;,0@R0#71<0Gf<,0@,9BPWf=,0@#7f>,0@/<Gg00dHRG#XR0%WGRG1V;3%U;RV%T;RXPXP8P9P9P:P;1S;=R=g00cE1I;5RUCE,>XEn%m9RRPX1HU=,>XPR1I;B/H=,>XCOCO1kX:R=P4P21P161i42#@dAh;53CgRRb9b<b=X>;A1;45g00fb[%7319B2[[^>;P4f@,0@PWP2O3b8W2W6P3P4O2n2001000000120000000b:b;O3b2Ceb1b2W1n0110000020001P4O1b1b01AJKP1PNP1PAP4PLPDn0100000020000,0@RJP1PA1DH<R<PLPDn0100000020000,0@'=,6@,0@#4?5Q<X01PNP1P1P1PA1DPHRPPLPDn0100000020000,0@,=J,6@,0@#4?54PP4P<P1P110@L/=J,6@,0@#4?564P41B66#:1B67#:n0110000020000b0P<P1P11=EJ,6@,0@#4?574P41B76#:1B77#:n0110000020000b0n0110000020000b012MBP4Ebb2b6PEPOPTP?PSP0PG%a;PVPXP8P9P9P:1HUU,>XP;PUg00e41I;>=c;@CE,>XFdP=PRb9b<b=1955/MYP4b8b:b;,`5E?1D3495FIe1G2D1K2DE?1GCD1KCDE?X5AX4AW3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_divu_tot : forall a b : word, mul_div M_DIVU a b = MallocOps.v_divu a b.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "p'0h01Hh14__x1h21Eh32H0h42H1h52H2h67__arithh74__ffh86__sat1h96__sat2h:8__varmaph;5__with<2Hah=4__x2h>2b1h?2b2h@1nhA1xhB1yhC1zhD1ahE1bi001bhF2b0p&0p;1p;2p;3p;4p;5p;6p;7p;8g006Kj11Tg0070j1bTg007Nj1<Tg00kaj20Tg01OXj2=Tg00OCj2JTg009lj35Tg00X;j1]Tg00mTj2BTg02@Zj3OTg013;j2GTg00nZk301Tg00[Xj13Tg00BVj1@Tg00HKj1CTg01fHj2cTg00o>j2_Tg01UZj1^Tg00C4j2[Tg00CQj22Tg00CmR0j2ZTg00Idj2YTg00JLj3XTg00;^j1WTg002=j1VTg00K0j2NTg00LJj1UTg00Lhj1TTg00RCj2MTg00MSj2LTg009Jk100Tg00Naj2~Tg00O]j2xTg00PIj3wTg00Phj4uTg00N6j4?Tg02A@j4nTg00\`j2ITg00SJj2DTg01^3j2QTg00XYj2PTg02Aaj4gTg02BBj2fTg00W3j1ETg00WRj2FTg00Ycj3>Tg00ZLj2eTg00[8j3dTg00KNj1jTg00Klj4kTg02Bkj5lTg010Dj3mTg01_ij3aTg02COj5`Tg02D;j5pTg02D`j4qTg01b9j3rTg02@>j4sTg011oj2tTg001_j6STg02E;j3vTg02Ejj4\Tg02FTj2yTg00^Bj7zTg00^fj8{Tg00Sfj6|Tg01^\j3}Tf0R1#1#1#1#1p>02g00bgR2f1R3;51p=9%31#3p=o%31#3#3#3p=i%31#3#3#3#3#3#3#3p=;g00_hR4g00`H751p=Hg00_JR59521p=K1D51p=4P2P3g00f;P1C?p=AP3g00`hR6g00aGR7P7g00agR8P1g00bGFzp=8f3R9P6P7P7P8f2R:P3P1G{p=7P3P6P7P7P8P1E|p=R%11#1p=h%11#1#1#1#1#1#1#1p=:A}231p=6g00B1R;#1R<#1$02R=#bR>#<R?10>1/=5P41J4110>3/=5=541P410>9/=5=541P4P?P3%];,B>R@f5RAf4RB5O>n0100000020000P4P?P3g02GYRC10>A10>BRD'G,B>n010000002000055?]2P310>:/=5REg00e[RF554g017ZRG%<1RH%<3RIP0%<:?531109:1093'9RJ[10:310:1'9%<9?5:3[RK%<B?59:\JB01:31P1n2001000000120000000W?W>W@RJPK^?I^>H^@GRGP1P>P@PC%3;#o#i#;#;#;#;#;#;#;#@,J210>@10>C'9dO4b0W2%HEP01=31#H19:3#C[RE1931#C1=:3#HRC[199:#C\C1c31P3n2001000000120000000XB2XA2PE^B2^A2P1PDP5P3O3%KD#CPJPGP1P>f7RGf6RJ5O>RD10>GRE10>J'GRC,B>R9P2PCf8,0>R@/GERH,B>,0>,91XC2P21_>CRI19H1XC2P2PIPC%^GRI%4E%@<RH%@=RK'[RL,2E'ZREPIPEf9RE,0>RI/G@RM#412MLPIP@1YHKRN125H%4K125L[[RO%4HRPg00clRQAXHK3UW<RK%4L\QRQ^<PRRP0f:,0>RS#4RT12SLRSf<,0>RU#4RVP:f=,0>/2LRWP0f?,0>RX#4RY12XLRZf@,0>R[#4PGfA,0>#4R\fB,0>/2LR]g00dHR^#WR_%V^R`1N23Ra%U2Rb%T2Rc1M25Rd1L2;Re'A,8cRf&007RgPfC71~c8RhP1P:1J4F1x1:=54FdAw253CuRFb7b:b;X12%41R4%43[^12P1fD,0>RiP:O2b6W5W0P3P1O2n2001000000120000000W4X3VP3P1O2n2001000000121000000b8b9PNPOPKPRP0PTPSf;,0>Rj,25P:P0PYPZ125XPGP_P`PaPbPcPfPgPcP2Peg00cERkPdC?,8c,RcPgP2Pdg00e4RlPeC?,8cC7C7PhPFb7b:b;X12%K3g00fbRm[125:[\4^12P1fC,0>R4PJf>RnO3b6X5]X0\P3P1O2n2001000000120000000X4WX3VP3P1O2n2001000000121000000b8b9RoCnPMPIPLPIP@PIPoPNPOPKPRP0PTPS1IjU,DUP:P0PYPZ1IX[,D[PG%h=#:#:#:#:#:#:#:#@,Q2R=P2%@;,P2P;1P25Cg,f2g00g?R5#ER;,F2RX'6'6%E;R;#E#E,F2Rj1F2;R;,6X=>2;R;'61Q2H1F25R5,6j'6165;,6=1655,6=5>25>25>25>2g00g^'e=d^_P`P21N2:P3%j2CkPbPcPc1M2HRH,Ad,8cPgPcPcP6P7P7P8DlPgAm2H>RH,Ad,8cC7C7PgPc1L2<R<,Ad,8cPgPcPfPgPcP2P<PkPdC?,8c,RcPgAa2<e,Ae,8cC7C7C7C7PhPFb7b:b;X12X=2PQ\P%4:RP%KBPm[1IAB,DB[\P[[^12^=2P1P4PiPEPJP:PnO6b6X5]X0\P3P1O2n2001000000121000000X4WX3VP3P1O2n2001000000121000000b8b9D`PNPOPKPRP0PTPS12ULP:P0PYPZ12[LPGP_P`PaPbPcP2PePlPHC?,8cRcPgPcC7PhPFb7b:b;X12121L123L[^12P1PiP3O2b6X5]X0\P3P1O2n2001000000120000000X4WX3VP3P1O2n2001000000121000000b8b9DpCqb3b09r>CCs10>91t>CES10>DAv>GJESO4b0b2b0W2n0110000020101P1O1b2bFP>g02H[P3P1C\1y3155?eXE?WDo"). Qed.

Section Divu.
Context {fx : FPState}.
Lemma step_divu_tot : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_DIVU rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (MallocOps.v_divu (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) ["Divu"] "h02Hdh12Heh22Hfh31bh41mh53memh62pch72rdh84regsh93romh:3rs1h;3rs2h<4segsh=1wp;1p;2p;3p;4p;5p;6p;>g002=j1NTg006Kj10Tg00[Xj1DTg0070j13Tg007Nj17Tg0013j2ITg0081j18Tg02IGj2CTg02JIj2;Tg009lj31Tg02Jkj1@Tg00:Fj2?Tg02Kkj1>Tg02L\j4MTg00BVj1LTg02MHj4KTg02Mhj1HTg02O0j3FTg01D=j3:Tg02OSj26Tg02Ejj4ETg02PLj34Tg02QGj2<Tg02RBj52Tg02S;j25Tg02FTj29Tg00OCj2BTg02TCj2GTg001_j6=Tg02UKj2ATg02VGl>JTg00><#Ng00B1#0R0#D#3R1%00R0#0R2#0#0R3#0#3R4#7R5'IR6%32#7#8\5R2%33#7R3%71R7%83f8R8f6R9'Cf3R:,;331g00_hR3f4R;#@g00`H31g02WHR<g00bgR='?R>#8f5R?#>P<P=g02H[R=P;P:f2R<CM%L0R0CK,;>31g00?;R>#HR@p,2fxRAP3P6g00_Jg01lU5F1RB9:1?RCf:RDP4P=16D;R416D:RECERF94D?n0100000020000f9RG/<0RHP8f7RID2,5>f0RJPAP3P6A:19BRBf;R1161?161;'99419n01000000200001<D0R0PGP8D2,5>RK51@X4@P5194ERLPAP3P6PBP1A419Jn0100000020000P0PGP8D2,5>=1@KX35PAP3P6PCPDA4D?Ln0100000020000PHP8PID2,5>,B@PF1G4EE=PAPDPGP8PID2,A1PAP1PDPGP8PIP9P=P?P;P:P<f1PJM>JE=W0W1W2X;7X:7W7W=X92W5X65W8W<o"). Qed.
End Divu.

(* [comment removed for export] *)
Ltac mach Hp HS ::=
  cur_instr ltac:(fun w i =>
    lazymatch i with
    | OpImm ALU_ADD _ _ _   => rz_plain Hp HS step_addi
    | OpImm ALU_AND _ _ _   => rz_plain Hp HS step_andi
    | OpImm ALU_OR _ _ _    => rz_plain Hp HS step_ori
    | OpImm ALU_XOR _ _ _   => rz_plain Hp HS step_xori
    | OpImm ALU_SLT _ _ _   => rz_plain Hp HS step_slti
    | OpImm ALU_SLTU _ _ _  => rz_plain Hp HS step_sltiu
    | ShiftImm ALU_SLL _ _ _ => rz_plain Hp HS step_slli
    | ShiftImm ALU_SRL _ _ _ => rz_plain Hp HS PropExec.step_srli
    | ShiftImm ALU_SRA _ _ _ => rz_plain Hp HS step_srai
    | Op ALU_ADD _ _ _  => rz_plain Hp HS step_add
    | Op ALU_SUB _ _ _  => rz_plain Hp HS step_sub
    | Op ALU_AND _ _ _  => rz_plain Hp HS step_and
    | Op ALU_OR _ _ _   => rz_plain Hp HS step_or
    | Op ALU_XOR _ _ _  => rz_plain Hp HS step_xor
    | Op ALU_SLL _ _ _  => rz_plain Hp HS step_sll
    | Op ALU_SRL _ _ _  => rz_plain Hp HS step_srl
    | Op ALU_SRA _ _ _  => rz_plain Hp HS step_sra
    | Op ALU_SLT _ _ _  => rz_plain Hp HS step_slt
    | Op ALU_SLTU _ _ _ => rz_plain Hp HS step_sltu
    | OpImm32 _ _ _     => rz_plain Hp HS step_addiw
    | Op32 ALU_ADD _ _ _ => rz_plain Hp HS step_addw
    | Op32 ALU_SUB _ _ _ => rz_plain Hp HS step_subw
    | Op32 ALU_SLL _ _ _ => rz_plain Hp HS step_sllw
    | Op32 ALU_SRL _ _ _ => rz_plain Hp HS step_srlw
    | Op32 ALU_SRA _ _ _ => rz_plain Hp HS step_sraw
    | ShiftImm32 ALU_SLL _ _ _ => rz_plain Hp HS step_slliw
    | ShiftImm32 ALU_SRL _ _ _ => rz_plain Hp HS step_srliw
    | ShiftImm32 ALU_SRA _ _ _ => rz_plain Hp HS step_sraiw
    | Mul M_MUL _ _ _   => rz_plain Hp HS step_mul
    | Mul M_MULHU _ _ _ => rz_plain Hp HS step_mulhu
    | Mul M_DIVU _ _ _  => rz_plain Hp HS step_divu_tot
    | Lui _ _           => rz_plain Hp HS step_lui
    | Auipc _ _         => rz_plain Hp HS step_auipc
    | Jal _ _           => rz_plain Hp HS step_jal_x0
    | _ => fail "mach: not a plain instruction:" i
    end).


Lemma word_pred_nat : forall k : nat, Z.of_nat (S k) < 2^64 ->
  v_addi (Z_to_bv 64 (Z.of_nat (S k))) (-1) = Z_to_bv 64 (Z.of_nat k).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h01xh14__x1h21zh31nh41yh52Hah63Hk0h77__arithh84__ffh96__sat0h:6__sat1h;8__varmaph<5__with=2b1h>2b2h?4cstrh@1HhA2HkhB1khC1mp;1p;2p;3p;4p;<p;8p;6p;7p;Bg00W3R0j1ETg01:hR1j17Tg006Kj18Tg00BVj1@Tg00C4j2nTg00CQR2j23Tg007Nj1:Tg009lj39j1^Tg00kaj22Tg00nZj3UTg0070j1NTg00mTj2;Tg00X;j1mTg02QGj2kTg00EER3j21Tg00o>j26j1cTg00OCj24Tg02X4j1DTg02XRj4[Tg01<Hl<ATg01<mj4XTg01=Tj1WTg00Idj2VTg00JLj3TTg00;^j1STg002=j1RTg00K0j2OTg00LJj1PTg00Lhj1QTg00MSj2MTg00RCj2<Tg00\=j3GTg00N6j4=Tg00Naj2lTg00O]j2jTg00PIj3hTg00Phj4gTg01>9j4KTg012^j8fTg00CmR4j2CTg00SJR5j2JTg02Y5j6dTg009Jj1bTg010Dj3`Tg00Rfj7aTg01b9j3_Tg001_j6?Tg011oj2BTg02Y^l<LTg02ZClB]Tg00^Bj7\Tg00^fj8iTg00bgR6f1R7f0R839p=0g01A5R9P9P6P6P0P1P1f3R0g02Zif2R:P7P8M<Lp=ZP9P6P6P6P1P1f5R1f4R;P0P:P7P8M<Lp=HP6P6P6P6P6P6P3P8P7P:P3P0P;P1f6R3f7R<f8f9MB]p=YP6P6P2P<P2P3P1P;P0P:P7P8M<Ap=Fg00_JR3/J8p=5P7g00`hR2g00aGR=P=g00agR>P8g00bGF\p=>P6P6P5P1P5P;P3P3P0P:P7P8M<Ap=eP0P2P=P=P>P:P7P8Gip=I%E8#7g00B1R5#8R1#@R?%81#8#8#8#8R1#@R@'nRA'3g017ZRB%:8RC%:7RDP4%::?978120:1207'0R4[12:712:8'0%:0?9:7[RE%:;?90:\4AU:78P8n2001000000120000000W>W=W3PE^>D^=C^3BP8%N1R1%E:RB#7RC,;1RD%m5RE'kR4%7:RF,;1RGP6121DRD/1ERH,61%70RI,;1,21RJ,08X26P6161CRK118E,61RL/0JX26P6161F%E0#7,61/1E,61/08X26P6PC161I,0LX26P6P6%c1RLPL11CERJPFP6\6/4L10JF%@5RL,1FRM/1ERN/0FP6P6%^6ROP8X06RPPO1078#DX46X06PJPNPPPPPPP6P6g02[M1178C[,46XC6X36PCPMPPPP%78,46X09RNPBPM118LRJX06ROP:PF146FRQCZRREHRSPEPE146EM:YPFPFPQM<A13CARQ13MARTPP1378#DX46X06RUPCPPPOPFO1ROO1PPPPPNPBPOPREHPAPA146ARR10AAeGFP7CXROPT%W0RB%5IRI1V?@RN133?%5@133A[[RV%5?RWg00clRXAT?@7UW5R@%5A\X^5WRWg00dHRX#SRY%RXRX1O67RZ%P6R[%Q6R\P61M65R51<6L5G6R]1<6E5G6g00cEP5C='>1l\>R^P8P:g00_hR_g00e[R`'41j8:=9_`dAh637CgR`b8b;b<X1611JE/08^16P8%7<R<O1b7b9b:b?b6CKGfPK%5CRK/CQ%5MRJ/CTPKPQPJPTPP1J78#DX46X061463PCPMPSEePPPUPCPMPSPAPAPRGFEdPOPTPBPIPNPVP@PWPYPXPZP[P\P61<63R3g00f;R[P5C=,>\%b=R5P\P6P]g00e41<6?=`61C=,>\R?P5P\P2P=P=P>P6P3P[P]C=,>\P?FaCICIP^P`b8b;b<X16%58117L/3A11:LRL#513LA'C[[^16P8P<P0P;O3b7b9b:b?b6CK9_1CE?121GRG1B1FE?PD1B1CE?1;1H,211B1HE?1214/0GeO4b@WAXB9o"). Qed.

Lemma c_eq0_nat : forall k : nat, Z.of_nat k < 2^64 ->
  c_eq (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 0) = (Z.of_nat k =? 0).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__with74__x1h84cstrh91zh:2Hkh;1bh<1kp;1p;2p;3p;4p;6p;7p;8g01:hj17Tg006Kj10Tg00BVj1<Tg00C4j2FTg00CQj22Tg0070j1RTg00mTj2=Tg00kaj2;Tg01OXj23Tg009lj35Tg00OCj2>Tg01=Tj1DTg00Idj2YTg00JLj3VTg00;^j1UTg002=j1QTg00KNj1PTg00LJj1MTg00Lhj1LTg00RCj29Tg00N6j46Tg010Dj3KTg00Naj2JTg00O]j2ITg00PIj3HTg00Phj4GTg00SJj2@Tg00Cmj2?Tg01P5j2ATg001_j68Tg00K0j2ETg00MSj2NTg009Jj1OTg01CDj2CTg01X\j2STg00^Bj7TTg00Rfj7XTg00^fj8WTg00_JR0f0R1'@p=1f1R2g00`hR3g00aGR4P4g00agR5P1g00bGFTp=4f2R6P3P4P4P5P2P1FXp=:f3R7P3P4P4P5P6P2P1GWp=Bg01A5%71g00B1R3#0R8#<R9%08#0#0#0#0R8#<R:'FR;'2g00_hR<%R8R8%72R=,=8R>';R?1=80R@,;8RA'3%76RB/30RC95<1X;<g00bgRDP=131A=5<CX9DPDP013B1=5<CX9D13=0,><PA%D2RA%1=RC1Y9:RB1209%1:120;RE[[RF%19RGg00clRHAV9:2UW0R:%1;\H^0GRGg00dHRH#URI%QHRH%PD%MDRJ%LDRKPD19D0RLg00f;RMPLC6,4KPDPLg00e4RN19D9=KD8R8C6,4K3:1JK5R5P1P6g00e[R9,><1I16=5<9dAHD02CGR9b2b5b61@00/?EP1b1b3b4b8,A0E8P?PAPCPBPFP:PGPIPH1ED2PJPKPDPLPM1ND3R3C6,4KRM%O4R4PKPDP3PNP8C6,4KR8P4A:KM8CBCBP5P9b2b5b6X7D%11122;%16126;'?[[^7DP1f5#7P7f4O3b1b3b4b8,A=E81C>@1S>@E8W:W<o"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac addi_nf l :=
  lazymatch l with
  | v_addi (v_addi ?x ?a) ?b =>
      let z := eval vm_compute in (a + b)%Z in
      lazymatch z with
      | 0%Z => addi_nf x
      | _ => addi_nf (v_addi x z)
      end
  | v_addi ?x 0%Z => addi_nf x
  | _ => l
  end.

Ltac call_side Hp Hag HI HW HS ::=
  cbv delta [ALLOC_STACK];
  lazymatch goal with
  | |- md_pure _ => mpure Hp
  | |- ms_vm _ = m_vmmaps _ => symmetry; apply with_vmmaps_vmmaps
  | |- magree _ _ => exact Hag
  | |- minv _ _ => exact HI
  | |- wtop _ => exact (minv_ceil _ _ HI)
  | |- bv_unsigned (getr _ _) = _ => sys_reg
  | |- bytes_le_to_Z ?b = _ =>
      match goal with
      | Hv : bytes_le_to_Z b = bv_unsigned (le_val b), Hc : c_eq (le_val b) _ = true |- _ =>
          rewrite Hv, (c_eq_eq _ _ Hc); vm_compute; reflexivity
      end
  | |- rdn _ _ _ _ = Some _ =>
      first [ assumption
            | eapply (magree_rd _ _ _ _ _ Hag (minv_lo64 _ _ HI)); eassumption ]
  | |- getr _ _ = ?v =>
      (* [comment removed for export] *)
      regnorm;
      lazymatch goal with |- ?l = ?r =>
        tryif has_evar r then
          (imm_norm;
           lazymatch goal with |- ?l1 = _ =>
             let l' := addi_nf l1 in
             tryif constr_eq l1 l' then reflexivity
             else (transitivity l';
                   [ rewrite ?v_addi_addi'; zsum_norm; rewrite ?v_addi_0;
                     first [reflexivity | klitsg; first [reflexivity | bveq]]
                   | reflexivity ])
           end)
        else (imm_norm; rewrite ?v_addi_addi', ?v_addi_0;
              first [reflexivity | apply v_addi_back; reflexivity | klitsg; first [reflexivity | bveq]])
      end
  | |- _ = negb (c_eq (getr _ _) _) => regnorm; first [ apply nosmall_word | vm_compute; reflexivity | reflexivity ]
  | |- bv_unsigned _ mod 16 = 0 => first [assumption | apply sp_mod16; [assumption | reflexivity | uaddr; alia]]
  | |- ret_ok _ => first [assumption | apply ret_ok_even; vm_compute; reflexivity]
  | |- wtop _ => exact (minv_ceil _ _ HI)
  | |- tsafe _ _ => first [ exact HS | exact (tsafe_bind_inv _ _ _ HS) ]
  | |- forall a : word, _ -> ?m a <> None => win_nn
  | |- @aslot_at _ _ _ => assumption
  | |- context [alloc_ceiling] => rewrite alloc_ceiling_val; uaddr; alia
  | |- _ => uaddr; alia
  end.

(* [comment removed for export] *)
Ltac mach_cutk_core HS Hag HI HW XTY PCF wl XR CUT Kx :=
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    set (Kx := K) in HS |- *;
    enough (CUT : forall (x : XTY) (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        XR x R' ->
        tsafe (Kx x s') P ->
        realizes segs (mkCfg (mkst R' (PCF x) mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (Kx x s') L));
    [ | join_intro_k Kx Hag HI HW HS ]
    end
  end end.
Tactic Notation "mach_cutk" constr(HS) constr(Hag) constr(HI) constr(HW)
    constr(XTY) constr(PCF) constr(wl) constr(XR) "as" ident(CUT) ident(Kx) :=
  mach_cutk_core HS Hag HI HW XTY PCF wl XR CUT Kx.

(* [comment removed for export] *)
Ltac cond_facts :=
  repeat match goal with
         | H : ?c = true |- context [?c'] => constr_eq c c'; lazymatch c with true => fail | _ => rewrite H end
         | H : ?c = false |- context [?c'] => constr_eq c c'; lazymatch c with false => fail | _ => rewrite H end
         end;
  cbv beta match delta [andb orb negb fst snd].

(* [comment removed for export] *)
Ltac bool_to_Z :=
  repeat match goal with
  | H : c_eq _ _ = true |- _ => rewrite c_eq_u in H; apply Z.eqb_eq in H
  | H : c_eq _ _ = false |- _ => rewrite c_eq_u in H; apply Z.eqb_neq in H
  | H : c_ltu _ _ = true |- _ => rewrite c_ltu_u in H; apply Z.ltb_lt in H
  | H : c_ltu _ _ = false |- _ => rewrite c_ltu_u in H; apply Z.ltb_ge in H
  | H : MallocOps.is0 _ = true |- _ => rewrite is0_u in H; apply Z.eqb_eq in H
  | H : MallocOps.is0 _ = false |- _ => rewrite is0_u in H; apply Z.eqb_neq in H
  end;
  repeat match goal with
  | H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
      lazymatch z with
      | bv_unsigned _ => fail
      | _ => let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 z)) in
             change (bv_unsigned (Z_to_bv 64 z)) with v in H
      end
  end.
Ltac blia := bool_to_Z; arith_only; lia.

(* [comment removed for export] *)
Ltac xr_extra := fail.
Ltac xr_tac :=
  cbv beta match; repeat split;
  try (first [ xr_extra
             | regnorm; imm_norm; rewrite ?v_addi_0; cond_facts;
               first [ reflexivity | klitsg; first [reflexivity | bveq] | assumption | xr_extra | alia ]
             | exfalso; blia ]).

Ltac use_cut_k CUT Kx Hag HI HS ::=
  lazymatch goal with
  | |- realizes _ _ (tshape (Kx ?x ?sb) _) =>
      eapply (CUT x sb); [ exact Hag | exact HI | win_same | keep_tac | xr_tac | exact HS ]
  end.

Ltac use_cut_kx CUT Kx Hag HI HS ::=
  lazymatch goal with
  | |- realizes _ _ (tshape (Kx ?x ?sb) _) =>
      eapply (CUT x sb); [ exact Hag | exact HI | win_pres | win_nn | keep_tac | xr_tac | exact HS ]
  end.

(* [comment removed for export] *)
Ltac mach_vjoin_core J wl XR CUT :=
  let J := eval vm_compute in J in
  let Jlit := constr:(@BV 64 J ltac:(vm_compute; exact I)) in
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) ?mdl) ?T =>
      enough (CUT : forall R' : bvmap 5 word,
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) -> XR R' ->
        realizes segs (mkCfg (mkst R' Jlit mmF rom) mdl) T)
  end.
Ltac vjoin_intro :=
  let R' := fresh "R" in let Hkeep := fresh "Hkeep" in let HX := fresh "HX" in
  intros R' Hkeep HX; keep_facts Hkeep; cbv beta in HX.
Tactic Notation "mach_vjoin" constr(J) constr(wl) constr(XR) "as" ident(CUT) :=
  mach_vjoin_core J wl XR CUT; [ | vjoin_intro ].

Ltac use_vcut CUT := eapply CUT; [ keep_tac | xr_tac ].

(* [comment removed for export] *)
Ltac mach_brc Hp HS :=
  branch_cond ltac:(fun t =>
    first
      [ match goal with Hc : ?t' = _ |- _ => unify t' t; mach_if Hp HS Hc end
      | check_closed_term t;
        let b := eval vm_compute in t in
        let Hc := fresh "Hc" in
        assert (Hc : t = b) by (vm_compute; reflexivity);
        mach_if Hp HS Hc; clear Hc
      | let Hc := fresh "Hc" in
        destruct (b_cases t) as [Hc|Hc]; mach_if Hp HS Hc ]).

(* [comment removed for export] *)
Ltac mach_pure Hp HS J :=
  let J := eval vm_compute in J in
  repeat (cur_pc ltac:(fun u =>
    tryif constr_eq u J then fail else
    cur_instr ltac:(fun w i =>
      lazymatch i with
      | Branch _ _ _ _ => mach_brc Hp HS
      | _ => mach Hp HS
      end))).

(* [comment removed for export] *)
Ltac mach_pload HS :=
  let bs := fresh "bs" in let Hok := fresh "Hok" in let Hrd := fresh "Hrd" in
  let Hv := fresh "Hv" in let EQ := fresh "EQ" in
  first
    [ destruct (tsafe_lbu_inv _ _ _ _ HS) as (bs & Hok & Hrd & EQ)
    | destruct (tsafe_ld_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ)
    | destruct (tsafe_lw_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ) ];
  rewrite EQ in HS; rewrite EQ; clear EQ;
  lazymatch type of Hrd with rdn _ ?m ?a ?n = Some _ =>
    match goal with
    | H' : rdn _ m a n = Some ?b0 |- _ =>
        tryif constr_eq b0 bs then fail else
          (rewrite H' in Hrd; injection Hrd as Hrd; subst bs; clear Hok)
    end
  end;
  mnorm HS.

(* [comment removed for export] *)
Ltac mnorm HS ::=
  repeat first
    [ progress (cbv beta match zeta delta [negb andb orb fst snd] in HS;
                cbv beta match zeta delta [negb andb orb fst snd])
    | progress (rewrite mbind_assoc in HS; rewrite mbind_assoc)
    | progress (rewrite mret_bind in HS; rewrite mret_bind)
    | progress (rewrite mbind_assoc_k in HS; rewrite mbind_assoc_k)
    | progress (rewrite mret_bind_k in HS; rewrite mret_bind_k)
    | progress (rewrite mbind_mlet in HS; rewrite mbind_mlet)
    | progress (snorm_in HS; rewrite ?upd_mem, ?upd_vm, ?upd_upd) ];
  try match goal with Hag : magree _ _ |- _ => snorm_in Hag end;
  try match goal with HI : minv _ _ |- _ => snorm_in HI end.

Ltac tnorm_eq ::=
  repeat first
    [ progress (cbv beta match zeta delta [negb andb orb fst snd])
    | progress (rewrite mbind_assoc)
    | progress (rewrite mret_bind)
    | progress (rewrite mbind_assoc_k)
    | progress (rewrite mret_bind_k)
    | progress (rewrite mbind_mlet)
    | progress (rewrite ?upd_mem, ?upd_vm, ?upd_upd) ];
  reflexivity.

(* [comment removed for export] *)
Ltac lits64 HS :=
  let one z :=
    let v := eval vm_compute in (2^64 - z)%Z in
    try change (Z_to_bv 64 (2^64 - z)) with (Z_to_bv 64 v) in HS |- * in
  one 1%Z; one 16%Z; one 20%Z; one 4096%Z.

(* [comment removed for export] *)
Ltac model_crash HS :=
  exfalso; clear -HS;
  cbv beta match delta [MallocTree.mbind mcrash tbind tsafe mlet] in HS;
  first [ exact HS | cbn in HS; exact HS ].

(* [comment removed for export] *)
Ltac in_zlist u l :=
  lazymatch l with
  | nil => fail
  | cons ?x ?t => tryif constr_eq u x then idtac else in_zlist u t
  end.
Ltac mach_pure_l Hp HS stops :=
  let stops := eval vm_compute in stops in
  repeat (cur_pc ltac:(fun u =>
    tryif in_zlist u stops then fail else
    cur_instr ltac:(fun w i =>
      lazymatch i with
      | Branch _ _ _ _ => mach_brc Hp HS
      | _ => mach Hp HS
      end))).

(* [comment removed for export] *)
Ltac mach_vlet_core J wl XR CUT HS :=
  lazymatch goal with
  | |- realizes _ _ (tshape (mlet ?E ?F ?sb) _) =>
      let XRE := constr:(XR E) in
      mach_vjoin_core J wl XRE CUT;
      [ | let R' := fresh "R" in let Hkeep := fresh "Hkeep" in let HX := fresh "HX" in
          let v := fresh "vj" in let HE := fresh "HvE" in
          intros R' Hkeep HX; keep_facts Hkeep; cbv beta in HX;
          remember E as v eqn:HE in *; clear HE;
          rewrite (mlet_eq v F) in HS |- *; cbv beta in HS; cbv beta; mnorm HS;
          revert HS; revert HX; revert v ]
  end.
(* [comment removed for export] *)
Tactic Notation "mach_vlet" constr(J) constr(wl) constr(XR) "as" ident(CUT) constr(HS) :=
  mach_vlet_core J wl XR CUT HS.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac pc_lit :=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst _ (@BV 64 _ _) _ _) _) _ => idtac
  | |- realizes _ _ _ => eapply rz_at_pc; [ | symmetry; pc_tac ]
  end.

(* [comment removed for export] *)
Ltac use_cut_kx CUT Kx Hag HI HS ::=
  lazymatch goal with
  | |- realizes _ _ (tshape (Kx ?x ?sb) _) =>
      eapply (CUT x sb);
      [ exact Hag | exact HI | win_pres | win_nn | keep_tac
      | hnf; xr_tac
      | exact HS ]
  end.

(* [comment removed for export] *)
Ltac piece_exit HK K Hag HI HS :=
  lazymatch goal with
  | |- realizes _ _ (tshape (K ?x ?sb) _) =>
      eapply rz_at_pc;
      [ eapply (HK x sb);
        [ exact Hag | exact HI | win_pres | win_nn | keep_tac | hnf; xr_tac | exact HS ]
      | bveq ]
  end.

(* [comment removed for export] *)
Ltac piece_intro Hag HI HW HS :=
  let x := fresh "x" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
  let Hag' := fresh "Hag" in let Hkeep := fresh "Hkeep" in let HJ := fresh "HJ" in let HJn := fresh "HJnn" in
  let HInew := fresh "HI" in let HX := fresh "HX" in let HP := fresh "HS" in
  first
    [ (* [comment removed for export] *)
      intros x s' mm' R' Hag' HInew HJ HJn Hkeep HX HP;
      lazymatch type of HP with tsafe _ _ => idtac end;
      uaddrH HJ; uaddrH HJn
    | (* [comment removed for export] *)
      intros x s' mm' R' Hag' HInew HJ Hkeep HX HP;
      lazymatch type of HP with tsafe _ _ => idtac end;
      uaddrH HJ ];
  clear HS Hag HI; rename HP into HS; rename Hag' into Hag; rename HInew into HI;
  note_win HI;
  frame_facts HW mm';
  keep_facts Hkeep;
  revert HS; revert HX; revert x.

(* [comment removed for export] *)
Ltac use_piece_core PL Hp Hag HI HW HS :=
  lazymatch type of HI with minv ?s0 _ =>
  cur_mstate HS ltac:(fun sb =>
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R _ ?mm ?rom) (with_vmmaps _ ?md)) _ =>
      eapply rz_at_pc;
      [ eapply (PL md R mm rom s0 sb);
        first [ lazymatch goal with |- forall (x : _) (s' : mstate), _ => piece_intro Hag HI HW HS end
              | call_side Hp Hag HI HW HS ]
      | bveq ]
  end) end.
Tactic Notation "use_piece" uconstr(PL) constr(Hp) constr(Hag) constr(HI) constr(HW) constr(HS) :=
  use_piece_core PL Hp Hag HI HW HS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac mach_pload_new HS :=
  let bs := fresh "pbs" in let Hok := fresh "Hpok" in let Hrd := fresh "Hprd" in
  let Hv := fresh "Hpv" in let EQ := fresh "EQ" in
  destruct (tsafe_ld_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ);
  rewrite EQ in HS; rewrite EQ; clear EQ; mnorm HS.

Ltac sys_calls Hp HS Hag HI HW t others :=
  let pmm := eval vm_compute in (bv_unsigned PC_MMAP) in
  let pmu := eval vm_compute in (bv_unsigned PC_MUNMAP) in
  let pmp := eval vm_compute in (bv_unsigned PC_MPROTECT) in
  tryif constr_eq t pmm then
    lazymatch goal with
    | |- realizes _ _ (tshape (MallocTree.mbind (sys_mmap ?k _) _ _) _) =>
        match goal with MM : forall k', mmap_stmt k' |- _ => mach_call Hp HS Hag HI HW (MM k) end
    | |- realizes _ _ (tshape (MallocTree.mbind (sys_mmap_fixed_none _ _) _ _) _) =>
        match goal with MF : mmap_fixed_stmt |- _ => mach_call Hp HS Hag HI HW MF end
    end
  else tryif constr_eq t pmu then
    match goal with MU : munmap_stmt |- _ => mach_call Hp HS Hag HI HW MU end
  else tryif constr_eq t pmp then
    (* [comment removed for export] *)
    mach_pload_new HS; mach_passert HS;
    match goal with MP : mprotect_stmt |- _ => mach_call Hp HS Hag HI HW MP end
  else others t.

(* [comment removed for export] *)
Ltac piece_run Hp HS Hag HI HW HK Hret calls K PCF :=
  repeat first
    [ progress (mrun_to_k Hp HS Hag HI HW HK Hret calls K PCF)
    | lazymatch goal with
      | |- realizes _ _ (tshape (MallocTree.mbind sys_brk_query _ _) _) => mach_sys_brk_query Hp HS Hag HI
      | |- realizes _ _ (tshape (MallocTree.mbind (sys_brk_grow _) _ _) _) => mach_sys_brk_grow Hp HS Hag HI
      end ].

(* [comment removed for export] *)
Ltac use_piece2_core PL a1 a2 Hp Hag HI HW HS :=
  lazymatch type of HI with minv ?s0 _ =>
  cur_mstate HS ltac:(fun sb =>
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R _ ?mm ?rom) (with_vmmaps _ ?md)) _ =>
      eapply rz_at_pc;
      [ eapply (PL md R mm rom s0 sb a1 a2);
        first [ lazymatch goal with |- forall (x : _) (s' : mstate), _ => piece_intro Hag HI HW HS end
              | call_side Hp Hag HI HW HS ]
      | bveq ]
  end) end.
Tactic Notation "use_piece2" uconstr(PL) constr(a1) constr(a2) constr(Hp) constr(Hag) constr(HI) constr(HW) constr(HS) :=
  use_piece2_core PL a1 a2 Hp Hag HI HW HS.

(* [comment removed for export] *)
Ltac keeps_facts Hk :=
  let one z :=
    let r := constr:(@BV 5 z I) in
    try (let H := fresh "Hk" in assert (H : getr _ r = getr _ r) by (apply Hk; cbv; tauto)) in
  one 1%Z; one 2%Z; one 3%Z; one 4%Z; one 8%Z; one 9%Z; one 10%Z; one 18%Z; one 19%Z; one 20%Z; one 21%Z;
  one 22%Z; one 23%Z; one 24%Z; one 25%Z; one 26%Z; one 27%Z.

(* [comment removed for export] *)
Lemma keeps_wreg : forall (wl : list Z) (R1 R2 : bvmap 5 word) (r : reg),
  keeps R1 R2 ->
  forallb (fun z => existsb (Z.eqb z) wl) [5;6;7;11;12;13;14;15;16;17;28;29;30;31]%Z = true ->
  wreg wl r = false -> getr R2 r = getr R1 r.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "p'0h02Hrh13Hinh21Hh31zh41rh54Hsubh61xh71Eh82Hkh92Hzh:2R1h;2R2h<1bi001bh=1eh>5lemmah?1oh@2wlp%0p;1p;2p;3p;6p;8g002=j1pTg006Kj1ATg00[Xj1LTg0070j1\Tg007Nj1bTg0013j2oTg02\1j2lTg01OXj1YTg00BVj1=Tg00;^j1cTg02\oj3[Tg02]Kj2mTg02]dj3kTg02^Uj3hTg00kaj2?Tg001_j6gj88Tg00]fj6^Tg009lj31Tg01eIj2]Tg00HKj1ZTg02_8j1eTg02`=j29Tg02O0j3XTg02OSj2VTg00OCj2WTg01B6R0j22Tg01BPj3HTg02``j3jTg00[8j3_Tg02a<j2iTg02b=j3aTg01Bjj3STg00bgR1f1R2f0R33jp=K%L3#=p=Jf2R4A_1235_1p=Qg00_hR5g00e[R6713p=O1i23g00`HR7515p=5Aa123p=C1?42=113p=nA1537p=ff4R8f3R9AX42331p=df5R:AX942718/23p=:g01lUR;9X23p=;f6R<?1:8A1942/23'2p=01V941V23518p=61?42=113#Zp=>A1:89A1423'2p=<A1:89A1423g00fbR='2'2p=P1W239H94p=Ig02bT9a23p=@A1423/2=p=MA1:891242;S3p=B1W239H949S:8p=NAS4239S89p=4A1123#Zp=FA1123p=3A1123/2=p=RA1189A1142/23'2p=71W13p=E1V891V4251:/]3p=DA1194A1123/2='2p=UA11891242;S3p=GAH4239S89p=T123=p=`%p1g00B1R>#AR?#LR@#\RA%A?RB#ARC#ARD#A#A#\#bRE'oRF%bARG1l42%Y3RH/K:X31%=@RI%L>RJ#ARK#=RL%LJRM#=RN%L@RO#=RP%AKRQ#=RR%LKRK#=RS%AMRT#=RU%LMRM#=RV%=DRD%JCRW%AT#=RX%JTRT%AM#=RY%JMRM%c13Q3Q3Q3Q3Q3Q3QRZ5[1#O15:41C3ZR[AnA:2R\f:R],KHX31R^=[1Z#Of<R_,KHR`X31P2O1#O\[^61Ra'mf;Rb,KHX31=[1Z#Of=Rc,KHX31P2O1#O\[^61;k3W>Ah1^ZP8O2PaP3P9P4O2%Y9/K]#OP1P8%O`X31P3f8R`,?ARaP4Eg%Ya/Kb#OP5f9Ra,?A#Y/K_%f3X<5P<P6P3E^A1567P5P6P5p-0P3g00clP=n0110000020000X=5P;P7P3E^P=1]=3b2b0b5b5b5W7%Z\R\eW9X31P\\[^31%e8PGP8PAg00_JR\P;19A\dPGP8PA%=>R>P;19A>dPGP8PA%=?R?P;19A?dPGP8PA%=JRJP;19AJdPGP8PA%=BR7P;19A7dPGP8PAPIP;19AIdPGP8PAPLP;19ALdPGP8PAPNP;19ANdPGP8PA%=CRCP;19ACdPGP8PA%LBRB#=R5P;19A5dPGP8PA%A@R@#=R6P;19A6dPGP8PAPPP;19APdPGP8PAPRP;19ARdPGP8PAPSP;19ASdPGP8PAPUP;19AUdPGP8PAPVP;19AVdPGP8PAPDP;19ADdPGP8PAPWP;19AWdPGP8PA%AB#=R^P;19A^dPGP8PA%JBRBP;19ABdPGP8PA%A@#=RHP;19AHdPGP8PA%J@R@P;19A@dPGP8PA%AO#=RdP;19AddPGP8PA%JOROP;19AOdPGP8PA%AQ#=ReP;19AedPGP8PA%JQRQP;19AQdPGP8PA%AK#=RfP;19AfdPGP8PA%JKRKP;19AKdPGP8PAPXP;19AXdPGP8PAPTP;19ATdPGP8PAPYP;19AYdPGP8PAPMP;19AMdDdE:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:E:P0AXA\;R\91G:PGP:1;A>R>PGP:1;A?R?PGP:1;AJRJPGP:1;A7R7PGP:1;AIR;PGP:1;ALRgPGP:1;ANRhPGP:1;ACRCPGP:1;A5R5PGP:1;A6R6PGP:1;APRiPGP:1;ARRjPGP:1;ASRkPGP:1;AURlPGP:1;AVRmPGP:1;ADRnPGP:1;AWRoPGP:1;A^R^PGP:1;ABRBPGP:1;AHRHPGP:1;A@R@PGP:1;AdRdPGP:1;AOROPGP:1;AeRePGP:1;AQRQPGP:1;AfRfPGP:1;AKRKPGP:1;AXRpPGP:1;ATRqPGP:1;AYRr1;AMRs91G:F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0PEf7RtP<P`P<D6P3A1G<\PGP\15b3A>A92\[^31RuPEPbP4P_P4D6]1]0X4G15]\A>A\2\[^311Vb\,WEW1W0PtP3P8P9G8W2P3O1PGP<P>PGP<P?PGP<PJPGP<P7PGP<P;PGP<PgPGP<PhPGP<PCPGP<P5PGP<P6PGP<PiPGP<PjPGP<PkPGP<PlPGP<PmPGP<PnPGP<PoPGP<P^PGP<PBPGP<PHPGP<P@PGP<PdPGP<POPGP<PePGP<PQPGP<PfPGP<PKPGP<PpPGP<PqPGP<PrA1G<sF0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P0A1Gt>PGPtP?PGPtPJPGPtP7PGPtP;PGPtPgPGPtPhPGPtPCPGPtP5PGPtP6PGPtPiPGPtPjPGPtPkPGPtPlPGPtPmPGPtPnPGPtPoPGPtP^PGPtPBPGPtPHPGPtP@PGPtPdPGPtPOPGPtPePGPtPQPGPtPfPGPtPKPGPtPpPGPtPqPGPtPrPGPtPsE<F0F0F0F0F0F0F0F0F0F0F0F0F0F0PEPaP`P]P`D6P3A1G`>PGP>15c3PEPcP4f>R9P4D6^1u]0X4G15_>A>A>2\[^31P]P>A1G>>PGP?P>PGPJP>PGP7P>PGPCP>PGP5P>PGP6P>PGP^P>PGPBP>PGPHP>PGP@P>PGPdP>PGPOP>PGPeP>PGPQP>PGPfP>PGPKP>EPF0F0F0F0F0F0F0PGP>CI1@G>eO2W1W0PaP3P<P:G8W2P3O1PGP`P?PGP`PJPGP`P7PGP`P;PGP`PgPGP`PhPGP`PCPGP`P5PGP`P6PGP`PiPGP`PjPGP`PkPGP`PlPGP`PmPGP`PnPGP`PoPGP`P^PGP`PBPGP`PHPGP`P@PGP`PdPGP`POPGP`PePGP`PQPGP`PfPGP`PKPGP`PpPGP`PqPGP`PrPGP`PsE<F0F0F0F0F0F0F0F0F0F0F0F0F0F0P0A1Ga?PGPaPJPGPaP7PGPaP;PGPaPgPGPaPhPGPaPCPGPaP5PGPaP6PGPaPiPGPaPjPGPaPkPGPaPlPGPaPmPGPaPnPGPaPoPGPaP^PGPaPBPGPaPHPGPaP@PGPaPdPGPaPOPGPaPePGPaPQPGPaPfPGPaPKPGPaPpPGPaPqPGPaPrA1GasF0F0F0F0F0F0F0F0F0F0F0F0F0F0PEPbP]P_P]D6P3A1G]?PGP?f?R:/53PEP:P4f@R<P4D6^1u]0X4G159?A>A?2\[^31P_P?PGP>P?A1G??R8PGPJP?PGP7P?PGPCP?PGP5P?PGP6P?PGP^P?PGPBP?PGPHP?PGP@P?PGPdP?PGPOP?PGPeP?PGPQP?PGPfP?AMGK?F0F0F0F0F0F0F0R\P8P\PGP?CIEB1@G?eO2W1W0PbP3P`PtG8W2P3O1PGP]PJPGP]P7PGP]P;PGP]PgPGP]PhPGP]PCPGP]P5PGP]P6PGP]PiPGP]PjPGP]PkPGP]PlPGP]PmPGP]PnPGP]PoPGP]P^PGP]PBPGP]PHPGP]P@PGP]PdPGP]POPGP]PePGP]PQPGP]PfPGP]PKPGP]PpPGP]PqPGP]PrA1G]sF0F0F0F0F0F0F0F0F0F0F0F0F0F0P0A1GbJPGPbP7PGPbP;PGPbPgPGPbPhPGPbPCPGPbP5PGPbP6PGPbPiPGPbPjPGPbPkPGPbPlPGPbPmPGPbPnPGPbPoPGPbP^PGPbPBPGPbPHPGPbP@PGPbPdPGPbPOPGPbPePGPbPQPGPbPfPGPbPKPGPbPpPGPbPqPGPbPrPGPbPsE<F0F0F0F0F0F0F0F0F0F0F0F0F0PEPcP_P9P_D6P3A1G_JPGPJfARt/53PEPtP4fBR`P4D6^1u]0X4G15<JA>AJ2\[^31P9PJPGP>PJA1G?JR\A1GJJR8PGP7PJPGPCPJPGP5PJPGP6PJPGP^PJPGPBPJPGPHPJPGP@PJPGPdPJPGPOPJPGPePJPGPQPJPGPfPJPGPKPJEPF0F0F0F0F0F0Rv'2RwP\PwP8PvPGPJENEB1@GJeO2W1W0PcP3P]PaG8W2P3O1PGP_P7PGP_P;PGP_PgPGP_PhPGP_PCPGP_P5PGP_P6PGP_PiPGP_PjPGP_PkPGP_PlPGP_PmPGP_PnPGP_PoPGP_P^PGP_PBPGP_PHPGP_P@PGP_PdPGP_POPGP_PePGP_PQPGP_PfPGP_PKPGP_PpPGP_PqPGP_PrPGP_PsE<F0F0F0F0F0F0F0F0F0F0F0F0F0P0A1Gc7PGPcP;PGPcPgPGPcPhPGPcPCPGPcP5PGPcP6PGPcPiPGPcPjPGPcPkPGPcPlPGPcPmPGPcPnPGPcPoPGPcP^PGPcPBPGPcPHPGPcP@PGPcPdPGPcPOPGPcPePGPcPQPGPcPfPGPcPKPGPcPpPGPcPqPGPcPrA1GcsF0F0F0F0F0F0F0F0F0F0F0F0F0PEP:P9P<P9D6P3A1G97PGP7fCRa/53PEPaP4fDR]P4D6^1u]0X4G15`7A>A72\[^31P<P7PGP>P7A1G?7RvA1GJ7R8A1G77RwPGPCP7PGP5P7PGP6P7PGP^P7PGPBP7PGPHP7PGP@P7PGPdP7PGPOP7PGPeP7PGPQP7PGPfP7AMGK7F0F0F0F0F0F0R\'2Rx'2RyPvPyP8PxPwP\PGP7CID4EB1@G7eO2W1W0P:P3P_PbG8W2P3O1PGP9P;PGP9PgPGP9PhPGP9PCPGP9P5PGP9P6PGP9PiPGP9PjPGP9PkPGP9PlPGP9PmPGP9PnPGP9PoPGP9P^PGP9PBPGP9PHPGP9P@PGP9PdPGP9POPGP9PePGP9PQPGP9PfPGP9PKPGP9PpPGP9PqPGP9PrA1G9sF0F0F0F0F0F0F0F0F0F0F0F0F0P0A1G:;PGP:PgPGP:PhPGP:PCPGP:P5PGP:P6PGP:PiPGP:PjPGP:PkPGP:PlPGP:PmPGP:PnPGP:PoPGP:P^PGP:PBPGP:PHPGP:P@PGP:PdPGP:POPGP:PePGP:PQPGP:PfPGP:PKPGP:PpPGP:PqPGP:PrPGP:PsE<F0F0F0F0F0F0F0F0F0F0F0F0PEPtP<P`P<D6P3A1G<;PGP;fERb/53PEPbP4fFR_P4D6^1u]0X4G15];1?A;R\/F2\[^31PEP]P;PbP;P3P\13I\PLP\PNP\PPP\PRP\PSP\PUP\PVP\PDP\PWP\PXP\PTP\PYP\1RM\D7D7D7D7D7D7%E\R;3H1C\ZeP;O3EDW1W0PtP3P9PcG8W2P3O1PGP<PgPGP<PhPGP<PCPGP<P5PGP<P6PGP<PiPGP<PjPGP<PkPGP<PlPGP<PmPGP<PnPGP<PoPGP<P^PGP<PBPGP<PHPGP<P@PGP<PdPGP<POPGP<PePGP<PQPGP<PfPGP<PKPGP<PpPGP<PqPGP<PrPGP<PsE<F0F0F0F0F0F0F0F0F0F0F0F0P0A1GtgPGPtPhPGPtPCPGPtP5PGPtP6PGPtPiPGPtPjPGPtPkPGPtPlPGPtPmPGPtPnPGPtPoPGPtP^PGPtPBPGPtPHPGPtP@PGPtPdPGPtPOPGPtPePGPtPQPGPtPfPGPtPKPGPtPpPGPtPqPGPtPrA1GtsF0F0F0F0F0F0F0F0F0F0F0F0PEPaP`P]P`D6P3A1G`gPGPgfGRc/53PEPcP4fHR9P4D6^1u]0X4G15_g1?AgR;/F2\[^31PEP_PgPcPgP3P;PIP;13L;RgPNP;PPP;PRP;PSP;PUP;PVP;PDP;PWP;PXP;PTP;PYP;PMP;CUD7D7D7D7D7R\%E;Rw9Hg\DG1C;ZePwO3EDW1W0PaP3P<P:G8W2P3O1PGP`PhPGP`PCPGP`P5PGP`P6PGP`PiPGP`PjPGP`PkPGP`PlPGP`PmPGP`PnPGP`PoPGP`P^PGP`PBPGP`PHPGP`P@PGP`PdPGP`POPGP`PePGP`PQPGP`PfPGP`PKPGP`PpPGP`PqPGP`PrA1G`sF0F0F0F0F0F0F0F0F0F0F0F0P0A1GahPGPaPCPGPaP5PGPaP6PGPaPiPGPaPjPGPaPkPGPaPlPGPaPmPGPaPnPGPaPoPGPaP^PGPaPBPGPaPHPGPaP@PGPaPdPGPaPOPGPaPePGPaPQPGPaPfPGPaPKPGPaPpPGPaPqPGPaPrPGPaPsE<F0F0F0F0F0F0F0F0F0F0F0PEPbP]P_P]D6P3A1G]hPGPhfIR:/53PEP:P4fJR<P4D6^1u]0X4G159h1?AhRw/F2\[^31PEP9PhP:PhP3PwPIPw13LwRh13NwR;PPPwPRPwPSPwPUPwPVPwPDPwPWPwPXPwPTPwPYPw1RMwD7D7D7D7D7R\'2RgPhPgP;P\%EwR\DTDG1CwZeP\O3EDW1W0PbP3P`PtG8W2P3O1PGP]PCPGP]P5PGP]P6PGP]PiPGP]PjPGP]PkPGP]PlPGP]PmPGP]PnPGP]PoPGP]P^PGP]PBPGP]PHPGP]P@PGP]PdPGP]POPGP]PePGP]PQPGP]PfPGP]PKPGP]PpPGP]PqPGP]PrPGP]PsE<F0F0F0F0F0F0F0F0F0F0F0P0A1GbCPGPbP5PGPbP6PGPbPiPGPbPjPGPbPkPGPbPlPGPbPmPGPbPnPGPbPoPGPbP^PGPbPBPGPbPHPGPbP@PGPbPdPGPbPOPGPbPePGPbPQPGPbPfPGPbPKPGPbPpPGPbPqPGPbPrA1GbsF0F0F0F0F0F0F0F0F0F0F0PEPcP_P9P_D6P3A1G_CPGPCfKRt/53PEPtP4fLR`P4D6^1u]0X4G15<CA>AC2\[^31P9PCPGP>PCA1G?CR\A1GJCRwA1G7CR;A1GCCRgPGP5PCPGP6PCPGP^PCPGPBPCPGPHPCPGP@PCPGPdPCPGPOPCPGPePCPGPQPCPGPfPCPGPKPCEPF0F0F0F0F0Rh'2Rx'2R8'2RyP\PyPwP8P;PxPgPhPGPCEND4EB1@GCeO2W1W0PcP3P]PaG8W2P3O1PGP_P5PGP_P6PGP_PiPGP_PjPGP_PkPGP_PlPGP_PmPGP_PnPGP_PoPGP_P^PGP_PBPGP_PHPGP_P@PGP_PdPGP_POPGP_PePGP_PQPGP_PfPGP_PKPGP_PpPGP_PqPGP_PrA1G_sF0F0F0F0F0F0F0F0F0F0F0P0A1Gc5PGPcP6PGPcPiPGPcPjPGPcPkPGPcPlPGPcPmPGPcPnPGPcPoPGPcP^PGPcPBPGPcPHPGPcP@PGPcPdPGPcPOPGPcPePGPcPQPGPcPfPGPcPKPGPcPpPGPcPqPGPcPrPGPcPsE<F0F0F0F0F0F0F0F0F0F0PEP:P9P<P9D6P3A1G95PGP5fMRa/53PEPaP4fNR]P4D6^1u]0X4G15`5A>A52\[^31P<P5PGP>P5A1G?5RhA1GJ5RgA1G75RxA1GC5R;A1G55R8PGP6P5PGP^P5PGPBP5PGPHP5PGP@P5PGPdP5PGPOP5PGPeP5PGPQP5PGPfP5AMGK5F0F0F0F0F0Rw'2Ry'2R\'2Rv'2RzPhPzPgPvPxP\P;PyP8PwPGP5CID4D4EB1@G5eO2W1W0P:P3P_PbG8W2P3O1PGP9P6PGP9PiPGP9PjPGP9PkPGP9PlPGP9PmPGP9PnPGP9PoPGP9P^PGP9PBPGP9PHPGP9P@PGP9PdPGP9POPGP9PePGP9PQPGP9PfPGP9PKPGP9PpPGP9PqPGP9PrPGP9PsE<F0F0F0F0F0F0F0F0F0F0P0A1G:6PGP:PiPGP:PjPGP:PkPGP:PlPGP:PmPGP:PnPGP:PoPGP:P^PGP:PBPGP:PHPGP:P@PGP:PdPGP:POPGP:PePGP:PQPGP:PfPGP:PKPGP:PpPGP:PqPGP:PrA1G:sF0F0F0F0F0F0F0F0F0F0PEPtP<P`P<D6P3A1G<6PGP6fORb/53PEPbP4fPR_P4D6^1u]0X4G15]6A>A62\[^31P`P6PGP>P6A1G?6RwA1GJ6R8A1G76RyA1GC6R;A1G56R\A1G66RxPGP^P6PGPBP6PGPHP6PGP@P6PGPdP6PGPOP6PGPeP6PGPQP6PGPfP6PGPKP6EPF0F0F0F0Rv'2Rg'2Rz'2Rh'2R{'2R|PwP|P8P{PyPhP;PzP\PgPxPvPGP6END4D4EB1@G6eO2W1W0PtP3P9PcG8W2P3O1PGP<PiPGP<PjPGP<PkPGP<PlPGP<PmPGP<PnPGP<PoPGP<P^PGP<PBPGP<PHPGP<P@PGP<PdPGP<POPGP<PePGP<PQPGP<PfPGP<PKPGP<PpPGP<PqPGP<PrA1G<sF0F0F0F0F0F0F0F0F0F0P0A1GtiPGPtPjPGPtPkPGPtPlPGPtPmPGPtPnPGPtPoPGPtP^PGPtPBPGPtPHPGPtP@PGPtPdPGPtPOPGPtPePGPtPQPGPtPfPGPtPKPGPtPpPGPtPqPGPtPrPGPtPsE<F0F0F0F0F0F0F0F0F0PEPaP`P]P`D6P3A1G`iPGPifQRc/53PEPcP4fRR9P4D6^1u]0X4G15_i1?AiRv/F2\[^31PEP_PiPcPiP3PvPIPv13LvRi13NvRx13PvRgPRPvPSPvPUPvPVPvPDPvPWPvPXPvPTPvPYPvPMPvCUD7D7D7D7R\'2Rz'2R;PiP;PxPz%EvRz9Hg\D4DG1CvZePzO3EDW1W0PaP3P<P:G8W2P3O1PGP`PjPGP`PkPGP`PlPGP`PmPGP`PnPGP`PoPGP`P^PGP`PBPGP`PHPGP`P@PGP`PdPGP`POPGP`PePGP`PQPGP`PfPGP`PKPGP`PpPGP`PqPGP`PrPGP`PsE<F0F0F0F0F0F0F0F0F0P0A1GajPGPaPkPGPaPlPGPaPmPGPaPnPGPaPoPGPaP^PGPaPBPGPaPHPGPaP@PGPaPdPGPaPOPGPaPePGPaPQPGPaPfPGPaPKPGPaPpPGPaPqPGPaPrA1GasF0F0F0F0F0F0F0F0F0PEPbP]P_P]D6P3A1G]jPGPjfSR:/53PEP:P4fTR<P4D6^1u]0X4G159j1?AjRz/F2\[^31PEP9PjP:PjP3PzPIPz13LzRj13NzRv13PzR\13RzRgPSPzPUPzPVPzPDPzPWPzPXPzPTPzPYPz1RMzD7D7D7D7Rx'2R;'2Ri'2RhPjPhPvPiP\P;PgPx%EzRxDTD4DG1CzZePxO3EDW1W0PbP3P`PtG8W2P3O1PGP]PkPGP]PlPGP]PmPGP]PnPGP]PoPGP]P^PGP]PBPGP]PHPGP]P@PGP]PdPGP]POPGP]PePGP]PQPGP]PfPGP]PKPGP]PpPGP]PqPGP]PrA1G]sF0F0F0F0F0F0F0F0F0P0A1GbkPGPbPlPGPbPmPGPbPnPGPbPoPGPbP^PGPbPBPGPbPHPGPbP@PGPbPdPGPbPOPGPbPePGPbPQPGPbPfPGPbPKPGPbPpPGPbPqPGPbPrPGPbPsE<F0F0F0F0F0F0F0F0PEPcP_P9P_D6P3A1G_kPGPkfURt/53PEPtP4fVR`P4D6^1u]0X4G15<k1?AkRx/F2\[^31PEP<PkPtPkP3PxPIPx13LxRk13NxRz13PxRg13RxR;13SxR\PUPxPVPxPDPxPWPxPXPxPTPxPYPxPMPxCUD7D7D7Ri'2Rv'2Rh'2Rj'2RyPkPyPzPjPgPhP;Pv%ExRv9H\iD4D4DG1CxZePvO3EDW1W0PcP3P]PaG8W2P3O1PGP_PlPGP_PmPGP_PnPGP_PoPGP_P^PGP_PBPGP_PHPGP_P@PGP_PdPGP_POPGP_PePGP_PQPGP_PfPGP_PKPGP_PpPGP_PqPGP_PrPGP_PsE<F0F0F0F0F0F0F0F0P0A1GclPGPcPmPGPcPnPGPcPoPGPcP^PGPcPBPGPcPHPGPcP@PGPcPdPGPcPOPGPcPePGPcPQPGPcPfPGPcPKPGPcPpPGPcPqPGPcPrA1GcsF0F0F0F0F0F0F0F0PEP:P9P<P9D6P3A1G9lPGPlfWRa/53PEPaP4fXR]P4D6^1u]0X4G15`l1?AlRv/F2\[^31PEP`PlPaPlP3PvPIPv13LvRl13NvRx13PvRi13RvR\13SvR;13UvRhPVPvPDPvPWPvPXPvPTPvPYPv1RMvD7D7D7Rg'2Rj'2Rz'2Ry'2Rk'2R{PlP{PxPkPiPyP\PzP;PjPhPg%EvRgDTD4D4DG1CvZePgO3EDW1W0P:P3P_PbG8W2P3O1PGP9PmPGP9PnPGP9PoPGP9P^PGP9PBPGP9PHPGP9P@PGP9PdPGP9POPGP9PePGP9PQPGP9PfPGP9PKPGP9PpPGP9PqPGP9PrA1G9sF0F0F0F0F0F0F0F0P0A1G:mPGP:PnPGP:PoPGP:P^PGP:PBPGP:PHPGP:P@PGP:PdPGP:POPGP:PePGP:PQPGP:PfPGP:PKPGP:PpPGP:PqPGP:PrPGP:PsE<F0F0F0F0F0F0F0PEPtP<P`P<D6P3A1G<mPGPmfYRb/53PEPbP4fZR_P4D6^1u]0X4G15]m1?AmRg/F2\[^31PEP]PmPbPmP3PgPIPg13LgRm13NgRv13PgRh13RgRj13SgR;13UgRz13VgR\PDPgPWPgPXPgPTPgPYPgPMPgCUD7D7Ry'2Ri'2Rk'2Rx'2R{'2Rl'2R8PmP8PvPlPhP{PjPxP;PkPzPi%EgRi9H\yD4D4D4DG1CgZePiO3EDW1W0PtP3P9PcG8W2P3O1PGP<PnPGP<PoPGP<P^PGP<PBPGP<PHPGP<P@PGP<PdPGP<POPGP<PePGP<PQPGP<PfPGP<PKPGP<PpPGP<PqPGP<PrPGP<PsE<F0F0F0F0F0F0F0P0A1GtnPGPtPoPGPtP^PGPtPBPGPtPHPGPtP@PGPtPdPGPtPOPGPtPePGPtPQPGPtPfPGPtPKPGPtPpPGPtPqPGPtPrA1GtsF0F0F0F0F0F0F0PEPaP`P]P`D6P3A1G`nPGPnf[Rc/53PEPcP4f\R9P4D6^1u]0X4G15_n1?AnRi/F2\[^31PEP_PnPcPnP3PiPIPi13LiRn13NiRg13PiRy13RiR\13SiRz13UiRk13ViR;13DiRxPWPiPXPiPTPiPYPi1RMiD7D7Rj'2R{'2Rh'2Rl'2Rv'2R8'2Rm'2R|PnP|PgPmPyP8P\PvPzPlPkPhP;P{PxPj%EiRjDTD4D4D4DG1CiZePjO3EDW1W0PaP3P<P:G8W2P3O1PGP`PoPGP`P^PGP`PBPGP`PHPGP`P@PGP`PdPGP`POPGP`PePGP`PQPGP`PfPGP`PKPGP`PpPGP`PqPGP`PrA1G`sF0F0F0F0F0F0F0P0A1GaoPGPaP^PGPaPBPGPaPHPGPaP@PGPaPdPGPaPOPGPaPePGPaPQPGPaPfPGPaPKPGPaPpPGPaPqPGPaPrPGPaPsE<F0F0F0F0F0F0PEPbP]P_P]D6P3A1G]oPGPof]R:/53PEP:P4f^R<P4D6^1u]0X4G159o1?AoRj/F2\[^31PEP9PoP:PoP3PjPIPj13LjRo13NjRi13PjRx13RjR{13SjR;13UjRh13VjRk13DjRl13WjRzPXPjPTPjPYPjPMPjCUD7Rv'2R\'2R8'2Ry'2Rm'2Rg'2R|'2Rn'2RwPoPwPiPnPxP|P{PgP;PmPhPyPkP8PlP\%EjR\9HzvD4D4D4D4DG1CjZeP\O3EDW1W0PbP3P`PtG8W2P3O1PGP]P^PGP]PBPGP]PHPGP]P@PGP]PdPGP]POPGP]PePGP]PQPGP]PfPGP]PKPGP]PpPGP]PqPGP]PrPGP]PsE<F0F0F0F0F0F0P0A1Gb^PGPbPBPGPbPHPGPbP@PGPbPdPGPbPOPGPbPePGPbPQPGPbPfPGPbPKPGPbPpPGPbPqPGPbPrA1GbsF0F0F0F0F0F0PEPcP_P9P_D6P3A1G_^PGP^f_Rt/53PEPtP4f`R`P4D6^1u]0X4G15<^A>A^2\[^31P9P^PGP>P^A1G?^R\A1GJ^RjA1G7^RvA1GC^RzA1G5^RlA1G6^R8A1G^^RkPGPBP^PGPHP^PGP@P^PGPdP^PGPOP^PGPeP^PGPQP^PGPfP^AMGK^F0F0F0F0Ry'2Rh'2Rm'2R;'2Rg'2R{'2R|P\P|PjP{PvPgPzP;PlPmP8PhPkPyPGP^CID4D4D4EB1@G^eO2W1W0PcP3P]PaG8W2P3O1PGP_PBPGP_PHPGP_P@PGP_PdPGP_POPGP_PePGP_PQPGP_PfPGP_PKPGP_PpPGP_PqPGP_PrA1G_sF0F0F0F0F0F0P0A1GcBPGPcPHPGPcP@PGPcPdPGPcPOPGPcPePGPcPQPGPcPfPGPcPKPGPcPpPGPcPqPGPcPrPGPcPsE<F0F0F0F0F0PEP:P9P<P9D6P3A1G9BPGPBfaRa/53PEPaP4fbR]P4D6^1u]0X4G15`BA>AB2\[^31P<PBPGP>PBA1G?BRyA1GJBRkA1G7BRhA1GCBR8A1G5BRmA1G6BRlA1G^BR;A1GBBRzPGPHPBPGP@PBPGPdPBPGPOPBPGPePBPGPQPBPGPfPBPGPKPBEPF0F0F0Rg'2Rv'2R{'2Rj'2R|'2R\'2Rx'2RnPyPnPkPxPhP\P8P|PmPjPlP{P;PvPzPgPGPBEND4D4D4EB1@GBeO2W1W0P:P3P_PbG8W2P3O1PGP9PHPGP9P@PGP9PdPGP9POPGP9PePGP9PQPGP9PfPGP9PKPGP9PpPGP9PqPGP9PrPGP9PsE<F0F0F0F0F0P0A1G:HPGP:P@PGP:PdPGP:POPGP:PePGP:PQPGP:PfPGP:PKPGP:PpPGP:PqPGP:PrA1G:sF0F0F0F0F0PEPtP<P`P<D6P3A1G<HPGPHfcRb/53PEPbP4fdR_P4D6^1u]0X4G15]HA>AH2\[^31P`PHPGP>PHA1G?HRgA1GJHRzA1G7HRvA1GCHR;A1G5HR{A1G6HRlA1G^HRjA1GBHRmA1GHHR|PGP@PHPGPdPHPGPOPHPGPePHPGPQPHPGPfPHAMGKHF0F0F0R8'2R\'2Rh'2Rx'2Rk'2Rn'2Ry'2Ri'2RwPgPwPzPiPvPyP;PnP{PkPlPxPjPhPmP\P|P8PGPHCID4D4D4D4EB1@GHeO2W1W0PtP3P9PcG8W2P3O1PGP<P@PGP<PdPGP<POPGP<PePGP<PQPGP<PfPGP<PKPGP<PpPGP<PqPGP<PrA1G<sF0F0F0F0F0P0A1Gt@PGPtPdPGPtPOPGPtPePGPtPQPGPtPfPGPtPKPGPtPpPGPtPqPGPtPrPGPtPsE<F0F0F0F0PEPaP`P]P`D6P3A1G`@PGP@feRc/53PEPcP4ffR9P4D6^1u]0X4G15_@A>A@2\[^31P]P@PGP>P@A1G?@R8A1GJ@R|A1G7@R\A1GC@RmA1G5@RhA1G6@RjA1G^@RxA1GB@RlA1GH@RkA1G@@R{PGPdP@PGPOP@PGPeP@PGPQP@PGPfP@PGPKP@EPF0F0Rn'2R;'2Ry'2Rv'2Ri'2Rz'2Rw'2Rg'2Ro'2R}P8P}P|PoP\PgPmPwPhPzPjPiPxPvPlPyPkP;P{PnPGP@END4D4D4D4EB1@G@eO2W1W0PaP3P<P:G8W2P3O1PGP`PdPGP`POPGP`PePGP`PQPGP`PfPGP`PKPGP`PpPGP`PqPGP`PrPGP`PsE<F0F0F0F0P0A1GadPGPaPOPGPaPePGPaPQPGPaPfPGPaPKPGPaPpPGPaPqPGPaPrA1GasF0F0F0F0PEPbP]P_P]D6P3A1G]dPGPdfgR:/53PEP:P4fhR<P4D6^1u]0X4G159dA>Ad2\[^31P_PdPGP>PdA1G?dS00A1GJdRnA1G7dR{A1GCdR;A1G5dRkA1G6dRyA1G^dRlA1GBdRvA1GHdRxA1G@dRiA1GddRjPGPOPdPGPePdPGPQPdPGPfPdAMGKdF0F0Rz'2Rh'2Rw'2Rm'2Rg'2R\'2Ro'2R|'2R}'2R8'2R~Q00P~PnP8P{P}P;P|PkPoPyP\PlPgPvPmPxPwPiPhPjPzPGPdCID4D4D4D4D4EB1@GdeO2W1W0PbP3P`PtG8W2P3O1PGP]POPGP]PePGP]PQPGP]PfPGP]PKPGP]PpPGP]PqPGP]PrA1G]sF0F0F0F0P0A1GbOPGPbPePGPbPQPGPbPfPGPbPKPGPbPpPGPbPqPGPbPrPGPbPsE<F0F0F0PEPcP_P9P_D6P3A1G_OPGPOfiRt/53PEPtP4fjR`P4D6^1u]0X4G15<OA>AO2\[^31P9POPGP>POA1G?OS00A1GJOS01A1G7OS02A1GCORzA1G5ORjA1G6ORhA1G^ORiA1GBORwA1GHORxA1G@ORmA1GdORvA1GOORgPGPePOPGPQPOPGPfPOPGPKPOEPF0Rl'2R\'2Ry'2Ro'2Rk'2R|'2R;'2R}'2R{'2R8'2Rn'2R~Q00P~Q01PnQ02P8PzP{PjP}PhP;PiP|PwPkPxPoPmPyPvP\PgPlPGPOEND4D4D4D4D4EB1@GOeO2W1W0PcP3P]PaG8W2P3O1PGP_PePGP_PQPGP_PfPGP_PKPGP_PpPGP_PqPGP_PrPGP_PsE<F0F0F0P0A1GcePGPcPQPGPcPfPGPcPKPGPcPpPGPcPqPGPcPrA1GcsF0F0F0PEP:P9P<P9D6P3A1G9ePGPefkRa/53PEPaP4flR]P4D6^1u]0X4G15`eA>Ae2\[^31P<PePGP>PeA1G?eS02A1GJeS01A1G7eS00A1GCeS03A1G5eS04A1G6eRlA1G^eRgA1GBeR\A1GHeRvA1G@eRyA1GdeRmA1GOeRoA1GeeRxPGPQPePGPfPeAMGKeF0Rk'2Rw'2R|'2Ri'2R;'2Rh'2R}'2Rj'2R{'2Rz'2R8'2Rn'2R~Q02P~Q01PnQ00P8Q03PzQ04P{PlPjPgP}P\PhPvP;PyPiPmP|PoPwPxPkPGPeCID4D4D4D4D4D4EB1@GeeO2W1W0P:P3P_PbG8W2P3O1PGP9PQPGP9PfPGP9PKPGP9PpPGP9PqPGP9PrA1G9sF0F0F0P0A1G:QPGP:PfPGP:PKPGP:PpPGP:PqPGP:PrPGP:PsE<F0F0PEPtP<P`P<D6P3A1G<QPGPQfmRb/53PEPbP4fnR_P4D6^1u]0X4G15]QA>AQ2\[^31P`PQPGP>PQA1G?QS04A1GJQS03A1G7QS00A1GCQS01A1G5QS02A1G6QS05A1G^QS06A1GBQRkA1GHQRxA1G@QRwA1GdQRoA1GOQR|A1GeQRmA1GQQRiPGPfPQPGPKPQEPRy'2R;'2Rv'2Rh'2R\'2R}'2Rg'2Rj'2Rl'2R{'2Rz'2R8'2Rn'2R~Q04P~Q03PnQ00P8Q01PzQ02P{Q05PlQ06PjPkPgPxP}PwP\PoPhP|PvPmP;PiPyPGPQEND4D4D4D4D4D4EB1@GQeO2W1W0PtP3P9PcG8W2P3O1PGP<PfPGP<PKPGP<PpPGP<PqPGP<PrPGP<PsE<F0F0P0A1GtfPGPtPKPGPtPpPGPtPqPGPtPrA1GtsF0F0PEPaP`P]P`D6P3A1G`fPGPffoRc/53PEPcP4fpR9P4D6^1u]0X4G15_fA>Af2\[^31P]PfPGP>PfA1G?fS06A1GJfS05A1G7fS02A1GCfS01A1G5fS00A1G6fS03A1G^fS04A1GBfS07A1GHfS08A1G@fRyA1GdfRiA1GOfR;A1GefRmA1GQfRvA1GffR|AMGKfRh'2Ro'2R\'2Rw'2R}'2Rx'2Rg'2Rk'2Rj'2Rl'2R{'2Rz'2R8'2Rn'2R~Q06P~Q05PnQ02P8Q01PzQ00P{Q03PlQ04PjQ07PkQ08PgPyPxPiP}P;PwPmP\PvPoP|PhPGPfCID4D4D4D4D4D4D4EB1@GfeO2W1W0PaP3P<P:G8W2P3O1PGP`PKPGP`PpPGP`PqPGP`PrA1G`sF0F0P0A1GaKPGPaPpPGPaPqPGPaPrPGPaPsE<F0PEPbP]P_P]D6P3A1G]KPGPKfqR:/53PEP:P4frR<P4D6^1u]0X4G159KA>AK2\[^31P_PKPGP>PKA1G?KR?A1GJKRJA1G7KR7A1GCKRCA1G5KR5A1G6KR6A1G^KR^A1GBKRBA1GHKRHA1G@KR@A1GdKRdA1GOKROA1GeKReA1GQKRQA1GfKRfA1GKKR>#`Rh'2R|'2Ro'2Rv'2R\'2Rm'2Rw'2R;'2R}'2Ri'2Rx'2Ry'2Rg'2Rk'2RjP?PjPJPkP7PgPCPyP5PxP6PiP^P}PBP;PHPwP@PmPdP\POPvPePoPQP|PfPhP>P=PGPKEND4D4D4D4D4D4D4EB1@GKeO2W1W0PbP3P`PtG8W2P3O1PGP]PpPGP]PqPGP]PrPGP]PsE<F0P0A1GbpPGPbPqPGPbPrA1GbsF0PEPcP_P9P_D6P3A1G_pPGPpfsRt/53PEPtP4ftR`P4D6^1u]0X4G15<p1?ApRK/F2\[^31PEP<PpPtPpP3PKPIPK13LKRp13NKR>13PKRh13RKRf13SKR|13UKRQ13VKRo13DKRe13WKRv13XKROPTPKPYPK1RMKD7R\'2Rd'2Rm'2R@'2Rw'2RH'2R;'2RB'2R}'2R^PpP^P>P}PhPBPfP;P|PHPQPwPoP@PePmPvPdPOP\%EKR\DTD4D4D4D4DG1CKZeP\O3EDW1W0PcP3P]PaG8W2P3O1PGP_PqPGP_PrA1G_sF0P0A1GcqPGPcPrPGPcPsE<PEP:P9P<P9D6P3A1G9qPGPqfuRa/53PEPaP4fvR]P4D6^1u]0X4G15`q1?AqR\/F2\[^31PEP`PqPaPqP3P\PIP\13L\Rq13N\Ra13P\RK13R\RO13S\Rd13U\Rv13V\Rm13D\Re13W\R@13X\Ro13T\RwPYP\PMP\CURQ'2RH'2R|'2R;'2Rf'2RB'2Rh'2R}'2R>'2R^'2RpPqPpPaP^PKP>POP}PdPhPvPBPmPfPeP;P@P|PoPH%E\RH9HwQD4D4D4D4D4DG1C\ZePHO3EDW1W0P:P3P_PbG8W2P3O1PGP9PrPGP9PsE<P0A1G:rA1G:sPEPtP<P`P<D6P3A1G<rPGPrfwR`/53PEP`P4fxP4D6^1u]0X4GRu15]r1?ArR4/F2\[^31PEP]PrP`PrP3P4PIP413L4Rr13N4R:13P4R013R4Rb13S4R_13U4RH13V4R\13D4RQ13W4Rw13X4Ro13T4R|13Y4R@1RM4R;'2Re'2Rf'2Rm'2RB'2Rv'2Rh'2Rd'2R}'2RO'2R>'2RKPrPKP:P>P0POPbP}P_PdPHPhP\PvPQPBPwPmPoPfP|PeP@P;%E4R;DTD4D4D4D4D4DG1C4ZeP;O3EDW1W0PtP3P9PcG8W2P3O1A1G<sPGPsPu15]s1?AsRA/F2\[^31PEP]PsP`PsP3PAPIPA13LARL13NARN13PARP13RARR13SARS13UARU13VARV13DARD13WARW13XARX13TART13YARY13MARM#`RI'2Rs'2R`'2R]'2RE'2R1'2R['2R2'2Ru'2RG'2R<'2R;PLP;PNP<PPPGPRPuPSP2PUP[PVP1PDPEPWP]PXP`PTPsPYPI%EARI9HM=D4D4D4D4D4D4DG1CAZePIO3EDW1W0PtP3P9PcG8W2P3O1n200100000021100011000W2P3O1n200100000021100011000W2P3O1n200100000021100011000W2P3O1n200100000021100011000W2P3O1n200100000021100011000W2P3O1n200100000021100011000W2P3O1n200100000021100011000W2P3O1n200100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000W2P3O1n201100000021100011000b?b1W0W5W8W4X;FW:W@o"). Qed.

(* [comment removed for export] *)
Definition NONCS : list Z := [0;1;5;6;7;10;11;12;13;14;15;16;17;28;29;30;31]%Z.

Lemma callee_saved_of_wreg : forall (wl : list Z) (r : reg),
  forallb (fun z => existsb (Z.eqb z) wl) NONCS = true ->
  wreg wl r = false -> AllocIface.callee_saved r.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep3 ()) [] "p'0h02H0h11Hh21mh31nh41rh52Hrh64Hsubh71eh81oh92wlh:1zi001bp;1p;3p;2p;5p;6p;7p;4g002=j1eTg006Kj1ITg00[Xj1GTg0070j1YTg007Nj1dTg02\oj3\Tg02a<j2STg02cXj5XTg02_8j1VTg02`=j27Tg00BVj1>Tg02O0j3PTg009lj31Tg00kaj22Tg00SJj24Tg00;^j1ZTg00[8j3QTg00]fj6WTg001_j76Tg00OCj2MTg01BPj3NTg01B6R0j23Tg01Bjj3LTg00CmR1j2ATg01L@j2cTg02d]j1bTg01OXj1TTg02``j3UTg01eIj2`Tg01J^j2]Tg02D`j4aTg00bgR2f1R3#Tf0R43Up=_g00_hR5g00e[R6714p=[g00`HR79154p=R%I4#>p=K%G4#>p=Jf4R8f3R9f2R:?P3431p=^f5R;AP9:3718/34p=9g01lUR<9P34p=:f6R=?1;8A19:3/34'3p=01A34,3:p=O1334,3:p=EAQ2349Q2:p=F%T3=U24=157p=5A1=;8149:1434'A'3p=<149:1434'Ap=;A189:/33/`4p=?A1;89A1:34'3p=8A1;891334,3:'3p=CA19:3/34,38,3;p=HA1;8913:3;L4p=@AL:349L89p=B1]34=156p==f7R>P9P:P3P4Ca9L;87L=p=D%e2g00B1R?#IR@#GRA#YRB#dRC1_4:X:2g02e`RD5\2#[1S:3#RP9PDP:P3P4DX1SD:#R%V9PCP9PBg00_JRDP<17BDdPCP9PB%>?REP<17BEdPCP9PB%>@RFP<17BFdPCP9PB%G?R?#>RGP<17BGdPCP9PB%I@R@#>RHP<17BHdPCP9PB%>ARIP<17BIdPCP9PB%I?RJ#>RKP<17BKdPCP9PB%G?R?#>RLP<17BLdPCP9PB%I@RM#>RNP<17BNdPCP9PB%G@R@#>ROP<17BOdPCP9PB%IARP#>RQP<17BQdPCP9PB%GARA#>RRP<17BRdPCP9PB%IJRS#>RTP<17BTdPCP9PB%GJRJ#>RUP<17BUdPCP9PB%I?RV#>RWP<17BWdPCP9PB%G?R?#>RXP<17BXdPCP9PB%KMRYP<17BYdPCP9PB%JMRMP<17BMdPCP9PB%K@RZP<17BZdPCP9PB%J@R@P<17B@dPCP9PB%KPR[P<17B[dPCP9PB%JPRPP<17BPdPCP9PB%KAR\P<17B\dPCP9PB%JARAP<17BAdPCP9PB%KSR]P<17B]dPCP9PB%JSRSP<17BSdPCP9PB%KJR^P<17B^dPCP9PB%JJRJP<17BJdPCP9PB%KVR_P<17B_dPCP9PB%JVRVP<17BVdPCP9PB%K?R`P<17B`dPCP9PB%J?R?P<17B?dD^E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9E9P0APBD<Ra91C8PCP81:BERbPCP81:BFRFPCP81:BGRGPCP81:BHRHPCP81:BIRcPCP81:BKRdPCP81:BLRePCP81:BNRNPCP81:BOROPCP81:BQRfPCP81:BRRgPCP81:BTRhPCP81:BURiPCP81:BWRjPCP81:BXRkPCP81:BYRlPCP81:BMRmPCP81:BZRnPCP81:B@R@PCP81:B[R[PCP81:BPRPPCP81:B\R\PCP81:BARAPCP81:B]R]PCP81:BSRSPCP81:B^R^PCP81:BJRoPCP81:B_RpPCP81:BVRqPCP81:B`Rr1:B?Rs91C8F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0A1C;FR8A1C;GRtA1C;HRuA1C;NRvA1C;ORw12B;Rx,4Z14xJ3O3E3EP4A1C;aPCPa12B4%Z29F`?9F_V9FYM9FWX9FTU9FQR9FKL9FEI9Q2DRD'5PCP3PFPCP3PGPCP3PHPCP3PNPCP3POPZ12B3RIPIPJF<F0F0]1X4CRI12BaRE/5DP5P6P5p-0P4g00clg00fbRLn0110000020000X75P<P7P4EWR7PLPCPaPFPCPaPGPCPaPHPCPaPNPCPaPOPZPEPEPJC;F0F0P4D?b0W1P=P4P9F6W0P4O1PCP;PbP8PtPuA1C;cPCP;PdPCP;PePvPwPCP;PfPCP;PgPCP;PhPCP;PiPCP;PjPCP;PkPCP;PlPCP;PmPCP;PnPCP;P@PCP;P[PCP;PPPCP;P\PCP;PAPCP;P]PCP;PSPCP;P^PCP;PoPCP;PpPCP;PqPCP;PrPCP;PsE8F0F0F0F0F0F0F0F0F0F0ECEHECP0A1C=bPCP=PFPCP=PGPCP=PHPCP=PcPCP=PdPCP=PePCP=PNPCP=POPCP=PfPCP=PgPCP=PhPCP=PiPCP=PjPCP=PkPCP=PlPCP=PmPCP=PnPCP=P@PCP=P[PCP=PPPCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrPCP=PsE8F0F0F0F0F0F0F0F0F0F0F0F0F0F0A1C>FR=A1C>GRwA1C>HRvA1C>NRuA1C>ORt12B>R8,4Z148J3O3E3EP4A1C>bPCPbPI12BbR8/5DP7PLPCPbPFPCPbPGPCPbPHPCPbPNPCPbPOPZP8P8PJC;F0F0P4D?b0W1f8R8P4P;F6W0P4O1PvA1C>cPCP>PdPCP>PePuPtPCP>PfPCP>PgPCP>PhPCP>PiPCP>PjPCP>PkPCP>PlPCP>PmPCP>PnPCP>P@PCP>P[PCP>PPPCP>P\PCP>PAPCP>P]PCP>PSPCP>P^PCP>PoPCP>PpPCP>PqPCP>PrPCP>PsE8F0F0F0F0F0F0F0F0F0F0ECEH9E=wP0A1C8FPCP8PGPCP8PHPCP8PcPCP8PdPCP8PePCP8PNPCP8POPCP8PfPCP8PgPCP8PhPCP8PiPCP8PjPCP8PkPCP8PlPCP8PmPCP8PnPCP8P@PCP8P[PCP8PPPCP8P\PCP8PAPCP8P]PCP8PSPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrA1C8sF0F0F0F0F0F0F0F0F0F0F0F0F0F0f9R8=1CFRwA1C8GR=A1C8HRtA1C8NRuA1C8ORv12B8R;,4Z14;J3O3E3EP4PCPFPI12BFR;/5DA1CFFPCPFPGPCPFPHPCPFPNPCPFPOPZP;P;PJC;F0F01MCF3NW1f:R;P4P>F6X0wP4O1P=PtPCP8PcPCP8PdPCP8PePuPvPCP8PfPCP8PgPCP8PhPCP8PiPCP8PjPCP8PkPCP8PlPCP8PmPCP8PnPCP8P@PCP8P[PCP8PPPCP8P\PCP8PAPCP8P]PCP8PSPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrA1C8sF0F0F0F0F0F0F0F0F0F0EHF0EHP0A1C;GPCP;PHPCP;PcPCP;PdPCP;PePCP;PNPCP;POPCP;PfPCP;PgPCP;PhPCP;PiPCP;PjPCP;PkPCP;PlPCP;PmPCP;PnPCP;P@PCP;P[PCP;PPPCP;P\PCP;PAPCP;P]PCP;PSPCP;P^PCP;PoPCP;PpPCP;PqPCP;PrPCP;PsE8F0F0F0F0F0F0F0F0F0F0F0F0F0PCf;R;PFA1C;GRvA1C;HRuA1C;NRtA1C;OR=PZ12B;RwPwPJC;3EECP4PCPGPI12BGRw/5DPCPGPFA1CGGR>PCPGPHPCPGPNPCPGPOPZPwPwPJF<F0Rw1MCG9N>wE@W1f<RwP4P8F6X0vP4O1PuA1C;cPCP;PdPCP;PePtP=PCP;PfPCP;PgPCP;PhPCP;PiPCP;PjPCP;PkPCP;PlPCP;PmPCP;PnPCP;P@PCP;P[PCP;PPPCP;P\PCP;PAPCP;P]PCP;PSPCP;P^PCP;PoPCP;PpPCP;PqPCP;PrPCP;PsE8F0F0F0F0F0F0F0F0F0F0ECEHP0A1CwHPCPwPcPCPwPdPCPwPePCPwPNPCPwPOPCPwPfPCPwPgPCPwPhPCPwPiPCPwPjPCPwPkPCPwPlPCPwPmPCPwPnPCPwP@PCPwP[PCPwPPPCPwP\PCPwPAPCPwP]PCPwPSPCPwP^PCPwPoPCPwPpPCPwPqPCPwPrA1CwsF0F0F0F0F0F0F0F0F0F0F0F0F0PCf=RwPFPCPwPGA1CwHR=A1CwNRtA1CwORu12BwRv,4Z14vJ3O3EF0P4PCPHPI12BHRv/5DPCPHPFA1CHGR8A1CHHR>PCPHPNPCPHPOPZPvPvPJC;F0Rv'3Rb1MCH9N>v9L8bE@W1f>RbP4P;F6X0=P4O1PCPwPcPCPwPdPCPwPePtPuPCPwPfPCPwPgPCPwPhPCPwPiPCPwPjPCPwPkPCPwPlPCPwPmPCPwPnPCPwP@PCPwP[PCPwPPPCPwP\PCPwPAPCPwP]PCPwPSPCPwP^PCPwPoPCPwPpPCPwPqPCPwPrPCPwPsE8F0F0F0F0F0F0F0F0F0F0ECF0P0A1CbcPCPbPdPCPbPePCPbPNPCPbPOPCPbPfPCPbPgPCPbPhPCPbPiPCPbPjPCPbPkPCPbPlPCPbPmPCPbPnPCPbP@PCPbP[PCPbPPPCPbP\PCPbPAPCPbP]PCPbPSPCPbP^PCPbPoPCPbPpPCPbPqPCPbPrPCPbPsE8F0F0F0F0F0F0F0F0F0F0F0F0PCf?RbPFPCPbPGPCPbPHA1CbNRuA1CbORtPZ12BbR=P=PJC;ECF0P4A1CbcPCPcPI12BcR=/5DP7PLPCPcPFPCPcPGPCPcPHPCPcPNPCPcPOPZP=P=PJC;F0F0P4D?b0W1f@R=P4PwF6W0P4O1PCPbPdPCPbPePuPtPCPbPfPCPbPgPCPbPhPCPbPiPCPbPjPCPbPkPCPbPlPCPbPmPCPbPnPCPbP@PCPbP[PCPbPPPCPbP\PCPbPAPCPbP]PCPbPSPCPbP^PCPbPoPCPbPpPCPbPqPCPbPrA1CbsF0F0F0F0F0F0F0F0F0F0EHF0P0A1C=dPCP=PePCP=PNPCP=POPCP=PfPCP=PgPCP=PhPCP=PiPCP=PjPCP=PkPCP=PlPCP=PmPCP=PnPCP=P@PCP=P[PCP=PPPCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrA1C=sF0F0F0F0F0F0F0F0F0F0F0F0PCfAR=PFPCP=PGPCP=PHA1C=NRtA1C=ORuPZ12B=RwPwPJC;ECF0P4A1C=dPCPdPI12BdRw/5DP7PLPCPdPFPCPdPGPCPdPHPCPdPNPCPdPOPZPwPwPJC;F0F0P4D?b0W1fBRwP4PbF6W0P4O1PCP=PePtPuPCP=PfPCP=PgPCP=PhPCP=PiPCP=PjPCP=PkPCP=PlPCP=PmPCP=PnPCP=P@PCP=P[PCP=PPPCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrPCP=PsE8F0F0F0F0F0F0F0F0F0F0ECP0A1CwePCPwPNPCPwPOPCPwPfPCPwPgPCPwPhPCPwPiPCPwPjPCPwPkPCPwPlPCPwPmPCPwPnPCPwP@PCPwP[PCPwPPPCPwP\PCPwPAPCPwP]PCPwPSPCPwP^PCPwPoPCPwPpPCPwPqPCPwPrPCPwPsE8F0F0F0F0F0F0F0F0F0F0F0PCfCRwPFPCPwPGPCPwPHA1CwNRuA1CwORtPZ12BwRbPbPJC;ECF0P4A1CwePCPePI12BeRb/5DP7PLPCPePFPCPePGPCPePHPCPePNPCPePOPZPbPbPJC;F0F0P4D?b0W1fDRbP4P=F6W0P4O1PuPtPCPwPfPCPwPgPCPwPhPCPwPiPCPwPjPCPwPkPCPwPlPCPwPmPCPwPnPCPwP@PCPwP[PCPwPPPCPwP\PCPwPAPCPwP]PCPwPSPCPwP^PCPwPoPCPwPpPCPwPqPCPwPrA1CwsF0F0F0F0F0F0F0F0F0F0EHP0A1CbNPCPbPOPCPbPfPCPbPgPCPbPhPCPbPiPCPbPjPCPbPkPCPbPlPCPbPmPCPbPnPCPbP@PCPbP[PCPbPPPCPbP\PCPbPAPCPbP]PCPbPSPCPbP^PCPbPoPCPbPpPCPbPqPCPbPrA1CbsF0F0F0F0F0F0F0F0F0F0F0PCfERbPFPCPbPGPCPbPHA1CbNRtA1CbORuPZ12BbR=P=PJC;ECF0P4PCPNPI12BNR=/5DPCPNPFA1CNGReA1CNHRdA1CNNRcPCPNPOPZP=P=PJF<R='3R;'3R8PeP8PdP;1MCN9Nc=DBE@W1fFR=P4PwF6X0tP4O1PuA1CbfPCPbPgPCPbPhPCPbPiPCPbPjPCPbPkPCPbPlPCPbPmPCPbPnPCPbP@PCPbP[PCPbPPPCPbP\PCPbPAPCPbP]PCPbPSPCPbP^PCPbPoPCPbPpPCPbPqPCPbPrPCPbPsE8F0F0F0F0F0F0F0F0F0EHP0A1C=OPCP=PfPCP=PgPCP=PhPCP=PiPCP=PjPCP=PkPCP=PlPCP=PmPCP=PnPCP=P@PCP=P[PCP=PPPCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrPCP=PsE8F0F0F0F0F0F0F0F0F0F0PCfGR=PFPCP=PGPCP=PHPCP=PNA1C=ORu12B=Rt,4Z14tJ3OF0F0P4PCPOPI12BORt/5DPCPOPFA1COGRwA1COHRcA1CONR;A1COORdPZPtPtPJC;Rt'3R8'3Re'3RvPwPvPcPe1MCO9Ndt9L;8DBE@W1fHR8P4PbF6X0uP4O1PCP=PfPCP=PgPCP=PhPCP=PiPCP=PjPCP=PkPCP=PlPCP=PmPCP=PnPCP=P@PCP=P[PCP=PPPCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrPCP=PsE8F0F0F0F0F0F0F0F0F0F0P0A1C8fPCP8PgPCP8PhPCP8PiPCP8PjPCP8PkPCP8PlPCP8PmPCP8PnPCP8P@PCP8P[PCP8PPPCP8P\PCP8PAPCP8P]PCP8PSPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrA1C8sF0F0F0F0F0F0F0F0F0F0PCfIR8PFPCP8PGPCP8PHPCP8PNPCP8POPZ12B8RuPuPJF<F0F0P4A1C8fPCPfPI12BfRu/5DP7PLPCPfPFPCPfPGPCPfPHPCPfPNPCPfPOPZPuPuPJC;F0F0P4D?b0W1fJRuP4P=F6W0P4O1PCP8PgPCP8PhPCP8PiPCP8PjPCP8PkPCP8PlPCP8PmPCP8PnPCP8P@PCP8P[PCP8PPPCP8P\PCP8PAPCP8P]PCP8PSPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrA1C8sF0F0F0F0F0F0F0F0F0F0P0A1CugPCPuPhPCPuPiPCPuPjPCPuPkPCPuPlPCPuPmPCPuPnPCPuP@PCPuP[PCPuPPPCPuP\PCPuPAPCPuP]PCPuPSPCPuP^PCPuPoPCPuPpPCPuPqPCPuPrPCPuPsE8F0F0F0F0F0F0F0F0F0PCfKRuPFPCPuPGPCPuPHPCPuPNPCPuPOPZ12BuR=P=PJF<F0F0P4A1CugPCPgPI12BgR=/5DP7PLPCPgPFPCPgPGPCPgPHPCPgPNPCPgPOPZP=P=PJC;F0F0P4D?b0W1fLR=P4P8F6W0P4O1PCPuPhPCPuPiPCPuPjPCPuPkPCPuPlPCPuPmPCPuPnPCPuP@PCPuP[PCPuPPPCPuP\PCPuPAPCPuP]PCPuPSPCPuP^PCPuPoPCPuPpPCPuPqPCPuPrPCPuPsE8F0F0F0F0F0F0F0F0F0P0A1C=hPCP=PiPCP=PjPCP=PkPCP=PlPCP=PmPCP=PnPCP=P@PCP=P[PCP=PPPCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrA1C=sF0F0F0F0F0F0F0F0F0PCfMR=PFPCP=PGPCP=PHPCP=PNPCP=POPZ12B=R8P8PJF<F0F0P4A1C=hPCPhPI12BhR8/5DP7PLPCPhPFPCPhPGPCPhPHPCPhPNPCPhPOPZP8P8PJC;F0F0P4D?b0W1fNR8P4PuF6W0P4O1PCP=PiPCP=PjPCP=PkPCP=PlPCP=PmPCP=PnPCP=P@PCP=P[PCP=PPPCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrA1C=sF0F0F0F0F0F0F0F0F0P0A1C8iPCP8PjPCP8PkPCP8PlPCP8PmPCP8PnPCP8P@PCP8P[PCP8PPPCP8P\PCP8PAPCP8P]PCP8PSPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrPCP8PsE8F0F0F0F0F0F0F0F0PCfOR8PFPCP8PGPCP8PHPCP8PNPCP8POPZ12B8RuPuPJF<F0F0P4A1C8iPCPiPI12BiRu/5DP7PLPCPiPFPCPiPGPCPiPHPCPiPNPCPiPOPZPuPuPJC;F0F0P4D?b0W1fPRuP4P=F6W0P4O1PCP8PjPCP8PkPCP8PlPCP8PmPCP8PnPCP8P@PCP8P[PCP8PPPCP8P\PCP8PAPCP8P]PCP8PSPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrPCP8PsE8F0F0F0F0F0F0F0F0P0A1CujPCPuPkPCPuPlPCPuPmPCPuPnPCPuP@PCPuP[PCPuPPPCPuP\PCPuPAPCPuP]PCPuPSPCPuP^PCPuPoPCPuPpPCPuPqPCPuPrA1CusF0F0F0F0F0F0F0F0PCfQRuPFPCPuPGPCPuPHPCPuPNPCPuPOPZ12BuR=P=PJF<F0F0P4A1CujPCPjPI12BjR=/5DP7PLPCPjPFPCPjPGPCPjPHPCPjPNPCPjPOPZP=P=PJC;F0F0P4D?b0W1fRR=P4P8F6W0P4O1PCPuPkPCPuPlPCPuPmPCPuPnPCPuP@PCPuP[PCPuPPPCPuP\PCPuPAPCPuP]PCPuPSPCPuP^PCPuPoPCPuPpPCPuPqPCPuPrA1CusF0F0F0F0F0F0F0F0P0A1C=kPCP=PlPCP=PmPCP=PnPCP=P@PCP=P[PCP=PPPCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrPCP=PsE8F0F0F0F0F0F0F0PCfSR=PFPCP=PGPCP=PHPCP=PNPCP=POPZ12B=R8P8PJF<F0F0P4A1C=kPCPkPI12BkR8/5DP7PLPCPkPFPCPkPGPCPkPHPCPkPNPCPkPOPZP8P8PJC;F0F0P4D?b0W1fTR8P4PuF6W0P4O1PCP=PlPCP=PmPCP=PnPCP=P@PCP=P[PCP=PPPCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrPCP=PsE8F0F0F0F0F0F0F0P0A1C8lPCP8PmPCP8PnPCP8P@PCP8P[PCP8PPPCP8P\PCP8PAPCP8P]PCP8PSPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrA1C8sF0F0F0F0F0F0F0PCfUR8PFPCP8PGPCP8PHPCP8PNPCP8POPZ12B8RuPuPJF<F0F0P4A1C8lPCPlPI12BlRu/5DP7PLPCPlPFPCPlPGPCPlPHPCPlPNPCPlPOPZPuPuPJC;F0F0P4D?b0W1fVRuP4P=F6W0P4O1PCP8PmPCP8PnPCP8P@PCP8P[PCP8PPPCP8P\PCP8PAPCP8P]PCP8PSPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrA1C8sF0F0F0F0F0F0F0P0A1CumPCPuPnPCPuP@PCPuP[PCPuPPPCPuP\PCPuPAPCPuP]PCPuPSPCPuP^PCPuPoPCPuPpPCPuPqPCPuPrPCPuPsE8F0F0F0F0F0F0PCfWRuPFPCPuPGPCPuPHPCPuPNPCPuPOPZ12BuR=P=PJF<F0F0P4A1CumPCPmPI12BmR=/5DP7PLPCPmPFPCPmPGPCPmPHPCPmPNPCPmPOPZP=P=PJC;F0F0P4D?b0W1fXR=P4P8F6W0P4O1PCPuPnPCPuP@PCPuP[PCPuPPPCPuP\PCPuPAPCPuP]PCPuPSPCPuP^PCPuPoPCPuPpPCPuPqPCPuPrPCPuPsE8F0F0F0F0F0F0P0A1C=nPCP=P@PCP=P[PCP=PPPCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrA1C=sF0F0F0F0F0F0PCfYR=PFPCP=PGPCP=PHPCP=PNPCP=POPZ12B=R8P8PJF<F0F0P4A1C=nPCPnPI12BnR8/5DPCPnPFA1CnGRmA1CnHRlA1CnNRkA1CnORn14Z8Rj148JRi'ARh'3Rg'3Rf'3RbPmPbPlPfPkPgPnPhPjPiP11=3414:3[R114341=:3Ri[149:\i1c34P3n2001000000120000000X22X32R3P1^22^32R2P4PZP81M56R61=Z8dO3b0P3P2P4P8PJP61=8JdO3b0GDDBE@W1fZR8P4PuF6W0P4O1PCP=P@PCP=P[PCP=PPPCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrA1C=sF0F0F0F0F0F0P0A1C8@PCP8P[PCP8PPPCP8P\PCP8PAPCP8P]PCP8PSPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrPCP8PsE8F0F0F0F0F0PCf[R8PFPCP8PGPCP8PHPCP8PNPCP8POPZ12B8RuPuPJF<F0F0P4A1C8@PCP@PI12B@Ru/5DPCP@PFA1C@GR5A1C@HR1A1C@NRiA1C@OR@14ZuR:14uJRj'ARh'3Rn'3Rg'3RkP5PkP1PgPiPnP@PhP:PjP3P2P4PZPuP61=ZudO3b0P3P2P4PuPJP61=uJdO3b0GDDBE@W1f\RuP4P=F6W0P4O1PCP8P[PCP8PPPCP8P\PCP8PAPCP8P]PCP8PSPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrPCP8PsE8F0F0F0F0F0P0A1Cu[PCPuPPPCPuP\PCPuPAPCPuP]PCPuPSPCPuP^PCPuPoPCPuPpPCPuPqPCPuPrA1CusF0F0F0F0F0PCf]RuPFPCPuPGPCPuPHPCPuPNPCPuPOPZ12BuR=P=PJF<F0F0P4A1Cu[PCP[PI12B[R=/5DPCP[PFA1C[GRjA1C[HR:A1C[NRhA1C[OR[14Z=R@14=JRn'ARi'3Rg'3R1'3RkPjPkP:P1PhPgP[PiP@PnP3P2P4PZP=P61=Z=dO3b0P3P2P4P=PJP61==JdO3b0GDDBE@W1f^R=P4P8F6W0P4O1PCPuPPPCPuP\PCPuPAPCPuP]PCPuPSPCPuP^PCPuPoPCPuPpPCPuPqPCPuPrA1CusF0F0F0F0F0P0A1C=PPCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrPCP=PsE8F0F0F0F0PCf_R=PFPCP=PGPCP=PHPCP=PNPCP=POPZ12B=R8P8PJF<F0F0P4A1C=PPCPPPI12BPR8/5DPCPPPFA1CPGRnA1CPHR@A1CPNRiA1CPORP14Z8R[148JRg'ARh'3R1'3R:'3RkPnPkP@P:PiP1PPPhP[PgP3P2P4PZP8P61=Z8dO3b0P3P2P4P8PJP61=8JdO3b0GDDBE@W1f`R8P4PuF6W0P4O1PCP=P\PCP=PAPCP=P]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrPCP=PsE8F0F0F0F0P0A1C8\PCP8PAPCP8P]PCP8PSPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrA1C8sF0F0F0F0PCfaR8PFPCP8PGPCP8PHPCP8PNPCP8POPZ12B8RuPuPJF<F0F0P4A1C8\PCP\PI12B\Ru/5DPCP\PFA1C\GRgA1C\HR[A1C\NRhA1C\OR\14ZuRP14uJR1'ARi'3R:'3R@'3RkPgPkP[P@PhP:P\PiPPP1P3P2P4PZPuP61=ZudO3b0P3P2P4PuPJP61=uJdO3b0GDDBE@W1fbRuP4P=F6W0P4O1PCP8PAPCP8P]PCP8PSPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrA1C8sF0F0F0F0P0A1CuAPCPuP]PCPuPSPCPuP^PCPuPoPCPuPpPCPuPqPCPuPrPCPuPsE8F0F0F0PCfcRuPFPCPuPGPCPuPHPCPuPNPCPuPOPZ12BuR=P=PJF<F0F0P4A1CuAPCPAPI12BAR=/5DPCPAPFA1CAGR1A1CAHRPA1CANRiA1CAORA14Z=R\14=JR:'ARh'3R@'3R['3RkP1PkPPP[PiP@PAPhP\P:P3P2P4PZP=P61=Z=dO3b0P3P2P4P=PJP61==JdO3b0GDDBE@W1fdR=P4P8F6W0P4O1PCPuP]PCPuPSPCPuP^PCPuPoPCPuPpPCPuPqPCPuPrPCPuPsE8F0F0F0P0A1C=]PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrA1C=sF0F0F0PCfeR=PFPCP=PGPCP=PHPCP=PNPCP=POPZ12B=R8P8PJF<F0F0P4A1C=]PCP]PI12B]R8/5DPCP]PFA1C]GR:A1C]HR\A1C]NRhA1C]OR]14Z8RA148JR@'ARi'3R['3RP'3RkP:PkP\PPPhP[P]PiPAP@P3P2P4PZP8P61=Z8dO3b0P3P2P4P8PJP61=8JdO3b0GDDBE@W1ffR8P4PuF6W0P4O1PCP=PSPCP=P^PCP=PoPCP=PpPCP=PqPCP=PrA1C=sF0F0F0P0A1C8SPCP8P^PCP8PoPCP8PpPCP8PqPCP8PrPCP8PsE8F0F0PCfgR8PFPCP8PGPCP8PHPCP8PNPCP8POPZ12B8RuPuPJF<F0F0P4A1C8SPCPSPI12BSRu/5DPCPSPFA1CSGR@A1CSHRAA1CSNRiA1CSORS14ZuR]14uJR['ARh'3RP'3R\'3RkP@PkPAP\PiPPPSPhP]P[P3P2P4PZPuP61=ZudO3b0P3P2P4PuPJP61=uJdO3b0GDDBE@W1fhRuP4P=F6W0P4O1PCP8P^PCP8PoPCP8PpPCP8PqPCP8PrPCP8PsE8F0F0P0A1Cu^PCPuPoPCPuPpPCPuPqPCPuPrA1CusF0F0PCfiRuPFPCPuPGPCPuPHPCPuPNPCPuPOPZ12BuR=P=PJF<F0F0P4A1Cu^PCP^PI12B^R=/5DPCP^PFA1C^GR[A1C^HR]A1C^NRhA1C^OR^14Z=RS14=JRP'ARi'3R\'3RA'3RkP[PkP]PAPhP\P^PiPSPPP3P2P4PZP=P61=Z=dO3b0P3P2P4P=PJP61==JdO3b0GDDBE@W1fjR=P4P8F6W0P4O1PCPuPoPCPuPpPCPuPqPCPuPrA1CusF0F0P0A1C=oPCP=PpPCP=PqPCP=PrPCP=PsE8F0PCfkR=PFPCP=PGPCP=PHPCP=PNPCP=POPZ12B=R8P8PJF<F0F0P4A1C=oPCPoPI12BoR8/5DPCPoPFA1CoGRPA1CoHRSA1CoNRiA1CoORo14Z8R^148JR\'ARh'3RA'3R]'3RkPPPkPSP]PiPAPoPhP^P\P3P2P4PZP8P61=Z8dO3b0P3P2P4P8PJP61=8JdO3b0GDDBE@W1flR8P4PuF6W0P4O1PCP=PpPCP=PqPCP=PrPCP=PsE8F0P0A1C8pPCP8PqPCP8PrA1C8sF0PCfmR8PFPCP8PGPCP8PHPCP8PNPCP8POPZ12B8RuPuPJF<F0F0P4A1C8pPCPpPI12BpRu/5DP7PLPCPpPFPCPpPGPCPpPHPCPpPNPCPpPOPZPuPuPJC;F0F0P4D?b0W1fnRuP4P=F6W0P4O1PCP8PqPCP8PrA1C8sF0P0A1CuqPCPuPrPCPuPsE8PCfoRuPFPCPuPGPCPuPHPCPuPNPCPuPOPZ12BuR=P=PJF<F0F0P4A1CuqPCPqPI12BqR=/5DP7PLPCPqPFPCPqPGPCPqPHPCPqPNPCPqPOPZP=P=PJC;F0F0P4D?b0W1fpR=P4P8F6W0P4O1PCPuPrPCPuPsE8P0A1C=rA1C=sPCfqR=PFPCP=PGPCP=PHPCP=PNPCP=POPZ12B=R0P0PJF<F0F0P4A1C=rPCPrPI12BrR0/5DP7PLPCPrPFPCPrPGPCPrPHPCPrPNPCPrPOPZP0P0PJC;F0F0P4D?b0W1frR0P4PuF6W0P4O1A1C=sPCPsPI12BsRB/5DP7PLPCPsPFPCPsPGPCPsPHPCPsPNPCPsPOPZPBPBPJC;F0F0P4D?b0W1P0P4PuF6W0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000W0P4O1n201100000021100011000b8%b9eb1W5W6W4W9o"). Qed.

Ltac keep_tac ::=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr;
  lazymatch type of Hr with wreg ?wl _ = false =>
    repeat first
      [ (* [comment removed for export] *)
        lazymatch goal with
        | |- getr (regupd ?R0 ?r0 ?v0) r = _ =>
            let R := constr:(regupd R0 r0 v0) in
            let bl := gf_reify R in
            lazymatch bl with
            | (?base, ?l) => rewrite (getr_upds_test (wreg wl) base l r eq_refl Hr : getr R r = getr base r)
            end
        end
      | rewrite (getr_other_w wl _ _ _ r); [ | reflexivity | exact Hr ]
      | match goal with
        | Hk : forall r' : reg, wreg ?wl' r' = false -> getr ?R1 r' = getr _ r' |- getr ?R1 r = _ =>
            rewrite (Hk r (wreg_sub wl wl' r eq_refl Hr))
        | Hk : forall r' : reg, AllocIface.callee_saved r' -> getr ?R1 r' = getr _ r' |- getr ?R1 r = _ =>
            rewrite (Hk r (callee_saved_of_wreg wl r eq_refl Hr))
        | Hk : keeps ?R0 ?R1 |- getr ?R1 r = _ =>
            rewrite (keeps_wreg wl R0 R1 r Hk eq_refl Hr)
        end ]
  end;
  reflexivity.
