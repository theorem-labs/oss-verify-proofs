(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtor LbB_DPdK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_TablStmt LbB_SnStmt LbB_SnV.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_SnQ () := "C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics5Riscv3Sem7mul_divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions6bv_andC45stdpp9bitvector;definitions9bv_shiftrC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4landC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec=bv_wrap64_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_and_unsignedC45stdpp9bitvector;definitionsBbv_shiftr_unsignedC45stdpp9bitvector;definitions6bv_mulC45stdpp9bitvector;definitions?bv_mul_unsignedC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06C47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4prod00I47Corelib5Lists7ListDef6Forall00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame7outsideC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=disjoint_fromC46Stdlib5Lists4List?Forall_cons_iffI47Corelib4Init5Logic2or00C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic4True01I46Stdlib5Lists4List6Exists00K46Stdlib9micromega=RingMicromega3Op206C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3ivlC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6fframeC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List8map_consC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface>AFS_MAXLIVE_BPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt9ADS_STACKC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN3tabC47Corelib4Init5Logic6eq_indK47Corelib5Lists7ListDef6Forall02c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ3P1wC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat7LINV_P5C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DPdK<aconst_ok_hiK47Corelib5Lists7ListDef6Forall01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst<ACONST_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;aimg_clientC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState<unsigned_litI47Corelib4Init9Datatypes6option00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat:LINV_P5_clK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3mrdC6ARocqVerifyHarness?AgentSubmission3bpB2Rt<BakeStackRep:wview_highK47Corelib4Init5Logic2ex01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=stk_transportC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsC4ARocqVerifyHarness?AgentSubmission8LibIface3memc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ9p1_rangesC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9aconst_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ7p1_keepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat6relro0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat5dstatC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst=ACONST_shbaseC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2wzK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst:ACONST_uarK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry04K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat:kimg_relroI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvAkword_of_rw_cellsC56Stdlib6NArith6BinNat1N3ltbC56Stdlib6ZArith6BinInt1Z4of_NC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt5sx32AC47Corelib4Init9Datatypes3appC47Corelib5Lists7ListDef3nthK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv:kwr_of_stkC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ3Wp0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ6kst_p1C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst;AGOT_SHBASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst<ASHBASE_CELLC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst8AGOT_UARC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9AUAR_CELLC56Stdlib6ZArith4Znat5Nat2Z6inj_leI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs<ASHADOW_BASEI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHCELLC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEC46Stdlib9micromega8ZifyInst7Inj_Z_ZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit6wboundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4fwclC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit5fkeysC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit3finc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ3tS0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN7tabs_wfC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN2tbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit3wclC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4wenvC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN2tBC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN3tloC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN3thiC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN4ttblC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN3tksC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28expr_eqbC46Stdlib5Lists4List2InK47Corelib4Init9Datatypes4bool02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4fentC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5winsTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN9sub_fp_ofC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame<munch_weakenC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame;munch_transC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame;wmono_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4ftblC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN7tabs_okC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit6fin_InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<wr_at_of_stkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DRep9wr_at_subC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface:rt_bp_baseC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceDstack_malloc_stmt_bpC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceDstack_malloc_sz_stmtC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface?stack_free_stmtC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceBstack_free_sz_stmtC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface?set_shadow_stmtC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface9rt_bp_extC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<AFS_MALLOC_5C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<AFS_MALLOC_6C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<AFS_MALLOC_8C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface:AFS_FREE_5C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface:AFS_FREE_6C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface:AFS_FREE_8C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface>ASET_SHADOW_00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface>ASET_SHADOW_F8C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<AFS_MALLOC_3C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<AFS_MALLOC_2C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<AFS_MALLOC_0C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvBsh0_of_addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3sh0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnVGshk_last_of_addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3shkC4ARocqVerifyHarness?AgentSubmission8PropExec3rdnC5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_RFSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<ah_RFS_rangeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7afsb_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8ff_classC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7ff_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7ff_flagC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<aframe_rangeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7hull_hiC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7hull_loC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3fszC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<ah_RFS_nodupI46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List>NoDup_cons_iffC46Stdlib5Lists4List6in_mapC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap;ah_RFS_disjC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap7fsz_posC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap;fresh_frameC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ3HHbC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AFS_HDRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8AFS_SIZEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface9AFS_FLAGSC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9umap_footc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ5quietC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB3lblC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6nval32C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_bliveC4ARocqVerifyHarness?AgentSubmission8LibIface4liveC46Stdlib5Lists4List:in_map_iffC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_nodeC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell8C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell4C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5apartC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4AC_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4LY_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4MI_Ac6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ2UWC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt7app_objC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DCtor=inframe_factsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5shvisC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DPdK:outside_ofC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9ALOWSH_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ7out_objc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ7po_thisc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ2W1C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame6sub_fpc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ9quiet_outC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit2gzC4ARocqVerifyHarness?AgentSubmission8PropExec7rdn_extc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQCdisjoint_of_outsideC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3bC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3aC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3cC56Stdlib6ZArith6BinInt1Z7div_mulC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts<nval32_agreec6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ:quiet_footC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep;umap_blocksC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts;umapx_agreeI5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5umapx00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3nshK46Stdlib9micromega5Tauto8GFormula01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadowEaddressable_transportC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame?wr_at_transportC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow:hull_lo_leC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow?shvis_transportC46Stdlib9micromega;ZifyClasses8or_morphC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface:athr_cellsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5ATSD0C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3ATPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK3PWFc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ2TWc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ8tw_placeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack09stack0_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface@aclient_write_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_sizeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface=aimg_client_wC6ARocqVerifyHarness?AgentSubmission3bpB3Lib6LbB_SR=aconst_ok_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ7tw_lawsc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ:tw_out_imgC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_RHEAPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnStmt5sn_XTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface4fshnC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep7xclientC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<aclient_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep7rin_ivsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap6ah_fsbC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8in_blockC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;in_block_shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap9ah_blocksC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ablock_rangeC47Corelib4Init5Logic7and_indC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep5xpresC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6RtB_Td6ATDLOCC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK2W3c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnQ3TW0".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition kst_p1 : list kentry :=
  [ KImg 0x17e000 0x186000; KWord (SA (ELit 0) SHCELL) 8 (ELit SHBASE); KWord (SA (ELit 0) AUAR_CELL) 4 (ELit 1);
    KWr (SA (EVar 33) (-8192)) (ELit 8192); KRange (EVar 33) (2 ^ 45) (2 ^ 47) ].

Lemma pd_mul32 : forall x, 0 <= x < 2 ^ 64 ->
  mul_div M_MUL (Z_to_bv 64 32) (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 5)) = Z_to_bv 64 (x - x mod 32).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnQ ()) [] "h06__sat1h11zh27__arithh34__ffh46__sat0h58__varmaph65__with74__x1h86__sat3h94__p1h:6__sat2h;4__x2h<4__x3h=2Hah>6__sat4h?6__sat5h@1HhA2b1hB2b2hC1nhD1BhE1DhF2HxhG1xp%0p&0p;1p;2p;3p;4p;6p;5p;7p;8p-1p10000p4p710p8g000Gj1ETg000lj1HTg001Jj2_Tg001gj29Tg002CR0j2MTg002^j1RTg003Aj3>Tg003[j24Tg004Ej3tTg004ij1`Tg005Gj2DTg005mj1CTg006Rk30@Tg007:k40;Tg007dj23Tg008Dj2JTg008ak308Tg009Fk305Tg009nj27Tg00:Nj2<Tg00:lj2=Tg00;Rj26Tg00;oj2BTg00<Lj2gTg00=4j3jTg00=Xj2sTg00>9j2kTg00>Sj1pTg00?3j1oTg00?Sj1nTg00@1j1mTg00@Oj1lTg00A:j2OTg00A]k60BTg00BAk20ATg00Bck20?Tg00COk30>Tg00Cnk40=Tg00D`k30:Tg00EAj2UTg00E^j2\Tg00FOj2ZTg00G@k309Tg00Ggj2YTg00HEj2WTg00Hhk104Tg00IJk403Tg00Ikj3fTg00JNj3XTg00K1k502Tg00K]k401Tg00L8k100Tg00LVj2}Tg00M7j1KTg00MVj3eTg00N?j2dTg00Nhj2PTg00OTj3QTg00P4j4{Tg00PRj3cTg00Q5j3bTg00QXj2iTg00RDj3NTg00Rgj2zTg00SPj3yTg00T9j3~Tg00Tbj1FTg00Ujj2STg00VYj3xTg00WGj3wTg00X8j3vTg00X]k306Tg00YKk207Tg00Ygj4^Tg00ZRj7[Tg00[6j6uTg00[Zj7rTg00\>j8]Tg00\bk30<Tg00]Kj6qTg00]iR1f0R2+07p=0g00^GR3f1R4;>2p=2f2R51642'=p=?1742,65p=|1354=>32p=af4R6f3R7/75'6/34=>32p=@P3P4g00^eP2C^p=TP4g00_LR8g00_kR9P9g00`KR:P2g00`kR;F[p=VP5P8P9P9P:P3P4g00aKP2C^P;F[p=:1942,M5p=8P5P8P9P9P:P3P4g00b2P2C^P;F[p=AP4P8P9P9P:P2Eup=hP5P8P9P9P:P4P2Frp=5P7P8P9P9P:P5P4P2G]p=L1d32p=GB0<342p=;f6R;P8P9P9P:f5R<P6P7P8P9P9P:P5P4P2G]G]p=IP3P6P7P5P4P2Eqp=1%02R=g00bYR>#ER?#HR@%E?#E#E#ERA#ERB#HRC'_RD,92RE'MS00g00c>RF%R2RG%R4RHP0%R5?>4214751474'2R0[14541452'2%R7?>54[RI%R6?>75\0At542P2n2001000000120000000WBWAWCPI^BH^AG^CFP2%`BRBPBg00c\%HARA,DBRFg00dH1DB5RG%C?#HRH,DBRI40@H0;S01135AR0,J5RJ,DBS0214BFRK%C>RL#CRM#C#C#C#HRN,DBRO:08BIRP:05BGRQ,4BS035?B137ARR,J7RS,DB,4BRT,22X1314BGS0414BPS05'7A?BK2/2TX1314BIS0614BORU'<RV1DB7,4BRW/729?BK/2TX131=BARX17WV9?B2/2TX131=B5RW172V9?BX/2TX131=BHRV1=B7RY1<2U'79?BX/2TX131=BNRZ1<V2,7Y9?BX/2TX131=BJS071<VZRT,7YRY9?BX/22X13A|XWTR[/3D1=BSR\,22X1313ADR]162Y?aD\X13135DS08P]P2PTPDP\D@X1313HDRTP]137DRY1<2ZPDP\D@X1313NDR^P]PY1<T2PDP\D@X1313JDP]PY1<T^RYPDP2D@X13P5P]P2PYPD13SDRSD@X13PAP2P7PYPDPSD@X13PHPAP71<2^PDPSD@X13PNPAP71<H2PDPSD@X131_@H,B516A2RY?aDSX131g@CRS191@R\%0C191D[R_[R`%0@Rag00e4RbAj@C4UW=RC%0D\b^=aRcP4g00eP1s1@'kP\eS09O1RdP_g00f6Re#pRf%oeRg%n3Rh%m3Ri%l3RjP8P9P9P:1O3AR81O31Rk'T,VjJ0B20Aj:R:P2P5g00fbRlg00gBRm'k20?25=>lmdB0>314H0=Rmb3b5b6A>3A1g00gb[P2b2b0b4b0:0:5A1B5A,6A/U0,251\7A%07S0:%0AR013<ARl#0[[1Z6A%06Rn1B;ARo#0\0[PSP`PCPcPdP_PfPgPhPiA:jk8P:Pmb3b5b6191AP2b2b0b4b0S0;b:b8:097A%0R?8RA1B6ARR#0Rp%EM#C#CRM#HRq,_@Rr,9RRRP6PA1\6ARs13;ARt#0\0\nRu1Z<ARv%0<Rwf7Rx/BA#0\0[RyPSP`PCPcPdP_p-0RzPfPg1Y34S0<PiPj1W3>R{9AjkR|1hj7R}55j&049R9P|CLP:Pmb3b5b6X73W91M=4%04R~[^73^9zP2f:S0=/9DQ0=f9O3b2b0b4b0b:b8PsPuPvPyQ0;b:b8S0;H03P6PAPrQ0;PsPuPvPy1g@qRy%0q191r[R1\\R\Aj@q4VbX=aRq%0r\b^=aRaPSP`PCPcPdP_P6Q09O1RbP1PfPgQ0<PiPj1O3@R@=f3BRv9:j{S0995j}P9%`M9f3@9X389:j{CLP:Pmb3b5b6X73X9z1M4E16Ar,94[^73^9zP2f=Rr#0Prf<O3b2b8b0b4b0b:b8b>b?I02H011MpR1B<A,6ARR1J;t/3D,22X131J<lRl16Ao/22X131\<AS0;13xA#0\0\wS0>1Z;AS0?%0;f8S0@/BA#0\0[S0APyP\PqPaPSP`PCPcPdP_PbP1&00>,}3R>g00h?Rw#KRo#KRt#G5e31d3wRw';g00h^Rp'P=QefPgP31Y35P41Y37C{S0BPiPj1W3?R?AX38{RE1W3LRL5c3'T,VjS0CP9PjAAjk?R@1hj<S0D55jP9Ab3?L,TE,VjFIP:Pmb3b5b6X73X;3X<3X9z1UY5,24%05/M616A5S0E1J76'2[[^73^;3^<3^9zP2f>RY/9D13YARMPY1BYAS0Ff;S0GPrO6b2b8b0b4b0b:b8b>b?13lDQ0;Q0>Q0?Q0APyP\PqPaPSP`PCPcPdP_PbP1%KtRt#GR}9e3>R>/;w%KtRt#KRu#K#G,;w/Pp'i%GtRt%Go/;wRo';/Pp=Qef5QePgQ0BPiPjPjP|P9PjAAjk8RsP9AAjkLCLS0HCLP9PjPjP|P9PjPsP9P@FIP9PjAX38L=c3?,T{,VjP9PjQ0995j|S09P9Ab3{?R{9AjkA:j{v55jFIFIP:Pmb3b5b6X73X;3X<3Pn\0R{\=P{\~R{16A6R=/U7,25Q0:?87D1J6<R|#0?8|D[[[[^73^;3^<3P2Q0FPMPYPxQ0@Q0GPrO7b2b8b0b4b0b:b8b>b?9NlDD113RDQ0;Q0>Q0?Q0APyP\PqPaPSP`PCPcPdP_PbP1%GuRu1;>o';/Pp1z3A=y3w1;t},;u';/Pp,iw=Qef5QePgQ0BPiPjPjP@P9Q0HCLP9PjQ0DA:jL855jP9PjQ0CP9PjA:j?v95j@P9AAjkEA:jEv55jFIFIP:Pmb3b5b6X73X;3X<3X9zA867AQ0E/U6,27A8n6D%0=?8=D[[[\{^73^;3^<3^9zP2%0MPMPYQ0FQ0@Q0=Q0GPrO8b2b8b0b4b0b:b8b>b?9NRDD1b@bDbE175HPSP`PCPcPdP_PfPgPhPi1O3HRR9AjkRrP:Pmb3b5b6%0HRYP2b2b0b4b09~5HD1P^PSP`PCPcPdP_PfPgPhPi1O3NR^9AjkA:j^v55jP:Pmb3b5b6%0N?8NDP2b2b0b4b09NNDD1PTPSP`PCPcPdP_PfPgPhPiA:jRv95jrP:Pmb3b5b6A8YHDP2b2b0b4b09NHDD1P]PSP`PCPcPdP_PfPgPhPiA:j8v95jsP:Pmb3b5b6A80ADP2b2b0b4b09NADD1Q08PSP`PCPcPdP_PfPgQ0<PiPjQ09P9Q09CLP:Pmb3b5b6X73Q00A8~4D[^73P2P;P<O2b2b0b4b09N5DD1Q07%FJD1PZ%FND1PV%FHD1PW%F5D1PX%FAD11=B[%F[D1Q02,4BR[1SBJD1PU1SBND1Q061SBHD1Q041SB5D1PK1SBAD1Q05AxBIOD1Q03AwBGPD1AvBFQ,4BB06BFQD1Q01,4B/2[eO4b@WFXG3o"). Qed.

Lemma disjoint_of_outside : forall W A n, Forall (fun iv : Z * Z => fst iv < snd iv) W -> 0 < n ->
  (forall x, A <= x < A + n -> outside W x) -> disjoint_from W A n.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnQ ()) [] "p'0h01xh11Ah21Wi001Wh34__p1h44__x1h54__x2h64__x3h74__x4h81nh92HWh:1ah;1li011lh<2H3h=2HOh>2Hnh?1Lh@1PhA1XhB2_HhC7__arithhD4__ffhE8__varmaphF5__withG1ohH1si021shI2z3hJ1GhK2G2hL1HhM2H1hN2H2hO2HxhP2IHhQ2hii032hihR2ivhS2loi042loi052W'i061gi071ii087outsidei091pi0:1zp;2p;1p;3p;4p;6p;5p;7p;8g00iJR0j2wTg00?3R1j1JTg001gj22Tg00ijj34Tg00EAj25Tg00jKj2CTg00kJj3ATg00>Sj1QTg00OTj38Tg002CR2j21Tg00lOj4vTg00YKj20Tg00m3j27Tg00mMj2VTg00n4j29Tg00nPR3j2STg00o0j3eTg00oJj3dTg00odj2>Tg010Aj2WTg00L8j1_Tg00LVj2^Tg00M7j1KTg00N?j2FTg00MVj3]Tg00Nhj2ITg00Ggj2NTg00?Sj1\Tg00P4j4LTg00@1j1[Tg00@Oj1ZTg00HEj2ETg000Gj1YTg00[6j6uTg00Hhj1tTg005mj1RTg00PRj3rTg00Ygj4?Tg00A:j2qTg00BAj2pTg00>9j2oTg00Bcj2hTg003Aj3TTg00COj3gTg00Cnj4fTg010cj1;Tg011<j2iTg00K]j4jTg011[j5kTg012=j3lTg012Zj3mTg0137j4nTg00\bj3cTg00ZRj7bTg00[Zj7aTg013Wj7`Tg00\>j8sTg00^GR4f0R57l4p=MAm445p=Hf3R6f2R7'0f1R8/25'1p=6P4P4P8P5Cnp=BAT485p=@1078/15p=OAc485p=<g00f6R9?885p=:P4P8g00aKP5C?p=GP8g00_LR:g00_kR;P;g00`KR<P5g00`kFbp=3P4P8g00^eP5C?p=PP7P:P;P;P<P8P5Fap=DP7P:P;P;P<P8P5F`p=XP6P:P;P;P<P7P8P5Gsp==1285,17p=U1w44R=#JR>P=%M5%H5'2XR=R?=4=7g00]iR@/28RAf4RBP5P515B6C6RCf6RD/C8[^04f5RE?AB6[[[^84^14RFX2>%Q=RG94=?1CG8\C^04g014;AAGB6eW=X>AW9X84X14P0P4P4A8=B694=?f8RGf7RH58=/C8\C^04A8=HD?AB6[\A[^84^14\F^;>P51BEB=8=694=?f9RI/BGRJ=8=H/C8\C^04g014Wp4p710RCp-0RK\5RL%J7RMP2A86859467P6P7O1A4B68'1[RNP7P8O1A4675'1A8B7894B6RO[PBP6O1A4EB7'1\OP6P7P8P5CvP8n2001000000120000000W;X:8W@W1PN^;M^:8^@L^1CP5P=P?PJPHP6O5%MJ%HJ'2A4=?H'1P2f:RJ/BIRC#M%HC'2A4=?G15HDf;RC'010JH'7AAIHD'1P5f<RL/BCRM#M%HM'2A4=?C15JIR?f>RM'0RNf=RO/0J'7AALJI1V?M19?M,SNP315CJRNf?R?'019N?15LCRPf@RQ'0RR10?L'7P515OLfARS'010QORT;e5X?RP5O119PQ1VQO19QO,STP310SM19SM15?MfCR3'0fBRT/0?RO'7P515Q?fDRP'0RR103QRU;d5X?OP5O119T?17RUPL1>QPRL1WQP12QP1@LP'11@LQ9OPQ'7fERU,>SRRP4g00bYRO#_,^4g00h?RV#KRW#KRX#KRY,F4RZ5]41F4VRV'<R[g00h^R\'IR]1F4W/<V,<Z/I\RW1F4X/<V,<Z/I\RZ%KY,F4/<[/I\R\%Q9R[':':':':%J9R9P4P41N4BRYP7%\4RVCLP81N46CL%[4RX%Z4R^1E4OR_%YOR`#Y,E4Ra'G,3^1E4`Rb/Pa,3^5D^P^P:P;P;P<PDEu1Pb_,3^5D^R:5X^%t;R;P^P4%RO,E4RO9r4_Rcg0154RdPaC?,3^P;P^1q4@/GO,3^P;P4P_g00b2RaPbC?,3^Re1Gbc,3^5D^C=C=C=1p^<R<P5P7g00fbRcg00gBRf'o1h57=TcfdAg4@8CfRfbDbEbFX44X54X64X74X3K12561@86Rc'11@85,1BRg'71586/9B12@B106BR@156E7UB[[[^44^54^64^74^3KP5fGRh/03PhPTP8P3P7PDPQO8bCbIb<O2PPPLPLP3C6#;g015[Ri#JRjPK^04]2P1PiPKP8g00e4P0P4P4PKP8P8PBPBP5C6#;PDP7PBO2'1n2001107000120104103n10110000020020107105X04X2jp?1000108RjPTPLO2'1P2PUPRPRPPC6#;PjP3PRO2g00gbP5Ph1>3hRhPhfFRhC6#;PjPhfHRR,>PO2P8fIRP,WU12UP1>UPRL/@P'11@LU9OPU'7fJ,>hP41:][,:W,:Z,:\P9P41N47P8P4PYP6PVCLCLPXP^P4P_Pa%R`,E4R`C?,3^1Pb`,3^5D^9X^:P;P^P4POPdP`C?,3^P;P^1G_O,3^P;1GbO,3^9D^eC=C=C=P<PfbDbEbFX44X54X64X74X3KAO56c,7g196B127BAU@BE[[[^44^54^64^74^3KP5fLRK,2RPRfKP8PKP7PGP?O8bCbIb<O1WBWAP8P5O2n2001000000121000000bG'iWKP5O1n200110200021010111106bHWJP5O1n200110200021010111106bHPCPJPIP5PHPCP5P5PNC6PGP8P5O2PQP8P8P?C6#;PjPMP8O2'1P2PSP7P7PQC6#;PjP?P7O21CQ6P5P3PBPBPTC6#;PjPTPEO2P5WAWBP8P5O2n2001000000120000000bGWOX04O5CjWNWMP8P5O2n2001000000121000000b9bL1BGH=8=D?AB6eW=X>AW9X84X14XPFX2>XQ4XS4P8P5O2n200110900012110:10:X:=P5DkW2o"). Qed.

Section P1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (this po tid pcons icount lo : Z) (LF : list fframe).
  Variables (bl bc : Z) (LB : list block) (ents : list (Z * (Z * (Z * Z * Z)))).
  Hypothesis Ha0 : a0 = Z_to_bv 64 this.
  Hypothesis Ha1 : a1 = Z_to_bv 64 po.
  Hypothesis Ha2 : a2 = Z_to_bv 64 (sx32A tid).
  Hypothesis TIDR : 0 <= tid < 2 ^ 32.

  Hypothesis DSA : addressable m0 po 20.
  Hypothesis DSW : wr_at asegs m0 po 20.
  Hypothesis DSO : app_obj po 20.
  Hypothesis DS8 : po mod 8 = 0.
  Hypothesis DSV : shvis m0 po (po + 20).
  Hypothesis DSin : obj_inframe LF po 20.

  Hypothesis PCA : addressable m0 pcons 48.
  Hypothesis PCO : app_obj pcons 48.
  Hypothesis PC8 : pcons mod 8 = 0.
  Hypothesis PCC : rw_cells asegs m0 (pcons + 32) [C8 (Z_to_bv 64 0)].
  Hypothesis PCfs : fsobj H LF pcons 48.
  Hypothesis DISJ : forall a, po <= a < po + 20 -> ~ (pcons <= a < pcons + 48).
  Hypothesis ICN : 0 <= icount < 2 ^ 63.

  Hypothesis THA : addressable m0 this 288.
  Hypothesis THO : app_obj this 288.
  Hypothesis TH8 : this mod 8 = 0.
  Hypothesis THfs : fsobj H LF this 288.
  Hypothesis THC1 : rw_cells asegs m0 (this + 8) [C8 (Z_to_bv 64 pcons)].
  Hypothesis THC2 : rw_cells asegs m0 (this + 80) [C8 (Z_to_bv 64 icount)].

  Hypothesis UM0 : umapx MI_A 32 (nval32 ASEGS) (lbl LB) m0 (this + 136) bl bc ents.
  Hypothesis USH : umap_sh m0 32 (bl, bc, ents).
  Hypothesis UBL : forall A n, In (A, n) (lbl LB) -> ablock_range H A n.

  Hypothesis STK : stk asegs m0 lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ADS_STACK.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPHI : bv_unsigned sp <= AAPP_HI.
  Hypothesis SPOBJ : forall O n, O = po /\ n = 20 \/ O = pcons /\ n = 48 \/ O = this /\ n = 288 ->
                     O + n <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= O.

  Hypothesis MI0 : mem_inv asegs m0.
  Hypothesis AC0 : ACONST m0.
  Hypothesis LV0 : LINV_P5 m0.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis RFS0 : as_RFS H LF m0.
  Hypothesis LFn : (length LF < AFS_MAXLIVE_BP)%nat.
  Hypothesis THR : athr_cells m0.

  Notation spz := (bv_unsigned sp) (only parsing).

  Definition Wp0 : list word :=
    [Z_to_bv 64 this; sp; ra; Z_to_bv 64 po; Z_to_bv 64 (sx32A tid); aw; s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; gp; tp].

  Definition P1w (m : mem) : Prop := munch [(spz - 8192, spz)] m0 m /\ wmono asegs m0 m.

  Lemma p1_ranges : 0 <= spz < 2 ^ 64 /\ aceil + ADS_STACK <= spz /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnQ ()) ["P1"] "h02Hah17__sat20h27__sat22h37__sat24h44__x1h51ah62H0h72H1h82H2h92H3h:4LFn0h;7__arithh<4__ffh=7__sat17h>7__sat18h?7__sat19h@7__sat21hA7__sat23hB7__sat25hC7__sat26hD8__varmaphE5__withF4cstrhG5cstr0hH4__p1hI4__x2hJ4__x3hK4__x4hL2A1hM2A2hN1RhO2_Hp;1p;2p;3p;4p;6p;<p;7p;8g016VR0p4p70R1p10000p4p710p8P1g017PR2p4p710p8P1p10180p4p710p8g000Gj11Tg004ij1_Tg018Mj2XTg003[j2sTg019@j1cTg001gR1j23Tg002CR3j22Tg019ij1ZTg005mj15Tg000lj16Tg01:ij1mTg00YKj24Tg007dj2;Tg003Aj3MTg01;cj1aTg00EAj2ETg001Jj2FTP2j2]Tg01<]R2j2\Tg01=5R4j1KTg00>9j2@Tg01=Uj4YTg01><j1JTg00E^j2=Tg00<Lj2DTg00=4j3CTg00=Xj2WTg00>Sj1UTg00?3j1TTg00Ggj2BTg00@1j1RTg00@Oj1STg00A:j2>Tg00HEj2ATg00Ikj3rTg00Ygj4QTg00Hhj1qTg00BAj2pTg00Bcj2lTg00COj3kTg00Cnj4jTg00M7j1NTg00N?j2GTg00\bj3LTg00Nhj2fTg00OTj3eTg00?Sj1dTg00P4j4OTg00[6j6bTg00Q5j3gTg00PRj3hTg008Dj2iTg00K]j4PTg01>al<`Tg00ZRj7nTg00[Zj7oTg00\>j8^Tf0R5#1#1p=<g00]iR6/45p=0%55#5p=V%55#5#5#5p=9%15#1#1#1p=I%15#1#1#1#1#1#1#1p=?g01?Fg00^GR7P2P4P1g01?ef4R1f3R4f2R2g01@GR8f1R9P5M<`p=[P7P9g00b2P5CQp=8P9g00_LR:g00_kR;P;g00`KR<P5g00`kFnp=7P2P:P;P;P<P9P5Fop=HP4P:P;P;P<P2P9P5G^p=:g00bYR=#1R>#<R?#1R@#1RA#1RB#_RCp,2spRD'X1sCDRD#0RE%cC,3D'2p,5HCEILRF#Z%5=RG#5RH#5#VRI#5#9#9RJ#1#9#9#1#<#I#?#?#6RK%mFRL'4RM%5J#9#9#1#<#I#?#?#6RJ,4LRN'2RO%<B#I#6RP,;L=M76%aFRF,4L1ELP,3F'2'2RF'2P3POPF%6>RP%6BRB'FRQ,3DRR,2ERSg01AKRT,EL/4DRU/2ORV'2RWP5P3PMPNPW\FP5PSPVp,2LF,]0R0/\8%K0RV%K8RW'3RXP0PV1@7VPW1@7WD[p,3LFnCYRYPX%J8R8%0WRW%J0R0%0VRV%6@R@,=DRZ%0@1;D@#0[\EREp,5pconsR@%6?R?'=R[%0@%0?R\1;@?#0[[R@%6IRI,DPR]136PR^%0I1FPIR_,36[R`[Ra%0PRbg00e4RcACPI9UW0RI%0_\c^0bRd%6ARA,DPRe%0A1FPARf,36[Rg\^RhACPA9VcX0bRA%0f\c^0bRi1DPBRj%0B136Q[Rk\^RlACPB9VcX0bRB%0Q\c^0bRbp,4thisRc/=?Rm%0c1;c?#0\\[Rcp,2poRn/=?Ro%0n1;n?#0\\[R\p,4TIDRRnp,3tidR?#0Rp13?fR?'2RfP3PpP?PSP5p,3ICNRqp,6icountRr#0Rs13r_Rr'2R_P3PsPrPSP5f=g00eP1W6P'@P^eR^O1RSPkf@P^O1RtPgfCP^O1R^P`g00f6Ru#URv%TuRw1B79Rx%R7Ry%S7Rz1>76R{1A7=R='8,7zP7P=g00aK1>7P=r7CCQ,7z5HzRC%q;RPPCC:1pz<RCP5P2g00fbR|g00gBR}'@1l52=M|}dAk769CjR6b<bDbEX47%05135Q'2%09139Q'2[^47P5PDfTRQO2b;b3b2b1X9rX8sP9P5O2n2001000000121000000b5X7?X6pP9P5O2n2001000000121000000b5b=b>b?b1b@b2bAb3bBbCbGbFb:PUPOPYPXP8PWP0PVPZPEP[P@P]PaPIPdPePhPAPiPjPlPBPbPmPcPoP\PnPfP3PpP?PUP5PqP_P3PsPrPUP5PSPkPtPgP^P`p-0RUg00h?R}#NR|#N,G71G7|1G7}5L75L7g00h^'f=euvPwP71B72P9P7%d7P41B71COCOPyPz1A7GRG,8{,7zPzP:P;P;P<f6Eb5HzPPPz1A7HRH1A7>R>9g7G'8,7zPPPz18=H,7zPPAh7=>/8G,7zC:C:C:PCP6b<bDbEX47XI7XJ7XK7WH%02/211i42,41f5RG,421E41/4G[[[^47^I7^J7^K7^HUP5PRp,2loPDPTPLPQp,2LOp,4CEILO8b;b3b2b1X9rX8sP9P5O2n2001000000121000000b5X7?X6pP9P5O2n2001000000121000000b5b=b>b?b1b@b2bAb3bBbCbGbFb:PYPXP8PWP0PVPZPEP[P@P]PaPIPdPePhPAPiPjPlPBPbPmPcPoP\PnPfP3PpP?POP5PqP_P3PsPrPOP5PSPkPtPgP^P`PvPwPxPyPz1>7J,8=,7zRyPPPz1>7K/8=,7zR=PPAHz=yC:C:PCP6b<bDbEX47145J14K914K2142J'2[[^47P5PLfLfMO3b;b3b2b1X9rX8sP9P5O2n2001000000121000000b5X7?X6pP9P5O2n2001000000121000000b5b=b>b?b1b@b2bAb3bBbCbGbFb:CPCPXOFXMNXLMP9P5O2n2001000010121000000X6OP9P5O2n2001000000121000000b6bNo"). Qed.

  Lemma p1_keep : forall m, P1w m -> mem_inv asegs m -> ACONST m /\ LINV_P5 m /\ stk asegs m lo spz.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnQ ()) ["P1"] "p'0h01bi001bh14__x1h22H0h37__sat20h47__sat22h57__sat24h61ah74__p1h84__x2h92Hah:4__p2h;4__x3h<3HV'h=4LFn0h>7__arithh?4__ffh@7__sat17hA7__sat18hB7__sat19hC7__sat21hD7__sat23hE7__sat25hF7__sat26hG8__varmaphH5__withI4cstrhJ5cstr0hK2EbhL2H1hM2H2hN2H3hO4__p3hP4__x4hQ4__p4hR4__p5hS4__p6hT4__p7hU2a3hV1oi011ohW1zhX2HVhY2HXhZ2Hch[2Hxh\2MIh]2MUh^2R1h_2R2h`2R3ha2T1hb2T2hc2T3hd2WMhe2_Hhf1mhg1xp%0p&0p;1p;2p;4p;3p;6p;7p;:p;<p;8p101BNp4p70R0g01CHR1p4p710p8P0g01CdR0p4p710p8g01DEk10WTg00iJk20VTg000Gj10Tg004ij1|Tg003[j2WTg000lj1DTg008Dj2eTg0137k40=Tg00>Sj1nTg00OTj3rTg01E=j3kTg01F:j3}Tg01G7j2{Tg01H3j1_Tg01Hmj1^Tg01Ikj4UTg002CR2j22Tg001Jj2hTg001gR3j25Tg01:ik10LTg00EAj2fTg00YKj21Tg005mj13Tg017Pk20:Tg01<]R4k209Tg01=5R5j1qTg00>9j2MTg01=Uk403Tg01><j1zTg00E^j2[Tg007dj2]Tg00<Lj2iTg00=4j3jTg00=Xk20UTg00M7j1TTg00N?j2yTg00Nhj2VTg00?3k10TTg00?Sk10STg00Ggj2\Tg00@1k10RTg00@Ok10QTg00HEj2RTg00Hhj1wTg00PRj3uTg00A:j2tTg00Q5k30OTg00BAk20KTg00Bck20JTg003Aj36Tg00COk30DTg00Cnk40CTg01Jfk30BTg01Khk20ATP0k60@Tg01LIk70?Tg01MIk10>Tg005Gj2pTg00jKj2`Tg010cj1oTg00A]k60<Tg00m3j2bTg00K]j4cTg00Ikk30;Tg01NHj2lTg00]Kj6mTg002^k108Tg01OLS00k107Tg01Onj18Tg01Pek406Tg01Qfj2ZTg01RHj2=Tg01Rbj3YTg01SZk304TP1k60ETg01T]k40FTg011<k20GTg00oJk30HTg01U7m:0ITg01>am<02Tg00\bk30MTg00P4k40NTg00Ygj4vTg00ZRj7sTg00[6k601Tg00[Zj7xTg00\>j8XTg013Wk700Tg01V<j3~Tf0R1#0#0p=@%01#0#0#0p=Og00]iR0/11p=4%31#3p=<%31#3#3#3p=J%01#0#0#0#0#0#0#0p=F%01#0#0#Dp=:g01?Fg00^GR6P4P5P3g01?ef4R3f3R5f2R4g01@GR7f1R8P1N<02p>05%01#3p=7%31#0p=91y61p=SB0M681p=Cg00f6R9?r81p=EP6P4P8P1H0Np=G1t61p=?P4g00_LR:g00_kR;P;g00`KR<P6P8g00b2P1Cvg00`kR=Fsp=;P8P:P;P;P<P1J01p=H%01#Dp>0PP4P:P;P;P<P8P1Fxp=Af6R>P:P;P;P<f5R?P3P5P:P;P;P<P4P8P1GXGXp=gP?P:P;P;P<P3P:P;P;P<P5P4FxP8P1GXp=L1108/21p=B1581,24p=IP6P8g00aKP1Cvp=KP8P:P;P;P<P1P=Fsp=N%31#3#0#0p=PP4P:P;P;P<P8P1K00p=dP5P:P;P;P<P4P8P1GXp=ag01W9R=?~81p=QA6481#op=>g01X0&0W1P220V66R@P6P6g00bYRA#0RB#@RC#0RD#0RE#0RF#|RGp,2sp'WRH%0F#@#ORI#DRJ'eRKPHH0=RL%n@RM3rRNp,2m0RO;k8A}=O81{=4%_5%^5P=P5p,2loRPPHCU'2'2[P1AkNO5A}=O31{=?g01Xa%4HRQ%DBRR%DFRF'hRS,5HS01'2S02p,5HCEIL$0LRTg01AK'f/1HS03%3AS04#3S05#3#<RU#3#J#JRV#0#J#J#O#F#F#:RW/1T%3V#J#J#O#F#F#:,1TS06'2S07'2S08'2P2Q02Q08f8RV#_%^VP=PVPPPHCU'2'2P1Q02Q08P2Q03Q07f<RX#_%^XP=PXPPPHCU'2'2P1Q03Q07f?RY#_%^YS09P=PYPPPHCUS0:'2PNPOPYp,3AC0f;RZf:R[P@g01Y_S0;PLPMg016Vp,2LF+0:RM0097%qMRL%q7R\'5R]PMPL1M6LP\1M6\I05p,3LFnH03S0<P]%z7S0=%4\S0>%zMS0?%4LS0@%DDRD,[HRL%4D1]HD#4[\QRQp,5pconsRD%DCRM'[R\%4D%4MR71]DM#4[[RD%DURU,iRR^150RR_%4U1hRUR`,50[Ra[Rb%4RRcg00e4RdAjRU8UW9RU%4`\d^9cRe%DERE,iRRf%4E1hRERg,50[Rh\_RiAjRE8VdX9cRE%4g\d^9cRj1iRFRk%4F150S[Rl\_RmAjRF8VdX9cRF%4S\d^9cRcp,4thisRn/[MRo%4n1]nM#4\7[Rnp,2poRp/[MRq%4p1]pM#4\7[R7p,4TIDRS0Ap,3tidRp#4RM15pgRp'2S0BP2PMPp%@A#F#7#9#9#9#9#F#:Rg/1KS0CP1p,3ICNS0Dp,6icountRr#4Rs15r`Rr'2S0EP2PsPrQ0CP1f=R`g00eP20U0R'MP_eR_O1S0FPlf@RtP_O1S0GPhfCS0HP_O1S0IPap-0R_g00h?Ru#TS0J#TRv#TS0K#SS0L%Sv1y6uS0M'CS0N'CS0Og00h^Ru'V%n9Rv'E&0T9R9&0S6Rw1\64S0P?G4w7G8&0R6Rx&0Q6RyPy%?WS0Q%3B,R6Rz5;yS0R1Hy3%w;R{Py&0PIRI#?S0S9u6z1R6AR|5;yP{Py1t60S0T=;y|R}1Hy?S0U5AyP{%?g%?J:0O6|S0V5;yFgEL20Ky<R~P1P4g00fbS0Wg00gBS0X'MQ0W20J14Q0X36dB0D608H0CR0b?bGbHX16X86X7_W:11W8/241f4I/181B4?1e5J,1g[[[^16^86^7_^:_P1Q01Q06PTPHfKfLS0XfPO7b>b5b4b3XNrXMsP8P1O2n2001000000121000000b6XLpX2MP8P1O2n2001000000121000000b6b@bAbBb3bCb4bDb5bEbFbJbIb=Q0Ce:0BKHQ0;-0A@J0@K0?Q09Q0:POPYp,3LV0151S,B1S0:&0>8f>S091pG4S0;P6P41`N1XW611K4?I4H#oS0CPdQ0<P]Q0=Q0>Q0?Q0@PLPQP\PDP^PbPUPePfPiPEPjPkPmPFPcPoPnPqP7Q0K#TS0K#SRKQ0O'C/VuR@1E@v,E@,E@'EP91\65S0O?G5w?G4w?G8wPxPyQ0U1R6BRB%3A#O#<#7#<#9#9#7#:S0W#?'K,Ny5Ay1Hy>S0U%3A#@#7#9#P#<#O#:S0Y#?,KB,Ny5Ayf7,HyS0Z%3A#@#7#9#P#<#9#<#:S0[#?,KB,Ny5Ay1HyVS0\%3A#7#P#<#9#7#@#9#7#:R@#?,KB,Ny5Ay5dy5dy5dyP{PyQ0Q1R6CRg5;yf9S0Q,Hy5AyP{PyQ0S9u6g=;y|P{Py1Hy[9Ay}P{PyP:P;P;P<Q0V=;yB1HyZ5AyJ0<FgFgP~P0b?bGbHX16X86X;6X7_X:_XO_XQ_XR_XS_XT_Q0W9I58Q0Y9I38Q0[9I?8AI>8@'b'b'b11W5/2V1f3I/141B5Z1e3J/1?/2`g00gb[[[[[^16^86^;6^7_^:_^O_^Q_^R_^S_^T_P115tHQ01Q06%3A#7#7#9#7#9#<#7#@#9#:/1t%3A#@#7#9#P#P#7#:/1t%3A#@#7#@#<#O#9#<#:/1t%0A#J#P#F#:/1tPTPtPHQ09fARJfBRIfFR@O>b>b@bAbBb3bCb4bDb5bEbFbJbIb=g014;CcQ0C/2de1`N4eQ0;,WGQ0<P]Q0=Q0>Q0?Q0@PLPQP\PDP^PbPUPePfPiPEPjPkPmPFPcPoPnPqP7Q0AQ0BP2PMPp15JS,BJP1Q0DQ0EP2PsPr15@S,B@P1Q0FPlQ0GPhQ0IPaPvP91\68PxPy%?R>0;6GRR,K|,Ny9Ay}R}P{P}CaP~P0b?bGbHX16Q0:158S,B8[^16P1fMS0:Q0XO2b>b5b4b3XNrXMsP8P1O2n2001000000121000000bUXLpX2MP8P1O2n2001000000121000000bUb@bAbBb3bCb4bDb5bEbFbJbIb=,l4EmO2%|C$08RC$07RdPI%84RBO1R<POPBO136eWZW9X66H06P=PNPOPYPPPHp,3STKR;PZP[11P1?I1HR:1`N81ZC1RN96d<X0C,=CP;P=POPPPHCUP2%4PS0X11HSR;%88,QO%wCR<5>dAY=OB=6dNX0C,=C'2\:^66R:'2RBfDRg%83O1=6dNX0C,=CP1Q0XP2P;P:fH%8VO1=6dNX0C,=CP1P1P[Q0QO2%8[,QO=>d<%8ZRZ9Y=O=6dNX0C,=C'2P21QOZ=>d<%8X9Y=O=6dNX0C,=CQ0:%8`R`O1=6dNX0C,=CP11QO`=>d<%8YRY9Y=O=6dNX0C,=CfJPYP8O2fORO/QY=>d<P6Ptg01Z\RY/11XW6Q0<P]Q0=Q0>Q0?Q0@PLPQP\PDP^PbPUPePfPiPEPjPkPmPFPcPoPnPqP7Q0AQ0BP2PMPp%3A#7#<#7#O#F#:RA/1OP1Q0DQ0EP2PsPrfTR=,1AP1Q0FPlQ0GPhQ0IPaQ0LQ0J#SQ0M'CR`'C,CK/Vu/EvP9Q0O9Gw3Q0P1\637G37G8S0PPxPyPyQ04#0,R6Rw=;y|S04Q0UP{PyPyQ0RQ0ZP{PyPyQ0TQ05,R6RX5;yS0TQ0\P{PyA;yzwS0\P{%?A=;y|CaELELELP~P0b?bGbHX16X86X;6XP6X7_X:_XO_1141Rw/2311W4RW/2>%4?R>/2V113?RV11A3[[[[^16^86^;6^P6^7_^:_^O_P1Q01Q06f[RA/5HPHPPPTPAfZS01f\RzfaRZp,4CEILR[O;b>b5b4b3XNrXMsP8P1O2n2001000000121000000b6XLpX2MP8P1O2n2001000000121000000b6b@bAbBb3bCb4bDb5bEbFbJbIb=11Yte1pGt,WGQ0<P]Q0=Q0>Q0?Q0@PLPQP\PDP^PbPUPePfPiPEPjPkPmPFPcPoPnPqP7Q0AQ0BP2PMPp15OS,BOP1Q0DQ0EP2PsPr15=S,B=P1Q0FPlQ0GPhQ0IPaQ0K#TRa#T#S1CK`'C/Vu%SaQ0N'C/Vu/Ev'EP9Q0PPxPyPyQ041K|X,NyP{PyPyQ0RQ0UP{PyPyQ0T1KXR,NyP{PyQ0\P{P}CaELELELP~P0b?bGbHX16X86X;6XP6X7_AIw1512W?AI>?S153S,B3\V[[[^16^86^;6^P6^7_P1Q06PHPPPTPAQ01PzPZP[O9b>b5b4b3XNrXMsP8P1O2n2001000000121000000b6XLpX2MP8P1O2n2001000000121000000b6b@bAbBb3bCb4bDb5bEbFbJbIb=,ltEm%8t,WG,1YRYePYPdfQRY%8JRJ'QA>d1<XVdP8PYPJO1RGB04YJ1J0EA>dG<fR%8IO1Pd1Md1fSQ0H#8O1=6d1Q00PCfUfE#8O1=6d1A>d8<A6d5NX0C,=C]<]KP8fV%8@O1=6dN1ZC8=>d<PC1ZC5=6dNX0CP41ZC4,MdH0FW<WKX0CP1O1P=%8gO1=6d<A>d<<A6d<NX0C,=CP11Md<O1+0GW<WKn10110100021010000P1P4O2bKbVb<bYb<WeWXP8P1O2n2001000000121000000b6Xc:Xb;P8P1O2n2001000000121000000X2BWaP8P1O2n2001000000121000000b240HW[Xg6N:0ICcCcW`W_P8P1O2n2001000000121000000W2W^P8P1O2n2001000000121000000b2W\WdW]P8P1O2n2001000000121000000W2Wfo"). Qed.

  Ltac evw0 := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wp0;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Lemma kst_p1_ok : forall R X m, P1w m -> mem_inv asegs m -> know_ok asegs (HLib.Eseed R (Wp0 ++ X)) m kst_p1.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnQ ()) ["P1"] "h01ah17__sat20h27__sat22h37__sat24h42H0h57__sat26h62H1h72H2h82H3h94LFn0h:7__arithh;4__ffh<7__sat17h=7__sat18h>7__sat19h?7__sat21h@7__sat23hA7__sat25hB8__varmaphC5__withD4cstrhE5cstr0hF2HahG4__x1hH4__x2hI1zhJ2_HhK1xhL4__p1hM4__p2hN7__sat28hO1mhP1nhQ2AChR2CShS2CUhT2MIhU2PWhV1RhW2R1hX2R2hY2R3hZ2RLh[2STh\1Xh]7__sat27h^7__sat29h_7__sat30h`1yp%0p%1p&0p;1p;2p;3p;6p;4p;Bp;;p;<p;7p;8g000Gj11Tg005mj16Tg004ij1LTg002^j1zTg01[Vk20yTg00?3j1vTg01DEk10[Tg01G7k20XTg01\Bk30QTg01H3j1jTg01Hmj1[Tg003[j2>Tg002CR0j25Tg01]>k10<Tg01^;k10;Tg000lj17Tg001Jj2XTg001gR1j2QTg01:ik10WTg00YKR2j22Tg01_7k20ITg01`8j1ZTg01`oj1]Tg00>Sj1UTg00OTj3:Tg01alk20ETg01bjk10xTg01cgk30rk40jTg01dhk20lTg01ebj1cTg01fZj2sTg00M7j1GTg01gSk30BTg01hMk10aTg00L8k10`Tg01iEk20_Tg01j?k30^Tg01k9k30]Tg01OLk10\Tg01Qfk206Tg00>9j2=Tg01l:R3j2`Tg01lTk605Tg017Pk20ZTg01<]R4k20YTg01=5R5j1STg01=Uk40UTg01><k104Tg00E^j2^Tg007dj2fTg00<Lj2VTg00=4j3WTg00=Xk20STg00?Sk10PTg00@1k10OTg00@Ok10NTg00BAk20MTg00Bck20LTg003Ak300Tg00COk30KTg00Cnk40JTg01m=j4PTg00EAR6j23Tg005Gj2RTg00A:j2}Tg00Ikj3pTg01NHj2|Tg00]Kj6dTg01mhj1hTg01n`j2MTg01oXj1tTg020Oj2gTg021Mk10HTg021kk40GTg022Nk202Tg023VlBwTg00Ggk203Tg00P4j4lTg00HEj2nTg00Q5k30DTg00Hhk10RTg008Dk20CTg024]k20TTg025:k10wTg025Xk20vTg026Jk10uTg026jk20tTg027Ak10sTg028@k30@Tg028]k40qTg0299k20pTg02:0k20?Tg02:dk20nTg02;am;0mTg00N?j2rTg00\bk30>Tg00Nhk20kTg01Khk20iTg01Cdj6YTg01Ikk40hTg02<ak20gTg02=Xk40fTg02>Wj4bTg01>al<eTg00Ygk40ATg00ZRk707Tg00[Zk70oTg02?Um<0:Tg02@:mB08Tg00PRk30dTg00\>k80cTg00[6k60bTg01W9R7f2R8f1R9f0R:H0hp=Ng02@`>0@9:-0g8p=FP7P9P:g02AXH0fp=Cg00]iR;/2:p=01389/2:p=;%6:#6#6#6p=B%1:#1p=A%1:#1#1#1p=@%1:#1#1#1#1#1#1#1p=I%1:#7p=D1289/5:p=HP7P9g02BSP:Cbp=kP7P9g02CRR<P:Cbp=mP7P9g02DRP:Cbp=oP7P9g02ENS00P:Cbp=u%6:#6p=a%G:#Gp>0e%G:#G#G#Gp=K%1:#6p>09g00^GR=/=:p=8g01?FS01P=P3P5P2g02FKf5R3f4R>f3R?P8P9P:M<ep=_Q01P=P4P5P1g01?eP>P?P8g01@GR1P9P:M<ep>0V1Q;:p=91}=:p=<P8g00_LR4g00_kS02Q02g00`KR@P=P9g00b2P:H0Ag00`kRAK07p=4P8P4Q02Q02P@P9P:K0op=JB00=9:p=OP=P9g00aKP:H0Ap=qP9P4Q02Q02P@P:PAK07p=i%6:#1p=TQ01P=P=P=P5P5P?P8P9g00h?S03P;P:N<0:p>0FP=P=P=P=P=P=P6P:P9P8P6P?P>P3f6RAf7RBP;f8RCNB08p={P=P=P2P3P2P>P;P;P?P8P9P:M<ep=yB0d=9:p=EQ01P=P=P=P5P5P3P>P?P8P9P:N<0:p=~P=P=P=P=P=P=P6P:P9P8P6P?P>P3PAPBPCf9R6NB08p=xP=P=P2PBP2PAP3P>P?P8P9P:M<ep>01P?P4Q02Q02P@P8P9P:L0cp=\A:89:9:>?p=?P9P4Q02Q02P@P:J0bp>0=g00bYR4#1S04#6S05#LS06Q04#1S07#1S08#1R2#1S09#1R5#LRD#zRE+0y%vEg01X0&0[:20X79B0Q89:%j8%[8p,2loRFp,2spS0:,>DRG5N8'5'5P0%j?%[?AN?FG'5AFAE3/C>P:%j3%[AANAFG'5P0%[BANBFGf:RB?FE6/CCP:%[6P0&0<B&0;Bf;?NFGf>RBf=R67FEf<RC'C[P:&0<C&0;6ANBFGg01Xa%0GRBQ04#7RC%75RA'XRH,QGS0;'5S0<p,5HCEIL$0WS0=g01AK;;GS0>%64#BRI#6#B#BRJ#1#B#B#A#@#I#I#DS0?Q0=Q0=%6JRJ#B#B#A#@#I#I#D'2S0@3HS0A'5S0B'5P0Q0<Q0BfCS0CfBRK7FEfA'CP:Q0<Q0BP0Q0>Q0AfGRLfFS0D7FEfERM'CP:Q0>Q0AfHRN00IKg02FmRK%Z<#]%UKRO3:RP,kNg02Gj#Z#]=:KORQ,mN'5P0fIS0E/kPQ0E/mQfLRNfKRR7FEfJ'CP:1kRP1mNQfMRN00ELQ00#Z#]=:KORL,oN%74RR#Z$0xS0F=:KOS0G,uN'5P0fNRN/oLQ0G,uNfQRNfPRO7FEfO'CP:1oOLQ0G,uNg02HhRNfTS0HfS7FEROfRS0I60r7S0J%14#a#B#@#I#D%64#@#a#@#I#D+0l%c;RLg02IbS0K'sRPQ03#GS0L$0eS0M#GRS#KRTg02J]#cS0N40BRUQ00,sLS0O%cRS0P80BSS0Q%62#LS0R$0aS0S%15#A#@S0T$0`R5'sS0UQ0T#7RL#cS0V+0_S0WQ0SQ05#6RV$09S0X#7S0Y,XCRW%aVS0Z#7S0[,XCRV40^S0\%UNS0]5:NS0^5:NS0_5:NRX5:NQ0I>0]OMPNQ0JPUPXP7POQ0IP<PQQ03%AJ#@#I#D#Z#]RJPPQ0NPTP3&0\KS0`206KJ'=Q01/=TQ0L/`TRJ1`TTRQ'5Q08#7RX,2RRU12XXRM'5S0aPJPQPUPMQ0LPR%8RS0bPTPX%8XS0cE_PTPXQ0cPTPXQ0cE_J05g016Vp,2LF+0ZRM00Y1%SMRU%S1RQ'QRJPMPU%8UPQ%8QI0Vp,3LFnH0URYPJ&041R1%0QRQ&04MRM%0URU%72R2,^GRZ%021fG2#0[\BRBp,5pconsR2/^XR[%02%0XR\1f2X#0[[R2%7IRI,VCR]%9CS0d%0I1XCIR^#9[R_[R`%0CRag00e4RbAWCI9UWFRI%0^\b^FaRcQ09#7Rd,VCReQ0d%0d1XCdRf#9[Rg[RhAWCd9VbXFaRd%0f\b^FaRi1VCARjQ0d%0A%9HS0e[Rk[RlAWCA9VbXFaRA%0H\b^FaRmp,4thisS0f/^XRnQ0f#0Q0f/fX#0\\[Rop,2poS0g/^XRpQ0g#0Q0g/fX#0\\[R\p,4TIDRRqp,3tidS0h#0RrQ0h/QfRf'5RsP0PrPfQ0aP:p,3ICNRtp,6icountRu#0Rv1Qu^Ru'5R^P0PvPuQ0aP:P6g00eP20S;C'=Q0deS0iO1R6Pkf@Q0iO1RwPgQ0CQ0iO1RxP_g00f6S0j#URyQ0j#vRz&0P=R{&0O=R|&0N=R}%<RS0k%<XS0l54}Q0lQ0l54}3J20M}@R@P:P8g00fbS0mg00gBR~'=Q0m20L:8<00~dB0K=;9H0JR~b;bBbCQ0aP:b:b3b2b1X8uX7vP9P:O2n2001000000121000000b0X6fX4rP9P:O2n2001000000121000000b0b<b=b>b1b?b2b@b3bAb5bEbDb9CPP=P;Q0K,3:Q03#SS0K,3<S0a'OXI=Q0a#81RD;S0n,>DS0oPYPJP1PQPMPUPZPBP[P2P]P`PIPcPePhPdPiPjPlPAPmPnPoPpP\PqPsP0PrPfQ0e9H;;S0eP:PtP^P0PvPuQ0eP:P6PkPwPgPxP_PyPzP{P|1}=;R<=4}<%<CS0p=p=DS0q,q<,i}5J}P@P~b;bBbCQ0eP:b:b3b2b1X8uX7vP9P:O2n2001000000121000000b0X6fX4rP9P:O2n2001000000121000000b0b<b=b>b1b?b2b@b3bAb5bEbDb9,|;S0eEd%hP,MO,>D%tP'3Q0a'Oe1gOPQ0a'Oe%64#A#T#A#T#@$09#a#A#DS0rQ0K'3S0s#0S0tQ0r/3;S0u#0S0vP:XK=RP129:$0HX`=XK=S0w1==;S0xQ0sQ0uPPPPPPP=P=g02KX139:H0G#8XO=XP=S0yQ0rQ0rQ0r#8Q0KPPPPQ01%S:#8WKS0zQ0xH0FS0{M9{S0|EyPYPJP1PQPMPUPZPBP[P2P]P`PIPcPePhPdPiPjPlPAPmPnPoPpP\PqPsP0PrPfQ0vP:PtP^P0PvPuQ0vP:P6PkPwPgPxP_PyPzP{P|Q0r#</E<S0r94}<P@P~b;bBbCQ0vP:b:b3b2b1X8uX7vP9P:O2n2001000000121000000b0X6fX4rP9P:O2n2001000000121000000b0b<b=b>b1b?b2b@b3bAb5bEbDb9CPQ0teQ0a#0eQ0s%STS0t'3S0v/2HS0}Q0u/3XS0~/2HS10PPQ0wQ0vQ0~PPPPPPQ0yQ0sQ0uQ0|Q0tPXPPPPQ0zPTPXQ0cE~M:xPHPH%8HS0|L01PYPJP1PQPMPUPZPBP[P2P]P`PIPcPePhPdPiPjPlPAPmPnPoPpP\PqPsP0PrPfQ10P:PtP^P0PvPuQ10P:P6PkPwPgPxP_PyPzP{P|Q0rQ0l'EQ0q54}P@P~b;bBbCQ10P:b:b3b2b1X8uX7vP9P:O2n2001000000121000000b0X6fX4rP9P:O2n2001000000121000000b0b<b=b>b1b?b2b@b3bAb5bEbDb9CPQ0}eQ0aQ0t;;HeQ08#L#zS08#vS0tQ0N,MO-02T'=MBwPNQ0JQ0QQ0_P7POQ0IQ00Q0GQ03Q0FQ0OQ0PPSP:Q0`Q0F-06K'=Q01/=SQ0L/`SS0`1`STS0F'5Q07#7RK,2RS0712KXS0G'5S0_Q0`Q0FQ07Q0GQ0LPRQ0bPSPK%8KS0bE_PSPKQ0bPTPXQ0cE_J05PYPJP1PQPMPUPZPBP[P2P]P`PIPcPePhPdPiPjPlPAPmPnPoPpP\PqPsP0PrPfQ0_P:PtP^P0PvPuQ0_P:P6PkPwPgPxP_PyPzP{P|Q0k%<KS0c54}Q0cQ0l54}5J}P@P~b;bBbCQ0_P:b:b3b2b1X8uX7vP9P:O2n2001000000121000000b0X6fX4rP9P:O2n2001000000121000000b0b<b=b>b1b?b2b@b3bAb5bEbDb9CPP=P;Q00,3:Q00Q0K'3RX'OXI=%8XQ0oQ0eEdQ0O#h,MO,>DQ0O#t'3/OXeQ0O,gO/OXe%64#A#T#A#T#@#T#@#DRRQ0K'3S0O#0S0e13R;R;#0S0oPPQ0wQ0xQ0OP;PPPPPPQ0yPRPR%8RQ0KQ0{M9{S0{EyPYPJP1PQPMPUPZPBP[P2P]P`PIPcPePhPdPiPjPlPAPmPnPoPpP\PqPsP0PrPfQ0oP:PtP^P0PvPuQ0oP:P6PkPwPgPxP_PyPzP{P|%<R/E<S0K94}<P@P~b;bBbCQ0oP:b:b3b2b1X8uX7vP9P:O2n2001000000121000000b0X6fX4rP9P:O2n2001000000121000000b0b<b=b>b1b?b2b@b3bAb5bEbDb9CPQ0ee%0XeQ0O%SSS0e'3S0o/2HS0x13;KS00/2HRRPPQ0wQ0oQ00PPPPPPQ0yQ0OP;Q0{Q0ePKPPPPQ0zPSPKQ0bE~M:xPHPHQ0|L01PYPJP1PQPMPUPZPBP[P2P]P`PIPcPePhPdPiPjPlPAPmPnPoPpP\PqPsP0PrPfPRP:PtP^P0PvPuPRP:P6PkPwPgPxP_PyPzP{P|Q0KQ0c'EQ0q54}P@P~b;bBbCPRP:b:b3b2b1X8uX7vP9P:O2n2001000000121000000b0X6fX4rP9P:O2n2001000000121000000b0b<b=b>b1b?b2b@b3bAb5bEbDb9CPQ0xeQ0e=;XHeQ0tQ0P,MO-02S'=MBwPNQ0JQ0WQ0^P7POQ0IPFPGQ0UQ0VQ0CPYPJP1PQPMPUPZPBP[P2P]P`PIPcPePhPdPiPjPlPAPmPnPoPpP\PqPsP0PrPf13G5RX,2FRRP:PtP^P0PvPuPRP:P6PkPwPgPxP_PyPzP=203=8S0CP9P{ClP|P}1n=4R4Q04,n=RRQ0T#DRK#<S0T60D=54}Q02$0RRP%<5R;,ER94}4C\P@P~b;bBbCXG=XH=20C9K,2:1385,29[^G=^H=P:PGPFp,2LOO3b:b3b2b1X8uX7vP9P:O2n2001000000121000000b0X6fX4rP9P:O2n2001000000121000000b0b<b=b>b1b?b2b@b3bAb5bEbDb9g00c>Q0mPEQ09#L-0T:fUQ06&0w:'R+0vPE&0u:%KT#K#K#K#K#K+0tPEQ0f,RDPEQ0:PEp,2raPEQ0g,RDPEQ0h$0s,RDPEp,2awPEp,2s0PEp,2s1PEp,2s2PEp,2s3PEp,2s4PEp,2s5PEp,2s6PEp,2s7PEp,2s8PEp,2s9PEp,3s10PEp,3s11PEp,2gpPEp,2tp%UED?D?D?D?D?D?D?D?D?D?Q0H60@EQ0nH0qn0100000020001WPQ01Q08#UU+0pQ0R+0?,>DRE/35S01,2FeQ0R-0?O,>DRT/35S0R,2FeQ0U#h,MO,>DQ0U#t'3RR,2FeQ0U,gOS0U,2FeP=PLA;X:GXI=PYPJP1PQPMPUPZPBP[P2P]P`PIPcPePhPdPiPjPlPAPmPnPoPpP\PqPsP0PrPfA;XLGRXP:PtP^P0PvPuPXP:P6PkPwPgPxP_PyPz203=9P|1E4;%<LR;'E=4}4P@P~b;bBbCXG=13:5?;L:^G=P:PGO1b:b3b2b1X8uX7vP9P:O2n2001000000121000000b0X6fX4rP9P:O2n2001000000121000000b0b<b=b>b1b?b2b@b3bAb5bEbDb91RDL,>DR5PYPJP1PQPMPUPZPBP[P2P]P`PIPcPePhPdPiPjPlPAPmPnPoPpP\PqPsP0PrPf%0L1QLH'5RHP:PtP^P0PvPuPHP:P6PkPwPgPxP_PyPzP{P|A4}<;Q0q,q;,i}5J}P@P~b;bBbCPHP:b:b3b2b1X8uX7vP9P:O2n2001000000121000000b0X6fX4rP9P:O2n2001000000121000000b0b<b=b>b1b?b2b@b3bAb5bEbDb9,|LRHEdQ01?;5GeQ0R?;5GeQ0V,MO,>DRX=;RGeQ0UQ0V-0nORR;;GeP=PL%9:XI=PYPJP1PQPMPUPZPBP[P2P]P`PIPcPePhPdPiPjPlPAPmPnPoPpP\PqPsP0PrPf%9LRLP:PtP^P0PvPuPLP:P6PkPwPgPxP_PyPzP{P|1q<;,i}P@P~b;bBbCPLP:b:b3b2b1X8uX7vP9P:O2n2001000000121000000b0X6fX4rP9P:O2n2001000000121000000b0b<b=b>b1b?b2b@b3bAb5bEbDb9P5PHEd%95R5eP5e%9Xe%9ReN;0mPNQ0JQ0\Q0]PYPJP1PQPMPUPZPBP[P2Q0Y,VCQ0dQ0Y#0%9W[R2[Q0Y=WC9VbXFa%0W\b^FaP]P`PIPcQ0[,VCQ0dQ0[#0%9V[Rc[Q0[=WC9VbXFa%0V\b^FaPePhPdPiPjPlPAPmPnPoPpP\PqPsP0PrPf12GV9HWGRsP:PtP^P0PvPuPsP:P6PkPwPgPxPcQ0DQ0iO1P_Q0EQ0iO1P2p-0R2Q0j1r=SQ0M,r=Q03,r=60>=60>=g00h^+0k;:yPzP=P{P9P=Q0CP8P{ClClP|P}Q0?#<Q05,n=R|54}20=}>5J}PPP}Q0T,E|=4}4PPP}A4}<420=}35J}PPP}Q0pQ0Z#L5p=94}4R<PPQ0pQ0X#L5p==4}4=J}<C\C\C\C\P@P~b;bBbCXG=XH=XL2WMQ0??H98A;8K9%08/5312?V12>V9HW>[[[[^G=^H=^L2^M2P:Q0;Q0@Q0=PGf[f\f`p,4SPHIO8b:bNb5b3b2b1X8uX7vP9P:O2n2001000000121000000b0X6fX4rP9P:O2n2001000000121000000b0b<b=b>b1b?b2b@b3bAb5b]bNb^b_bEbDb9Pse12EV9HWEe12TV9HWTeQ0S,MO,>DRD12DV5HWRWePWeP7POQ0IQ0\H0jeQ0J-0iNEYEYEYEYEYQ0I,COROePOeWSWJP9P:O2n2001000000121000000b4WRWJP9P:O2n2001000000121000000b4WYWXP9P:O2n2001000000121000000W4WWP9P:O2n2001000000121000000b4W[WJWZP9P:O2n2001000000121000000W4P9P:O2n2001000000121000000W4WQP9P:O2n2001000000121000000b0WTWUWOW\WVo"). Qed.

  Definition tS0 (T : list fent) (ks : list (Z * nat)) : tab := (EVar 33, spz, -8192, 0, T, ks).

  Lemma tabs_wf1 : forall T ks, fwcl (wbound Wp0) T = true -> fin (-8192) 0 (fkeys T ++ ks) = true -> tabs_wf Wp0 [tS0 T ks].
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnQ ()) ["P1"] "p'0h02H0h12Hah27__sat20h37__sat22h47__sat24h51ah62Hbh72H1h82H2h94__p1h:4__x1h;2H3h<4LFn0h=7__arithh>4__ffh?7__sat17h@7__sat18hA7__sat19hB7__sat21hC7__sat23hD7__sat25hE7__sat26hF8__varmaphG5__withH4cstrhI5cstr0hJ4__p2hK4__x2hL2u1hM2u2hN1ChO2F1hP2R1hQ2R2hR2R3hS1ThT1ehU2kshV1thW2t1hX2t2i001bp%0p&0p;1p;2p;3p;4p;6p;7p;<p;8g00?3j1^Tg00iJk20?Tg02L<j1}Tg02M8j2STg000Gj11Tg00L8j1yTg02N2j1\Tg028@j3_Tg02Nmj3RTg004ij1oTg003[j2`Tg000lj1:Tg001Jj2]Tg001gR0j2;Tg002CR1j22Tg01:ik106Tg005mj1=Tg00YKj23Tg02Ofj24Tg00>Sj1kTg00OTj3ETg02P^j2gTg02Q\j1<Tg02RUj2mTg02SNj1qTg01n`j2dTg02THj16Tg003Aj3>Tg02UAj1QTg00EAj2@Tg02V;j18Tg02W5j1cTg02X0j1aTg00ijk30>Tg02Xjj2JTg00m3S00j2?Tg00>9j2ITg017Pk20=Tg01<]R2k20<Tg01=5R3j1nTg01=Uk408Tg01><j1iTg00E^j2MTg007dj2PTg00<Lj2ZTg00=4j3XTg00=Xk205Tg00M7j1YTg00N?j2[Tg00\bj3hTg00Nhk203Tg00?Sk102Tg00Ggj2fTg00P4j4bTg00@1k101Tg00@Oj1|Tg00A:j2GTg00HEj2eTg00Hhj1{Tg00PRj3TTg00BAj2xTg00Bcj2zTg00COj3wTg00Cnj4~Tg00Ikk300Tg00Ygj4jTg00K]j4ATg01Khj2vTg01Cdj6uTg01CHj6tj7lTg011<k204Tg02Ydj3sTg01>am<07Tg00ZRj7rTg00[6k609Tg00[Zk70:Tg00\>j8pTg00fbR4f0R5g00gBR63>p=9%15#1p=N%15#1#1#1p=Wg00]iR7/35p=0f2R8f1R9'@/35p=5%=5#=#=#=p=C%15#1#1#1#1#1#1#1p=Lg01BNR:?s95p=Fg02Z;S019>45p=H%85,@9p=O%Q5,@9p=7g01?FR;g00^GR<P2P3P0g01?ef4R0f3R3P8g01@GR2P9P5N<07p>0;P<P9g00b2P5Cjp=DP9g00_LR=g00_kR>P>g00`KR?P5g00`kFrp=BP9P=P>P>P?P5J09p=VP8P=P>P>P?P9P5K0:p=UP3P=P>P>P?P8P9P5Gpp=Kg02Z[#^20?<;R;#^g02@`R=#}R@/S9#9g00bYRA#1RB#NRC#1RD#1RE#1RF#1#N#WRG#yRH%\8=_;97R7#9g01Xa%oFRIp,2sp'`RJ#0RK%:BRL%:FRF']RM,;JS02'2RNp,5HCEIL$06ROg01AK;5JRP%=A#CRQ#=#C#CRR#1#C#C#1#N#W#L#L#:RS/3O%=R#C#C#1#N#W#L#L#:,3OS03'2RR'2RT'2P1PNPTf5RU/40%k:RV5E:,g=P5P1PPPRf9RWf8S04'4=E:V,g=P5%<5RX,m@#9%q=R=/dX,`I%65RY5><%Q5RZ,@Y#0%85R[,3ZA5Y[M%c5RY,S@#9%\Y%a55_;9RZ[#9'2'2'2'2'2'2XV:R[f<f;'4RZ=E:V60>:f>RYf=R\'4=E:V,F9S05f?/4Y=E:V,F9S06%<3%<8'J#HS07%60RY/O0S08%63R]/73'3%8317Y0S0955]'?[[[^X:^W:P:P[PZPV%<ZR],m@#91d=],`I%6ZR]5><R=%QZRY,@]#0R^%8ZR_,3YS0:A5]_MS0;%cZR`,S@#9S0<%\`%aZ5_;9RY_#9S0='2S0>'2S0?'2R_'2RY'21I46R;P=PY1I<]P^P_g016Vp,2LF+0=R_00<2%n_R]%n2RY';R=P_P]1I<]PY1I<YI0;p,3LFnH08S0@P=%i2S0A%0YS0B%i_S0C%0]S0D%:DRD,MJS0E%0D1PJD#0[\KS0Fp,5pconsRD%:CRC'MR]%0D%0CR_1PDC#0[[RD%:QRQ,ZLRY1;7LR2%0Q1]LQRZ,;7[R`[R@%0LRag00e4RbAXLQ9UW1RQ%0Z\b^1aRc%:ERE,ZLRd%0E1]LERe,;7[Rf\2RgAXLE9VbX1aRE%0e\b^1aRh1ZLFRi%0F1;7M[Rj\2RkAXLF9VbX1aRF%0M\b^1aRap,4thisRl/MCRm%0l1PlC#0\_[Rlp,2poRn/MCRo%0n1PnC#0\_[R_p,4TIDRRnp,3tidRC#0Rp1;CeRC'2ReP1PpPC1@JH#0RqP5p,3ICNRrp,6icountRs#0Rt1;sZRs'2RZP1PtPsPqP5P\g00eP2057L'IP2eR2O1R\Pjf@RuP2O1RvPffCRwP2O1R2P`p-0Rxg00f6Ryg00h?Rz#Y#YR{#Y,[<1[<{1[<z5h<5h<g00h^+03%kyRz3E%^yRyP<&02<R{P9P<1f<8P8P{CbCb&01<R|%|<R}1G<S%=B,e<RB'D,B}1V}05U}%{>R>P}%1G#:RG,G<9T<B1e<ARA'D,B}P>P}1G<7RB/DA,B}1V}U5U}P>1G<HR~9T<A,DB,B}CKCKCK1x}?R?P5P8P;1z58#9dAw<79C~R;b>bFbGX:<XK<X9xWJ13S9/28A58G9%08/2U1@3H#0[[[^:<^K<^9x^JxP5Q02Q03POPJfKfLfPROO7b=b4b3b2X;sX8tP9P5O2n2001000000121000000b5X7CX0pP9P5O2n2001000000121000000b5b?b@bAb2bBb3bCb4bDbEbIbHb<PqeP^eQ0:Q0?Q0@P=Q0AQ0BQ0CQ0DQ0EQ0FP]PDPYP@PQPcPdPgPEPhPiPkPFPaPmPlPoP_PnPeP1PpPC13H7RHP5PrPZP1PtPsPHP5P\PjPvPfP2P`PzPyP{P|1D~B,B}P?P;b>bFbGPHP5b=b4b3b2X;sX8tP9P5O2n2001000000121000000b5X7CX0pP9P5O2n2001000000121000000b5b?b@bAb2bBb3bCb4bDbEbIbHb<PHeQ0:eQ0;Q0>Q0@P=Q0AQ0BQ0CQ0DQ0EQ0FP]PDPYP@PQPcPdPgPEPhPiPkPFPaPmPlPoP_PnPeP1PpPCA5J7MReP5PrPZP1PtPsPeP5P\PjPvPfP2P`PzPy1f<9P|P}1V}3P<PAg00aK1G<L>00<IRICj,B}5U}P>AT<AB/DI,B}CKP?P;b>bFbGX:<X9x1;5M,29A597M[^:<^9xP5PKPJPOO3b=b4b3b2X;sX8tP9P5O2n2001000000121000000b5X7CX0pP9P5O2n2001000000121000000b5b?b@bAb2bBb3bCb4bDbEbIbHb<PeeQ0;eQ0<Q0=f:Q0<ePWQ0=eCACACACACACA1v:[EuQ05Q06Q07Q00fAR[/4u=>:01F0V%6URu%8UQ0935Q0817uU'3'?P8fBRu/4[=>:UP:14wuRuf6R[#<,JX#H%69Re/O9Rpf7RC#6Rt/7CRs'31OtCRt17e9Re'3'?]6XL:%<u%<U'J#HQ00fDRu/4w=>:[1F[VfERw/4uRu#6RO%8u;5s17Ou,3t'?P0A>:uCP:fFRu/4wRwfGR0/4uRu#</JX#HfH/40R0#6RX/O0RO/3e17X0RX,3p'?]6XM:%<wRw/Jw#HP4P6P4PxP5Pbg00gbRbn0110000020000XT4g014;Q01P5EtPb13OXRX/?X0045b0W6Q04P5P8FlW0P5O11FCVPb%6uRC%8u%6WRX/7W35%8W17Cu55X'?P5n010000000W0P5O1n200100000021000010000W6P[P5P8FlW0P5O11FUVPb%6[Rb/7[,3t%8[=5bs'?P5n010000000W0P5O1n200100000021100010000W6W8W7XM:XL:CAXRRXQPP9P5O2n2001000000121000000X0TXPNP9P5O2n2001000000121000000b0WOWNWUWSo"). Qed.

  Lemma P1w_step : forall T ks m m', P1w m -> munch (winsT [tS0 T ks]) m m' -> wmono asegs m m' -> mem_inv asegs m' -> P1w m'.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnQ ()) ["P1"] "h02Hah12H0h27__sat20h37__sat22h44__x1h51ah63iv'h72H1h82H2h92H3h:4LFn0h;2MUh<3MU0h=1Th>2WMh?3WM0h@2_HhA7__arithhB4__ffhC7__sat17hD7__sat18hE7__sat19hF7__sat21hG7__sat23hH7__sat24hI8__varmaphJ5__withK4cstrhL5cstr0hM2ivhN2kshO1mhP2m'p;1p;2p;3p;4p;7p;6p;<g00?3j1ATg00iJj2VTg000Gj11Tg004ij1JTg002^j1XTg01OLj1qTg01DEj1PTg003[j2cTg000lj16Tg008Dj2KTg00>Sj1DTg00OTj3?Tg01E=j3<Tg01F:j39Tg02Ofj2=Tg02[Uj1FTg01G7j2UTg02Ydj3ETg00YKj22Tg002CR0j23Tg01RHj2`Tg02THj1MTg02UAj1OTg00EAj24Tg02V;j1NTg003Aj3LTg00>9j2;Tg00o0j3^Tg017Pj2]Tg01<]R1j2\Tg01=5R2j1ITg001gR3j25Tg01=Uj4ZTg01><j1GTg00E^j2>Tg007dj2@Tg005mj17Tg00<Lj2YTg001Jj2WTg00=4j3HTg00L8j1yTg00=Xj2xTg00Ggj2wTg00@1j1vTg00@Oj1pTg00HEj2oTg00A:j2CTg00Q5j3lTg00PRj3TTg00Ygj4QTg00[Zj7jTg00BAj2iTg00Bcj2gTg00COj3fTg00Cnj4hTg00K]j4RTg01T]j4eTg01Khj2kTg01Cdj6dTg02\Qj3mTg02]Qj6nTg02^Uj6bTg02_Xj6aTg0137j4rTg012=j3sTg012Zj3tTg01>al<uTg00ZRj7_Tg00^GR4P4f1R5f0R6Crp=BAs446p=:At446p=8g01?FR7P4P1P2P3g01?ef4R3f3R2f2R1g01@GR8P5P6M<up=[g00]iR9/26p=0P5g00_LR:g00_kR;P;g00`KR<P6g00`kF_p=Sg02Z[#A1V47#Ag01X0g00bYR7#1R=#1#1R>#1R?#1R@#1RA#JRB#X%J>#X#q[%P5P01V44RCp,2sp,cBRB%1A#1#1#1#1#1#1RA#6RD'KRE/BBRF%DCRG3?RHp,2m0RI;<1g01W9RJ?9I1g01BNRKf5RL/=3%DKRM3?#F?<21A9J321UJ3%PL[[[P6A<HI3A9JILf8RNf7RO'==?KM#Ff6RP;<LA9JOP1UJOA<HINA9JINPHPIf9ROPNP3f;R3f:'=RP=?KM#FRMPHPOPNPCAEC6HRK%:6RL%:5'2%85%86RQ'2'3'3X6C,`CXMCRR%MPRS%OP'4%NP,4S'BRSPGPCf</=3R3#MRP%O3'4%N3,4P'BRP#:,2L%8P/2Q'3,3KX6CPFAECFH%:F%:S'2%8S%8F'2'3RSALCFFAECFG1;CF3^g016Vp,2LF']RF/\8%IFRG%I8RK'5RQPFPG1;4GPK1;4KD[p,3LFnCZPQ%G8%0K%GF%0G%6?R?,>B%0B%0?1@B?#0[[p,5pconsR?%6>R>'>%0?%0>RG1@?>#0[[%6=R=%77#7#7#7#7#6R?'Y159=RF%0?1W=?RK,59[R8[%0=RQg00e4RPAH=?5UW0%0K\P^0Q%6@R@,Y=%0@1W=@R?,59[RL\FAH=@5VPX0Q%0?\P^0Qp,4thisRQ/>>%0Q1@Q>#0\G[p,2poRQ/>>%0Q1@Q>#0\G[p,4TIDRp,3tidRG#0RQ15G?RG'3P0PQPG%yARA,4B,2E14B9/2B'3REP6p,3ICNp,6icountR?#0R>15?KR?'3P0P>P?PEP6f=g00eP1x9=';PFeRFO1PLf@PFO1P8g00f6R8#D%A81w45%v4%p4R8P:P;P;P<P41o47R71C4D5l4g00b2R;1C4A9T47CQ,S8P41C499T47P;P7CQ,S8Fj1i8<P6P1g00fbR8g00gBR<';1g61=L8<dAf495ChbBbIbJX441K6D146A'21469/26'3^44P6PBO1bAb3b2X9?X8>P5P6O2n2001000000121000000b5X7GX1QP5P6O2n2001000000121000000b5bCbDbEb2bFb3bGbHbLbKb:PSeCRCe1kCREd9mMHP1EnEbPJPIPOPNP2P5EaCRW@W>W;W?W<P5P6O2n2001000000121000000W1WPWOWNW=o"). Qed.

  Lemma tabs_ok1 : forall m T ks, P1w m -> mem_inv asegs m -> ftbl Wp0 spz m T -> fin (-8192) 0 ks = true ->
    tabs_ok Wp0 m [tS0 T ks].
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnQ ()) ["P1"] "h01ah12H0h27__sat20h37__sat22h44__x1h52Hah64__x2h74__x3h82H3h92H4h:2H5h;4LFn0h<7__arithh=4__ffh>7__sat17h?7__sat18h@7__sat19hA7__sat21hB7__sat23hC7__sat24hD8__varmaphE5__withF4cstrhG5cstr0hH5cstr1hI1khJ1whK4__p1hL4__x4hM2F1hN2H1hO2H2hP2H6hQ2HThR2HihS3LO'hT2MIhU2PWhV2SThW1ThX1WhY2_HhZ3_H0h[2ksh\1mh]1tp%0p&0p;1p;2p;4p;3p;7p;5p;6p;9p;<p;8g00?3j1QTg00iJk203Tg01DEj1qTg01G7j2fTg000Gj15Tg004ik102Tg003[j2yTg02`[j4RTg00L8j1lTg02Nmj3hTg003Aj3TTg01\Bj3eTg01H3j1MTg01Hmj1BTg01Ikj4>Tg002CR0j22Tg02Ofj2@Tg00>Sj1STg00OTj3PTg02aUj3ZTg02THj1ITg02W5j1WTg0137j4pTg02X0j1UTg02Ydj3XTg00EAj21Tg01=5R1j13Tg02bSj4?Tg02cMj7gTg00YKR2j24Tg00M7j17Tg01l:R3j26Tg008Dj2DTg02dIj5dTg017Pj2cTg01<]R4j2bTg001gR5j2=Tg00>9j2;Tg01=Uj4`Tg01><j1LTg000lj18Tg00E^j2KTg007dj2JTg005mj1ATg00<Lj2_Tg001Jj2^Tg00=4j3]Tg00=Xk201Tg00N?j2OTg00\bj3\Tg00Nhk200Tg00Ggj2CTg00P4j4NTg00@1j1~Tg00@Oj1}Tg00HEj2ETg00A:j2FTg00Q5j3YTg00Hhj1xTg00PRj3GTg00BAj2uTg00Bcj2oTg00COj3rTg00Cnj4sTg00?Sj1nTg01lTj6tTg00[6j6mTg00[Zj7vTg02eKl9wTg00K]j4kTg01Khj2zTg01Cdj6{Tg01>al<[Tg00Ygj4jTg00ZRj7|Tg00\>j8iTf0R6g00]iR7'4p=<g01?FR8g00^GR9P4P1P5g01?ef4R5f3R4f2R:g01@GR;f1R<P6M<[p=a1476p=0P9P<g00b2P6Cjp=9P<g00_LR=g00_kR>P>g00`KR?P6g00`kF|p=:P4P=P>P>P?P:P<P6Gip=HP8P9P3P1P2g02FKf5R2P5P4P:P<P6M<[p=Vg01X0g02Z[#Q20398R1#Q%q:g01W9R3/f4g02@`R@g00bYRA#5RB#5RC#5RD#5RE#5RF#5RG$02p,2sp'yRHP5P4CRg00fbRI%5G#5#5#5#5#5#5RG#lRJ?h74g00gBRK3Tf6RL?e4:%ML%BLP3PLp,2loRMPHC>'2'2P0f7RN#M%BNP3PNPMPHC>'2f8ROg01BNRP1@NL%SPRQ3P5Z@P6f9RR#Mf:RS#BP3PSPMPHC>'2P0f;RT#BP3PTPMPHC>f<RU1@TS=PPQ5Z@P6f=RT#BP3f>RVPMPHC>PPP@%I6f@RW%W6CRP9P8P<P6CpRX%U:5X1P3fC%I4/1:%3<RYC?[^J8^I9'2X]PRZ1@VTRVPQP@%IVf?R@%WVCR1@W@#U9X1XRXP3fBfA/@W#I/1:PYC?S00[^J8^I9PSPJP7PWP:P<PUP6Fg14J:11:Y#<g00h?RY#7RS/6<%7SR1#7#7#7#7#7#7RV,6<'2'2'2P014J4RQ%3:,14#<16S:16:V'2'2P3fD11H5%34C?P614J2%32,1L#<16S2162V'2'2P0%3L,1N#<16SL16LV'2P3fH11HO%3NC?P6%3O,1R#<16SR16RV'2p,2LOg01AK,DH,4MP3fLRRPMPHPTDdP3PRPM1DHMR3C?fMPMP311HT%3UROP6g016Vp,2LF'cRN/b;%3NRL%3;R2'=R[PNPL1;9LP21;92Dap,3LFnC`R\P[%L;R;%02R2%LNRN%0LRL%L@S01%3@#0S02%8ERE,KHR@%0H%0E1JHE#0[[REp,5pconsR]%8DRD'KR^%0]%0DR_1J]D#0[[R]%8BR`%AARa#A#A#A#A#8Rb'_Rc1=7`Rd%0b1^`bRe,=7[Rf[Rg%0`Rhg00e4RiA]`b<UW5Rb%0e\i^5hRj%8FRF,_`Rk%0F1^`FRl,=7[Rm\dRnA]`F<ViX5hRF%0l\i^5hRhp,4thisRi/KDRo%0i1JiD#0\_[Rip,2poRp/KDRq%0p1JpD#0\_[R_p,4TIDRRpp,3tidRr#0Rs1=rlRr'2RlP0PsPrfKRt,1HRu,4MP6p,3ICNRvp,6icountRw#0Rx1=weRw'2ReP0PxPwfPRy,1HRz,4MP6PTg00eP2017`';PdeRdO1R`PmPWPdO1RdPfg00f6RT1O911O9S1O9Y5\95\9g00h^+00%STRY3P%QTRTP91C9:P<1C94S03CN%~9R1%}9R{1E9AR|1E9BRB%5G#8RG,F95Y9'9,:{%x>R}P{1F9J1E9aRa'9,:{P}AG9BaRJ,9|,:{CHCH1u{?R~P6P:1;IK1o6:=TIKdAr97<CsRKb=bDbEX49X69X791D<G,461145,4:\Q[^49^69^79P6fVRQPHPMfJRGPyO5b<b3b2X:wX9xP<P6O2n2001000000121000000b0X8rX1sP<P6O2n2001000000121000000b0b>b?b@b2bAb3bBbCbHbGbFb;P\P[P;P2PNPLQ01Q02P@PEP^P]PcPgPbPjPkPnPFPhPoPiPqP_PpPlP0PsPr%3G,1u11M3R3'4P6PvPeP0PxPwfO#3,1z/43P6P`PmPdPfPYPTP9P91C95P:%n9CNP<Q03CNP1P{1F97R7,9J,:{P}AG9|B=G9a1E9CRCAY9|C5G9'9,:{CHP~PKb=bDbEX49X69X79XL911<:RC#<11C41D<5,15'4[^49^69^79^L9P6PMfU#3PQPHPRO5b<b3b2X:wX9xP<P6O2n2001000000121000000b0X8rX1sP<P6O2n2001000000121000000b0b>b?b@b2bAb3bBbCbHbGbFb;16SURR16UVRH'2%8ARA/4ORM14ODR5'2RCPRPHPMP5PSPA1;9APUPO1;9ORSEVPUPOPSPVPD1;9DEVEtP:C`PCP\P[P;P2PNPL%LW%3W#0P@PEP^P]PcPgPbPjPkPnPFPhPoPiPqP_PpPlP0PsPr%3t#0P6PvPeP0PxPw%3y#0P6P`PmPdPfp-0RfPYPT1C9<P1P{P{P=P>P>P?1F9A/9|,:{P{P=P>P>P?P4EmFvP}197|,:{CHP~PKb=bDbEX49WK14A6/2<%0<[^49^KfP6%3QRQ/4DPQfIO3b<b3b2XPwX:xP<P6O2n2001000000121000000b0X9rX1sP<P6O2n2001000000121000000b0b>b?b@b2bAb3bBbCbHbGbFb;b1M9wbXbSW8WOP<P6O2n2001000000121000000W1WNP<P6O2n2001000000121000000b0Q00eXRXXJ8XI9Ck1zPZE{WVWZP<P6O2n2001000000121000000W1WYP<P6O2n2001000000121000000b0WMWQWTWUW[WWW\o"). Qed.

  Ltac dkrun1 HRT HSF HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS0 SF []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] (kst_p1 ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp0) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          eapply (dk_runN Wp0 [tS0 SF ks1] (tabs_wf1 SF ks1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    P1w (P1w_step SF ks1) Q R F pc fc m ro RT [] kst_p1 fuel stops (SCR [] [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok1; [exact HP | exact HMI | exact HSF | vm_compute; reflexivity]
          | exact HP | exact HMI | apply kst_p1_ok; [exact HP | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end
    end.

  Lemma HHb : asan_rt_hyps H.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnQ ()) ["P1"] "p;3g02fJj30Tp,5HCEILp,1Hp,4HHbp30o"). Qed.
  Lemma SM4 : stack_malloc_stmt H 4 AFS_MALLOC_4.
  Proof. exact (ah_fs4 H HHb). Qed.

  Lemma po_this : this + 272 <= po \/ po + 20 <= this.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnQ ()) ["P1"] "p'0h04__x1h12H0h27__arithh34__x2h44__x3h51Hh64__ffh78__varmaph85__with92H1h:2H2h;2H3h<1Lh=2S4h>4__x4h?1eh@1qhA1rhB1si001shC1EhD2E8hE1GhF2G2hG1RhH2S0hI2T8hJ7__sat10hK6__sat9hL1oi011oi021bi038bv_is_wfi04;bv_unsignedi051gi061li071zp;1p;2p;3p;4p;6p;7p;8g000Gj18Tg005mj1JTg000lj1<Tg00EAj20Tg00mMj2_Tg00YKj27Tg00n4j2GTg00nPR0j2`Tg00m3j2gTg00o0j3dTg00oJj3cTg00D`j2STg010cj1bTg00;oj2QTg00;Rj2?Tg007dj2OTg00G@j2\Tg001gj22Tg002Cj25Tg03:5j2UTg03:\j2^Tg03;Bj2aTg00=Xj2hTg00>9j2WTg00L8j1fTg00LVj2eTg00M7j1DTg00N?j2@Tg00MVj3LTg00Nhj2KTg00>Sj1TTg00OTj3BTg00?3R1j1RTg00Ggj2FTg00P4j4MTg00@1j1}Tg00@Oj1|Tg00A:j2>Tg00A]j6{Tg00Hhj1zTg00HEj2ITg00JNj3HTg00BAj2yTg00Bcj2xTg003Aj3CTg00COj3wTg00Cnj4tTg00FOj2]Tg00QXj2VTg00?Sj1sTg00Ygj49Tg03;hj6rTg03=0j2qTg01CHj6NTg011<j2ZTg03=hj7pTg03?4j3oTg004ij1YTg002^R2j1nTg01OLR3j1mTg005Gj2PTg03?lj4lTg01Qfj2XTg00\bj3kTg00ZRj7uTg00PRj3vTg00\>j8jTg00[Zj7iTf0R4#8#8p==g00^GR5g00]iR67C4p=Ef1R7=C54p=31764p=4Ak574p=6P5P7g00^eP4C9p=AP7g00_LR8g00_kR9P9g00`KR:P4g00`kFup=1Av574p=:f3R;P8P9P9P:f2R<P7P4Gjp=;P<P8P9P9P:P7P4Fip=[p,4thisR=g00bYR>#8R?#8R@#8RA#J#=#=#<RB'0RCp,2poRD'_17CDRE1GCDRC'`P0PEPC%J?#=#<RF,0DRG/7=RH,gERIP4AdEH4X<EP4O11_G=1GG=RG,`HP0PHPGPIP4AcEH4X<HP4O1%<ARH,SD%EHRE#bR01QDHRJ,?H1ODHRK'0,3D[1\DH126HRL%4K12KH'5[1UDH12H6RM12HK17K6'5[1^DH%EJ\E1aDH13KD\EPJP5PKP5f5RKg00eP1h6H'WPLeO1RN%44124H'5ROg00f6RP%f>,e5RQg00h?RR#DRS#DRT,@5RU5L51@5SRV9L5Q1@5RRR'6'6g00h^RW'K16VRRR,6U/KW%TPRX5BP3B%RPRYP51F5<P71F5;RZCM%}5R[%|5R\P\P\P8P9P9P:1>5HR81>56R]'A,1\E{%z9R91I5>R^1I5?R?9H58%J>,I5R>':'A,1\C;P9P\1A>],1\P9AH5?8,A^,1\C;C;1y\:R:P4P<g00fbR]g00gBR_'W1x4<=C]_dAw567CtR_b6b7b8X05X35X45R]g00gbR`\E1?H</0;,37[%E;1?;HRa,3<Rb[[^05^35^45RcP4P<P;PDf8Rdp,3DS8O5b2b1bAb@b;b:b9b1b51?JH,3D1S=H1Q=HRe,?H1O=HRf'0,3=\01\=H%4f12fH'5\L1U=H12Hf17f6'5\M1^=H%Ee\E1a=H13f=\EPeP5PfP5PNPOP]PcP4P<P;P=Pdp,3TH8O5b2b1bAb@b;b:b9b1b51?eH,3=1]=H%4=%4HRc%4e[[1]DH%4D%4J\c[%DTRT#DRc,@59L5QRQ1@5T/6U'6%Dc,@516QV'61KRW'V'V=BPXPYP5P5f4RP,F5P<%s5CMP7PZCMP[P\1I5@=H58,A^,1\P9P\AH5>8,A?,1\P9P\P51>5FR>,:?g0154R8P^C9,1\P9P\P51>5B,:^P8P?C9,1\P9P5P^g00b2R9%8AR8#<RZ,>5RR,:?R?C9,1\P5P?g00aKR?%J@#8#=#=#<RW,>5,:^C9,1\5[\C;C;C;C;P:P_b6b7b8X05X35X45X>5134a10;F/G<10;B/GP10KZRB,7P10PW,2B'5[[\b[^05^35^45^>5P4PePJPDP=P;PPPKPdO8b2bKbJ10DZRd,7=10=W,2d'5p,2m0RKP=PWPdp,3THAP4Er1qKdPKPDPFPdp,3DSA1OFHRW#ER=P5PWP5p-0RPP4P`g00e4R;P`n011070003001000010000X?5g014;RJP6P4ENP`1Z`4Reb5WC%b=ePXPY1F57P[P51:^RRRP9PRC9,1\P5PRP?1:^>C9,1\5[\P:P_b6b7b8X05104ZRZ/7Z104F,2Z'5^05P4PDO1b2FpAoKdW%YARA#nRW#RRD#mRZg03@]PK%=8#Y1QdHg02J]'0'PPSCl%<@,PA%TWR@5BW,XDRS9CZ4XLZP41PA6=BW@,XDR@P7ENACZ@SPZP@P3PDPPP4P1PWPPP4P`P2PAPPP7P5PPP7P;P`P`n011070003001000010000n101102000120104103n10110600020020102106P`n10110100021010600X?ZPJPSP4ENP`Peb1b=P`eb=bHbGbIbD,ZIXFGP4O1n200110000021010611105bBXECP4O1n200110000021010611105bBo"). Qed.

  Definition W1 (ff fp : Z) : list (Z * Z) :=
    [(spz - 8192, spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 1024); (sh ff, sh ff + 128)].

  Lemma new_frame : forall m ff fp, as_RFS H ((4, ff, fp) :: LF) m ->
    fresh_frame H LF 4 ff fp
    /\ (ff + 1024 <= po \/ po + 20 <= ff) /\ (ff + 1024 <= pcons \/ pcons + 48 <= ff)
    /\ (fp + 1 <= pcons \/ pcons + 48 <= fp) /\ (fp + 1 <= po \/ po + 20 <= fp)
    /\ (hull_hi (po + 20) <= ff \/ ff + 1024 <= hull_lo po)
    /\ po + 20 <= aceil /\ po + 20 + 64 <= AAPP_HI
    /\ (ff + 1024 <= this \/ this + 288 <= ff) /\ (fp + 1 <= this \/ this + 288 <= fp).
  Proof using HCEIL H HHbp this po pcons LF DSin PCfs THfs.
    clear Ha0 Ha1 Ha2 TIDR DSA DSW DSO DS8 DSV PCA PCO PC8 PCC DISJ ICN THA THO TH8 THC1 THC2 UM0 USH UBL STK CEIL LO SP16 SPHI SPOBJ MI0 AC0 LV0 TP RFS0 LFn THR.
    intros m ff fp RF.
    pose proof (fresh_of_RFS H HHb LF 4 ff fp m RF) as FRESH.
    destruct (ah_RFS_range H HHb _ _ RF) as [FO FR].
    pose proof FO as (B1 & B2 & B3 & B4).
    pose proof (FR (4, ff, fp) (or_introl eq_refl)) as (K1 & K2 & K3 & (K4 & K5) & K6).
    cbn [ff_class ff_addr ff_flag fst snd] in K1, K2, K3, K4, K5, K6. unfold fsz in K3. change (64 * 2 ^ 4) with 1024 in K3.
    pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    assert (FRM : forall f, In f LF -> (ff + 1024 <= ff_addr f \/ ff_addr f + fsz (ff_class f) <= ff)
      /\ as_FSB H + AFS_HDR <= ff_addr f /\ ff_addr f + fsz (ff_class f) <= as_FSB H + AFS_SIZE
      /\ ff_addr f mod 64 = 0 /\ fsz (ff_class f) mod 64 = 0).
    { intros f Hf. destruct FRESH as (_ & _ & D). destruct (D f Hf) as [D1 _].
      unfold fsz in D1 at 1. change (64 * 2 ^ 4) with 1024 in D1.
      pose proof (FR f (or_intror Hf)) as (L1 & L2 & L3 & (L4 & L5) & L6).
      split; [exact D1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
      unfold fsz. rewrite Z.mul_comm. apply Z_mod_mult. }
    assert (FSO : forall O n, fsobj H LF O n -> (ff + 1024 <= O \/ O + n <= ff) /\ (fp + 1 <= O \/ O + n <= fp)).
    { intros O n [OB | (f & Hf & F1 & F2)].
      - clear - OB K2 K3 K6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *. lia.
      - destruct (FRM f Hf) as (D1 & L2 & L3 & _). clear - D1 L2 F1 F2 K6. unfold AFS_HDR, AFS_FLAGS in *. lia. }
    destruct (FSO pcons 48 PCfs) as [PC1 PC2].
    destruct (FSO this 288 THfs) as [TH1 TH2].
    pose proof DSin as (f & Hf & F1 & F2).
    destruct (FRM f Hf) as (D1 & L2 & L3 & L4 & FM).
    split; [exact FRESH|].
    split; [clear - D1 F1 F2; lia|].
    split; [clear - PC1; lia|].
    split; [clear - PC2; lia|].
    split; [clear - K6 L2 F1 F2; unfold AFS_HDR, AFS_FLAGS in *; lia|].
    split; [unfold hull_lo, hull_hi; clear - D1 F1 F2 L4 FM K4; Z.div_mod_to_equations; lia|].
    split; [clear - F2 L3 B2; lia|].
    split; [clear - F2 L3 B2 A1 A2; unfold AAPP_HI; lia|].
    split; [clear - TH1; lia | clear - TH2; lia].
  Qed.

  Definition quiet (a : Z) : Prop := (this <= a < this + 272) \/ (exists A n, In (A, n) (lbl LB) /\ A <= a < A + n).

  Lemma quiet_foot : forall a, umap_foot 32 (this + 136) bl bc ents a -> quiet a.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnQ ()) ["P1"] "p'0h01Ah11nh22H0h31pi001ph41xi011xh52Hah63Hinh72_Hh81Bh91Eh:2Hlh;2Hph<4__x1h=4__x2h>1fh?1lh@2p'hA1yhB3HbchC7__arithhD4__ffhE8__varmaphF5__withG1ahH2a3hI1khJ1ohK2p0hL1vi021zp;1p;2p;7p;4p;3p;8p;>p;5p;Bg000Gj17Tg000lj19Tg00iJR0j2HTg005mj1=Tg00EAj23Tg03Y^j7pTg010cj1dTg00;Rj2bTg012=j2_j3@Tg03Scj4ITg02Ydj31Tg00m3R1j2QTg03ZYj1FTg03[Sj1kTg00>Sj1jTg00?3j1UTg00Ggj2iTg00?Sj1hTg00P4j4fTg00@1j1eTg00@Oj1cTg00HEj2STg00A:j2KTg00PRj3JTg00Ygj4CTg00Hhj1aTg00\>j8`Tg00BAj2^Tg00>9j2]Tg00Bcj2\Tg003Aj3<Tg00COj3[Tg00Cnj4ZTg00o0j3vTg03\Lj1uj4MTg03]Dl>tTg002CR2j24Tg03^=j5sTg011<j2rTg00K]j4YTg01T]j4DTg00oJj3XTg01RHR3j2ATg03^oj5oTg03_NlBmTg001gj2>Tg001Jj2VTg007dj2LTg03`Fj4OTg03a=j4NTg03b4j4;Tg00]Kj7nTg00YKj2BTg0137j4TTg00ZRj7gTg00[Zj7qTf3R4f2R5'Bf1R6f0R7'>'4p=5g00^GR8g00]iR97<7p=?f4R:1B451>67'4'4p=21A87p=0P8P8P6P7CTp=8P6g00_LR;g00_kR<P<g00`KR=P7g00`kFgp=GP5P;P<P<P=P6P7Fqp=RA<867p=:P8P5P6P7CTp=61467,45p=E1467,45,44,4:p=P1B56/47p=l1B56/47,44p=Wg00bYR>#7R?#7#7R@#7RA#7#9RB1H88RC/H8RDp,4thisRE%=@#7#7#7RF#9RG'3RHp,2blRIp,2bcRJp,4entsRKP7FpP1PHP6P6%=?RL#7#7#7#9RM,3HRNC5%?JRO#dRPPIP6P6%9@R@/bJRQ,3IRRD21H8DRS,H8RTP81_8SRUPKCIRV9187RWP7P5P5137BRXD2X38#0'Q%F5P7PHP5P5PNC5PEP4P4%7F#9RF,3ERNC51867p,2LB#kRY51CRZP6f5R[P[1367R\D2X18#0X08#0g00f6R]#j%U]P81i85P6%h8Cf%e8%c8R]P;P<P<P=P81S8>R>1K8G5J8R;g00b2R^1S8?R_CC,G]P8P_g00aKR`1K8M9J8;CC,G]5R]%a<P8P>P^P_CC,G]P8P_P`1K8F9J8>CC,G]5R]G`1^]=P7P5g00fbR]g00gBR=']1\75=<]=dA[896CZbDbEbFX<8X=8137GRGP6P613GMC5P6P5P5136FC5[^<8^=8P7P:PEP6O3bC3vW5P7O1PPPIP5P5PRD2PWP7P4P4PXD2X38#0'QP1PPPIP4P4PRD2PWP7P:P:PXD2X38#0%F:P7PPPIP:P:PRD2P2PPPIP[P[PRC5f6RF#FRGP7PIf8R=P=PRC5PEf9R]P]PNC5PZP6f;R>P>P\D2X18#0X08#0g03bkR`g03@]R_g03ceR^g03d_R<PBPD%u_R;PYp,2m0RaPHPIPJPKp,3UM0RbM>t%?IRc,4ORd18IQReP`P_P^P<PYDsRf51CRg,4PRh'QP1PdPhPZP6f=R1P1P\D2X18#0X08#0P7P2POPcPZP6f?RiPiP\D2X18#0X08#0RjP7PZP6fBRkPkP\D2X18#0X08Rl#0RmP=P6O1'rX7cX9OP6P7O2n2001000000120000000X2dP7O1P2PPPgPjP7P8PlPIP818I7=1CYPIfARlPl13I7D2X18PQA1CeYPIf@RePePRC5P7f7RRCYCDCDX:gX7PP6P7O2n2001000000120000000X2hP7O1n200100000021000011000bJ3XW5XBPP6P7O2n2001000000121000000W2P7O1PWP7P[P[PXD2X38#0P3P8PWP7PFPFPXD2X38PGP7PWP7P=P=PXD2P2A186VP6P]P]136BC5f:RX#FP7A184VP:f<RVPV13:BC5PEP1P1PNC5g0180RNp4p710R1PNp4p7210RNP6\6RE%U5RVP2P:P4P5P6CI9147P:P7O1=<[5A1F74'4X4[,A[[RWP4P7O1=<:6A1[75'4X4:,A:P[P:P4P5CI91:6RG[P[P7O1=<F4A1R7:'4X4F,AF\GP:P4P5P6P7DoP6n2001000000120000000XA5W?W>W8W0PW^A5^?V^>E^8N^01P7PTP8PUPKPFP5O6A@8S7RU/:RA1T7KR1'4X4T,ATP3PT1:U=/41X4TPmP7P0P8PS1:U>/41PZP6fFR1P1P\D2X18#0X08#0[P7P0P8PDA6S57R09@8S/:iA1T0K'4PZP6fJR0P0P\D2X18#0X08#0[P7A6D6796S[Ri9@8S/:kA1TiK'4P2A6D5696SFR59@8SfC':A1T5KPZP6fNR5P5P\D2X18#0X08#0P7A6D:496S=9@8SfE':A6D[:96S]=1TKP8fGR]A6DRF96S7=1TKPZP6fSR:P:P\D2X18#0X08#0]6X@8A6DF[96S]=1TKP`P_P^P<PBPDP;PYPaPHPIPJPKPbfHRbPRPFP7MBm18bB=1Cf1>9b13bB%9?R?%=L#=#=#9'VRL%9ARA,Lb#?P_Pa13b@PRCOP_Pa13bAPRCNP9PRPR1V?BR?C5P_PaPbPFCMPbPBPHPMC;fIRFPBPIPQC;\P3EDP3l3EP218FB=1Cf1>9F13FBPL1LFA#?P_Pa13F@P=COP_Pa13FAP=CNP9P=P=P?C5P_PaPFPRCMPFPBPHPMC;P0PBPIPQC;\P3EDPCWPZP6fTR0P0P\D2X18#0X08#0P7fK/8B=1CffLRf,>913fBPL1LfA#?P_Pa13f@P>COP_Pa13fAP>CNP9P>P>P?C5P_PaPfPXCMPfPBPHPMC;fMRMPBPIPQC;\P3EDPCWP8PZP6fWRZPZP\D2X18#0X08PMP81857=1CYP5fVR\P\1357D2X18PB18MB=1CYPMfURYPY13MBC5P6PbCYCDCDW7W:P6P7O2n2001000000121000000bHW6PXP6P7FnW6W9P6P7O2n2001000000121000000W2XLDXI8P6P7O2n2001100000121102100XKSX@8P6P7O2n2001100000121102100X4TP6P7O2n2001000000121101000b;b27XjW5W;P6P7O2n2001000000121000000W2X38P6P7O2n2001000000121101000W2P7O1n200100000021100011000W2P7O1n200100000021100011000W2XG8o"). Qed.

  Definition UW (ff fp : Z) : list (Z * Z) :=
    [(spz - 16384, spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 1024); (sh ff, sh ff + 128); (po, po + 20)].

  Lemma out_obj : forall ff fp O N a, fresh_frame H LF 4 ff fp -> O <= a < O + N ->
    AIMG_TOP <= O -> O + N <= AAPP_HI -> (O + N <= ALOWSH_LO \/ AHI_LO <= O) ->
    (O + N <= spz - 16384 \/ spz <= O) ->
    (O + N <= as_FSB H + AFS_FLAGS - 0x1000 \/ as_FSB H + AFS_HDR <= O) ->
    (O + N <= ff \/ ff + 1024 <= O) -> (O + N <= po \/ po + 20 <= O) ->
    outside (UW ff fp) a /\ outside (UW ff fp) (a / 8 + SHBASE) /\ 0 <= a < 2 ^ 47.
  Proof using HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR DSO DSin ICN CEIL LO RFS0 LFn.
    clear Ha0 Ha1 Ha2 DSA DSW DS8 DSV PCA PCO PC8 PCC PCfs DISJ THA THO TH8 THfs THC1 THC2 UM0 USH UBL STK SP16 SPHI SPOBJ MI0 AC0 LV0 TP THR.
    intros ff fp O N a FR Ha O1 O2 O3 O4 O5 O6 O7.
    pose proof FR as ((K1 & K2 & K3 & (K4 & K5) & K6) & (B1 & B2 & B3 & B4) & _).
    unfold fsz in K3. change (64 * 2 ^ 4) with 1024 in K3.
    pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    pose proof DSO as (D1 & D2 & D3).
    assert (B4' : as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H).
    { clear - B4. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in *. destruct B4; [left | right]; lia. }
    assert (EA : a / 8 * 8 <= a < a / 8 * 8 + 8) by (clear; Z.div_mod_to_equations; lia).
    assert (EF : ff = ff / 8 * 8) by (clear - K4; Z.div_mod_to_equations; lia).
    unfold UW. cbn [outside]. unfold sh.
    clear - Ha O1 O2 O3 O4 O5 O6 O7 K2 K3 K6 B1 B2 B4' A1 A2 D1 D2 D3 CEIL LO EA EF.
    unfold ADS_STACK, AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE, SHBASE in *.
    set (a8 := a / 8) in *. set (f8 := ff / 8) in *.
    repeat split; lia.
  Qed.

  Lemma quiet_out : forall ff fp a, fresh_frame H LF 4 ff fp ->
    (ff + 1024 <= this \/ this + 288 <= ff) -> (fp + 1 <= this \/ this + 288 <= fp) -> quiet a ->
    outside (UW ff fp) a /\ outside (UW ff fp) (a / 8 + SHBASE) /\ 0 <= a < 2 ^ 47.
  Proof using HCEIL H HHbp sp m0 this po tid pcons icount lo LF LB TIDR DSA DSO DS8 DSin ICN THA THO TH8 THfs UBL CEIL LO SPOBJ RFS0 LFn.
    clear Ha0 Ha1 Ha2 DSW DSV PCA PCO PC8 PCC PCfs DISJ THC1 THC2 UM0 USH STK SP16 SPHI MI0 AC0 LV0 TP THR.
    intros ff fp a FR THF' THP' Q.
    destruct (ah_RFS_range H HHb _ _ RFS0) as [FO FR0].
    pose proof FR as ((K1 & K2 & K3 & (K4 & K5) & K6) & _ & _).
    unfold fsz in K3. change (64 * 2 ^ 4) with 1024 in K3.
    pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    assert (POF : as_FSB H + AFS_HDR <= po /\ po + 20 <= as_FSB H + AFS_SIZE).
    { pose proof DSin as (f & Hf & F1 & F2). pose proof (FR0 f Hf) as (L1 & L2 & L3 & _). clear - F1 F2 L2 L3. lia. }
    destruct Q as [Q | (A & n & Hin & Q)].
    - pose proof THO as (T1 & T2 & T3).
      pose proof (SPOBJ this 288 ltac:(clear; tauto)) as TS.
      assert (TF : this + 288 <= as_FSB H \/ as_FSB H + AFS_HDR <= this).
      { pose proof THfs as [OB | (f & Hf & F1 & F2)]; [clear - OB; unfold AFS_HDR, AFS_SIZE in *; lia|].
        pose proof (FR0 f Hf) as (L1 & L2 & _). clear - F1 L2. lia. }
      apply (out_obj ff fp this 272 a FR Q).
      + exact T1.
      + clear - T3. lia.
      + clear - T2. lia.
      + clear - TS. unfold ADS_STACK in *. lia.
      + clear - TF. unfold AFS_FLAGS in *. lia.
      + clear - THF'. lia.
      + exact po_this.
    - pose proof (UBL A n Hin) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
      apply (out_obj ff fp A n a FR Q).
      + exact B4.
      + clear - B5 A2. unfold AAPP_HI. lia.
      + clear - B7. unfold aapp, aapp_lo, aapp_hi in B7. lia.
      + clear - B5 CEIL LO. unfold ADS_STACK in *. lia.
      + clear - B6. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. lia.
      + clear - B6 K2 K3. unfold AFS_HDR, AFS_SIZE in *. lia.
      + clear - B6 POF. unfold AFS_HDR, AFS_SIZE in *. lia.
  Qed.

  Lemma W1_sub : forall ff fp, sub_fp (W1 ff fp) (UW ff fp).
  Proof using H sp po.
    clear HHbp Ha0 Ha1 Ha2 TIDR DSA DSW DSO DS8 DSV DSin PCA PCO PC8 PCC PCfs DISJ ICN THA THO TH8 THfs THC1 THC2 UM0 USH UBL STK CEIL LO SP16 SPHI SPOBJ MI0 AC0 LV0 TP RFS0 LFn THR.
    intros ff fp. apply sub_fp_of. unfold W1, UW.
    apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn [fst snd]; lia]|].
    apply Forall_cons; [exists (as_FSB H, as_FSB H + AFS_FLAGS); split; [right; left; reflexivity | cbn [fst snd]; lia]|].
    apply Forall_cons; [exists (fp, fp + 1); split; [right; right; left; reflexivity | cbn [fst snd]; lia]|].
    apply Forall_cons; [exists (ff, ff + 1024); split; [right; right; right; left; reflexivity | cbn [fst snd]; lia]|].
    apply Forall_cons; [exists (sh ff, sh ff + 128); split; [right; right; right; right; left; reflexivity | cbn [fst snd]; lia]|].
    apply Forall_nil.
  Qed.

  Lemma quiet_keep : forall ff fp W m, fresh_frame H LF 4 ff fp ->
    (ff + 1024 <= this \/ this + 288 <= ff) -> (fp + 1 <= this \/ this + 288 <= fp) ->
    sub_fp W (UW ff fp) -> Forall (fun iv : Z * Z => fst iv < snd iv) W -> munch W m0 m -> wmono asegs m0 m ->
    rw_cells asegs m (this + 8) [C8 (Z_to_bv 64 pcons)] /\ rw_cells asegs m (this + 80) [C8 (Z_to_bv 64 icount)]
    /\ umapx MI_A 32 (nval32 ASEGS) (lbl LB) m (this + 136) bl bc ents
    /\ gz m (this + 136) 40 /\ (bc <> 0 -> gz m bl (8 * bc)) /\ (forall p k v, In (p, (k, v)) ents -> gz m p 32).
  Proof using HCEIL H HHbp sp m0 this po tid pcons icount lo LF bl bc LB ents TIDR DSA DSO DS8 DSin ICN THA THO TH8 THfs THC1 THC2 UM0 USH UBL CEIL LO SPOBJ RFS0 LFn.
    clear Ha0 Ha1 Ha2 DSW DSV PCA PCO PC8 PCC PCfs DISJ STK SP16 SPHI MI0 AC0 LV0 TP THR.
    intros ff fp W m FR THF' THP' SUB NE MU WM.
    assert (UFO : forall a, umap_foot 32 (this + 136) bl bc ents a ->
      outside W a /\ outside W (a / 8 + SHBASE) /\ 0 <= a < 2 ^ 47).
    { intros a Ha. destruct (quiet_out ff fp a FR THF' THP' (quiet_foot a Ha)) as (O1 & O2 & Ra).
      split; [exact (SUB a O1)|]. split; [exact (SUB _ O2) | exact Ra]. }
    assert (AG : forall a, umap_foot 32 (this + 136) bl bc ents a -> m (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)).
    { intros a Ha. destruct (UFO a Ha) as (O1 & _ & Ra). apply MU. rewrite unsigned_lit by (clear - Ra; lia). exact O1. }
    assert (GZ : forall a n, gz m0 a n -> (forall i, 0 <= i < n -> umap_foot 32 (this + 136) bl bc ents (a + i)) -> gz m a n).
    { intros a n G F0 i Hi. pose proof (G i Hi) as S. unfold sh0, shk in *.
      destruct (UFO (a + i) (F0 i Hi)) as (_ & O2 & Ra).
      assert (RS : 0 <= (a + i) / 8 + SHBASE < 2 ^ 64).
      { assert (Q : 0 <= (a + i) / 8 < 2 ^ 44)
          by (split; [apply Z.div_pos; clear - Ra; lia | apply Z.div_lt_upper_bound; clear - Ra; lia]).
        unfold SHBASE. clear - Q. lia. }
      rewrite <- S. apply (PropExec.rdn_ext asegs 1 m m0 (Z_to_bv 64 ((a + i) / 8 + SHBASE))).
      - rewrite unsigned_lit by exact RS. clear - RS. cbn. lia.
      - intros x Hx. rewrite unsigned_lit in Hx by exact RS.
        assert (Ex : x = Z_to_bv 64 ((a + i) / 8 + SHBASE)).
        { apply bv_eq. rewrite unsigned_lit by exact RS. clear - Hx. cbn in Hx. lia. }
        subst x. apply MU. rewrite unsigned_lit by exact RS. exact O2. }
    assert (DJ : forall k n, 0 <= k -> 0 < n -> k + n <= 272 -> disjoint_from W (this + k) n).
    { intros k n Hk Hn Hkn. apply disjoint_of_outside; [exact NE | exact Hn |]. intros x Hx.
      assert (QX : quiet x) by (left; clear - Hk Hkn Hx; lia).
      destruct (quiet_out ff fp x FR THF' THP' QX) as (O1 & _ & _). exact (SUB x O1). }
    split; [eapply rw_cells_transport; [exact THC1 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat]; apply DJ; clear; lia]|].
    split; [eapply rw_cells_transport; [exact THC2 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat]; apply DJ; clear; lia]|].
    split.
    { eapply (umapx_agree ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (nval32_agree ASEGS) ltac:(clear; lia) (lbl LB) (lbl LB) m0 m);
        [exact UM0 | exact AG | intros p n _ Hl; exact Hl]. }
    pose proof USH as (US1 & US2). cbn [t3a t3b t3c fst snd] in US1, US2.
    split.
    { apply GZ; [| intros i Hi; left; clear - Hi; lia].
      intros i Hi. apply (sh0_of_addressable m0 this 288); [exact THA | change (288 / 8) with 36; clear - Hi; lia]. }
    split.
    { intros Hbc. apply GZ; [| intros i Hi; right; left; split; [exact Hbc | clear - Hi; lia]].
      intros i Hi. apply (sh0_of_addressable m0 bl (8 * bc)); [exact (US1 Hbc)|].
      rewrite (Z.mul_comm 8 bc), Z.div_mul by lia. clear - Hi. lia. }
    intros p k v Hin. apply GZ.
    - intros i Hi. apply (sh0_of_addressable m0 p 32); [exact (US2 p k v Hin) | change (32 / 8) with 4; clear - Hi; lia].
    - intros i Hi. right; right. exists p. split; [| clear - Hi; lia].
      apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin].
  Qed.

  Lemma W1_keep : forall m ff fp, munch (W1 ff fp) m0 m -> wmono asegs m0 m ->
    afsb_ok H -> aframe_range H 4 ff fp ->
    (ff + 1024 <= po \/ po + 20 <= ff) -> (ff + 1024 <= pcons \/ pcons + 48 <= ff) ->
    (fp + 1 <= pcons \/ pcons + 48 <= fp) -> (fp + 1 <= po \/ po + 20 <= fp) ->
    (hull_hi (po + 20) <= ff \/ ff + 1024 <= hull_lo po) -> po + 20 <= aceil ->
    (ff + 1024 <= this \/ this + 288 <= ff) -> (fp + 1 <= this \/ this + 288 <= fp) ->
    addressable m po 20 /\ wr_at asegs m po 20 /\ shvis m po (po + 20)
    /\ addressable m pcons 48 /\ rw_cells asegs m (pcons + 32) [C8 (Z_to_bv 64 0)] /\ LINV_P5 m /\ stk asegs m lo spz
    /\ addressable m this 288.
  Proof using HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR DSA DSW DSO DS8 DSV PCA PCO PC8 PCC PCfs ICN THA THO TH8 STK CEIL LO SPHI SPOBJ LV0 RFS0 LFn.
    clear Ha0 Ha1 Ha2 DSin DISJ THfs THC1 THC2 UM0 USH UBL SP16 MI0 AC0 TP THR.
    intros m ff fp MU WM FO FFR FFDS FFPC FPPC FPDS HULL DAC THF' THP'.
    pose proof FO as (B1 & B2 & B3 & B4).
    pose proof FFR as (K1 & K2 & K3 & (K4 & K5) & K6). unfold fsz in K3. change (64 * 2 ^ 4) with 1024 in K3.
    pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    assert (B4' : as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H).
    { clear - B4. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in *. destruct B4; [left | right]; lia. }
    pose proof DSO as (O1 & O2 & O3). pose proof PCO as (Q1 & Q2 & Q3). pose proof THO as (T1 & T2 & T3).
    assert (SHA : forall A n, AIMG_TOP <= A -> A mod 8 = 0 -> 0 <= n -> A + n <= AAPP_HI -> (A + n <= ff \/ ff + 1024 <= A) ->
      disjoint_from (W1 ff fp) (sh A) (nsh n)).
    { intros A n H1 H2 H3 H5 H6.
      assert (N8 : (nsh n = n / 8 /\ n = n / 8 * 8) \/ (nsh n = n / 8 + 1 /\ n / 8 * 8 < n < n / 8 * 8 + 8))
        by (clear - H3; unfold nsh; Z.div_mod_to_equations; lia).
      assert (EA : A = A / 8 * 8) by (clear - H2; Z.div_mod_to_equations; lia).
      assert (EN : 0 <= n / 8) by (clear - H3; Z.div_mod_to_equations; lia).
      assert (EF : ff = ff / 8 * 8) by (clear - K4; Z.div_mod_to_equations; lia).
      unfold W1. cbn [disjoint_from]. unfold sh.
      clear - H1 H2 H3 H5 H6 EA EN EF N8 K2 K3 K6 B1 B2 B4' A1 A2 CEIL LO.
      unfold ADS_STACK, AFS_HDR, AFS_SIZE, AFS_FLAGS, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *.
      set (a8 := A / 8) in *. set (n8 := n / 8) in *. set (f8 := ff / 8) in *. set (ns := nsh n) in *. lia. }
    assert (FSO : forall O n, fsobj H LF O n -> O + n <= as_FSB H \/ as_FSB H + AFS_HDR <= O).
    { intros O n [OB | (f & Hf & F1 & F2)]; [clear - OB; unfold AFS_HDR, AFS_SIZE in *; lia|].
      destruct (ah_RFS_range H HHb _ _ RFS0) as [_ FR0]. pose proof (FR0 f Hf) as (L1 & L2 & _). clear - F1 L2. lia. }
    pose proof (FSO pcons 48 PCfs) as PCF.
    pose proof (SPOBJ pcons 48 ltac:(clear; tauto)) as SC.
    split.
    { eapply addressable_transport; [exact DSA | exact MU | exact WM |].
      apply SHA; [exact O1 | exact DS8 | clear; lia | exact O3 | clear - FFDS; lia]. }
    split; [eapply wr_at_transport; [exact DSW | exact WM]|].
    split.
    { eapply shvis_transport; [exact DSV | exact MU | exact WM |].
      unfold W1, hull_lo, hull_hi in *. cbn [disjoint_from].
      clear - O1 O2 O3 HULL DAC K2 K3 K4 K6 B1 B2 B4' A1 A2 CEIL LO.
      unfold sh, ADS_STACK, AFS_HDR, AFS_SIZE, AFS_FLAGS, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *.
      Z.div_mod_to_equations. lia. }
    split.
    { eapply addressable_transport; [exact PCA | exact MU | exact WM |].
      apply SHA; [exact Q1 | exact PC8 | clear; lia | exact Q3 | clear - FFPC; lia]. }
    split.
    { eapply rw_cells_transport; [exact PCC | exact MU | exact WM |]. cbn [cells_size csize Nat.add Z.of_nat].
      assert (SHF : sh ff + 128 <= pcons \/ pcons + 40 <= sh ff).
      { clear - Q1 Q2 Q3 K2 K3 B1 B2 A2.
        assert (E : ff / 8 * 8 <= ff < ff / 8 * 8 + 8) by (clear; Z.div_mod_to_equations; lia).
        unfold sh, ASHADOW_BASE, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, AFS_HDR, AFS_SIZE in *. set (f8 := ff / 8) in *. lia. }
      unfold W1. cbn [disjoint_from]. clear - SC PCF SHF FFPC FPPC.
      unfold ADS_STACK, AFS_FLAGS, AFS_HDR in *. lia. }
    split.
    { eapply LINV_P5_cl; [exact LV0|]. intros a Ha Hc. unfold wa. apply MU. rewrite unsigned_lit by lia.
      assert (AT : a < AIMG_TOP) by (clear - Hc; unfold aimg_client, AIMG_TOP in *; lia).
      assert (F8 : 0 <= ff / 8) by (apply Z.div_pos; unfold AFS_HDR, AIMG_TOP in *; lia).
      apply LbB_DPdK.outside_of. unfold W1. unfold sh.
      clear - AT F8 B1 K6 K2 CEIL LO A1. unfold ADS_STACK, AFS_HDR, AFS_FLAGS, AIMG_TOP, ASHADOW_BASE in *.
      repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    split.
    { eapply stk_transport; [exact STK | exact MU | exact WM |]. intros x Hx. right.
      pose proof STK as (S1 & S2 & S3). destruct (S3 x Hx) as [HV _].
      pose proof (WM (wa x) HV) as HV'.
      assert (HX : AIMG_TOP <= bv_unsigned (wa x)) by (unfold wa; rewrite unsigned_lit by lia; unfold AIMG_TOP; lia).
      rewrite (BakeStackRep.wview_high m (wa x) HX) in HV'.
      destruct (m (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction]. }
    eapply addressable_transport; [exact THA | exact MU | exact WM |].
    apply SHA; [exact T1 | exact TH8 | clear; lia | exact T3 | clear - THF'; lia].
  Qed.

  Lemma athr_keep : forall m m' x y, athr_cells m -> munch [(x, y)] m m' -> wmono asegs m m' -> aceil <= x -> athr_cells m'.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnQ ()) ["P1"] "p'0h02H0h17__sat22h27__sat24h31ah44__x1h52teh62tbh72H1h82H2h92H3h:4LFn0h;7__arithh<4__ffh=7__sat17h>7__sat18h?7__sat19h@7__sat20hA7__sat21hB7__sat23hC7__sat25hD7__sat26hE7__sat27hF8__varmaphG5__withH4cstrhI5cstr0hJ1DhK4__x2hL1ThM2HahN1xi001xhO3ctxhP1nhQ4__p1hR4__x3hS4__x4hT4__x5hU4__x6hV4__x7hW2a3hX1mhY1yhZ2A1h[2A2h\2C1h]2C2h^2C3h_2C4h`2C5ha2DJhb2H4hc2H5hd2Hxhe2MUhf2R1hg2R2hh2R3hi2R4hj2R5hk2R6hl2R7hm2R8hn2R9ho2WMhp2_Hhq2m'p%0p%1p&0p;1p;2p;4p;3p;6p;7p;5p;:p;<p;8p;Bg000Gj18Tg004ik10<Tg002^k109Tg01OLk10OTg04FAj2<Tg00>Sj1|Tg005mj1?Tg00EAR0j23Tg01`oj1KTg000lj1QTg01:ik10^Tg01RHR1j2;Tg00iJk20TTg00YKR2j20Tg019ik10bTg002CR3j21Tg01;ck10aTg001gR4j2RTg007dj2kTg017Pk20]Tg01<]R5k20\Tg01=5R6j1ITg01=Uk40ZTg01><k10:Tg003[k20YTg00E^j2HTg00<Lk208Tg001Jk207Tg00=4k306Tg00m3j2{Tg00=Xk20XTg00>9j2zTg00M7j1pTg00N?j2xTg00\bk305Tg00Nhk20WTg00OTj3XTg00?3k10VTg00?Sk10UTg00@1k10STg00@Ok10RTg00HEk204Tg00Hhk10QTg00A:k203Tg00[6k60PTg013Wk70NTg04@ak50MTg00[Zk70LTg00BAk20JTg00Bck20ITg003Aj3aTg00COk30HTg00Cnk40GTg00kJk30FTg044^j1bTg021Mk10ETg021kk40KTg01m=j4cTg045_l:eTg00K]j4wTg01T]j4nTg01`8k10BTg02>Wj4ATg0137k40ATg01E=k30hTg01F:k30gTg01>am<0@Tg00Ggk20fTg00P4k40eTg00PRk30>Tg00Ygj4tTg00ZRj7rTg00\>k80=Tg02?Um<0dTg02@:mB0cTg02FmR7f1R8$0B#Kf0R93Xp=9%89#8p=M%89#Qp=T%K8=X79p=WAX789p=Cg00]iR:/R9p=6g00^GR;1k89;a:p=7%89#8#8#8p=lf2R</38/09p=2f3R=,R:1k<8=a;:/19'1p=Of5R>f4R?13=</08/19'1'1p=5g01W9R@P=P<P8CA/19p=gP@f6RAP>P?CAP@P=P<P8CA/19'1p=JP@P>g04G?S00P?CAP@P=P<P8CA/19'1p=y1;;9p=LP;P;P?P=H0A=X><@0h89p==B0g@89p=>13=</08/19p=BP@P>P?P=CA1189,1<'1p>01P@PAQ00P>CAP@P?13=<P8CA/19'1p=FP@P?13=<P8CA/19p=@13<8/09,1=,1?p=:P@f7RBPAP>CAP@P?13=<P8CA/19'1p=EP@P8Q00P9CAp=uP@P=13<8P9CAp=]&0B9#Kp=~P@P=P<AX789CAp>0C1189,1<p=i1089,1<p>0;1R:8/19p>0?1k<8=a;:/19p=}%?9#?p=m%?9#?#?#?p=^%89#8#8#8#8#8#8#8p=s10<8/19p>0`1R:<Aa;8:/19'1p>0_P@P<P8P9CAp=q10:9p=41z;9p=Dg01?FS01P;P5P6P4g01?eP?P=P<g01@GR4P8P9N<0@p>0[1k89,0:p=N%p9#pp=V20f;9p=\P;P<P8P9H0ep=U204;9p=ZB0>;89p=PP;P8g00b2R5P9Ctp=fP;P8g00aKP9Ctp=oP<g00_LS02g00_kRCPCg00`KRDP;P8P5P9Ctg00`kREFrp=YP?Q02PCPCPDP=Q02PCPCPDP<PEFrP8P9L0=p=SP;P;P<P8H0A=X=9p>00%89#?p=v%?9#8p=_203;9p=GQ01P;P;P;P6P6P>P?P=P<P8P9N<0dp>02P;P;P;P;P;P;P0P9P8P<P0P=P?P>PAPBf8R0f9R6NB0cp=jP;P;P2PBP2PAP>P?P=P<P8P9N<0@p=dP;B0>;<8P5P9Ctp=hP?Q02PCPCPDP=P<P8Q02PCPCPDP9PEFrL0=p=`P8Q02PCPCPDP9PEFrp>0DPAP>P?P=P<P8P9CwCwp=[g03T?g00bYS03#8RE#8R5#8R2#8S04#8RF#8RG$0<RH$09RI&0<2$09$0O[p,5HCEILRJ/<=P1P;P6%|7R7,9?RKP6%?5S05#?#M#TR5,3?RL19=7RMP6Q03#?RN#8#MRO#TRP,3=RQ%K8RR1W97RS'CRTP6g04H8RU%Q2RV'3RW19<7RXP6%QORO,3<RY19U7RU%6?RZ17?VR[P?%?E#l#TR\&0^JR]%6=R^17=VR_P=%QGR`P]P<P<PV%QFRF=2<]CORaE5RbE5RcCgFJEyX5I,;IX6I,;IXJ;#LXL;#LXO;20T;;RdP=P<%|dReP>P?E=1>A>10]>1<JB[[[P9f;RfPKPfPLPMPfPQPTPfPWPXPfPYPUPcCgFJEyX5I,;IX6I,;IXJ;#LXL;#LP1P;f<Rg19>7RhPgP>P5PMPgPQPTPgPWPXPgPYPU%6>Ri17>VRjP>P\P]PbCBJ01FJFFX5I,;IX6I,;IXJ;#LXL;PdPBPAPeP6P0E=f:Rk/>610]61<Jf[[[P9f>Rl19B7RmPlPBP5PMPlPQPTPlPWPXPlPYPU%6BRn17BVRoPBP\P]PbCBJ01FJFFX5I,;IX6I,;IXJ;#LP1P;f?Rp1907RqPpP0P5PKPpP?PPPTPpPWPXPpPYPU%60S06170VRrP0P\P]PZP[P?P`P]PaE5E5FJD@FFX5I,;IX6I,;IXJ;PdPfPkPef=R[PgE=1>l[10][1<Jp[[[P9fARZ19k7RsPZPkP519A7RtPZPAPPPTPZPWPXPZPYPU%6kRu17kVRvPkP\P]%6ARw17AVRxPAP`P]PaE5E5FJD@FFX5I,;IX6I,;IP1PIfBRy19f7PyPfP5PmPyPBPPPTPyPWPMPyP=POPUPfPfPVPfP\P]PnPoPBP`P]P^P_P=PFP]D:E5CBCOGED@FFX5I,;IX6IPdPpPlPePZf@R_E=1>yZ10]ZfCR^,<J[[[P9fDRo19[7RnPoP[P51967RmPoP6PPPTPoPWPhPoP>POPU%6[Rh17[VRzP[P\P]%66R{176VR|P6P`P]PiPjP>PFP]D:E5E5GED@FFX5I,;IP1PIfER119l7P1PlP5PsP1PkPP1W<SP1PWPtP1PAPOPUPlPlPVPlP\P]PuPvPkP`P]PwPxPAPFP]D:E5CBCOGED@FFX5IPdP^PyPeP1PoE=fFS07/>110]1fGRx,<J[[[P9Px19_7RwPxP_P519g7RkPxPgPP%K?Rv/CSPxPWPqPxP0POPU%6_Rq17_VRuP_P\P]%6gRt17gVRsPgP`P]Q06PrP0PFP]D:E5E5GED@FFP3fHRr19Z7Rj'uPrPZP5PnPrP[PP%K>Ri1CR7'CPrPWPmPrP6POPU%6ZRm17ZVRRPZP\P]PhPzP[P`P]P{P|P6PFP]D:E5E5GED@D@PdPxQ07PefIR|PrE=fJS08/>|10]|fKS09,<J[[[P9Q0819^7R{'uQ09PoP5PwQ09P_PP%K0R01Cv7'CQ09PWPkQ09PgPOPU%6oRk17oVRvPoP\P]PqPuP_P`P]PtPsPgPFP]D:E5E5GED@D@P3fLRsP1P5PjC]PsPZPP%K6Rt1Ci7'CPsPWPnPsP[POPU%61Rn171VRiP1P\P]PmPRPZP`P]PhPzP[PFP]D:E5E5GED@PdQ09Q08PefMRzPsE=fNS0:/>z10]zfORh,<J[[[P9Q0:PxP5P{C]PhPoPP1C07,WgPhPWPwPhP_POPU%6rRw17rVR0PrP\P]PkPvPoP`P]PqPuP_PFP]D:E5E5GED@P3fPR_P1PP1Ct7,W[C]P_PWPjP_PZPOPU%6|Rj17|VRtP|P\P]PnPiP1P`P]PmPRPZPFP]D:E5E5GEPdPhQ0:PefQRhP_E=fRS0;/>h10]hfSRZ,<J[[[P9Q0;PxPP1Wf7,WpC]PZPW19o7PZPoPOPU%6sRR17sVRmPsP\P]PwP0PrP`P]PkPvPoPFP]D:E5E5GEP3fTRoPW%~1P7H0CPoP1POPU%6zRv17zVRkPzP\P]PjPtP|P`P]PnPiP1PFP]D:E5E5D@PdPZQ0;PefURZPoE=fVS0</>Z10]ZfWR1,<J[[[P9Q0<PW%~xP7H0CP1PrPOPU%6_Ri17_VRnP_P\P]PRPmPsP`P]PwP0PrPFP]D:E5E5D@P3fXR0P|POPUC]%6hRw17hVRuPhP\P]PvPkPzP`P]PjPtP|PFP]D:E5E5PdP1Q0<PefYR|P0E=fZS0=/>|10]|f[Rt,<J[[[P9Q0=Q09POPUC]%6oRj17oVRqPoP\P]PiPnP_P`P]PRPmPsPFP]D:E5E5P3%6ZRs17ZVRmA2Z\]PwPuPhP`P]PvPkPzPFP]D:E53iPdPtQ0=Pef]Rkf\RvE=f^S0>/>k10]kf_RR,<J[[[P9%61170VR1A20\]PjPqPoP`P]PiPnP_PFP]D:E53iP317|VR_P|P\P]PsPmPZP`P]PwPuPhPFP]D:E5CBPdPRQ0>PefaRhf`S0?E=fbS0@/>h10]hfcRu,<J[[[P917tVPvP\P]%60RtP1P0P`P]PjPqPoPFP]D:E5CBP3A2k\]%6|RoP_P|P`P]PsPmPZPFP]D:E5PdPuQ0@PefeRZfdRmE=ffS0A/>Z10]ZfgRs,<J[[[P9A2R\]%6vRq17vVRjPvP`P]PtP1P0PFP]D:E5P3%6kR117kVRtA2k`]PoP_P|PFP]D:3iPdPsQ0APefiS0BfhR|E=fjS0CQ0B'>Q0B,0]fkR_,<J[[[P9%6RQ0?/7VRRQ0??2`]PqPjPvPFP]D:3iP317hVRvPhP`P]P1PtPkPFP]D:CBPdP_Q0CPefmS0DflS0EE=fnS0FQ0D'>Q0D,0]foRt,<J[[[P917uVPmP`P]Q0?Q0?/3F>0;R]+0?CBP3A2Z`]13hF>0;v]-0?hPdPtQ0FPefqRtfpE=frS0G/>t10]tfsRv,<J[[[P9A2s`]PmPmPVA2mF]COP3%6ZA2ZF]9}ZVPdPvQ0GPefuS0HftE=fvRvQ0H'>Q0H,0]fwRZ,<J[[[P9%6sA2|F]9}|VP3Q0B/7VQ0B?2F]PdPZPvPefyRZfxS0IE=fzR|/>Z10]Zf{Rs,<J[[[P917_VQ0E?2F]PdP|PZPef|R_PsE=f}Rm/>_10]_&0bJ%?NS0J#?#mR_#?#^#^RR#8#^#^#M#l#s#s#TS0K/0]S0L%?R#^#^#M#l#s#s#T,0]S0M'1S0N%8G#l#TRG&0aJRR13]G,RR60`]5}]S0O'1P3Q0NQ0Op+01ARR,<JP9Q0NP3Q0LQ0MQ0Op+01ERG,<J[P9Q0LQ0MQ0OP;p+01MS0PPKQ0PPLPMQ0PPQPTQ0PPWPXQ0PPYPUPcCgFJEyX5I,;IX6I,;IXJ;#LXL;#LXO;p+01BP;p+01LRcp+01FRL/97PcPLP5PMPcPQPTPcPWPXPcPYPU1kLVS0QPLP\P]PbCB60_LCgFJFFX5I,;IX6I,;IXJ;#LXL;PmP;p+01KS0R19G7Q0RPGP519R7Q0RPRPPPTQ0RPWPXQ0RPYPUPGPGPVPGP\P]PRPRPVPRP`P]PaCBCOCBCOFJD@FFX5I,;IX6I,;IXJ;PZPIp+01JS0Sp+01DS0T/97Q0SQ0TP5p+01@RZ/97Q0SPZPPPTQ0SPW19s7Q0SPsPOPUQ0TQ0TPVQ0TP\P]PZPZPVPZP`P]PsPsPVA2sF]COCBCOCBCOGED@FFX5I,;IX6IQ0HPIp+01IRsp+01CRZ/97S0U'uS0V13Z5RTf~Ra/97S0W5qsS0XPs13aPRR%KvS0Y/CS19|7S0Z9qsWS0[13|ORS=qsUS0\%6ZS0]17ZVS0^A2Z\]S0_%6aS0`17aVS0aA2a`]S0b%6|S0c17|VS0dA2|F]S0e'1S0f'1S0g'1S0h'1S0i'1S0j'1S0k'1S0l'1S0m'1S0n'1S0oCg3iX5IPt%48S0pA2<8]S0qg016Vp,2LF+0]Rt00\4%ItR|%I4Ra'RRZPtP|%D|Pa%DaI0[p,3LFnH0ZS0rPZ&0:4S0s%4aS0t&0:tS0u%4|S0vp,2sp-0YHRHQ04#QR|'HS0w%4H%4|1NH|[[S0xp,5pconsRH/HVS0y%4H%4VRt1NHV[[S0zp+01GS0{/HVQ0{#41NsV\t[%QERH%Q_R_+08Ra%6HR4%4_207H_Rv#6[RG[RY%4HRXg00e4RmB06H_8UWMR_%4v\m^MXRb208HFRc%4F207HFRQ#6[RM\4RKB06HF8VmXMXRJ%4Q\m^MXRXp+01PS0|/HVQ0|#4p+01R/NV\t[1HsV%4sQ0R/NV\t[p,4thisRu/HVR1%4u1NuV\t[Rup,2poRj/HVRq%4j1NjV\t[Rjp,4TIDRRop,3tidRw#4Rn1RwQRw'1RQP3PnPwp+01[92^yp+01ZS0}/0^'{/1mP9p,3ICNR^p,6icountRi#4R{1RivRi'1RvP3P{Pip+01`92rxp+01_/0r'{/1mP9Ppg00eP20X:H'zP4eR4O1RHPMPyP4O1R4PGp-0S0~g00f6Rpg00h?Rr#V#VRx#pS10,x;1x;x1x;r605;605;g00h^+0W%|pRr3X&0VpRp%\A&0U;S117U?Q117UB%\BQ117UB%\>7UB7U<%\=7U8&0S;Rx&0R;R}P}Q03-04;R~%ZERE'PS12%Z2S13'f&0QCR2P}P}Q13%ZNS14'fP2P}P}203;:RNQ05#8#Z'oP2P}P}Q04#Z,oNP2P}P}Q0J#8#Z,oNP2P}Q02PCPCPDP}Q02PCPCPDQ12Q145Y}P}Q02PCPCPDP6J0PK0NP}Q02PCPCPDI0MK0LDSDSDSDSDS20J}DRDP9P<g00fbRCg00gBR6'z20I9<=aC6dB0H;:8H0GR6b<bFbGX4;XK;XR;XS;XT;XU;XV;WQQ0~A298=10?=Q06Q06Q06A2>AB/{g/1m[[[[[^4;^K;^R;^S;^T;^U;^V;]QP9p+01eQ0:'0p+01Yp+01]p+01aP]p+01fPzQ0:Q09P0Q0?Q0EQ0IO=b;b2b1XciXb{P8P9O2n2001000000121000000bWX9wX0nP8P9O2n2001000000121000000bWb=b>b?b@bAb1bBb2bCbDbEbIbHb:PdQ0RQ0SPeH00@0F=<R=eW8W7XP;X3;Q0pQ0qP=[[^P;^3;Q0VQ0XQ0YQ0G/W7'CS0Y9qsRS0GQ0o'1S0V'1P@Pdp+01HRdQ0{PeH00S0{Q0SPsQ00Q0UQ0FPgPfP9Q00Q0U#b#IReQ0rPZQ0sQ0tQ0uQ0vQ0wQ0xQ0yQ0zQ0T/HVR7Q0T#4Q0Q#4\t[R=PaPYP_PbPcPKPJPXQ0P/HVRzQ0P#4p+01OS0P/NV\t[Rm1HLVRB%4L1NdV\t[RtP1PuPqPjPoPQP3PnPwQ03#?#v#m#M#m#v#_#_#M#_#M#TRd#4RLP9P^PvP3P{PiPLP9PHPMP4PGPrPpQ11Px%GdS0Q9Y}NPDP6b<bFbGPLP9b;b2b1X9iX8{P8P9O2n2001000000121000000b3X7wX0nP8P9O2n2001000000121000000b3b=b>b?b@bAb1bBb2bCbDbEbIbHb:PLeQ00,0:eQ10#p#VS10#IR:,3dRL/0]13dVS0T/0]RAP9XN;R>1089$0EXY;XN;S0UPLQ0TP>P>P>P;P;g02KX1389H0K#DXX;XP;RLPdPd%DdP:PVP>P>Q01%I9#DWNS01Q10PV%DVJ02S0FM:jP]P]%D]R?GdQ0rPZQ0sQ0tQ0uQ0vQ0wQ0xQ0yQ0zP7P=PaPYP_PbPcPKPJPXPzPmPBPtP1PuPqPjPoPQP3PnPwPAP9P^PvP3P{PiPAP9PHPMP4PGPrPp%\8RAPxP}Q0K#G=Y}~S0pP2P}Q0Q%GVRC;h~D`PDP6b<bFbGX4;Q0K/09S0KQ0T/08[^4;P9P]Q0:O2S0Tb;b2b1X9iX8{P8P9O2n2001000000121000000b3X7wX0nP8P9O2n2001000000121000000b3b=b>b?b@bAb1bBb2bCbDbEbIbHb:CcA2de]eQ00?2e]eO4M:eQ0XQ0VP@Q0{Q0SPsPTQ0WQ0CPgPfP9PTQ0W#b#IS0WQ0rPZQ0sQ0tQ0uQ0vQ0wQ0xQ0yQ0zP7P=PaPYP_PbPcPKPJPXPzPmPBPtP1PuPqPjPoPQP3PnPwp+01S/35S0C#4P9P^PvP3P{Pip+01X/35Re#4P9PHPMP4PGPrPpPAPxP}1oN~-0D}S0VP2P}%G5,P~S0X,fND`PDP6b<bFbGX4;%69Rd1385R5#4[^4;P9p+01^S00Q0HO2b;b2b1X9iX8{P8P9O2n2001000000121000000b3X7wX0nP8P9O2n2001000000121000000b3b=b>b?b@bAb1bBb2bCbDbEbIbHb:%4Te13T:S0H/0]13TVS0Q/0]P>Q0UQ0HQ0QP>P>P>PLPTPT%DTP:PVQ0FM:jP]P]P?GdQ0rPZQ0sQ0tQ0uQ0vQ0wQ0xQ0yQ0zP7P=PaPYP_PbPcPKPJPXPzPmPBPtP1PuPqPjPoPQP3PnPwQ0C?2V]P9P^PvP3P{PiA2eV]P9PHPMP4PGPrPp%\<Q117U8S0CPxP}P}%G\=h~EP2Q0X/PC=Y}EDSPDP6b<bFbGX4;XK;A29\8A25V<[^4;^K;P9P]Q00Q0DO3b;b2b1X9iX8{P8P9O2n2001000000121000000b3X7wX0nP8P9O2n2001000000121000000b3b=b>b?b@bAb1bBb2bCbDbEbIbHb:CcQ0W=2T]eO4M:eQ0GQ0oP@Q0{Q0SPsPRQ0YQ0APgPfP9PRQ0Y#b#IRTQ0rPZQ0sQ0tQ0uQ0vQ0wQ0xQ0yQ0zP7P=PaPYP_PbPcPKPJPXPzPmPBPtP1PuPqPjPoPQP3PnPwQ0P/3PR5#4P9P^PvP3P{Pip+01T/3PR\#4P9PHPMP4PGPrPpPAPxP}Q0VP2P}%GP,P~Re,fND`PDP6b<bFbGX4;138PRP#4\d^4;P9Q0}Q0BO2b;b2b1X9iX8{P8P9O2n2001000000121000000b3X7wX0nP8P9O2n2001000000121000000b3b=b>b?b@bAb1bBb2bCbDbEbIbHb:%4ReQ10#V#V#V#VS10#IS0B,3RS0P/0]13R|S0Y/0]P>Q0UQ0PQ0YP>P>P>PLPRPR%DRQ0BP|P>P>Q01Q10P|%D|J02M:jP]P]P?GdQ0rPZQ0sQ0tQ0uQ0vQ0wQ0xQ0yQ0zP7P=PaPYP_PbPcPKPJPXPzPmPBPtP1PuPqPjPoPQP3PnPwA25|]P9P^PvP3P{PiA2\|]P9PHPMP4PGPrPpQ0CPxP}P}%G`=h~EP2%G|,Pe=Y}EDSPDP6b<bFbGX4;XK;A29`8A2P|<[^4;^K;P9P]Q0}PhO3b;b2b1X9iX8{P8P9O2n2001000000121000000b3X7wX0nP8P9O2n2001000000121000000b3b=b>b?b@bAb1bBb2bCbDbEbIbHb:CcA2RT]eO4M:eQ0[Q0nP@Q0{Q0SPsPWQ0ZQ0@PgPfP9PWQ0Z#b#IRTQ0rPZQ0sQ0tQ0uQ0vQ0wQ0xQ0yQ0zP7P=PaPYP_PbPcPKPJPXPzPmPBPtP1PuPqPjPoPQP3PnPwQ03#?#v#_#M#_#m#l#_#m#M#TRR/3VRh#4RPP9P^PvP3P{PiPPP9PHPMP4PGPrPpQ11Px%GR/PCRR9Y}NPDP6b<bFbGPPP9b;b2b1X9iX8{P8P9O2n2001000000121000000b3X7wX0nP8P9O2n2001000000121000000b3b=b>b?b@bAb1bBb2bCbDbEbIbHb:PPe%4We13h:RP/0]13hVR|/0]R`P>Q0UPPP|P>P>P>PLPhPh%DhP:PVQ0FM:jP]P]P?GdQ0rPZQ0sQ0tQ0uQ0vQ0wQ0xQ0yQ0zP7P=PaPYP_PbPcPKPJPXPzPmPBPtP1PuPqPjPoPQP3PnPwP`P9P^PvP3P{PiP`P9PHPMP4PGPrPpPAPxP}Q0pP2P}AhRC~D`PDP6b<bFbGX4;Q0K10|8[^4;Q0Tb;b2b1X9iX8{P8P9O2n2001000000121000000b3X7wX0nP8P9O2n2001000000121000000b3b=b>b?b@bAb1bBb2bCbDbEbIbHb:CcA2hT]eA2WT]eO4M:eQ0\Q0mP@Q0{Q0SPsPSPUQ0>PgPfP9PS%bU#IRUQ0rPZQ0sQ0tQ0uQ0vQ0wQ0xQ0yQ0zP7P=PaPYP_PbPcPKPJPXPzPmPBPtP1PuPqPjPoPQP3PnPwQ0R/3ORf#4P9P^PvP3P{PiQ0|/3ORg#4P9PHPMP4PGPrPpPAPxP}Q0VP2P}%GO,P~RA,fND`PDP6b<bFbGX4;138ORO#4\d^4;P9p+01VRdPkO2b;b2b1X9iX8{P8P9O2n2001000000121000000b3X7wX0nP8P9O2n2001000000121000000b3b=b>b?b@bAb1bBb2bCbDbEbIbHb:%4Se13S:Rk/0]13SVRN/0]P>Q0UPkPNP>P>P>PLPSPS%DSP:PVQ0FM:jP]P]P?GdQ0rPZQ0sQ0tQ0uQ0vQ0wQ0xQ0yQ0zP7P=PaPYP_PbPcPKPJPXPzPmPBPtP1PuPqPjPoPQP3PnPwA2fV]P9P^PvP3P{PiA2gV]P9PHPMP4PGPrPpQ0CPxP}P}%GF=h~EP21PAC=Y}EDSPDP6b<bFbGX4;XK;A29F8A2OV<[^4;^K;P9P]PdP0O3b;b2b1X9iX8{P8P9O2n2001000000121000000b3X7wX0nP8P9O2n2001000000121000000b3b=b>b?b@bAb1bBb2bCbDbEbIbHb:CcA2SU]eO4M:eQ0]Q0lQ0=Q0^Q0kQ0<Q0_Q0jQ0;Q0`Q0iQ0:Q0aQ0hQ08Q0bQ0gQ07Q0cQ0fPyQ0dQ0ePlP[CwF[F[F[F[F[F[baCnCnCnCnCnWpW[WZP8P9O2n2001000000121000000W0P8P9O2n2001000000121000000b0WdWoWeWnWmP8P9O2n2001000000121000000W0WlP8P9O2n2001000000121000000W0WkP8P9O2n2001000000121000000W0WjP8P9O2n2001000000121000000W0WiP8P9O2n2001000000121000000W0WhP8P9O2n2001000000121000000W0WgP8P9O2n2001000000121000000W0WfP8P9O2n2001000000121000000W0W`P8P9O2n2001000000121000000W0W_P8P9O2n2001000000121000000W0W^P8P9O2n2001000000121000000W0W]P8P9O2n2001000000121000000W0W\P8P9O2n2001000000121000000W0X5IP8P9O2n2011000000121100000W0X6IP8P9O2n2011000000121100000W0XJ;P8P9O2n2011000000121100000W0XL;P8P9O2n2011000000121100000W0XO;P8P9O2n2011000000121100000W0XY;XN;WqWXo"). Qed.

  Definition TW (ff fp : Z) : list (Z * Z) :=
    [(spz - 16384, spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 1024); (sh ff, sh ff + 128);
     (po + 2, po + 4); (po + 8, po + 20)].

  Lemma tw_munch : forall ff fp m1 m', munch (W1 ff fp) m0 m1 -> munch (LbB_SnK.PWF sp po ff fp) m1 m' ->
    munch (TW ff fp) m0 m'.
  Proof using H sp m0 po.
    clear HHbp Ha0 Ha1 Ha2 TIDR DSA DSW DSO DS8 DSV DSin PCA PCO PC8 PCC PCfs DISJ ICN THA THO TH8 THfs THC1 THC2 UM0 USH UBL STK CEIL LO SP16 SPHI SPOBJ MI0 AC0 LV0 TP RFS0 LFn THR.
    intros ff fp m1 m' M1 M2 x Hx. unfold TW in Hx. cbn [outside] in Hx.
    transitivity (m1 x).
    - apply M2. unfold LbB_SnK.PWF. cbn [outside]. lia.
    - apply M1. unfold W1. cbn [outside]. lia.
  Qed.

  Lemma tw_place : forall ff fp, fresh_frame H LF 4 ff fp ->
    as_FSB H + AFS_HDR <= ff /\ ff + 1024 <= as_FSB H + AFS_SIZE /\ ff mod 64 = 0
    /\ as_FSB H + AFS_FLAGS <= fp < as_FSB H + AFS_HDR
    /\ AIMG_TOP <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ as_FSB H mod 4096 = 0
    /\ (as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H) /\ aapp (as_FSB H) AFS_SIZE
    /\ sh (as_FSB H) <= sh ff /\ sh ff + 128 <= sh (as_FSB H + AFS_SIZE) /\ 0x800d5000 <= sh ff
    /\ sh ff + 128 <= sh aceil.
  Proof using HCEIL H LF.
    clear HHbp Ha0 Ha1 Ha2 TIDR DSA DSW DSO DS8 DSV DSin PCA PCO PC8 PCC PCfs DISJ ICN THA THO TH8 THfs THC1 THC2 UM0 USH UBL STK CEIL LO SP16 SPHI SPOBJ MI0 AC0 LV0 TP RFS0 LFn THR.
    intros ff fp (FFR & FSB_OK & _).
    pose proof FFR as (K1 & K2 & K3 & (K4 & K5) & K6). unfold fsz in K3. change (64 * 2 ^ 4) with 1024 in K3.
    pose proof FSB_OK as (B1 & B2 & B3 & B4).
    assert (B4' : as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H).
    { clear - B4. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in *. destruct B4; [left | right]; lia. }
    assert (SH : sh (as_FSB H) <= sh ff /\ sh ff + 128 <= sh (as_FSB H + AFS_SIZE) /\ 2148356096 <= sh ff
                 /\ sh ff + 128 <= sh aceil).
    { clear - K2 K3 B1 B2. unfold sh, ASHADOW_BASE, AFS_HDR, AFS_SIZE, AIMG_TOP in *. Z.div_mod_to_equations. lia. }
    destruct SH as (S1 & S2 & S3 & S4).
    repeat match goal with |- _ /\ _ => split end; try assumption; lia.
  Qed.

  Lemma tw_laws : forall LB0 ff fp, fresh_frame H LF 4 ff fp ->
    Forall (aclient_write_ok H LB0) (TW ff fp) /\ Forall stack0_ok (TW ff fp) /\ Forall aconst_ok (TW ff fp).
  Proof using HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR DSO DSin ICN CEIL LO RFS0 LFn.
    clear Ha0 Ha1 Ha2 DSA DSW DS8 DSV PCA PCO PC8 PCC PCfs DISJ THA THO TH8 THfs THC1 THC2 UM0 USH UBL STK SP16 SPHI SPOBJ MI0 AC0 LV0 TP THR.
    intros LB0 ff fp FR.
    pose proof (tw_place ff fp FR) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13).
    pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    destruct (ah_RFS_range H HHb _ _ RFS0) as [_ FR0].
    assert (POF : as_FSB H + AFS_HDR <= po /\ po + 20 <= as_FSB H + AFS_SIZE).
    { pose proof DSin as (f & Hf & F1 & F2). pose proof (FR0 f Hf) as (L1 & L2 & L3 & _). clear - F1 F2 L2 L3. lia. }
    assert (SA : ALOWSH_LO <= sh aceil) by (clear - A1; unfold sh, ASHADOW_BASE, ALOWSH_LO in *; Z.div_mod_to_equations; lia).
    unfold TW. split; [|split].
    - repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd].
      + left. clear - CEIL LO. unfold ADS_STACK in *. lia.
      + right; right; right; right; left. clear. unfold AFS_FLAGS, AFS_SIZE. lia.
      + right; right; right; right; left. clear - P4. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. lia.
      + right; right; right; right; left. clear - P1 P2. unfold AFS_HDR in *. lia.
      + right; right; right; right; right; left. clear - P10 P11. lia.
      + right; right; right; right; left. clear - POF. unfold AFS_HDR in *. lia.
      + right; right; right; right; left. clear - POF. unfold AFS_HDR in *. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold stack0_ok; cbn [fst snd].
      + left. clear - CEIL LO A1. unfold ADS_STACK, AHI_LO in *. lia.
      + clear - P8 SA. unfold AFS_FLAGS, AFS_SIZE in *. destruct P8; [right | left]; lia.
      + clear - P8 P4 SA. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. destruct P8; [right | left]; lia.
      + clear - P8 P1 P2 SA. unfold AFS_HDR in *. destruct P8; [right | left]; lia.
      + right. exact P13.
      + clear - P8 POF SA. unfold AFS_HDR, AFS_SIZE in *. destruct P8; [right | left]; lia.
      + clear - P8 POF SA. unfold AFS_HDR, AFS_SIZE in *. destruct P8; [right | left]; lia.
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply LbB_DPdK.aconst_ok_hi. clear - CEIL LO A1. unfold ADS_STACK in *. lia.
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact P9 | clear; lia | clear; unfold AFS_FLAGS, AFS_SIZE; lia].
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact P9 | clear - P4; unfold AFS_FLAGS in *; lia | clear - P4; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *; lia].
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact P9 | clear - P1; unfold AFS_HDR in *; lia | exact P2].
      + apply LbB_DPdK.aconst_ok_hi. clear - P12. lia.
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact P9 | clear - POF; unfold AFS_HDR in *; lia | clear - POF; lia].
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact P9 | clear - POF; unfold AFS_HDR in *; lia | clear - POF; lia].
  Qed.

  Lemma tw_out_img : forall ff fp a, fresh_frame H LF 4 ff fp -> aimg_client a -> outside (TW ff fp) a.
  Proof using HCEIL H sp this po tid pcons icount lo LF TIDR DSO ICN CEIL LO LFn.
    clear HHbp Ha0 Ha1 Ha2 DSA DSW DS8 DSV DSin PCA PCO PC8 PCC PCfs DISJ THA THO TH8 THfs THC1 THC2 UM0 USH UBL STK SP16 SPHI SPOBJ MI0 AC0 LV0 TP RFS0 THR.
    intros ff fp a FR Ha.
    pose proof (tw_place ff fp FR) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13).
    pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    pose proof DSO as (O1 & O2 & O3).
    assert (AT : a < AIMG_TOP) by (clear - Ha; unfold aimg_client, AIMG_TOP in *; lia).
    apply LbB_DPdK.outside_of. unfold TW.
    clear - AT P1 P4 P5 P12 O1 A1 CEIL LO.
    unfold ADS_STACK, AFS_HDR, AFS_FLAGS, AIMG_TOP in *.
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
  Qed.

  Lemma tw_keep : forall ff fp m', fresh_frame H LF 4 ff fp -> munch (TW ff fp) m0 m' -> wmono asegs m0 m' ->
    stk asegs m' lo spz /\ LINV_P5 m' /\ ACONST m' /\ wr_at asegs m' po 20.
  Proof using HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR DSW DSO DSin ICN STK CEIL LO AC0 LV0 RFS0 LFn.
    clear Ha0 Ha1 Ha2 DSA DS8 DSV PCA PCO PC8 PCC PCfs DISJ THA THO TH8 THfs THC1 THC2 UM0 USH UBL SP16 SPHI SPOBJ MI0 TP THR.
    intros ff fp m' FR MU WM.
    pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof (tw_laws [] ff fp FR) as (_ & _ & LAC).
    split.
    { eapply stk_transport; [exact STK | exact MU | exact WM |]. intros x Hx. right.
      pose proof STK as (S1 & S2 & S3). destruct (S3 x Hx) as [HV _].
      pose proof (WM (wa x) HV) as HV'.
      assert (HX : AIMG_TOP <= bv_unsigned (wa x)) by (unfold wa; rewrite unsigned_lit by lia; unfold AIMG_TOP; lia).
      rewrite (BakeStackRep.wview_high m' (wa x) HX) in HV'.
      destruct (m' (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction]. }
    split.
    { eapply LINV_P5_cl; [exact LV0|]. intros a Ha Hc. unfold wa. apply MU. rewrite unsigned_lit by lia.
      exact (tw_out_img ff fp a FR Hc). }
    split; [eapply ACONST_frame; [exact AC0 | exact MU | exact WM | exact LAC]|].
    eapply wr_at_transport; [exact DSW | exact WM].
  Qed.

  Lemma tw_xpres : forall s LB0 m' ff fp, as_RHEAP H s LB0 m0 -> munch (TW ff fp) m0 m' -> wmono asegs m0 m' ->
    xpres H LB0 spz (sn_XT po ++ [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 4); (sh ff, sh ff + fshn 4)])
          m0 m'.
  Proof using HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR ICN CEIL LO LFn.
    clear Ha0 Ha1 Ha2 DSA DSW DSO DS8 DSV DSin PCA PCO PC8 PCC PCfs DISJ THA THO TH8 THfs THC1 THC2 UM0 USH UBL STK SP16 SPHI SPOBJ MI0 AC0 LV0 TP RFS0 THR.
    intros s LB0 m' ff fp RH MU WM.
    apply (xpres_of_munch H s LB0 spz _ (TW ff fp) m0 m0 m' HHb RH MU WM).
    unfold TW, sn_XT, sn_X. change (fsz 4) with 1024. change (fshn 4) with 128.
    apply Forall_cons; [left; cbn [fst snd]; clear - CEIL LO; unfold ADS_STACK in *; lia|].
    repeat (apply Forall_cons; [right; intros x Hx; cbn [fst snd app rin_ivs] in *; lia|]).
    apply Forall_nil.
  Qed.

  Definition TW0 (ff fp : Z) : list (Z * Z) :=
    [(spz - 16384, spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 1024); (sh ff, sh ff + 128)].

  Lemma tw0_munch : forall ff fp m1 m', munch (W1 ff fp) m0 m1 -> munch (LbB_SnK.W3 sp ff) m1 m' -> munch (TW0 ff fp) m0 m'.
  Proof using H sp m0.
    clear HHbp Ha0 Ha1 Ha2 TIDR DSA DSW DSO DS8 DSV DSin PCA PCO PC8 PCC PCfs DISJ ICN THA THO TH8 THfs THC1 THC2 UM0 USH UBL STK CEIL LO SP16 SPHI SPOBJ MI0 AC0 LV0 TP RFS0 LFn THR.
    intros ff fp m1 m' M1 M2 x Hx. unfold TW0 in Hx. cbn [outside] in Hx.
    transitivity (m1 x).
    - apply M2. unfold LbB_SnK.W3. cbn [outside]. unfold sh, ASHADOW_BASE, SHBASE in *. lia.
    - apply M1. unfold W1. cbn [outside]. lia.
  Qed.
  Lemma tw0_tw : forall ff fp m m', munch (TW0 ff fp) m m' -> munch (TW ff fp) m m'.
  Proof using H sp po.
    clear HHbp Ha0 Ha1 Ha2 TIDR DSA DSW DSO DS8 DSV DSin PCA PCO PC8 PCC PCfs DISJ ICN THA THO TH8 THfs THC1 THC2 UM0 USH UBL STK CEIL LO SP16 SPHI SPOBJ MI0 AC0 LV0 TP RFS0 LFn THR.
    intros ff fp m m' MU x Hx. apply MU. unfold TW, TW0 in *. cbn [outside] in *. tauto.
  Qed.
  Lemma tw0_laws : forall LB0 ff fp, fresh_frame H LF 4 ff fp ->
    Forall (aclient_write_ok H LB0) (TW0 ff fp) /\ Forall stack0_ok (TW0 ff fp) /\ Forall aconst_ok (TW0 ff fp).
  Proof using HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR DSO DSin ICN CEIL LO RFS0 LFn.
    clear Ha0 Ha1 Ha2 DSA DSW DS8 DSV PCA PCO PC8 PCC PCfs DISJ THA THO TH8 THfs THC1 THC2 UM0 USH UBL STK SP16 SPHI SPOBJ MI0 AC0 LV0 TP THR.
    intros LB0 ff fp FR.
    pose proof (tw_place ff fp FR) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13).
    pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    assert (SA : ALOWSH_LO <= sh aceil) by (clear - A1; unfold sh, ASHADOW_BASE, ALOWSH_LO in *; Z.div_mod_to_equations; lia).
    unfold TW0. split; [|split].
    - repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd].
      + left. clear - CEIL LO. unfold ADS_STACK in *. lia.
      + right; right; right; right; left. clear. unfold AFS_FLAGS, AFS_SIZE. lia.
      + right; right; right; right; left. clear - P4. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. lia.
      + right; right; right; right; left. clear - P1 P2. unfold AFS_HDR in *. lia.
      + right; right; right; right; right; left. clear - P10 P11. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold stack0_ok; cbn [fst snd].
      + left. clear - CEIL LO A1. unfold ADS_STACK, AHI_LO in *. lia.
      + clear - P8 SA. unfold AFS_FLAGS, AFS_SIZE in *. destruct P8; [right | left]; lia.
      + clear - P8 P4 SA. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. destruct P8; [right | left]; lia.
      + clear - P8 P1 P2 SA. unfold AFS_HDR in *. destruct P8; [right | left]; lia.
      + right. exact P13.
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply LbB_DPdK.aconst_ok_hi. clear - CEIL LO A1. unfold ADS_STACK in *. lia.
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact P9 | clear; lia | clear; unfold AFS_FLAGS, AFS_SIZE; lia].
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact P9 | clear - P4; unfold AFS_FLAGS in *; lia | clear - P4; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *; lia].
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact P9 | clear - P1; unfold AFS_HDR in *; lia | exact P2].
      + apply LbB_DPdK.aconst_ok_hi. clear - P12. lia.
  Qed.

  Lemma tw0_xpres : forall s LB0 m' ff fp, as_RHEAP H s LB0 m0 -> munch (TW0 ff fp) m0 m' -> wmono asegs m0 m' ->
    xpres H LB0 spz ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)
                     :: [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 4); (sh ff, sh ff + fshn 4)]) m0 m'.
  Proof using HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR ICN CEIL LO LFn.
    clear Ha0 Ha1 Ha2 DSA DSW DSO DS8 DSV DSin PCA PCO PC8 PCC PCfs DISJ THA THO TH8 THfs THC1 THC2 UM0 USH UBL STK SP16 SPHI SPOBJ MI0 AC0 LV0 TP RFS0 THR.
    intros s LB0 m' ff fp RH MU WM.
    apply (xpres_of_munch H s LB0 spz _ (TW0 ff fp) m0 m0 m' HHb RH MU WM).
    unfold TW0. change (fsz 4) with 1024. change (fshn 4) with 128.
    apply Forall_cons; [left; cbn [fst snd]; clear - CEIL LO; unfold ADS_STACK in *; lia|].
    repeat (apply Forall_cons; [right; intros x Hx; cbn [fst snd rin_ivs] in *; lia|]).
    apply Forall_nil.
  Qed.

End P1.
