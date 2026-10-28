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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DPdK LbB_PmXp.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_TablStmt LbB_SnStmt LbB_WoGen LbB_SnXD LbB_SnXK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_SnXT () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4ftblC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep5xpresC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit5fkeysC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6of_natC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep=xclient_rangeI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic5proj1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8fkeys_InC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep>xpres_rw_cellsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4wenvC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell05K47Corelib4Init9Datatypes4list02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsI47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00I7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil8HeapCeil00I6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3asr00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockK47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4fentI46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic3and00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00K47Corelib4Init9Datatypes3nat01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_spC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD3xSPC56Stdlib6ZArith6BinInt1Z3powC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBI47Corelib4Init5Logic2or00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXK8xpre_geoC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_loC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD5x_shiC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_tpC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_LFC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeapAfresh_frame_factsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3fszC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<aframe_rangeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7afsb_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7ff_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8ff_classC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7ff_flagC47Corelib4Init5Logic3notC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD9ASX_STACKC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AFS_HDRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8AFS_SIZEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface9AFS_FLAGSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9ALOWSH_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3ATPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6fframeI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD6x_thisC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD7x_pconsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_fcC4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD3x_sC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_LBC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD3x_mC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_RHEAPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface8lb_smallC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init9Datatypes6lengthC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface6nlargeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD3x_BC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;as_rauxv_okC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02I47Corelib4Init5Logic2ex00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_raC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat7LINV_P5C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_RFSC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack06stack0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_s0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_CHC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_chainC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_TRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5pf_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt8ds_tr_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_ALC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD5x_tidC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt6ds_objK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD8x_icountC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_poC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt;obj_inframeC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap5fsobjC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt7app_objc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT9ex_rangesC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<RT_SMALL_MAXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface:RT_CNT_MAXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<RT_LARGE_MAXC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD9SX_FRAMESC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface>AFS_MAXLIVE_BPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnStmt5SN_PFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD7SX_COSTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt9ADS_STACKK46Stdlib9micromega=RingMicromega3Op201C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD3xS1C56Stdlib6ZArith6BinInt1Z3divC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXK9xS1_factsC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula06C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEI47Corelib4Init5Logic5False00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap:fs_scratchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXK8xpre_allC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD2XEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<ah_RFS_rangeC47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap7fsz_posK47Corelib4Init5Logic2ex01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow8aapp_subC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap=fsobj_windowsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3nshC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface4fshnC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow@aapp_disjoint_shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7sh_monoK46Stdlib9micromega:ZMicromega;ZArithProof03C47Corelib4Init9Datatypes3appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface=aclient_rangeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;aimg_clientC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_sizeC46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap=fsobj_scratchC46Stdlib5Lists4List;Forall_implC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap@fsobj_scratch_shC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6RtB_Td6ATDLOCC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs<ASHADOW_BASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow@ASHADOW_BASE_valC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_Stc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT2PxC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap;fresh_frameC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD6xsavedc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT:xobj_rangeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKitAaclient_range_subC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmXpAxpres_addressableC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD8SX_FLAGPC56Stdlib6ZArith4Znat5Nat2Z7inj_addC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD8SX_SAVEDC46Stdlib9micromega8ZifyInst7Inj_Z_ZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXK5xlinvC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<ah_frm_shvisC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5shvisC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7hull_loC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7hull_hiC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<wr_at_of_stkC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Peano2ltC56Stdlib6NArith6BinNat1N6of_natC56Stdlib6NArith6BinNat1N3addC56Stdlib6NArith6BinNat1N8ltb_specC56Stdlib6NArith6BinNat1N2ltC56Stdlib6NArith6BinNat1N2leC56Stdlib6NArith6BinNat1N3ltbI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z4of_NC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List8app_nth1K5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedI47Corelib7Numbers7BinNums1N00C46Stdlib6ZArith4Znat7nat_N_ZC56Stdlib6ZArith4Znat3N2Z7inj_addC56Stdlib6ZArith4Znat3N2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib6ZArith4Znat7N_nat_ZC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat3N2Z6inj_lec6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT2WxC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN3tabC47Corelib4Init5Logic6eq_indc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT7ex_keepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat6relro0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat5dstatK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit9estart_shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst=ACONST_shbaseC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2wzC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst:ACONST_uarC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry04K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat:kimg_relroI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C46Stdlib9micromega;ZifyClasses9and_morphC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState<unsigned_litC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvAkword_of_rw_cellsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt5sx32AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_awC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_s1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_s2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_s3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_s4C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_s5C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_s6C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_s7C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_s8C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_s9C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD5x_s10C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD5x_s11C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_gpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_blC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4x_bcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv:kwr_of_stkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<kwr_of_wr_atC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT6kst_exC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst;AGOT_SHBASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst<ASHBASE_CELLC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst8AGOT_UARC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9AUAR_CELLI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00C56Stdlib6ZArith4Znat5Nat2Z6inj_lec6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT7ex_valsK4ELinuxProcessSemantics5Riscv5Instr5aluop07C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DPdK6PD_SHBC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHCELLC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addK4ELinuxProcessSemantics5Riscv5Instr5aluop01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT3shTc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT3evTC56Stdlib6ZArith6BinInt1Z7div_addC56Stdlib6ZArith6BinInt1Z8add_commC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC47Corelib7Classes?RelationClasses=eq_TransitiveC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2Zrc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT7ex_winsc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT8ex_keepTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvBsh0_of_addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8kshadow0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT9shT_apartc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT9shT_startC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3le8C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells6cbytesc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT2kTc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT:this_apartc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT7shb_eq0C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT3wokC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses=iff_ReflexiveC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8srl3_valC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit6wboundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4fwclC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit3finc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT9wok_factsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN2tbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit3wclC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN2tBC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN3tloC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN3thiC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN4ttblC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN3tksc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT2tSc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT3tFwc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT3tHwC47Corelib4Init5Logic9False_indC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN7tabs_wfC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28expr_eqbK47Corelib4Init9Datatypes4bool02c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT8tab_valsK47Corelib4Init5Logic4True01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT9tabs_wf3wC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit6fin_InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DRep9wr_at_subC56Stdlib5Arith8PeanoNat3Nat3lebC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List>forallb_forallC47Corelib7Classes9Morphisms5flip2K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula0:C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationK46Stdlib9micromega5Tauto4kind02c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT6wk_stkc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT9fin_widerc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT6wk_winC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN7tabs_okc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT6shb_eqc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT9tabs_ok3wC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5winsTC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_WoGen9stk_wmonoC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXK4xwinC56Stdlib6ZArith6BinInt1Z9add_assocC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXK:xinv_munchc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXT9Px_step3wC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4rtblC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit:edenot_wclI6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnXD4xent00C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC56Stdlib6ZArith4Znat3N2Z9is_nonnegC56Stdlib6ZArith4Znat5Nat2Z8inj_succ".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation PD_SHB := LbB_DPdK.PD_SHB (only parsing).

Definition kst_ex : list kentry :=
  [ KImg 0x17e000 0x186000; KWord (SA (ELit 0) SHCELL) 8 (ELit SHBASE); KWord (SA (ELit 0) AUAR_CELL) 4 (ELit 1);
    KWr (SA (EVar 58) (-8192)) (ELit 8208); KRange (EVar 58) (2 ^ 45) (2 ^ 47);
    KWr (SA (EVar 52) 0) (ELit 1016); KRange (EVar 52) 0x6e8000 (2 ^ 47 - 1024);
    KWr (SA PD_SHB SHBASE) (ELit 128);
    KDisj (SA (EVar 52) 0) (ELit 1016) (SA (EVar 58) (-8192)) (ELit 8208);
    KDisj (SA PD_SHB SHBASE) (ELit 128) (SA (EVar 58) (-8192)) (ELit 8208);
    KDisj (SA PD_SHB SHBASE) (ELit 128) (SA (EVar 52) 0) (ELit 1024) ].

Lemma ftbl_xpres {HCEIL : HeapCeil} : forall (H : asr) LB SP X W B m m' tbl,
  ftbl W B m tbl -> xpres H LB SP X m m' ->
  (forall k w, In (k, w) (fkeys tbl) -> xclient_range H LB SP X (B + k) (Z.of_nat w)) ->
  ftbl W B m' tbl.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) [] "p'0h01fi001fh11xh25HCEILh31Ah41Ph51ei011eh61ki021kh71lh81wi031wh91Bh:1Hh;2H0h<2HCh=2HTh>2Hih?2LBh@2RWhA2SPhB1WhC1XhD2XPhE1mhF2m'hG1ni041nhH1pi051phI3tbli061yi071zp;1p;2p;4p;7p;3p;6p;5p;<p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9p1003<p4p710g003WR0p4p710p8g0045j15Tg004UR1j2;Tg0055j14Tg005Zj1?Tg0068j1OTg006[j4<Tg007Uj7MTg008Mj1ATg009Hj32Tg009_j20Tg00:<j18Tg00:\j79Tg00;\j36Tg00<=j3=Tg00<_j1NTg00=?j47Tg00=_j6LTg00>:j5KTg00?8j2HTg00?Xj1CTP0j6BTg00@<j1DTg00A=l<ETg00B>j1FTg00C8j2GTg00D0j2@Tg00E8j2ITg00F5j3JTg00FUj4>Tg00GSR0g00H1R2f1R3f0R4C7p=:g00HPR5f4R6f3R7f2R8#F/G3'@'I;J4p=3g00IMP8P3P4C>p=1g00JDR9g00KCg00L<#51;00#5g00M5#4#4#4#4#4#4#?#O#5g00MZR:g00NQ#5P6P7P8P4C<f:R;f9f8R<f7R=f6R>P7P8FM1;02R?1:34%A632f>R@f=RAf<RBf;P;10<8%83F9[^82^60g00OKp4p710R<p-0RC\4RD%53REg00OhA6834A2648P6P3O1[^17RF[A2743P7P3O1[^18A6783[RGA6678\FA=834P4n2001000000120000000W7W4W3PG^7E^4D^3<P4g00PCR<,;?RDP1P?P<PCP4P1P0P2PCP310B3P4P4PAP8%N5R5D351;n2001106000120102103n2001100000120106101X0DP6P1P?P<A2D4>P1P?P<PCP3P1P0P2PCP310@3P4P4f?REP8P5D351Bn2001106000120102103n2001100000120106101[P4P1P0P2P?P<P3P4C7=2D;P1P0P2PCP8f@R;/03P4P4fARGP7P5D351@n2001106000120102103[^5<P4P?P<1:83P4C7=2DAP1P?P<PCP4P1P0P2PCP3fERFfFRH/03P4P4fGRIP8P5D331n2001106000120102103n2001100000120106101X0DRJ=6D@A2D4;P1P?P<PCP4P1P0P2PCP3fHRKfIRL/03P4P4fJP8P5D331n2001106000120102103n2001100000120106101X0DP3O1[^1D[A2D4EP1P?P<PCP4P1P0P2PCP310K3P4P4PLP8P5D351In2001106000120102103n2001100000120106101X0DP3O1[^1DP1P?P<PCP4P1P0P2PCP310I3P4P4PKP8P5D351Hn2001106000120102103n2001100000120106101X0D=6DE[A=DJ@PAP?P<1:78P3C7R@P4ELPJP@O1PKPIPHPFfDR@PGP;fB/06RGP7P7fCRJP8P5D3R5PAP4P2P7PLPKPIPHPFf5,0J%84F9XG2PBP6P7PEP6P7P8P3DKO3g00Q;,H7%C7EBPKPIPHPFP@PG%D5#8F9eM<EA1;G5eb@W>X5<X82X60P3P4O2n2001105000121107104XH?P3P4O2n2001105000121105101X1DO4b;P=P>P6P7C<eW<WDW=WIXF:WEX90WBWCXA0W?W:X29P4O1X29P4O1W2o"). Qed.

Section XT.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable e : xent H.
  Variables (ff fp : Z).

  Variables (p1 n1 p2 n2 : Z).
  Hypothesis HP : xpre H e.
  Hypothesis FF : fresh_frame H (x_LF e) 4 ff fp.

  Hypothesis THI : obj_inframe (x_LF e) (x_this e) 288.
  Hypothesis PCI : obj_inframe (x_LF e) (x_pcons e) 48.

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.
  Notation SP := (xSP e) (only parsing).
  Notation this := (x_this e) (only parsing).
  Notation pcons := (x_pcons e) (only parsing).

  Definition Wx : list word :=
    [Z_to_bv 64 this; x_sp e; x_ra e; Z_to_bv 64 (x_po e); Z_to_bv 64 (sx32A (x_tid e)); x_aw e;
     x_s0 e; x_s1 e; x_s2 e; x_s3 e; x_s4 e; x_s5 e; x_s6 e; x_s7 e; x_s8 e; x_s9 e; x_s10 e; x_s11 e; x_gp e; x_tp e;
     Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 pcons; Z_to_bv 64 (x_icount e); Z_to_bv 64 (x_bl e); Z_to_bv 64 (x_bc e);
     Z_to_bv 64 (xS1 e); Z_to_bv 64 p1; Z_to_bv 64 n1; Z_to_bv 64 p2; Z_to_bv 64 n2].

  Definition Px (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (m : mem) : Prop := xinv H e ff fp XSc sk LBk m.

  Lemma ex_ranges :
    0 <= SP < 2 ^ 64 /\ aceil + ASX_STACK <= SP /\ SP <= AAPP_HI
    /\ as_FSB H + AFS_HDR <= ff /\ ff + 1024 <= as_FSB H + AFS_SIZE /\ ff mod 64 = 0
    /\ as_FSB H + AFS_FLAGS <= fp < as_FSB H + AFS_HDR
    /\ AIMG_TOP <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ as_FSB H mod 4096 = 0
    /\ (as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H)
    /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000.
Proof.
    pose proof (bv_unsigned_in_range 64 (x_sp e)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof (xpre_geo H e HP) as (CE & LO & SPS & SHI & SP16 & TP).
    pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    pose proof FF as ((K1 & K2 & K3 & (K4 & K5) & K6) & (B1 & B2 & B3 & B4) & _).
    unfold fsz in K3. change (64 * 2 ^ 4) with 1024 in K3. unfold xSP in *.
    split; [lia|]. split; [unfold ASX_STACK, ASN_STACK, ADS_STACK in *; lia|]. split; [lia|].
    split; [lia|]. split; [lia|]. split; [exact K4|]. split; [lia|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
    split; [|lia]. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in *. destruct B4; [left | right]; lia.
  Qed.

  Lemma ex_vals : 0 <= ff < 2 ^ 64 /\ 0 <= fp < 2 ^ 64 /\ 0 < this /\ this + 288 <= 2 ^ 47 /\ this mod 8 = 0
    /\ 0 < pcons /\ pcons + 48 <= 2 ^ 47.
Proof using HP FF.
    pose proof ex_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & (_ & T8 & _ & T0 & T47 & _) & _ & _ & _ & (_ & _ & _ & P0 & P47 & _) & _).
    unfold AIMG_TOP, AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
    split; [lia|]. split; [lia|]. split; [exact T0|]. split; [exact T47|]. split; [exact T8|]. split; [exact P0 | exact P47].
  Qed.
  Lemma ex_wins : ff + 1024 <= xS1 e - 8192 /\ ff / 8 + SHBASE + 128 <= xS1 e - 8192
    /\ (ff + 1024 <= ff / 8 + SHBASE \/ ff / 8 + SHBASE + 128 <= ff) /\ 0 <= ff / 8 /\ x_lo e <= xS1 e - 8192
    /\ xS1 e + 16 <= SP - 80 /\ 2 ^ 45 <= xS1 e /\ xS1 e + 16 <= 2 ^ 47.
Proof using HP FF.
    pose proof ex_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof (xS1_facts H e HP) as (S0 & (S1 & S2) & S3 & S4 & S5 & S6).
    assert (E8 : ff = 8 * (ff / 8)) by (clear - R6; Z.div_mod_to_equations; lia).
    unfold SHBASE, AIMG_TOP, AFS_HDR, AFS_FLAGS, AFS_SIZE, ALOWSH_LO, AHI_LO in *.
    set (q := ff / 8) in *. clearbody q.
    split; [lia|]. split; [lia|]. split; [destruct R11; [left | right]; lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
  Qed.

  Lemma xobj_range : forall XSc O n, obj_inframe (x_LF e) O n -> 0 <= n -> O mod 8 = 0 ->
    Forall (fs_scratch H (x_LF e)) XSc ->
    xclient_range H (x_LB e) SP ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XE H ff fp ++ XSc) O n
    /\ xclient_range H (x_LB e) SP ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XE H ff fp ++ XSc) (sh O) (nsh n).
Proof using HHbp HP FF.
    intros XSc O n (f & IN & O1 & O2) Hn O8 FS.
    pose proof (rt_bp_base H HHbp) as HH0.
    pose proof ex_ranges as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R12).
    destruct (xpre_all H e HP) as (_ & _ & _ & _ & (RF & _) & _).
    destruct (ah_RFS_range H HH0 _ _ RF) as [(A1 & A2 & A3 & A4) AR].
    pose proof (AR f IN) as (K & Q1 & Q2 & _ & _).
    pose proof (fsz_pos (ff_class f) ltac:(lia)) as FZ.
    assert (OB1 : as_FSB H <= O) by (unfold AFS_HDR in *; lia).
    assert (OB2 : O + n <= as_FSB H + AFS_SIZE) by lia.
    assert (Htop : O + n <= AAPP_HI) by (unfold AAPP_HI; lia).
    assert (HO : 0 <= O) by (unfold AIMG_TOP in A1; lia).
    assert (FO : fsobj H (x_LF e) O n) by (right; exists f; auto).
    assert (AO : aapp O n) by (eapply aapp_sub; [exact A4 | exact OB1 | exact OB2]).
    assert (FSA : Forall (fs_scratch H (x_LF e)) (XE H ff fp ++ XSc))
      by (apply Forall_app; split; [exact (fs_scratch_of_fresh H (x_LF e) 4 ff fp FF) | exact FS]).
    unfold xclient_range, aclient_range. split; split.
    - right; right; right; right; left. lia.
    - apply Forall_cons; [cbn [fst snd]; right; unfold RtB_Td.ATDLOC; unfold AIMG_TOP in A1; lia|].
      eapply Forall_impl; [| exact FSA]. intros iv FSi.
      exact (fsobj_scratch H HH0 (x_LF e) O n (x_m e) iv RF FO HO Hn Htop AO FSi).
    - right; right; right; right; right; left. split.
      + apply sh_mono; lia.
      + unfold sh, nsh. clear - O8 OB2 A3 Hn. unfold AFS_SIZE in *. Z.div_mod_to_equations. lia.
    - apply Forall_cons.
      + cbn [fst snd]. right. assert (0 <= O / 8) by (apply Z.div_pos; lia).
        unfold sh, ASHADOW_BASE, RtB_Td.ATDLOC. lia.
      + eapply Forall_impl; [| exact FSA]. intros iv FSi.
        exact (fsobj_scratch_sh H HH0 (x_LF e) O n (x_m e) iv RF FO HO Hn Htop FSi).
  Qed.

  Lemma ex_keepT : forall XSc sk LBk m, Px XSc sk LBk m ->
    addressable m this 288
    /\ rw_cells asegs m (this + 8) [C8 (Z_to_bv 64 pcons)] /\ rw_cells asegs m (this + 80) [C8 (Z_to_bv 64 (x_icount e))]
    /\ addressable m pcons 48 /\ rw_cells asegs m (pcons + 32) [C8 (Z_to_bv 64 0)].
Proof using HHbp HP FF THI PCI.
    intros XSc sk LBk m HI.
    destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XP & FS & _).
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & (TA & T8 & _) & C1 & C2 & _ & (PA & P8 & _) & C3 & _).
    assert (IF : forall O n j w, obj_inframe (x_LF e) O n -> 0 <= j -> 0 <= w -> j + w <= n -> obj_inframe (x_LF e) (O + j) w).
    { intros O n j w (f & IN & B1 & B2) J1 J2 J3. exists f. split; [exact IN | lia]. }
    assert (T8a : (this + 8) mod 8 = 0) by (clear - T8; Z.div_mod_to_equations; lia).
    assert (T8b : (this + 80) mod 8 = 0) by (clear - T8; Z.div_mod_to_equations; lia).
    assert (P8a : (pcons + 32) mod 8 = 0) by (clear - P8; Z.div_mod_to_equations; lia).
    pose proof (xobj_range XSc _ _ THI ltac:(lia) T8 FS) as (_ & XT).
    pose proof (xobj_range XSc _ _ (IF _ _ 8 8 THI ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) T8a FS) as (XT1 & _).
    pose proof (xobj_range XSc _ _ (IF _ _ 80 8 THI ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) T8b FS) as (XT2 & _).
    pose proof (xobj_range XSc _ _ PCI ltac:(lia) P8 FS) as (_ & XP0).
    pose proof (xobj_range XSc _ _ (IF _ _ 32 8 PCI ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) P8a FS) as (XP1 & _).
    split; [eapply LbB_PmXp.xpres_addressable; [exact XP | exact TA | exact XT]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C1 | exact XT1]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C2 | exact XT2]|].
    split; [eapply LbB_PmXp.xpres_addressable; [exact XP | exact PA | exact XP0]|].
    eapply xpres_rw_cells; [exact XP | exact C3 | exact XP1].
  Qed.

  Lemma ex_keep : forall XSc sk LBk m, Px XSc sk LBk m ->
    ACONST m /\ LINV_P5 m /\ mem_inv asegs m /\ stk asegs m (x_lo e) SP /\ wr_at asegs m ff 1016 /\ wr_at asegs m (sh ff) 128
    /\ as_RFS H ((4, ff, fp) :: x_LF e) m.
Proof using HHbp HP FF.
    intros XSc sk LBk m HI.
    destruct HI as (RF & _ & _ & AC & MI & _ & _ & _ & ST & _ & _ & WF & _ & _ & _ & LVI).
    pose proof (rt_bp_base H HHbp) as HH0.
    pose proof ex_ranges as (_ & _ & _ & _ & _ & R6 & _).
    pose proof (ah_frm_shvis H HH0 _ m (4, ff, fp) RF (or_introl eq_refl)) as SV.
    unfold ff_addr, ff_class in SV. cbn [fst snd] in SV. change (fsz 4) with 1024 in SV. unfold shvis in SV.
    assert (HL : hull_lo ff = ff) by (unfold hull_lo; rewrite R6; lia).
    assert (HU : hull_hi (ff + 1024) = ff + 1024) by (unfold hull_hi; clear - R6; Z.div_mod_to_equations; lia).
    assert (S1 : sh (ff + 1024) = sh ff + 128) by (unfold sh; clear - R6; Z.div_mod_to_equations; lia).
    rewrite HL, HU, S1 in SV. pose proof (wr_at_of_stk asegs m _ _ SV) as W.
    replace (sh ff + 128 - sh ff) with 128 in W by lia.
    split; [exact AC|]. split; [exact LVI|]. split; [exact MI|]. split; [exact ST|]. split; [exact WF|].
    split; [exact W | exact RF].
  Qed.

  Lemma evWx : forall R X (k : nat), (k < 31)%nat ->
    ev (HLib.Eseed R (Wx ++ X)) (32 + N.of_nat k) = nth k Wx (Z_to_bv 64 0).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) ["XT"] "p'0h04__p1h14__x1h24__x2h32H1h43Hk0h57__arithh64__ffh78__varmaph85__with94cstrh:2H0h;2H3h<4__p2h=1bi001bh>1nh?1xh@2z3hA2HkhB1RhC1XhD2b0hE1khF1mhG1yp&0p;1p;2p;3p;4p;<p;8p;6p;Bp;7g0055j1<Tg00V6j1@Tg005Zj1ATg0068j1kTg033Rk20ATg0045j1iTg013kj14Tg034>R0j2CTg034VR1j1;Tg0356R2j2:Tg035Sj2pTg0365R3j2GTg036QR4j2JTg036mj2WTg037JR5k30?Tg037nR6j1UTg00`@j2FTg038Lj2STg039>R7j1fTg039^j2_Tg02T1j3RTg03:5j46j3dj2ck108Tg00`fj30j1aTg00V[j1^Tg00:<R8j12Tg009_R9j2>Tg00TZR:j27Tg00lUj23Tg03:Qj4LTg03;8j1oTg00X3R;j28Tg00<_j1[Tg00loj2ZTg00mMj1nTg00mkj1mTg00nVj2YTg00o9j2lTg010jk10@Tg01:?j3jTg011Lk20=Tg011nk20<Tg012Zk30;Tg0139k409Tg01XXj29Tg03;]j2ITg03<:k207Tg03<]k306Tg02j9l<HTg03=:k201Tg00Ohj2?Tg00\9j2QTg014Jj2ETg0153j3BTg015\j2PTg01Y5j1~Tg02@@j2}Tg02@aj3|Tg00F5j3DTg016Hj1{Tg019aj4zTg02Ckj3yTg02g`j4eTg03=\j8KTg01TIj2xTg03>9k600Tg003Wj6wTg03>Vj2vTg03?Mj2`Tg03@Ak205Tg02iTl<gTg02hnlBbTg010?j4TTg0185j7tTg01:bk60:Tg019=j8rTg018Yj7qTg02E7k70>Tf0R<#4#4#4#4p=5g00H1R=g03A8R>g00GSR?P?P1P8P6f3R1g03AVf2R@f1RAP<M<gp=uP>P>P>P?P?P?P2P6P6P6P9g03B3f5R9f4R2P1P@PAP<MBbp=hP>P?P3P6P:g03BTP9P2P1P@PAP<M<Hp=sP=P?P0P8P:g03C4P9P2P1P@PAP<M<Hp=\P?PAg01=CP<CTp=XPAg01;dR:g01<CR0P0g01<cR3P<g01=jFtp=1P?PAg01IKP<CTp=VPAP:P0P0P3P<J0:p=MP1P:P0P0P3P@PAP<Grp==P>P=P?P?P7P6P8P1g03CVP@PAP<M<gp>04P=P=P=P?P?P?g03D3P8P8P8f6R7g03DSP9P2P1P@PAP<MBbp>03P>P?P4P6P;g03E:P9P2P1P@PAP<M<Hp>02P?PAg02:IP<CTp=OP@P:P0P0P3PAP<Fqp=NP@P:P0P0P3PAP<K0>p=]g00M5R:#<R;#@#AR6%<;#<R4#<#<RB#<#ARC#kRD+0A%iDREg00Q;RF#4RG#4RH#4RI#5#5#5#5#5#5#5RJ,C<%ABRK%;A':RL/pK1GLK1JKL1WLK40?%;@,:K/WKg01J2RMP5%;1,:KR5/GK1JK5PMPDPAf7R5%;9RN,:KRO#U,F6'SPD%fORP%4JRQ'_RRg03EZRS=RD7g01;FRT,FCRCC6RUn0100000020000PDP9PSPCC650DPA%;2,:KRV/GK1GOK%^BRB%29RW'>RX/7BRYPOP<X??RZPWO1R[,>BR\PKPB13?BR]PNP[PZP9PW13?WR[CuR^EhR_PKPBP]EsP<CLPY1C7J%27RY%@:#@#@#@#^R`'7RaP7PY13?YPJP`13?`RYE\P9CLRbPa%o5Rc%25,8TR5p-0Rdg01H_Re#[Rf%ieRg1Z?A%n?Rh%m?Ri1Y?TRj1l?:Rk'X,1i&0@0R0Pi1Y?BRl=j?k/Vl,1iP01Mi1C=C=20=i3R3P<P@g01JRRm,3M20<<@=0MmdB0;?TAH09Rmb6b7b8X1?W018T<1>BARn/7BP1[[^1?^0dP<f;Rof9Rp#;,:K#U,F6'SPDPpPSPCC650D%2pRpPAP1O4b5b9b4b3W:P<O11JKVPDPDPRPSPCC6PDP7PSPCC690D<X=DPDPDAdDRSAdD9SPCPCPEPD\DRV1cDR1cD9PSPSP=PV\ERV&08DRqPqPRP9PV\=/3qA0=R919XB,ITRq=0?WP=P?%a=P8%a?%2A%2<50?A0=A<207A<406XG=X?=PRPq19A<,ITXF?X>?PPPXPZPOPXPKPBP]PNPWP^EhH04PQPBP]K03R^P9PWP[M<H1JKO18BXRXPKPBP]POP\P_J02P<CLR_PXPbPaPcP5f8#2,>B/9BR\-01TRO17T\1IT\R]=0?\'?18\TA0?]T'?'QR]1>Bp/9B,ITRpP?1E?HRH1E?G1E?FRF5B?5B?g01K2RG'PR\1E?I%~:,}?=|?H=B?FRF5B?/PG1PFG=Def5De5DePgP?1Z?@PA%{?CzRFPhPi1Mi21l?;R;9j?l=y?lRl,Ok,1i5NiRG1Xlj,1i1Okj,1iRl5Ni5]iP0Pi1Xj;,1iP01Ok;,1iC=C=P3Pmb6b7b8X1?X2?X0d19nBRn90?<,?@Rj18nTA0?<TRn'?'Q18T@A0?@1[[^1?^2?^0dP<%2oRo,>B/9BRB,7TRHPoPAP@P1O5b5b@b;b9b4b3CeGK13ESGK13DCGKPUPDPSP7PCPR1CRJ17q`PRPqP^PJP`PYE\P_PXPbPaPcP5POP]PpP?ADe\fPgPFPhPi1Mi9=Nil9]iGP0Pi1Y?`RG,V;,1iP01VkG,1iC=C=P3Pmb6b7b8X1?X2?X0dX<d1?1n,Qj17@`R`P`[[^1?^2?^0d^<dP<18BTPHPoPAP@P2O6b5b@b;b9b4b3Ce1xDS,CReJ00EwW:P<O1n200210000000021100011000bDb=PMPD1W<K%U<,F6,S2PD%f</_QARDS1PCC6n0100000020000X>>%A4#k#[V='v/`LPDPAPSPCC6RC50DeARDS@-051/`L=0DCeWAXE=WCWBo"). Qed.

  Ltac evwx := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wx;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Lemma kst_ex_ok : forall R X XSc sk LBk m, Px XSc sk LBk m -> know_ok asegs (HLib.Eseed R (Wx ++ X)) m kst_ex.
Proof using HHbp HP FF.
    intros R X XSc sk LBk m HI.
    destruct (ex_keep XSc sk LBk m HI) as (AC & LV & MI & ST & FW & SW & RF).
    pose proof ex_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof ex_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
    pose proof ex_wins as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    assert (SHF : edenot (HLib.Eseed R (Wx ++ X)) (EVar 52) = Z_to_bv 64 ff) by reflexivity.
    assert (ESH : estart (HLib.Eseed R (Wx ++ X)) (SA PD_SHB SHBASE) = sh ff).
    { unfold LbB_DPdK.PD_SHB. erewrite estart_sh; [| exact SHF | lia]. unfold sh, SHBASE, ASHADOW_BASE. lia. }
    assert (SHE : sh ff = ff / 8 + SHBASE) by (unfold sh, SHBASE, ASHADOW_BASE; lia).
    pose proof (ACONST_shbase m AC) as [_ CS]. pose proof (ACONST_uar m AC) as [_ CU].
    unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *.
    unfold know_ok, kst_ex. repeat apply Forall_cons; try apply Forall_nil.
    - apply kimg_relro. exact (proj1 LV).
    - eapply (kword_of_rw_cells asegs _ m ASHBASE_CELL _ 0%nat (C8 (wz 0x7fff8000))); [exact CS | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off edenot]; rewrite unsigned_lit by lia; reflexivity
        | unfold ASHBASE_CELL; cbn; lia | unfold ASHBASE_CELL; cbn; lia | reflexivity].
    - eapply (kword_of_rw_cells asegs _ m AUAR_CELL _ 0%nat (C4 (wz 1))); [exact CU | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off edenot]; rewrite unsigned_lit by lia; reflexivity
        | unfold AUAR_CELL; cbn; lia | unfold AUAR_CELL; cbn; lia | reflexivity].
    - eapply kwr_of_stk; [exact ST | | |]; evwx; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwx. rewrite unsigned_lit by lia. lia.
    - eapply kwr_of_wr_at; [exact FW | | |]; evwx; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwx. rewrite unsigned_lit by lia. lia.
    - eapply kwr_of_wr_at; [exact SW | rewrite ESH; lia | rewrite ESH; unfold elenZ; cbn [edenot]; rewrite unsigned_lit by lia; lia
                           | unfold elenZ; cbn [edenot]; rewrite unsigned_lit by lia; lia].
    - cbn [kentry_ok]. evwx. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. rewrite ESH, SHE. evwx. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. rewrite ESH, SHE. evwx. rewrite !unsigned_lit by lia. lia.
  Qed.

  Definition shT (k : Z) : saddr := SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit k)) (ELit 3)) SHBASE.
  Definition kT (k : Z) (v : expr) : list kentry :=
    [KWord (shT k) 1 (ELit 0); KDisj (shT k) (ELit 1) (SA PD_SHB SHBASE) (ELit 128);
     KDisj (shT k) (ELit 1) (SA (EVar 58) (-8192)) (ELit 8208); KDisj (shT k) (ELit 1) (SA (EVar 52) 0) (ELit 1016);
     KWord (SA (EVar 32) k) 8 v;
     KDisj (SA (EVar 32) 0) (ELit 288) (SA (EVar 58) (-8192)) (ELit 8208);
     KDisj (SA (EVar 32) 0) (ELit 288) (SA (EVar 52) 0) (ELit 1016);
     KDisj (SA (EVar 32) 0) (ELit 288) (SA PD_SHB SHBASE) (ELit 128)].

  Lemma evT : forall R X k, 0 <= k <= 288 ->
    edenot (HLib.Eseed R (Wx ++ X)) (EAlu ALU_ADD (EVar 32) (ELit k)) = Z_to_bv 64 (this + k).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) ["XT"] "h06__sat3h16__sat5h24__x1h32H0h42Hah57__arithh64__ffh76__sat2h86__sat4h98__varmaph:5__with;4__x2h<2Hkh=1Rh>2T0h?2T1h@1XhA2_HhB3_H0hC3_H1hD1kp;1p;2p;3p;4p;5p;7p;8g0055j15Tg00V6j1;Tg005Zj1ETg0068j1kTg033Rj2aTg0045j1VTg00V[j17Tg00X3j26Tg00OhR0j20Tg00Zbj2LTg00TZj2:Tg01K^j2jTg009_j23Tg00XOj2`Tg00`fj34Tg01LZj2^Tg02T1j3ATg03@Aj2BTg03J^j1[Tg03KVj1@Tg03LNj3>Tg00C8j2CTg00`@j2?Tg00jhj2QTg00kPj3PTg00l4j2ZTg00lUj2NTg00<_j1YTg00loj2MTg00mMj1XTg00mkj1WTg00o9j2OTg00nVj2ITg01:?j3RTg00o\j3KTg010jj1iTg011Lj2hTg011nj2gTg012Zj3fTg0139j4eTg013kj1HTg014Jj2DTg0153j3GTg015\j2STg00F5j3UTg016Hj1_Tg019aj4bTg04;Qj5cTg010?j4TTg0185j7dTg018Yj7]Tg019=j8\Tf0R1#5#5p==g01;FR2/61p=11:21p=9g00GSR3f1R4g01=CP1CTp=<P4g01;dR5g01<CR6P6g01<cR7P1g01=jFdp=2P3P4g01IKP1CTp=Jf2R8P5P6P6P7P4P1F]p=Ff3R9P5P6P6P7P8P4P1G\p=8g00M5R5#5R:#;R;#E%5:R<#5R=#=R>#5R?#ER@#kRA'a%VA%11%;<#5#=#=#7R<,61'0RBg0481p,2ffRC#1%7:RD%7?R?'LRE,:C'0RCp,2fpRF#11:FE'0RFp,1HRGp,1eRH'jRI#9RJ13I<%;;#;#;R;#7RK,LDRL'6RM%7=,`I=4321^GHRH#9%;5#=#=#7,3H/6L'0'0RH'0RG'0R='0RN'0P0PCPNf5g03EZROf4RP5AA'Bg04<HRQ%E>#[R>%@93>'C13I9,?@54AP1P0PFP=f9f8RR9AAO'Bf7RS#@9>Q>'C13IS,?@54AP1P0PJPGf=f<RS9AAO'Bf;RT#@9>Q>'C13IT,?@54AP1P0PMPHfAf@9AAO'Bf?R0#@9>Q>'C13I0,?@54AP1PIfBR01QDKRT%9DRU%1K%9L[RV[RW%1DRXg01G]RYAPDK4UW4RK%1L\Y^4XRZ1QD?R[%1?%9E[R\\UR]APD?4VYX4XR?%1E\Y^4XRXP4g01H91Z2D'NPUeRUO1RYP\PPPUO1RUPVg01H_R^#YR_%V^R`1M34Ra%X3Rb%W3Rc1O35R51I3<Rd5R31I3DRD%E;5K3'<,2cR;%i6R6Pc1I32Re/J5,2cRfP61<e5,2cRgAK3D@RD,J5,2c5FcRhC8C81hc7R7P1P8g01J2Rig01JRRj'N1g18=4ijdAf324CeR2b6b9b:X23131</6LRL%94Rj%181:8E'0[[^23P1PIPRPSO3b5b1b0b7b0b8b1PTPWPKPZP[P]P?PXPYP\PUPVP_P`PaPbPc1<5d,2c9FcgP6PhC8P7P2b6b9b:X23%141:4E'0\B^23P1fIRBfHRhO2b5b1b0b7b0b8b1PTPWPKPZP[P]P?PXPYP\PUPVg00Q;RV#HRU#HR\#HRY#H,D31D3U1D3VRV5G35G3g01K2RU'S1D3Y1D3\=G3V5G3/SU=U^_5U^P`P31M38P4%_3CbPbPcP;P6PcPfP6Pc1O3:R:,<e,2c1<:d,2c5FcP6AR35:R:,<e,2c1J:D,2c5FcC8C8C8P7P2b6b9b:X23X;3%19169<'0139PRP#11:PE'0[\j\L^23^;3P1PBPIPRPSPhO5b5b1b0b7b0b8b1DcfDfC9AAO'B%@09>Q>'C13I0,?@54AeXCHX?MP4P1O2n2001000000121000000X3GX>JP4P1O2n2001000000121000000X3=XBFP4P1O2n2001000000121000000X3NXACP4P1O2n2001000000121000000b3W<XD3W@W=o"). Qed.

  Lemma shT_start : forall R X k, 0 <= k < 288 -> estart (HLib.Eseed R (Wx ++ X)) (shT k) = (this + k) / 8 + SHBASE.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) ["XT"] "h02H0h12Hah24__x1h37__arithh44__ffh56__sat3h66__sat5h78__varmaph85__with94__x2h:2Hkh;1Rh<2T0h=2T1h>1Xh?2_Hh@3_H0hA3_H1hB6__sat2hC6__sat4hD1kp;1p;2p;3p;4p;5p;7p;8g0055j14Tg00V6j16Tg005Zj1DTg0068j1mTg033Rj2gTg0045j1MTg00V[j17Tg00TZj28Tg00OhR0j21Tg00Zbj2JTg01K^j2XTg009_j20Tg00X3j2<Tg00XOj2fTg00`fj35Tg01LZj2bTg02T1j3:Tg03@Aj2;Tg04=4j1=Tg03N?j2>Tg02;ij2@Tg03J^j1^Tg03KVj1]Tg03LNj3\Tg00<_j1[Tg00loj2LTg00mMj1ZTg00mkj1YTg00nVj2ITg00o9j2KTg010jj1WTg011Lj2VTg00lUj2UTg011nj2lTg012Zj3kTg0139j4jTg04=mj4iTg00jhj2STg00kPj3RTg00l4j2hTg013kj1HTg014Jj2?Tg0153j3ETg015\j2QTg00F5j3OTg016Hj1dTg019aj4cTg01:?j3NTg00o\j3PTg03O=j5eTg010?j4TTg0185j7aTg018Yj7`Tg019=j8_Tf0R1#4#4p=Bg01;FR2/<1p=21821p=9g00GSR3f1R4g01=CP1CTp=AP4g01;dR5g01<CR6P6g01<cR7P1g01=jFap=3P3P4g01IKP1CTp=Ff2R8P5P6P6P7P4P1F`p=Gf3R9P5P6P6P7P8P4P1G_p=Cg00M5R5#4R:#6R;#D%4:R<#4R=#BR>#4R?#DR@#mRA'g%MA%21%6<#4#B#B#7R<,81'1RBg0481p,2ffRC#2%7:RD%7?R?'JRE,8C'1RCp,2fpRF#218FE'1RFp,1HRGp,1eRH'XRI#9RJ10I<%6;#6#6R;#7RK,JDRL'<RM%7=R=,fI=5321bGHRH#9%65#B#B#7,0H/<L'1'1RH'1RG'1RN'1RO'1P0PCPOf5g03EZRPf4RQ5:A';%=9'>10I9/@=g02E[RR'0553P1P0PFPNf9f8RS9:AP';f7RT#='>10IT/@=/0R553P1P0PJPGf=f<RT9:AP';f;RU#='>10IU/@=/0R553P1P0PMPHfAf@9:AP';f?R0#='>10I0/@=/0R553P1fDR0fCRU9:AP';RPg04<H%D>#^fBR>#]3\10I>RAP0PUP>g01H_R0#[RV%M0RW1L34%Z3RX%Y3RY1I32RZ1K35R5'A,3YR[1I3<R\,F5,3Y5GY%W6R61A5\,3Y9GY[CC1VY7R7P1P8g01J2R[g01JRR]'U1l18=5[]dAk324CjR]b4b7b8X23%241<4<'1\B^23P1PUP>O2b3Ci1SDK%9DRU%2K%9L[RB[%2DR[g01G]R^ARDK4UW1%2L\^^1[1SD?%2?%9E[RK\UARD?4V^X1[%2E\^^1[P4g01H91h2D'UPUeRUO1PKPQPUO1PBg00Q;RB#HRU#HRK#HR2#H,?31?3U1?3BRB5E35E3g01K2RU'Q1?321?3K=E3B5E3/QU=O0V5O0PWP31L38P4%d3CcPXPYAN35\1I3DRD%D;5P3'A,3YP6PY1FZ5,3YP6PY1K3:R:,AZ,3Y1F:\,3Y5GYP6AN35:R:,AZ,3YAP3D@,F:,3Y5GYCCCCCCP7P]b4b7b8X23X93101</<L%94%29189<'1109QRQ#218QE'1[[[^23^93P1fIPIPSPTfHO5b3b6b5bBb5bCb6De%=>,>P1@A=/0R553eXAHX=MP4P1O2n2001000000121000000X0GX<JP4P1O2n2001000000121000000X0NX@FP4P1O2n2001000000121000000X0OX?CP4P1O2n2001000000121000000b0W:XD3W>W;o"). Qed.

  Lemma shT_apart : forall k, 0 <= k < 288 ->
    (this + k) / 8 + SHBASE + 1 <= ff / 8 + SHBASE \/ ff / 8 + SHBASE + 128 <= (this + k) / 8 + SHBASE.
Proof using HHbp HP FF THI.
    intros k Hk.
    pose proof ex_ranges as (_ & _ & _ & _ & _ & R6 & _).
    pose proof ex_vals as (_ & _ & _ & _ & T8 & _).
    pose proof THI as (f & IN & T1 & T2).
    pose proof FF as (_ & _ & FD). destruct (FD f IN) as [D _]. change (fsz 4) with 1024 in D.
    assert (THF : this + 288 <= ff \/ ff + 1024 <= this) by (destruct D; [right | left]; lia).
    assert (EF : ff = ff / 8 * 8) by (clear - R6; Z.div_mod_to_equations; lia).
    assert (ET : this = this / 8 * 8) by (clear - T8; Z.div_mod_to_equations; lia).
    clear - Hk THF EF ET. set (f8 := ff / 8) in *. set (t8 := this / 8) in *.
    assert (E2 : (this + k) / 8 = t8 + k / 8) by (rewrite ET; rewrite Z.add_comm, Z.div_add by lia; lia).
    rewrite E2. assert (0 <= k / 8 < 36) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    destruct THF as [A|A]; [left | right]; lia.
  Qed.

  Lemma shb_eq0 : ff / 8 + SHBASE = sh ff.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) ["XT"] "h04__x1h17__arithh24__ffh36__sat3h48__varmaph55__witp;1p;2p;3p;4p;7g0055j12Tg00V[j17Tg02BQj2;Tg00X3j26Tg02;ij2HTg00<_j1BTg0045j1?Tg00loj2=Tg00mMj1<Tg00mkj1:Tg00o9j29Tg00V6j13Tg00nVj2ITg01:?j38Tg010?j4GTg0185j7FTg011Lj2DTg00lUj2ATg011nj2@Tg00`fj35Tg012Zj3>Tg0139j4CTg009_j24Tg02N]j1ETf0R0#2#2p=0%30#3p=1p,2ffR1g00M5R2#2#0#7R3';g01;FR4/6116431H13R3,64[[g00GSR5g01H_R6#B%?6f1R6,=5%<5%:5R7g01;dg01<CR8P8g01<cR8P51952R9%32#1#1#1#1#1#1#1#2#0#0#0#0#0#0#0#7R2,I5R:585g02:IA85:9CGg01=jFF1D78P0f2R8g01J2R7g01JRR:'A1@08=57:dA>546CCb2b4b5W014021420555^05P0P3O1b1b3g02E[,43%E1555eo"). Qed.

  Lemma this_apart :
       x_this e + 288 <= xS1 e - 8192
    /\ (x_this e + 288 <= ff \/ ff + 1024 <= x_this e)
    /\ (x_this e + 288 <= sh ff \/ sh ff + 128 <= x_this e)
    /\ (forall k, 0 <= k < 288 -> (x_this e + k) / 8 + SHBASE + 1 <= xS1 e - 8192
                                  /\ ((x_this e + k) / 8 + SHBASE + 1 <= ff \/ ff + 1024 <= (x_this e + k) / 8 + SHBASE)).
Proof using HHbp HP FF THI.
    pose proof (rt_bp_base H HHbp) as HH0.
    pose proof ex_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof ex_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
    pose proof (xS1_facts H e HP) as (S0 & (S1 & S2) & S3 & S4 & S5 & S6).
    destruct (xpre_all H e HP) as (_ & _ & _ & _ & (RF & _) & _).
    pose proof THI as (f & IN & T1 & T2).
    pose proof (proj2 (ah_RFS_range H HH0 _ _ RF) f IN) as (K & Q1 & Q2 & _ & _).
    pose proof (fsz_pos (ff_class f) ltac:(lia)) as FZ.
    pose proof FF as (_ & _ & FD). destruct (FD f IN) as [D _]. change (fsz 4) with 1024 in D.
    assert (TB1 : as_FSB H <= this) by (unfold AFS_HDR in *; lia).
    assert (TB2 : this + 288 <= as_FSB H + AFS_SIZE) by lia.
    assert (SHE : sh ff = ff / 8 + SHBASE) by (unfold sh, SHBASE, ASHADOW_BASE; lia).
    rewrite SHE.
    assert (F8 : 0 <= ff / 8 /\ 8 * (ff / 8) <= ff) by (clear - V1; Z.div_mod_to_equations; lia).
    unfold SHBASE, AIMG_TOP, AFS_HDR, AFS_FLAGS, AFS_SIZE, ALOWSH_LO, AHI_LO in *.
    split; [lia|]. split; [destruct D; [right | left]; lia|]. split; [destruct R11; [left | right]; lia|].
    intros k Hk.
    assert (U : 0 <= (this + k) / 8 /\ 8 * ((this + k) / 8) <= this + k) by (clear - Hk V3; Z.div_mod_to_equations; lia).
    split; [lia|]. destruct R11; [right | left]; lia.
  Qed.

  Lemma kT_ok : forall R X XSc sk LBk m k v (ve : expr), Px XSc sk LBk m -> 0 <= k -> k + 8 <= 288 -> k mod 8 = 0 ->
    rw_cells asegs m (this + k) [C8 (Z_to_bv 64 v)] -> edenot (HLib.Eseed R (Wx ++ X)) ve = Z_to_bv 64 v ->
    know_ok asegs (HLib.Eseed R (Wx ++ X)) m (kT k ve).
Proof using HHbp HP FF THI PCI.
    intros R X XSc sk LBk m k v ve HI K0 K8 KM RC EV.
    destruct (ex_keepT XSc sk LBk m HI) as (THA & _).
    pose proof ex_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
    pose proof ex_wins as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    pose proof this_apart as (A1 & A2 & A3 & A4).
    pose proof (A4 k ltac:(lia)) as (A5 & A6).
    pose proof (shT_apart k ltac:(lia)) as A7.
    assert (ESH : estart (HLib.Eseed R (Wx ++ X)) (SA PD_SHB SHBASE) = ff / 8 + SHBASE).
    { unfold LbB_DPdK.PD_SHB. apply estart_sh; [reflexivity | lia]. }
    pose proof shb_eq0 as SHE.
    unfold know_ok, kT. repeat apply Forall_cons; try apply Forall_nil.
    - apply (kshadow0 _ m (EAlu ALU_ADD (EVar 32) (ELit k)) (this + k));
        [ apply evT; lia | lia
        | eapply (sh0_of_addressable m this 288 (this + k)); [exact THA | change (8 * (288 / 8)) with 288; lia] ].
    - cbn [kentry_ok]. rewrite shT_start by lia. rewrite ESH. unfold elenZ. cbn [edenot]. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. rewrite shT_start by lia. evwx. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. rewrite shT_start by lia. evwx. rewrite !unsigned_lit by lia. lia.
    - eapply (kword_of_rw_cells asegs _ m (this + k) _ 0%nat (C8 (Z_to_bv 64 v))); [exact RC | reflexivity | reflexivity | lia
        | evwx; rewrite unsigned_lit by lia; lia | lia | lia | rewrite EV; reflexivity].
    - cbn [kentry_ok]. evwx. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwx. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. rewrite ESH, SHE. evwx. rewrite !unsigned_lit by lia. lia.
  Qed.

  Lemma scT_flat : forall R X k, 0 <= k < 288 -> flat (HLib.Eseed R (Wx ++ X)) (shT k) 1.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) ["XT"] "h02Hah14__x1h22H0h36__sat3h47__arithh54__ffh64__p1h76__sat2h86__sat5h98__varmaph:5__with;4__x2h<6__sat4h=2Hkh>1Rh?2T0h@2T1hA1XhB2_HhC3_H0hD3_H1hE6__sat1hF1khG1zp;1p;2p;3p;4p;6p;5p;7p;8g0055j15Tg00V6j1>Tg005Zj1FTg0068j1tTg033Rj2nTg0045j1STg00V[j16Tg00TZj24Tg00OhR0j20Tg00Zbj2MTg01K^j2sTg009_j22Tg00X3j2:Tg00XOj2dTg00`fj3RTg01LZj2`Tg02T1j3BTg03@Aj2?Tg04=4j1ATg04VSj3CTg02;ij2ETg013kj1QTg014Jj2ITg0153j3PTg015\j2\Tg00<_j1[Tg00F5j3ZTg00loj2OTg016Hj1YTg019aj4XTg00mMj1WTg00mkj1VTg00nVj2<Tg00o9j2NTg010jj1rTg01:bj6qTg01:?j3GTg011Lj2pTg00lUj2UTg011nj2mTg012Zj3lTg0139j4kTg04?ij4fTg00jhj2LTg00kPj3KTg00l4j2cTg00o\j3JTg02Anj3eTg01Slj2bTg04@Jj5aTg017Zj4gTg02BQj2hTg03N?j2iTg04Pjj4jTg003Wj6_Tg010?j4TTg0185j7oTg018Yj7^Tg019=j8]Tf0R1#5#5p=Hg01;FR2/:1p=1%51#5#5#5p=@1421p=7%>1#>p=8g00GSR3f1R4g01IKP1CTp=;P4g01;dR5g01<CR6P6g01<cR7P1g01=jFop=3P3P4g01=CP1CTp=9f2R8P5P6P6P7P4P1F^p==f3R9P5P6P6P7P8P4P1G]p=Dg00M5R:#5R;#>R<#F%5;R=#5R>#5#HR?#FR@#tRA'n%SA%11RB%>=#5#@#6R=,41'0g0481p,2ffRC#1%6;RD%6?R?'MRE,4C'0RCp,2fpRF#114FE'0RFp,1HRGp,1eRH'sRI#7RJ12I=%><R<#8RK#6RL,MDRM':RN%6>R>,dI=R321`GHRH#7%>:RG#@#6,2H/:M'0'0RH'0RO'0RP'0RQ'0P0PCPQf5RRg03EZRSf4RT5BA'?%A9%6:RU3CP1P0PFPPf9f8RV9BAS'?f7#A;CUP1P0PJPOf=f<9BAS'?f;#A;CUP1P0PNPHfAR0f@9BAS'?f?#A;CUP1P3fBRW,2IRX/E>RYg02E[RZ'2141E%1UR[121U/:E'0'0,0BXG3%1YR\%H<R<#6R],MDR^,4YRYPXP>p-0R_g01H_R`g00Q;Ra#QRb#Q,I31I3b1I3a5P35P3g01K2'\%[`Ra3ZRb%S`R`P31O38P4%Y3RcCXRd%W3Re%V3Rf1<32Rg1N3:R:';,3f%r6RhPf1N3;R;,9g,3fPfP5P6P6P7PTEqR65=fPhAG3:;R5,9g,3fCDCD1pf7R7P1P8g01J2Rig01JRRj'U1m18=RijdAl324CkRjb5b9b:X13X;3W6%71%18/091289Ri#1[[^13^;3^6_P1fCRk/4=PkPIf6PWO5b4PaP`PcPe1<3>Rc,;g,3fP7Pjb5b9b:%7>P1b4RlCfPXP>P^1LDLRX%7DRm%1L%7M[Rn[Ro%1DRpg01G]RqAKDL4UW0RL%1M\q^0pRrP4g01H91c2D'UPmeR2O1RsPnPlb3b7b31LD]Rl%1]%7^[Rt\mRuAKD]4VqX0pR]%1^\q^0pRvPXPoPLPrPsPnPTP2O1PtPbP`PdPePf1<3=Rd9G3:1<3DRb%FK5J3'9,3fPhPf1;;d,3f9=f6Ph%F<9J3bR<9e3c,;5,3fCDCDP7Pjb5b9b:X13X;3X6_121=/:M148=,091b>^,4i[[^13^;3^6_P1fIR_#1P_PIPVfHO5b4b8b3b7b3b<b8DaCg10\YPlPuP]PvfE,2IRv/h>%1v%1>fG,2I/E>#1[[1LD?%1?%7E[Rv\mAKD?4VqX0p%1E\q^0pPsPvPRP2O1PtPaP`1O34PePf19g:,3f1;:<,3f5=fPh%8G#8#8#8#8#8#8#5#H#@#@#@#6RG,<39G3:R:,9g,3fAJ3b@Rb,;:,3f1<3UR@,9g,3fAG3:@/9b,3f5=f5=f5=fCDP7Pjb5b9b:X13141^,0B124GRG#114GE12GU/:E,0['0'0[^13P1fK,2I/E>PVO2b4b8b7bEb7b3b<b812Ik/E>/2ZRZ#114ZE12ZU/:E,0['0'0eb2fDR[ABASk'?RS%AWRA'iP[PkPWP0CjE_ACSAUeXDHX@NP4P1O2n2001000000121000000X2OX?JP4P1O2n2001000000121000000X2PXCFP4P1O2n2001000000121000000X2QXBCP4P1O2n2001000000121000000b2W=XF3WAW>o"). Qed.

  Lemma scP_flat : forall R X k n, 0 <= k -> 0 <= n -> k + n <= 288 -> flat (HLib.Eseed R (Wx ++ X)) (SA (EVar 32) k) n.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) ["XT"] "h02H0h12Hah26__sat3h36__sat5h44__x1h57__arithh64__ffh76__sat2h86__sat4h98__varmaph:5__with;4__x2h<4__x3h=2Hkh>3Hknh?2Hnh@1RhA2T0hB2T1hC1XhD2_HhE3_H0hF3_H1hG1khH1nhI1zp;1p;2p;3p;4p;6p;7p;8g0055j18Tg00V6j1<Tg005Zj1ETg0068j1qTg033Rj2jTg0045j1TTg00V[j1:Tg00Zbj2OTg00TZj27Tg01K^j2pTg00XOj2nTg00`fj3UTg01LZj2fTg00OhR0j21Tg02T1j3BTg03@Aj2CTg03J^j1]Tg03MFj2ATg04VSj3@Tg009_j2FTg00jhj2RTg00kPj3QTg00l4j2\Tg00lUj2PTg013kj1?Tg014Jj2;Tg015\j2JTg00<_j1[Tg00F5j3ITg00loj2KTg019aj4ZTg00mMj1YTg00mkj1XTg00o9j2HTg00nVj2NTg01:?j3DTg00o\j3WTg010jj1oTg011Lj2iTg011nj2hTg012Zj3gTg0139j4eTg00`@j2bTg00SGj2STg03[Bj2aTg003Wj6cTg03\Fj1dTg00C8j2`Tg03]>j1_Tg00X3j2LTg0153j3^Tg010?j4VTg0185j7kTg018Yj7lTg019=j8mTf0R1#8#8p=>g01;FR2/L1p=6f2R3f1R4'F/L1p=31L24/11p=21721p==g00GSR5?^41p=9P5P4g01=CP1CVp=5P4g01;dR6g01<CR7P7g01<cR8P1g01=jFkp=0P5P4g01IKP1CVp=MP3P6P7P7P8P4P1Flp=Gf3R9P6P7P7P8P3P4P1Gmp=4g00M5R6#8R:#<R;#E%8:R<#8R=#>R>#8R?#ER@#qRA'j%TA%64RB%<<#8#>#>#:R<9393g0481p,2ffRC%::RD%:?R?'ORE,7C'2RCp,2fpRF17FE'2RFp,1HRGp,1eRH'pRI#=RJ%<;#<#<R;#:RK,ODRL93I<RM%:=,nI=U521fGHRH#=%<6RG#>#>#:=3HL'1'1RH'1R='1RN'1RO'1P0PCPOf8RPg03EZRQf7RR5BA'C%E>#]R>f6RS'Af5RT3@P1P0PFPNf<RUf;9BAQ'Cf:,A>f93@P1P0PJP=f@f?9BAQ'Cf>,A>f=3@P1P0PMPHfDR0fC9BAQ'CfB,A>fA3@P1P5PIfFRV,F1RW17WEfERXA3WXE'2'1'2XI51RDKRW%=DRY%6K%=L[RZ[R[%6DR\g01G]R]AQDK4UW1RK%6L\]^1\R^1RD?R_%6?%=E[R`\YRaAQD?4V]X1\R?%6E\]^1\R\P4g01H91\2D'PPYeRYO1R]P`f4RbPYO1RYPZg01H_Rcg00Q;Rd#?Re#?Rf#?Rg#?Rh#?,;5Ri1;5gRg1;5dRd'9'9g01K2Rj'J1;5f/9d,9g,9i/Jj1;5h1;5e/9d'9/Jj%[cRj5Ic5Ic3I%TcRcP51K53P41K59CZ%Y5Rd%X5Re1H56R61N5<Rh5D51N5DRD%E;5W5'5,0eR;%o7R7Pe1N52Ri/M6,0eRgP7Pe1H5:R:1H5GRG5D5/5h,0eP7Pe15iG,0eRhP7Pe15i:,0eP7AD56:R:,5i,0eAW5D@RD,M:,0eAD5:G/5D,0e9Geh5Ge5GeC4C4C4C4C41ie8R8P1P3g01J2Rhg01JRR:'P1h13=Uh:dAg524CeR2b6b9b:X45X;5X<5A31<LRL%=4R:A39b<%6TRb1FTSRT17TEA3TRE,2R'1'2\b[[[[^45^;5^<5P1fKfLPIPPPUfHfIfJO8b5b3b2b7b2b8b31b@I,S@PWP[PKP^P_PaP?P\P]P`PYPZPjPc1K54PdPeP;P7PePgP715i6,0e1M6D,0e5GeC4C4P8P2b6b9b:X45173E,23\:\L^45P1PIPPPUO3b5b3b2b7b2b8b3,aIEcfGABAQV'CRV1A>XRX#d'`,S@%_X'FR@17@EA3@0E,20'1'2eA@VX0eXFHXBMP4P1O2n2001000000121000000X0=XAJP4P1O2n2001000000121000000X0NXEFP4P1O2n2001000000121000000X0OXDCP4P1O2n2001000000121000000b0W>X?BW=XH5XG5WCW@o"). Qed.

  Definition tS (T : list fent) (ks : list (Z * nat)) : tab := (EVar 58, xS1 e, -8192, 16, T, ks).

  Definition tFw (hF : Z) (T : list fent) (ks : list (Z * nat)) : tab := (EVar 52, ff, 0, hF, T, ks).
  Definition tHw (hH : Z) (T : list fent) (ks : list (Z * nat)) : tab := (PD_SHB, ff / 8, SHBASE, SHBASE + hH, T, ks).
  Definition tF (T : list fent) (ks : list (Z * nat)) : tab := tFw 1016 T ks.
  Definition tH (T : list fent) (ks : list (Z * nat)) : tab := tHw 128 T ks.
  Definition wok (hF hH : Z) : bool := ((0 <=? hF) && (hF <=? 1016) && (0 <=? hH) && (hH <=? 128))%bool.
  Lemma wok_facts : forall hF hH, wok hF hH = true -> 0 <= hF <= 1016 /\ 0 <= hH <= 128.
Proof using.
    intros hF hH Hw. unfold wok in Hw.
    apply andb_true_iff in Hw as [Hw D]. apply andb_true_iff in Hw as [Hw C]. apply andb_true_iff in Hw as [A B].
    apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C. apply Z.leb_le in D. lia.
  Qed.

  Lemma tab_vals : bv_unsigned (edenot (wenv Wx) (EVar 58)) = xS1 e /\ bv_unsigned (edenot (wenv Wx) (EVar 52)) = ff
    /\ bv_unsigned (edenot (wenv Wx) PD_SHB) = ff / 8.
Proof using HP FF.
    pose proof ex_vals as (V1 & _). pose proof ex_wins as (_ & _ & _ & _ & _ & _ & W7 & W8).
    split; [change (edenot (wenv Wx) (EVar 58)) with (Z_to_bv 64 (xS1 e)); apply unsigned_lit; lia|].
    split; [change (edenot (wenv Wx) (EVar 52)) with (Z_to_bv 64 ff); apply unsigned_lit; lia|].
    unfold PD_SHB. apply (srl3_val (wenv Wx) (EVar 52) ff); [reflexivity | lia].
  Qed.

  Lemma tabs_wf3w : forall hF hH SF FT HT ks1 ks2 ks3, wok hF hH = true ->
    fwcl (wbound Wx) SF = true -> fwcl (wbound Wx) FT = true -> fwcl (wbound Wx) HT = true ->
    fin (-8192) 16 (fkeys SF ++ ks1) = true -> fin 0 hF (fkeys FT ++ ks2) = true -> fin SHBASE (SHBASE + hH) (fkeys HT ++ ks3) = true ->
    tabs_wf Wx [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3].
Proof using HP FF.
    intros hF hH SF FT HT ks1 ks2 ks3 Hw C1 C2 C3 F1 F2 F3.
    destruct (wok_facts hF hH Hw) as (Wf & Wh).
    pose proof ex_wins as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8). pose proof tab_vals as (T1 & T2 & T3).
    pose proof ex_vals as (V1 & _).
    split.
    - repeat constructor; cbn [tb tB tlo thi ttbl tks tS tFw tHw]; try reflexivity; try assumption; unfold SHBASE in *; lia.
    - intros t1 t2 H1 H2 Hb. cbn [In] in H1, H2.
      destruct H1 as [<-|[<-|[<-|[]]]]; destruct H2 as [<-|[<-|[<-|[]]]]; cbn [tb tB tlo thi tS tFw tHw] in *;
        try (vm_compute in Hb; discriminate Hb); unfold SHBASE in *; lia.
  Qed.
  Lemma tabs_wf3 : forall SF FT HT ks1 ks2 ks3,
    fwcl (wbound Wx) SF = true -> fwcl (wbound Wx) FT = true -> fwcl (wbound Wx) HT = true ->
    fin (-8192) 16 (fkeys SF ++ ks1) = true -> fin 0 1016 (fkeys FT ++ ks2) = true -> fin SHBASE (SHBASE + 128) (fkeys HT ++ ks3) = true ->
    tabs_wf Wx [tS SF ks1; tF FT ks2; tH HT ks3].
Proof using HP FF.
    intros SF FT HT ks1 ks2 ks3 C1 C2 C3 F1 F2 F3.
    exact (tabs_wf3w 1016 128 SF FT HT ks1 ks2 ks3 eq_refl C1 C2 C3 F1 F2 F3).
  Qed.

  Lemma wk_stk : forall m (ks : list (Z * nat)), stk asegs m (x_lo e) SP -> fin (-8192) 16 ks = true ->
    forall k w, In (k, w) ks -> wr_at asegs m (xS1 e + k) (Z.of_nat w).
Proof using HP FF.
    intros m ks ST Hf k w Hi. destruct (fin_In _ _ _ k w Hf Hi) as (H1 & H2 & H3).
    pose proof ex_wins as (_ & _ & _ & _ & W5 & W6 & _).
    pose proof (wr_at_of_stk asegs m (x_lo e) SP ST) as W. eapply wr_at_sub; [exact W | lia | lia | lia].
  Qed.
  Lemma wk_win : forall m A n (ks : list (Z * nat)) B lo0, wr_at asegs m A n -> A = B + lo0 ->
    fin lo0 (lo0 + n) ks = true -> forall k w, In (k, w) ks -> wr_at asegs m (B + k) (Z.of_nat w).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) ["XT"] "h04__x1h12H0h24__x2h34__x3h41Wh57__arithh64__ffh78__varmaph85__with94cstrh:1Ah;4__p1h<4__x4h=4__x5h>1kh?1wh@1BhA2H1hB2H2hC2H3hD2HfhE2HihF1ahG2kshH3lo0hI1mhJ1np;1p;2p;3p;4p;7p;6p;9p;<p;8g0055j1:Tg005Zj1JTg0068j1ETg03YUj1MTg004Uj2dTg0045j1HTg009_j20Tg00`fj3CTg04d>j3BTg00=?j4LTg009Hj3DTg00:<R0j14Tg054Dj7aTg00X3R1j21Tg013kj15Tg01_iR2j22Tg00OhR3j23Tg00V[j1GTg00lUj2=Tg03ZYj6VTg03:Qj4UTg03;8j1TTg00<_j1QTg00loj2<Tg019aj4>Tg00mMj1PTg00mkj1OTg00o9j2;Tg00V6j1ATg010jj1NTg011Lj2KTg011nj2RTg012Zj3STg0139j4cTg016Hj1bTg00nVj2ITg01:bj6`Tg018Yj7_Tg055@l9]Tg003Wj7ZTg01mPj4[Tg02j9l<\Tg010?j4YTg0185j7XTg01:?j3^Tg019=j8WTg00IMf2R4f1R5f0R6C[p=9g01J2R7g01JRR87C6p=@g00H1R9g00GSR:P2P0P1g047Of5R1f4R0f3R2P4P5P6M<\p=FP:P5g01=CP6CYp=7P5g01;dR;g01<CR<P<g01<cR=P6g01=jFXp=8A^:56p=6P2P;P<P<P=P4P5P6GWp=?g00M5R>#:R?#:R@#:RA#:#:#:#J#E%JA#E#M[1d:9RB#HA910210459C:1P:1024RCf8RDf6RE796f7RF,00=B0E#@P:P9P5P6CLRGf9RH5DBf=RI10H4%45RJ39[^?9^>:[]4X::A9FC1102E=B21#@ADBGDPFf:RG,0FRBPHP4P5P2P6Fa11F4104J/1Bg00Q;#5RB/25%5B#5#5#5#5#5#5RJ,25'3'3'3P311D2%44,02f;RC,0D'112B4124J'3'3f>RK10G0%4239P611G1%41,0E10CK'112B1121J'3'3P3%4E,0Ff<f?'0'112BE12EJ'3fB10KD%4F39P6%4D,0HfARF,0K'112BH12HJ'3fEf@,0FfCRH10FC%4GRFPI12BGR312GJRL'3%G>RM/1FRN%GARA,1FRO'3RPP3PLPNPOPBPM1=:MPGPF1=:FRBEFPGPFPBPJPA1=:AEFEVP6CURJPP%TCRBg01;FRF%4C'1RCg01H_RG#QRO%HGRGP:1<:4P51<:2C>%P:RN%O:RL1;:?R3%A>,;:RQ'7,8L%N<RR1;:>R>/63RS16>Q'7,8LC?1KL=RTP6P41=781R64#@dAS:F5CcR8b6b7b8X0:X2:X3:11541054R71052'1[^0:^2:^3:P6PKPHfDRUPDO4b5b9b1PJPPPBPCPOPGP:P:1<:0P4%b:RDC>P5P:1<:1P2PDC>C>PNPL163Q1;:@R@%A?,;:R?'6'7,8LPR16SQ16>@/6?'7,8LC?PTP8b6b7b8X0:X2:X3:X<:X=:1020,1710721050/01'1[^0:^2:^3:^<:^=:P6fFPH%4IRIPKPUP0O6b5b9b1PJPPPBPCp-0RCPOPG1<:5PNPLPLP;P<P<P=1I:M/7>,8LPLP;P<P<P=P2E`F_PR1I:F/7>,8LC?PTP8b6b7b8X0:W;11M6/3511F5[^0:^;CP611IAPIP4O3b5b9b1M9]WCWBP5P6O2n2001000000121000000W1WAP5P6O2n2001000000121000000bFWEX?9X>:WDW4PEP6P5FZW1W4XH:X@:WGXJ:X::WIo"). Qed.
  Lemma shb_eq : ff / 8 + SHBASE = sh ff.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) ["XT"] "h04__x1h17__arithh24__ffh36__sat3h48__varmaph55__witp;1p;2p;3p;4p;7g0055j12Tg00V[j17Tg02BQj2;Tg00X3j26Tg02;ij2HTg00<_j1BTg0045j1?Tg00loj2=Tg00mMj1<Tg00mkj1:Tg00o9j29Tg00V6j13Tg00nVj2ITg01:?j38Tg010?j4GTg0185j7FTg011Lj2DTg00lUj2ATg011nj2@Tg00`fj35Tg012Zj3>Tg0139j4CTg009_j24Tg02N]j1ETf0R0#2#2p=0%30#3p=1p,2ffR1g00M5R2#2#0#7R3';g01;FR4/6116431H13R3,64[[g00GSR5g01H_R6#B%?6f1R6,=5%<5%:5R7g01;dg01<CR8P8g01<cR8P51952R9%32#1#1#1#1#1#1#1#2#0#0#0#0#0#0#0#7R2,I5R:585g02:IA85:9CGg01=jFF1D78P0f2R8g01J2R7g01JRR:'A1@08=57:dA>546CCb2b4b5W014021420555^05P0P3O1b1b3g02E[,43%E1555eo"). Qed.

  Lemma fin_wider : forall lo hi hi' ks, fin lo hi ks = true -> hi <= hi' -> fin lo hi' ks = true.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) ["XT"] "h05lemmah12kwh21xh31Kh41Fh52H0h62K1h72K2h84__x1h94__x2h:4__x3h;4__x4h<1Ah=1Bh>2Hhh?2Hkh@2K3hA2K4hB7__arithhC4__ffhD8__varmaphE5__withF4cstrhG2hihH3hi'hI2kshJ2lohK1yp&0p;2p;1p;3p;4p;8p;6p;7p;5p;=g004Uk200Tg0045j1]Tg04d>j3STg00X3j2<Tg04XHj20Tg013kj1>Tg056?j29Tg056_j3FTg009Hj3`Tg04YCR0j2:Tg04`=R1j2}Tg057;j3UTg04Y\R2j3HTg04Xej28Tg00OhR3j24Tg04ZMj2BTg04CUj4KTg001?j4eTg04Znj2dTg057^j4cj7wTg04[[j8MTg04Ebj3bTg04\NR4j6ITg04]@j2_Tg00:<j1RTg009_j2JTg03;8j1~Tg014Jj2QTg0153j3^Tg015\j2|Tg00<_j1{Tg00F5j3yTg00loj2[Tg016Hj1xTg019aj4ZTg00mMj1uTg00mkj1tTg00o9j2GTg0055j1YTg01:?j3sTg010jj1rTg00V6j1qTg0185j7WTg058@j5pTg058dj6oTg011Lj2nTg00lUj2mTg011nj2lTg012Zj3kTg0139j4jTg017Zj4LTg00`fj3ATg02\Pj3iTg02\mj3vTg04_Jj4hTg04]`l=gTg010?j4zTg019=j8fTg01J2R5f0R6g01JRR73Ap=1g00GSR8g00H1R9;i6p=6Av896p=3f1R:%R6'Jp=7f3R;f2R<'8/8:/86p==p-0R=P0P;g059HR>P<P:P6Fwp=\18<:/86p=N18:6=A57p=;AA5:7/46p=?P=P:P0P6CKp=PP=f4R?P0P0P;P<P:P6GMp=T19:6=A57p=2P=P0P:P6Chp=CP6P:P3P4P<g01=jR4P;P?f5R@f6RAf7RBf8RCf9RDM=gp=DP=P=P0P0P6P0P1P2GMp=aAA567,4:p=@14<:/46p=E10:6=A57p=5P8P:g01=CP6Czp=OP:g01;dR2g01<CREPEg01<cRFP6P4FWp=XP;P2PEPEPFP<P:P6Gfp=V20089R9#]AS;<6#11<;<%66RG,0ARH%36RI,7GRJ/0?g00Q;RK#>RL/9IRM%>LRN#>#>#>#>#>#>RO,9IRIC=X19RP=F9<#1A`96;RQ10CGRR10JARSPMPIC=X19P:O1#1[^29':1}6:XK=X2=RT10BGRU10J@RVPMPIC=X19=F9;#1A`96?RW10DGRG10JBRXPMPIC=X19P:O1#1[^29P6C\W0AU9P<PHPVPMPIC=X19RV=F9<#1PRPXPMPIC=X19P:O1#1\Q^29RQ':PUPSPMPIC=X19=F9;#1PG10JCPMPIC=X19P:O1#1\W^29;H6W0AU9V<P:O2PQP<P:P6O2%6:RQ,0C%3:RV,7Q/0B19LV3N19VO';%6<RV,0DRQ%3<RI,7VRV/0B19LIRM3NRJ19IORI';%1IRG,?J':PTf:RS%6;RU'0RX%3;RR,7URU/0C'8RH19LRRP'8RY19RORR';%1YRY%1RRZ'4P6C\W01BJI10VC=NQMRM/;I1?MGRG':10UD,8XRX/8PRU/;R%1URU/4Z;H6W01BMIP6O2PG%1PRG,?H,:YP=^==RY^<=RMP=\=P=P=P0P0CKRI'PRRP=P=P0P=P=P=P1CeRQCKRV,PYRJPY1d=0R[PIPVP=P=P0P0P[P0PQP=P0PTP>CcGMDTR>f;RT%6?RQ'0RV%3?R\,7QRQ/0DR]'8R^19L\R_';%1^R^%1_R`'4P612\OR\P\g04`[9b=0Ra/C\RbM:DW01BHP1?XGRG,:UPMPRP=P=P0P1CKR1,PYR0PYP[PIP1%a[DTR[10QSRQ,8VR1/;_%11R1/4`P6P\P\PbM:DW01BXPP6O214GZ%1VRG/@],:^PMPRPJP>f<R^%6@RZ'0RX%3@RP,7ZRZ/0SRb';R_12LPRI'4%1XRY/@bRb/4IP_PbP6PIPI1CaIRbEI12PORPPP1CaPR_M:DW01BV]1@GQRG,:1PMPRP0P[10ZTRZ,;XRX/4I1@YZRZ/4IRYPXPZP6PIPIPbEIPPPPP_M:DW01BVQP6O2AEG`\P3PYPPf=RP%6ARY'0%3ARA,7Y/5T'?12LA12AO3EP6f>RA%6BRY'5%3BRB,7Y/5P12LB3EP3f?RB%6CRY'0%3CRC,7Y/5A'?12LC%3D/2OfARD%6SRC'5RY%3SRS,7CRC/0B'@12LS12SO3E[P6f@RS,0C,@YP3fBR3%6TRY'5%3T,7Y/5D%3^,2L%3P/2OfER^%6ARY'0%3ARA,7YRYfCRT'5'?12LA12AO3E[[P6fDRA%6P'515YA%3B,2L%3S/2OfHRS%6DRD'51<SDRB':RAPMPRPJP>fIR>%63RJ'5RR%33R3,7JRMfGRY'5RP'4RC12L3RG'41<>JRJ/4PR\/4GPCP\PRPJP6PPPP1CaPEIPGPG1CaGEI123OR3P31Ca3M:DW01_SDRDAHRJ6X0APDP;O2PB15MS1<MSRB':%6TRD%3TRT#RRA'JRJ/5>1<J>;H6W01_MSP;O2PBfJRB/<DRD15JSRJ'4RS12LTRM'412TOPSPMPDPJP:%~Tg01;FRT/<Ag01H_RA1Q8N1Q8L1Q8K5^85^8g01K2'|%{A3y%]AP8P81[8?P<%x8CZP:1[8;CZ%u8%t8RAg00M5RK,G8%YKRL,G85s8RN%YL,G8RL'O,XA%rERJPA%qK,G8RK,OL,XAPJPAP2PEPEPAP2PEPEg05:>RJ1ONKP4FWPAP2PEPEPJDpEoCVCV1nAFP6P<1m571l6<#1dAk8T:CjbCbDbEX88X98X:8X;81J6:/<;1<?;1J<;/5?[[^88^98^:8^;8P6fKPB%3^#R%6^P<PYO6bBbFCLP;CLP<CLb7b6O2WAW@W7W6P:P6O2n2001000000121000000W5P:P6O2n2001000000121000000W5P:P6O2n2001000000121000000b3O2b3O2b3O2b3X?WX19b4O2AS@;<#1eW>W4WIXH8XG8XJ8o"). Qed.
  Lemma tabs_ok3w : forall hF hH XSc sk LBk m SF FT HT ks1 ks2 ks3, wok hF hH = true -> Px XSc sk LBk m ->
    ftbl Wx (xS1 e) m SF -> ftbl Wx ff m FT -> ftbl Wx (ff / 8) m HT ->
    fin (-8192) 16 ks1 = true -> fin 0 hF ks2 = true -> fin SHBASE (SHBASE + hH) ks3 = true ->
    tabs_ok Wx m [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3].
Proof using HHbp HP FF.
    intros hF hH XSc sk LBk m SF FT HT ks1 ks2 ks3 Hw HPX H1 H2 H3 F1 F2 F3.
    destruct (wok_facts hF hH Hw) as (Wf & Wh).
    destruct (ex_keep XSc sk LBk m HPX) as (_ & _ & _ & ST & FW & SW & _).
    apply Forall_cons; [split; [exact H1 | exact (wk_stk m ks1 ST F1)]|].
    apply Forall_cons; [split; [exact H2 | exact (wk_win m ff 1016 ks2 ff 0 FW ltac:(lia) (fin_wider 0 hF (0 + 1016) ks2 F2 ltac:(lia)))]|].
    apply Forall_cons; [split; [exact H3 | exact (wk_win m (sh ff) 128 ks3 (ff / 8) SHBASE SW ltac:(rewrite shb_eq; lia)
                                                    (fin_wider SHBASE (SHBASE + hH) (SHBASE + 128) ks3 F3 ltac:(lia)))]|].
    apply Forall_nil.
  Qed.
  Lemma tabs_ok3 : forall XSc sk LBk m SF FT HT ks1 ks2 ks3, Px XSc sk LBk m ->
    ftbl Wx (xS1 e) m SF -> ftbl Wx ff m FT -> ftbl Wx (ff / 8) m HT ->
    fin (-8192) 16 ks1 = true -> fin 0 1016 ks2 = true -> fin SHBASE (SHBASE + 128) ks3 = true ->
    tabs_ok Wx m [tS SF ks1; tF FT ks2; tH HT ks3].
Proof using HHbp HP FF.
    intros XSc sk LBk m SF FT HT ks1 ks2 ks3 HPX H1 H2 H3 F1 F2 F3.
    exact (tabs_ok3w 1016 128 XSc sk LBk m SF FT HT ks1 ks2 ks3 eq_refl HPX H1 H2 H3 F1 F2 F3).
  Qed.

  Lemma Px_step3w : forall hF hH XSc sk LBk SF FT HT ks1 ks2 ks3 m m', wok hF hH = true -> Px XSc sk LBk m ->
    munch (winsT [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3]) m m' -> wmono asegs m m' -> mem_inv asegs m' -> Px XSc sk LBk m'.
Proof using HHbp HP FF.
    intros hF hH XSc sk LBk SF FT HT ks1 ks2 ks3 m m' Hw HPX MU WM MI.
    destruct (wok_facts hF hH Hw) as (Wf & Wh).
    pose proof (xS1_facts H e HP) as (_ & (S2 & _) & _ & _ & S5 & S6).
    pose proof aceil_facts as ((A1 & _) & _).
    pose proof HPX as HX. unfold Px, xinv in HX. destruct HX as (_ & _ & _ & _ & _ & _ & _ & _ & ST & _).
    apply (xinv_munch H (rt_bp_base H HHbp) e ff fp XSc sk LBk m m' _ HP HPX MU WM MI).
    - eapply LbB_WoGen.stk_wmono; [exact ST | exact WM | lia].
    - unfold winsT. cbn [map tB tlo thi tS tFw tHw]. pose proof shb_eq as SE.
      apply Forall_cons; [unfold xwin; cbn [fst snd]; left; unfold SX_SAVED; lia|].
      apply Forall_cons; [unfold xwin; cbn [fst snd]; right; left; unfold SX_FLAGP; lia|].
      apply Forall_cons; [unfold xwin; cbn [fst snd]; right; right; lia|].
      apply Forall_nil.
  Qed.
  Lemma Px_step3 : forall XSc sk LBk SF FT HT ks1 ks2 ks3 m m', Px XSc sk LBk m ->
    munch (winsT [tS SF ks1; tF FT ks2; tH HT ks3]) m m' -> wmono asegs m m' -> mem_inv asegs m' -> Px XSc sk LBk m'.
Proof using HHbp HP FF.
    intros XSc sk LBk SF FT HT ks1 ks2 ks3 m m' HPX MU WM MI.
    exact (Px_step3w 1016 128 XSc sk LBk SF FT HT ks1 ks2 ks3 m m' eq_refl HPX MU WM MI).
  Qed.

  Ltac tnormp H :=
    lazymatch type of H with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    end.

  Ltac exrun3w hF hH HRT HSF HFT HHT HPX HMI fuel stops kx :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HPX with Px ?XSc ?sk ?LBk _ =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tFw hF FT []; tHw hH HT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) ((kst_ex ++ kx) ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] (((kst_ex ++ kx) ++ kf) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wx) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 58) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wx [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3]
                    (tabs_wf3w hF hH SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    (Px XSc sk LBk) (fun m0 m0' => Px_step3w hF hH XSc sk LBk SF FT HT ks1 ks2 ks3 m0 m0' eq_refl)
                    Q R F pc fc m ro RT [] ((kst_ex ++ kx) ++ kf) fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply (tabs_ok3w hF hH XSc sk LBk); [vm_compute; reflexivity | exact HPX | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HPX | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply Forall_app; split; [apply (kst_ex_ok _ _ XSc sk LBk); exact HPX | ] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end
    end.

  Ltac exrun3wd dirs hF hH HRT HSF HFT HHT HPX HMI fuel stops kx :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HPX with Px ?XSc ?sk ?LBk _ =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tFw hF FT []; tHw hH HT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) ((kst_ex ++ kx) ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (((kst_ex ++ kx) ++ kf) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wx) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 58) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wx [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3]
                    (tabs_wf3w hF hH SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    (Px XSc sk LBk) (fun m0 m0' => Px_step3w hF hH XSc sk LBk SF FT HT ks1 ks2 ks3 m0 m0' eq_refl)
                    Q R F pc fc m ro RT [] ((kst_ex ++ kx) ++ kf) fuel stops (SCR dirs [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply (tabs_ok3w hF hH XSc sk LBk); [vm_compute; reflexivity | exact HPX | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HPX | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply Forall_app; split; [apply (kst_ex_ok _ _ XSc sk LBk); exact HPX | ] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end
    end.

  Ltac exrun3 HRT HSF HFT HHT HPX HMI fuel stops kx := exrun3w 1016 128 HRT HSF HFT HHT HPX HMI fuel stops kx.

  Ltac tsplit HTS H1 H2 H3 :=
    lazymatch type of HTS with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in HTS; clear E end;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS]; apply Forall_cons_iff in HTS as [H3 _];
    cbn [fst snd] in H1, H2, H3.

  Ltac rgetx HRT r H :=
    lazymatch type of HRT with rtbl _ ?R ?RT =>
      let e0 := eval vm_compute in (match find (fun p : reg * expr => bv_eqb (fst p) r) RT with Some p => snd p | None => ELit 0 end) in
      assert (H : PropExec.getr R r = edenot (wenv Wx) e0)
        by (apply (rtbl_In Wx R RT r e0 HRT); apply LbB_DCtorK.inb_In'; vm_compute; reflexivity);
      unfold wenv in H; cbn [edenot] in H; unfold HLib.Eseed, reg_ev, Wx in H;
      lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
            Init.Nat.add Nat.sub nth app] in H;
      rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z in H by (pose proof ex_vals; pose proof ex_wins; lia)
    end.

End XT.

Lemma rtbl_sw : forall W W' k R RT, (forall n, (32 <= n < k)%N -> ev (wenv W) n = ev (wenv W') n) ->
  forallb (fun re : reg * expr => wcl k (snd re)) RT = true -> rtbl W R RT -> rtbl W' R RT.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) [] "p'0h02reh11xh21Ah31Ph41lh51Ch61Gh71Hh82HCh92HEh:2HTh;2Hih<1Rh=2RTh>1Wh?2W'h@1bi001bhA2e0hB1khC1nhD1ri011ei021pp;1p;2p;3p;4p;6g0055j14Tg005Zj1>Tg0068j1@Tg0045j19Tg00V6j1MTg033Rj2LTg004UR0j2KTg036Qj2GTg0365j2FTg00OhR1j2ETg00B>j11Tg03?Mj2?Tg00`fj3:Tg02\mj3=Tg04foj26Tg056_j3<Tg05H<j3DTg00;\j37Tg009Hj33Tg00<=j3BTg02\Pj3;Tg038Lj22Tg00=?j48Tg00=_j6CTg057;j3HTg00C8j2ATg05I6j6ITg003Wj6JTg01J2f0R2g01JR3:p=5f3R3f2R4f1R5/A23:p=0g00M5#4R6#4#4#4#4R7#4#>#@R8#9R9g03A8R:%M6#>R6/L8%@6R6g00PCR;'KR<#9%>7/G21F23'Ef6R7#1/?5f5#1/?55:8[^C:f4R:A=6;2R='6X0<=<<5#5AD734g00OKp4p710R>p-0\2R?%95R@P1A7452A3:24P:P5O1[^13R1[A3325P3P5O1[^14A7345[RAA7:34\1AB452P2n2001000000120000000W4W3W2PA^4@^3?^2>P2P<P8A;6;2R>,27f8R?#1P=C0X0<P:P0P6P;A3<27P8A;6;5,2?f:R?#1A=6;5C0[P2P6P;P5P2C8f9R053<P8f<R@/2>f?RA#1R1P=C0X0<RB=7<?A3<2@RCP812A>fB#1P=C0X0<P5O1[^1<[f;RD93<2P8f>RE/2>fARF#1P=C0X0<P5O1[^1<P8f=RG/2>f@R>#1RHP=C0X0<=7<D[AB<B?f7P6P;P4P5C8R?P2ECPBP?O116E=X0<R?=<<D#5A3<2G16F=X0<P5O1#5[^1<[16>=X0<P5O1#5\C^1<16A=X0<=<<@#5[AH<?DP0P6P;P3P4C8R4P5ECP?P4O1#5P81AH3P8P2PHP:C0X@8PHP1PEP3P2PDEI12G:P5EJP8P6P;P:P3C8R89;6;,2GP1A=6;8C0eb5b6W;XA;XD6P5P2O2n2001102000121100101X1<O4b7AD7:3eW:W8W9W=W<WBX?9W>o"). Qed.
Lemma ftbl_sw : forall W W' k B m tbl, (forall n, (32 <= n < k)%N -> ev (wenv W) n = ev (wenv W') n) ->
  fwcl k tbl = true -> ftbl W B m tbl -> ftbl W' B m tbl.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) [] "p'0h01fi001fh11xh21Ah31Ph41lh51Bh61Ch71Gh81Hh92HCh:2HEh;2HTh<2Hih=1Wh>2W'h?1bh@1ei011ehA2e0hB1ki021khC2k0hD1mhE1ni031nhF1pi041phG3tblhH1wi051wi061yi072y0i082y1i091zp;1p;2p;3p;4p;6g0055j14Tg005Zj1BTg0068j1GTg0045j1:Tg036Qj2PTg0365j2OTg00OhR0j2LTg00B>j10Tg03?Mj2@Tg00`fj3>Tg04cDj2DTg006[j4;Tg00;\j37Tg009Hj33Tg00<=j3ATg004UR1j2?Tg00C8j22Tg00<_j1NTg00=?j46Tg00=_j6=Tg04foj28Tg056_j3<Tg057;j3FTg05I6j6HTg03GLj6ITg009_j2ETg00D0j2JTg00E8j2KTg00F5j3CTg00FUj4MTg01J2R2f0R3g01JR3>p=5g00IMf6R4f5R5f4R6'Eg00HPR7f3R8f2R9f1R:'J'K;C3CMp=1g00GSR;g00H1R<P:P3C6p=9g00M5#4#4#4#4#4R=#4#B#GR>#:R?g03A8R@g00MZg00NQ#:%B=/P31O36'Lf7R=#0/@:%04/@:5>>[^E@1D6:#5P=P6P8P9C;g00OKp4p710R@p-0RA\3RB%::RCP0A79:3A3639P6P:O1[^18R0[A383:P8P:O1[^19A789:[RDA7689\0AA9:3P3n2001000000120000000W4W3W2PD^4C^3B^2@P31?;<R@g00PCRB'?RCP1P@PBPAP3P1P;P<PAP:f:RDf;R0P:P3P3f=RE#0/29%N7R7F1n2001106000120102105n2001100000120106101X0CP6P1P@PBA3C34P1P@PBPAP:P1P;P<PAP:f<PEP:P3P3f?RF#0/29P7F1n2001106000120102105n2001100000120106101[P3P1P;P<P@PBP:P3C6=3CDP1P;P<PAP9f>RDPFP:P3P3fARG#0/28P7F1n2001106000120102105[^@BP3P@PB199:P3C6=3CEP1P@PBPAP3P1P;P<PAP:fDRHfERIP:P3P3fHRJ#0/29P7F1n2001106000120102105n2001100000120106101X0CRK=7CDf@RL93C3RMP1P@PBPAP3P1P;P<PAP:fGRNPJP:P3P3fK#0/29P7F1n2001106000120102105n2001100000120106101X0CP:O1[^1C[A3C3FP1P@PBPAP3P1P;P<PAP:fFROPNP:P3P3fJRP#0/29P7F1n2001106000120102105n2001100000120106101X0CP:O1[^1CP1P@PBPAP3P1P;P<PAP:PIPOP:P3P3fIRO#0/29P7F1n2001106000120102105n2001100000120106101X0C=7CF[AACKDP0P@PB1989P:C6R0P3E=PKP0O1P1P@PBP2P3P1P;P<P2P:18N9n2001106000120107108n2001100000120106101X0CRN=<CF#5A3C3GP1P@PBP2P3P1P;P<P2P:18P9n2001106000120107108n2001100000120106101X0CP:O1#5[^1C[P1P@PBP2P3P1P;P<P2P:18O9n2001106000120107108n2001100000120106101X0CP:O1#5\M^1CP1P@PBP2P3P1P;P<P2P:18J9n2001106000120107108n2001100000120106101X0C=<CL#5[AFCNFPEP@PB1968P9C6R9P:E=PNP9O1#5P>%0IRI/28fBR9fCRNP4P5P5P3P7F1X?>P:%0HRH/28R>PIPHPNP8P3PFEHEIPGP9P5P6P6P>P7F1eb6b7W<XABXH<XC;P:P3O2n2001104000121109103XF@P:P3O2n2001104000121104101X1CO4b8P=P5P6P8C;eW;W9W:WGWDX5;WBX>?W=o"). Qed.
Lemma Wx_sw1 {HCEIL : HeapCeil} : forall (H : asr) (e : xent H) ff fp p1 n1 p2 n2 q2 m2 n, (32 <= n < 61)%N ->
  ev (wenv (Wx H e ff fp p1 n1 p2 n2)) n = ev (wenv (Wx H e ff fp p1 n1 q2 m2)) n.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) [] "p'0h01Kh11kh24__p1h34__x1h44__p2h51ni001nh65HCEILh73Hn0h82X0h97__arithh:4__ffh;8__varmaph<5__with=4cstrh>1Xh?4__p3h@4__x2hA1xhB1HhC2H3hD2HnhE2K0hF1bi011bhG2b0hH5cstr0hI1ehJ2ffhK2fphL1mhM2m2hN2n1hO2n2hP2p1hQ2p2hR2q2hS2z3p%0p&0p;1p;2p;3p;8p;4p;6p;7p;<p;Bg05J6k109Tg0055j1@Tg005Zj1LTg036QR0j2=Tg00V6j1HTg0365R1j2ATg00Ohj2:Tg035Sj2tTg036mj2[Tg037JR2j3oTg0068j1aTg05K2j2lTg037nR3j1<Tg00`@j2OTg038Lj2^Tg039>R4j1\Tg013kR5j11Tg039^j2YTg03EZj80Tg03:5j43Tg00`fj3;Tg00V[j1NTg00TZR6j28Tg03:Qj4ETg00X3R7j29Tg03ZYj6dTg05Kdj1cTg00<_j1bTg0045j1mTg00loj2`Tg00mMj1kTg00mkj1jTg00nVj2KTg00o9j2_Tg010?j4ITg010jk108Tg011Lk207Tg00lUj2]Tg011nk206Tg012Zk305Tg0139k403Tg034>R8j22Tg01XXj2GTg03;]j2MTg03=:j2}Tg00\9j2hTg014Jj2XTg0153j3gTg015\j2|Tg00F5j3{Tg016Hj1zTg019aj4yTg02Ckj3xTg02E7j7wTg02g`j4uTg00:<R9j1VTg009_j2DTg03;8j1rTg03>Vj2fTg03?Mj2PTg00B>j1eTg02j9l<ZTg0185j7qTg01:bj6pTg018Yk700Tg019=j8nTg02iTl<RTg02hnmB04Tg01:?j3JTf0R:#1#1p>02g00GSR;/]:p=>g03A8R<P;P1P3P6g03BTf5R1f4R=f3R>f2R?f1R@P:M<Zp=WP<P;P0P3P7g03E:P1P=P>P?P@P:M<Zp=QP@g01;dR7g01<CR0P0g01<cRAP:g01=jFqp=?P@P7P0P0PAP:Epp=UP?P7P0P0PAP@P:K00p=TP;P@g01IKP:CIp=SP>P7P0P0PAP?P@P:Gnp=FP<g00H1RBP;P;P4P3P9P>g03CVP?P@P:M<Rp>01PBPBPBP;P;P;g03D3P9P9P9f6R3g03DSP1P=P>P?P@P:NB04p=~PBP;P8P9P6g03C4P1P=P>P?P@P:M<Zp=iP=P>P?P@C3=;1:p=4P>P?P@P:C3,]=p=51D=>/D?/D@/D:p=6PBPBP;P;P5P9P9P>g05LGR6P?P@P:M<Rp=sPBPBP;P;P5P9P9P3P6P1P=PBPBP;P;P5P9P9P>P6P?P@P:M<RM<Rp=7AJ;@:p=vAJ;=>=J;?=J;@=J;:p=C%1:#1#1#1p=Bg00JDR6g00KC&09:g00M5R9#@R5#@#@S00#@#@R8#LR4/=:%H9#HS01#H#@#HRC#LRD,A:':1t@41A@41=4@1[@43o1[?4g01J2REP21A>41=4>%@8#LR2#aRFPEPFP@%H5#LRG/lFRH%<1RI,OG'^RJPF%\1S02g00Q;RK#1RL#1RM#1RN#1RO#1RP#1RQ#1RR#1RS#1RT#1RU#1RV#1RW#1RX#1RY#1RZ#1R[#1R\#1R]#1R^#1R_#1R`#1Ra#1Rb#1Rc#1Rd#1Re#1Rf#1Rg#1Rh#1$02Ri'YRjf?Rkf>Rlf=Rmf<Rnf;Rof:Rpf9Rqf8RrG0g01;FRs,O2R2C3n0100000020000PEPFP@PJPFPjPkPlPmPnPoPpf7RJP3G0P2C3n01000000200003;P@1A=41A14%N8R8,8IRtP1PI%>IS03P4P8%>8RuEWP:CEPt1=43Rt1A3DRv':%<3Rw,98Rx%NCRC,8wRy':RzPtPvPxPyP4P8PuP3Pw%>wRyEQP3PwPyPDPC%>CS04EWEdP1CES05Pz%cJS06%<J,9sS07p-0Ryg01H_Rw#bRx%mwS081`;@S09%k;S0:%j;RvP;1K;8Rtg01=CS0;1_;9R{CI,?v1Uv>S0<5Tv&080R|Pv1S{t,?vP|1Uv=S0=CFCF207vAS0>P:P?g01JRR},]E206:?=;E}dB05;s@H03S0?b:b;b<X3;X2yW4198:/:@18@8P=[[^3;^2y^4yP:%<qR},OG,^HR~=;F~18}CP}P?P>O5b9b=b7b8W>P:O11=4=12jhS0@1GI8,MsS0AQ01#@#H#NR~'8PjQ0A1G@:,MsXL;X5;Q02PIP:XA;P1PIQ03H01PiP8PuF~PhP~%>~S02Ei1=41198IRjP4P8PuP1PIQ03EQP:CEPjQ05PzQ06Q07%<r/G8Rz,}s18sz1MszRj=;;z':19zsA;;js':'h1G}8,MsP;1X;M1X;L1X;K5g;5g;g01K2'|={wxQ08P;1`;?P@%z;CyQ0:PvPvP7P0P0PAQ0=P;P{g02:IRA1_;5R5=x;tCI,?v5Tv1Uv1P;P{PA1K;sS0=CI,?v5TvFwP|Pv1Uv31K;C,S5,?v5TvP|1K;~S07,S{,?vCFCFQ0>Q0?b:b;b<X3;X@;X2yX4yX?y1G@89;;:,:?A;;:s,:>'h18?C,:118?~[[^3;^@;^2y^4y^?yP:%<oR5,981G58RA/9s18sAP5P@P?P=O7b9bSbCb=b7b8CuQ0@12:hR5PBPFPFP@fDRAfCRtfBR0fAR7f@RwPkPlPmG0P2PFP@PAPtP0P7PwPkPnPoG0P2C3E4^05P@12KhPFPFPKPtP0P7PwPkPlPoPpG0P2D5W0%1:RK/2hR5PBPFPF%1@R}fGRjfFRzfERIPAPtP0P7PwG0P2PFP}PjPzPIPAPtP0PkPlG0P2C3E4^05P@12LhPFPFPLPzPIPAPtP0P7PlPmG0P2D5W0%1KRK/2hRmPBPFPF%1}RlfJRLfIR5fHRkPjPzPIPAPtG0P2PFPlPLP5PkPjPzPIP0P7G0P2C3E4^0mP@12MhPFPFPMP5PkPjPzPIPAP7PwG0P2D5W0%1KRK/2hRwPBPFPF%1lR7fMRMfLRmfKR0PLP5PkPjPzG0P2PFP7PMPmP0PLP5PkPIPAG0P2C3E4^0wP@12NhPFPFPNPmP0PLP5PkPjPAPtG0P2D5W0%1KRK/2hRtPBPFPF%17RAfPRNfORwfNRIPMPmP0PLP5G0P2PFPAPNPwPIPMPmP0PkPjG0P2C3E4^0tP@12OhPFPFPOPwPIPMPmP0PLPjPzG0P2D5W0%1KRK/2hRzPBPFPF%1ARjfSROfRRtfQRkPNPwPIPMPmG0P2PFPjPOPtPkPNPwPIP0PLG0P2C3E4^0zP@12PhPFPFPPPtPkPNPwPIPMPLP5G0P2D5W0%1KRK/2hR5PBPFPF%1jRLfVRPfURzfTR0POPtPkPNPwG0P2PFPLPPPzP0POPtPkPIPMG0P2C3E4^05P@12QhPFPFPQPzP0POPtPkPNPMPmG0P2D5W0%1KRK/2hRmPBPFPF%1LRMfYRQfXR5fWRIPPPzP0POPtG0P2PFPMPQP5PIPPPzP0PkPNG0P2C3E4^0mP@12RhPFPFPRP5PIPPPzP0POPNPwG0P2D5W0%1KRK/2hRwPBPFPF%1MRNf\RRf[RmfZRkPQP5PIPPPzG0P2PFPNPRPmPkPQP5PIP0POG0P2C3E4^0wP@12ShPFPFPSPmPkPQP5PIPPPOPtG0P2D5W0%1KRK/2hRtPBPFPF%1NROf_RSf^Rwf]R0PRPmPkPQP5G0P2PFPOPSPwP0PRPmPkPIPPG0P2C3E4^0tP@12ThPFPFPTPwP0PRPmPkPQPPPzG0P2D5W0%1KRK/2hRzPBPFPF%1ORPfbRTfaRtf`RIPSPwP0PRPmG0P2PFPPPTPtPIPSPwP0PkPQG0P2C3E4^0zP@12UhPFPFPUPtPIPSPwP0PRPQP5G0P2D5W0%1KRK/2hR5PBPFPF%1PRQfeRUfdRzfcRkPTPtPIPSPwG0P2PFPQPUPzPkPTPtPIP0PRG0P2C3E4^05P@12VhPFPFPVPzPkPTPtPIPSPRPmG0P2D5W0%1KRK/2hRmPBPFPF%1QRRfhRVfgR5ffR0PUPzPkPTPtG0P2PFPRPVP5P0PUPzPkPIPSG0P2C3E4^0mP@12WhPFPFPWP5P0PUPzPkPTPSPwG0P2D5W0%1KRK/2hRwPBPFPF%1RRSfkRWfjRmfiRIPVP5P0PUPzG0P2PFPSPWPmPIPVP5P0PkPTG0P2C3E4^0wP@12XhPFPFPXPmPIPVP5P0PUPTPtG0P2D5W0%1KRK/2hRtPBPFPF%1SRTfnRXfmRwflRkPWPmPIPVP5G0P2PFPTPXPwPkPWPmPIP0PUG0P2C3E4^0tP@12YhPFPFPYPwPkPWPmPIPVPUPzG0P2D5W0%1KRK/2hRzPBPFPF%1TRUfqRYfpRtfoR0PXPwPkPWPmG0P2PFPUPYPtP0PXPwPkPIPVG0P2C3E4^0zP@12ZhPFPFPZPtP0PXPwPkPWPVP5G0P2D5W0%1KRK/2hR5PBPFPF%1URVftRZfsRzfrRIPYPtP0PXPwG0P2PFPVPZPzPIPYPtP0PkPWG0P2C3E4^05P@12[hPFPFP[PzPIPYPtP0PXPWPmG0P2D5W0%1KRK/2hRmPBPFPF%1VRWfwR[fvR5fuRkPZPzPIPYPtG0P2PFPWP[P5PkPZPzPIP0PXG0P2C3E4^0mP@12\hPFPFP\P5PkPZPzPIPYPXPwG0P2D5W0%1KRK/2hRwPBPFPF%1WRXfzR\fyRmfxR0P[P5PkPZPzG0P2PFPXP\PmP0P[P5PkPIPYG0P2C3E4^0wP@12]hPFPFP]PmP0P[P5PkPZPYPtG0P2D5W0%1KRK/2hRtPBPFPF%1XRYf}R]f|Rwf{RIP\PmP0P[P5G0P2PFPYP]PwPIP\PmP0PkPZG0P2C3E4^0tP@12^hPFPFP^PwPIP\PmP0P[PZPzG0P2D5W0%1KRK/2hRzPBPFPF%1YRZp+01AR^p+01@Rtf~RkP]PwPIP\PmG0P2PFPZP^PtPkP]PwPIP0P[G0P2C3E4^0zP@12_hPFPFP_PtPkP]PwPIP\P[P5G0P2D5W0%1KRK/2hR5PBPFPF%1ZR[p+01DR_p+01CRzp+01BR0P^PtPkP]PwG0P2PFP[P_PzP0P^PtPkPIP\G0P2C3E4^05P@12`hPFPFP`PzP0P^PtPkP]P\PmG0P2D5W0%1KRK/2hRmPBPFPF%1[R\p+01GR`p+01FR5p+01ERIP_PzP0P^PtG0P2PFP\P`P5PIP_PzP0PkP]G0P2C3E4^0mP@12ahPFPFPaP5PIP_PzP0P^P]PwG0P2D5W0%1KRK/2hRwPBPFPF%1\R]p+01JRap+01IRmp+01HRkP`P5PIP_PzG0P2PFP]PaPmPkP`P5PIP0P^G0P2C3E4^0wP@12bhPFPFPbPmPkP`P5PIP_P^PtG0P2D5W0%1KRK/2hRtPBPFPF%1]R^p+01MRbp+01LRwp+01KR0PaPmPkP`P5G0P2PFP^PbPwP0PaPmPkPIP_G0P2C3E4^0tP@12chPFPFPcPwP0PaPmPkP`P_PzG0P2D5W0%1KRK/2hRzPBPFPF%1^R_p+01PRcp+01ORtp+01NRIPbPwP0PaPmG0P2PFP_PcPtPIPbPwP0PkP`G0P2C3E4^0zP@12dhPFPFPdPtPIPbPwP0PaP`P5G0P2D5W0%1KRK/2hR5PBPFPF%1_R`p+01SRdp+01RRzp+01QRkPcPtPIPbPwG0P2PFP`PdPzPkPcPtPIP0PaG0P2C3E4^05P@12ehPFPFPePzPkPcPtPIPbPaPmG0P2D5W0%1KRK/2hRmPBPFPF%1`Rap+01VRep+01UR5p+01TR0PdPzPkPcPtG0P2PFPaPeP5P0PdPzPkPIPbG0P2C3E4^0mP@12fhPFPFPfP5P0PdPzPkPcPbPwG0P2D5W0%1KRK/2hRbPBPFPF%1aRfp+01YS0@p+01XRmp+01WRIPeP5P0PdPzG0P2PFPfQ0@PmPIPeP5P0PkPcG0P2C3E4^0bP@12ghPFPFPgPmPIPeP5P0PdPcPtG0P2D5W0%1K/2h%1fRK/2h%V@Rt%N9R9'DP9P9P9P9D6P9P9P9P9D6P9P9P9P9D6P9P9P9P9D6P9P9P9P9D6P9P9P9P9D6P9P9P9P9D6/8~S06PK1D:9XA;RKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPKPtO1S05O1S03O1S0AO1S01O1S0BO1S0CO1S0DO1S0EO1S0FO1S0GO1S0HO1S0IO1S0JO1S0KO1S0LO1S0MO1S0NO1S0OO1S0PO1S0QO1S0RO1S0SO1RcO1RdO1R5O1ReO1RgO1RbO1PKPfPbPKPaPgPKP`PePKP_P5PKP^PdPKP]PcPKP\Q0SPKP[Q0RPKPZQ0QPKPYQ0PPKPXQ0OPKPWQ0NPKPVQ0MPKPUQ0LPKPTQ0KPKPSQ0JPKPRQ0IPKPQQ0HPKPPQ0GPKPOQ0FPKPNQ0EPKPMQ0DPKPLQ0CPKPjQ0BPKPAQ01PKP7Q0APKPlQ03PKP}Q05PKP@Pt%>tCsF7F7F7F7F7F7F7F7F7F7F7F7F7F7PhP~Q02EiP:CEQ061=4k%<kRh,98RtP4P8PuPkPh%>hEQPwCEPt1=4zRt1AzDRw':%<zRh,98RK18hCR}':RlPtPwPKP}P4P8PuPzPh%>hRuEQPzPhPuPDPCQ04EWEdPkCEPl%r=%V=,9s%c0%<0,9sPxQ08Q09Q0:PvP;Q0=Q0;P{CI,?vP|Pv1K;9Rx,v{PxPxPxPxDCPxPxPxPxDCPxPxPxPxDCPxPxPxPxDCPxPxPxPxDCPxPxPxPxDCPxPxPxPxDCQ07'S,?vP|Q0<CFCFQ0>Q0?b:b;b<X3;X2y19s:1D@9P9P9P9P9D6P9P9P9P9D6P9P9P9P9D6P9P9P9P9D6P9P9P9P9D6P9P9P9P9D6P9P9P9P9D6/8~P>[[^3;^2yP:PFPF%1J#B#B#B#B#B#B#BRyp+01`R~p+01_R9p+01^Rsp+01]R|p+01\Rvp+01[Rxp+01ZQ0@G0P2PFPyP~P9PsP|PvPxPmPIG0P2C3E4%VJP?P1O4b9bHb=b7b8bEW0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1B%\3/YiP:O2b0W>P:O1n200210100001021100011000bGbFPEPF1[:4R4%<:,OG,^HRHPF%\:/YiRiPnPoPpPqPrPJP3P1G0P2C3n0100000020000X5<Q00#L#a#bVBRB'f/P@PEPFP4PHPFPiPnPoPpPqPrPJP=P>G0P2C3n0100000020000X5</fB/P@5;FePoPpPqPrPJP3P1P=G0#e/P@PoPpPqPrPJP3P>P?G0#e/P@5;FeWDX5<XM;XR;XO;XQ;XN;XP;XK;XJ;WIWBX66P:O1X66P:O1W6o"). Qed.
Lemma Wx_sw {HCEIL : HeapCeil} : forall (H : asr) (e : xent H) ff fp p1 n1 p2 n2 q1 m1 q2 m2 n, (32 <= n < 59)%N ->
  ev (wenv (Wx H e ff fp p1 n1 p2 n2)) n = ev (wenv (Wx H e ff fp q1 m1 q2 m2)) n.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnXT ()) [] "p'0h01Kh11kh24__p1h34__x1h44__p2h51ni001nh65HCEILh73Hn0h82X0h97__arithh:4__ffh;8__varmaph<5__with=4cstrh>1Xh?4__p3h@4__x2hA1xhB1HhC2H3hD2HnhE2K0hF1bi011bhG2b0hH5cstr0hI1ehJ2ffhK2fphL1mhM2m1hN2m2hO2n1hP2n2hQ2p1hR2p2hS2q1hT2q2hU2z3p%0p&0p;1p;2p;3p;8p;4p;6p;7p;<p;Bg05J6k10;Tg0055j1@Tg005Zj1LTg036QR0j2ATg00V6j1BTg0365R1j2CTg00Ohj2:Tg035Sj2xTg036mj2XTg037JR2j3qTg0068j1aTg05K2j2mTg037nR3j1<Tg00`@j2OTg038Lj2^Tg039>R4j1\Tg013kR5j10Tg039^j2ZTg03EZj81Tg03:5j43Tg00`fj3;Tg00V[j1NTg00TZR6j28Tg03:Qj4HTg00X3R7j29Tg03ZYj6jTg05Kdj1cTg00<_j1bTg0045j1nTg00loj2`Tg00mMj1lTg00mkj1kTg00nVj2KTg00o9j2_Tg010?j4JTg010jk10:Tg011Lk209Tg00lUj2]Tg011nk208Tg012Zk307Tg0139k406Tg034>R8j22Tg01XXj2ITg03;]j2PTg03=:k201Tg00\9j2hTg014Jj2YTg0153j3fTg015\k200Tg00F5j3~Tg016Hj1}Tg019aj4|Tg02Ckj3{Tg02E7j7zTg02g`j4yTg00:<R9j1WTg009_j2=Tg03;8j1vTg03>Vj2eTg03?Mj2MTg00B>j1gTg02j9l<[Tg0185j7rTg01:bj6pTg018Yk702Tg019=k803Tg02iTl<QTg02hnlBoTg01:?j3ETf0R:#0#0#0#0p=Dg00GSR;/]:p=?g03A8R<P;P1P3P6g03BTf5R1f4R=f3R>f2R?f1R@P:M<[p=VP<P;P0P3P7g03E:P1P=P>P?P@P:M<[p=SP@g01;dR7g01<CR0P0g01<cRAP:g01=jFrp=>P@P7P0P0PAP:Epp=UP?P7P0P0PAP@P:K02p=TP;P@g01IKP:CJp=RP>P7P0P0PAP?P@P:L03p=GP<g00H1RBP;P;P4P3P9P>g03CVP?P@P:M<Qp>05PBPBPBP;P;P;g03D3P9P9P9f6R3g03DSP1P=P>P?P@P:MBop>04PBP;P8P9P6g03C4P1P=P>P?P@P:M<[p=iP=P>P?P@C3=;1:p=4P>P?P@P:C3,]=p=51=?@/=:p=d1==>/=?/=@/=:p=7PBPBP;P;P5P9P9P>g05LGR6P?P@P:M<Qp=wPBPBP;P;P5P9P9P3P6P1P=PBPBP;P;P5P9P9P>P6P?P@P:M<QM<Qp=6AE;@:p=uAE;?@=E;:p=tAE;=>=E;?=E;@=E;:p=F%0:#0p=sg00JDR6g00KC&0;:g00M5R9#@R5#@#@S00#@#@R8#LR4/A:%B9S01#B#@#B#BRC#LRD,C:':1x@41C@41A4@1X@43q1X?4g01J2REP21C>41A4>%@8#LR2#aRFPEPFP@%B5#LRG/mFRH%<1RI,OG'^RJPF%\1S02g00Q;RK#0RL#0RM#0RN#0RO#0RP#0RQ#0RR#0RS#0RT#0RU#0RV#0RW#0RX#0RY#0RZ#0R[#0R\#0R]#0R^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0#DRg'ZRhfARif@Rjf?Rkf>Rlf=Rmf<Rnf;Rof:RpG1g01;FRq,O2R2C3n0100000020000PEPFP@PJPFPhPiPjPkPlf9RJf8Rrf7RsP3G1P2C3n01000000200003;P@1C=41C14%N8R8,8IRtP1PI%?IS03P4P8%?8RuEVP:CHPt1A43Rt1C3DRv':%<3Rw,98Rx%NCRC,8wRy':RzPtPvPxPyP4P8PuP3Pw%?wRyESP3PwPyPDPC%?CS04EVEjP1CHS05Pz%csS06%<s,9qS07p-0Ryg01H_Rw#bRx%nwS081`;@S09%l;S0:%k;RvP;1K;8Rtg01=CS0;1_;9R{CJ,>v1Uv>S0<5Tv&0:0R|Pv1R{t,>vP|1Uv=S0=CGCG209vAS0>P:P?g01JRR},]E208:?=;E}dB07;q@H06S0?b:b;b<X3;X2yW4198:/:@18@8P=[[^3;^2y^4yP:%<JR},OG,^HR~=;F~18}CP}P?P>O5b9b=b7b8W>P:O11A4=12hfS0@1II8,PqS0AQ01#@#B#B#NR~'8PhQ0A1I@:,PqXL;X5;Q02PIP:XA;P1PIQ03H05PgP8PuK04PfP~%?~S02Ei1A41198IRhP4P8PuP1PIQ03ESP:CHPhQ05PzQ06Q07%<r/I8Rz-01q18qz1PqzRh=;;z':19zqA;;hq':'h1I}8,PqP;1Y;M1Y;L1Y;K5f;5f;g01K2+00=~wxQ08P;1`;?P@%};C|Q0:PvPvP7P0P0PAQ0=P;P{g02:IRA1_;5R5={;tCJ,>v5Tv1Uv1P;P{PA1K;qS0=CJ,>v5TvFzP|Pv1Uv31K;C,R5,>v5TvP|1K;~S07,R{,>vCGCGQ0>Q0?b:b;b<X3;X@;X2yX4yX?y1I@89;;:,:?A;;:q,:>'h18?C,:118?~[[^3;^@;^2y^4y^?yP:%<oR5,981I58RA/9q18qAP5P@P?P=O7b9bUbCb=b7b8CyQ0@12:fR5PBPFPFP@fFRAfERtfDR0fCR7fBRwPiPjPkG1P2PFP@PAPtP0P7PlPmPnPoG1P2C3E4^05P@12KfPFPFPKPtP0P7PwPmPnPoPpG1P2D5W0%0:RK/2fR5PBPFPF%0@R}fIRhfHRzfGRIPAPtP0P7PwG1P2PFP}PhPzPIPAPiPjPkPlG1P2C3E4^05P@12LfPFPFPLPzPIPAPtPjPkPlPmG1P2D5W0%0KS0@/2fS06PBQ06PFPF%0}RKfLRkfKRLfJR5PhPzPIPAPtG1P2PFPKPkPLP5PhP0P7PwPiG1P2C3E4]0P@12MfPFPFPMPLP5PhPzP7PwPiPjG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0KRjfORifNRwfMRMPkPLP5PhPzG1P2PFPjPiPwPMPkPIPAPtP0G1P2C3E4]0P@12NfPFPFPNPwPMPkPLPAPtP0P7G1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0jR7fRR0fQRtfPRNPiPwPMPkPLG1P2PFP7P0PtPNPiP5PhPzPIG1P2C3E4]0P@12OfPFPFPOPtPNPiPwPhPzPIPAG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%07RAfURIfTRzfSROP0PtPNPiPwG1P2PFPAPIPzPOP0PMPkPLP5G1P2C3E4]0P@12PfPFPFPPPzPOP0PtPkPLP5PhG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0ARhfXR5fWRLfVRPPIPzPOP0PtG1P2PFPhP5PLPPPIPNPiPwPMG1P2C3E4]0P@12QfPFPFPQPLPPPIPzPiPwPMPkG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0hRkf[RMfZRwfYRQP5PLPPPIPzG1P2PFPkPMPwPQP5POP0PtPNG1P2C3E4]0P@12RfPFPFPRPwPQP5PLP0PtPNPiG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0kRif^RNf]Rtf\RRPMPwPQP5PLG1P2PFPiPNPtPRPMPPPIPzPOG1P2C3E4]0P@12SfPFPFPSPtPRPMPwPIPzPOP0G1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0iR0faROf`Rzf_RSPNPtPRPMPwG1P2PFP0POPzPSPNPQP5PLPPG1P2C3E4]0P@12TfPFPFPTPzPSPNPtP5PLPPPIG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%00RIfdRPfcRLfbRTPOPzPSPNPtG1P2PFPIPPPLPTPOPRPMPwPQG1P2C3E4]0P@12UfPFPFPUPLPTPOPzPMPwPQP5G1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0IR5fgRQffRwfeRUPPPLPTPOPzG1P2PFP5PQPwPUPPPSPNPtPRG1P2C3E4]0P@12VfPFPFPVPwPUPPPLPNPtPRPMG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%05RMfjRRfiRtfhRVPQPwPUPPPLG1P2PFPMPRPtPVPQPTPOPzPSG1P2C3E4]0P@12WfPFPFPWPtPVPQPwPOPzPSPNG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0MRNfmRSflRzfkRWPRPtPVPQPwG1P2PFPNPSPzPWPRPUPPPLPTG1P2C3E4]0P@12XfPFPFPXPzPWPRPtPPPLPTPOG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0NROfpRTfoRLfnRXPSPzPWPRPtG1P2PFPOPTPLPXPSPVPQPwPUG1P2C3E4]0P@12YfPFPFPYPLPXPSPzPQPwPUPPG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0ORPfsRUfrRwfqRYPTPLPXPSPzG1P2PFPPPUPwPYPTPWPRPtPVG1P2C3E4]0P@12ZfPFPFPZPwPYPTPLPRPtPVPQG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0PRQfvRVfuRtftRZPUPwPYPTPLG1P2PFPQPVPtPZPUPXPSPzPWG1P2C3E4]0P@12[fPFPFP[PtPZPUPwPSPzPWPRG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0QRRfyRWfxRzfwR[PVPtPZPUPwG1P2PFPRPWPzP[PVPYPTPLPXG1P2C3E4]0P@12\fPFPFP\PzP[PVPtPTPLPXPSG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0RRSf|RXf{RLfzR\PWPzP[PVPtG1P2PFPSPXPLP\PWPZPUPwPYG1P2C3E4]0P@12]fPFPFP]PLP\PWPzPUPwPYPTG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0SRTp+01@RYf~Rwf}R]PXPLP\PWPzG1P2PFPTPYPwP]PXP[PVPtPZG1P2C3E4]0P@12^fPFPFP^PwP]PXPLPVPtPZPUG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0TRUp+01CRZp+01BRtp+01AR^PYPwP]PXPLG1P2PFPUPZPtP^PYP\PWPzP[G1P2C3E4]0P@12_fPFPFP_PtP^PYPwPWPzP[PVG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0URVp+01FR[p+01ERzp+01DR_PZPtP^PYPwG1P2PFPVP[PzP_PZP]PXPLP\G1P2C3E4]0P@12`fPFPFP`PzP_PZPtPXPLP\PWG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0VRWp+01IR\p+01HRLp+01GR`P[PzP_PZPtG1P2PFPWP\PLP`P[P^PYPwP]G1P2C3E4]0P@12afPFPFPaPLP`P[PzPYPwP]PXG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0WRXp+01LR]p+01KRwp+01JRaP\PLP`P[PzG1P2PFPXP]PwPaP\P_PZPtP^G1P2C3E4]0P@12bfPFPFPbPwPaP\PLPZPtP^PYG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0XRYp+01OR^p+01NRtp+01MRbP]PwPaP\PLG1P2PFPYP^PtPbP]P`P[PzP_G1P2C3E4]0P@12cfPFPFPcPtPbP]PwP[PzP_PZG1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0YRZp+01RR_p+01QRzp+01PRcP^PtPbP]PwG1P2PFPZP_PzPcP^PaP\PLP`G1P2C3E4]0P@12dfPFPFPdPzPcP^PtP\PLP`P[G1P2D5W0Q0@#0S0@/2fS06PBQ06PFPF%0ZR`p+01US05p+01TRLp+01SRdP_PzPcP^PtG1P2PFP`Q05PLPdP_PbP]PwPaG1P2C3E4]0P@12efPFPFPePLPdP_PzP]PwPaP\G1P2D5W0Q0@#0/2f%0`R\/2f%W@Ra%N9R9'=?d99P9P9P9P9D7P9P9P9P9D7P9P9P9P9D7P9P9P9P9D7P9P9P9P9D7P9P9P9P9D7/8~S0@P\1=:9XA;R\P\P\P\P\P\P\P\P\P\P\P\P\P\P\P\P\P\P\P\P\P\P\P\P\P\P\PaO1S06O1S03O1S0AO1S01O1S0BO1S0CO1S0DO1S0EO1S0FO1S0GO1S0HO1S0IO1S0JO1S0KO1S0LO1S0MO1S0NO1S0OO1S0PO1S0QO1S0RO1S0SO1ReO1RbO1R^O1RcO1P\P`PcP\PZP^P\PYPbP\PXPeP\PWQ0SP\PVQ0RP\PUQ0QP\PTQ0PP\PSQ0OP\PRQ0NP\PQQ0MP\PPQ0LP\POQ0KP\PNQ0JP\PMQ0IP\P5Q0HP\PIQ0GP\P0Q0FP\PiQ0EP\PkQ0DP\PhQ0CP\PAQ0BP\P7Q01P\PjQ0AP\PKQ03P\P}Q06P\P@Pa%?aCwF6F6F6F6F6F6F6F6F6F6F6F6F6PfP~Q02EiP:CHQ0@1A4w%<wRf,98RaP4P8PuPwPf%?fESP[CHPa1A4]Ra1C]DR[':%<]Rf,98R\18fCR}':RKPaP[P\P}P4P8PuP]Pf%?fRuESP]PfPuPDPCQ04EVEjPwCHPK%v=%W=,9q%ct%<t,9qPxQ08Q09Q0:PvP;Q0=Q0;P{CJ,>vP|Pv1K;9Rx,u{?txxPxPxPxPxDFPxPxPxPxDFPxPxPxPxDFPxPxPxPxDFPxPxPxPxDFPxPxPxPxDFQ07'R,>vP|Q0<CGCGQ0>Q0?b:b;b<X3;X2y19q:1=@9?d99P9P9P9P9D7P9P9P9P9D7P9P9P9P9D7P9P9P9P9D7P9P9P9P9D7P9P9P9P9D7/8~P>[[^3;^2yP:PFPF%0s#s#D#D#D#D#D#DRyp+01\R~p+01[R9p+01ZRqp+01YR|p+01Xp+01Wp+01VQ05G1P2PFPyP~P9PqP|PLPdP_PzG1P2C3E4%WsP?P1O4b9bHb=b7b8bEW0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110001020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1BP:O1n0110000020011100P:O1W0X1B%\3/ZgP:O2b0W>P:O1n200210100001021100011000bGbFPEPF1X:4R4%<:,OG,^HRHPF%\:/ZgRgPlPmPnPoPpPJPrPsG1P2C3n0100000020000X5<Q00#L#a#bVBRB'e/M@PEPFP4PHPFPgPlPmPnPoP3P1P=P>G1P2C3n0100000020000X5</eB/M@5;FePmPnPoPpPJPrPsP3G1#g/M@PmPnPoPpP1P=P>P?G1#g/M@5;FeWDX5<XN;XT;XM;XS;XP;XR;XO;XQ;XK;XJ;WIWBX66P:O1X66P:O1W6o"). Qed.
