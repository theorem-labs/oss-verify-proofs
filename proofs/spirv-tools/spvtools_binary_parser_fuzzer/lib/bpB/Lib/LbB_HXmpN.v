(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3 Hoare RefMemcpyLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HRehStmt LbB_HKit LbB_VecT LbB_HXmpS LbB_HEmpK LbB_HXmpD LbB_HXmpI LbB_HXmpI2
  LbB_HXmpI3 LbB_HXmpI4 LbB_HXmpX LbB_HXmpR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_HNextPrime.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_HXmpN () := "C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockI46Stdlib7Sorting;Permutation;Permutation00C46Stdlib5Lists4List8nil_consC46Stdlib7Sorting;Permutation>Permutation_inC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes6option01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7ro_addrC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission3bpB2Rt<BakeStackRepBfind_segment_asegsC56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00C47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic9False_indK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib>LbB_HNextPrime7RO_LO_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib>LbB_HNextPrime7RO_HI_AI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C4ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_bothbTgt_spvtools_binary_parser_fuzzer_both_segment_000C4ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_bothbTgt_spvtools_binary_parser_fuzzer_both_segment_001C4ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_bothbTgt_spvtools_binary_parser_fuzzer_both_segment_002C4ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_bothbTgt_spvtools_binary_parser_fuzzer_both_segment_003I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC46Stdlib5Lists4List2InC47Corelib4Init5Logic3notK45stdpp9bitvector;definitions2bv01C4ARocqVerifyHarness?AgentSubmission8PropExec4getrC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6np_argC4ARocqVerifyHarness?AgentSubmission5Hoare6ret_okC56Stdlib6ZArith6BinInt1Z6moduloC4ARocqVerifyHarness?AgentSubmission8LibIface:stack_roomC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_MPRESK47Corelib4Init9Datatypes3nat02C4ARocqVerifyHarness?AgentSubmission<RefMemcpyLib8keeps_csC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRK4ARocqVerifyHarness?AgentSubmission8PropExec7FPState01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpNBro_none_of_mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib>LbB_HNextPrimeAnext_prime_spec_AC4ARocqVerifyHarness?AgentSubmission8PropExec7seg_romC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstI4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00I47Corelib4Init5Logic2ex00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge;msteps_fullC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKit5sr_msC56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC4ARocqVerifyHarness?AgentSubmission7CatExec6wbytesC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9bseq_nextI4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ARocqVerifyHarness?AgentSubmission8LibIface3memC6ARocqVerifyHarness?AgentSubmission3bpB3Lib>LbB_HNextPrime4NP_AC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4BSEQC6ARocqVerifyHarness?AgentSubmission3bpB3Lib>LbB_HNextPrime;BSEQ_LAST_AK47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsI47Corelib4Init9Datatypes4prod00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpR4GPREC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD3spfI47Corelib5Lists7ListDef6Forall00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD5FRAMEK47Corelib7Numbers7BinNums1Z03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt>map_live_frameC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6nval24K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7ZlengthI47Corelib4Init5Logic2or00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_sizeC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep;umap_blocksC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5apartC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_ALC56Stdlib6ZArith6BinInt1Z3mulC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface6nsmallC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface3nlgC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface3ICMC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_TRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt:emp_del_raK47Corelib4Init9Datatypes4list02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8trace_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB3lblK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;as_rauxv_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_RHEAPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own6lb_ownC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep5xpresC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_RFSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack06stack0C56Stdlib6ZArith6BinInt1Z2geC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface8lb_smallC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface6nlargeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap6ah_fsbC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7afsb_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD9obj_placeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<afs_write_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9aconst_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack09stack0_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface@aclient_write_okC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap?stack_window_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01C46Stdlib5Lists4List;Forall_implC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpI2<dj_of_forallC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=disjoint_fromC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3nshC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;sh_nsh_highC56Stdlib6ZArith6BinInt1Z6of_natC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<client_frameC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_hiC56Stdlib6ZArith6BinInt1Z3divC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeK47Corelib4Init5Logic2or02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrameBrw_cells_transportC56Stdlib6ZArith6BinInt1Z7pos_subC57Corelib7BinNums6PosDef3Pos3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib7Sorting;Permutation?Permutation_symC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB:lbl_in_invC46Stdlib5Lists4List9in_or_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap9ah_blocksC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ablock_rangeC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9umap_footC47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:in_app_iffC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib5Lists4List:in_map_iffK47Corelib4Init5Logic2ex01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame7outsideC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpI2=out_of_forallC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts<nval24_agreeC4ARocqVerifyHarness?AgentSubmission8LibIface4liveC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts;umapx_agreeC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3bC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3aC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3cK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadowEaddressable_transportC47Corelib4Init9Datatypes3sndC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own;wr_at_wmonoC47Corelib4Init3Nat3addC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own<lb_own_wmonoC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep7rin_ivsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep>xpres_of_munchC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep<xpres_weakenC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep;xpres_transC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack0@stack0_transportC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkI5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5umapx00K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC47Corelib4Init9Datatypes6lengthC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt7umap_shK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4AC_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4LY_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4MI_AI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<RT_LARGE_MAXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<RT_SMALL_MAXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface:RT_CNT_MAXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPK46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3ATPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HRehStmt:AREH_STACKC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts9BSEQ_LASTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface9APC0_FREEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt7EMP_EXTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8AFS_SIZEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEC46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201C46Stdlib5Lists4List8map_consC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3mrdC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem>wr_at_store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD4rSheC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRC4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpI2QIC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HFind;BSEQ_boundAC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge9rfull_mkRC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call=regs_keep_mkRC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7mod_addc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpNAstack_room_of_stkC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge8rfull_eqC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC35stdpp7tactics<f_equal_helpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv9wbytes_eqC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame:munch_reflC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame6insideC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses8or_morphC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame;munch_writeC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame:wmono_reflC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame;wmono_writeC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem=mem_inv_storeC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame9stk_writeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>ah_mpres_transK47Corelib5Lists7ListDef6Forall02c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpN:gpre_stackC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpR;stage_rcallC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT9sr_blk_eqc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpN5np_srC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_bseqC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotI5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpN4E_NPI5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00K47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpR4E_RCc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpN5E_NPR".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_NP : Z := 0xfba5c.
Definition E_NPR : Z := 0xfbd8c.
Definition nreq (bc : Z) : Z := if Z.eqb bc 0 then 1 else np_arg bc.
Definition srNP0 : list expr := srs sr_id [(2%bv, EVar 34); (8%bv, EVar 32); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (11%bv, ELit 1)].
Definition srNP1 : list expr := srs sr_id [(2%bv, EVar 34); (8%bv, EVar 32); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (11%bv, EVar 33)].
Definition KNP : list kentry :=
  [KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit SHBASE);
   KWr (SA (EVar 34) (-32)) (ELit 32); KRange (EVar 34) (2 ^ 45) (2 ^ 47)].
Definition tlNP : list expr := [EVar 18; EAlu ALU_ADD (EVar 32) (ELit 8); EVar 32; ELit E_IDX].
Definition lgNP : list sentry := Eval cbv in c8log (EVar 34) (-32) tlNP.
Lemma lgNP_c8 : lgNP = c8log (EVar 34) (-32) tlNP.
Proof. reflexivity. Qed.

Lemma ro_none_of_mem_inv : forall m, mem_inv asegs m ->
  forall i, LbB_HNextPrime.RO_LO_A <= i < LbB_HNextPrime.RO_HI_A -> m (Z_to_bv 64 i) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HXmpN ()) [] "p'0h02ROh14__x1h24__p1h32b0h42b1h51Eh62H0h72H2h87__arithh94__ffh:4__p2h;8__varmaph<5__with=2H1h>1Hh?2Hah@6__sat1hA1oi001ohB2H3hC2HihD2MIhE6__sat0hF1bi011bhG1ehH1ihI1mhJ1zi023segi031xp;1p;2p;3p;4p;6p;7p;8p10000p4p70R0p1000ip4p710p8P0p1001Tp4p710p8P0p10021p4p710p8p1002]p4p7210R0g003IR1p4p710p8P0p1003ep4p710p8g004Cj13Tg004hj1PTg005Fj1OTg005iR0j1STg006Kj2dTg007Gj22Tg007cj21Tg008?j2CTg008Zj2;Tg009@j2ETg009Zj3:Tg00:4j1JTg00:Vj2@Tg00;8j2mTg00<4j2cTg00<^j19Tg00=<j3MTg00>@j1`Tg00?Bj1^Tg00?`j2]Tg00@Hj2\Tg00@ej3[Tg00AIj2ZTg00Ajj1YTg00BJj1XTg00Bjj2WTg00CHj1VTg00Cfj1UTg00DQj2?Tg00E4j2TTg00EWj4LTg00FBj1=Tg00Fgj3nTg00GJj2lTg00Glj2kTg00HXj3jTg00I7j4fTg00Iij2eTP1j6NTg00Jcj24Tg00K@j1bTg00LKj2FTg00Lmj27Tg00MJR1j3GTg00Mnj26Tg00NLj2QTg00Nkj3aTg00ONj7_Tg00P2j7gTg00PVj8hTg00Q:j6iTf0R2#3#3p=Hg00Q^R3g00R>R47:2p=0%32#3#3#3#3#3#3#3p=Bf1R5g00R^R6g00S=R7P7g00S]R8P2g00T=F_p=8%=2#=p=K%=2#3p=>%32#3#3#3p=Dg00T]R9P5g00U;P2CLp=Af2R:P6P7P7P8P5P2Fgp=If3R;P6P7P7P8P:P5P2Ghp=<17;:1752'6p=5P5P6P7P7P8P2Eip=Rg00UbR6#3R<#3R=#3R>#3#HR?#PR@#O%P>#OR>#SRA[g00VGRB/d2g00W>/22g00XA,12'CP;1;@5O1PA1EA2f4RC1;@:O1=:A2P0P>f6RD1;@CO1=:A2%J>RE9:A5]5P5f7RFf5RG,;@O11@>25:A1@>5=:AEPF1;@DRDP5P2O31mBD#0P91;@F,c@P0g00YDRDP3%96RH9MB2%`2#^RIP4n10110300021010200#0XJ9P2PF%9<R<%9?RJ']g00ZCRK/1<RL12KJ1\<JRM,1K[RN[12K<ROg00ZaRPA[<J5UW?12KM\P^?OP5g00[=1ZK<'EPLeO1PNg00[cRN#YRL%XNRN1W95RO%V9RJ%U9RQP9%H?#B#9R?,?9RRg00\ORS1T96RTCL,8QRU%36#=#K#K#>#D#B#9RV,?9RW,AT,8QRX5IQ%J7R7P91?9KPSPTCL,8Q1?9<=n9@,AT,8Q5IQC<1lQ8R8P2P:g00]6R<,E31k2:=:3<dAj9K5CfRSb9b;b<X1912?2112V'C12K5115M'C[^19P2f;RMf:RKO2b8b@bEb@,eFENP0PDP3AMBFHPIP4n10110300021010200#0%SDRYf8RZ=MBHP0PDP3P2PIP4n10110300021010200#0XAYP2P3PYP?PZ14ZHRB%>=#H#=#D#B#9R=C5g00]V,@DR[P3PYP=PZPBPVC5g00_U,@DR\P3PYPVPZPB%=6#D#=#>#D#B#9R]C5g00aT,@DR^P3PYP]PZPB%>6#K#>#>#H#D#B#9R6C5g00cS,@DRB%JDR_n0100000020000n0100000020000n0100000020000n0100000020001R`%bZENP0PDP3P`PIP4n10110300021010200#0f9R`,F?12?`11`?17?`3G17?KP3P112?M11M?P0PDP3P3PYf=RM/4HRK/7=R`,65P[P3PYP=PMPKPVC5P\P3PYPVPMPKP]C5P^P3PYP]PMPKP6C5PBP_n0100000020000n0100000020000n0100000020000RKn0100000020001PIP4n10110300021010200#0g00eRRM]0P5f<RZ,2?P0PDP3P3PY16<`P[PKn0100000020001PIP4n10110300021010200#0f>/4HRa/F=Rb12a=11=a17a=3GRaf?/4H/7=RcP3P1f@/4HRd/2=Re11=dRdP0PDP3P3PY16<5RfP[P3PYP=fBRg14gHRhPVC5P\P3PYPVPgPhP]C5P^P3PYP]PgPhP6C5PBP_n0100000020000n0100000020000n0100000020000Rhn0100000020001PIP4n10110300021010200#0PM]0P5fA/4HRg/2=RiP0PDP3P3PY16<<RjP[Phn0100000020001PIP4n10110300021010200#0P3P<P3p-0RkP2PPPMn0110100020000XG3g00eoP4P2ENRPPM1QM2Rlb=W0W6P2O111=gRgP0PDP3P3PY16<4RmP[Phn0100000020001PIP4n10110300021010200#0fCRn,F=12=n11n=17=n3GfDRo,7=P3P1fERp,2=11p=P0PDP3P3PYfGRp/4HRq/7VRr,65P\P3PYPVPpPqP]C5P^P3PYP]PpPqP6C5PBP_n0100000020000n0100000020000Rqn0100000020000PIP4n10110300021010200#0PM]0P5fFRp,2=P0PDP3P3PY16<rP\Pqn0100000020000PIP4n10110300021010200#0fH/4HRs/FVRt12sV11Vs17sV3GRsfI/4H/7VRuP3P1fJ/4HRv/2VRw11VvRvP0PDP3P3PYPfP\P3PYPVfLRf14fHRxP]C5P^P3PYP]PfPxP6C5PBP_n0100000020000n0100000020000R_n0100000020000PIP4n10110300021010200#0PM]0P5fK/4HRB/2VR6P0PDP3P3PYPjP\P_n0100000020000PIP4n10110300021010200#0PPPMPlbBW0W7P2O111VBRBP0PDP3P3PYPmP\P_n0100000020000PIP4n10110300021010200#0PLPNPOPJPQ1?9H9a9TRm,AW,8QP7PQ1RQ;RW=IQXP71RQCRXC<C<P8PSb9b;b<X19X2kX:k142H,1V115V,C:PC[[^19^2k^:kP2PMfNRl,2?PlP:fMO5b8W0W7P2O1n200210100000021100011000P:O1b4b3W0W=P2O111p=P0PDP3P3PY164rP\Pqn0100000020000PIP4n10110300021010200#0PtPsPuP3P1PwPvP0PDP3P3PY1645RvP\P_n0100000020000PIP4n10110300021010200#0PM]0P5P0PDP3P3PY164<R<P\P_n0100000020000PIP4n10110300021010200#0PLPNPOPJPQ1?9=Rw,AT,8QP7PQ1Awm,8QP7PWC<C<P8PSb9b;b<X19X2k112=145H,1=P;[[^19^2kP2PMPlPFPZO4b8RlW0X76P2O1P0PDP3P3PY1644R6P\P_n0100000020000PIP4n10110300021010200#0PlW0X7BP2O1n200210100000021100011000P:O1b4b3W0W=P2O1n200210100000021100011000P:O1b4b3W0W6P2O1n200210100001021100011000P:O1b4b3W0W>P2O111Z?P0PDP3P3PY164`P[PKn0100000020001PIP4n10110300021010200#0PbPaPcP3P1PePdP0PDP3P3PYPvP[Phn0100000020001PIP4n10110300021010200#0PM]0P5P0PDP3P3PYP<P[Phn0100000020001PIP4n10110300021010200#0PLPNPOPJPQ1ATR,8QP7PQAIQUWP7PXC<C<P8PSb9b;b<X19X2kX:k112?12?5/C:PC[[^19^2k^:kP2PM11oVPoPFPnO5b8RnW0X6iP2O1P0PDP3P3PYP6P[Phn0100000020001PIP4n10110300021010200#0PnW0X6gP2O1n200210100001021100011000P:O1b4b3W0W>P2O1n200210100001021100011000P:O1b4b3b0b0b0'QW5XF>P2O1PG1;@;O1=:AE1EAEW5n10110000021110100P2O1b5bAWCXH9WDWIo"). Qed.

Section NP.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma np_sr : forall (Q : config -> Prop) (s : as_St H) (msF : machine_state) (mo : Model) (R : bvmap 5 word) (F : bvmap 5 word)
      (fc : bv 32) (m : mem) (bc sp : Z) (ret : word),
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 LbB_HNextPrime.NP_A) fc None m (seg_rom asegs) ->
    In bc BSEQ -> bc <> 0 -> bc <> LbB_HNextPrime.BSEQ_LAST_A ->
    getr R 10%bv = Z_to_bv 64 (np_arg bc) -> getr R 1%bv = ret -> ret_ok ret -> getr R 2%bv = Z_to_bv 64 sp ->
    sp mod 16 = 0 -> 2 ^ 24 <= sp -> sp <= 2 ^ 47 -> stack_room asegs m sp 16 -> mem_inv asegs m -> rfull R ->
    (forall msF' mo' R', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       as_VIS H s msF' = MS R' F ret fc None (CatExec.wbytes m (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ret)) (seg_rom asegs) ->
       kept R R' -> getr R' 10%bv = Z_to_bv 64 (bseq_next bc) -> rfull R' -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HXmpN ()) ["NP"] "p'0h02R'h12H0h23mo'h34msF'h41Fh52FRh63FR'h73G10h82H1h93H10h:2H2h;3Hinh<3Hmsh=3Hn0h>3Hnlh?4Hreth@1KhA4KEPThB2KRhC3KR'hD2MIhE3MP'hF1QhG1RhH4ROOMhI4SP16hJ3SPHhK3SPLhL3VIShM4VIS'hN2bchO1ehP2fchQ1mhR2mohS3msFhT3rethU1shV2spi001xp;1p;2p;3p;7p;4p;Bp;5p;=g00fKj1`Tg004Cj11Tg00FBj1=Tg004hj1@Tg005Fj1KTg002]j2VTg00gDj2;Tg00h9j3BTg00i5j3ATg008Zj2?Tg00:4j1NTg00ioj1MTg00k1j7ETg009Zj33Tg00kkj3]Tg00lBj1JTg00<^j1:Tg00l[j3DTg00m>j26Tg00n0j1UTg00nhj1TTg00oYj2STg00@Hj2HTg007Gj2GTg0109j4RTg006Kj2QTg0111j1CTg011nj3FTg012jj14Tg013Ij28Tg014Cj3>Tg015<j22Tg0163j2OTg017<lBPTg018Ij1LTg019>j50Tg01:0j3<Tg008?R0j29Tg01:dR1j2_Tg01;>j5^Tg01<Aj1\Tg01=@l=YTg01>;j2XTg01>Xj2WTg01?`j3ZTg01@Sj1[Tf3R2f2R3f1R4f0R5'?33p=If5R6f4R71X23'?1W453Zp=5%[5,?49323p=7g01ANp-0[p,1HR8#`g01BCR9g01CJR:g00UbR;#1R<#=R=#@R>%1<#1R?#1R@#1RA#1#@RB#KRC'VRD%@A#Kg01D@g00T]RAf9REf8RFf7RG';RH5B8f:RI=A8EPGf6RJg01E1,?BRKP6%NCRLP7g00VGRM#MRNFE539g01F19]A7g00ZCRO93A6#Jg01Fg93AJ#JPCf;RP%1=#:g00eoRQ5D>RR'6PB%UGCIf<RS%:;=D>Q'6=3CJ%TGPCf>RT%:<R<=D>Q'6PBPECI%:@R@,SI=3AO%=;#1#1#1#:,H</GP%==#=#=#:,H<,GSPMf?R<f=R=P@CRf@R@,QMfDR;#CfKRO1;345B8fJRQ=F83fMR>=A87P3fIRUP;fHRVPLfGRWPBfERX%:?R?g01Gn#4#4#4#4#4#4#4#4RYP;E5RZPNFE53918O2PC167RR[PBPVC7%C6fRR\=>8H[[[[[[^0D^2:^3912X;fFRHfCR]fBR^fAR_P@P=PSPPPIPEPFPGPJP6P7P21O]3MBPg01HMRP12HXRSPWPKP;%LPR=D0PSP5P_P;PBP^P?PYP_E5P=D03<18W5PC165RR_PBP]C7'9'9X0D,_DP1PD12WHR1PVPKPXP=D0P1P5P^PXPBP]P?PYP^E5P=D05<P18V5PCP_PBP;C7'9'9X0DfLR^1;QU5>8P512UVR1PQPKPWP=D0P1P5P;PZP=D05<P18Q5PCP_PBPHC7'9'9P012QURUPOPKPVP=D0PUP4PXPVPBPHP?PYPXE5P=D05<P18O4PC164RPBPWC7'9fPRXfNRH/;>5>8P512^ORUP>PKPQP=D0PUP2PWPQPBPVP?PYPWE5P=D05<P18H7PCP[PBPQC7'9P0fOR0/86PC166RPBPOC7fTROfQRQ,;\5>8P518QGPC16FRPBPHC7PM12\QRMfSRRPKPXP=D0PMPEP>PXPBPHP?PYP>E5P=D0RXP6PTD^%\X#Cp,5HCEILP8p,2HHfXRXfWREfVRMfURFPOPRPKP\PLPQPNFE12R\PIPHPQPBP0P?PYPHE5P=D0P>P^PJfY1;455B8AF8X4f[=A8212EMPTP\PFPBPRP?PYP\E5P=D0539P]P7P2P<P3P4P5PGPJP6O9WMWEWCX2:X39M=Yb6W7WAP4P5O2n2001000000121000000W1W<P4P5O2n2001000000121000000W1X0DP4P5O2n2001000000121100000bOW@W5WDWHWJWKWIW:W?W8W9W>W=W;WLWBXTCXVAWNWQWPX4DWGWRWSWUWFo"). Qed.
End NP.

Section EmpN.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis REH : reh_stmt H EMP_EXT.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spz : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc key : Z) (ents : list (Z * (Z * Z))).
  Variables (lo B shi : Z) (m0 : mem) (mo0 : Model).

  Abbreviation GPREx := (GPRE H ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).
  Abbreviation QIx := (QI H ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).

  Lemma gpre_stack : forall s mo m m1 errv' LB' LBm p (W : list (Z * Z)),
    GPREx s mo m errv' LB' LBm p ->
    munch W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo spz ->
    Forall (fun iv => aceil <= fst iv /\ snd iv <= spf spz /\ fst iv <= snd iv) W ->
    GPREx s mo m1 errv' LB' LBm p.
  Proof.
    intros s mo m m1 errv' LB' LBm p W GP MU WM MI1 ST1 FW.
    destruct GP as (MP & FR & SP16 & SPL & SPH & RAE & MI & ST & ERR & RA & TPV & ACS & ACL & LOR & SHI & SPB & BR & LFO & OCE
                    & U & SH & GROW & BCL & SZR & KR32 & AD & WR & OBL & P0 & P1 & P16 & PO & PA & NC & ADP
                    & RH & PE & PM & OWN & XP & RF & AC & S0 & AL & AL0 & RS & RC & RL & RICM & TRK).
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    pose proof (obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    unfold spf in *.
    assert (FWK : Forall (fun iv => aclient_write_ok H LB' iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] (X1 & X2 & X3). cbn [Datatypes.fst Datatypes.snd] in *.
      destruct (stack_window_ok H LB' LF l h X1 ltac:(unfold AFS_SIZE in *; lia)) as (W1 & W2 & W3).
      split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. left. cbn. unfold AHI_LO. lia. }
    assert (F1 : Forall (aclient_write_ok H LB') W) by (eapply Forall_impl; [|exact FWK]; intros iv X; exact (proj1 X)).
    assert (F2 : Forall (afs_write_ok H LF) W) by (eapply Forall_impl; [|exact FWK]; intros iv X; exact (proj1 (proj2 X))).
    assert (F3 : Forall aconst_ok W) by (eapply Forall_impl; [|exact FWK]; intros iv X; exact (proj1 (proj2 (proj2 X)))).
    assert (F4 : Forall stack0_ok W) by (eapply Forall_impl; [|exact FWK]; intros iv X; exact (proj2 (proj2 (proj2 X)))).
    assert (FDJ : forall a k, a + k <= aceil \/ spz - 96 <= a -> disjoint_from W a k).
    { intros a k Hc. apply LbB_HXmpI2.dj_of_forall. eapply Forall_impl; [|exact FW]. intros iv (X1 & X2 & X3). lia. }
    assert (FSH : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from W (sh A) (nsh k)).
    { intros A k HA Hk Hak. apply LbB_HXmpI2.dj_of_forall. eapply Forall_impl; [|exact FW]. intros iv (X1 & X2 & X3).
      pose proof (sh_nsh_high A k HA Hk ltac:(unfold AAPP_HI; lia)) as SN. unfold AHI_LO in SN. lia. }
    destruct (client_frame H HH s LB' LF B W m m1 RH RF AC RA MU WM F1 F2 F3) as (RH1 & RF1 & AC1 & RA1).
    unfold GPRE.
    split; [exact MP|].
    split; [unfold FRAME, spf in FR |- *; eapply rw_cells_transport; [exact FR | exact MU | exact WM | apply FDJ; right; lia]|].
    split; [exact SP16|]. split; [exact SPL|]. split; [exact SPH|]. split; [exact RAE|].
    split; [exact MI1|]. split; [exact ST1|].
    split. { rewrite TPV in ERR |- *. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
             eapply rw_cells_transport; [exact ERR | exact MU | exact WM | apply FDJ; left; cbn; unfold ATP; lia]. }
    split; [exact RA1|].
    split; [exact TPV|]. split; [exact ACS|]. split; [exact ACL|]. split; [exact LOR|]. split; [exact SHI|].
    split; [exact SPB|]. split; [exact BR|]. split; [exact LFO|]. split; [exact OCE|].

    assert (BLK : forall q k, In (q, k) (umap_blocks 24 bl bc ents) -> 0 < q /\ q + k <= aceil /\ 0 <= k /\ aapp q k).
    { intros q k Hq. destruct (lbl_in_inv LBm q k (Permutation_in _ (Permutation_sym PM) (or_intror Hq))) as (qi & Qi).
      assert (QiL : In (qi, q, k) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact Qi).
      pose proof (ah_blocks H HH _ _ _ _ RH QiL) as (B0 & _ & Bn & _ & BC & _ & BA).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, Bn, BC, BA. split; [lia|]. split; [lia|]. split; [lia | exact BA]. }
    assert (FPA : forall a, umap_foot 24 obj bl bc ents a -> 0 <= a < aceil).
    { intros a [Ha | [[Hbc Ha] | (q & Hq & Hqa)]].
      - lia.
      - assert (IB : In (bl, 8 * bc) (umap_blocks 24 bl bc ents))
          by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc 0); [lia | left; reflexivity]).
        destruct (BLK _ _ IB) as (B0 & BC & _). lia.
      - apply in_map_iff in Hq. destruct Hq as ([z [k v]] & Hz & Hin). cbn in Hz. subst z.
        assert (IB : In (q, 24) (umap_blocks 24 bl bc ents))
          by (unfold umap_blocks; apply in_app_iff; right; apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin]).
        destruct (BLK _ _ IB) as (B0 & BC & _). lia. }
    assert (OUT : forall a, 0 <= a < aceil -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha. apply MU. rewrite u64_of_Z by lia. apply LbB_HXmpI2.out_of_forall. eapply Forall_impl; [|exact FW]. intros iv (X1 & X2 & X3). lia. }
    split; [eapply (umapx_agree ASEGS LY_A MI_A 24 _ (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia) (lbl LB') (lbl LB') m m1);
              [exact U | intros a Ha; exact (OUT a (FPA a Ha)) | intros; assumption]|].
    split.
    { destruct SH as [SHb SHn]. unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c in *. cbn [Datatypes.fst Datatypes.snd] in *. split.
      - intros Hbc. assert (IB : In (bl, 8 * bc) (umap_blocks 24 bl bc ents))
          by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc 0); [lia | left; reflexivity]).
        destruct (BLK _ _ IB) as (B0 & BC & Bn & _).
        eapply addressable_transport; [exact (SHb Hbc) | exact MU | exact WM | apply FSH; lia].
      - intros q k v Hin. assert (IB : In (q, 24) (umap_blocks 24 bl bc ents))
          by (unfold umap_blocks; apply in_app_iff; right; apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin]).
        destruct (BLK _ _ IB) as (B0 & BC & Bn & _).
        eapply addressable_transport; [exact (SHn q k v Hin) | exact MU | exact WM | apply FSH; lia]. }
    split; [exact GROW|]. split; [exact BCL|]. split; [exact SZR|]. split; [exact KR32|].
    split; [eapply addressable_transport; [exact AD | exact MU | exact WM | apply FSH; lia]|].
    split; [exact (wr_at_wmono _ _ _ _ WR WM)|].
    split; [exact OBL|].
    split; [exact P0|]. split; [exact P1|]. split; [exact P16|]. split; [exact PO|]. split; [exact PA|].
    destruct (lbl_in_inv LBm p 24 (Permutation_in _ (Permutation_sym PM) (or_introl eq_refl))) as (qp & QPm).
    assert (QPL : In (qp, p, 24) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact QPm).
    pose proof (ah_blocks H HH _ _ _ _ RH QPL) as (_ & _ & _ & _ & PCE & _ & _). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in PCE.
    split; [eapply rw_cells_transport; [exact NC | exact MU | exact WM | apply FDJ; left; cbn [cells_size csize Z.of_nat]; lia]|].
    split; [eapply addressable_transport; [exact ADP | exact MU | exact WM | apply FSH; lia]|].
    split; [exact RH1|]. split; [exact PE|]. split; [exact PM|].
    split; [exact (lb_own_wmono _ _ _ OWN WM)|].
    split.
    { eapply xpres_trans; [exact XP|]. eapply (xpres_weaken H).
      - eapply (xpres_of_munch H s LB' spz [(obj, obj + 40)] W m m m1 HH RH MU WM).
        eapply Forall_impl; [|exact FW]; intros iv (X1 & X2 & X3); left; lia.
      - lia.
      - intros b Hb. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. left. exact Hb.
      - intros a Ha. exact Ha. }
    split; [exact RF1|]. split; [exact AC1|]. split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact F4]|].
    split; [exact AL|]. split; [exact AL0|]. split; [exact RS|]. split; [exact RC|]. split; [exact RL|]. split; [exact RICM|].
    exact TRK.
  Qed.

  Lemma stack_room_of_stk : forall m sp S, stk asegs m lo spz -> lo <= sp - S -> sp <= spz -> 0 <= S -> stack_room asegs m sp S.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HXmpN ()) ["EmpN"] "h04__x1h17__sat13h24__x2h34__x3h47__arithh54__ffh68__varmaph75__with87__sat12h91bh:1ah;1xh<2H0h=2Hah>2SOh?4__p1h@4__p2hA7__sat14hB4__x4hC4__x5hD1ihE1mhF2H1hG3H12hH2H2hI2H3hJ2HihK1ShL2S1hM2S2hN2S3hO1WhP1nhQ2sphR1yhS1zhT3z12p&0p;1p;4p;2p;3p;<p;7p;9p;6p;8p;Bg004Cj1;Tg004hj1]Tg005Fj1RTg005ij1cTg02g6k401Tg00<^j1VTg00@Hj2mTg007GR0j20Tg007cj27Tg008?R1j23Tg03Elj1:Tg03Fcj3?Tg00:4j1^Tg009Zj32Tg00lBj1CTg03G`j3ATg00:Vj2yTg01:dj2<Tg01>;j21Tg0109j4OTg00JcR2j24Tg00?`j2lTg00@ej3kTg00AIj2jTg009@j29Tg00Ajj1gTg00BJj1fTg00Bjj2=Tg00CHj1eTg00Cfj1dTg00DQj2QTg00E4j2>Tg00GJj2bTg00Glj2aTg00HXj3`Tg00I7j4_Tg027Mk100Tg02m?j4DTg00Fgj3~Tg02o2j3BTg00Nkj3JTg00FBj1[Tg00EWj4ITg02;ej3{Tg02:jj4ZTg02kEj4zTg03HXR3j1KTg02@\R4j1XTg03I8j2LTg02H6j1xTg02HTj4wTg031Dl<oTg03IUj2nTg01THj2TTg012jj1PTg029gj2HTg02m]j3GTg02nFj2STg01^Oj3UTg02oUj7rTg02I7j4sTg03J7l9tTg03K:j4NTg003ej6uTg00ONj7WTg00PVj8iTg00P2j7hTg0309l<\Tg030^lB|Tg00Q:j6}Tg00ZCR5f0R6'0p=5f2R7g00R^R8g00S=R9P9g00S]R:g00T]R;f1R<g00\OP6CIg00T=R=FWp=6f3R>P8P9P9P:P7P<P6Gip=8g00Q^R?g00]6R@726p=EP<P8P9P9P:P6P=FWp=@P7P8P9P9P:P<P6Fhp=FP;g03:>R=P;P;P3f4R3P4P>g03L:P7P<P6M<\p=vP=P;P;P;P4P4f5R4P3P>P7P<P6M<\p=qP;P;P;P;P;P;P2P6P<P7P2P>P3P4f6R2f7RAf8RBf9RCMB|p=pP<P8P9P9P:P6E}p=YP;P<g03DhP6CIp=Mg00UbRD#;RE#;RF#;RG#;#;#;RH#]RI#R%]G#RRG#cRJ[g00VGRKP7p,2loRLp,3spzRMH01P1%5LRN%VERO%VHRH'mRP,0MRQ10L6176M'3RR%:<RS9?K4%^GRT52J#C%:7RU9AK21yG6RV52JX9G,<G'3[^:;'311>7,0L103M%53PKPAP2P4CO[[[P6A?KBS=2JT#CAAKCU=2JVX9G,<G'3\R^:;,3QP1PQA?KCS=2JT#Cf:R1=AKU=2JVX9G,<G'3\R^:;11A2,0L10BM%5BPKf;RWP1PCCO[[[P6f<RX=?KS=2JT#Cf=RS=AKU=2JVX9G,<G'3\R^:;111C,0L10WM%5WPN11MLRW,4L/0PR1%56RC176W'3RRf@RU14L<RY#:5?K=2JT#CRT[^D;RZ'31lOHR[175OR\%5H175P[R][R^%5OR_g00ZaR`AkOH<UW=RH%5P\`^=_R_P<g00[=1j5O'9P\eO1R\P]g00[cR`#gRa%f`Rb1=;<%e;Rc%d;Rd1Q;5Re1>;DRf56dRg%^9RhPgC81bd:RgP6P719?@1a67#EdA`;5<C_R@b5b6b7X0;%5<R?\C^0;P6PLPXO2b4b1b8b1P1PZP[P^PHP_P\P]PaPbP;1=;7RZP<&00;R1CDPcPd1>;ERC1Q;O=~;IRI56dPhAB;Cf9J;f=6dIC8PgP@b5b6b7X0;X2;10<P117<,4</0P[^0;^2;P6PMPLPBO3b4b1b8b1fARP14L7#:5AK=2JVX9G,<GP4PYP[P^PHP_P\P]PaPbP;PZP<1=;>CDRZPcPdA6deCRYP;PCg00U;RG%[D,>;RD=B;fCI,@d5FdPhAJ;fCRV96dfP;PVPGPDCI,@d5FdC8PgP@b5b6b7X0;X2;X3;1176,7<,3?14<7R?,0<17?>'3[^0;^2;^3;P6PMP4PLP3O4b4b1b8b1O25{TXJRXD;CZCZPKf>RRPLPWCzPKf?RTPLPW11RS/1LR?%KSRGP6P[P^PHP_P\P]PaPbPZPcPdAB;fCRV96dDPhAB;VDRJ96deC8PgP@b5b6b7X0;X2;X3;116<RI,0711<7/1>#5[^0;^2;^3;P6PLPPfBROPAO4b4b1b8b1%XGRi,4?Rj/0W1L5SRk,4?Rl/0WP;P;P0P6X;;RmP010<6#xXR;X;;PjPlPmPmPmP;P;g03DD14<6Cw,9;XE;XP;P?P?19;?PiPkPmPm%X6,9;X;=PGPkPm1L56X;;PSPS19;SDvEqM:pPWPW19;WM<o1n5S175SA2;kS'310S5A2;k5'3'T1L5RP;P[P^PHP_P\P]p-0Rkg01GnRW#PRm#PR=#P,H;Ri1H;=1H;m1H;W5G;RW5G;5G;g039RRm'SAG;iW/Sm=U`a5U`PbP;P;1=;3P7P1CDP<P;1=;4P>P1CDCDPcPdPdP8P9P9P:1YdA1>;FRF/MC,@d5Fd1YdB1MFe,@d5FdFrPhPdPYPhPd%[E,>;RE96dfPhAJ;JFAB;ED56dC8C8C8PgP@b5b6b7X0;X2;X3;XB;XC;X?kW@A2;><,34A2;>5,32'T%57107211>3/14/4211A4'0[[[^0;^2;^3;^B;^C;^?k^@kP6fCRk/05175kPMP3PLPkfDP4PAPBO:b4bAb1bAbTbGCsM9tPKPT14L?#:PGCN#EP[P^PHP_P\P]PaPbPZPcAJ;DJ,MV,@dPgP@b5b6b7X0;X2;X3;11I7,4792;I^0;^2;^3;P6PLPOPkO3b4b1b8b111TRRk11kL,4L52;P;11UTRk/1L,4LPKPO%:6%KUCN#EXS;P<PkP6EuPKPP%:k%KTCN#EP6b>b<b>bOPKPRPSPXCOeWIWHWFWNXMQP<P6O2n2001000000121000000W<XLNP<P6O2n2001000000121000000W<XK;XQ;WEo"). Qed.

  Lemma stage_np : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 (spf spz)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 8)) y10
                             (Z_to_bv 64 (nreq bc)) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) y20
                             (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) (Z_to_bv 64 p)
                             (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_NP) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    GPREx s mo m errv' LB' LBm p ->
    as_SR H QIx (mkCfg msF mo).
  Proof using All.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ KR GP.
    pose proof GP as GP0.
    destruct GP0 as (MP & FR & SP16 & SPL & SPH & RAE & MI & ST & ERR & RA & TPV & ACS & ACL & LOR & SHI & SPB & BR & LFO & OCE
                     & U & SH & GROW & BCL & SZR & KR32 & AD & WR & OBL & P0 & P1 & P16 & PO & PA & NC & ADP
                     & RH & PE & PM & OWN & XP & RF & AC & S0 & AL & AL0 & RS & RC & RL & RICM & TRK).
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof LOR as LOR'. unfold AREH_STACK, AOPNEW_STACK, AMALLOC_STACK, spf in LOR'.
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U)) as BCR.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (ACONST_shbase m AC) as [CG CS].
    unfold spf in SPL, ACS. unfold spf in VIS.
    assert (FW1 : Forall (fun iv => aceil <= fst iv /\ snd iv <= spf spz /\ fst iv <= snd iv) [(spz - 96 - 32, spz - 96)])
      by (apply Forall_cons; [cbn [Datatypes.fst Datatypes.snd]; unfold spf; lia | apply Forall_nil]).
    pose (RN := fun v : word => mkR y1 (Z_to_bv 64 (spz - 96)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 8)) y10
                  v y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) y20
                  (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) (Z_to_bv 64 p)
                  (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31).
    assert (HF : forall v M1, log_flat (Eseed (RN v) [Z_to_bv 64 obj; v; Z_to_bv 64 (spz - 96)]) lgNP ->
                 M1 = mem_denot (Eseed (RN v) [Z_to_bv 64 obj; v; Z_to_bv 64 (spz - 96)]) m lgNP ->
                 munch [(spz - 96 - 32, spz - 96)] m M1 /\ wmono asegs m M1 /\ stk asegs M1 lo spz
                 /\ rw_cells asegs M1 (spz - 96 - 32) [C8 (Z_to_bv 64 (obj + 24)); C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 E_IDX)]).
    { intros v M1 Hlf HM. subst M1.
      split. { apply munch_mem_denot; [exact Hlf|]. unfold lgNP.
               repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
               apply Forall_nil. }
      split; [apply wmono_mem_denot|]. split; [apply stk_mem_denot; exact ST|].
      assert (CE : map (fun e => C8 (edenot (Eseed (RN v) [Z_to_bv 64 obj; v; Z_to_bv 64 (spz - 96)]) e)) tlNP
                   = [C8 (Z_to_bv 64 (obj + 24)); C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 E_IDX)]).
      { unfold tlNP. cbn [map]. unfold RN. evs. rewrite w_add by lia. reflexivity. }
      rewrite <- CE. rewrite lgNP_c8 in Hlf |- *.
      apply rw_cells_c8log; [exact Hlf | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off a_base]; lia |].
      cbn [tlNP length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul].
      exact (wr_at_subE m lo (spz - lo) (spz - 96 - 32) 32 (wr_at_of_stk asegs m lo spz ST) ltac:(lia) ltac:(lia) ltac:(lia)). }
    assert (HK : forall v, know_ok asegs (Eseed (RN v) [Z_to_bv 64 obj; v; Z_to_bv 64 (spz - 96)]) m KNP).
    { intros v. unfold KNP, know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ m AGOT_SHBASE _ 0%nat (C8 (wz ASHBASE_CELL)));
          [exact CG | reflexivity | reflexivity | lia | reflexivity | unfold AGOT_SHBASE; cbn; lia | unfold AGOT_SHBASE; cbn; lia | reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ m ASHBASE_CELL _ 0%nat (C8 (wz ASHADOW_BASE)));
          [exact CS | reflexivity | reflexivity | lia | reflexivity | unfold ASHBASE_CELL; cbn; lia | unfold ASHBASE_CELL; cbn; lia | reflexivity]. }
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia
                                             | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]. apply Forall_nil. }

    destruct (Z.eqb_spec bc 0) as [Hb0 | Hb0].
    - assert (NQ : nreq bc = 1) by (unfold nreq; rewrite Hb0; reflexivity).
      rewrite NQ in VIS.
      remember (mkR y1 (Z_to_bv 64 (spz - 96)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 8)) y10
                    (Z_to_bv 64 1) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) y20
                    (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) (Z_to_bv 64 p)
                    (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31) as R eqn:HR0.
      assert (HRN : R = RN (Z_to_bv 64 1)) by exact HR0.
      pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 1; Z_to_bv 64 (spz - 96)]).
      assert (HR : regs_ok E srNP0 R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; rewrite ?w_add by lia; reflexivity] |]).
        apply Forall_nil. }
      assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
      assert (HK0 : know_ok asegs E m KNP) by (unfold E; rewrite HRN; apply HK).
      xrun_at (PropExec.mkFP F fc) asegs R E_NP m (seg_rom asegs) HR HK0 60%nat [E_RC; LbB_HNextPrime.NP_A] (SCR [] [] []) 50%N.
      { split_scs. }
      change (log_flat E lgNP) in Hlf.
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) => change mm with (mem_denot E m lgNP) in Hms end.
      set (M1 := mem_denot E m lgNP) in Hms.
      destruct (HF (Z_to_bv 64 1) M1 ltac:(rewrite <- HRN; exact Hlf) ltac:(subst M1 E; rewrite <- HRN; reflexivity))
        as (MU1 & WM1 & ST1 & HF1).
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
      pose proof (gpre_stack s mo m M1 errv' LB' LBm p _ GP MU1 WM1 MI1 ST1 FW1) as GP1.
      readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
      rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 12%bv G12.
      assert (G2' : getr R' 2 = Z_to_bv 64 (spz - 96 - 32)) by (rewrite G2, w_addm by lia; f_equal; lia).
      assert (G9' : getr R' 9 = Z_to_bv 64 SHBASE) by (rewrite G9; reflexivity).
      assert (G11' : getr R' 11 = Z_to_bv 64 (bseq_next bc)) by (rewrite G11, Hb0; reflexivity).
      rewrite G1, G2', G8, G9', G10, G11', G12 in HRe. clear G2 G9 G11.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply (stage_rcall H HH REH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
                s msF1 mo1 M1 F fc) with (errv' := errv') (LB' := LB') (LBm := LBm) (p := p);
        [exact VIS1 | exact FRZ | exact KR1 | | exact HF1].
      destruct GP1 as (MPx & GPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact GPr].

    - assert (NQ : nreq bc = np_arg bc) by (unfold nreq; destruct (Z.eqb_spec bc 0); [lia | reflexivity]).
      rewrite NQ in VIS.
      remember (mkR y1 (Z_to_bv 64 (spz - 96)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 8)) y10
                    (Z_to_bv 64 (np_arg bc)) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) y20
                    (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) (Z_to_bv 64 p)
                    (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31) as R eqn:HR0.
      assert (HRN : R = RN (Z_to_bv 64 (np_arg bc))) by exact HR0.
      pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 (np_arg bc); Z_to_bv 64 (spz - 96)]).
      assert (HR : regs_ok E srNP1 R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; rewrite ?w_add by lia; reflexivity] |]).
        apply Forall_nil. }
      assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
      assert (HK0 : know_ok asegs E m KNP) by (unfold E; rewrite HRN; apply HK).
      xrun_at (PropExec.mkFP F fc) asegs R E_NP m (seg_rom asegs) HR HK0 60%nat [E_RC; LbB_HNextPrime.NP_A] (SCR [true; false] [] []) 50%N.
      { clear - E Hb0 BCR. split_scs; cbn [sc_denot]; evs; unfold np_arg;
          first [ rewrite br_ne by lia; apply (proj2 (Bool.negb_true_iff _)); apply Z.eqb_neq; lia
                | rewrite (w_addm (2 * bc + 1) (-1)) by lia; replace (2 * bc + 1 + -1) with (2 * bc) by lia;
                  rewrite w_and by lia; rewrite land_oe by lia; rewrite br_eq by lia; apply Z.eqb_neq; lia ]. }
      change (log_flat E lgNP) in Hlf.
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) => change mm with (mem_denot E m lgNP) in Hms end.
      set (M1 := mem_denot E m lgNP) in Hms.
      destruct (HF (Z_to_bv 64 (np_arg bc)) M1 ltac:(rewrite <- HRN; exact Hlf) ltac:(subst M1 E; rewrite <- HRN; reflexivity))
        as (MU1 & WM1 & ST1 & HF1).
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
      pose proof (gpre_stack s mo m M1 errv' LB' LBm p _ GP MU1 WM1 MI1 ST1 FW1) as GP1.
      readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
      rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 10%bv G10. rreg HR' 11%bv G11.
      assert (G1' : getr R' 1 = Z_to_bv 64 E_NPR) by (rewrite G1; reflexivity).
      assert (G2' : getr R' 2 = Z_to_bv 64 (spz - 96 - 32)) by (rewrite G2, w_addm by lia; f_equal; lia).
      assert (G9' : getr R' 9 = Z_to_bv 64 SHBASE) by (rewrite G9; reflexivity).
      rewrite G1', G2', G8, G9', G10, G11 in HRe. clear G1 G2 G9.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply (np_sr H HH QIx s msF1 mo1 _ F fc M1 bc (spz - 96 - 32) (Z_to_bv 64 E_NPR) KR1 VIS1 (u_bseq U) Hb0);
        [ unfold LbB_HNextPrime.BSEQ_LAST_A; unfold BSEQ_LAST in BCL; exact BCL
        | reflexivity | reflexivity | vm_compute; reflexivity | reflexivity
        | replace (spz - 96 - 32) with (spz + (-8) * 16) by lia; rewrite Z.mod_add by lia; exact SP16 | lia | lia
        | apply (stack_room_of_stk M1 (spz - 96 - 32) 16); [exact ST1 | lia | lia | lia] | exact MI1 | apply rfull_mkR | ].
      intros msF2 mo2 R2 KR2 MP2 VIS2 KEPT G10n FR2.
      assert (Q1 : getr R2 1 = Z_to_bv 64 E_NPR) by (rewrite (KEPT 1%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q2 : getr R2 2 = Z_to_bv 64 (spz - 96 - 32)) by (rewrite (KEPT 2%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q3 : getr R2 3 = gp) by (rewrite (KEPT 3%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q4 : getr R2 4 = tp) by (rewrite (KEPT 4%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q8 : getr R2 8 = Z_to_bv 64 obj) by (rewrite (KEPT 8%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q9 : getr R2 9 = Z_to_bv 64 SHBASE) by (rewrite (KEPT 9%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q18 : getr R2 18 = Z_to_bv 64 (obj + 24)) by (rewrite (KEPT 18%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q19 : getr R2 19 = Z_to_bv 64 SHBASE) by (rewrite (KEPT 19%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q20 : getr R2 20 = y20) by (rewrite (KEPT 20%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q21 : getr R2 21 = Z_to_bv 64 (obj / 8)) by (rewrite (KEPT 21%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q22 : getr R2 22 = Z_to_bv 64 key) by (rewrite (KEPT 22%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q23 : getr R2 23 = Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) by (rewrite (KEPT 23%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q24 : getr R2 24 = Z_to_bv 64 p) by (rewrite (KEPT 24%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q25 : getr R2 25 = rShe (Z_to_bv 64 p)) by (rewrite (KEPT 25%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q26 : getr R2 26 = rShe (Z_to_bv 64 (obj + 24))) by (rewrite (KEPT 26%bv ltac:(cbn; tauto)); reflexivity).
      assert (Q27 : getr R2 27 = s11) by (rewrite (KEPT 27%bv ltac:(cbn; tauto)); reflexivity).
      rewrite (rfull_eq R2 FR2) in VIS2.
      rewrite Q1, Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27, G10n in VIS2.
      set (bs := word_to_le_bytes 8 (Z_to_bv 64 E_NPR)) in VIS2.
      assert (Lbs : length bs = 8%nat) by reflexivity.
      set (M2 := CatExec.wbytes M1 (Z_to_bv 64 (spz - 96 - 32 - 8)) bs) in VIS2.
      assert (E2 : M2 = write_to_mem M1 (wa (spz - 96 - 32 - 8)) bs) by (subst M2; rewrite wbytes_eq; reflexivity).
      assert (MU2 : munch [(spz - 96 - 32 - 8, spz - 96 - 32)] M1 M2).
      { rewrite E2. apply munch_write; [apply munch_refl | lia | rewrite Lbs; cbn; lia | rewrite Lbs; cbn; lia]. }
      assert (WM2 : wmono asegs M1 M2) by (rewrite E2; apply wmono_write; apply wmono_refl).
      assert (MI2 : mem_inv asegs M2).
      { rewrite E2. apply mem_inv_store; [exact MI1|]. rewrite Lbs.
        pose proof (stack_room_of_stk M1 (spz - 96 - 32) 8 ST1 ltac:(lia) ltac:(lia) ltac:(lia)) as SR0. unfold stack_room in SR0. exact SR0. }
      assert (ST2 : stk asegs M2 lo spz) by (rewrite E2; apply stk_write; [exact ST1 | lia | rewrite Lbs; cbn; lia]).
      pose proof (gpre_stack s mo M1 M2 errv' LB' LBm p _ GP1 MU2 WM2 MI2 ST2
                    ltac:(apply Forall_cons; [cbn [Datatypes.fst Datatypes.snd]; unfold spf; lia | apply Forall_nil])) as GP2.
      assert (HF2 : rw_cells asegs M2 (spz - 96 - 32) [C8 (Z_to_bv 64 (obj + 24)); C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 E_IDX)]).
      { eapply rw_cells_transport; [exact HF1 | exact MU2 | exact WM2 |]. apply LbB_HXmpI2.dj_of_forall.
        apply Forall_cons; [cbn [Datatypes.fst Datatypes.snd]; lia | apply Forall_nil]. }

      remember (mkR (Z_to_bv 64 E_NPR) (Z_to_bv 64 (spz - 96 - 32)) gp tp (getr R2 5) (getr R2 6) (getr R2 7) (Z_to_bv 64 obj)
                    (Z_to_bv 64 SHBASE) (Z_to_bv 64 (bseq_next bc)) (getr R2 11) (getr R2 12) (getr R2 13) (getr R2 14) (getr R2 15)
                    (getr R2 16) (getr R2 17) (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) y20 (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key)
                    (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) (Z_to_bv 64 p) (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11
                    (getr R2 28) (getr R2 29) (getr R2 30) (getr R2 31)) as R3 eqn:HR3.
      pose (E3 := Eseed R3 []).
      assert (HR3' : regs_ok E3 (srs sr_id []) R3) by (apply regs_ok_srs; [apply regs_ok_seed | apply Forall_nil]).
      assert (HK3 : know_ok asegs E3 M2 []) by constructor.
      assert (FHF3 : rfull R3) by (rewrite HR3; apply rfull_mkR).
      xrun_at (PropExec.mkFP F fc) asegs R3 E_NPR M2 (seg_rom asegs) HR3' HK3 10%nat [E_RC] (SCR [] [] []) 50%N.
      { split_scs. }
      readback HR'0 (msteps_full asegs _ _ Hms0 FHF3) HR3 HRe3.
      rreg HR'0 10%bv G10r. rreg HR'0 11%bv G11r.
      assert (G10r' : getr R'0 10 = Z_to_bv 64 obj) by (rewrite G10r, HR3; reflexivity).
      assert (G11r' : getr R'0 11 = Z_to_bv 64 (bseq_next bc)) by (rewrite G11r, HR3; reflexivity).
      rewrite G10r', G11r' in HRe3. clear G10r G11r.
      eapply (sr_blk_eq H HH); [exact KR2 | exact VIS2 | exact FHF3 | exact Hms0 | exact HRe3 |].
      intros msF4 mo4 KR4 MP4 VIS4.
      eapply (stage_rcall H HH REH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
                s msF4 mo4 M2 F fc) with (errv' := errv') (LB' := LB') (LBm := LBm) (p := p);
        [exact VIS4 | exact FRZ | exact KR4 | | exact HF2].
      destruct GP2 as (MPx & GPr). split; [|exact GPr].
      eapply (ah_mpres_trans H HH); [exact MPx|]. eapply (ah_mpres_trans H HH); [exact MP1|].
      eapply (ah_mpres_trans H HH); [exact MP2 | exact MP4].
  Qed.
End EmpN.
