(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3 Hoare RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HRehStmt LbB_HKit LbB_VecT LbB_HEmpS LbB_HEmpK LbB_HEmpD LbB_HEmpI LbB_HEmpI2
  LbB_HEmpI3 LbB_HEmpI4 LbB_HEmpX LbB_HEmpR.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_HNextPrime.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_HEmpN () := "C69OSSVerify5KrLib3bpB2Rt7BsIface5blockC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C46Stdlib5Lists4List8nil_consC46Stdlib7Sorting;Permutation>Permutation_inC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib3bpB2HF3Lib4BMem7mem_invC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes6option01C79OSSVerify5KrLib3bpB2HF3Lib4BMem7ro_addrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib7LibHash4HLib8u64_of_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib3bpB2Rt<BakeStackRepBfind_segment_asegsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00C47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic9False_indK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib3bpB2Rt5BSegs5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib>LbB_HNextPrime7RO_LO_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib>LbB_HNextPrime7RO_HI_AC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C49OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_bothbTgt_spvtools_binary_parser_fuzzer_both_segment_000C1@~~~~~~~~~~~~~~~~C49OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_bothbTgt_spvtools_binary_parser_fuzzer_both_segment_001C1@~~~~~~~~~~~~~~~~C49OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_bothbTgt_spvtools_binary_parser_fuzzer_both_segment_002C1@~~~~~~~~~~~~~~~~C49OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_bothbTgt_spvtools_binary_parser_fuzzer_both_segment_003C1@~~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C69OSSVerify5KrLib3bpB2Rt7BsIface5as_StC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib3bpB2Rt7BsIface8as_AKRELC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface6as_VISC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib:BLPropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BMState2MSC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notK45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep6np_argC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Hoare6ret_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC49OSSVerify5KrLib8LibIface:stack_roomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_Bridge5rfullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface8as_MPRESC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C49OSSVerify5KrLib<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5as_SRC1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib8PropExec7FPState01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_HEmpNBro_none_of_mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib>LbB_HNextPrimeAnext_prime_spec_AC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib6CatSim6msteps00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib3bpB3Lib:LbB_Bridge;msteps_fullC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC69OSSVerify5KrLib3bpB3Lib8LbB_HKit5sr_msC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep9bseq_nextC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C49OSSVerify5KrLib8LibIface3memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib>LbB_HNextPrime4NP_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep4BSEQC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib>LbB_HNextPrime;BSEQ_LAST_AC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpR4GPREC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow5aceilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpD3spfC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpD5FRAMEC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C69OSSVerify5KrLib3bpB3Lib<LbB_HEmpStmt>map_live_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep6nval24C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7LibHash4HRep7ZlengthC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C69OSSVerify5KrLib3bpB2Rt7BsIface8blk_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface8blk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep;umap_blocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep5apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5as_ALC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib3bpB2Rt9RtB_Iface6nsmallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_Iface3nlgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_Iface3ICMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5as_TRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_HEmpStmt:emp_del_raC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib3bpB2Rt7BsIface8trace_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB3lblC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface;as_rauxv_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow;addressableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface8as_RHEAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib7LbB_Own6lb_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt6BXXRep5xpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface6as_RFSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsConst6ACONSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsStack06stack0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2geC69OSSVerify5KrLib3bpB2Rt9RtB_Iface8lb_smallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_Iface6nlargeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow;aceil_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF8BeapCeil5hceilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9BsCXXHeap6ah_fsbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface7afsb_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface6as_FSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow4aappC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpD9obj_placeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface<afs_write_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsConst9aconst_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsStack09stack0_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface@aclient_write_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t01C69OSSVerify5KrLib3bpB2Rt9BsCXXHeap?stack_window_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow2shC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01C46Stdlib5Lists4List;Forall_implC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI2<dj_of_forallC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame=disjoint_fromC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow3nshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow;sh_nsh_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib3bpB2Rt9BsCXXHeap<client_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep8u_obj_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep8u_obj_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC79OSSVerify5KrLib3bpB2HF3Lib6BCells:cells_sizeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C79OSSVerify5KrLib3bpB2HF3Lib7BLFrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7pos_subC57Corelib7BinNums6PosDef3Pos3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib7Sorting;Permutation?Permutation_symC69OSSVerify5KrLib3bpB3Lib8LbB_MILB:lbl_in_invC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib3bpB2Rt9BsCXXHeap9ah_blocksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep9umap_footC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:in_app_iffC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib5Lists4List:in_map_iffK47Corelib4Init5Logic2ex01C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI2=out_of_forallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash9HRepFacts<nval24_agreeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface4liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash9HRepFacts;umapx_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts3t3bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts3t3aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts3t3cC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib3bpB2Rt8BsShadowEaddressable_transportC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib3bpB3Lib7LbB_Own;wr_at_wmonoC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC69OSSVerify5KrLib3bpB3Lib7LbB_Own<lb_own_wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt6BXXRep7rin_ivsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt6BXXRep>xpres_of_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt6BXXRep<xpres_weakenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt6BXXRep;xpres_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsStack0@stack0_transportC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame3stkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7LibHash4HRep5umapx00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib5BStep8rw_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC79OSSVerify5KrLib3bpB2HF3Lib4BMem5wr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib;LbB_PrsStmt7umap_shC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC69OSSVerify5KrLib3bpB3Lib8LbB_MILB4AC_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB4LY_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB4MI_AC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_Iface<RT_LARGE_MAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_Iface<RT_SMALL_MAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_Iface:RT_CNT_MAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt5BSegs8AIMG_TOPC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC69OSSVerify5KrLib3bpB2Rt7BsIface3ATPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_HRehStmt:AREH_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts9BSEQ_LASTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface9APC0_FREEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_HEmpStmt7EMP_U32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface8AFS_SIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow6AHI_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow7AAPP_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib7LbB_Kit6SHBASEC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201C46Stdlib5Lists4List8map_consC79OSSVerify5KrLib3bpB2HF3Lib4BMem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC79OSSVerify5KrLib3bpB2HF3Lib4BMem3mrdC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC79OSSVerify5KrLib3bpB2HF3Lib4BMem>wr_at_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC69OSSVerify5KrLib3bpB3Lib9LbB_HEmpD4rSheC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame3mkRC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7FPSteps8frm_zeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpI2QIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HFind;BSEQ_boundAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib5EseedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib<regs_ok_seedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26edenotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib7LibHash4HLib;regs_ok_srsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib3srsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_Bridge9rfull_mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9scs_denotC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX27scripts01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX29sym_state01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX28sym_execC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7SymRun39run_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25s_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_Call=regs_keep_mkRC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7mod_addc69OSSVerify5KrLib3bpB3Lib9LbB_HEmpNAstack_room_of_stkC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC69OSSVerify5KrLib3bpB3Lib:LbB_Bridge8rfull_eqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib3bpB3Lib8LbB_Conv9wbytes_eqC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame:munch_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame6insideC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses8or_morphC79OSSVerify5KrLib3bpB2HF3Lib7BLFrame;munch_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame:wmono_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame;wmono_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib4BMem=mem_inv_storeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame9stk_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9BsCXXHeap>ah_mpres_transC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02c69OSSVerify5KrLib3bpB3Lib9LbB_HEmpN:gpre_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpR;stage_rcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_VecT9sr_blk_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_HEmpN5np_srC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep6u_bseqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_HEmpN4E_NPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX23env00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25sr_idC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26kentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01I59OSSVerify5KrLib8SymExec33SX26sentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX27scripts00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpR4E_RCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_HEmpN5E_NPRC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_NP : Z := 0xfa768.
Definition E_NPR : Z := 0xfaa98.
Definition nreq (bc : Z) : Z := if Z.eqb bc 0 then 1 else np_arg bc.
Definition srNP0 : list expr := srs sr_id [(2%bv, EVar 34); (8%bv, EVar 32); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (11%bv, ELit 1)].
Definition srNP1 : list expr := srs sr_id [(2%bv, EVar 34); (8%bv, EVar 32); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (11%bv, EVar 33)].
Definition KNP : list kentry :=
  [KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit SHBASE);
   KRange (EVar 34) (2 ^ 45) (2 ^ 47); KWr (SA (EVar 34) (-32)) (ELit 32)].
Definition tlNP : list expr := [EVar 18; EAlu ALU_ADD (EVar 32) (ELit 8); EVar 32; ELit E_IDX].
Definition lgNP : list sentry := Eval cbv in c8log (EVar 34) (-32) tlNP.
Lemma lgNP_c8 : lgNP = c8log (EVar 34) (-32) tlNP.
Proof. reflexivity. Qed.

Lemma ro_none_of_mem_inv : forall m, mem_inv asegs m ->
  forall i, LbB_HNextPrime.RO_LO_A <= i < LbB_HNextPrime.RO_HI_A -> m (Z_to_bv 64 i) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpN ()) [] "p'0h02ROh14__x1h24__p1h32b0h42b1h51Eh62H0h72H2h87__arithh94__ffh:4__p2h;8__varmaph<5__with=2H1h>1Hh?2Hah@6__sat1hA1oi001ohB2H3hC2HihD2MIhE6__sat0hF1bi011bhG1ehH1ihI1mhJ1zi023segi031xp;1p;2p;3p;4p;6p;7p;8p10000p4p70R0p1000ip4p710p8P0p1001Tp4p710p8P0p10021p4p710p8p1002]p4p7210R0g003IR1p4p710p8P0p1003ep4p710p8g004Cj13Tg004hj1PTg005Fj1OTg005iR0j1STg006Kj2dTg007Gj22Tg007cj21Tg008?j2CTg008Zj2;Tg009@j2ETg009Zj3:Tg00:4j1JTg00:Vj2@Tg00;8j2mTg00<4j2cTg00<^j19Tg00=<j3MTg00>@j1`Tg00?Bj1^Tg00?`j2]Tg00@Hj2\Tg00@ej3[Tg00AIj2ZTg00Ajj1YTg00BJj1XTg00Bjj2WTg00CHj1VTg00Cfj1UTg00DQj2?Tg00E4j2TTg00EWj4LTg00FBj1=Tg00Fgj3nTg00GJj2lTg00Glj2kTg00HXj3jTg00I7j4fTg00Iij2eTP1j6NTg00Jcj24Tg00K@j1bTg00LKj2FTg00Lmj27Tg00MJR1j3GTg00Mnj26Tg00NLj2QTg00Nkj3aTg00ONj7_Tg00P2j7gTg00PVj8hTg00Q:j6iTf0R2#3#3p=Hg00Q^R3g00R>R47:2p=0%32#3#3#3#3#3#3#3p=Bf1R5g00R^R6g00S=R7P7g00S]R8P2g00T=F_p=8%=2#=p=K%=2#3p=>%32#3#3#3p=Dg00T]R9P5g00U;P2CLp=Af2R:P6P7P7P8P5P2Fgp=If3R;P6P7P7P8P:P5P2Ghp=<17;:1752'6p=5P5P6P7P7P8P2Eip=Rg00UbR6#3R<#3R=#3R>#3#HR?#PR@#O%P>#OR>#SRA[g00VGRB/d2g00W>/22g00XA,12'CP;1;@5O1PA1EA2f4RC1;@:O1=:A2P0P>f6RD1;@CO1=:A2%J>RE9:A5]5P5f7RFf5RG,;@O11@>25:A1@>5=:AEPF1;@DRDP5P2O31mBD#0P91;@F,c@P0g00YDRDP3%96RH9MB2%`2#^RIP4n10110300021010200#0XJ9P2PF%9<R<%9?RJ']g00ZCRK/1<RL12KJ1\<JRM,1K[RN[12K<ROg00ZaRPA[<J5UW?12KM\P^?OP5g00[=1ZK<'EPLeO1PNg00[cRN#YRL%XNRN1W95RO%V9RJ%U9RQP9%H?#B#9R?,?9RRg00\ORS1T96RTCL,8QRU%36#=#K#K#>#D#B#9RV,?9RW,AT,8QRX5IQ%J7R7P91?9KPSPTCL,8Q1?9<=n9@,AT,8Q5IQC<1lQ8R8P2P:g00]6R<,E31k2:=:3<dAj9K5CfRSb9b;b<X1912?2112V'C12K5115M'C[^19P2f;RMf:RKO2b8b@bEb@,eFENP0PDP3AMBFHPIP4n10110300021010200#0%SDRYf8RZ=MBHP0PDP3P2PIP4n10110300021010200#0XAYP2P3PYP?PZ14ZHRB%>=#H#=#D#B#9R=C5g00]V,@DR[P3PYP=PZPBPVC5g00_U,@DR\P3PYPVPZPB%=6#D#=#>#D#B#9R]C5g00aT,@DR^P3PYP]PZPB%>6#K#>#>#H#D#B#9R6C5g00cS,@DRB%JDR_n0100000020000n0100000020000n0100000020000n0100000020001R`%bZENP0PDP3P`PIP4n10110300021010200#0f9R`,F?12?`11`?17?`3G17?KP3P112?M11M?P0PDP3P3PYf=RM/4HRK/7=R`,65P[P3PYP=PMPKPVC5P\P3PYPVPMPKP]C5P^P3PYP]PMPKP6C5PBP_n0100000020000n0100000020000n0100000020000RKn0100000020001PIP4n10110300021010200#0g00eRRM]0P5f<RZ,2?P0PDP3P3PY16<`P[PKn0100000020001PIP4n10110300021010200#0f>/4HRa/F=Rb12a=11=a17a=3GRaf?/4H/7=RcP3P1f@/4HRd/2=Re11=dRdP0PDP3P3PY16<5RfP[P3PYP=fBRg14gHRhPVC5P\P3PYPVPgPhP]C5P^P3PYP]PgPhP6C5PBP_n0100000020000n0100000020000n0100000020000Rhn0100000020001PIP4n10110300021010200#0PM]0P5fA/4HRg/2=RiP0PDP3P3PY16<<RjP[Phn0100000020001PIP4n10110300021010200#0P3P<P3p-0RkP2PPPMn0110100020000XG3g00eoP4P2ENRPPM1QM2Rlb=W0W6P2O111=gRgP0PDP3P3PY16<4RmP[Phn0100000020001PIP4n10110300021010200#0fCRn,F=12=n11n=17=n3GfDRo,7=P3P1fERp,2=11p=P0PDP3P3PYfGRp/4HRq/7VRr,65P\P3PYPVPpPqP]C5P^P3PYP]PpPqP6C5PBP_n0100000020000n0100000020000Rqn0100000020000PIP4n10110300021010200#0PM]0P5fFRp,2=P0PDP3P3PY16<rP\Pqn0100000020000PIP4n10110300021010200#0fH/4HRs/FVRt12sV11Vs17sV3GRsfI/4H/7VRuP3P1fJ/4HRv/2VRw11VvRvP0PDP3P3PYPfP\P3PYPVfLRf14fHRxP]C5P^P3PYP]PfPxP6C5PBP_n0100000020000n0100000020000R_n0100000020000PIP4n10110300021010200#0PM]0P5fK/4HRB/2VR6P0PDP3P3PYPjP\P_n0100000020000PIP4n10110300021010200#0PPPMPlbBW0W7P2O111VBRBP0PDP3P3PYPmP\P_n0100000020000PIP4n10110300021010200#0PLPNPOPJPQ1?9H9a9TRm,AW,8QP7PQ1RQ;RW=IQXP71RQCRXC<C<P8PSb9b;b<X19X2kX:k142H,1V115V,C:PC[[^19^2k^:kP2PMfNRl,2?PlP:fMO5b8W0W7P2O1n200210100000021100011000P:O1b4b3W0W=P2O111p=P0PDP3P3PY164rP\Pqn0100000020000PIP4n10110300021010200#0PtPsPuP3P1PwPvP0PDP3P3PY1645RvP\P_n0100000020000PIP4n10110300021010200#0PM]0P5P0PDP3P3PY164<R<P\P_n0100000020000PIP4n10110300021010200#0PLPNPOPJPQ1?9=Rw,AT,8QP7PQ1Awm,8QP7PWC<C<P8PSb9b;b<X19X2k112=145H,1=P;[[^19^2kP2PMPlPFPZO4b8RlW0X76P2O1P0PDP3P3PY1644R6P\P_n0100000020000PIP4n10110300021010200#0PlW0X7BP2O1n200210100000021100011000P:O1b4b3W0W=P2O1n200210100000021100011000P:O1b4b3W0W6P2O1n200210100001021100011000P:O1b4b3W0W>P2O111Z?P0PDP3P3PY164`P[PKn0100000020001PIP4n10110300021010200#0PbPaPcP3P1PePdP0PDP3P3PYPvP[Phn0100000020001PIP4n10110300021010200#0PM]0P5P0PDP3P3PYP<P[Phn0100000020001PIP4n10110300021010200#0PLPNPOPJPQ1ATR,8QP7PQAIQUWP7PXC<C<P8PSb9b;b<X19X2kX:k112?12?5/C:PC[[^19^2k^:kP2PM11oVPoPFPnO5b8RnW0X6iP2O1P0PDP3P3PYP6P[Phn0100000020001PIP4n10110300021010200#0PnW0X6gP2O1n200210100001021100011000P:O1b4b3W0W>P2O1n200210100001021100011000P:O1b4b3b0b0b0'QW5XF>P2O1PG1;@;O1=:AE1EAEW5n10110000021110100P2O1b5bAWCXH9WDWIo"). Qed.

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
ltac2:(KReplay.run1 (kr_t_LbB_HEmpN ()) ["NP"] "p'0h02R'h12H0h23mo'h34msF'h41Fh52FRh63FR'h73G10h82H1h93H10h:2H2h;3Hinh<3Hmsh=3Hn0h>3Hnlh?4Hreth@1KhA4KEPThB2KRhC3KR'hD2MIhE3MP'hF1QhG1RhH4ROOMhI4SP16hJ3SPHhK3SPLhL3VIShM4VIS'hN2bchO1ehP2fchQ1mhR2mohS3msFhT3rethU1shV2spi001xp;1p;2p;3p;7p;4p;Bp;5p;=g00fKj1`Tg004Cj11Tg00FBj1=Tg004hj1@Tg005Fj1KTg002]j2VTg00gDj2;Tg00h9j3BTg00i5j3ATg008Zj2?Tg00:4j1NTg00ioj1MTg00k1j7ETg009Zj33Tg00kkj3]Tg00lBj1JTg00<^j1:Tg00l[j3DTg00m>j26Tg00n0j1UTg00nhj1TTg00oYj2STg00@Hj2HTg007Gj2GTg0109j4RTg006Kj2QTg0111j1CTg011nj3FTg012jj14Tg013Ij28Tg014Cj3>Tg015<j22Tg0163j2OTg017<lBPTg018Ij1LTg019>j50Tg01:0j3<Tg008?R0j29Tg01:dR1j2_Tg01;>j5^Tg01<Aj1\Tg01=@l=YTg01>;j2XTg01>Xj2WTg01?`j3ZTg01@Sj1[Tf3R2f2R3f1R4f0R5'?33p=If5R6f4R71X23'?1W453Zp=5%[5,?49323p=7g01ANp-0[p,1HR8#`g01BCR9g01CJR:g00UbR;#1R<#=R=#@R>%1<#1R?#1R@#1RA#1#@RB#KRC'VRD%@A#Kg01D@g00T]RAf9REf8RFf7RG';RH5B8f:RI=A8EPGf6RJg01E1,?BRKP6%NCRLP7g00VGRM#MRNFE539g01F19]A7g00ZCRO93A6#Jg01Fg93AJ#JPCf;RP%1=#:g00eoRQ5D>RR'6PB%UGCIf<RS%:;=D>Q'6=3CJ%TGPCf>RT%:<R<=D>Q'6PBPECI%:@R@,SI=3AO%=;#1#1#1#:,H</GP%==#=#=#:,H<,GSPMf?R<f=R=P@CRf@R@,QMfDR;#CfKRO1;345B8fJRQ=F83fMR>=A87P3fIRUP;fHRVPLfGRWPBfERX%:?R?g01Gn#4#4#4#4#4#4#4#4RYP;E5RZPNFE53918O2PC167RR[PBPVC7%C6fRR\=>8H[[[[[[^0D^2:^3912X;fFRHfCR]fBR^fAR_P@P=PSPPPIPEPFPGPJP6P7P21O]3MBPg01HMRP12HXRSPWPKP;%LPR=D0PSP5P_P;PBP^P?PYP_E5P=D03<18W5PC165RR_PBP]C7'9'9X0D,_DP1PD12WHR1PVPKPXP=D0P1P5P^PXPBP]P?PYP^E5P=D05<P18V5PCP_PBP;C7'9'9X0DfLR^1;QU5>8P512UVR1PQPKPWP=D0P1P5P;PZP=D05<P18Q5PCP_PBPHC7'9'9P012QURUPOPKPVP=D0PUP4PXPVPBPHP?PYPXE5P=D05<P18O4PC164RPBPWC7'9fPRXfNRH/;>5>8P512^ORUP>PKPQP=D0PUP2PWPQPBPVP?PYPWE5P=D05<P18H7PCP[PBPQC7'9P0fOR0/86PC166RPBPOC7fTROfQRQ,;\5>8P518QGPC16FRPBPHC7PM12\QRMfSRRPKPXP=D0PMPEP>PXPBPHP?PYP>E5P=D0RXP6PTD^%\X#Cp,5HCEILP8p,2HHfXRXfWREfVRMfURFPOPRPKP\PLPQPNFE12R\PIPHPQPBP0P?PYPHE5P=D0P>P^PJfY1;455B8AF8X4f[=A8212EMPTP\PFPBPRP?PYP\E5P=D0539P]P7P2P<P3P4P5PGPJP6O9WMWEWCX2:X39M=Yb6W7WAP4P5O2n2001000000121000000W1W<P4P5O2n2001000000121000000W1X0DP4P5O2n2001000000121100000bOW@W5WDWHWJWKWIW:W?W8W9W>W=W;WLWBXTCXVAWNWQWPX4DWGWRWSWUWFo"). Qed.
End NP.

Section EmpN.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis REH : reh_stmt H EMP_U32.
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
    intros s mo m m1 errv' LB' LBm p W before untouched views_kept inv_after stack_after fits.
    pose proof aceil_facts as ((ceil_low & ceil_high) & _ & _).
    destruct before as (pres_mo & frame_m & spz16 & spf_low & spz_high & ra_even & inv_m & stk_m & errno_m & auxv_m
      & tp_is & ceil_spf & ceil_lo & lo_room & spz_shi & spz_B & B_top & live_obj & obj_ceil & map_m & mapsh_m
      & full_or_empty & bc_last & len_small & key32 & objaddr_m & objwr_m & obj_sep & p_pos & p_top & p16 & p_obj
      & p_blocks & node_m & paddr_m & heap_m & lb_split & lbm_perm & own_m & xp_m & fs_m & const_m & stk0_m
      & al_ge & al_pos & small_cap & cnt_cap & large_cap & icm_le & trace_k).
    (* Every address below the heap ceiling keeps its byte: the writes all sit at or above it. *)
    assert (below_same : forall x, 0 <= x < aceil -> m1 (Z_to_bv 64 x) = m (Z_to_bv 64 x)).
    { intros x x_low. apply untouched. rewrite u64_of_Z by lia. apply outI.
      eapply Forall_impl; [|exact fits]. intros iv fit; cbv beta in fit |- *. lia. }
    assert (owned_low : forall A n, In (A, n) (lbl LBm) -> 0 < A /\ A + n <= aceil).
    { intros A n in_lbl. destruct (lbl_in_inv LBm A n in_lbl) as (q & in_m).
      assert (in_all : In (q, A, n) LB').
      { eapply Permutation_in; [apply Permutation_sym; exact lb_split|]. apply in_or_app. right. exact in_m. }
      pose proof (ah_blocks H HH s LB' m (q, A, n) heap_m in_all) as range.
      unfold ablock_range in range. cbn [blk_addr blk_size fst snd] in range. lia. }
    assert (map_low : forall A n, In (A, n) (umap_blocks 24 bl bc ents) -> 0 < A /\ A + n <= aceil).
    { intros A n in_map. apply owned_low.
      eapply Permutation_in; [apply Permutation_sym; exact lbm_perm|]. right. exact in_map. }
    assert (foot_same : forall a, umap_foot 24 obj bl bc ents a -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a foot. apply below_same.
      destruct foot as [in_obj | [(nonempty & in_bkt) | (q & q_key & in_node)]].
      - pose proof (u_obj_lo map_m). lia.
      - assert (bkt_blk : In (bl, 8 * bc) (umap_blocks 24 bl bc ents)).
        { unfold umap_blocks. apply in_or_app. left.
          destruct (Z.eqb_spec bc 0) as [is_zero | _]; [contradiction | left; reflexivity]. }
        pose proof (map_low _ _ bkt_blk). lia.
      - assert (node_blk : In (q, 24) (umap_blocks 24 bl bc ents)).
        { unfold umap_blocks. apply in_or_app. right.
          apply in_map_iff in q_key. destruct q_key as (e & e_fst & e_in).
          apply in_map_iff. exists e. split; [f_equal; exact e_fst | exact e_in]. }
        pose proof (map_low _ _ node_blk). lia. }
    assert (shadow_clear : forall A n, 0 <= A -> 0 <= n -> A + n <= 2 ^ 47 -> disjoint_from W (sh A) (nsh n)).
    { intros A n A_pos n_pos A_top. apply dsh_app; [| exact A_pos | exact n_pos | exact A_top].
      eapply Forall_impl; [|exact fits]. intros iv fit; cbv beta in fit |- *. right. unfold AHI_LO. lia. }
    pose proof (ah_fsb H HH s LB' m heap_m) as (_ & fsb_ceil & _ & _).
    assert (clients : Forall (aclient_write_ok H LB') W).
    { eapply Forall_impl; [|exact fits]. intros iv fit; cbv beta in fit |- *. unfold aclient_write_ok. left. apply fit. }
    assert (fs_ok : Forall (afs_write_ok H LF) W).
    { eapply Forall_impl; [|exact fits]. intros [a1 a2] fit; cbv beta in fit |- *. cbn [fst snd] in fit.
      assert (at_ceil : aceil <= a1) by lia.
      exact (proj1 (proj2 (stack_window_ok H LB' LF a1 a2 at_ceil fsb_ceil))). }
    assert (consts_ok : Forall aconst_ok W).
    { eapply Forall_impl; [|exact fits]. intros [a1 a2] fit; cbv beta in fit |- *. cbn [fst snd] in fit.
      assert (at_ceil : aceil <= a1) by lia.
      exact (proj2 (proj2 (stack_window_ok H LB' LF a1 a2 at_ceil fsb_ceil))). }
    destruct (client_frame H HH s LB' LF B W m m1 heap_m fs_m const_m auxv_m untouched views_kept clients fs_ok consts_ok)
      as (heap_1 & fs_1 & const_1 & auxv_1).
    assert (frame_1 : FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz m1).
    { unfold FRAME in *. eapply rw_cells_transport; [exact frame_m | exact untouched | exact views_kept |].
      apply djI. eapply Forall_impl; [|exact fits]. intros iv fit; cbv beta in fit |- *. cbn [cells_size csize Nat.add]. lia. }
    assert (errno_1 : rw_cells asegs m1 (bv_unsigned tp + -164) [C4 errv']).
    { eapply rw_cells_transport; [exact errno_m | exact untouched | exact views_kept |].
      apply djI. eapply Forall_impl; [|exact fits]. intros iv fit; cbv beta in fit |- *.
      rewrite tp_is, u64_of_Z by (unfold ATP; lia). cbn [cells_size csize]. unfold ATP. lia. }
    assert (p_low : 0 < p /\ p + 24 <= aceil).
    { apply owned_low. eapply Permutation_in; [apply Permutation_sym; exact lbm_perm | left; reflexivity]. }
    assert (node_1 : rw_cells asegs m1 p [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_transport; [exact node_m | exact untouched | exact views_kept |].
      apply djI. eapply Forall_impl; [|exact fits]. intros iv fit; cbv beta in fit |- *. cbn [cells_size csize Nat.add]. lia. }
    assert (objaddr_1 : addressable m1 obj 40).
    { eapply addressable_transport; [exact objaddr_m | exact untouched | exact views_kept |].
      pose proof (u_obj_lo map_m). pose proof (u_obj_hi map_m). apply shadow_clear; lia. }
    assert (paddr_1 : addressable m1 p 24).
    { eapply addressable_transport; [exact paddr_m | exact untouched | exact views_kept |].
      apply shadow_clear; lia. }
    assert (map_1 : umapx MI_A 24 (nval24 ASEGS) (lbl LB') m1 obj bl bc ents).
    { eapply umapx_agree; [exact (nval24_agree ASEGS) | lia | exact map_m | exact foot_same |].
      intros q n _ live. exact live. }
    assert (mapsh_1 : umap_sh m1 24 (bl, bc, ents)).
    { unfold umap_sh in mapsh_m |- *. cbn [HStmts.t3a HStmts.t3b HStmts.t3c fst snd] in mapsh_m |- *.
      destruct mapsh_m as [bkt_sh node_sh]. split.
      - intros nonempty. pose proof (u_bl_lo map_m nonempty). pose proof (u_bl_hi map_m).
        pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq map_m)).
        eapply addressable_transport; [exact (bkt_sh nonempty) | exact untouched | exact views_kept |].
        apply shadow_clear; lia.
      - intros q k v in_ents. destruct (u_node map_m q k v in_ents) as (_ & q_pos & q_top & _).
        eapply addressable_transport; [exact (node_sh q k v in_ents) | exact untouched | exact views_kept |].
        apply shadow_clear; lia. }
    assert (stk0_1 : stack0 m1 lo shi).
    { eapply stack0_transport; [exact stk0_m | exact untouched | exact views_kept |].
      eapply Forall_impl; [|exact fits]. intros iv fit; cbv beta in fit |- *. unfold stack0_ok. left. unfold AHI_LO. lia. }
    assert (xp_1 : xpres H LB0 spz [(obj, obj + 40)] m0 m1).
    { eapply (xpres_munch_mixed H HH s LB' LB0 LBm spz [(obj, obj + 40)] W m0 m m1);
        [exact xp_m | exact heap_m | exact lb_split | unfold spf in *; lia | exact untouched | exact views_kept |].
      eapply Forall_impl; [|exact fits]. intros iv fit; cbv beta in fit |- *. unfold wmix. left. unfold spf in fit. lia. }
    pose proof (wr_at_wmono m m1 obj 40 objwr_m views_kept) as objwr_1.
    pose proof (lb_own_wmono LBm m m1 own_m views_kept) as own_1.
    unfold GPRE.
    repeat match goal with |- _ /\ _ => split end.
    all: first [assumption | lia].
  Qed.

  Lemma stack_room_of_stk : forall m sp S, stk asegs m lo spz -> lo <= sp - S -> sp <= spz -> 0 <= S -> stack_room asegs m sp S.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpN ()) ["EmpN"] "h04__x1h17__sat13h24__x2h34__x3h47__arithh54__ffh68__varmaph75__with87__sat12h91bh:1ah;1xh<2H0h=2Hah>2SOh?4__p1h@4__p2hA7__sat14hB4__x4hC4__x5hD1ihE1mhF2H1hG3H12hH2H2hI2H3hJ2HihK1ShL2S1hM2S2hN2S3hO1WhP1nhQ2sphR1yhS1zhT3z12p&0p;1p;4p;2p;3p;<p;7p;9p;6p;8p;Bg004Cj1;Tg004hj1]Tg005Fj1RTg005ij1cTg02g6k401Tg00<^j1VTg00@Hj2mTg007GR0j20Tg007cj27Tg008?R1j23Tg03Elj1:Tg03Fcj3?Tg00:4j1^Tg009Zj32Tg00lBj1CTg03G`j3ATg00:Vj2yTg01:dj2<Tg01>;j21Tg0109j4OTg00JcR2j24Tg00?`j2lTg00@ej3kTg00AIj2jTg009@j29Tg00Ajj1gTg00BJj1fTg00Bjj2=Tg00CHj1eTg00Cfj1dTg00DQj2QTg00E4j2>Tg00GJj2bTg00Glj2aTg00HXj3`Tg00I7j4_Tg027Mk100Tg02m?j4DTg00Fgj3~Tg02o2j3BTg00Nkj3JTg00FBj1[Tg00EWj4ITg02;ej3{Tg02:jj4ZTg02kEj4zTg03HXR3j1KTg02@\R4j1XTg03I8j2LTg02H6j1xTg02HTj4wTg031Dl<oTg03IUj2nTg01THj2TTg012jj1PTg029gj2HTg02m]j3GTg02nFj2STg01^Oj3UTg02oUj7rTg02I7j4sTg03J7l9tTg03K:j4NTg003ej6uTg00ONj7WTg00PVj8iTg00P2j7hTg0309l<\Tg030^lB|Tg00Q:j6}Tg00ZCR5f0R6'0p=5f2R7g00R^R8g00S=R9P9g00S]R:g00T]R;f1R<g00\OP6CIg00T=R=FWp=6f3R>P8P9P9P:P7P<P6Gip=8g00Q^R?g00]6R@726p=EP<P8P9P9P:P6P=FWp=@P7P8P9P9P:P<P6Fhp=FP;g03:>R=P;P;P3f4R3P4P>g03L:P7P<P6M<\p=vP=P;P;P;P4P4f5R4P3P>P7P<P6M<\p=qP;P;P;P;P;P;P2P6P<P7P2P>P3P4f6R2f7RAf8RBf9RCMB|p=pP<P8P9P9P:P6E}p=YP;P<g03DhP6CIp=Mg00UbRD#;RE#;RF#;RG#;#;#;RH#]RI#R%]G#RRG#cRJ[g00VGRKP7p,2loRLp,3spzRMH01P1%5LRN%VERO%VHRH'mRP,0MRQ10L6176M'3RR%:<RS9?K4%^GRT52J#C%:7RU9AK21yG6RV52JX9G,<G'3[^:;'311>7,0L103M%53PKPAP2P4CO[[[P6A?KBS=2JT#CAAKCU=2JVX9G,<G'3\R^:;,3QP1PQA?KCS=2JT#Cf:R1=AKU=2JVX9G,<G'3\R^:;11A2,0L10BM%5BPKf;RWP1PCCO[[[P6f<RX=?KS=2JT#Cf=RS=AKU=2JVX9G,<G'3\R^:;111C,0L10WM%5WPN11MLRW,4L/0PR1%56RC176W'3RRf@RU14L<RY#:5?K=2JT#CRT[^D;RZ'31lOHR[175OR\%5H175P[R][R^%5OR_g00ZaR`AkOH<UW=RH%5P\`^=_R_P<g00[=1j5O'9P\eO1R\P]g00[cR`#gRa%f`Rb1=;<%e;Rc%d;Rd1Q;5Re1>;DRf56dRg%^9RhPgC81bd:RgP6P719?@1a67#EdA`;5<C_R@b5b6b7X0;%5<R?\C^0;P6PLPXO2b4b1b8b1P1PZP[P^PHP_P\P]PaPbP;1=;7RZP<&00;R1CDPcPd1>;ERC1Q;O=~;IRI56dPhAB;Cf9J;f=6dIC8PgP@b5b6b7X0;X2;10<P117<,4</0P[^0;^2;P6PMPLPBO3b4b1b8b1fARP14L7#:5AK=2JVX9G,<GP4PYP[P^PHP_P\P]PaPbP;PZP<1=;>CDRZPcPdA6deCRYP;PCg00U;RG%[D,>;RD=B;fCI,@d5FdPhAJ;fCRV96dfP;PVPGPDCI,@d5FdC8PgP@b5b6b7X0;X2;X3;1176,7<,3?14<7R?,0<17?>'3[^0;^2;^3;P6PMP4PLP3O4b4b1b8b1O25{TXJRXD;CZCZPKf>RRPLPWCzPKf?RTPLPW11RS/1LR?%KSRGP6P[P^PHP_P\P]PaPbPZPcPdAB;fCRV96dDPhAB;VDRJ96deC8PgP@b5b6b7X0;X2;X3;116<RI,0711<7/1>#5[^0;^2;^3;P6PLPPfBROPAO4b4b1b8b1%XGRi,4?Rj/0W1L5SRk,4?Rl/0WP;P;P0P6X;;RmP010<6#xXR;X;;PjPlPmPmPmP;P;g03DD14<6Cw,9;XE;XP;P?P?19;?PiPkPmPm%X6,9;X;=PGPkPm1L56X;;PSPS19;SDvEqM:pPWPW19;WM<o1n5S175SA2;kS'310S5A2;k5'3'T1L5RP;P[P^PHP_P\P]p-0Rkg01GnRW#PRm#PR=#P,H;Ri1H;=1H;m1H;W5G;RW5G;5G;g039RRm'SAG;iW/Sm=U`a5U`PbP;P;1=;3P7P1CDP<P;1=;4P>P1CDCDPcPdPdP8P9P9P:1YdA1>;FRF/MC,@d5Fd1YdB1MFe,@d5FdFrPhPdPYPhPd%[E,>;RE96dfPhAJ;JFAB;ED56dC8C8C8PgP@b5b6b7X0;X2;X3;XB;XC;X?kW@A2;><,34A2;>5,32'T%57107211>3/14/4211A4'0[[[^0;^2;^3;^B;^C;^?k^@kP6fCRk/05175kPMP3PLPkfDP4PAPBO:b4bAb1bAbTbGCsM9tPKPT14L?#:PGCN#EP[P^PHP_P\P]PaPbPZPcAJ;DJ,MV,@dPgP@b5b6b7X0;X2;X3;11I7,4792;I^0;^2;^3;P6PLPOPkO3b4b1b8b111TRRk11kL,4L52;P;11UTRk/1L,4LPKPO%:6%KUCN#EXS;P<PkP6EuPKPP%:k%KTCN#EP6b>b<b>bOPKPRPSPXCOeWIWHWFWNXMQP<P6O2n2001000000121000000W<XLNP<P6O2n2001000000121000000W<XK;XQ;WEo"). Qed.

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
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 errv' LB' LBm p
      at_np fcsr kernel pre.
    pose proof pre as (_ & _ & spz16 & spf_low & spz_high & _ & inv_m & stk_m & _ & _ & _ & _ & ceil_lo & lo_room
      & _ & _ & _ & live_obj & obj_ceil & map_m & _ & _ & bc_last & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & fs_m & const_m & _).
    unfold AREH_STACK, AOPNEW_STACK, AMALLOC_STACK in lo_room. unfold spf in *.
    pose proof aceil_facts as ((ceil_low & ceil_high) & _ & _).
    pose proof (obj_place H HH LF obj m fs_m live_obj) as (_ & _ & _ & obj_img).
    unfold AIMG_TOP in obj_img.
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq map_m)) as bc_range.
    (* Writes this stage makes stay in the forty bytes under the frame base. *)
    set (W := [(spz - 96 - 40, spz - 96)]).
    assert (W_fits : Forall (fun iv => aceil <= fst iv /\ snd iv <= spf spz /\ fst iv <= snd iv) W).
    { unfold W. apply Forall_cons; [| apply Forall_nil]. cbv beta. unfold spf. cbn [fst snd]. lia. }
    remember (mkR y1 (Z_to_bv 64 (spz - 96)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 8)) y10
                  (Z_to_bv 64 (nreq bc)) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) y20
                  (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) (Z_to_bv 64 p)
                  (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31) as regs0 eqn:regs0_is.
    assert (full0 : rfull regs0) by (rewrite regs0_is; apply rfull_mkR).
    pose (E := Eseed regs0 [Z_to_bv 64 obj; Z_to_bv 64 (nreq bc); Z_to_bv 64 (spz - 96)]).
    assert (sp_seed : ev E 34 = Z_to_bv 64 (spz - 96)) by (subst E; evs; reflexivity).
    assert (room32 : stack_room asegs m (spz - 96) 32) by (eapply stack_room_of_stk; [exact stk_m | lia | lia | lia]).
    destruct (ACONST_shbase m const_m) as [got_cell shcell_cell].
    assert (known : know_ok asegs E m KNP).
    { unfold KNP, know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m AGOT_SHBASE _ 0%nat (C8 (wz ASHBASE_CELL)));
          [ exact got_cell | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off edenot]; rewrite u64_of_Z by lia; reflexivity
          | unfold AGOT_SHBASE; lia | unfold AGOT_SHBASE; cbn [Z.of_nat]; lia | reflexivity ]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m ASHBASE_CELL _ 0%nat (C8 (wz ASHADOW_BASE)));
          [ exact shcell_cell | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off edenot]; rewrite u64_of_Z by lia; reflexivity
          | unfold ASHBASE_CELL; lia | unfold ASHBASE_CELL; cbn [Z.of_nat]; lia | reflexivity ]. }
      apply Forall_cons; [exact (krange_var asegs E m 34 (spz - 96) (2 ^ 45) (2 ^ 47) sp_seed ltac:(lia) ltac:(lia)) |].
      apply Forall_cons; [exact (kwr_stack asegs E m 34 (spz - 96) 32 (-32) sp_seed eq_refl ltac:(lia) ltac:(lia) room32) |].
      apply Forall_nil. }
    (* The four saved registers land in the new frame, whichever way the bucket count goes. *)
    assert (wr_frame : wr_at asegs m (spz - 96 - 32) 32).
    { eapply wr_at_subE; [exact (wr_at_of_stk asegs m lo spz stk_m) | lia | lia | lia]. }
    assert (saved_vals : map (fun v => C8 (edenot E v)) tlNP
                         = [C8 (Z_to_bv 64 (obj + 24)); C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 E_IDX)]).
    { unfold tlNP. cbn [map]. subst E. evs. rewrite w_add by lia. rewrite regs0_is. reflexivity. }
    assert (saved_cells : rw_cells asegs (mem_denot E m lgNP) (spz - 96 - 32)
                            [C8 (Z_to_bv 64 (obj + 24)); C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 E_IDX)]).
    { assert (flat_log : log_flat E lgNP).
      { unfold lgNP. cbn [log_flat]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite sp_seed, u64_of_Z by lia.
        cbn [Z.of_nat]. repeat split; lia. }
      rewrite <- saved_vals. rewrite lgNP_c8 in flat_log |- *.
      apply rw_cells_c8log; [exact flat_log | unfold estart; cbn [a_base a_off edenot]; rewrite sp_seed, u64_of_Z by lia; lia |].
      exact wr_frame. }
    assert (log_in_W : munch W m (mem_denot E m lgNP)).
    { apply munch_mem_denot.
      - unfold lgNP. cbn [log_flat]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite sp_seed, u64_of_Z by lia.
        cbn [Z.of_nat]. repeat split; lia.
      - unfold lgNP. repeat (apply Forall_cons; [cbv beta; unfold W, estart; cbn [e_addr e_width a_base a_off edenot inside];
                                                 rewrite sp_seed, u64_of_Z by lia; cbn [Z.of_nat]; lia |]).
        apply Forall_nil. }
    pose proof (wmono_mem_denot E m lgNP) as views_log.
    pose proof (stk_mem_denot E m lgNP lo spz stk_m) as stk_log.
    destruct (Z.eq_dec bc 0) as [empty | nonempty].
    - (* No buckets yet: the code takes two buckets at once and skips the prime search. *)
      assert (seeded : regs_ok E srNP0 regs0).
      { unfold srNP0. apply regs_ok_srs; [apply regs_ok_seed |].
        apply Forall_cons; [cbn [fst snd]; split; [intros zero_reg; discriminate zero_reg | rewrite regs0_is; evs; reflexivity] |].
        apply Forall_cons; [cbn [fst snd]; split; [intros zero_reg; discriminate zero_reg | rewrite regs0_is; evs; reflexivity] |].
        apply Forall_cons; [cbn [fst snd]; split; [intros zero_reg; discriminate zero_reg | rewrite regs0_is; evs; rewrite w_add by lia; reflexivity] |].
        apply Forall_cons; [cbn [fst snd]; split; [intros zero_reg; discriminate zero_reg | rewrite regs0_is, empty; reflexivity] |].
        apply Forall_nil. }
      xrun_at (PropExec.mkFP F fc) asegs regs0 E_NP m (seg_rom asegs) seeded known 40%nat [E_RC] (SCR [] [] []) 35%N.
      { split_scs. }
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) => change mm with (mem_denot E m lgNP) in Hms end.
      readback HR' (msteps_full asegs _ _ Hms full0) regs0_is regs_after.
      rreg HR' 2%bv sp_after. rreg HR' 8%bv s0_after. rreg HR' 9%bv s1_after. rreg HR' 10%bv a0_after. rreg HR' 11%bv a1_after.
      rewrite w_addm in sp_after by lia. replace (spz - 96 + -32) with (spz - 96 - 32) in sp_after by lia.
      assert (two_is : Z_to_bv 64 2 = Z_to_bv 64 (bseq_next bc)) by (rewrite empty; reflexivity).
      rewrite sp_after, s0_after, s1_after, a0_after, a1_after, two_is in regs_after.
      eapply (sr_blk_eq H HH); [exact kernel | exact at_np | exact full0 | exact Hms | exact regs_after |].
      intros msF1 mo1 kernel1 step1 at_rc.
      pose proof (gpre_stack s mo m _ errv' LB' LBm p W pre log_in_W views_log
                    (msteps_mem_inv asegs _ _ Hms inv_m) stk_log W_fits) as (pres_mo & rest).
      eapply (stage_rcall H HH REH).
      + unfold spf. exact at_rc.
      + exact fcsr.
      + exact kernel1.
      + exact (conj (ah_mpres_trans H HH _ _ _ pres_mo step1) rest).
      + unfold spf. exact saved_cells.
    - (* Buckets exist: grow to the next prime of the sequence, then join the same rehash call. *)
      assert (arg_is : nreq bc = np_arg bc) by (unfold nreq; rewrite (proj2 (Z.eqb_neq bc 0) nonempty); reflexivity).
      assert (arg_range : 3 <= np_arg bc <= 2 * 26339969 + 1) by (unfold np_arg; lia).
      assert (seeded : regs_ok E srNP1 regs0).
      { unfold srNP1. apply regs_ok_srs; [apply regs_ok_seed |].
        apply Forall_cons; [cbn [fst snd]; split; [intros zero_reg; discriminate zero_reg | rewrite regs0_is; evs; reflexivity] |].
        apply Forall_cons; [cbn [fst snd]; split; [intros zero_reg; discriminate zero_reg | rewrite regs0_is; evs; reflexivity] |].
        apply Forall_cons; [cbn [fst snd]; split; [intros zero_reg; discriminate zero_reg | rewrite regs0_is; evs; rewrite w_add by lia; reflexivity] |].
        apply Forall_cons; [cbn [fst snd]; split; [intros zero_reg; discriminate zero_reg | rewrite regs0_is; evs; reflexivity] |].
        apply Forall_nil. }
      xrun_at (PropExec.mkFP F fc) asegs regs0 E_NP m (seg_rom asegs) seeded known 40%nat [LbB_HNextPrime.NP_A]
        (SCR [true; false] [] []) 35%N.
      { assert (odd_and : Z.land (2 * bc + 1) (2 * bc) = 2 * bc).
        { apply Z.bits_inj'. intros n n_nonneg. rewrite Z.land_spec.
          destruct (Z.eq_dec n 0) as [n_zero | n_pos].
          - rewrite n_zero, Z.testbit_even_0. apply andb_false_r.
          - replace n with (Z.succ (Z.pred n)) by lia.
            rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia. apply andb_diag. }
        split_scs; cbn [sc_denot]; subst E; evs; rewrite arg_is.
        - rewrite w_addm by lia. rewrite w_and by lia. unfold np_arg in *.
          replace (2 * bc + 1 + -1) with (2 * bc) by lia. rewrite odd_and.
          rewrite br_eq by lia. apply Z.eqb_neq. lia.
        - rewrite br_ne by lia. apply negb_true_iff, Z.eqb_neq. lia. }
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) => change mm with (mem_denot E m lgNP) in Hms end.
      set (M1 := mem_denot E m lgNP) in *.
      readback HR' (msteps_full asegs _ _ Hms full0) regs0_is regs_after.
      rreg HR' 1%bv ra_after. rreg HR' 2%bv sp_after. rreg HR' 8%bv s0_after. rreg HR' 9%bv s1_after.
      rreg HR' 10%bv a0_after.
      rewrite w_addm in sp_after by lia. replace (spz - 96 + -32) with (spz - 96 - 32) in sp_after by lia.
      rewrite ra_after, sp_after, s0_after, s1_after, a0_after in regs_after.
      eapply (sr_blk_eq H HH); [exact kernel | exact at_np | exact full0 | exact Hms | exact regs_after |].
      intros msF1 mo1 kernel1 step1 at_call.
      pose proof (msteps_mem_inv asegs _ _ Hms inv_m) as inv1.
      assert (room16 : stack_room asegs M1 (spz - 96 - 32) 16) by (eapply stack_room_of_stk; [exact stk_log | lia | lia | lia]).
      assert (room8 : stack_room asegs M1 (spz - 96 - 32) 8) by (eapply stack_room_of_stk; [exact stk_log | lia | lia | lia]).
      eapply (np_sr H HH QIx s msF1 mo1 _ F fc M1 bc (spz - 96 - 32) (Z_to_bv 64 E_NPR)).
      + exact kernel1.
      + exact at_call.
      + exact (u_bseq map_m).
      + exact nonempty.
      + unfold LbB_HNextPrime.BSEQ_LAST_A. unfold BSEQ_LAST in bc_last. exact bc_last.
      + rewrite <- arg_is. reflexivity.
      + reflexivity.
      + unfold ret_ok. apply bv_eq. vm_compute. reflexivity.
      + reflexivity.
      + replace (spz - 96 - 32) with (spz + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact spz16.
      + lia.
      + lia.
      + exact room16.
      + exact inv1.
      + apply rfull_mkR.
      + intros msF2 mo2 R2 kernel2 step2 at_ret kept2 a0_ret full2.
        rewrite wbytes_eq in at_ret.
        replace (spz - 96 - 32 - 8) with (spz - 96 - 40) in at_ret by lia.
        set (M2 := write_to_mem M1 (Z_to_bv 64 (spz - 96 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 E_NPR))) in *.
        assert (len8 : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 E_NPR))) = 8)
          by (rewrite CatExec.length_N_to_le_bytes; reflexivity).
        assert (inv2 : mem_inv asegs M2).
        { unfold M2. apply mem_inv_store; [exact inv1 |]. rewrite CatExec.length_N_to_le_bytes.
          unfold stack_room in room8. replace (spz - 96 - 32 - 8) with (spz - 96 - 40) in room8 by lia. exact room8. }
        assert (stk2 : stk asegs M2 lo spz) by (unfold M2; apply stk_write; [exact stk_log | lia | rewrite len8; lia]).
        assert (W_2 : munch W m M2)
          by (unfold M2; apply munch_write; [exact log_in_W | lia | rewrite len8; lia | rewrite len8; unfold W; cbn [inside]; left; lia]).
        assert (views_2 : wmono asegs m M2) by (unfold M2; apply wmono_write; exact views_log).
        assert (cells_2 : rw_cells asegs M2 (spz - 96 - 32)
                            [C8 (Z_to_bv 64 (obj + 24)); C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 E_IDX)]).
        { apply (rw_cells_transport asegs [(spz - 96 - 40, spz - 96 - 32)] M1 M2); [exact saved_cells | | |].
          - unfold M2. apply munch_write; [intros x _; reflexivity | lia | rewrite len8; lia | rewrite len8; cbn [inside]; left; lia].
          - unfold M2. apply wmono_write. intros x defined. exact defined.
          - cbn [disjoint_from cells_size csize Nat.add]. lia. }
        (* The prime search keeps every callee-saved register, so the frame the rehash call wants is still there. *)
        assert (R2_vals : R2 = mkR (getr R2 1%bv) (Z_to_bv 64 (spz - 96 - 32)) gp tp (getr R2 5%bv) (getr R2 6%bv) (getr R2 7%bv)
                                   (Z_to_bv 64 obj) (Z_to_bv 64 2147450880) (getr R2 10%bv) (getr R2 11%bv) (getr R2 12%bv)
                                   (getr R2 13%bv) (getr R2 14%bv) (getr R2 15%bv) (getr R2 16%bv) (getr R2 17%bv)
                                   (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) (getr R2 20%bv) (Z_to_bv 64 (obj / 8))
                                   (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) (Z_to_bv 64 p)
                                   (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11
                                   (getr R2 28%bv) (getr R2 29%bv) (getr R2 30%bv) (getr R2 31%bv)).
        { rewrite (rfull_eq R2 full2) at 1. f_equal;
            lazymatch goal with |- getr R2 ?r = _ => rewrite (kept2 r ltac:(inb)); reflexivity end. }
        pose (E2 := Eseed R2 [Z_to_bv 64 obj; Z_to_bv 64 (bseq_next bc)]).
        assert (seeded2 : regs_ok E2 (srs sr_id [(8%bv, EVar 32); (10%bv, EVar 33)]) R2).
        { apply regs_ok_srs; [apply regs_ok_seed |].
          apply Forall_cons; [cbn [fst snd]; split; [intros zero_reg; discriminate zero_reg | rewrite R2_vals at 1; subst E2; evs; reflexivity] |].
          apply Forall_cons; [cbn [fst snd]; split; [intros zero_reg; discriminate zero_reg | subst E2; evs; exact a0_ret] |].
          apply Forall_nil. }
        assert (known2 : know_ok asegs E2 M2 []) by apply Forall_nil.
        xrun_at (PropExec.mkFP F fc) asegs R2 E_NPR M2 (seg_rom asegs) seeded2 known2 10%nat [E_RC] (SCR [] [] []) 35%N.
        { split_scs. }
        readback HR'0 (msteps_full asegs _ _ Hms0 full2) R2_vals regs_back.
        rreg HR'0 8%bv s0_back. rreg HR'0 10%bv a0_back. rreg HR'0 11%bv a1_back.
        rewrite s0_back, a0_back, a1_back in regs_back.
        eapply (sr_blk_eq H HH); [exact kernel2 | exact at_ret | exact full2 | exact Hms0 | exact regs_back |].
        intros msF3 mo3 kernel3 step3 at_rc.
        pose proof (gpre_stack s mo m M2 errv' LB' LBm p W pre W_2 views_2 inv2 stk2 W_fits) as (pres_mo & rest).
        eapply (stage_rcall H HH REH).
        * unfold spf. exact at_rc.
        * exact fcsr.
        * exact kernel3.
        * exact (conj (ah_mpres_trans H HH _ _ _ (ah_mpres_trans H HH _ _ _ (ah_mpres_trans H HH _ _ _ pres_mo step1) step2) step3) rest).
        * unfold spf. exact cells_2.
  Qed.
End EmpN.
