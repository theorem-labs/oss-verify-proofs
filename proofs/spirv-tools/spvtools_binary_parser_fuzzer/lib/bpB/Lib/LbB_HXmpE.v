(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3 Hoare RefMemcpyLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HFpu HCommon.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HRehStmt LbB_HKit LbB_VecT LbB_HXmpS LbB_HEmpK LbB_HXmpD LbB_HXmpI LbB_HXmpI2
  LbB_HXmpI3 LbB_HXmpI4 LbB_HXmpX LbB_HXmpR LbB_HXmpN LbB_HXmpF LbB_HXmpL LbB_HStKit LbB_HXmpNd.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_TopKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_RGl.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_HXmpE () := "C46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockI46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;Permutation>Permutation_inC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes4list02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKit5c8logK47Corelib4Init5Logic2eq01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00K47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE5a2PROc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE5tlPROK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addC5ARocqVerifyHarness?AgentSubmission7LibHash5HWord5w_srlC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K4ELinuxProcessSemantics5Riscv5Instr5aluop01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop07C5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evC4ELinuxProcessSemantics5Riscv3Sem7mul_divK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE6popcwDI5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes3nat00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE5popcDC46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or01C45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init5Logic2or02K46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4BSEQI47Corelib4Init5Logic5False00K45stdpp9bitvector;definitions2bv01C4ARocqVerifyHarness?AgentSubmission8PropExec4getrC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC56Stdlib6NArith6BinNat1N6to_natK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6reg_evK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC4ELinuxProcessSemantics5Riscv3Sem<branch_takenK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5br_eqC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstI47Corelib4Init5Logic2ex00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE6aonlyDC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpS9syms_sameC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpS?syms_same_soundK47Corelib4Init5Logic2ex01I4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00C5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsK47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idK47Corelib4Init9Datatypes3nat01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE3srDI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K46Stdlib9micromega:ZMicromega;ZArithProof01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpS4E_BBC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpS4E_NFc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE6SCR_D0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE5E_DSPK47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE7non_dspC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HFind;BSEQ_boundAC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE<popcwD_casesC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4hmodC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega6VarMap1t03C4ARocqVerifyHarness?AgentSubmission7SymRun3@branch_ltu_lit_lc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE9popcD_envC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sr_getC47Corelib4Init5Logic8eq_transC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z9land_commC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_andK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6w_addmC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMStateCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6br_ltuC56Stdlib6ZArith6BinInt1Z9mod_smallK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr06C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv7Prelude4sextC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HFind:remuw_valAK47Corelib4Init9Datatypes4bool02c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE6SCR_D2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE7SCR_Dltc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE7SCR_DgeK4ELinuxProcessSemantics5Riscv5Instr5mulop08C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_RHEAPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface=aclient_rangeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap6ah_fsbC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7afsb_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;aimg_clientC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_sizeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3nshC56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib5Lists4List9in_or_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap9ah_blocksC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ablock_rangeC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula06C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs<ASHADOW_BASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow@ASHADOW_BASE_valC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8AFS_SIZEI47Corelib4Init9Datatypes:comparison00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt9emp_entryC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6nval24C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB3lblC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt7umap_shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt>map_live_frameC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_ContStmt4fldAC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow:accessibleC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt7emp_srcC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7ZlengthK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_ALC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface8lb_smallC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9bseq_nextC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface6nsmallC56Stdlib6ZArith6BinInt1Z6of_natC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface6nlargeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface3nlgC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface3ICMC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_TRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt:emp_del_raC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8trace_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;as_rauxv_okC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_RFSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack06stack0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own6lb_ownC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt8emp_postC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_hiC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5u_hdrI5ARocqVerifyHarness?AgentSubmission7LibHash4HRep3hdr00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell8C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6hdaddrC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell4C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7definedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvBsh0_of_addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit2gzI47Corelib4Init9Datatypes6option00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2b8K47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7byte_okC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst=ACONST_shbaseC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2wzK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD9obj_placeC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5apartc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE6acl_loC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge9rfull_mkRK4ARocqVerifyHarness?AgentSubmission8PropExec7FPState01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface=aimg_client_wC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface@aclient_write_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7ff_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8ff_classC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3fszC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<afs_write_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst>aconst_ok_highC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9aconst_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack09stack0_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<client_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack0@stack0_transportC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_TopKit9stk_wmonoC56Stdlib6ZArith6BinInt1Z7pos_subC57Corelib7BinNums6PosDef3Pos3addC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C46Stdlib9micromega;ZifyClasses;rew_iff_revC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=disjoint_fromC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrameBrw_cells_transportC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep:xpres_reflC46Stdlib7Sorting;Permutation@Permutation_reflC46Stdlib5Lists4List9app_nil_rC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKit4wmixC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep7rin_ivsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKitAxpres_munch_mixedC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep5xpresC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep<xpres_weakenC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<aclient_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8in_blockC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;in_block_shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep7xclientC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB:lbl_in_invC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:in_map_iffC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts<nval24_agreeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HStKit:blkx_introC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HStKit8umapx_xpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HStKit;blksh_introC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HStKit:umap_sh_xpC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_alK46Stdlib9micromega:ZMicromega;ZArithProof03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HStKit>addressable_xpI47Corelib5Lists7ListDef6Forall00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep;xpres_wr_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own<lb_own_wmonoC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame7outsideC4ARocqVerifyHarness?AgentSubmission8LibIface4zwinC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission7LibCont4CRep8agree_onC5ARocqVerifyHarness?AgentSubmission7LibCont4CRep9fld_agreeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadowDaccessible_transportC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_MPRESC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD5FRAMEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD3spfC56Stdlib6ZArith6BinInt1Z2geC56Stdlib6ZArith6BinInt1Z7le_reflC56Stdlib6ZArith6BinInt1Z5le_geC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpNd4NPREC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE5dsp_zC4ARocqVerifyHarness?AgentSubmission6CatSim<msteps_transC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpNd:stage_nodeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib6LbB_SR6sr_blkc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE6dsp_nzC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpS4SENVC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpS;emp_from_bbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpS6efoundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6aonlyTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD;stage_foundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpNd8src4_shkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3shkC56Stdlib6ZArith6BinInt1Z4of_NC4ARocqVerifyHarness?AgentSubmission8PropExec3rdnC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cellwK5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01C56Stdlib6NArith6BinNat1N2leC4ARocqVerifyHarness?AgentSubmission8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8v_addi_ZC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26adenotC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib=sc_read_cellwK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond06C35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseI47Corelib4Init5Peano2le00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvAkword_of_rw_cellsK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv:kwr_of_stkK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3sh0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6kn_fixC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8kshadow0K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit7kshadowK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr07C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit<br_lts_smallC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit9land7_valC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit@ext_shadow_smallC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5br_neC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame6insideC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?munch_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge>msteps_mem_invc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE8sh_wordEC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init9Datatypes6lengthC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKit>rw_cells_c8logC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge;msteps_fullC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call=regs_keep_mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt8emp_stmtI5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5umapx00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep;umap_blocksC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_bseqC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3mrdC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3aC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3bC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3cC46Stdlib5Lists4List7existsbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call6inb_InC5ARocqVerifyHarness?AgentSubmission8SymExec33SX27ext_valC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26e_addrC5ARocqVerifyHarness?AgentSubmission8SymExec33SX27e_widthI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4AC_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4LY_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4MI_AC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst;AGOT_SHBASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst<ASHBASE_CELLC46Stdlib9micromega8ZifyInst7Inj_Z_ZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8non_argTC56Stdlib6ZArith4Znat3N2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_lec6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE5lgPROc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE6srPRO'K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ARocqVerifyHarness?AgentSubmission8LibIface3memI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6fframeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt7EMP_EXTC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts9BSEQ_LASTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<RT_SMALL_MAXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface:RT_CNT_MAXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<RT_LARGE_MAXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface9APC0_FREEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt:AEMP_STACKC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3ATPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ATLS_PRIV_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ATLS_PRIV_HIC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface4bptrC46Stdlib5Lists4List8map_consC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpS7E_FOUNDc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE5srPROc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE6SCR_P0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE5KN_P0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE6SCR_P1c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE5KN_P1c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE8lgPRO_c8".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_DSP : Z := 0xfb6c0.

Definition srPRO : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 37)].
Definition SCR_P0 := SCR [] [EVar 34; EVar 35] [].
Definition SCR_P1 := SCR [true; true] [EVar 34; EVar 35] [].
Definition KN_GOT : list kentry := [KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit SHBASE)].
Definition KN_PRO : list kentry :=
  KN_GOT ++ [KWr (SA (EVar 37) (-96)) (ELit 96);
             KRange (EVar 32) 1 (2 ^ 47); KRange (EVar 33) 0 (2 ^ 47); KRange (EVar 37) (2 ^ 45) (2 ^ 47);
             KDisj (SA (EVar 33) 0) (ELit 4) (SA (EVar 37) (-96)) (ELit 96);
             KDisj (SA (EVar 32) 0) (ELit 40) (SA (EVar 37) (-96)) (ELit 96)].
Definition KN_P0 : list kentry := KN_PRO.
Definition KN_P1 : list kentry := KN_PRO ++ [KWord (SA (EAlu ALU_SRL (EVar 33) (ELit 3)) SHBASE) 1 (EVar 36)].
Definition KN_SK0 : kentry := KWord (SA (EAlu ALU_SRL (EVar 33) (ELit 3)) SHBASE) 1 (ELit 0).
Definition KN_SO8 : kentry := KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) SHBASE) 1 (ELit 0).

Definition runPRO :=
  Eval vm_compute in (sym_exec ASEGS 60 true [E_DSP] SCR_P0 (SS 0xfb648 srPRO [] (kn_fix 20 [E_DSP] SCR_P0 0xfb648 srPRO KN_P0 50) 50) []).
Definition srPRO' : list expr := Eval cbv in (let '(ss, _, _) := runPRO in s_regs ss).
Definition lgPRO : list sentry := Eval cbv in (let '(ss, _, _) := runPRO in s_log ss).

Definition tlPRO : list expr := [EVar 26; EVar 25; EVar 24; EVar 23; EVar 22; EVar 21; EVar 20; EVar 19; EVar 18; EVar 9; EVar 8; EVar 1].
Lemma lgPRO_c8 : lgPRO = c8log (EVar 37) (-96) tlPRO.
Proof. vm_compute. reflexivity. Qed.
Lemma sh_wordE : forall x, 0 <= x < 2 ^ 64 ->
  alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 2147450880) = Z_to_bv 64 (x / 8 + SHBASE).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HXmpE ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with56__sat0h66__sat1h72Hah84__p1h96__sat2h:6__sat3h;6__sat4h<1bh=1Hh>2Hxh?1xp;1p;2p;3p;6p;4p;5p;7p;8g005Wj1:Tg00>Yj1;Tg00?7j2BTg00?Tj21Tg00@0j24Tg006aj1ETg00@Kj1STg006<j1>Tg00@nj29Tg00AKj25Tg00B1j3CTg00BYj2@Tg00C6j3ATg00CPj2FTg00D8j3JTg00D\j1YTg0057j1XTg00E<j2WTg00EZj1VTg00F8j1UTg00Fcj2<Tg00GFj2TTg00Gij6RTg00HMj1OTg00Hoj2NTg00:0j2DTg00IQj2MTg00J=j3LTg00J\j4PTg00KNj1QTg00Klj4KTg00LMj3HTg00M0j3eTg00MSj2dTg00N0j5cTg00N\j4bTg00O7j2aTg00Ohj3_Tg00PKj5^Tg000dj6GTg00QBj4]Tg00R:j2\Tg00RVj4ITg00SAj7[Tg00Sej7ZTg00TIj8`Tg00TmR0f0R1'\p=0%:1#:p=3%>1#>p=6g00UKR2f1R3g00UiP1CIp=?P3g00VPR4g00VoR5P5g00WOR6P1g00WoF[p=2f2R7P4P5P5P6P3P1FZp=7f3R8P4P5P5P6P7P3P1G`p==P2P3g00XOP1CIp=8%01R9g00;DR:#:R;#;R<%3;R;#:#3R=#;R>'BR?,11R@'4RA%E=R=#SRB%>:RC#;RD,B<,93,5=g00Y6RE%6CRC#6#6#6#6#6#6#:#3#3#3#3#3#3#3#;RF,5=RG7C1%;;R;,97RHg00Yb'@,5=RI5ABX<B193;RJ#0RK%:C#>RC#;RL,B<RM,1JRJP3P;1F<>RN110<RO%0>110?[[RP%0<RQg00Z]RRAJ<>3UW7RS%0?\R^7QRTp-0RUg00[9RV#YRW%XVRV1W23RX%V2RY%U2RZ1<20R[1T2:R:'?,2ZR\PZP4P5P5P6P8ERR457Z%O5R5P\C=1NZ6R6P1P7g00[eR]g00\ER^'D1M17=A]^dAL203CPR^b2b3b4X02W81493%03R][^02^8UP1f4R_/1?P_P8O3b1b5b6PWPV%Q2R`PY1<2;Ra,8[,2ZP6P^b2b3b4110;P1b1RbCKP3P;PMPb1F<LRb%0L110M[\OROAJ<L3VRX7QRL%0M\R^7QRQPNPPPSPTPWPVPXPYPZ1<2<R<=H2=RR,8:,2ZR097Z4P5%EC9H2<R<9e2a,8:,2ZC=P6P^b2b3b4X02X8U143@1d;M,13[^02^8UP1f6RU#0PUf5O3b1b5b6b9b:DcCb14KJPB1@HF,5=RJ198;/@F,5=9AB1X<B1DBJ15=H=CEGRGPHPF1a7;RH%07%0;19_;#0[[R7PbPOPLPQPNPPPSPTPWPVPXPYPZ18:<,2Z97Z\R<P5A7Z\0R0C=P6P^b2b3b4X02111M,49R9113?,4]R][^02P1f8/9;PUO2RUb1b5b6b9b:b;PNPPPSPTPWPVP`PY1<2FR;,?[,2Z18;R,2Z57ZP6P^b2b3b4%0F11F?'4P1b1b5b6PHP7PbPOPLPQPNPPPSPTPWPVPXPYPZP<P5A_2:;R;,?[,2Z18;R,2Z57ZC=P6P^b2b3b4X021@3FRF#011F?'4\9^02PUb1b5b6b9b:b;D^EGAABGIeb=g00\e15=315=D3CP3PDPNPPPSPTPWPVPXPYPZP0P5P0C=P6P^b2b3b4X02P]\A^02P1P_P8O2b1b5b6PWPVP`PY1<2DRY,?[,2Z1<2>,8Y,2Z57ZP6P^b2b3b4%0D11D>'4P1b1C]EGW>X?2o"). Qed.

Definition srD : list expr := srs sr_id [(20%bv, EVar 34); (22%bv, EVar 33)].

Definition popcD : expr :=
  Eval vm_compute in
    (let '(ss, _, _) := sym_exec ASEGS 100 true [0xfb738] (SCR [false] [] []) (SS E_DSP srD [] [] 50) [] in
     sr_get (s_regs ss) 11%bv).
Definition popcwD (w : word) : word := edenot (Env (fun _ => w) (fun _ => [])) popcD.
Lemma popcD_env : forall E, edenot E popcD = popcwD (ev E 34).
Proof. intros E. unfold popcwD, popcD. cbn [edenot ev]. reflexivity. Qed.
Ltac vm_popcD :=
  match goal with |- context [bv_unsigned (popcwD ?w)] =>
    let v := eval vm_compute in (bv_unsigned (popcwD w)) in
    replace (bv_unsigned (popcwD w)) with v by (vm_compute; reflexivity) end.
Lemma popcwD_cases : forall bc, In bc BSEQ -> bc <> 0 ->
  (bc = 2 /\ bv_unsigned (popcwD (Z_to_bv 64 bc)) = 1) \/ (bc <> 2 /\ 2 <= bv_unsigned (popcwD (Z_to_bv 64 bc))).
Proof.
  intros bc Hin Hnz. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; lia
            | left; split; [reflexivity | vm_popcD; reflexivity]
            | right; split; [lia | vm_popcD; lia] ] |]).
  destruct Hin.
Qed.

Definition non_dsp : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition aonlyD (R R' : bvmap 5 word) : Prop := forall r, In r non_dsp -> getr R' r = getr R r.
Definition SCR_D0 := SCR [true] [] [].
Definition SCR_D2 := SCR [false; false] [] [].
Definition SCR_Dlt := SCR [false; true; true] [] [].
Definition SCR_Dge := SCR [false; true; false] [] [].

Section Dsp.
  Context {fx : PropExec.FPState}.
  Context {AC : AllocCeiling}.
  Variable rom : word -> option byte.
  Variables (M : mem) (key bc : Z).
  #[local] Abbreviation st R pc := (@PropExec.mkst fx R (Z_to_bv 64 pc) M rom).

  Ltac runD R scr :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in let Hpc := fresh "Hpc" in
    pose (E := Eseed R [Z_to_bv 64 0; Z_to_bv 64 key; Z_to_bv 64 bc]);
    assert (HR : regs_ok E srD R) by
      (apply regs_ok_srs; [apply regs_ok_seed|];
       repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | evs; assumption] |]); apply Forall_nil);
    assert (HK : know_ok ASEGS E M (@nil kentry)) by (unfold know_ok; apply Forall_nil);
    assert (Hpc : forall b : bool, branch_taken BC_LTU (edenot E (ELit 1)) (edenot E popcD) = b ->
                  sc_denot ASEGS M E (SCBr b BC_LTU (ELit 1) popcD)) by (intros b Hb; exact Hb);
    xrun HR HK 60%nat [E_BB; E_NF] scr 50%N;
    [ split_scs; try sc_auto1;
      try (apply Hpc; rewrite popcD_env; evs; rewrite branch_ltu_lit_l by lia; bool_lia);
      try (cbn [sc_denot]; evs; rewrite ?br_ne, ?br_eq, ?br_ltu, ?br_geu by lia; bool_lia)
    | ].

  Lemma dsp_z : forall R, getr R 20%bv = Z_to_bv 64 bc -> getr R 22%bv = Z_to_bv 64 key -> bc = 0 ->
    exists R', CatSim.msteps ASEGS (st R E_DSP) (st R' E_NF) /\ aonlyD R R'.
  Proof.
    intros R H20 H22 Hbc. runD R SCR_D0.
    exists R'. split; [exact Hms|]. intros r Hr. refine (LbB_HXmpS.syms_same_sound _ _ _ _ _ non_dsp HR HR' _ r Hr). vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma dsp_nz : forall R, In bc BSEQ -> bc <> 0 -> 0 <= key < 2 ^ 32 -> getr R 20%bv = Z_to_bv 64 bc -> getr R 22%bv = Z_to_bv 64 key ->
    exists R' pw, CatSim.msteps ASEGS (st R E_DSP) (st R' E_BB) /\ aonlyD R R' /\ getr R' 24%bv = Z_to_bv 64 (hmod key bc)
      /\ getr R' 11%bv = Z_to_bv 64 pw /\ 0 <= pw < 2 ^ 64 /\ (bc <> 2 -> 2 <= pw) /\ (bc = 2 -> pw < 2).
  Proof.
    intros R Hin Hbc Hk H20 H22. pose proof (LbB_HFind.BSEQ_boundA bc Hin) as Hbcr.
    pose proof (bv_unsigned_in_range 64 (popcwD (Z_to_bv 64 bc))) as PWR. change (bv_modulus 64) with (2 ^ 64) in PWR.
    destruct (popcwD_cases bc Hin Hbc) as [[Hbc2 Hp1]|[Hbc2 Hp2]].
    - runD R SCR_D2.
      assert (P11 : getr R' 11%bv = popcwD (Z_to_bv 64 bc)) by exact (eq_trans (HR' 11%bv) (popcD_env E)).
      rreg HR' 24%bv G24.
      exists R', (bv_unsigned (popcwD (Z_to_bv 64 bc))). split; [exact Hms|].
      split; [intros r Hr; refine (LbB_HXmpS.syms_same_sound _ _ _ _ _ non_dsp HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true)|].
      split; [rewrite G24; rewrite w_addm, w_and by lia; subst bc; unfold hmod; change (2 + -1) with (Z.ones 1); rewrite Z.land_comm, Z.land_ones by lia; reflexivity|].
      split; [rewrite P11; symmetry; apply Z_to_bv_bv_unsigned|]. lia.
    - destruct (Z.lt_ge_cases key bc) as [Hlt|Hge].
      + runD R SCR_Dlt.
        assert (P11 : getr R' 11%bv = popcwD (Z_to_bv 64 bc)) by exact (eq_trans (HR' 11%bv) (popcD_env E)).
        rreg HR' 24%bv G24.
        exists R', (bv_unsigned (popcwD (Z_to_bv 64 bc))). split; [exact Hms|].
        split; [intros r Hr; refine (LbB_HXmpS.syms_same_sound _ _ _ _ _ non_dsp HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true)|].
        split; [rewrite G24; unfold hmod; rewrite Z.mod_small by lia; reflexivity|].
        split; [rewrite P11; symmetry; apply Z_to_bv_bv_unsigned|]. lia.
      + runD R SCR_Dge.
        assert (P11 : getr R' 11%bv = popcwD (Z_to_bv 64 bc)) by exact (eq_trans (HR' 11%bv) (popcD_env E)).
        rreg HR' 24%bv G24.
        exists R', (bv_unsigned (popcwD (Z_to_bv 64 bc))). split; [exact Hms|].
        split; [intros r Hr; refine (LbB_HXmpS.syms_same_sound _ _ _ _ _ non_dsp HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true)|].
        split; [rewrite G24; unfold hmod; apply LbB_HFind.remuw_valA; lia|].
        split; [rewrite P11; symmetry; apply Z_to_bv_bv_unsigned|]. lia.
  Qed.
End Dsp.

Section EmpE.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHB.
  Hypothesis REH : reh_stmt H EMP_EXT.

  Lemma acl_lo : forall s LB LB0 LBm m SP a n, as_RHEAP H s LB m -> Permutation LB (LB0 ++ LBm) -> 0 < n ->
    aclient_range H LB0 SP a n -> SP <= a \/ a + n <= aceil.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HXmpE ()) ["EmpE"] "p'0h02H0h11bh24__x1h34__x2h44__x3h54__p1h64__x4h71Xh87__arithh94__ffh:8__varmaph;5__with<4__p2h=4__x5h>1ah?4__x6h@2H1hA2H5hB2H6hC2X1hD2X2hE2_HhF3_H0hG1zhH2H2hI2H3hJ2H4hK2H7hL2H8hM2HbhN3HbLhO2QChP3_H1hQ4__p3hR4__p4hS4__x7hT4__x8hU4__x9hV1qhW2q0hX1rhY2r0hZ4ACF1h[4ACF2h\2F1h]2F2h^2F3h_2F4h`1Hha2H9hb2Hnhc2LBhd3LB0he3LBmhf2PEhg2Q0hh2Qnhi2RHhj2SPhk1Yhl3_H2hm3_H3hn6__sat5ho1mhp1nhq1si001xp%0p%1p&0p;1p;4p;3p;2p;6p;7p;5p;9p;8g02:Wk10kTg0057k10@Tg02;Pk40TTg003Rj3wTg002;k30jTg00?Tj25Tg02<Lk60YTg02=Mk10STg006<j17Tg005Wj14Tg02>Mk10bTg00R:j21Tg00@0R0j26Tg00>Yj1kTg01jjj2;Tg02?Gk10WTg00BYj20Tg02@Ak70NTg02A=k20MTg02B8k10LTg02C2j3ETg02Ckk105Tg02Djj13Tg02Efj18Tg02Fbj1MTg02GYj1lTg00iZk300Tg02HQj2nTg02Hnk20^Tg00D\k10]Tg00KNk10\Tg00EZk10[Tg00F8k10ZTg00Fck20>Tg00HMk10XTg00GFk20=Tg02I_k30VTg00Hok20UTg00:0k209Tg00IQk20RTg00C6j3zTg00J=k30QTg00J\k40PTg013Tj1_Tg01>kk207Tg01@fj2yTg00k\j3fTg02JBk40:Tg02Jok50;Tg002fk60<Tg02KMm904Tg02LLk40ITg00@nj2ATg02MLj2qTg00hbk10HTg00MSj2\Tg02Mmj2pTg02NTj2rTg02O;j2oTg02Oaj2sTg02PGk20GTg0087k10FTg01>Jk20OTg01?Tk302Tg02Phk208Tg02QQk301Tg00k8k60ETg00M0k30DTg00j^R1j2CTg00hKk30iTg01LJS00k20BTg00E<k20gTg01e\k40fTg00RVj4uTg00SAj7~Tg00Ohk30aTg00Sek70?Tg00TIj8}Tg01@=k30`Tg008Uk30cTg00Gik60_Tg02R:k70dTg004[k60eTf0R2#7#7#7#7p=B%42#4#4#4p=]%42#4#4#4#4#4#4#4p=L%42#4#4#kp=@g00UKR3g00TmR47z2p=Gf2R5f1R6'1/62p=<1056/12p=21156/C2p=hg02R^/12p=Og001BR7@0i62p=9f4R8f3R9/151162'6'6p=:20B72p=ef6R:f5R;'11189'61156g02SXR<,12'6'Cp=J11891156'6/C2p=V20B76/C2p=W1C62,C5p>0A1162,C5p>0h11951162'Cp=Z1142p=[20g32p=YP3P5P6P2H0fp==20=32p=XP3P6g00XOP2Cup=jP6g00VPR=g00VoR>P>g00WOR?P2g00WoR@F~p=mB0a362p=D20>32p=FP5P=P>P>P?P3P6g00UiRAP2CuP@F~p=HP9P=P>P>P?P5P6P=P>P>P?P2P@F~K0?p=UP9P=P>P>P?P5P6P2G}p=i20732p=^B0`362p=Pg00[9R@@0c62p=gP6P=P>P>P?P2J0_p=a%72#7p=Q%42#7p=>%72#4p=?%42#4p=N%72#7#4#4p=cP5P=P>P>P?P6P2K0dp=xP:P=P>P>P?P;P8P9P=P>P>P?P5P6P2G}G}p=R1562,65p>061656/C2p>0K16891656/C2'Cp>0J1062,15p=b10:;/181n56,19'C/62p=K1156/62,69p=d1662,65p>031146/62p=SP3g02TSP5P6P2g02UQJ0ep=v%86/02p=TAz362p=I1162,65p=`P5P=P>P>P?P6P2K0?p={P3P6g00l6P2Cup=tP3P6PAP2Cup=|1156112<'6p>0Cp,1HR<$0k&0@7S01Q01Q01g02VVP<f7RAP:P9H0TAw7:;:0j7A1545p,5HCEILRBP<f8RCP;P8P9J0Y&0SBg00;DRD#7S02#7S03#B#B#BRE#4#B#B#]#L#L#@RF&0bBRG'1S04%7ES05#B#B#]#L#L#@,1GS06'6S07%4DS08#4S09#4S0:#4RE#LS0;#kRH,;G#GS0<&0WBRI10GH,5I5<GS0='6S0>'6P0Q07Q0>A2A:G9hCAP2Q07P0Q04Q06Q0>f<S0?f;RIf:RJ=2IG3h[P2Q04Q06Q0>P0Q0<Q0=f@S0@f?RKf>S0A=2KG3hP2Q0<Q0=PBP<p,2HHS0BfHRLfGRMfDS0CQ0@K0N20MB<P0&0L<RN#OS0Dg02WMRO,0NRP/1GS0E1;NHRQ#GS0FAEBNOS0G'6S0H'6S0IfES0JQ0CQ0CfCS0K;2G3hP2Q0DQ0IP0Q0EQ0HfIS0LA2LMG7hLP2Q0EQ0HP0Q0FQ0GfMS0MfLRLfKS0N=2LG3hP2Q0FQ0GP1fPRLfORO'110LORR,529<L2&056RS[^>3fTRT,92RU%32RVPLPR%82RW,0VRXD:X17#ePU%MVRUPLPR%lW,0URWD:X17PNPOfNS0O,0ORYPP%MNRZPOPY%MPR[%MGR\POPYFJDV'W40AfQRY/1LR]@0hRGfJS0PfRR^/1Y10YLR_/1G<002X7]P2O1152_9<Y2PS[^>3fUR],92R`PVPYP_PXD:X17#eP`PUPYP_PWD:X17PNPLPRPPPZPLPRP[P\PLPRFJDV'W40AP110^YRR,529<^2PS[^>3fVR`,92RaPVP^PRPXD:X17PaPUP^PRPWD:X17PNPYP_PPPZPYP_P[P\PYP_FJDV'W'WfSR_P^PRPGCZP210_^Ra,529<_2PS[^>311T_11aGP2%kDRS,naRb20^NH%[N%[H%[Q[[&0]@RQ&0@@R@%Y5RH&0\3Rc7=6&0[3Rd&0Z3Re20>34RfQ08#XRg'j,me&0X>RhPe20=3DRi1DigRi%FS60V3Rg5HePe1jgiCUCi20Ue?RjP2P5g00[eRkg00\ERl+0920R25=zkldB0Q346H0PRlb9b:b;X23X3315461065Rk/nSRm15mk5<6[^23^33P2PTP]PYO3b8bnO2&05bp-0Rbg01SfRm#_Rn#_S0Q#^S0R%^nS0S2073mS0T'P'Pg01XYS0U'yRm1gmQS0V,gm,gm'gP@%Y9S0W9=H6S0XPdPePe1ae;S0YPe%7D#]#Q#>#Q#?#?#>#@RH#F,jgCUPe1ae:S0ZPe%7D#N#>#?#c#Q#]#@Rm#F,jgCUPe1aeAPe%7D#N#>#?#c#Q#?#Q#@Rn#F,jgCUPe1aeCS0[Pe%7D#>#c#Q#?#>#N#?#>#@Ro#F,jgCU5xe5xe5xePhPe%FFQ02#XRg5HeS0\PhAHeigS0]FRPjPlb9b:b;X23X33X43X5bX<bXQbWRP91026/nSRp/5HP815pm15pnB06:po60K;I0J11F9A2598S0^[[^23^33^43^5b^<b^Qb^RbP2%7D#>#>#?#>#?#Q#>#N#?#@10]TRp/nSRS'1%7D#N#>#?#c#c#>#@/1S%7D#N#>#N#Q#]#?#Q#@/1S%4D#B#c#L#@/1SPGPTP]P6Q0LO9b8bk3fW7P2O1fWRS,92RoPVP_PaPXD:X17PoPUP_PaPWD:X17PNP^PRPPPZP^PRP[P\P^PRFJDV'W'WP1fXRR,92RoPVPT10T_RnPXD:X17#ePoPUPTPnPWD:X17PNP_PaPPPZP_PaP[P\P_PaFJDV'WP]PTPnPGCZP2fYRa,92S0_PVP]PpPXD:X17#eQ00P7fZRo,92S0`PVP`10`]RmPXD:X17PSP`PmPGCZS0aP2f\RH,92S0bPVPR10RSRVPXD:P0f]RX,96%36S0c10aRRqQ0c%86S0d3b7<af[RrPo10oaS0ePGCZS0fP2f_Rs,99%38S0g10HrS0hQ0g%88S0i3b7<HP0%3;S0j/1XQ0j%8;S0k'092XHPsf^Rt10tXS0lPGCZP2%3AS0m/1sf`Ru/0sS0n%3CS0o%8CS0p3bfbRvfaRw'1A2wuGP7feRxfdRy5w7RzffR{f9R|P7P{PzPtH0:P7PxPyP|19|x19|y<00;I0;J0<19|{S0qPBP<Q0BfhRzfgR}PyPJPuP2N904PBP<%3J%8JH0IS0rP0%3IR~,54S0s%kERE,;~#G%8IS0t#[%O~Q0t,0~S0uPGQ0uPEPNPPP~PEQ0t9EB~FKCd403S0tfcS0u=2yGP2f=S0v#3,54S0wQ0A#3R~/;E#GQ0A#8S0A#[%O~Q0A,0~S0xPGQ0xPEPNPPP~PEQ0A9EB~FKCd403S0AP0%3KR~/;E#GS0x%8KRK%O~10~KS0yPGQ0yPEPNPPP~PEAEB~KFKCd'SS0yA2z}GP2fAS0z#3/;E#GS0{fBRK#8R~%3KRK#O10K~S0|PGQ0|PEPNPPPKPEAEBK~FKCd'SS0|P0Q0K#8RK#[S0}Q0K#3R~#O10~KS0KPGQ0KPEPNPPP~PEAEB~KFKCdS0KflS0~fk;2GP2Q0J#8#[S0JfFR~#3RK#O%8~R~,0KS10PGQ10PEPNPPPKPEAEBK~FKCdS10P0%3MR~#OS11%8MRK,0~S12Q12PEPNPPP~PEAEB~KFK7<GS12fpfo;2GP2Q0L#3#OS0LQ0P#3RKQ0P#8R~'0S0PQ0PPEPNPPPKPEAEBK~FK7<GS0PP0Q0N#3R~Q0N#8RK'0S0N/1GS13Q0NPEPNPPP~PEAEB~KFKS0Nftfs;2GP2Q0M#3Q0M#8;2GS0MQ0O#3RKQ0O#8R~'0PEPNPPPKPEAEBK~FKS0OQ0VP@%Y8S14?=5cS15%Y;S16?=9c7=6PdPeQ09#XR~Q08#7S08#XRK'DRE=HegPhPeAHeiEPhQ0]FRPjPlb9b:b;X23X33X43X63X=3A2985108;S17,1kQ0^[[^23^33^43^63^=3P2%8LS18%3LREPGfwfxP5PMO7b8WmWOP6P2O2n2001000000121000000W0WlP6P2O2n2001000000121000000W0WPP6P2O2n2001000000121000000W0WFP6P2O2n2001000000121000000W0WEP6P2O2n2001000000121000000b0bN3fWDWCP6P2O2n2001000000121000000W0WMP6P2O2n2001000000121000000W0X17P6P2O2n2001000000121100000W0P2O1Q0_PUP]PpPWD:X17PNPTPnPPPZPTPnP[P\PTPnFJDV'WP1Q0`PUP`PmPWD:X17#ePNP]PpPPPZP]PpP[P\P]PpFJDVQ0aP2192rPUPS10S`RpPWD:X17#eQ00P7Q0bPUPRPVPWD:X17PaPRPVPGCZRnP2192tPUPoQ0ePWD:P0196sQ0c#MRW10roRUQ0d#l7bW7<rPXPHQ0hPGCZP2199wQ0g#MRWQ0lQ0i#l7bW7<tP0Q0j#MRW/1sQ0k#l,0W92stPwPuQ0nPGCZP2Q0m#M/1wQ0o#MQ0p#l'092vwQ0u,1yQ0u?2vGP7Aw7}{RyPzP|P7PzPyPuH0:P7P}P{P|19|}Q0q<00;I0;J0<19|zPBP<Q0BfjR<fiRBP{PJPvP2N904Q0rP0Q0sQ0tA2{xGP2Q0wQ0AP0Q0xQ0yA2<BGP2Q0{Q0|P0Q0}Q0KfnfmRB;2GP2Q0JQ10P0Q11Q12frfq;2GP2Q0LQ0PP0Q13Q0Nfvfu;2GP2Q0MQ0OQ0:#kR0,AEREfzR<522XG3Q05#]#L#@R{7vM%3O/A0fyRO52{f{%3YRx/A0,02Q03#kRz,TY/A0'072<XG3?vM{10{EQ18/0z/A0'092<O1qx0%G0Rx$0HRO%3^R^1A^0,\01;^0'0'I[1p^01540R^%3_R</;0RE15E0'S[1r<01504R<%3TRT/;0RE,50?`E4[1oT0%3]R]/A0#G\x1s]0%3`R]/;0/I]\x1A]0P3%3S/;0P31TRz/q01TazR]1A]0,\01;]0'0'I\O1p]01TozR]/;0RT15T0'S\^1r]01TrzR]/;0RT,50?`T4\<1o]01THzR]/A0#G\x1s]01TXzRX/;0/IX\x1AX0P31Ttz/;0P3P;g02XI20G40+09P^eRtO1RX1520,S2R]Q0vPtO1Rt%[CRT@06C0REQ0Q#_RM#_RY#_R}#_Ru#_#^&0FD-0O3RD%^u6023%^}%^Y:023D%^M2083zQ0R601320830RMQ0S6013Q0T:013M'P'P'P'P'PRM'P'PQ0U'y/gQP@%YC?=8c%Y:RD7=5%Y|?=;c%YA7=97=6PdPeQ09#7#XRY9Hef1aeI5{ePhPePePeP=P>P>P?%F0R?/tf,meJ0ER>PhQ03#XR=%Fz'DB0D3?KR}/DY't,meCiPhPeQ0:#XRY9HefRfQ0?,ae5{ePhPePeP>PhQ02#4#XRuB0D3?~/DY't,meCiPhPe1Du==HegPhPeQ0\PhPe%F{R=/D~/DK9HeiPhQ0]CiFRFRFRPjPlb9b:b;X23X33X43X63X=3X?3XS3XT3XU3X5bX<b16T|g00mS\xRT10Cz1\0:/0J'I[Q0?,S|1\0A/0I,I|\TA2|J:11FA10{|/0J92:AA2AC|[[[[[[[^23^33^43^63^=3^?3^S3^T3^U3^5b^<bP215J01590RCP9PJ%8v%3vP8PIPGp+01Lp+01MP5P|P6Q0@Q0Cp+01AQ0zOBb8b0bAbYbWbLbKbBbAbJbXbVbIbHb@b0b`bDbCWPWOP6P2O2n2001000000121000000W0WFP6P2O2n2001000000121000000W0WhP6P2O2n2001000000121000000W0WEP6P2O2n2001000000121000000W0WgP6P2O2n2001000000121000000b0bN3fWDWCP6P2O2n2001000000121000000W0WMP6P2O2n2001000000121000000W0X17P6P2O2n2001000000121100000W0P2O1PNP`PmPPPZP`PmP[P\P`PmFJDVP111pP9<NSPZPSPpP[P\PSPpFJPnP211VP9<NR11oa11qGQ0VP@Q15Q0W7=6PdPeQ08#?#N#>#N#?#L#@RP#FRn,D~R~=HegPhPePeQ0ZPe1|i~CUPhQ0]FRPjPlb9b:b;X23X33X43X63X5bA29P5108P9`;kQ0^[[^23^33^43^63^5bP211NoPNPGPaPoQ0@P6O7b83fW7P2O1PZPRPVP[P\PRPVFJP111q[9<ZaB0C\aqQ0fP2Q0e/1[9<Zo11HrRZ11UGR[1AN0Rq,02Q0h10NPRa/A0R17b27<HXG3?v2{10{qAbU{17<r1qN01\0q1;N0RU'0,IN\O1pN015U0,SU\^1rN0150U?`U4\<1oN0%Gq\x1sN01IUN\xPqP3PUP31qa01\011;a0RU'0,Ia\O1pa015U0,SU\^1ra0150U?`U4\<1oa0%G1\x1sa01IUa\xP1P3PUP3PXP]PtPEQ0U,yM/gQP@A=D:cQ167=5Q14?=9c7=6PdPeQ0[9{efPhPePeP>Ph1DunRn1D}Y't,meCiPhPeAHengPhPeQ0\PhPePe1ae|Pe1D=K,|iCUPhQ0]CiFRFRPjPlb9b:b;X23X33X43X63X=3X?3X5bX<b1S;:10:PRP1\0;/0A'I\T11P811F;Q1710{A5`IA2;:A[[[[[^23^33^43^63^=3^?3^5b^<bP2A2{IBPCP9PNP8PGQ0~PBP5P|P_PwQ0zO=b8b@bBbYbWbabLbKbBbAbXbVbJbIbHb@b0b73fW7P2O1Q0e:0C\oQ0VP@Q0XPdPeQ0\PhPePeQ0YPeQ0;#4#B#B#B#B#]#L#@Re#F,|iCUPhQ0]FRPjPlb9b:b;X23X33X43X5b11F5A`8keQ0^[[^23^33^43^5bP211\HPGPrPHPLP6O6b89fZ[W7P2O1n200100000021100011000W0P2O1n200100000021100011000W0P2O1n200100000021100011000W0P2O1n200100000021100011000W0P2O1n200100000021100011000W0P2O1n200100000021000011000W_W^P6P2O2n2001000000121000000W0W]P6P2O2n2001000000121000000W0W\P6P2O2n2001000000121000000b0WFWEP6P2O2n2001000000121000000W0W[WZP6P2O2n2001000000121000000W0P6P2O2n2001000000121000000b0W7WbWfWiXp3X>3Xj3WoWeWdWcWqo"). Qed.

  Lemma agree_of_munchE : forall W m m' a k, munch W m m' -> (forall x, a <= x < a + k -> outside W x) ->
    0 <= a -> a + k <= 2 ^ 64 -> HRepFacts.agree_on m m' a k.
  Proof. intros W m m' a k MU HO Ha Hak i Hi. apply MU. rewrite HLib.u64_of_Z by lia. apply HO. lia. Qed.

  Tactic Notation "rq" constr(AO) constr(HRe) uconstr(r) ident(Q) :=
    pose proof (AO (r : reg) ltac:(inb)) as Q; rewrite HRe in Q; cbn [getr mkR PropExec.getr Vector.nth] in Q.
  Tactic Notation "rq2" constr(AO3) constr(AO2) constr(HRe) uconstr(r) ident(Q) :=
    pose proof (AO3 (r : reg) ltac:(inb)) as Q; rewrite (AO2 (r : reg) ltac:(inb)), HRe in Q; cbn [getr mkR PropExec.getr Vector.nth] in Q.

  Ltac pro_reg HR' HR0 :=
    first
    [ reflexivity
    | lazymatch goal with |- getr _ ?r = _ =>
        let G := fresh "G" in rreg HR' r G; rewrite G; clear G
      end;
      rewrite ?HR0; cbn [getr mkR PropExec.getr Vector.nth];
      rewrite ?w_add by lia; rewrite ?sh_wordE by lia; rewrite ?w_addm, ?HWord.w_srl by lia;
      first [reflexivity | f_equal; lia] ].

  Ltac stage_tac VIS1 FRZ KR1 NPTAC :=
    lazymatch goal with
    | |- asan_rt_hyps_bp _ => assumption
    | |- reh_stmt _ _ => assumption
    | |- asan_rt_hyps _ => assumption
    | |- as_VIS _ _ _ = _ => exact VIS1
    | |- frm_zero _ => exact FRZ
    | |- as_AKREL _ _ _ => exact KR1
    | |- _ => NPTAC
    end.

  Theorem emp_specA : emp_stmt H EMP_EXT.
  Proof using All.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LB0 LBm LF
      obj bl bc keyp tupp keyp2 key ents lo B shi errv
      VIS FRZ A0 A1 A3 U SH PE PM ADH WRH LFO OCE OBL FK AK EK FT AT ET FK2 AK2 EK2 KAL TAL K2AL KR32 ZLEN BCL RH KR AL0
      RSM RCN RLG RICM TRK RAX SPB BR SP16 ST ACL LOR ERR MI TPV RAE AC RF S0 SHI OWN.
    subst a0 a1 a3.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    set (spz := bv_unsigned sp) in *.
    assert (SPE : sp = Z_to_bv 64 spz) by (unfold spz; symmetry; apply Z_to_bv_bv_unsigned).
    clearbody spz. subst sp.
    change (as_SR H (LbB_HXmpI.QI H ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz s LB0 LF obj bl bc key ents lo B shi m mo)
                  (mkCfg msF mo)).

    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof LOR as LOR'. unfold AEMP_STACK, AOPNEW_STACK in LOR'. try unfold AMALLOC_STACK in LOR'.
    assert (LOS : lo <= spz - 96) by (clear - LOR'; lia).
    assert (SPH : spz <= 2 ^ 47) by (destruct S0 as (g & _ & Hg & _); unfold AAPP_HI in Hg; clear - Hg SHI; lia).
    assert (SPL : 2 ^ 45 <= spz - 96) by (clear - ACF1 ACL LOS; lia).
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_al U) as Hoal.
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U)) as BCR.
    destruct (u_hdr U) as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    assert (GZO : gz m obj 40) by (apply LbB_HXmpI.gzA; [exact ADH | reflexivity]).
    pose proof (LbB_HXmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    pose proof AK as (AK0 & AK1 & _). pose proof AT as (AT0 & AT1 & _). pose proof AK2 as (AK20 & AK21 & _).
    unfold AAPP_HI in AK1, AT1, AK21.
    pose proof (acl_lo s LB LB0 LBm m spz keyp 4 RH PE ltac:(lia) (proj1 EK)) as KLOC.
    pose proof (acl_lo s LB LB0 LBm m spz tupp 8 RH PE ltac:(lia) (proj1 ET)) as TLOC.
    pose proof (acl_lo s LB LB0 LBm m spz keyp2 4 RH PE ltac:(lia) (proj1 EK2)) as K2LOC.

    destruct (LbB_HXmpNd.src4_shk m keyp AK KAL) as (k & SHK & KC).
    assert (KB : 0 <= k < 8) by (destruct KC as [KC|KC]; lia).
    set (R := mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 obj) (Z_to_bv 64 keyp) a2 (Z_to_bv 64 tupp) a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) in VIS.
    assert (HR0 : R = mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 obj) (Z_to_bv 64 keyp) a2 (Z_to_bv 64 tupp) a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) by reflexivity.
    clearbody R.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 keyp; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 k; Z_to_bv 64 spz]).
    assert (HR : regs_ok E srPRO R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst E; evs; rewrite HR0; reflexivity] |]).
      apply Forall_nil. }
    assert (CK : cellw ASEGS m keyp 4 key) by (split; [cbn; lia | exact FK]).
    assert (Hrd_b : sc_denot asegs m E (SCReadBase (SA (EVar 32) 8) 8 false (EVar 34))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbc); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (Hrd_k : sc_denot asegs m E (SCReadBase (SA (EVar 33) 0) 4 false (EVar 35))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ CK); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (HKP : know_ok asegs E m KN_PRO).
    { unfold KN_PRO, KN_GOT, know_ok. destruct (ACONST_shbase m AC) as [CG CS].
      apply Forall_cons.
      { eapply (kword_of_rw_cells _ _ _ _ _ 0%nat (C8 (wz ASHBASE_CELL)));
          [ exact CG | reflexivity | reflexivity | lia
          | unfold estart; evs; unfold AGOT_SHBASE; rewrite ?u64_of_Z by lia; cbn [a_off a_base Z.of_nat]; lia
          | unfold AGOT_SHBASE; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | unfold AGOT_SHBASE; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | reflexivity ]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells _ _ _ _ _ 0%nat (C8 (wz ASHADOW_BASE)));
          [ exact CS | reflexivity | reflexivity | lia
          | unfold estart; evs; unfold ASHBASE_CELL; rewrite ?u64_of_Z by lia; cbn [a_off a_base Z.of_nat]; lia
          | unfold ASHBASE_CELL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | unfold ASHBASE_CELL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | rewrite ASHADOW_BASE_val; reflexivity ]. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off a_base]; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off a_base]; lia
                           | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off a_base]; lia|].
      apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off a_base]; lia|].
      apply Forall_nil. }
    assert (KSO8 : kentry_ok asegs E m KN_SO8).
    { apply (kshadow0 E m (EAlu ALU_ADD (EVar 32) (ELit 8)) (obj + 8));
        [evs; rewrite w_add by lia; reflexivity | lia | eapply sh0_of_addressable; [exact ADH | change (8 * (40 / 8)) with 40; lia]]. }
    set (M1 := mem_denot E m (c8log (EVar 37) (-96) tlPRO)).
    assert (PRO : exists R1 x12,
               CatSim.msteps asegs (MS R F (Z_to_bv 64 (emp_entry EMP_EXT)) fc None m (seg_rom asegs))
                                   (MS R1 F (Z_to_bv 64 E_DSP) fc None M1 (seg_rom asegs))
               /\ log_flat E (c8log (EVar 37) (-96) tlPRO)
               /\ R1 = mkR ra (Z_to_bv 64 (spz - 96)) gp tp t0 t1 t2 (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 0)
                           (Z_to_bv 64 keyp) x12 (Z_to_bv 64 tupp) a4 a5 a6 a7 (Z_to_bv 64 tupp) (Z_to_bv 64 SHBASE)
                           (Z_to_bv 64 bc) (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE))
                           s8 s9 s10 s11 t3 t4 t5 t6).
    { destruct (Z.eq_dec k 0) as [K0 | K1].
      -
        subst k.
        assert (HK : know_ok asegs E m (KN_P0 ++ [KN_SK0; KN_SO8])).
        { unfold know_ok, KN_P0. apply Forall_app. split; [exact HKP|].
          apply Forall_cons; [|apply Forall_cons; [exact KSO8 | apply Forall_nil]].
          apply (kshadow0 E m (EVar 33) keyp); [evs; reflexivity | lia | exact SHK]. }
        xrun_at (PropExec.mkFP F fc) asegs R (emp_entry EMP_EXT) m (seg_rom asegs) HR HK 60%nat [E_DSP] SCR_P0 50%N.
        { clear - E Hrd_b Hrd_k. split_scs; first [exact Hrd_b | exact Hrd_k]. }
        change (log_flat E (c8log (EVar 37) (-96) tlPRO)) in Hlf.
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) => change mm with M1 in Hms end.
        readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
        exists R', (getr R' 12%bv). split; [exact Hms|]. split; [exact Hlf|].
        rewrite HRe. f_equal; pro_reg HR' HR0.
      -
        assert (HK : know_ok asegs E m (KN_P1 ++ [KN_SO8])).
        { unfold know_ok, KN_P1. rewrite <- app_assoc. apply Forall_app. split; [exact HKP|].
          apply Forall_cons; [|apply Forall_cons; [exact KSO8 | apply Forall_nil]].
          apply (kshadow E m (EVar 33) keyp k (EVar 36)); [evs; reflexivity | lia | lia | evs; reflexivity | exact SHK]. }
        xrun_at (PropExec.mkFP F fc) asegs R (emp_entry EMP_EXT) m (seg_rom asegs) HR HK 60%nat [E_DSP] SCR_P1 50%N.
        { clear - E Hrd_b Hrd_k K1 KC KB AK0 AK1.
          split_scs;
            first [ exact Hrd_b | exact Hrd_k
                  | cbn [sc_denot]; evs; rewrite ?ext_shadow_small by lia; rewrite ?land7_val by lia; rewrite ?w_add by lia;
                    rewrite ?br_ne, ?br_lts_small by lia; destruct KC as [KC|KC]; [lia|]; bool_lia ]. }
        change (log_flat E (c8log (EVar 37) (-96) tlPRO)) in Hlf.
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) => change mm with M1 in Hms end.
        readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
        exists R', (getr R' 12%bv). split; [exact Hms|]. split; [exact Hlf|].
        rewrite HRe. f_equal; pro_reg HR' HR0. }
    destruct PRO as (R1 & x12 & Hms & Hlf & HRe).

    assert (FRM : LbB_HXmpD.FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz M1).
    { unfold LbB_HXmpD.FRAME, LbB_HXmpD.spf, M1.
      replace [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        with (map (fun v => C8 (edenot E v)) tlPRO) by (subst E; rewrite HR0; reflexivity).
      apply rw_cells_c8log; [exact Hlf | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off a_base]; lia |].
      change (8 * Z.of_nat (length tlPRO)) with 96.
      eapply LbB_HXmpD.wr_at_subE; [exact (wr_at_of_stk _ _ _ _ ST) | lia | lia | lia]. }
    set (W1 := [(spz - 96, spz)]).
    assert (MU1 : munch W1 m M1).
    { subst M1 W1. apply munch_mem_denot; [exact Hlf|]. unfold tlPRO. cbn [c8log].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                                  cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (FW1 : aclient_write_ok H LB (spz - 96, spz) /\ afs_write_ok H LF (spz - 96, spz) /\ aconst_ok (spz - 96, spz))
      by (apply stack_window_ok; [lia | exact FB2]).
    destruct FW1 as (FW1a & FW1b & FW1c).
    assert (F1 : Forall (aclient_write_ok H LB) W1) by (subst W1; constructor; [exact FW1a | constructor]).
    assert (F2 : Forall (afs_write_ok H LF) W1) by (subst W1; constructor; [exact FW1b | constructor]).
    assert (F3 : Forall aconst_ok W1) by (subst W1; constructor; [exact FW1c | constructor]).
    destruct (client_frame H HH s LB LF B W1 m M1 RH RF AC RAX MU1 WM1 F1 F2 F3) as (RH1 & RF1 & AC1 & RAX1).
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (XP1 : xpres H LB0 spz [(obj, obj + 40)] m M1).
    { eapply (xpres_munch_mixed H HH s LB LB0 LBm spz [(obj, obj + 40)] W1 m m M1);
        [apply xpres_refl | exact RH | exact PE | lia | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
    assert (AG1 : forall a k, 0 <= a -> 0 <= k -> (a + k <= spz - 96 \/ spz <= a) -> a + k <= 2 ^ 64 -> HRepFacts.agree_on m M1 a k).
    { intros a k0 Ha Hk Hak Hb. eapply agree_of_munchE; [exact MU1 | | lia | lia].
      intros x Hx. subst W1. cbn. split; [lia | exact I]. }
    assert (SHO : forall x, 0 <= x -> x + 1 <= 2 ^ 47 -> outside W1 (sh x)).
    { intros x Hx0 Hx1. pose proof (sh_nsh_high x 1 Hx0 ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SN.
      unfold AHI_LO, nsh in SN. subst W1. cbn. split; [|exact I]. lia. }
    assert (DSH1 : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from W1 (sh A) (nsh k)).
    { intros A k0 HA Hk HAk. subst W1. apply LbB_HXmpI.dsh_app; [| exact HA | exact Hk | exact HAk].
      unfold ALOWSH_LO, AHI_LO. apply Forall_cons; [cbn [fst snd]; right; clear - SPL; lia | apply Forall_nil]. }
    assert (ERR1 : rw_cells asegs M1 (bv_unsigned tp + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |].
      subst W1. cbn [disjoint_from cells_size csize]. rewrite TPV, u64_of_Z by (unfold ATP; lia). unfold ATP.
      split; [|exact I]. cbn. lia. }
    assert (U1 : umapx MI_A 24 (nval24 ASEGS) (lbl LB) M1 obj bl bc ents).
    { eapply (umapx_agree ASEGS LY_A MI_A 24 _ (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia) (lbl LB) (lbl LB) m M1);
        [exact U | | intros; assumption].
      intros a Ha.
      assert (AGa : 0 <= aceil) by (clear - ACF1; lia).
      pose proof (AG1 0 aceil (Z.le_refl 0) AGa ltac:(left; clear - ACL LOS; lia) ltac:(clear - ACF2; lia)) as AG.
      assert (Ha' : 0 <= a < aceil).
      { destruct Ha as [Ha | [[Hbc Ha] | (q & Hq & Hqa)]]; [lia | |].
        - pose proof (u_bl_hi U). pose proof (u_bl_lo U Hbc).
          destruct (lbl_in_inv LBm bl (8 * bc) (Permutation_in _ (Permutation_sym PM) ltac:(unfold umap_blocks; apply in_or_app; left; destruct (Z.eqb_spec bc 0); [lia | left; reflexivity]))) as (qi & Qi).
          pose proof (ah_blocks H HH _ _ _ _ RH (Permutation_in _ (Permutation_sym PE) (in_or_app _ _ _ (or_intror Qi)))) as (_ & _ & _ & _ & QC & _).
          cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in QC. lia.
        - apply in_map_iff in Hq. destruct Hq as ([z [k0 v]] & Hz & Hin). cbn in Hz. subst z.
          destruct (lbl_in_inv LBm q 24 (Permutation_in _ (Permutation_sym PM) ltac:(unfold umap_blocks; apply in_or_app; right; apply in_map_iff; exists (q, (k0, v)); split; [reflexivity | exact Hin]))) as (qi & Qi).
          pose proof (ah_blocks H HH _ _ _ _ RH (Permutation_in _ (Permutation_sym PE) (in_or_app _ _ _ (or_intror Qi)))) as (Q0 & _ & _ & _ & QC & _).
          cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in QC, Q0. cbn in Hqa. clear - QC Q0 Hqa. lia. }
      pose proof (AG a ltac:(lia)) as X. rewrite Z.add_0_l in X. exact X. }
    assert (SH1 : umap_sh M1 24 (bl, bc, ents)).
    { destruct SH as [SHb SHn]. unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c in *. cbn [Datatypes.fst Datatypes.snd] in *. split.
      - intros Hbc. pose proof (u_bl_hi U). pose proof (u_bl_lo U Hbc).
        eapply addressable_transport; [exact (SHb Hbc) | exact MU1 | exact WM1 | apply DSH1; lia].
      - intros q k0 v Hin. destruct (u_node U q k0 v Hin) as (_ & E0 & E1 & _).
        eapply addressable_transport; [exact (SHn q k0 v Hin) | exact MU1 | exact WM1 | apply DSH1; lia]. }
    assert (ADH1 : addressable M1 obj 40) by (eapply addressable_transport; [exact ADH | exact MU1 | exact WM1 | apply DSH1; lia]).
    assert (WRH1 : wr_at asegs M1 obj 40) by exact (wr_at_wmono _ _ _ _ WRH WM1).
    assert (OWN1 : lb_own LBm M1) by exact (lb_own_wmono _ _ _ OWN WM1).
    assert (FT1 : fldA M1 tupp 8 keyp2).
    { unfold fldA in FT |- *. eapply (CRep.fld_agree ASEGS); [lia | cbn; lia | exact FT |].
      intros a Ha. unfold zwin in Ha. cbn [Z.of_nat] in Ha.
      pose proof (AG1 tupp 8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (a - tupp) ltac:(lia)) as X.
      replace (tupp + (a - tupp)) with a in X by lia. exact X. }
    assert (FK21 : fldA M1 keyp2 4 key).
    { unfold fldA in FK2 |- *. eapply (CRep.fld_agree ASEGS); [lia | cbn; lia | exact FK2 |].
      intros a Ha. unfold zwin in Ha. cbn [Z.of_nat] in Ha.
      pose proof (AG1 keyp2 4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (a - keyp2) ltac:(lia)) as X.
      replace (keyp2 + (a - keyp2)) with a in X by lia. exact X. }
    assert (AT2 : accessible M1 tupp 8) by (eapply accessible_transport; [exact AT | exact MU1 | intros x Hx; apply SHO; lia]).
    assert (AK22 : accessible M1 keyp2 4) by (eapply accessible_transport; [exact AK2 | exact MU1 | intros x Hx; apply SHO; lia]).
    assert (SE : LbB_HXmpS.SENV LY_A MI_A (lbl LB) M1 obj bl bc key ents).
    { pose proof SH1 as SH1'. destruct SH1' as [SHb SHn]. unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn.
      cbn [Datatypes.fst Datatypes.snd] in SHb, SHn.
      split; [exact U1|]. split; [exact KR32|].
      split; [apply LbB_HXmpI.gzA; [exact ADH1 | reflexivity]|].
      split; [intros Hb; apply LbB_HXmpI.gzA; [exact (SHb Hb) | rewrite Z.mul_comm; apply Z_mod_mult]|].
      intros q k0 v Hq. apply LbB_HXmpI.gzA; [exact (SHn q k0 v Hq) | reflexivity]. }
    assert (NP1 : forall mo1, as_MPRES H mo mo1 ->
              LbB_HXmpNd.NPRE H ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz s LB0 LF obj bl bc key ents lo B shi m mo tupp keyp2
                s mo1 M1 errv LB LBm).
    { intros mo1 MP1. unfold LbB_HXmpNd.NPRE.
      repeat match goal with |- _ /\ _ => split end;
        first [ assumption | unfold LbB_HXmpD.spf; lia | lia ]. }

    destruct (Z.eq_dec bc 0) as [Hbc0 | Hbcn].
    - destruct (@dsp_z (PropExec.mkFP F fc) (seg_rom asegs) M1 key bc R1 ltac:(rewrite HRe; reflexivity)
                  ltac:(rewrite HRe; reflexivity) Hbc0) as (R2 & Hms2 & AO2).
      pose proof (CatSim.msteps_trans _ _ _ _ Hms Hms2) as Hms12.
      eapply (sr_blk H HH); [exact KR | exact VIS | exact FHF | exact Hms12 |].
      intros msF1 mo1 KR1 MP1 VIS1.
      rq AO2 HRe 2%bv Q2. rq AO2 HRe 3%bv Q3. rq AO2 HRe 4%bv Q4. rq AO2 HRe 8%bv Q8. rq AO2 HRe 9%bv Q9.
      rq AO2 HRe 18%bv Q18. rq AO2 HRe 19%bv Q19. rq AO2 HRe 20%bv Q20. rq AO2 HRe 21%bv Q21. rq AO2 HRe 22%bv Q22.
      rq AO2 HRe 23%bv Q23. rq AO2 HRe 27%bv Q27.
      rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q21, Q22, Q23, Q27 in VIS1.
      eapply LbB_HXmpNd.stage_node with (tupp := tupp) (keyp2 := keyp2) (s := s) (errv := errv) (LB := LB) (LBm := LBm).
      all: stage_tac VIS1 FRZ KR1 ltac:(first [exact (NP1 mo1 MP1) | intros X; exfalso; exact (X Hbc0)]).
    - destruct (@dsp_nz (PropExec.mkFP F fc) (seg_rom asegs) M1 key bc R1 (u_bseq U) Hbcn KR32
                  ltac:(rewrite HRe; reflexivity) ltac:(rewrite HRe; reflexivity))
          as (R2 & pw & Hms2 & AO2 & G24 & G11 & PWR & PW2 & PW1).
      pose proof (CatSim.msteps_trans _ _ _ _ Hms Hms2) as Hms12.
      rq AO2 HRe 8%bv A8. rq AO2 HRe 19%bv A19. rq AO2 HRe 22%bv A22. rq AO2 HRe 21%bv A21. rq AO2 HRe 20%bv A20.
      destruct (@LbB_HXmpS.emp_from_bb (PropExec.mkFP F fc) _ LY_A MI_A (seg_rom asegs) (lbl LB) M1 obj bl bc key ents R2 pw SE Hbcn
                  A8 A19 A22 A21 A20 G24 G11 PWR PW2 PW1) as [R3 [(r & EF & Hms3 & AO3 & G10) | (Hms3 & AO3)]].
      +
        destruct EF as [v Hin].
        pose proof (CatSim.msteps_trans _ _ _ _ Hms12 Hms3) as Hms13.
        eapply (sr_blk H HH); [exact KR | exact VIS | exact FHF | exact Hms13 |].
        intros msF1 mo1 KR1 MP1 VIS1.
        rq2 AO3 AO2 HRe 2%bv B2. rq2 AO3 AO2 HRe 3%bv B3. rq2 AO3 AO2 HRe 4%bv B4. rq2 AO3 AO2 HRe 27%bv B27.
        rewrite B2, B3, B4, B27, G10 in VIS1.
        eapply LbB_HXmpD.stage_found with (s := s) (p := r) (v := v) (LB' := LB) (LBm' := LBm) (errv' := errv).
        all: stage_tac VIS1 FRZ KR1 ltac:(first [assumption | unfold LbB_HXmpD.spf; lia | lia]).
      +
        pose proof (CatSim.msteps_trans _ _ _ _ Hms12 Hms3) as Hms13.
        eapply (sr_blk H HH); [exact KR | exact VIS | exact FHF | exact Hms13 |].
        intros msF1 mo1 KR1 MP1 VIS1.
        rq2 AO3 AO2 HRe 2%bv B2. rq2 AO3 AO2 HRe 3%bv B3. rq2 AO3 AO2 HRe 4%bv B4. rq2 AO3 AO2 HRe 8%bv B8. rq2 AO3 AO2 HRe 9%bv B9.
        rq2 AO3 AO2 HRe 18%bv B18. rq2 AO3 AO2 HRe 19%bv B19. rq2 AO3 AO2 HRe 20%bv B20. rq2 AO3 AO2 HRe 21%bv B21.
        rq2 AO3 AO2 HRe 22%bv B22. rq2 AO3 AO2 HRe 23%bv B23. rq2 AO3 AO2 HRe 27%bv B27.
        pose proof (AO3 (24%bv : reg) ltac:(inb)) as B24. rewrite G24 in B24.
        rewrite B2, B3, B4, B8, B9, B18, B19, B20, B21, B22, B23, B27, B24 in VIS1.
        eapply LbB_HXmpNd.stage_node with (tupp := tupp) (keyp2 := keyp2) (s := s) (errv := errv) (LB := LB) (LBm := LBm).
        all: stage_tac VIS1 FRZ KR1 ltac:(first [exact (NP1 mo1 MP1) | intros _; reflexivity]).
  Qed.
End EmpE.
