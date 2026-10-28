(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HWord HLib HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_HEmpS LbB_HEmpK LbB_HEmpD.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_HEmpI () := "C46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface4bptrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockI46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;Permutation>Permutation_inC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z2leC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvBsh0_of_addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit2gzK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3memK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6hdaddrC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5chainC47Corelib4Init9Datatypes8list_indC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell8C5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC4ARocqVerifyHarness?AgentSubmission8LibIface3memC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5apartI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C46Stdlib5Lists4List2InC46Stdlib5Lists4List4lastC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or01C47Corelib4Init5Logic3notK47Corelib4Init5Logic2or02I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6nval24C56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep;umap_blocksC4ARocqVerifyHarness?AgentSubmission7StoreOk9mem_growsC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9umap_footC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpK5lastaK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell4C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_hiC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_alC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_bl_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_bl_hiC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_bl_objC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame7outsideC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init5Logic3and01C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts8agree_onI47Corelib4Init5Logic2ex00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI:last_in_neK47Corelib4Init5Logic2ex01C46Stdlib5Lists4List:in_app_iffC56Stdlib6ZArith6BinInt1Z4of_NC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts;cellw_agreeC47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:in_map_iffK46Stdlib9micromega:ZMicromega;ZArithProof03C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses8or_morphC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpK:umapx_linkI5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5umapx00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7ZlengthC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9bucket_okC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_nodeC4ARocqVerifyHarness?AgentSubmission8LibIface4liveK46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4AC_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4LY_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4MI_AI47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes:comparison00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib4Init9Datatypes3sndI47Corelib5Lists7ListDef6Forall00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3nshC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=disjoint_fromC46Stdlib5Lists4List:Forall_invC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;sh_nsh_highC56Stdlib6ZArith6BinInt1Z7div_posC46Stdlib5Lists4List?Forall_inv_tailC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9ALOWSH_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs<ASHADOW_BASEC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BellsX<rw_cells_appC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKit=rw_cells_addrK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec9u64_rangeC46Stdlib6ZArith:ZArith_dec8Z_lt_decI47Corelib4Init6Specif7sumbool00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKitFdefined_of_rw_cells_hiC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7definedC56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega7EnvRing5PExpr04C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMStateCZ_to_bv_bv_unsignedC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_RHEAPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap9ah_blocksC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_sizeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ablock_rangeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface@aclient_write_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<afs_write_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9aconst_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack09stack0_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface=aimg_client_wC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7ff_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8ff_classC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3fszC6ARocqVerifyHarness?AgentSubmission3bpB3Lib6LbB_SR=aconst_ok_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack0>stack0_ok_aappC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8AFS_SIZEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ATLS_PRIV_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ATLS_PRIV_HIC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6fframec6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI6ISTATEC4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI4IPREC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4hmodC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_MPRESC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD5FRAMEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD3spfK47Corelib7Numbers7BinNums1Z03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt>map_live_frameC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9bseq_nextC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_ALC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface3ICMC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB3lblC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;as_rauxv_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_RFSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack06stack0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own6lb_ownC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep5xpresC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD9obj_placeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_bseqC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HFind;BSEQ_boundAC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5u_hdrI5ARocqVerifyHarness?AgentSubmission7LibHash4HRep3hdr00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3aC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3cC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI3gzAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB:lbl_in_invC46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib5Lists4List9in_or_appC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD4rSheC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HFind>in_split_entsAC46Stdlib5Lists4List9last_lastC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_chainc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI9chain_atAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS7gz_subEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own9lb_own_InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD:wr_at_subEc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI:apart_subAC46Stdlib5Lists4List9app_assocC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap6ah_fsbC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7afsb_okC47Corelib4Init9Datatypes6lengthC46Stdlib7Sorting;PermutationBPermutation_lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI<cells4_splitC56Stdlib6NArith6BinNat1N6to_natC4ARocqVerifyHarness?AgentSubmission8PropExec3rdnC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD4shEeC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedK45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS8srl3_valC47Corelib4Init5Logic6eq_symK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okK5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6kn_fixC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells8cells_atC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<kwr_of_wr_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3sh0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8kshadow0K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_mulK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond02C56Stdlib6NArith6BinNat1N2leC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8v_addi_ZC4ARocqVerifyHarness?AgentSubmission8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26adenotC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib=sc_read_cellwC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib7sc_flatC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit:div8_boundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit9estart_shC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotK4ARocqVerifyHarness?AgentSubmission8PropExec7FPState01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26e_addrC5ARocqVerifyHarness?AgentSubmission8SymExec33SX27e_widthC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame6insideC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?munch_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S?mem_denot_growsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge>msteps_mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv=stk_mem_denotC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells6cbytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvDrw_cells_mem_denot_wC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKit7log_ivsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKit9munch_logC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge9rfull_mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge;msteps_fullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call=regs_keep_mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD=obj_window_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKit4wmixC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep7rin_ivsc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI7blk_winC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<client_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack0@stack0_transportC56Stdlib6ZArith6BinInt1Z7pos_subC57Corelib7BinNums6PosDef3Pos3addK46Stdlib9micromega5Tauto8GFormula01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI7dsh_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadowEaddressable_transportC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKitAxpres_munch_mixedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKitBrw_cells_of_cellw8C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C46Stdlib9micromega;ZifyClasses7rew_iffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB6lbl_inC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKitBcellw8_of_rw_cellsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKitBcellw4_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5u_bktC46Stdlib5Lists4List7map_appc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpICgrows_of_munch_cellc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI9ins_umapxC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC46Stdlib7Sorting;PermutationBPermutation_middleK46Stdlib7Sorting;Permutation;Permutation04C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>ah_mpres_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own;wr_at_wmonoK46Stdlib7Sorting;Permutation;Permutation02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own<lb_own_wmonoC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD9stage_endC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT9sr_blk_eqC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC56Stdlib6ZArith6BinInt1Z2geC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt7umap_shC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3bC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5hdkeyC56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6reg_evK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01I4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrameBrw_cells_transportC47Corelib4Init5Logic7f_equalK47Corelib4Init9Datatypes4bool02c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI2QII5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00C56Stdlib6ZArith4Znat3N2Z6inj_leI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3ATPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEI5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI5E_INSc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI3srIK4ELinuxProcessSemantics5Riscv5Instr5mulop01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD5E_ENDc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI6SCR_PNc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI4KNP0I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00K47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_INS : Z := 0xfa7a4.

Lemma gzA : forall m A n, addressable m A n -> n mod 8 = 0 -> gz m A n.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpI ()) [] "h07__arithh14__ffh26__sat0h38__varmaph45__with54__x1h64__x2h74__x3h84__x4h94__x5h:1Ah;2ADh<2Hdh=2Hih>2Hnh?6__sat1h@1ihA1mhB1np;3p;1p;2p;6p;4p;7p;8p-1p10000p4p710R0p8p1000Gp4p710R1p1000dp4p710R2p8P1p1001@p4p710R3p8p1001^p4p70P0p8p1002Vp4p70R0p1003Op4p710p8P0P1p8P0p1004:p4p710p8P0p1004fp4p710p8p1005Cp4p7210P3p8p1005op4p710P3p8p1006Jp4p7210R0P2p8P0P3p8g006gj3aTg007gj1=Tg008Lj1STg008jj22Tg009Jj2<Tg009fj2;Tg00:Aj24Tg00:^j2CTg00;Oj1MTg00;oj1KTg00<Oj1JTg00<mj1`Tg00=Kj1^Tg00>6j2HTg00>Yj6XTg00?=j2WTg00?_j2VTg00@9j2UTg00@ej38Tg00A?j3RTg00A^j4QTg00BPj3PTg00C1j2DTg00CNj29Tg00Ckj2OTg00D\j17Tg00E;j26Tg00Edj3ATg00FMj2LTg00G9j3NTg00GYj2FTg00H7j4BTg00HUj1ETg00I:j25Tg00I]j3TTg00J@j3@Tg00Jcj1_Tg00KEj43Tg00L0j2GTg00LLj6]Tg00MTj3ZTg00NKj7[Tg00Noj7\Tg00OSj8YTg00P7R3f0R0g00PUR238p=:1G20p=0P3f1R1g00Q3P0C3p=>P1g00QZR4g00R9R5P5g00RYR6P0g00S9F[p=1f2R7P4P5P5P6P1P0F\p=If3R8P4P5P5P6P7P1P0GYp=?g00SYAa710g00TQR9#=R:#=R;#=#SR<,21#:%001<08';f6R=f5R>f4R?14>1P81C?<%0?%0<R@12=<#0[[g00U6RA#MRB%KARC%J3RD%`3RE%^3RFP4P5P5P61H3<R41H32RG'>,1FEX1WF6R6P0P7g00UbRHg00VBRI'V1U07=8HIdAR321CQR2b1b3b4%:<g00Vb[P0b0b29P?<1D?<,9<12?<'4983?1C><%0>f7/2<#0\@[1O=<%0=f8RI/D<RH#0\@[g00W?R@#7RJ#7RK#7#7,63163K163J163@5A35A35A3g00W^'L=NABPCP3P31F3?P7PDCBP1P31F3>P8PDCBCBPEPF%E:,53RE%E9,539T34R4153;R;5@3'>,1F%_5R5PFP3PGg00XJRD153:R:C3,1FP3P:g00Y1R1PEC3,1F5IFP5PF1>;G,1FP5P31539R9PDA@39:R:C3,1FP3P:P1A@394C3,1F5IFC?C?C?P6P2b1b3b4X53X63X73X83X9319<7/48983?%071<7>';%:>148?R2,G819<>,48,<2';[[[^53^63^73^83^93P0PI12I<PHP>f9P8P?P=O8b0b2b?b<E]W=X@3AZ?87eW>W;XB3X:3WAo"). Qed.

Lemma chain_atA : forall (V : Type) (M : mem) l1 (p k : Z) (v : V) l2,
  chain ASEGS M (l1 ++ (p, (k, v)) :: l2) -> cell8 ASEGS M p (hdaddr l2).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpI ()) [] "p'0h01kh12l2h21pi001ph31vh42l1h51Hh62IHh71Mh81Vh91ah:2kvh;1lh<1qi011zp;1p;3p;2p;5p;4p200R0g00YXR1p4p710p8P0g00ZPR2p4p7210p8P0g00[GR3p4p710p8P0g004fR4p4p710p8g00;oj11TP4j35TP1j27Tg00;Oj1=Tg00[ij3<Tg00G9j38Tg00\Dj3;TP3j5:Tg00\_R3j2@Tg00]?j49TP2j4?Tg00]_j4>Tg00P7R2f0R1'@p=0P2f2R4f1R5P1C9p=4f4R6P2f3R7P4P5C9;81p=3g00^VR8P4P5P1C?p=2P8P4P5P1C>p=6g00`4%05#0#1%04#0R8%18f5R9f6R:#0R;#0R<#1f7R=%0=R>#0R?P?P>P7A4=45P1D375672:f8R>/7596=6[]1]3^02^22W4%09#0#1%=<P<P;P7A4:45P1D355<92:917=596:6A2=:5;<1W5W1X36X02X22P3P2%07%06#0#1%0>#0#1f9R3%03R<#0R@P@P<P7A4345P1D375672>f:R</759636[]1^3=^02^22%1@%0<R@#0RAA8A:9PAP@P7A4<45P1D33592<3f;R3/7596<6[]1^3>^02^22[];P1%1?%03#0#1f<R?%0?R@#0RAPAP@P7A4?45P1D3756723f=R@/7596?6[]1^3<^02^22%1A%0@RA#0R<P<PAP=P:P9D3P<PAP7A4@45P1D33592@?P9P6P7P4P5f>R9%09R?#0RAPAP?P6A4974P5D375:R:'796@>A29@:;;1O5W5W1X33X02X22W6W4X:;X<2P5P1O2n2001100000120101100X98P1D:W4W7X80o"). Qed.

Lemma apart_subA : forall a k b m k' m', apart a k b m -> k' <= k /\ m' <= m -> apart a k' b m'.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpI ()) [] "h04__x1h14__x2h24__x3h34__x4h44__x5h54__x6h61Hh72H0h82H1h92H2h:7__arithh;4__ffh<8__varmaph=5__with>1ah?1bh@1khA2k'hB1mhC2m'p;4p;2p;1p;3p;7p;8g00`ej4=Tg00L0j20Tg009fR0j2OTg00D\j16Tg00E;j24Tg00Edj38Tg00FMj2ATg00;Oj1NTg00G9j3>Tg00;oj1GTg00GYj29Tg00H7j4:Tg00<Oj1CTg00<mj1STg00=Kj1RTg007gj1<Tg00I:j23Tg00HUj1BTg00Jcj1QTg00J@j35Tg00?=j2MTg00?_j2LTg00@9j2KTg00@ej3JTg00A?j3HTg00A^j4ITg00:Aj27Tg00a\j2?Tg00KEj4FTg00NKj7ETg00b6j7DTg00OSj8PTg00P7R1f1R2g00XJf0R3CFp=2P2g00QZR4g00R9R5P5g00RYR6P3g00S9FEp=1f2R7P4P5P5P6P2P3FDp=@f3R8P4P5P5P6P7P2P3GPp=;f5R4f4R9P8P7C=1074R:1028'OP0f6R0,081079f8R;P9P0P8C=P3104;f7R<,04g00U6R=g00W?R>#6R?#6R@#6RA#6,41141@R@141>581581g00W^R>'A141A141?981@581/A>%N=5>=3>%G=P1P11919P71910C:P2P11914P8%C1C:C:%S1%R1R=g00TQR>#<R@#<,31R?%B>RA#<,31RB'2,1=%Q5R5P=131@RC%B@,31R@'2,1=P5P=131>R>=51@131ARA'2,1=A51AB/2>,1=5@=P5A51>C/2A,1=A51A?/2>,1=5@=C;C;C;1M=6P3P7g00UbR=g00VBR6'L1K37=J=6dg00PU=H12CIb;b<b=X01X11X21X31X41X5110841770/09179</07'?1789/041740/08'?[\:[^01^11^21^31^41^51P3f9R:f;R8P<f:P;f<P2P7P0O9b:P8P<P:P0C=eW9W8P2P3O2n2001000000121000000W7W6XC1XA1XB1X?1X@1X>1o"). Qed.

Lemma last_in_ne : forall (T : Type) (l : list T) d, l <> [] -> In (last l d) l.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpI ()) [] "p'0h03Hneh12IHh21li001lh31Hh42H0h53Heqh61Th71ah81bh91dh:1ei011tp;1p;3p;2p;6p;5p200R0g00bZR1p4p710p8P0g000dR2p4p710p8P0g00[GR3p4p710p8P0g00c1R4p4p710p8g00;oR5j10Tg00;Oj11TP4j34TP1j35Tg00?_j29Tg00@ej36Tg00cJj28Tg00G9j33Tg00cij3<TP2j6;Tg00dCj17Tg00d\j3:TP3j5=Tf2R3f1R2f0R136#7p=2%01P3%03R4f3R6#0R7%16R8721f4R9A4923;52[W2%13R:=24:1978A6788%19R8=493=598P2P1O1'8b5W0%09?218f5R8A4826;52[%08A3832%1832P5f6R:f7R4#0R;%14R<721f8R=A4=2:;52[%0=A3=82%1=R>32f9R?A3?:3R@=4?4;5@]0]1P3%0:%1:R@;2@A44<8=54<[A349<=2;<A3=8>=4=:R:96=8A5=:>19=:3<W0W1%0?f:R:#0A3:21%1:32f;R>A3>32R8=4>?;58[%0>A3>=8%1>32f<R>A3>63R8=4>:R:76?A5>:8P2%0>%1>768R8f=R>#0R:A3>96P5f>p-0P1g00VbR5g00e6n10110000020020000000X::g00eR%1>P1E;P51851b4W3%78eO13:W0W1W2X8=P2P1O2n10110000020020101100P2P1O2W0W1X27X73P2D=X92W2X60o"). Qed.

Lemma ins_umapx : forall (LBl : list (Z * Z)) (m M1 : mem) (obj key p bl2 bc2 : Z) (l1 l2 : list (Z * (Z * Z))),
  umapx MI_A 24 (nval24 ASEGS) LBl m obj bl2 bc2 (l1 ++ l2) -> bc2 <> 0 -> Zlength (l1 ++ l2) + 1 <= bc2 -> 0 <= key < 2 ^ 32 ->
  In (p, 24) LBl -> 0 < p -> p + 24 <= 2 ^ 47 -> p mod 16 = 0 -> apart p 24 obj 40 ->
  (forall q n, In (q, n) (umap_blocks 24 bl2 bc2 (l1 ++ l2)) -> apart p 24 q n) ->
  mem_grows m M1 ->
  (forall a, umap_foot 24 obj bl2 bc2 (l1 ++ l2) a -> ~ (lasta (obj + 16) l1 <= a < lasta (obj + 16) l1 + 8) ->
             ~ (bl2 <= a < bl2 + 8 * bc2) -> M1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  cell8 ASEGS M1 p (hdaddr l2) -> cell8 ASEGS M1 (p + 8) key -> cell4 ASEGS M1 (p + 16) key -> cell4 ASEGS M1 (p + 20) 0 ->
  cell8 ASEGS M1 (lasta (obj + 16) l1) p ->
  (forall i, 0 <= i < bc2 -> exists b', cell8 ASEGS M1 (bl2 + 8 * i) b' /\ bucket_ok obj bc2 (l1 ++ (p, (key, 0)) :: l2) i b') ->
  forall M', munch [(obj + 24, obj + 32)] M1 M' -> mem_grows M1 M' ->
  cell8 ASEGS M' (obj + 24) (Zlength (l1 ++ l2) + 1) ->
  umapx MI_A 24 (nval24 ASEGS) LBl M' obj bl2 bc2 (l1 ++ (p, (key, 0)) :: l2).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpI ()) [] "p'0h04__x1h16__sat5h26__sat7h37__arithh44__ffh56__sat3h66__sat4h76__sat6h86__sat8h98__varmaph:5__with;4__x2h<6__sat9h=1Hh>4__x3h?4__x4h@4__p1hA7__sat10hB4__x5hC1xi001xhD2HahE1ahF2b'hG1yhH1nhI4__p2hJ1ihK1li011lhL1pi021phM1qhN1zi031zhO1AhP3AG1hQ2CBhR5CpredhS3CszhT2HLhU5HloadhV3HpahW1UhX3HinhY2_HhZ2l1h[1Bh\2Hih]2Hqh^3Hq0h_3Hq1h`3_H0ha1ehb1fhc1khd2l'he1mhf2p0hg1vhh3AGshi3Cb'hj2Chhk2Ckhl2Cnhm2Cvhn2H0ho3HLRhp3Hanhq3Hbchr4Hbl0hs4Hbl1ht4Hblohu2Hdhv3Hkrhw5Hlasthx3Hnbhy3Hnphz3Hnsh{3Ho0h|3Ho1h}4Hoalh~3Hoki043Hp0i054Hpali063Hpci073Hpli083Hpoi093Hqai0:3Hqoi0;2Hri0<2Hxi0=2Hyi0>2Hzi0?3LBli0@2M'i0A2M1i0B3MG'i0C3MG1i0D3MU'i0E3_H1i0F3_H2i0G3_H3i0H3_H4i0I3_H5i0J2a0i0K3bc2i0L3bl2i0M2e0i0N3keyi0O3l1'i0P2l2i0Q1oi0R3objp%0p%1p%2p&0p&1p;2p;1p;3p;4p;5p;7p;>p;?p;6p;:p;Qp;=p;8p;Bp;<g00\_S00k20sTg00;oS01k103Tg00HUj1{Tg007gj1UTg008Lj1ZTg00enk11Jk40UTg004fj34Tg00ffk20JTg00bZj38Tg00`ej4FTg00gCk50GTg00h@k20kTg00i6k70<Tg00:AR0j20Tg00j1j2=Tg00jmk10CTg00kKk10dTg00knk10}Tg00lPk20@Tg00@ej3?Tg00YXk20bTg00m6j4wTg00CNj2MTg00;Ok10XTg00G9j3HTg00mmk31TTg00njm>1RTg00odm>1LTg010^m>1ITg011Xm?1GTg012Qm>1ETg013Jm?1DTg014Dk20ETg009Jj2;Tg00:^j2@Tg015Ck20OTg015kk30QTg00D\j1yTg00E;k20rTg00GYk208Tg00<Ok112Tg00<mk111Tg00=Kk110Tg00>6k20hTg00Jck10gTg00I:k20fTg00?=k20~Tg00?_k20BTg00@9k20|Tg00A?k30{Tg00A^k40zTg016Ok40?Tg016jk20cTg017Tk20yTg0185k30aTg018Xk20`Tg001@j6xk71BTg019Rk40xTg01:QS02j2WTg00a\S03j2LTg00cik30^Tg00]?j4~Tg00c1k30=Tg00dCj1}Tg000dk60]Tg00cJk20wTg01:kk40vTg01;lk40\Tg00d\k30uTg00L0R1j22Tg01<Fk41UTg01<eR2k10TTg01=Cm:02Tg009fS04j23Tg01>Ek21Fk316Tg00I]k30RTg01>bk40LTg01?>k51CTg01?]k20pTg01@Ik10oTg01@gk41ATg01AJk21>Tg01B3k30PTg01B\k40mTg01CGk61=Tg01ComQ1<Tg01E0m=1;Tg01Eik20lTg008jk20NTg00]_k409Tg01Fbk61:Tg00Edk30MTg00FMk20jTg00H7k419Tg00KEj4zTg00NKj7gTg00J@k318Tg00b6k70iTg00Nok70STg00>Yk617Tg00OSk806Tg01G]mB1KTg01HUk515Tg01IGk61MTg01Ikm<14Tg01JPmB13Tg01K6m<1OTg01K[S05g00^VR3g01LUS06g01MOS07f7R4g00P7R5f6R6f5R7f4R8f3R9f2R:f1R;f0R<N=1;p>0Dg00PUR=9?5<#}p=6A4:;<-0l9p>0A10:;/2<p=512=:1;;<'3p=OP5P5P;P<C~p=D1;=<p=<20N;<=?5=p>0I10;<,;:p=o12:;/3<#}p=S1M;<,0:,;9p=lP3P:P;P<H09p=`P3P910:;P<H09p=|P3P:P;P<Cwp>0_12=<p=11;;<,3:p=9P5P9P:P5P5P;P=C~C~=H8<p=[P5P6P7A489:P;P<J1:p=PP3P8109:P;H09/3<p=G1W5<p=X20l:;/0<p>0H1089,2710:;/2<'Lp=n20N;<,2=p=B20r5<p=vB0M5;<p>0Fg00U6R>B0M5:;g00W^R?+0j;H<p=pP5P:P;P<H19p=:20f5<p=^P:g00QZR@g00R9RAPAg00RYRBP5P;g00XJRCP<Czg00S9RDFgp=CP:P@PAPAPBP5P;g00Y1REP<CzPDFgp=VB185;<p=720h5<p=sP6P@PAPAPBP7P@PAPAPBP5P8PCP9CzPDFgP:P@PAPAPBP5P;PCP<CzPDFgK0ip=iP8P@PAPAPBP9P:P@PAPAPBP5P;PEP<CzPDFgK0Sp=cP;P@PAPAPBP<J17p>0eP9P@PAPAPBP:P;P<L06p=>P6P@PAPAPBP7P8P9P@PAPAPBP:P;P<L06L06p=IP7P@PAPAPBP8P@PAPAPBP9P:K0SP;P<L06p=b129:12;<'Lp=K12:;/3<p=JB0M5;<00j?p>0>AH>;<p>01P5P;PCP<Czp=TP8P@PAPAPBP9P@PAPAPBP:PDFgP;P<L06p=j1M;<,0:p>071=:;=?5<p=]B165;<p=YA89:;/3<p=N20B5<p=tA?5;<p=E12:;/L<p>0[12:;/3<,39p=a12:;/L<,39,38p>0ZP:P@PAPAPBP;P<K0Sp=_12=912:;/3<'3p>0YP5P:P;P<C~p=f12=6127810:;,29/L<'3'3p=uA4:;<9889p>04Q05P3Q06Q07P<P5P;P:P9P8P7P6P4f8RCf9R?f:RFf;RGf<RHNB1Kp>0tQ05P3Q06Q07P<I15p>00P8P9P:1M;<CFp=AP3P4P6P7H0UP8P9P:P;CF/3<'3p=Q1;:;,39/3<p=rP3P8109:P;Cw/3<p=e20N:;=?5=/3<p=R13;<,3:p=dP8P9P:P;CF/3<p=\P3P9P:P;H0U/3<,38p=qP3P7P8P9Cw13:;/3<'3p>0WP3P:P;P<H0Up>0VP3P7P8P9Cw13;<,3:'3p>1SP3P910:;P<Cwp>1QP9P@PAPAPBP:P;P@PAPAPBP<PDFgK0ip>1P12;<,L:p>1NP8P@PAPAPBP9P:P;P@PAPAPBP<PDFgL06p>05P;P@PAPAPBP<J1Mp>0:10;<,;:,39#}p>1HP8P5P9A4:;<H0L9857p=h129:1;;<'3,38p=mP5P;PEP<Czp>0KA8:;<,39p=kP3P6P7P8H09P3P9P:P;Cw/3<'3p>0;P3P9P:P;H09/3<p>0qg01NIS08P5P5P5P2P2P7P8P9P:P;P<N<14p>1@P5P5P5P5P5P5P0P<P;P:P0P9P8P7P6P4PCP?NB13p>1?P5P5P1P4P1P6P7P8P9P:P;P<N<1Op>0n20s55R1$03g00`4S09Q0920s51R0$03R2g00TQRE#{R@#US0:#U#U#ZRD&1J3S0;P?PCP6P9P:A40;<L0D%69P0P0P9P:H0A%ZERI;58%UERJ#ZRK%UJS0<#URL#URM#URN#ZRO+0JRP9OCCS0=1DCDf=S0>581%<?%{JS0?#{RQ#{#{S0@#ZRR-0JKRS95FDS0A%ZMRM-0IGS0BPHPDf>RTQ0?#US0C#URU#U#ZRVCF1D;<S0DPDP5PTQ0>A40HGI0G581f@S0EPDP:P;CF[^H5^M5fBRWfAS0F+0kPDP5PWf?RXPTQ0>=40HP<K0<fCRY/0MS0G/=TRZ%ZLR[9o;Z7S;Q0FP:Q0FP[Q0ECl7S:&0CLS0H$0dS0I$0}S0JfFS0K%UNS0L$0CS0M00@9S0NO1fGRNQ0NO13?[[[^E5Q0E20b5H5`YfDRZQ0FP[PWC|fES0O10WMS0P<0_YP3Q0K%ZUS0Q,0YP=CwQ0K/0MS0RQ0F'==`NZ%1<S0S?9<ZfKRUPN1M[:S0TP<fJS0UQ0KP0Q0OP0P1fHR\fIR]PZD[P:P<FPDGXF5#X[^J5Q0M$0dS0VQ0J[10]DS0W10]O'D&0X1S0X5H1Q0U<1T<20kU;P:PUPDQ0KQ0O540>0H0IC|Q05P3Q06Q07PDP5Q0;fOR^fNS0YfLR_P]P\Q0K940NQ0ON>1R%<_S0ZQ05P3Q06Q07PDP5Q0;fPR`P^fMRaQ0UP]A40\NQ0KN>1LA5aVSQ05P3Q06Q07PDP5Q0;fQRbP`Q0YPUQ0UA40]\PNN>1IQ0Y00I[Q05P3Q06Q07PDP5Q0;fRS0[PbP^P_PUQ0U=40]P\PNN?1GQ0ZQ05P3Q06Q07PDP5Q0;fSRcQ0[P`PaP_Q0U940UP]N>1E1M[_=5aSQ05P3Q06Q07PDP5Q0;fTRdPcPbQ0YPaA40_UQ0UP]N?1DQ0Y1M[aPbPVCF%1;S0\A5:;SS0]109:fVRePDPePOP9EnS0^Q0S?9<8PXQ0M106;Rf+0@S0_P5PffZRg/0D10gO'DQ0X5H100E<XN5fYRh/0DRi10hORj,;f7Sfg00e6S0`1@h[S0a%1hS0b%1[S0cf[Rk/B[[[S0d20OKRRl%<KRm%1R%<S[Rn[Ro%1KRpQ0`B0QKR;UWDRRQ0`%1S[^DpRq20OKORr%1O%<P[Rs\mRtQ0`B0QKO;UXDpRuQ0`%1P[^DpRvf\Rw/@M%1wS0e%1MS0ff^Rx/BM[[g00W?Ry#yRz#yS0g#yR{#yR|#yR}#vS0h%v|S0i%vz+0FS0j%y}S0k#vS0lQ0i20r5yS0m+0FS0n&0X>Ry3p3p&03>R>2085:S0o&125R}20857S0p?:8}7:97:;&115Rz&105R|P|20h5=R~%^@S0q5C|Q0q%^QRQ5V|&0gARAP|P|P|%^JS0r/7Q20f5ERE%sDS0s'7S0tP|%sOS0u,7ES0vQ0rFiPAP|AV|~ES0wPAP|%{@#^S0x9V|~S0yPAP|Q0tQ0rQ0q'7R@5C|P|P@Q0vDc-0e|C>FIEb20~|BRBP<P:g00UbR@g00VBRJ+0B20|<:=?@JdB0{5=;H0zRJb4b9b:X05X;5X>5X?5XB5%1:S0z?9:810:710;DS0{10;OS0|P:CK%<:S0}%<6S0~108DS101076R@108OS11,;@3Jg00VbS12[[[[[^05^;5^>5^?5^B5P<PHPxPCQ0>f`S13P4P?PYPdO9b3b5b6b1b7b2b8g00eRS14H0?1DijQ0X5H100EfeQ0MQ0_+0cQ0aQ0dPlPoPRPqPrPtPuPvQ0L#ZRj-0OKS0L%1j20JKjRi#<[S0d\mS0aQ0`B0QKj;UXDpS0_Q0`%1i[^DpS151@xMS16%1xQ0fQ13/BM[[S17P:g01Ng20y=K+0BPmeRmO1RpQ0dP7PmO1RjPsPCPmO1S18PnQ0hQ0n+0>S19Q0l%v{Q0m+0FS1:+0>S1;001y+01S1<P>20858S1=?:7}20859S1>7::Q0p?:7}9:}77:;PzP|P|Q0r9C|~S1?Q0r=V|QPAP|P|17EQ%sKRKQ0@$0C60a5RQ'TPAP|AC|~ES0@PAP|%^L9V|~S1@PAP|Q0:#^9V|~S0:PAP|Q0r,7ERL9C|~P|PLQ0M:0a5KS1ADcC>FIDjEbPBPJb4b9b:X05X;5X>5X?5XB5Q0\?9;8A5;7SQ0zQ0~Q0~AO@@i[[[[[^05^;5^>5^?5^B5P<Q0FfeS1BfcS1CQ0>PWPHPXQ0EP\PhO:b3b<b2b1b5b6b1b7b2b8b<bA-0`fExO2W\XJ5fXRfPTP8P9H0xR@eWuWpWDXH5XE5Q0\Q0]Q0^P@[[[^H5^E5Q0YP220B2<A?2^<Q01P0A?2b<PDQ0;PgPhfWR@PdPcA40;bL0DP0P0P:Q0[H0A?5IdQ0DPDP5PfP@fURK9407RLI0G581PgPDP:P;CF[^H5^M5PDP5PkPfP@PLP<K0<10wMS0]/=6RLAo;L[7S;B07g[hS0^,;:9Sg:Q0Jf_RLQ0NO1S1DQ13Q0NO13?[[[^E510kMS1E/=7=`whQ0S?9<hQ13PwQ0TP<PLPkP0P?P0P1f]R{PxPhD[S1FP:P<FPDGXF5#X[^J5PZP{PDA404@>0H0IC|10xMS1GQ1G7]CP0P<P?10LMS1H1Y1<S1I7]?CNXG0,W0'L]S]Q]R]P]V]U]W]TP;&0X0Rm9?2`PDQ0;PhPfPePcQ0[A40m`L0DP0P0PmPbH0A?5IcQ0DPDP5P@PeA40mdS1JI0G581PhPDP:P;CF[^H5^M5PDP5PgP@PeQ1JP<K0<Q1E/=mS1JQ1J=o;[7S;B07h[fS1J,;:9Sh:Q0JPxQ0NO1Q1D3?[[[^E510gMS1D/=m=`kfQ0S?9<fPLPkQ0TP<PxPgP0PmP0P1PwP{PfD[S1KP:P<FPDGXF5#X[^J510wDS1LA40me>0H0I5`Y10{MS1MQ1M7]mP0P<PmQ1GQ1I7]mCNXG0,W0Q1M#t40^WSWQWRWPWVWUWWWTAH0;<9?2dPDQ0;P{PwPgP@PeAH0:;=40dL0DP0P0AH09:PKH0A?5I@Q0DPDP5PkPgAH067S1M=40fS1NI0G581P{PDP:P;CF[^H5^M5PDP5PxPkPgQ1NP<K0<Q1HAH046'=S1NQ1N=o;[7S;P:P{P[PwCl9S{:Q0JfbS1NQ0NO1Q1CQ0NO13?[[[^E5Q1GQ1M'==`LwQ0S?9<wQ1CPLQ0TP<Q1NPxP0AH0F?S1MP0P1Q13faS0NPwD[P:P<FPDGXF5#X[^J5Q13/0DS1OAH0C4=40g>0H0I5`NQ0N/0MS1PAH0?CS1QQ1P3]P0P<Q1MQ1N/0MS1RQ1MQ1I3]CNXG0RI,W0P0PIP5P1P=P5P5P=P=C~C~S1S:0=0wRIP2PwP0Q1S:0=0{S1TP<Q1R/=<S1UQ1T,Y1'ECNXK2A80IwQ1P/=wS1P1Y1I'EP0PwQ1SP2Q1QA?2<m#}XZ2Q1Q=?2mS1TP2Q1MQ01P0p-0RIP<Q12Q0`n10110100020020000000Z0M2Q14PmP<J0]Q12Q1200w<bnW=Q1T#}ePwP4ExH0vP2Q1QQ1UQ1S:0=0<,Y1'EXZ2Q1QQ1S60=0,Y1#tPwP4ExH0?Q1QP4J0]H0\40uWSWQWRWPWVWUWWWTZ0O2Xa0P;P<O2n10110101020121102101P<Q0YP_Q0OPYPTQ0>P?O8bTbK10cMS1QQ0YQ1Q3]P0P<P^10dMS1S/=^S1UQ1I'ECNXG0,W0'LQ03Q1UQ1S'EP0P<P`10KMS1T/=`S01Q1I'ECNXG0,W0Q01#1S1MQ01/0[RmPS10KDS1V10KOS1WQ01'2S1X60[mCaP<Q01Q1T'EP510eMRmQ0S10<[S1T/2SS1YQ1T10@DS1Z10@OS1[/2<I0ZXN51@e[%1eQ0c1Bf[[[PlPoPRPqPrPtPuPv1@hMQ0bQ0f1BkM[[PpPsPjPnPyP>2085;S1\PzP|P|%sVS1],7E/TQPAP|Q0wPA%sM,7ES1^9C|~S1_Q1^%s[S1`'7S1a=C|QP|P|Q1aQ0tP|Q0vQ1^Fi5_|5_|C>DjPBPJb4b9b:X05A5<VS%<;S1a10:MS1b#1S1cQ1b/0[S1dPSQ1d10:DS1d10:OS1eQ1bCKCa[[^05P<PLQ0FPWO3b3b2b1b5b6b1b7b2b81=mbRmP<ExW=P<O1P0P<PbQ1I,EmCNXG0,W0Q02P0P0P<Q0[10@MQ0['=S1fQ1I'ECNXG0Q1fQ1f/0[S1gPSQ1gQ1ZQ1[Q1fCKH0YP<Q00P5P1P0P<PKQ1DQ1I7]KCNQ1E/=eRm10m[S1EPSQ1E10kDS1E10kOS1DPmCKH0Y[P<Q00P5P5P0Af1:<S1[PhQ1G/=hS1GQ1[,Y1S1Z'ECNQ1H/=gRm10m[S1HPSQ1HPLPDA5LOmFu[P<P0Q0D9f17S0DPwQ1PQ0D,Y1S1H'ECNQ041D:;9f16S1P=80{Q1RQ1P,Y1S1h7]{Q1C/0M/=xRm10m[S1RPSQ1RQ1CPDQ1C?5OmFuP<1D899f1CS1R=80LQ1B/0MQ131D789f1?S1i,Y13]P51D67S1j9f1F,Y1S1kQ0SQ1YQ1TfgS1l/0DQ1l?5O<I0ZXN5PDQ0;fiS1mfhS1nffS1oQ1CQ1NQ0NQ13540PLPFP6P7g000Gp4p710S1p&03<S1q&03;S1rQ04P9P<P9P:P;I04A88;9A88;:'LRm[A89<:A89<;'LP8P;P8P9P:I04[S1sP7P:P7P8P9I04\mP9P:P;P<H1UP<n2001000000120000000XE:WdWKWOQ1pQ1qQ1rQ1s^E:]d]K]OP<P0Q1NQ0N1D46S1p9f1GRmQ1N980mQ0N980m<0^:O5b=N=0tP11DFDQ1m$00%<FQ0AQ1nPFP[P6Q1nPFPMP6%16P6PPQ1nPFP7PFPDQ1oPVQ1N#6PGPDfdS1qP[Q1CDA[GQCrDeDG9RFM3dCNQ041DGDfjS0A$00581%<GA5GDSQ0BQ1mPGP[P4C|Q1mPGPMP4%14S1r?94PS1sQ1mPGP6PGPDQ1lPVQ1C#6PHPDQ1BP[Q1qDA[D\DqDe3d3d%1HS0B10H[RmPSPmQ1nPDQ1nPOPHEnCaP<Q0>/DDflS1t$00581%<TA5TDSQ1tPTP[PFQ1tPTPMPF%1FPFPPQ1tPTP?PTPDQ0APVQ1o#6PXPDQ1nP[Q1lDA[GQCrDeDG9RTM3dQ04%<X10XDfmS1uPXP[PGQ1uPXPMPGAOGGPS1vQ1uPXPFPXPDfkS1wPVQ1l#6Q0EPDQ1mP[Q1nDA[D\DqDeDG9RXM7JSQ0E#1S1xQ0E/0[RmPSPmQ1tPDQ1tPOQ0EEnCaP<Q0F#<10WDfpRmPWP[PTPmQ0PPT%1T1;TPPmPWQ0>PWPDfnS0PPVQ0A#6PYPDQ1tP[Q1wDA[GQJ0WDG9RWM7JSQ04A5YDSfqS1yPYP[PXQ1yQ0GPXAOXXPS0GQ1y@0VYTPYPDfoS1zPVQ1w#6PZPDQ1uP[Q1tDA[D\J1SDG9RYMPZ10Z[S1{PSQ1{PmPDA5mOZFuP<Q0O?5DSQ0KftS1{Q0KP[PWQ1{Q0RPW%1W1;WPQ1{Q0KQ0FQ0KPDfrS0RPVQ0P#6PNPDPmP[Q1zDA[GQJ0WDG7RMQ0420INMfuS1|PNP[PYQ1|PNPMPY%1YS1}?9YPS1~Q1|PNPWPNPDfsS20PVQ1z#6P\PDQ1yP[PmDA[D\DqDeDGP\10\[S21PSQ21Q1{PDQ1{?5O\FuP<20I]MS22fxS23Q0UP[Q0KQ23Q0UPMQ0KQ0K#1S24Q0KPPQ23Q0UQ0OQ0UPDfvS25PVQ0R#6PUPDQ1{P[Q20DA[GQCrDeDGQ04fyS26PUP[PNC|Q26PUPMPN%1NS27PNPPQ26PUQ0KPUPDfwS28PVQ20#6P_PDQ1|P[Q1{DA[GQCrDeP_10_[S29PSQ29Q23PDQ23?5O_FuP<f{S2:10a[S2;;`]f|S2<Q0YPMQ0UQ0U#1Q0UPPQ2<Q0YP]Q0YPDfzS2=PVQ25#6S2>P^PDQ23Q28,M[S2?CF[GQCrDeQ04f}S2@P^PMPUH1Q%1US2APUPPQ2@P^Q0UP^PDQ2:PVQ28#6P`PDQ26P[Q23DA[GQCrP`10`[S2BPSQ2BQ2<PDQ2<?5O`FuP<p+01@S2C10bMS2D<0_aQ0Y#1Q0YPPp+01AS2EQ0[PaQ0[PDf~S2FPVQ2=#6S2GPcPDQ2<Q2:,M[S2HCF[GQCrQ04%1^S2I?9^Pp+01BS2JPcQ0YPcPDQ2CPVQ2:#6PdPDQ2@P[Q2<DA[GQ%1dS2K10d[S2LPSQ2LQ2EPDQ2EPOPdEnCaP<AObbPp+01ES2MPePbPePDp+01CS2NPVQ2F#6S2OP@PDQ2EQ2C,M[S2PCF[GQQ04p+01FS2QQ0[80V@P@PDp+01DS2RPVQ2C#6PfPDQ2JP[Q2EDA[D\%1fS2S10f[RmPSPmQ2MPDQ2MPOPfEnCaP<p+01HS2T@0VhdPgPDp+01GS2UPVQ2N#6PkPDQ2MP[Q2RDA[D\Q04PkPDQ2TPVCFQ2R#6PwPDQ2QP[Q2MDA[Q0e10w[RmPSPmp+01IS2VPDQ2VPOPwEnCaP<P{PDp+01JS2WPVCFQ2U#6PLPDQ2VP[Q2TDA[p+01LS2X/@[Q2X#1Q0cp+01NS2Y/B[[[PlPoPRPqPrPtPuPvp+01ORm/@M%1mQ0fp+01Q/BM[[PyP>Q0o?:;}S2ZPzP|P|Q0tQ0r5C|S2[P|Q0rQ1]'7/TEH1PS2\PAP|Q0t=C|QS0tPAP|Q0wPAQ0@Q1`,7ES2]=C|QS2^P|P|Q2]Q0rQ0s'7S2_P|Q0rQ0u'7S2`PEFiS2a5_|5_|C>FIPBPJb4b9b:X05X;510<DS2b/2;S2c10;V<1N<S2dQ0{/2SQ0}P9109[RmPSPmQ10Q11P9CKH0Y[[[^05^;5P<p+01SQ1oPCP`PdO5b3b5b6b1b7b2b8Y0IY0:P;P<O2n2001000000121000000W=Y0HP;P<O2n2001000000121000000W=Y0GP;P<O2n2001000000121000000W=Y0FP;P<O2n2001000000121000000W=Y0EP;P<O2n2001000000121000000W=W`P;P<O2n2001000000121000000W=W_P;P<O2n2001000000121000000W=W^P;P<O2n2001000000121000000W=WYP;P<O2n2001000000121000000bEQ1kQ1k/0[RmPSPmQ1oPDQ1oQ1k75OFueQ1o/0MQ0N'=P<ExW=Y0=P;P<O2n2001000000121000000W=Xg5Xc5P;P<O2n2001102000121103103Xf1XM5P;P<O2n2001102000121103102XC0P;P<O2n2001000000121100000W=P<O1n200100000021100011000Q1UQ1U/0[RmPSPmPdPDQ1U95dOFuQ05P3Q06Q07PKPdPfP@PHPcQ0[PbP`P^Q0YPaP_PUQ0UP]P\PNQ0KQ0OP3PePHPcQ0H20b5^PWP:PcQ0H$0TS071@K[Rm%1KS06Q0c1B@[[[RZPlPoPRPqPrPtPuPv1@fMS05Q2SQ0f1BgM[[S2SPpPsPjPnPyP>Q1\PzP|Q0wPAQ0@C>PBPJb4b9b:X05%<<S1UQ0\[^05P<PwQ0[O2S1kb3b2b1b5b6b1b7b2b8%1cePmPZPlPoPRPqPrPtPuPvQ05Q2SPpPsPjPnPyP>Q1\PzP|Q0tPAQ2^C>PBPJb4b9b:X05Q2b/2SS1110;[S2e/2SS2f[^05P<PwPbO2S2gb3b2b1b5b6b1b7b2b8Q07,0cS2h/2SePmPZPlPoPRPqPrPtPuPvQ05Q2SPyP>Q2ZPzP|Q2\PAQ2aC>PBPJb4b9b:X05X;5Q2dQ2eQ1dQ1eP;CKS2i[^05^;5P<PwPgPaO3S2jb3b5b6b1b7b2b8Q2hQ1VQ1WPcCKeO5PmPZPlPoPRPqPrPtPuPvQ0LQ0aQ0_Q151@gMS2k%1gQ0f1BwM[[S2lPpQ0dPjPsQ18PnPyP>Q1\PzP|Q0tPAP|Q0wPAP|Q0@P|PEQ1ADcS2mFIPBPJb4b9b:X05Q11Q1aQ0z?9:i[[^05P<PLPdPKO3S0zb3b<b2b1b5b6b1b7b2b8b<bAPmPZPlPoPRPqPrPtPuPvQ0LQ0aQ0_Q15Q2kQ2lPpQ0dPjPsQ18PnPyP>Q1\PzP|Q0tPAQ2]Q1A5C|S2nC>PBPJb4b9b:X05Q11Q2e/2iS2o[^05P<PLPdO2S2pb3b<b2b1b5b6b1b7b2b8b<bAQ2h/2ieN:02P3PePH10c[S2hQ0HPdQ0FP:Q2hQ07PmPZPlPoPRPqPrPtPuPvQ05Q2SPpPsPjPnPyP>Q1\PzP|Q0wPAQ2]9C|~S2qC>PBPJb4b9b:X05Q1UQ2e#1[^05Q1kb3b2b1b5b6b1b7b2b8Q2h#1ePmPZPlPoPRPqPrPtPuPvQ05Q2SPpPsPjPnPyP>Q1\PzP|Q0tPAP|Q2]Q1`'7S2r/TQI05PBPJb4b9b:X05Q11Q2e/0[S2s/2S[^05Q2gb3b2b1b5b6b1b7b2b8Q2hQ07'0S2t/2SePmPZPlPoPRPqPrPtPuPvQ05Q2SPyP>Q2ZPzP|Q2\PAP|P|Q2rQ2_P|Q2`Q2]FiC>PBPJb4b9b:X05X;5Q2dQ2sQ1dQ1eQ2eCK[^05^;5Q2jb3b5b6b1b7b2b8Q2tQ1VQ1WQ2hCKeO5PmPZPlPoPRPqPrPtPuPvQ0LQ0aQ0_Q15Q2kQ2lPpQ0dPjPsQ18PnPyP>Q1\PzP|Q0tPAP|Q0wPAP|Q2qP|Q2]Q1ADcFIPBPJb4b9b:X05Q11Q1a10:[S2]Q2];Oi[[^05Q0zb3b<b2b1b5b6b1b7b2b8b<bAPmPZPlPoPRPqPrPtPuPvQ0LQ0aQ0_Q15Q2kQ2lPpQ0dPjPsQ18PnPyP>Q1\PzP|Q0tPAP|Q2rQ1A'TI05PBPJb4b9b:X05Q11Q2s/2i[^05Q2pb3b<b2b1b5b6b1b7b2b8b<bAQ2t/2ieN:02P3PePHQ1QQ0<$0CS2tPdQ0EP:Q1QQ2t$0TS2sPmPZPlPoPRPqPrPtPuPvQ05Q2SPpPsPjPnPyP>Q1\PzP|Q0wPAQ1_C>PBPJb4b9b:X05Q1U10;MS2r#1[^05Q1kb3b2b1b5b6b1b7b2b8Q1Q#1ePmPZPlPoPRPqPrPtPuPvQ05Q2SPpPsPjPnPyP>Q1\PzP|Q0tPAP|Q1^Q0<#ZS2]#sS2q'7S2h/TQI05PBPJb4b9b:X05Q11Q2rQ2]'0S2e/2S[^05Q2gb3b2b1b5b6b1b7b2b8Q1QQ2s'0S2u/2SePmPZPlPoPRPqPrPtPuPvQ05Q2SPyP>Q2ZPzP|Q2\PAP|P|Q2hQ2_P|Q2`Q1^FiC>PBPJb4b9b:X05X;5Q2dQ2eQ1dQ1eQ2rCK[^05^;5Q2jb3b5b6b1b7b2b8Q2uQ1VQ1WQ1QCKeO5PmPZPlPoPRPqPrPtPuPvQ0LQ0aQ0_Q15Q2kQ2lPpQ0dPjPsQ18PnPyP>Q1\PzP|Q0tPAP|Q0wPAP|Q1_P|Q1^Q1ADcFIPBPJb4b9b:X05Q11Q1aQ1cQ1b;9i[[^05Q0zb3b<b2b1b5b6b1b7b2b8b<bAPmPZPlPoPRPqPrPtPuPvQ0LQ0aQ0_Q15Q2kQ2lPpQ0dPjPsQ18PnPyP>Q1\PzP|Q0tPAP|Q2hQ1A'TI05PBPJb4b9b:X05Q11Q2e/2i[^05Q2pb3b<b2b1b5b6b1b7b2b8b<bAQ2u/2ieN:02P3PePHQ0Q,0cS2uQ2tP=PXP:Q2uQ2sPmPZPlPoPRPqPrPtPuPvQ05Q2SPpPsPjPnPyP>Q1\PzP|Q0wPAQ0Q#s,7ER=9C|~S2tC>PBPJb4b9b:X05Q1UQ0Q,0;S2e#1[^05Q1kb3b2b1b5b6b1b7b2b8Q2u#1ePmPZPlPoPRPqPrPtPuPvQ05Q2SPpPsPjPnPyP>Q1\PzP|Q0tPAP|Q2q,7=S2q/TQI05PBPJb4b9b:X05Q11Q2eQ2]'0S2]/2S[^05Q2gb3b2b1b5b6b1b7b2b8Q2uQ2s'0S2s/2SePmPZPlPoPRPqPrPtPuPvQ05Q2SPyP>Q2ZPzP|Q2\PAP|P|Q2qQ2_P|Q2`P=FiC>PBPJb4b9b:X05X;5Q2dQ2]Q1dQ1eQ2eCK[^05^;5Q2jb3b5b6b1b7b2b8Q2sQ1VQ1WQ2uCKeO5PmPZPlPoPRPqPrPtPuPvQ0LQ0aQ0_Q15Q2kQ2lPpQ0dPjPsQ18PnPyP>Q1\PzP|Q0tPAP|Q0wPAP|Q2tP|P=Q1ADcFIPBPJb4b9b:X05Q11Q1aQ0Q,0:R=?O=i[[^05Q0zb3b<b2b1b5b6b1b7b2b8b<bAPmPZPlPoPRPqPrPtPuPvQ0LQ0aQ0_Q15Q2kQ2lPpQ0dPjPsQ18PnPyP>Q1\PzP|Q0tPAP|Q2qQ1A'TI05PBPJb4b9b:X05Q11Q2]/2i[^05Q2pb3b<b2b1b5b6b1b7b2b8b<bAQ2s/2ieN:02P3PePHQ01Q0HPcPTP:Q01Q07PmPZPlPoPRPqPrPtPuPvQ05Q2SPyP>Q1\PzP|P|Q0@20:|9S2sPAQ0@EbPBPJb4b9b:X05X@IQ0S/3;Q0\[^05^@IP<Q0]/=@R=/0[S0]/2SS2pQ0]Q1L10wOS0]P=CKS11'3P=P4O3b3b5b6b1b7b2b8Q1MePmPZPlPoPRPqPrPtPuPvQ05Q2SPyP>Q1\PzP|Q2sQ2^20:|8S1M5_|5_|S2]PAQ2^C>PBPJb4b9b:X05X@IXIIQ1Y=d;:S2qQ2f[^05^@I^IIP<Q11%1=S11P=P4O4b3b5b6b1b7b2b8Q01Q07'0S01/2SePmPZPlPoPRPqPrPtPuPvQ05Q2SPyP>Q2ZPzP|P|Q1M20:|7Q2a5_|PAQ2aEbPBPJb4b9b:X05X;5X@IXIIP:P9Q1TQ0{Q0|/2<I0ZQ2i[^05^;5^@I^IIP<Q2pQ11PwP=P4O5b3b5b6b1b7b2b8Q01Q1VQ1X40[eO5PmPZPlPoPRPqPrPtPuPvQ0LQ0aQ0_Q15Q2kQ2lPyP>Q1\PzP|P|Q0@Q2^Q2s5_|PAQ2mEbPBPJb4b9b:X05X@IQ0SQ1Y;d;Q0\?9;iS1Y[^05^@IP<Q1G/0[PxPDPxPOQ1GEnR=Q1GP?O3b3b5b6b1b7b2b8b<bAPmPZPlPoPRPqPrPtPuPvQ0LQ0aQ0_Q15Q2kQ2lPyP>Q1\PzP|Q2]PAQ2nC>PBPJb4b9b:X05X@IXIIQ2qQ2o[^05^@I^IIP<P=Q1G#1Q1GP?O4b3b5b6b1b7b2b8b<bAQ01/2ieN:02P?Q0VQ0JPfP<O1Q0I$0g3?#}PHP;Q0KP;P<O2O2Y0<WCPDP5PePcQ0[A40b`P<K0<Q1fQ1g,;;7S;A5fD:P:PfPOH1HP9PeP[PKCl9Se9Q03Ao8gV9Jg8%6eP@P8P8P@P[PeClCaP<P021F51R=P0PePKEhP<P7P7Q2bDmXL5#X'LAO77SS1fP9Ao7kV9Jk71@w[Q0eQ0c1Bx[[[PlPoPRPqPrPtPuPv1@LM%1LQ0fQ0N/BM[[PpPsPjPnQ0hQ0g#vQ0m+0FQ0iQ1:;py3pP>Q0oQ1>7:99:};PzP|P|Q0x=C|EQ0xQ1]'7RZ9V|EPAP|P|1TZQPAP|Q0yPAP|Q0?#^9V|~PAP|Q0@P|PEPQDcS0@FIS0?DjEbPBPJb4b9b:X05X;5X>5Ao<:V9J:<109VS0x/2S%<8RZAO88SS0g\Z[[[^05^;5^>5P<Q1BQ1CPXP?PNP\PhO7b3b2b1b5b6b1b7b2b8WDP<O1%6@PfP7P7PfP[P@ClCaP<P0P=P0P@PeEhP<P6P6Q2bDmXL5#X'LQ03%6fPhP6P6Q1JDmP<P0P=P0PfP@EhP<P4P4Q2bDmXL5#XQ1r?94SP<%6hPgP4P4Q0^DmQ04%6gPCPkP[PgCl9JkCAO??SS0^P<%6wPGPxP[P{Cl9JxGQ1N/@[Q1N#1Q0cQ1q/B[[[PlPoPRPqPrPtPuPvQ1B/@MS1rQ1B#1Q0fQ1l/BM[[S1JPpPsPjPnQ1<P>Q0p?:9}Q1=7::S1<9:};PzP|P|Q0<#{#^Rm=C|EQ1`Q0q60R5,7mS039V|EPAP|P|Q03/TQPAP|P|20K~mPAQ0?DjDjEbPBPJb4b9b:X05X;5X>5X?5XB5P<P8P[P;Cl9J8<Q0T=57SQ0~Q0~Q0~Q1f[[[[[^05^;5^>5^?5^B5P<Q1nQ1wQ1mQ1lQ0OP?Q0UPUQ0YPLO:b3b2b1b5b6b1b7b2b8WDWYP;P<O2n2001000000121000000W=P<O1P<P0P=P0PhPfEhP<PCPCQ2bDmXL5#XQ02P5P<P0P=P0PgPhEhP<P?P?Q2bDmXL5Q0^P<P<P0P=P0PwPkEhP<PGPGQ2bDmQ04P;P0P=P0P{PwEhQ0{,;H9J;HQ0>Q0>;OSP<P9P0P=P0PLPxEhQ10,;X9J8Xg006JRmp4p710S10Pmp4p7210S2bP;\;S0^&03:S03Q04P8P9P:P;H0L989<P8P<O1=?7:P6P<P9CkXC7,W7[S0eP9P<O1=?8;P7P<P:CkXC8,W8P7P8P9P:H0L988;Rm[P7P<O1=?69P4P<P8CkXC6,W6\mP8P9P:P;P<I1CP;n2001000000120000000XG:WKWbW[WOQ10Q2bQ0^Q03Q0e^G:]K]b][]OP<P0P5P=Q1NQ0N540P6P:O6Q1I/E4P0P<Q1CQ1N540CkXC0,W0Q02P0Q1I/ECP0P<Q1qQ1C540CkXC0Q1}?9YSP<Q00P5P1Q1I/EGP0P<Q1lQ1o540CkQ27?9NS[P<Q00P5P5Q1Z/EXP0Q1[Q1wQ0A540CkQ2A?9US[P<Q1H/EWP0Q0DQ0PQ1u540CkQ04Q1h/EYP0Q1PP0Q1zQ0PI04Q2I?9^SP<Q1R,Y1Q0O'EP0Q1iP0Q0RQ1yI04P5PNQ1p9f1<Q1{Q20540R=580Q2K?9dS]XXN5P0Q1j9f1NP0Q20Q0RI04PDQ0;Q2<Q2:Q26Q25Q1|P=Q0RP\P4P6P<N=0tP11D\DQ2<$00%<\A5\DSQ2:Q21P4Q2:10\MP4Q1sQ2:P\P6P\PDQ26PVQ1|#6P]PDQ28P[Q25DA[D\DqK0;9R\M3dCNQ041D]DQ2@$00581%<]Q0WPSQ22Q2<P]P[PCC|Q2<P]PMPCQ0=Q2<P]P4P]PDQ2=PVQ2>Q0UPDQ23Q2?CF[D\DqDe3dCaQ06?9KSP<1DUDQ2C$00581Q0ZA5_DSQ2CQ29PGQ2C10_MPGQ1vQ2CP_PFP_PDQ2@PVQ26#6PaPDQ2:P[Q2=DA[D\DqK0;9R_M3dQ04%<a10aDQ2EQ2;PHQ2E10aMPHQ0BPHPPQ2EPaPGPaPDQ2FPVQ2GQ0YPDQ2<Q2HCF[GQCrK0;9RaM7JSQ0b?9hSP<%<^10`DQ2RQ2BPXQ2R10`MPXQ0GQ2RP`PTP`PDQ2JPVQ2@#6PbPDQ2CP[Q2FDA[D\DqK0;9R`M7JSQ04A5bDSQ2MPbP[Q0EQ2MQ2DQ0EQ1xQ0E/;PQ2MPbPXPbPDQ2NPVQ2OQ0[PDQ2EQ2PCF[GQJ0WDG9RbMAO{{SP<A5cDSQ2TQ2LPYQ2TQ1SPYQ1~Q2TPdPWPdPDQ2QPVQ2J#6PKPDQ2RP[Q2NDA[D\DqK0;9RdMQ2U/@[Q2U#1Q0cQ2V/B[[[PlPoPRPqPrPtPuPvQ2W/@MQ2W#1Q0fQ2X/BM[[PpPsPjPnQ1;Q19001y+01P>Q1=?:8}RV9:}8Q0oQ1>7:87:;PzP|P|Q0C#^RbQ0s'7RP/TQPAP|P|20K~bPAP|P|AC|bEAV|EPPAQ0?EbDjDjPBPJb4b9b:X05X;5X>5X?5A59DSAo:7D9J7:%<7RPQ1f\P[[\Z[^05^;5^>5^?5P<Pxp+01PQ2YQ1mPFPTPhQ0RQ2RO9b3b2b1b5b6b1b7b2b8W`W_P;P<O2n2001000000121000000W=W^P;P<O2n2001000000121000000W=WYP;P<O2n2001000000121000000c0JWXPFP;P<K1BWXY0>P;P<O2n2001000000121000000W=Xg5Xc5P;P<O2n2001102000121103103Xf1XN5P;P<O2n2001102000121103102XC0P;P<O2n2001000000121100000b]b=Y09W]P;P<O2n2001000000121000000W=XM5P;P<O2n2001000000121100000W=P<O1n200100000021100011000W=P<O1n200100000021100011000Q0gQ0JPwQ0M00@7RTO1Q0JQ0JPxQ0M00@6O17?<Y0QP]P7P8P9P;O4PWPTO1Q0FPTP5P7Q1LQ0]'DQ0X5H100E<XN5Q1EQ1D,;77S7Q0`1@k[Rb%1kQ0c1B{[[[R`PlPoPRPqPrPtPuPvQ16Q17PyP>Q2ZPzP|P|Q2[P|Q0rQ0vDc-0e|RaPAPaC>PBPJb4b9b:X05X;5Q2c10<O79;Q12[Q0{Q0|,;:7J:Q12[[^05^;5P<PHQ1NP?O3b3b5b6b1b7b2b8Q14H0?Q1EQ1D'DQ0X5H100E7eQ0M00cTPbP`PlPoPRPqPrPtPuPvQ0LQ0aQ0_Q15Q13/@MQ13#1R`Q0fQ1N/BM[[PpQ0dPjPsQ18PnPyP>Q1\PzP|Q0@PAQ2mC>PBPJb4b9b:X05Q0S?9<SQ1Y[^05P<Q0FPHO2b3b<b2b1b5b6b1b7b2b8b<bA-0`7ExO2Exc0;WxWzWyWDXE5Q0SQ0[79<PXP;P<O2PhPKQ0TP<PfPdP0PcP0P1PeP@Q0[D[P:P<FPDGXF5#XQ02P5PgPe1M[9RXP<PhPKP0PdP0P1P@PfPcD[P9P<FPDGXF5Q0FP@1M[8RcP<PgPeP0PKP0P1PfPhPdD[P8P<FPDGXF5#XP<PwPf1M[7RdP<PkP@P0PeP0P1PhPgPKD[P7P<FPDGQ04P{Ph1M[6RKP;C|PwPfP0P@P0P1PgPkPeD[P6P;FPQ0OB07k[CReP<PxPgP0PhQ1KPCP<FPH0qXF5#XP<A`Le9PLPkP0PgQ1FP?P8FPP5P\B07x[GP<Q0NP{P0PwP0P1PLQ13PkD[PGP<FPH0qXF5P7B07{[FRG=`N7Q13PwP0PkP0P1PxPLPgD[PFP7FPP3Q0NPNPGQ0HP7P;Q0>PGQ07Q13/@[RNQ0cQ1N/B[[\`R`PlPoPRPqPrPtPuPvQ1C/@MR3Q1C#1Q0fQ1B/BM[[RMPpPsPjPnQ1:Q0mQ0h+0>+0p001yP>Q1>9:V:?:;}PzP|P|Q1?20:|6PAP|Q0wPAP|Q1@PAP|Q0:PAQ1`Q0r60R5,7ERV9C|~RFC>FIEbPBPJb4b9b:X05X;5X>5X?5X@IQ0\/38Q1a108dRd#1\P\P[[^05^;5^>5^?5^@IP<Q1B,;YQ1mQ1lPYQ1oPWP]P_P{O9b3b2b1b5b6b1b7b2b8Q07,0GR]/2S10G[RP/2SP<XC5R812;<$0oXG5XC5RgP]PPP8P8P8P5P5g01OM10;<H1A#tXe5XH5PGPG%tGQ07P[P8P8Q08&0T<#tWCQ0HP[%t[J1@N:1?RLPSPS%tSL0nPNP`PlPoPRPqPrPtPuPvP3PMPpPsPjPn21>5[RxQ0i60P5Q1:;pyR1P>Q1<?:;}R0PzP|20:|4Q0rQ0<#^Rw5V|R?5_|RePAP|Q1`>0R5w,7ERw=C|QRCPAP|Q1@PAP|Q0:PAQ1`,7VRh=C|QFIFIPBPJb4b9b:X05X;5X>5X?5XB5X@I1;;:RQ,37R@A5;XSRXQ0~Q0~10d[R[/2S[[[[^05^;5^>5^?5^B5^@IP<Q1}Q1mQ1lQ1BPYQ1oPWP\P_P{O:b3b2b1b5b6b1b7b2b8H0mQ1O,2]R{Q13?5OGRG'LQ1O,2PR\/LGP{PGP\PGP8PgP]PPPLQ1OQ1OQ1O#tL0n&0oGJ1=PNP`PlPoPRPqPrPtPuPvP3PMQ0h:0P5xRMQ0jQ0l:0P5xQ0n;py3pP>Q1=?::}Q0p9:}97:;PzP|Q1?=_|?R?PAP|P|P|PwQ0qP|Q0qQ1]'7PEFiPAP|P|Q0q-0K~PAP|Q0yPAP|P|PhQ0qQ0s'7P|Q0qQ0u'7PVFiC>DjFIPBPJb4b9b:X05X;5X>5X?5XB5Q0\?9;910;cP9Q0xP;CK%<4R4P[P6PDP6POPdEn[\Z[[^05^;5^>5^?5^B5P<Q1BQ1CQ1lQ0FQ1qQ0EQ0OQ0UPkO9b3b5b6b1b7b2b8H0mO5PNP`PlPoPRPqPrPtPuPvQ0LQ0aQ0_Q15Q1rQ1JPpQ0dPjPsQ18PnQ0nQ1:Q0mQ0k#y#v+0>+0p001y5pMP>P0PzP|P?PAP|PCPAP|Q0wPAP|Q1@PAP|Q0:PAP|PFP|PVQ1ADcC>FIFIPBPJb4b9b:X05X;5X>5X?5XB5Q0\/3QQ0}107KRK?OKi\4\4[\X[^05^;5^>5^?5^B5P<Q1tQ0AQ1nQ0KQ1mQ0OPUP_P^Q13O:b3b<b2b1b5b6b1b7b2b8b<bAPNP`PlPoPRPqPrPtPuPvQ0LQ0aQ0_Q15Q1rQ1JPpQ0dPjPsQ18PnP1P>P0PzP|PePAP|PCPAP|Q1@PAP|Q0:PAQ1A9C|hFIFIPBPJb4b9b:X05X;5X>5X?5XB5X@IQ0~Q0~12[i[[\X\@^05^;5^>5^?5^B5^@IP<Q24Q1tQ0AQ1nQ0KQ1mQ0OPUP^Q13O:b3b<b2b1b5b6b1b7b2b8b<bA12]ieN:02P<H0?H0\W~WiP;P<O2n2001000000121000000W=XF5P;P<O2n2001000000121100000baW\XJ5NQ1<bobwbhbtbsbrb}b|b{WSY0BY0DY0@WQWRWmWkWjWlWPY0CWVY08Y05Y06Y04Y07WvWUWqWWZ0P2WZZ0K5Z0L5XL5Z0N5Z0R5Y0AWeY0?o"). Qed.

Lemma dsh_app : forall (W : list (Z * Z)) A n, Forall (fun iv => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W ->
  0 <= A -> 0 <= n -> A + n <= 2 ^ 47 -> disjoint_from W (sh A) (nsh n).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpI ()) [] "p'0h06__sat4h14__x1h22FWh34__x2h47__arithh54__ffh66__sat3h78__varmaph85__with91Wh:1Hh;2Hah<6__sat5h=4__x3h>4__x4h?1Ah@2F1hA2HAhB3HanhC2HnhD2IHhE2SNhF1ahG2ivhH1lhI1nhJ2w1hK2w2i001pi011zp;2p;1p;3p;5p;4p;6p;7p;8g00\_R0j2pTg00;oj1QTg01P1j3^Tg00L0j20Tg01>Ej3oTg00a\j2ATg01PNj3@Tg00:Aj2:Tg007gj11Tg008Lj1<Tg00ffj2RTg01Poj13Tg01Qfj17Tg01R^j39Tg00;Oj1NTg00G9j3=Tg01Scj5bTg015Cj2`Tg009Jj2HTg015kj3]Tg017Tj2\Tg00?_j2KTg00GYj2CTg00<Oj1[Tg00H7j4GTg00<mj1ZTg00=Kj1YTg00I:j2BTg00J@j3XTg00>6j2>Tg00jmj1WTg0185j3VTg00Jcj1UTg00?=j2STg00@9j2TTg00@ej3nTg00A?j3mTg00A^j4lTg01TBj5jTg00KEj4OTg01UBj4eTg00C1j2ITg00Ckj3dTg00D\j1ETg00E;j2?Tg00Edj3DTg00FMj2MTg00HUj15Tg01Ucj5aTg016Oj4fTg00[Gj6gTg00]?j4hTg00NKj7PTg00OSj8kTg00b6j7_Tg00PUR1f0R2'0p=6%52#5#5#5p=8g00P7R3P3f1R4P2Chp=Ff2R5g00QZR6g00R9R7P7g00RYR8P3P4g00XJP2COg00S9R9FPp=4f3R:P6P7P7P8P5P4P2Gkp=;P4P6P7P7P8P2P9FPp=i%12#1p=J%12#1#1#1p=2%52#5p=cP5P6P7P7P8P4P2F_p=L1p33R6#QR9A^332g01VG'0g01WER;Ao332'0'AXG6R<=@65%65R=f4R>/::g00TQR?#1R@#<RA%8@RB#<RC'RRD'0P6A@6<2REf7RF#3f6RG#7594]2X99%N6RH9@6<g00eR%3Gf5RI#759HeW2P0P3P3f9R0#3f8#7594^2EA=6549@6<A=6:5f:RH#3%7039]2[^H9P2f<RJ#3f;RK#7594^2E1F:5==649@6<P6P<1F>:REP5P2DbP<PEO1f>RL#3RMf=RN#7RO':RP/0I10>M'AA9:MOPLPNPKPH1`ACRK1H1ARO%6C1H1D[RM[RQ%6ARRg00e6RSA]AC4UW;RC%6D\S^;RRRP4g01Ng1\1A'KPOeROO1RSPMg00U6RT#NRU%QTRVP31C35P4%[3RWCGRX%Z3RY%Y3RZ1B3?R[1B3@R\5X3R]1>3A%WB5V354ZRB%U7R7PBC;1SZ8R8P2P5g00UbRBg00VBRA'K1T25=nBAdAm314ClRAb5b7b8X13X331:24/0D1:45RB/0D[^13^33P2fAfBRDPNO3b4b0b6b01:LNg01X@'0eDj10P;f?RP%1@R@#1R;#<RLPKPQPCPRPSPMPUPV1C34PYPZ1>31R^=4Z[R_P7P_C;P8PAb5b7b8X13%62%64R_[^13P2fCR`f@RaO2b4b0b6b0PKPQPCPRPSPMPUPVPWPYP3P^g00Y11>3LCO,iZP8PAb5b7b81H1LP2b4b0b6b0Ce1IPL#6PKPQPCPRAdDLP%6L1I`L#6[P5POO1PMPUPVPXPYPZA4Z^\P7A4Z[]C;P8PAb5b7b8X13X33104B\_^13^33P2fE/ILg01Y<RLPIO3b4b<b6b0b<b:%3P,0LRLePLPKPQPCPRg00W?RR#ERC#ERQ#ERK,?31?3QRQ1?3C5D35D3g00W^RC'M%EK,?31?3R9D3Q5D3/MC==TU5=TPVP3P31C3>P5PWCGP41C3:CGPYPZ%5?R?#5#8#8#8RY#5#1#J#2#2#2#<RW,>3=4Z[P7PZ%J;#2#2#8#8#8#8#1#J#2#2#2#<R;,>3RV94Z]P7PZ1B3@R@%1Y#5#c#2#2#2#<RY,>354Z1B3?R?94ZV5LZP7A4Z]?A4Z@[5LZC;C;C;P8PAb5b7b8X13X33X=3X>310W210B;10IY10;>'A1::>/0I10G:'A[[[^13^33^=3^>3P2P0PH%7D%3`P:P>PIO7b4b6b0%3aRa%7P':/0F10Ga'Aeb:bEP5P6P<1FI>P:P4DaO1Cfb@A=6E5%3N%7J39eW2WDX99XK3XJ3P4P2O2n2001100000121101101XF6PGP:EgWBXC=WAW2XI3X?3W9o"). Qed.

Lemma cells4_split : forall m A c1 c2 c3 c4, rw_cells asegs m A [C8 c1; C8 c2; C4 c3; C4 c4] ->
  rw_cells asegs m A [C8 c1] /\ rw_cells asegs m (A + 8) [C8 c2] /\ rw_cells asegs m (A + 16) [C4 c3] /\ rw_cells asegs m (A + 20) [C4 c4].
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpI ()) [] "h02Hch14__x1h21mh31Ah41Hh57__arithh64__ffh78__varmaph85__with91xh:3cs1h;3cs2h<4segsh=2H1h>2H2h?2H3h@2H4hA2c1hB2c2hC2c3hD2c4hE1nhF1yp;1p;4p;2p;5p;3p;6p;Bp;<p;7g007gj1;Tg00jmj1VTg00kKj1PTg00knj1[Tg00;Oj1UTg00;oj1ITg01Z:j44Tg009fR0j2>Tg01[8j5lTg008Lj1CTg00:AR1j20Tg00HUj1aTg00D\j18Tg01\;j2QTg01\RR2j1?Tg00@ej1^j3STg01@Ij1]Tg01@gj4\Tg00?_j2GTg00GYj2ZTg00<mj1YTg00=Kj1XTg00I:j2WTg00>6j2ATg00?=j2kTg00@9j2jTg00A?j3iTg00A^j4gTg01B\j4MTg01]2j6ETg016Oj4LTg01^5j1dTg00G9j3RTg01_2j1cTg004fj3bTg01_oj1KTg01JPlBTTg01Ikl<eTg01K6l<fTg00J@j3`Tg00KEj4_Tg00NKj7hTg01a0R3f1R4#df0R53Rp=2%c4=R35p=1g01amR6f2R7P4P5C4p=7Ab345p=5%K5#?,04p=9P6f3R8%K4#?,07P5C4p=<P6P8P7P4C4/>5p=3P6P81074P5C4p=@%K5#?p=Bg00P7R9?S45p=61G95p=:g01bdR:P:P:P9P9P9g01cCP2P2P2P1g01ccP8P7P4g00W?R;g00PUR<P5MBTp=OP:P9P9P9P2P2f5R2f4R=P8P7P4P5M<ep=NP9P9P9P9P9P9P1P5P4P7P1P8P=P2f6R1f7R>f8R?f9R@MBTp=FP9P9P5P4P7P8P=P2P1P>P?P@M<fp=JA`945p==P9P4g00Q3P5C_p=HP4g00QZg00R9RAPAg00RYRAP5g00S9Fhp=Dg00TQRB#;RC#;RD#;RE#;RF#;#;#V#PRG%VE#P#[[RH%U3RI,25,24,17,18972=g01dF#IRJ%I3R3P0P=P8P71545C4P2P=P8P7C4P2P=1987P4C4'>[RKP=P8P7P4C4P=P81974P5C4'>P2P=P81574C4RL[P1P2P=P8C4P1P219=8P7C4'>\LP=P8P7P4P5DlP4n2001000000120000000X;3W:X39X2HW<RLPK^;3^:3^39^2H^<JRJP5P6P>P1112IRH11=I128IR8127I'5'5R3P4O6P>P1PHP>P1PHP3C<C3P0111IR397?>P?P>P312=IR=/58,5HC<P@P?11>IP@%CERE,0?P3P@%CFRF,0?122IP@P?%aC#;#;#CRCP=C@C3C3C3P5f:R=11?IR277@f;R3P=11@I12>I121I'5,52C<PLPJP5P6f=R2f<R1113IRH#BR8'0RK11=IRM12@IR@12?I'5R?P4O6P2PKPMP2PKPMP?C<C3P0f>R?111IRM,92RK;7HP?PKP812=IR=/5@C@f?R@P?112IR8P@10?EPMP@10?F123IP@P?PCP=C@C3C3C3P5f@R=P@11?I#BR3P8C@fAR811@I,9=P3122I121I'5C@PLPJP5P6fCR6fBRJ118I#BRL'011=I'9R112@IR@12?IR?P4O6P6P1P@P6P1P@P?C<C3P0fDR011JIR?,96/0LRL12=IR=37P0PLP=P@C<fER@P0116IRLP@100EP?P@100F128IP@P0PCP=C@C3C3C3P5fFR=110I#BR8,0@PL12JIRJC<fGRL11@IR@,9=/08126IR6PJC<fHRJ11=I77LR=10LER8=7J@R?10LFR1120IR057JRI10LCR3=7J6RM'>RK'>RHP2P?PKPJ%8;#8#8#8RK#8#8#8#8R?/Q;R2#?RN,0LROP8P@P>16O810E<R>,0LR@/68%^9RPP5X99RQPP1645#]XF9X99RRPOP@PQPQPQP9P9g01OM1045C\#:X29XE9RSPLPL%:LPNP>PQPQ%?5#:X9:R:P2P>P?PE%:E1G9<R?COENR2M:FRLP8P8%:8M:Jg00U6R8#URT%I8R81Z94RU%Y9RV%X9RW1W9BRB1A9ERX1A9<RY'=RZ'=R[1=BX'H'D1kWARAP5P7g00UbRXg00VBR\'G1j57=SX\dAi9<4CgR\b6b7b8X19105>RX105E'6^19P5PJO1REb5CMEEPIPMPJ10ONRMP1P0P416M110@>R0/61PPPQPPPRPMP0PQPQPQPSPOP@PLPNP>P2M:FR2P1P1%:1M:JPTP8PUPV1=[ZR[1A9F,=B'H,DWPAP\b6b7b8X1910X>RX105F'6^19PEb5CMEEPJ1QK;R;#?RJ,0MRFP3P6P516F3%CDRD/0<R<,00R6/63PPPQPPPRPFP6PQPQPQPSPMP0P2PJP<PQPQP:P;P<PKPD%:DP?COENM:FP3P3%:3M:JPTP8PUPV1A9D/=Y,=[1A9C,=B'H,DWPAP\b6b7b8X1910X<105C'6^19PEb5CMEECLCLCL1>=HeW@W?P4P5O2n2001000000121000000b0b4W0W>P4P5O2n2001000000121000000b0b4W0W=P4P5O2n2001000000121000000b0b4W0XDGXCGXBGXAGX39W2o"). Qed.

Lemma grows_of_munch_cell : forall m m' a v, munch [(a, a + 8)] m m' -> rw_cells asegs m' a [C8 v] -> AIMG_TOP <= a ->
  a + 8 <= 2 ^ 64 -> mem_grows m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpI ()) [] "p'0h04__x1h14__x2h27__sat10h31Dh47__arithh54__ffh64__p1h76__sat9h88__varmaph95__with:1xh;2Hah<1Lh=1Uh>1si001sh?1Hh@3Ha8hA2HchB2HxhC2MUhD2XrhE1ahF1bhG1mhH2m'hI1ohJ1vhK1yhL1zi011li021np;1p;2p;3p;4p;6p;5p;<p;7p;8p;Bg007gj1;Tg00jmj1TTg00kKj1NTg00knj1\Tg00\_j2~Tg008Lj1HTg00:AR0j22Tg00;Oj1ITg00G9j3<Tg00mmj3[Tg01_2j1LTg01Z:j4VTg00L0j29Tg00ffj2}Tg00Jcj1STg01eEj1qTg016jj21Tg009JR1j20Tg009fj26Tg01fIj2OTg00dCj13Tg01fmR2j2RTg015Cj2bTg015kj3`Tg017Tj2_Tg00?_j28Tg00;oj1^Tg00GYj2]Tg00<Oj1ZTg00H7j4YTg00<mj1XTg00=Kj1WTg00I:j2KTg00KEj4?Tg01IGj6UTg00?=j2|Tg00@9j2{Tg00@ej3@Tg00A?j3xTg00A^j4wTg016Oj4MTg014Dj2QTg001@j6FTg01gMj5rTg01_oj1pTg01\RR3j1GTg01hYj3oTg01iRj2=Tg00D\j15Tg01\;j2nTg01ioj3mTg01@Ij1lTg01K6l<iTg01jUj6jTg00>6j2PTg00J@j3ATg01k>j3gTg01B\j4fTg00lPj2BTg01kaj1eTg000dj6dTg00h@j2sTg00]?j4tTg00NKj7cTg00Noj7uTg00>Yj6vTg00OSj8aTg01JPlByTg01Ikl<zTg00P7R4P4f1R5f0R6Ctp=Ef2R7?@56#3p=4g00PUR8/96p=:P4P5g00Y1P6C?p=>P5g00QZR9g00R9R:P:g00RYR;P6g00S9Fcp=7P7P9P:P:P;P5P6Fup=JP5P9P:P:P;P6Evp=Df3R<P9P:P:P;P7P5P6Gap=Cg01bdR=P=P=P4P4P4g01cCP3P3P3P0g01ccP<P7P5g00W?R0P8P6MByp=kP=P4P4P4P3P3f5R3f4R>P<P7P5P6M<zp=hg00TQR?#;R@#;#;RA#;#;#;RB#TRC#NRD%TA#NRE#\RF[RG1~44RH%HARA,25RI,E5%IHRJ3<?[<7g01amP<P7g01a0RK%L5%IKRL3<CVg01ll/9<12>A%H@RM%HBRB'}RN'9f8ROP6O1%SERE54F%q511C5RP#:10PN'611C7RP/OO10PORP%3P'RP211C<f9RP'0RQ%3Qf;RQP>O1=4FEP611C>f:RR'0RSPFf=RTP3O1A4F6EXIFRUP>f<RVP3O1PPP311C3R3,9Q12QARW,03RX'6#3g00e6RY1bMBRZ108MR[%:B108N[R\[R]%:MR^A`MB5VYW;RB%:N\Y^;^R^P5g01Ng1_8M'8P[eO1R[P\p-0RMg00U6RN#IR_%^NRNP41]47P5%Z4CYR`%X4Ra%W4Rb1K4@R@1K4?R?'>,7b%S:RcP4P?g00XJRdP@C?,7bPbP9P:P:P;P>EUR:5Jb,DbCC1|b;R;P6P7g00UbR9g00VBRe'81{67=@9edAx485CwReb5b8b9X04X14W61056R91957/6<g00VbRf[[^04^14^6MP611CPRPf?Rg/2A'0PPPgP>O4b4b2b7b2g00eRRhCM1EQW=<HJ/Q3eO2EFW<P6O1%3S1O3W%3X,RXP2f6R2,1C12VA'0RX%3Xf>RXf7RWO1=4FEP611CW12TA'0R3PgPX%LT=<KLRLPQPRDr%pL#G9ogXP61=PgRP%:PRL%50#5#5#5#5#5#5#5RK/n0R0#GRT,0PRS'612A8Ri,0PRj,6LPLPSPLPj18ML9mLLP4P4P1P6X:4RLP1%l9XK4X:4PPPP184PPTPiPLPL%G6,84X:=P0PiPKPA184A1848CkEhM<iEjPZP]PBP^P_PNP`PaPb1P4ARK9A4@,>?,7bPcPb1>?@,7b,DbPcP41P48R8PdAg4?@RdC?,7bAA4K8,>d,7b5JbCCCCP;Peb5b8b9X04X14106I1057Pf[1=7<R8#:108i'6[[^04^14P6fBR811CVRiP>PWO4b4b7b2CfO2f@R>12gP,BCO1=4FEPZP]PBP^P[P\P_PNP`PaP4P?g00Q3AA4@dC?,7bP;Peb5b8b9X04X141=65,259@46^04^14P6fDRd11CXO2b4b2b7b211CRRR1=R>,2>5@4P4fARR11CQRQ/=R'2fCR\1BC6O1=4FEXL4P5PQP6EFP81BCQO1=4FEPD1BCiPdP6O1=4FEXFDP6PV%eVEdP\PVO1=4FEP6b3b3b?b3b3W=P6O1%33PFP>POO1PUPWPgPOO1PVPO11CORO,9X12XARC,0O'6#3PYPZP]PBP^P_PNP`PaPbAA4?K,>@,7bR@,DbPcAJb:@,DbCCP;Peb5b8b9X04X14X6M126A,05Pf[107I,6<Pf[[^04^14^6MP619RQPQPRP<O4b4b7b2PhCM1EXC=<HJ/QOeO2EFW=P6O1n200110000021110111102b>W<P6O1n200110000021110111102b>bDWBX:D1sW2eW@W;WAWCXJDXE4XHGWGo"). Qed.

Definition srI : list expr :=
  srs sr_id [(8%bv, EVar 32); (10%bv, EVar 33); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 24)); (19%bv, ELit SHBASE);
             (20%bv, EVar 35); (21%bv, EAlu ALU_SRL (EVar 32) (ELit 3)); (22%bv, EVar 34); (24%bv, EVar 36);
             (25%bv, shEe (EVar 33)); (26%bv, shEe (EAlu ALU_ADD (EVar 32) (ELit 24)))].
Definition KNP0 : list kentry :=
  [KWr (SA (EVar 33) 0) (ELit 8); KWr (SA (EVar 38) 0) (ELit 8);
   KRange (EVar 32) 0x6e8000 (2 ^ 47 - 40); KRange (EVar 33) 0x6e8000 (2 ^ 47 - 24); KRange (EVar 38) 0x6e8000 (2 ^ 47 - 8)].
Definition SCR_PN := SCR [false; false; false; false; false; false] [EVar 37; EVar 38; EVar 39] [].

Lemma ck_srl : forall M E e a k, edenot E e = Z_to_bv 64 a -> 0 <= k < 64 -> 0 <= a < 2 ^ k ->
  sc_denot ASEGS M E (SCBr false BC_NE (EAlu ALU_SRL e (ELit k)) (ELit 0)).
Proof.
  intros M E e a k He Hk Ha. cbn [sc_denot]. cbn [edenot]. rewrite He.
  assert (Ha64 : 0 <= a < 2 ^ 64) by (split; [lia|]; eapply Z.lt_le_trans; [apply (proj2 Ha)|]; apply Z.pow_le_mono_r; lia).
  rewrite w_srl by lia. rewrite (Z.div_small a (2 ^ k)) by lia. reflexivity.
Qed.

Lemma ck_nulleq : forall M E e1 e2 a b, edenot E e2 = Z_to_bv 64 a -> edenot E e1 = Z_to_bv 64 b ->
  0 < a < 2 ^ 64 -> 0 < b < 2 ^ 64 ->
  sc_denot ASEGS M E (SCBr false BC_EQ (EAlu ALU_SLTU (ELit 0) e2) (EAlu ALU_SLTU e1 (ELit 1))).
Proof.
  intros M E e1 e2 a b H2 H1 Ha Hb. cbn [sc_denot]. cbn [edenot]. rewrite H1, H2.
  rewrite !w_sltu by lia.
  replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite br_eq by lia. reflexivity.
Qed.

Lemma ck_notlt : forall M E e1 e2 p k, edenot E e1 = Z_to_bv 64 (2 ^ 64 - 1 - p) -> edenot E e2 = Z_to_bv 64 k ->
  0 <= p -> 0 <= k -> p + k < 2 ^ 64 ->
  sc_denot ASEGS M E (SCBr false BC_LTU e1 e2).
Proof.
  intros M E e1 e2 p k H1 H2 Hp Hk Hpk. cbn [sc_denot]. rewrite H1, H2. rewrite br_ltu by lia.
  destruct (Z.ltb_spec (2 ^ 64 - 1 - p) k); [lia | reflexivity].
Qed.

Ltac sckI :=
  first [ sck
        | eapply ck_srl; [sck_ev | lia | lia]
        | eapply ck_nulleq; [sck_ev | sck_ev | lia | lia]
        | eapply ck_notlt; [evs; rewrite w_notexpr by lia; reflexivity | sck_ev | lia | lia | lia] ].

Lemma lasta_snocI : forall (l : list (Z * (Z * Z))) x t, LbB_HEmpK.lasta t (l ++ [x]) = fst x.
Proof.
  intros l x t. unfold LbB_HEmpK.lasta. destruct l as [|e l']; cbn [app]; [reflexivity|].
  rewrite app_comm_cons, last_last. reflexivity.
Qed.

Lemma lasta_cases : forall (l1 l2 : list (Z * (Z * Z))) t,
  l1 = [] /\ LbB_HEmpK.lasta t l1 = t \/ exists k v, In (LbB_HEmpK.lasta t l1, (k, v)) (l1 ++ l2).
Proof.
  intros l1 l2 t. destruct l1 as [|e l1']; [left; split; reflexivity | right].
  unfold LbB_HEmpK.lasta. destruct (last (e :: l1') (0, (0, 0))) as [q [k v]] eqn:EL. exists k, v. cbn [fst].
  apply in_or_app; left. rewrite <- EL. apply last_in_ne. discriminate.
Qed.

Lemma djI : forall (W : list (Z * Z)) a n, Forall (fun iv => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof.
  intros W a n HW. induction HW as [|[lo hi] W' Hiv HW' IH]; cbn [disjoint_from]; [exact I|].
  cbn [fst snd] in Hiv. split; [exact Hiv | exact IH].
Qed.

Lemma outI : forall (W : list (Z * Z)) x, Forall (fun iv => x < fst iv \/ snd iv <= x) W -> outside W x.
Proof.
  intros W x HW. induction HW as [|[lo hi] W' Hiv HW' IH]; cbn [outside]; [exact I|].
  cbn [fst snd] in Hiv. split; [lia | exact IH].
Qed.

Lemma in_fst_ins : forall (A B : list (Z * (Z * Z))) x y q, In q (map fst (A ++ x :: B)) -> In q (map fst ((A ++ [x]) ++ y :: B)).
Proof.
  intros A B x y q Hq. rewrite <- app_assoc. cbn [app]. rewrite map_app in *. cbn [map] in *.
  apply in_app_or in Hq. apply in_or_app.
  destruct Hq as [Hq | [Hq | Hq]]; [left; exact Hq | right; left; exact Hq | right; right; right; exact Hq].
Qed.

Lemma hdkey_snoc : forall (l1 l2 : list (Z * (Z * Z))) x y, hdkey ((l1 ++ [x]) ++ y :: l2) = hdkey (l1 ++ x :: l2).
Proof. intros l1 l2 x y. destruct l1; reflexivity. Qed.

Section EmpI.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spz : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc key : Z) (ents : list (Z * (Z * Z))).
  Variables (lo B shi : Z) (m0 : mem) (mo0 : Model).

  Definition QI : config -> Prop := QF H ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0.

  Lemma blk_win : forall s LBx m q A N a1 a2, as_RHEAP H s LBx m -> In (q, A, N) LBx -> A <= a1 -> a2 <= A + N ->
    aclient_write_ok H LBx (a1, a2) /\ afs_write_ok H LF (a1, a2) /\ aconst_ok (a1, a2) /\ stack0_ok (a1, a2)
    /\ (a2 <= ALOWSH_LO \/ AHI_LO <= a1).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpI ()) ["EmpI"] "h04__x1h14__x2h24__x3h32H0h47__arithh54__ffh67__sat17h78__varmaph85__with94__x4h:4__p1h;4__x5h<4__x6h=4__p2h>1bh?1Ah@2B0hA3B16hB2BAhC2BChD2BFhE2BIhF2BnhG2H1hH2H2hI2INhJ3LBxhK1NhL2RHhM2a1hN2a2hO1fhP1mhQ1qhR1sp%0p&0p;1p;4p;2p;3p;9p;8p;7p;6g01mfk10FTg00;oj1pTg01n_k404Tg00\_j2jTg00bZj3[Tg00L0j20Tg01o[l9|Tg020Zj13Tg021Vj14Tg022Rj4sTg009Jj2YTg007gj1ITg008Lj1XTg008jj2WTg00:Aj21Tg023Rk107Tg024Lk103Tg025Fj39Tg026?j4FTg027Cj3JTg028Cj1DTg029@j2HTg00a\j25Tg009fR0j27Tg01>Ej3rTg01P1j3qTg02:>k20ETg01:Qj2hTg01Poj1\Tg01Qfk10DTg00:^k20CTg00;Ok10BTg00<Ok10?Tg00<mk10>Tg00=Kk10=Tg00HUj1>Tg00I:j2NTg00J@j3VTg00Jck10<Tg00?=k20;Tg00?_k20:Tg00@9k209Tg00@ej3nTg00A?k306Tg00A^k405Tg016Oj4QTg01;lk402Tg00cij3mTg00d\j3lTg02;?k100Tg02<:j1~Tg02=6j1}Tg01iRj2`Tg00D\j1TTg00E;j2STg00FMj2_Tg00G9j3^Tg00>6j2RTg01k>j3{Tg00KEj4aTg02=mj8yTg02>nj8xTg00]?j4fTg00GYj2wTg00H7j4vTg00NKj7oTg00Noj7uTg00OSj8gTg00Edk30@Tg00b6j7tTg01IGk60ATf3R1g00P7R2g001^R3P2f2R4f1R5Cff0R6Cfp=21156,04p=;%I6#Ip=8g00PUR79n26p=Z1076p=@g01ll/06p==f6R8f5R9'1f4R:'01`45,01'5/76p=:1756,74,71,7:p=AP2P2P5P6Cfp=Bg01VGS00,06p=Gg01WER;/06p=K1045/76p=<1756,74p=E1145/06p=i1`56,04p=]1045/56p=L1w26p=PP2P4P5P6Cvp=CP4g00QZR<g00R9R=P=g00RYR>P2P5g00XJP6Cag00S9R?Fop=6P4P<P=P=P>P5P6Fup=dP8P<P=P=P>P9P:P1P<P=P=P>P4P5P6GgGgp=O1545/76p>01%>6#Ip=?B0@256p=MP4P<P=P=P>P5P6Ftp=UP5P<P=P=P>P6P?Fop=k1056,54p=cP5P<P=P=P>P6J0Ap=eP1P<P=P=P>P4P5P6Ggp=b1556,74p=z1056,74p>08p,1HR<$0Fg002VR?#pg02@1P<f7R@P8P9H041j32RA/j2PAP9P:P1C2;[@1091A;189p,5HCEILRBP<p,2HHf;RCf:RDf9REPAf8RFP@P8C2RGP1P4M9|PBP<%3G%4GCsP0PAPEPFP@C2RG#3RH,Y7g00TQRI#IRJ#IRK#8#XRL,WH#Z%4GRG#@%=H11HGRM&07BRN'0PMPL&03<RMg02@hRO,1MRPPHPLA9BHGF:DAPBP<f<RG1B@8RHCFp,2LFRQ=J<H%DH1HBH%G8%K@'5DAP6PAPCPDPEC2#3,Y7PAPGPCPDC2RH#3RR/WL#Z%4HRH#@%=R11RHRS/0NPSPLPMPPPRPLA9BRHF:DAP0PAf=RHPGPCC2RG#3RR/WL#Z%4GRG#@%=R11RGRSPSPLPMPPPRPLA9BRGF:7<N3EPBP<f@RG1BCDRRCFAJ<QR%DR1HBR%GD%KC'5DAP6PAf?RDf>RRPHC2#3/WL#ZPAPGPDPRC2RH#4RS#@%3HRH#=11HSRTPTPLPMPPPHPLA9BHSF:7<N3EP0PAfARHPGPDC2RG#4RS#@%3GRG#=11GSRT/0NPTPLPMPPPGPLA9BGSF:3EPBP<fDRG1BDRRSCFAJ<QS%DS1HBS%GR%KD'5DAP6PAfCRDfBRRPHC2#4#@PAPGPDPRC2RH#3RS#=%4HRH,1SRT/0NPTPLPMPPPSPLA9BSHF:3EP0PAfERHPGPDC2RG#3RS#=%4GRG,1SRTPTPLPMPPPSPLA9BSGF:7<NPBP<fHRG1BDRRSCFAJ<QS%DS1HBS%GR%KD'5DAP6PAfGRDfFRRPHC2#3#=PAPGPDPRC2RH#3RS%4HRH'1RTPTPLPMPPPSPLA9BSHF:7<NP0PAfIRHPGPDC2RG#3RS%4GRG'1RT/0NPTPLPMPPPSPLA9BSGF:PBP<fLRG1BDRRSCFAJ<QS%DS1HBS%GR%KD'5DAP6PAfKRRfJRSPHC2RH#3%4H;iNPAPGPRPSC2RH#3RT%4HRH'1PLPMPPPTPLA9BTHF:P0PAfMR0PGPRC2RH#3RT%4HRH'1/1LA]PTL7LMA9BTHPBP<fPRH1BRSRTCFAJ<QT%DT1HBT%GS%KR'5DAP6PAfORSfNRTP0C2RU#3RV%4U'1/1LA]PVL7LMPAPHPSPTC2RV#3%4V59BPBP<fSRV1BT0RUCFAJ<QUR<%DURW1HBURX%G0%KT'5RY'7RZ'7R['7Ar22UR\,0NAq22URU-0E\R]fT9[?6R^%36R_1BSTR`9r22Ra'0Aq22`R`%46Rb7;_3EX>?Rc,h?Rd%\_R_/0a&0Db9;`_5E^X>?,h?10UP9<M\%\M%\P,0U7<\%\N10U;7<\'5'5'5R^'5R_'5P?PcPAfQRAPHPSC2RcA[?cV%3cRV%4c9;UV7<\RVPR20CHLRc%@H%@LfRR?/WL#@[[Rbg00U6Re$0BRf%peRg%P:Rh&0?2Ri7C4%P1Rj7C5&0>2Rk&0=2Rl%>IRm,N2Rn1N2IRo1N2KRK5V256lRp&0<=R=Pl1N2JRq96loRrP=AdlrpFO20;l>R>P6P4g00UbRpg00VBRs+0:20964=npsdB06275H05Rsb5b7b8X02X12X22X92A;4611054RpA;:499<41[[^02^12^22^92P6PAPSPHP?PRPGO6b4b6PVeCQH029md^9l]_3lP<P[10UM10P\g02AdR[g02BdR</0\5LU401RUg02CdR\A[\6Q&006RQ/0a%~6#}9;`Q3EXO\'h10PT9L0MRP%?I#>#?#8#?#>#>#8#8#?#>#?#8#XR\%>JRJ#?#8#X'`RQ%ImRm#I#8#XR`,1\Ra/0T5L0PcPbg00W?R_#TR]#TR^#TRd#T#T,S2RV1S2^1S2_R_'M'Mg00W^R^'_1S2dRd1S2]R]'M,MV/_^=^ef5^eRVPg%P89Ch4%P9?C1i7C5RhPkPl1N2JRJ1N2m5V2Rm1R2LRt5V2=6lqAV2qnRuA{2Jt56l5UlP=PlP21R27Rtg00Y1RvPJCa,klRwP=PlA6lomRxP=PlA6lJKRyP=A6luK9UlrFOFOP>Psb5b7b8X02X12X22X92X;2X<211:9Rz/1L1154R{?]:L7L51Y79RLA;48@R|10@8R}10:9R~1198;c@[[[[^02^12^22^92^;2^<2P6PAP?PHPOPMPSP1PDPRPGO:b4b6PcPbp-0RM1M]_,Md/_^=^efPg%P5%P4Re7C4PkPl%?I#>#>#?#?#8#8#8#8#8#8#8#XRI,R2=6lnP=PlP2PtPvPnCa,klP=PlA6lnqP=1el:1R2\1R2`5V2=6lq5UlCbFOP>Psb5b7b8X02X12W:10I51Y741014Ac9a1[[[^02^12^:MP610SQP?PHPCPDPGO6b4b6CQ100[10<T5zPePUe3mPWPZPBPHPSPTP0P6PcPbPfPgACe5iPkPlPrP=PrCbP>Psb5b7b8X02X121065Pp[^02^12P6PHP?PGO3b4b610HTeRpPcPbPfPgACe5jPkPlA6louRuP=PuCbP>Psb5b7b8X02X12X22106{A;541[^02^12^22P6PAP?PSPRO4b4b6A;0HSeR1GyPXPYPBPHPSPTP0P6PpP1GxPcPbPVPgPhPkPl1elFA6lmq5dlA6lnJ1elE5dl5UlP=PlPwP=PlPxP=PlPyP=A6lnK9UlrFOFOP>Psb5b7b8X02X12X22X92X;2X<2X:MX=MB088z5A<4:@'5Ac~8@\}\|\L[^02^12^22^92^;2^<2^:M^=MP6Ai?AN%=?PAP?PHP;Q00PSP4PDPRPGO<b4b6CQCQCQCQWBWDP5P6O2n2001000000121000000W3WCP5P6O2n2001000000121000000W3WEP5P6O2n2001000000121000000W3WFP5P6O2n2001000000121000000W3WAP5P6O2n2001000000121000000W3W@P5P6O2n2001000000121000000b3WHWGWIWLXN2XM2XK2X?2XQ3WPWJWRo"). Qed.

  Definition IPRE (s : as_St H) (mo : Model) (m : mem) (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z)
      (ents2 : list (Z * (Z * Z))) (rehashed : bool) : Prop :=
    as_MPRES H mo0 mo
    /\ FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz m /\ spz mod 16 = 0 /\ 2 ^ 45 <= spf spz /\ spz <= 2 ^ 47
    /\ bv_unsigned ra mod 2 = 0
    /\ mem_inv asegs m /\ stk asegs m lo spz /\ rw_cells asegs m (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m B
    /\ tp = Z_to_bv 64 ATP /\ aceil <= spf spz
    /\ map_live_frame LF obj

    /\ umapx MI_A 24 (nval24 ASEGS) (lbl LB') m obj bl2 bc2 ents2 /\ umap_sh m 24 (bl2, bc2, ents2)
    /\ Permutation ents2 ents /\ bc2 <> 0 /\ Zlength ents + 1 <= bc2 /\ 0 <= key < 2 ^ 32
    /\ addressable m obj 40 /\ wr_at asegs m obj 40

    /\ 0 < p /\ p + 24 <= 2 ^ 47 /\ p mod 16 = 0 /\ apart p 24 obj 40
    /\ (forall q n, In (q, n) (umap_blocks 24 bl2 bc2 ents2) -> apart p 24 q n)
    /\ rw_cells asegs m p [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0)] /\ addressable m p 24
    /\ (rehashed = false -> bl2 = bl /\ bc2 = bc) /\ (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc2 = bseq_next bc)
    /\ as_RHEAP H s LB' m /\ Permutation LB' (LB0 ++ LBm')
    /\ Permutation (lbl LBm') ((p, 24) :: umap_blocks 24 bl2 bc2 ents2)
    /\ lb_own LBm' m
    /\ xpres H LB0 spz [(obj, obj + 40)] m0 m
    /\ as_RFS H LF m /\ ACONST m /\ stack0 m lo shi
    /\ as_AL H s >= as_AL H sk0 - (if rehashed then ICM (8 * bc2) else 0).

  Definition ISTATE (msF : machine_state) (s : as_St H) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 : word) (p bc2 : Z) : Prop :=
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 (spf spz)) gp tp y5 y6 y7 (Z_to_bv 64 obj) y9 (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) (Z_to_bv 64 bc2) (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key)
                             y23 (Z_to_bv 64 (hmod key bc2)) (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11
                             y28 y29 y30 y31)
                        F (Z_to_bv 64 E_INS) fc None m (seg_rom asegs).

  Lemma ins_post : forall (s : as_St H) (msF : machine_state) (mo : Model) (m M2 : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (l1 l2 : list (Z * (Z * Z))) (rehashed : bool) (W : list (Z * Z)),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 (spf spz)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 (obj + 24)) y19 y20 y21 y22 y23 y24 y25 (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_END) fc None M2 (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPRE s mo m errv' LB' LBm' p bl2 bc2 (l1 ++ l2) rehashed ->
    munch W m M2 -> wmono asegs m M2 -> mem_grows m M2 -> mem_inv asegs M2 -> stk asegs M2 lo spz ->
    Forall (fun iv => iv = (p, p + 8) \/ iv = (LbB_HEmpK.lasta (obj + 16) l1, LbB_HEmpK.lasta (obj + 16) l1 + 8)
                      \/ (bl2 <= fst iv /\ snd iv <= bl2 + 8 * bc2)) W ->
    rw_cells asegs M2 p [C8 (Z_to_bv 64 (hdaddr l2))] -> rw_cells asegs M2 (LbB_HEmpK.lasta (obj + 16) l1) [C8 (Z_to_bv 64 p)] ->
    (forall i, 0 <= i < bc2 -> exists b', cell8 ASEGS M2 (bl2 + 8 * i) b' /\ bucket_ok obj bc2 (l1 ++ (p, (key, 0)) :: l2) i b') ->
    as_SR H QI (mkCfg msF mo).
  Proof.
    intros s msF mo m M2 F fc y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31
      errv' LB' LBm' p bl2 bc2 l1 l2 rehashed W VIS FRZ KR IP MU2 WM2 MG2 MI2 ST2 FW Cn2 Cs2 CB2.
    destruct IP as (MP & FR & SP16 & SPL & SPH & RAE & MI & ST & ERR & RA & TPV & ACL & LFO & U2 & SH2 & PERM2 & BC2 & LOAD & KR32
                    & AD & WR & P0 & P1 & P16 & PO & PA & NC & ADP & CR3 & CR4 & RH & PE & PM & OWN & XP & RF & AC & S0 & AL).
    pose proof (obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3).
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (u_obj_lo U2) as Ho0. pose proof (u_obj_hi U2) as Ho1. pose proof (u_obj_al U2) as Hoal.
    pose proof (u_bl_lo U2 BC2) as Hbl0. pose proof (u_bl_hi U2) as Hbl1. pose proof (u_bl_obj U2 BC2) as Hblo.
    pose proof (LbB_HFind.BSEQ_boundA bc2 (u_bseq U2)) as BCR.
    destruct (u_hdr U2) as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    destruct SH2 as [SHb SHn]. unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn. cbn [Datatypes.fst Datatypes.snd] in SHb, SHn.
    assert (ZL : Zlength (l1 ++ l2) = Zlength ents) by (unfold Zlength; rewrite (Permutation_length PERM2); reflexivity).
    assert (ZL0 : 0 <= Zlength ents) by (unfold Zlength; lia).
    pose proof (cells4_split _ _ _ _ _ _ NC) as (NC0 & N8 & N16 & N20).
    pose proof PO as PO'. unfold apart in PO', Hblo.
    assert (INBL : In (bl2, 8 * bc2) (umap_blocks 24 bl2 bc2 (l1 ++ l2)))
      by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc2 0); [lia | left; reflexivity]).
    assert (PBL : p + 24 <= bl2 \/ bl2 + 8 * bc2 <= p) by (pose proof (PA bl2 (8 * bc2) INBL) as Hap; unfold apart in Hap; exact Hap).
    assert (INM : forall q n, In (q, n) (lbl LBm') -> exists qi, In (qi, q, n) LBm' /\ In (qi, q, n) LB'
                   /\ 0 < q /\ q mod 16 = 0 /\ AIMG_TOP <= q /\ q + n <= aceil /\ aapp q n).
    { intros q n Hq. destruct (lbl_in_inv LBm' q n Hq) as (qi & Qi).
      assert (QiL : In (qi, q, n) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact Qi).
      pose proof (ah_blocks H HH _ _ _ _ RH QiL) as (B0 & B16 & Bn & BI & BC & BF & BA).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, B16, Bn, BI, BC, BF, BA.
      exists qi. repeat split; assumption. }
    destruct (INM p 24 (Permutation_in _ (Permutation_sym PM) (or_introl eq_refl))) as (qp & QPm & QPl & _ & _ & PIM & PCE & PAPP).
    destruct (INM bl2 (8 * bc2) (Permutation_in _ (Permutation_sym PM) (or_intror INBL))) as (qbl & QBm & QBl & _ & _ & BIM & BCE & BAPP).
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    set (b0 := LbB_HEmpK.lasta (obj + 16) l1) in *.
    assert (B0C : b0 = obj + 16 \/
                  exists qb kb vb, In (qb, b0, 24) LBm' /\ In (qb, b0, 24) LB' /\ In (b0, (kb, vb)) (l1 ++ l2)
                                   /\ AIMG_TOP <= b0 /\ b0 + 24 <= aceil /\ aapp b0 24 /\ apart b0 24 obj 40 /\ apart p 24 b0 24).
    { destruct (lasta_cases l1 l2 (obj + 16)) as [[_ E0] | (kb & vb & Hin)]; [left; exact E0 | right].
      fold b0 in Hin.
      assert (INB : In (b0, 24) (umap_blocks 24 bl2 bc2 (l1 ++ l2))).
      { unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (b0, (kb, vb)). split; [reflexivity | exact Hin]. }
      destruct (INM b0 24 (Permutation_in _ (Permutation_sym PM) (or_intror INB))) as (qb & QB1 & QB2 & _ & _ & BB1 & BB2 & BB3).
      destruct (u_node U2 b0 kb vb Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & BOA & _).
      exists qb, kb, vb. split; [exact QB1|]. split; [exact QB2|]. split; [exact Hin|]. split; [exact BB1|].
      split; [exact BB2|]. split; [exact BB3|]. split; [exact BOA | exact (PA b0 24 INB)]. }

    assert (FWX : Forall (fun iv => aclient_write_ok H LB' iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv
                        /\ (snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) /\ wmix LBm' spz [(obj, obj + 40)] iv
                        /\ AIMG_TOP <= fst iv /\ snd iv <= aceil
                        /\ (snd iv <= obj + 24 \/ obj + 32 <= fst iv) /\ (snd iv <= p + 8 \/ p + 24 <= fst iv)) W).
    { eapply Forall_impl; [|exact FW]. intros iv [-> | [-> | (Hl & Hh)]].
      - destruct (blk_win s LB' m qp p 24 p (p + 8) RH QPl ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4 & W5).
        split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
        split; [right; right; exists qp, p, 24; split; [exact QPm | cbn; lia]|].
        cbn [Datatypes.fst Datatypes.snd]. lia.
      - destruct B0C as [E0 | (qb & kb & vb & QB1 & QB2 & Hin & BB1 & BB2 & BB3 & BOA & BPA)].
        + rewrite E0. destruct (obj_window_ok H HH LF obj LB' m (obj + 16) (obj + 16 + 8) RF LFO ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4).
          split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
          split; [unfold aapp, aapp_lo, aapp_hi in VA; cbn [Datatypes.fst Datatypes.snd]; lia|].
          split; [right; left; intros a Ha; cbn [rin_ivs Datatypes.fst Datatypes.snd] in *; left; lia|].
          cbn [Datatypes.fst Datatypes.snd]. unfold AFS_SIZE in *. lia.
        + unfold apart in BOA, BPA.
          destruct (blk_win s LB' m qb b0 24 b0 (b0 + 8) RH QB2 ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4 & W5).
          split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
          split; [right; right; exists qb, b0, 24; split; [exact QB1 | cbn; lia]|].
          cbn [Datatypes.fst Datatypes.snd]. lia.
      - destruct iv as [a1 a2]. cbn [Datatypes.fst Datatypes.snd] in Hl, Hh |- *.
        destruct (blk_win s LB' m qbl bl2 (8 * bc2) a1 a2 RH QBl Hl Hh) as (W1 & W2 & W3 & W4 & W5).
        split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
        split; [right; right; exists qbl, bl2, (8 * bc2); split; [exact QBm | cbn; lia]|].
        lia. }
    assert (F1 : Forall (aclient_write_ok H LB') W) by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 X)).
    assert (F2 : Forall (afs_write_ok H LF) W) by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 X))).
    assert (F3 : Forall aconst_ok W) by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 (proj2 X)))).
    assert (F4 : Forall stack0_ok W) by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 (proj2 (proj2 X))))).
    assert (FAPP : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W)
      by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 (proj2 (proj2 (proj2 X)))))).
    assert (FMIX : Forall (wmix LBm' spz [(obj, obj + 40)]) W)
      by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 X))))))).
    assert (FDJ : forall a n, (a + n <= AIMG_TOP \/ aceil <= a \/ (obj + 24 <= a /\ a + n <= obj + 32) \/ (p + 8 <= a /\ a + n <= p + 24)) ->
                  disjoint_from W a n).
    { intros a n Hc. apply djI. eapply Forall_impl; [|exact FWX].
      intros iv (_ & _ & _ & _ & _ & _ & X1 & X2 & X3 & X4). lia. }
    destruct (client_frame H HH s LB' LF B W m M2 RH RF AC RA MU2 WM2 F1 F2 F3) as (RH2 & RF2 & AC2 & RA2).
    assert (S02 : stack0 M2 lo shi) by (eapply stack0_transport; [exact S0 | exact MU2 | exact WM2 | exact F4]).
    assert (ERR2 : rw_cells asegs M2 (errno_addr tp) [C4 errv']).
    { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
      eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | apply FDJ; left; cbn; unfold ATP, AIMG_TOP; lia]. }
    assert (FR2 : FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz M2).
    { unfold FRAME, spf in *. eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 |].
      apply FDJ. right; left. exact ACL. }
    assert (ADO2 : addressable M2 obj 40)
      by (eapply addressable_transport; [exact AD | exact MU2 | exact WM2 | apply dsh_app; [exact FAPP | lia | lia | lia]]).
    assert (XP2 : xpres H LB0 spz [(obj, obj + 40)] m0 M2).
    { eapply (xpres_munch_mixed H HH s LB' LB0 LBm' spz [(obj, obj + 40)] W m0 m M2);
        [exact XP | exact RH | exact PE | unfold spf in ACL; lia | exact MU2 | exact WM2 | exact FMIX]. }
    assert (CSZ2 : rw_cells asegs M2 (obj + 24) [C8 (Z_to_bv 64 (Zlength ents))]).
    { rewrite <- ZL. eapply rw_cells_transport; [exact (rw_cells_of_cellw8 m (obj + 24) _ Csz ltac:(lia) ltac:(lia)) | exact MU2 | exact WM2 |].
      apply FDJ. right; right; left. cbn. lia. }
    assert (N82 : rw_cells asegs M2 (p + 8) [C8 (Z_to_bv 64 key)])
      by (eapply rw_cells_transport; [exact N8 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (N162 : rw_cells asegs M2 (p + 16) [C4 (Z_to_bv 64 key)])
      by (eapply rw_cells_transport; [exact N16 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (N202 : rw_cells asegs M2 (p + 20) [C4 (Z_to_bv 64 0)])
      by (eapply rw_cells_transport; [exact N20 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (HFP : forall a, umap_foot 24 obj bl2 bc2 (l1 ++ l2) a -> ~ (p <= a < p + 24)).
    { intros a [Ha | [[Hbc Ha] | (q & Hq & Hqa)]] Hpa'.
      - lia.
      - lia.
      - apply in_map_iff in Hq. destruct Hq as ([z [k v]] & Hz & Hin). cbn in Hz. subst z.
        pose proof (PA q 24 ltac:(unfold umap_blocks; apply in_app_iff; right; apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin])) as Hap.
        unfold apart in Hap. lia. }
    assert (HFR : forall a, umap_foot 24 obj bl2 bc2 (l1 ++ l2) a -> 0 <= a < 2 ^ 47).
    { intros a [Ha | [[Hbc Ha] | (q & Hq & Hqa)]]; [lia | lia |].
      apply in_map_iff in Hq. destruct Hq as ([z [k v]] & Hz & Hin). cbn in Hz. subst z.
      destruct (u_node U2 q k v Hin) as (_ & Hq0 & Hq1 & _). lia. }
    pose proof (proj1 Cp1) as Hfr.
    assert (B0R : 0 <= b0 /\ b0 + 8 <= 2 ^ 47).
    { destruct B0C as [E0 | (qb & kb & vb & _ & _ & Hin & _)]; [lia|].
      destruct (u_node U2 b0 kb vb Hin) as (_ & Hq0 & Hq1 & _). lia. }
    assert (HL2 : 0 <= hdaddr l2 < 2 ^ 64).
    { destruct l2 as [|[q [k v]] l2']; cbn [hdaddr]; [lia|].
      destruct (u_node U2 q k v ltac:(apply in_or_app; right; left; reflexivity)) as (_ & Hq0 & Hq1 & _). lia. }
    assert (HU : forall M', munch [(obj + 24, obj + 32)] M2 M' -> wmono asegs M2 M' ->
                   rw_cells asegs M' (obj + 24) [C8 (Z_to_bv 64 (Zlength ents + 1))] ->
                   umapx MI_A 24 (nval24 ASEGS) (lbl LB') M' obj bl2 bc2 (l1 ++ (p, (key, 0)) :: l2)).
    { intros M' MU' WM' CS'.
      exact (ins_umapx (lbl LB') m M2 obj key p bl2 bc2 l1 l2 U2 BC2 ltac:(rewrite ZL; lia) KR32 (lbl_in _ _ _ _ QPl) P0 P1 P16 PO PA MG2
        ltac:(intros a Ha Hnp Hnb; change (LbB_HEmpK.lasta (obj + 16) l1) with b0 in Hnp; pose proof (HFR a Ha) as Hr; pose proof (HFP a Ha) as Hnp';
              apply MU2; rewrite u64_of_Z by lia; apply outI; eapply Forall_impl; [|exact FW];
              intros iv [-> | [-> | (Hl & Hh)]]; cbn [Datatypes.fst Datatypes.snd]; lia)
        (cellw8_of_rw_cells M2 p (hdaddr l2) Cn2 HL2 ltac:(lia))
        (cellw8_of_rw_cells M2 (p + 8) key N82 ltac:(lia) ltac:(lia))
        (cellw4_of_rw_cells M2 (p + 16) key N162 KR32 ltac:(lia))
        (cellw4_of_rw_cells M2 (p + 20) 0 N202 ltac:(lia) ltac:(lia))
        (cellw8_of_rw_cells M2 b0 p Cs2 ltac:(lia) ltac:(lia))
        CB2 M' MU'
        (grows_of_munch_cell M2 M' (obj + 24) _ ltac:(replace (obj + 24 + 8) with (obj + 32) by lia; exact MU') CS'
           ltac:(lia) ltac:(lia))
        ltac:(rewrite ZL; exact (cellw8_of_rw_cells M' (obj + 24) (Zlength ents + 1) CS' ltac:(lia) ltac:(lia)))). }
    assert (SH2' : umap_sh M2 24 (bl2, bc2, l1 ++ (p, (key, 0)) :: l2)).
    { unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c. cbn [Datatypes.fst Datatypes.snd]. split.
      - intros Hbc. eapply addressable_transport; [exact (SHb Hbc) | exact MU2 | exact WM2 | apply dsh_app; [exact FAPP | lia | lia | lia]].
      - intros q k v Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Hin | Hin]].
        + assert (Hin' : In (q, (k, v)) (l1 ++ l2)) by (apply in_or_app; left; exact Hin).
          destruct (u_node U2 q k v Hin') as (_ & Hq0 & Hq1 & _).
          eapply addressable_transport; [exact (SHn q k v Hin') | exact MU2 | exact WM2 | apply dsh_app; [exact FAPP | lia | lia | lia]].
        + injection Hin as E1 E2 E3. subst q. eapply addressable_transport; [exact ADP | exact MU2 | exact WM2 | apply dsh_app; [exact FAPP | lia | lia | lia]].
        + assert (Hin' : In (q, (k, v)) (l1 ++ l2)) by (apply in_or_app; right; exact Hin).
          destruct (u_node U2 q k v Hin') as (_ & Hq0 & Hq1 & _).
          eapply addressable_transport; [exact (SHn q k v Hin') | exact MU2 | exact WM2 | apply dsh_app; [exact FAPP | lia | lia | lia]]. }
    assert (NDR : forall q k v, In (q, (k, v)) (l1 ++ (p, (key, 0)) :: l2) -> 0 <= q /\ q + 24 <= 2 ^ 47).
    { intros q k v Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Hin | Hin]].
      - destruct (u_node U2 q k v ltac:(apply in_or_app; left; exact Hin)) as (_ & Hq0 & Hq1 & _); lia.
      - injection Hin as E1 E2 E3; subst q; lia.
      - destruct (u_node U2 q k v ltac:(apply in_or_app; right; exact Hin)) as (_ & Hq0 & Hq1 & _); lia. }
    assert (PM2 : Permutation (lbl LBm') (umap_blocks 24 bl2 bc2 (l1 ++ (p, (key, 0)) :: l2))).
    { eapply perm_trans; [exact PM|]. unfold umap_blocks. rewrite !map_app. cbn [map fst].
      rewrite !app_assoc. apply Permutation_middle. }
    assert (PERM3 : Permutation (l1 ++ (p, (key, 0)) :: l2) ((p, (key, 0)) :: ents)).
    { eapply perm_trans; [apply Permutation_sym, Permutation_middle | apply perm_skip; exact PERM2]. }
    unfold QI.
    eapply (stage_end H HH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
              s msF mo M2 F fc) with (LB' := LB') (LBm' := LBm') (p := p) (bl' := bl2) (bc' := bc2)
            (ents' := l1 ++ (p, (key, 0)) :: l2) (rehashed := rehashed);
      [ exact VIS | exact FRZ | exact KR | exact MP | exact FR2 | exact SP16 | exact SPL | exact SPH | exact RAE
      | exact MI2 | exact ST2 | exact ERR2 | exact RA2 | exact TPV | exact ACL
      | exact LFO | exact Hoal | exact CSZ2 | lia | exact HU | exact SH2' | intros _; lia | exact NDR | exact ADO2
      | exact (wr_at_wmono _ _ _ _ WR WM2) | apply in_or_app; right; left; reflexivity | exact PERM3
      | exact CR3 | exact CR4 | exact RH2 | exact PE | exact PM2 | exact (lb_own_wmono _ _ _ OWN WM2) | exact XP2
      | exact RF2 | exact AC2 | exact S02 | exact AL ].
  Qed.

  Lemma stage_ins_pn : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (ents2 : list (Z * (Z * Z))) (rehashed : bool) (b : Z),
    ISTATE msF s m F fc y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 p bc2 ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPRE s mo m errv' LB' LBm' p bl2 bc2 ents2 rehashed ->
    cell8 ASEGS m (bl2 + 8 * hmod key bc2) b -> bucket_ok obj bc2 ents2 (hmod key bc2) b -> b <> 0 ->
    as_SR H QI (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
      errv' LB' LBm' p bl2 bc2 ents2 rehashed b VIS FRZ KR IP Cb Hbok Hbnz.
    unfold ISTATE in VIS.
    pose proof IP as IP0.
    destruct IP0 as (MP & FR & SP16 & SPL & SPH & RAE & MI & ST & ERR & RA & TPV & ACL & LFO & U2 & SH2 & PERM2 & BC2 & LOAD & KR32
                     & AD & WR & P0 & P1 & P16 & PO & PA & NC & ADP & CR3 & CR4 & RH & PE & PM & OWN & XP & RF & AC & S0 & AL).
    pose proof (obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3).
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (u_obj_lo U2) as Ho0. pose proof (u_obj_hi U2) as Ho1. pose proof (u_obj_al U2) as Hoal.
    pose proof (u_bl_lo U2 BC2) as Hbl0. pose proof (u_bl_hi U2) as Hbl1. pose proof (u_bl_obj U2 BC2) as Hblo.
    pose proof (u_bl_al U2) as Hbla.
    pose proof (LbB_HFind.BSEQ_boundA bc2 (u_bseq U2)) as BCR.
    destruct (u_hdr U2) as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    destruct SH2 as [SHb SHn]. unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn. cbn [Datatypes.fst Datatypes.snd] in SHb, SHn.
    pose proof PO as PO'. unfold apart in PO', Hblo.
    assert (INBL : In (bl2, 8 * bc2) (umap_blocks 24 bl2 bc2 ents2))
      by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc2 0); [lia | left; reflexivity]).
    assert (PBL : p + 24 <= bl2 \/ bl2 + 8 * bc2 <= p) by (pose proof (PA bl2 (8 * bc2) INBL) as Hap; unfold apart in Hap; exact Hap).
    assert (INM : forall q n, In (q, n) (lbl LBm') -> exists qi, In (qi, q, n) LBm' /\ In (qi, q, n) LB'
                   /\ 0 < q /\ q mod 16 = 0 /\ AIMG_TOP <= q /\ q + n <= aceil /\ aapp q n).
    { intros q n Hq. destruct (lbl_in_inv LBm' q n Hq) as (qi & Qi).
      assert (QiL : In (qi, q, n) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact Qi).
      pose proof (ah_blocks H HH _ _ _ _ RH QiL) as (B0 & B16 & Bn & BI & BC & BF & BA).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, B16, Bn, BI, BC, BF, BA.
      exists qi. repeat split; assumption. }
    destruct (INM p 24 (Permutation_in _ (Permutation_sym PM) (or_introl eq_refl))) as (qp & QPm & QPl & _ & _ & PIM & PCE & PAPP).
    pose proof (lb_own_In LBm' m _ OWN QPm) as WRP. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in WRP.
    set (h := hmod key bc2) in *.
    assert (Hh : 0 <= h < bc2) by (subst h; unfold hmod; apply Z.mod_pos_bound; lia).
    assert (GZO : gz m obj 40) by (intros i Hi; eapply sh0_of_addressable; [exact AD | change (8 * (40 / 8)) with 40; lia]).
    assert (GZP : gz m p 24) by (intros i Hi; eapply sh0_of_addressable; [exact ADP | change (8 * (24 / 8)) with 24; lia]).
    assert (GZB : gz m bl2 (8 * bc2)).
    { apply gzA; [exact (SHb BC2) | rewrite Z.mul_comm, Z_mod_mult; reflexivity]. }
    assert (SPLIT : exists l1 l2, ents2 = l1 ++ l2 /\ LbB_HEmpK.lasta (obj + 16) l1 = b /\ cell8 ASEGS m b (hdaddr l2)
                     /\ AIMG_TOP <= b /\ b + 8 <= 2 ^ 47 /\ b mod 8 = 0 /\ gz m b 8 /\ wr_at asegs m b 8
                     /\ (p + 24 <= b \/ b + 8 <= p) /\ (bl2 + 8 * bc2 <= b \/ b + 8 <= bl2)
                     /\ (forall i, 0 <= i < bc2 -> exists b', cell8 ASEGS m (bl2 + 8 * i) b'
                                                    /\ bucket_ok obj bc2 (l1 ++ (p, (key, 0)) :: l2) i b')).
    { destruct Hbok as [Hb0 | [Hin | (Hbo & Hne & Hhk)]]; [exfalso; exact (Hbnz Hb0) | |].
      - destruct (in_split_entsS Z b ents2 Hin) as (l1 & k & v & l2 & Ee).
        assert (Hin' : In (b, (k, v)) ents2) by (rewrite Ee; apply in_or_app; right; left; reflexivity).
        destruct (u_node U2 b k v Hin') as (_ & Bq0 & Bq1 & Bq16 & _ & _ & _ & _ & BOA & BBL).
        assert (INB : In (b, 24) (umap_blocks 24 bl2 bc2 ents2)).
        { unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (b, (k, v)). split; [reflexivity | exact Hin']. }
        destruct (INM b 24 (Permutation_in _ (Permutation_sym PM) (or_intror INB))) as (qb & QB1 & QB2 & _ & _ & BB1 & BB2 & BB3).
        pose proof (lb_own_In LBm' m _ OWN QB1) as WRB. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in WRB.
        pose proof (PA b 24 INB) as PAB. unfold apart in PAB, BOA. specialize (BBL BC2). unfold apart in BBL.
        exists (l1 ++ [(b, (k, v))]), l2. split; [rewrite Ee, <- app_assoc; reflexivity|].
        split; [apply lasta_snocI|].
        split; [rewrite Ee in *; exact (chain_atA Z m l1 b k v l2 (u_chain U2))|].
        split; [lia|]. split; [lia|]. split; [apply al8_16; exact Bq16|].
        split; [intros i Hi; eapply sh0_of_addressable; [exact (SHn b k v Hin') | change (8 * (24 / 8)) with 24; lia]|].
        split; [exact (wr_at_subE m b 24 b 8 WRB ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [lia|]. split; [lia|].
        intros i Hi. destruct (u_bkt U2 i Hi) as (b' & Cb' & Hok'). exists b'. split; [exact Cb'|].
        rewrite Ee in Hok'. destruct Hok' as [H0 | [Hn | (Hs & Hne' & Hi')]]; [left; exact H0 | right; left | right; right].
        + apply in_fst_ins. exact Hn.
        + split; [exact Hs|]. split; [intros Hc; symmetry in Hc; exact (app_cons_not_nil _ _ _ Hc)|].
          rewrite hdkey_snoc. exact Hi'.
      - assert (Hbo' : b = obj + 16) by exact Hbo. subst b.
        exists [], ents2. split; [reflexivity|]. split; [reflexivity|].
        split; [exact Cp1|]. split; [lia|]. split; [lia|]. split; [al8|].
        split; [intros i Hi; replace (obj + 16 + i) with (obj + (16 + i)) by lia; apply GZO; lia|].
        split; [exact (wr_at_subE m obj 40 (obj + 16) 8 WR ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [lia|]. split; [lia|].
        intros i Hi. destruct (u_bkt U2 i Hi) as (b' & Cb' & Hok'). exists b'. split; [exact Cb'|].
        destruct Hok' as [H0 | [Hn | (Hs & Hne' & Hi')]]; [left; exact H0 | right; left | right; right].
        + cbn [app map fst]. right. exact Hn.
        + cbn [app]. split; [exact Hs|]. split; [discriminate|]. cbn [hdkey]. rewrite Hi', <- Hhk. reflexivity. }
    destruct SPLIT as (l1 & l2 & Ee & Lb & Cbn & Bim & Bhi & Bal & GZb & WRb & BP & BBL & BKT).
    pose proof (proj1 Cbn) as Hnr.
    assert (Bpos : 0 < b) by (unfold AIMG_TOP in Bim; lia).
    unfold cell8 in Cb, Cbn, Cbl.

    remember (mkR y1 (Z_to_bv 64 (spf spz)) gp tp y5 y6 y7 (Z_to_bv 64 obj) y9 (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) (Z_to_bv 64 bc2) (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key)
                  y23 (Z_to_bv 64 h) (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc2; Z_to_bv 64 h;
                        Z_to_bv 64 bl2; Z_to_bv 64 b; Z_to_bv 64 (hdaddr l2)]).
    assert (HR : regs_ok E srI R).
    { unfold srI. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; unfold shEe, rShe; evs;
                rewrite ?w_add by lia; first [reflexivity | rewrite (LbB_HEmpS.srl3_val obj) by lia; reflexivity]] |]).
      apply Forall_nil. }
    assert (HK : know_ok asegs E m (kn_fix 20 [E_END] SCR_PN E_INS srI KNP0 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WRP | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WRb | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; unfold AIMG_TOP in *; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_INS m (seg_rom asegs) HR HK 60%nat [E_END] SCR_PN 50%N.
    { split_scs; first [ sckI | sc_shdj
                       | eapply (sc_flat _ _ _ _ (8 * h + bl2)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia]
                       | eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cb); [cbn; lia | evs; rewrite w_mul, w_add, v_addi_Z by lia; f_equal; lia | evs; reflexivity]
                       | sc_rd Cbn | sc_rd Cbl ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M2 := mem_denot E m lg) in Hms end end.
    assert (MU2 : munch [(b, b + 8); (p, p + 8)] m M2).
    { subst M2. apply munch_mem_denot; [exact Hlf|].
      apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                          cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; left; lia|].
      apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                          cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; right; left; lia|].
      apply Forall_nil. }
    assert (WM2 : wmono asegs m M2) by (subst M2; apply wmono_mem_denot).
    assert (MG2 : mem_grows m M2) by (subst M2; apply mem_denot_grows).
    assert (MI2 : mem_inv asegs M2) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST2 : stk asegs M2 lo spz) by (subst M2; apply stk_mem_denot; exact ST).
    assert (WRp8 : wr_at asegs m p 8) by exact (wr_at_subE m p 24 p 8 WRP ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (Cs2 : rw_cells asegs M2 b [C8 (Z_to_bv 64 p)]) by (subst M2; rwc_new Hlf WRb).
    assert (Cn2 : rw_cells asegs M2 p [C8 (Z_to_bv 64 (hdaddr l2))]) by (subst M2; rwc_new Hlf WRp8).
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 10%bv G10. rreg HR' 18%bv G18. rreg HR' 26%bv G26.
    rewrite w_add in G18 by lia.
    assert (G26' : getr R' 26%bv = rShe (Z_to_bv 64 (obj + 24))) by (rewrite G26; unfold rShe; rewrite w_add by lia; reflexivity).
    rewrite G10, G18, G26' in HRe.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    subst ents2.
    eapply (ins_post s msF1 mo1 m M2 F fc) with (l1 := l1) (l2 := l2) (W := [(b, b + 8); (p, p + 8)]);
      [ exact VIS1 | exact FRZ | exact KR1 | | exact MU2 | exact WM2 | exact MG2 | exact MI2 | exact ST2 | | | | ].
    - destruct IP as (MPx & IPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact IPr].
    - rewrite Lb. apply Forall_cons; [right; left; reflexivity|]. apply Forall_cons; [left; reflexivity | apply Forall_nil].
    - exact Cn2.
    - rewrite Lb. exact Cs2.
    - intros i Hi. destruct (BKT i Hi) as (b' & Cb' & Hok'). exists b'. split; [|exact Hok'].
      eapply cellw_agree; [exact Cb' | | lia | cbn; lia]. intros j Hj.
      apply MU2. rewrite u64_of_Z by lia. cbn [outside]. split; [lia|]. split; [lia | exact I].
  Qed.
End EmpI.
