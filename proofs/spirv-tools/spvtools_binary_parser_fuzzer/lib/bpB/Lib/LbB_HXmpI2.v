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
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_HXmpS LbB_HEmpK LbB_HXmpD LbB_HXmpI.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_HXmpI2 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib5Lists7ListDef6Forall00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=disjoint_fromK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z3addC46Stdlib5Lists4List:Forall_invC46Stdlib5Lists4List?Forall_inv_tailK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes4prod01I47Corelib7Numbers7BinNums1Z00K47Corelib4Init5Logic4True01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame7outsideC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic5False00C47Corelib4Init5Logic3iffC47Corelib4Init5Logic7and_indC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes3appI47Corelib4Init5Logic4True00C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes?RelationClasses=iff_ReflexiveK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC45stdpp9bitvector;definitions;bv_unsignedc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpI2;outside_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface4bptrC46Stdlib5Lists4List2InC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockI46Stdlib7Sorting;Permutation;Permutation00C46Stdlib5Lists4List8nil_consC46Stdlib7Sorting;PermutationBPermutation_lengthC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD3spfC45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD4rSheC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpI4IPREC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC4ARocqVerifyHarness?AgentSubmission7StoreOk9mem_growsC56Stdlib6ZArith6BinInt1Z3mulK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9bucket_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_MPRESC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD5FRAMEC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums1Z03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt>map_live_frameC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6nval24C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7ZlengthC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5apartK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9bseq_nextC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_ALC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface3ICMC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpI2QIC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB3lblC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;as_rauxv_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_RHEAPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own6lb_ownC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep5xpresC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_RFSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack06stack0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD9obj_placeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_hiC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_alC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_bl_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_bl_hiC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_bl_objC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_bseqC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HFind;BSEQ_boundAC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5u_hdrI5ARocqVerifyHarness?AgentSubmission7LibHash4HRep3hdr00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7definedC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3aC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3cC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpI<cells4_splitC46Stdlib5Lists4List:in_app_iffC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib5Lists7ListDef3mapC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K47Corelib4Init5Logic2or01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB:lbl_in_invC46Stdlib7Sorting;Permutation?Permutation_symK47Corelib4Init5Logic2or02C46Stdlib5Lists4List9in_or_appC46Stdlib7Sorting;Permutation>Permutation_inC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap9ah_blocksC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_sizeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ablock_rangeK47Corelib4Init5Logic2ex01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap6ah_fsbC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7afsb_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<afs_write_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9aconst_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack09stack0_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpI7blk_winC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface@aclient_write_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKit4wmixC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep7rin_ivsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD=obj_window_okC46Stdlib5Lists4List;Forall_implC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpI2<dj_of_forallC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<client_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack0@stack0_transportC56Stdlib6ZArith6BinInt1Z7pos_subC57Corelib7BinNums6PosDef3Pos3addK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC47Corelib4Init5Logic6eq_indC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega7EnvRing5PExpr04C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpI7dsh_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadowEaddressable_transportC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKitAxpres_munch_mixedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKitBrw_cells_of_cellw8C46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9umap_footC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6NArith6BinNat1N6to_natC4ARocqVerifyHarness?AgentSubmission8PropExec3rdnC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C46Stdlib9micromega;ZifyClasses6eq_iffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB6lbl_inC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpK5lastac6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpI2=out_of_forallC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKitBcellw8_of_rw_cellsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKitBcellw4_of_rw_cellsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpICgrows_of_munch_cellC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpI9ins_umapxK46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib7Sorting;PermutationBPermutation_middleK46Stdlib7Sorting;Permutation;Permutation04C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own;wr_at_wmonoK46Stdlib7Sorting;Permutation;Permutation02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own<lb_own_wmonoC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD9stage_endC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6hdaddrC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell8I5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5umapx00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep;umap_blocksC56Stdlib6ZArith6BinInt1Z2geC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt7umap_shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell4C5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3bK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_nodeC4ARocqVerifyHarness?AgentSubmission8LibIface4liveC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic7f_equalC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4AC_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4LY_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4MI_AK47Corelib4Init9Datatypes4bool02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9ALOWSH_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ARocqVerifyHarness?AgentSubmission8LibIface3memC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD5E_ENDC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3ATPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8AFS_SIZEI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEC46Stdlib5Lists4List8map_consC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4hmodC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own9lb_own_InC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpI3gzAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit2gzC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpD:wr_at_subEC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedK45stdpp9bitvector;definitions2bv01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6reg_evK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6kn_fixC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_mulC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<kwr_of_wr_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3sh0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8kshadow0C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond02C35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib7sc_flatC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit:div8_boundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit9estart_shC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotK4ARocqVerifyHarness?AgentSubmission8PropExec7FPState01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26e_addrC5ARocqVerifyHarness?AgentSubmission8SymExec33SX27e_widthC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame6insideK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?munch_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S?mem_denot_growsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge>msteps_mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv=stk_mem_denotC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells6cbytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvDrw_cells_mem_denot_wC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega5Tauto8GFormula01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge9rfull_mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge;msteps_fullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call=regs_keep_mkRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>ah_mpres_transc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpI2?munch_app_transC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame;wmono_transC4ARocqVerifyHarness?AgentSubmission7StoreOk?mem_grows_transC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5u_bktC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts8agree_onC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts;cellw_agreec6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpI2:front_postC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT9sr_blk_eqC4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics5Riscv3Sem7mul_divI4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5hdkeyK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpI24E_J2I5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpI23srTI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00K4ELinuxProcessSemantics5Riscv5Instr5aluop07c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HXmpI23KNTI5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00K47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_J2 : Z := 0xfbbb8.

Lemma dj_of_forall : forall (W : list (Z * Z)) a n, Forall (fun iv => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HXmpI2 ()) [] "p'0h02ivh12FWh21Wh32F1h42IHh51ah62a0h72hih81lh92loh:1ni001pi011zp;2p;1p;3p;5p;4p;6p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9p1001ip4p7210p1002Up4p710p8g0033R0j2BTg003Sj1ATg0043j3<Tg004Pj39Tg004mj32Tg005Nj31Tg006Sj1;Tg0073j33Tg007Sj26Tg0080j5:Tg008Oj5@Tg0093j4?Tg009Nj6>Tg00:0j24Tg00:Lj28Tg00:fj4=Tf4R1f3R2'6f2R3'4f1R4f0R5'4'8p=0g00;FR6P6P4P5C=p=514231445'8p=71B66R7#AR8P3P4A<665R9A9665R:P3D0X07=273P7P1P2P9P:P1D0X07=275A1412]1X28P2P3P9P:P2D0X07%;7R;527g00;dA1;23eW1P0P6P6f6R0f5R;P9P:P0D0X07=275A140;]1f7R<P0P9P:P<D0X07A3734527A3723?1<0]1[^88P5f9R<f8R0P9P:P<D0X07=275A14<0]1f:R0P<P9P:P0D0X071523=374527P7f;R=/60R>P9P:P=C7X07R?1512R@P3P5D:P?P@O1P>P;P1P=C7A12=0P5P3P7f<R>P=P9P:P>D0X0715;1P2P4D@O1C?b3A37@3?10<eW1W4X28X76X96P4P5O2n2001100000120101101X67P2P5E>W1X:6X56W2o"). Qed.

Lemma out_of_forall : forall (W : list (Z * Z)) x, Forall (fun iv => x < fst iv \/ snd iv <= x) W -> outside W x.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HXmpI2 ()) [] "p'0h02ivh12FWh21Wh34__x1h44__x2h54__x3h62F1h72IHh87__arithh94__ffh:8__varmaph;5__with<1ah=2hih>1lh?2loh@1xi001pi011zp;2p;1p;3p;5p;4p;7p;6p;8g0033R0j2XTg003Sj1<Tg0043j3ETg004Pj3ATg004mj32Tg00<@j21Tg006Sj1;Tg0073j35Tg0080j5@Tg00:0j26Tg00=?j29Tg00=[j2=Tg00>6j1VTg00>Oj2:Tg00>mj4UTg00?Kj1TTg00?ij1QTg00@Tj1ITg00A9j28Tg00A\j44Tg00BGj1DTg00Blj7FTg00CPj1CTg00D2j7GTg00DVj6HTg00E:j8BTg00E^j2JTg00F@j2KTg00FZj2LTg00GFj3MTg00G`j3NTg00H?j4?Tg008Oj5OTg0093j4PTg009Nj6>Tg00:Lj2RTg00:fj4STg00I1j7WTf3R1f2R2'9f1R3f0R4'6'Rp=0g00;FR5P5P3P4CSp=7P3g00IUR6g00J4R7P7g00JTR8P4g00K4FWp=31X55R9#<R:P3AE554R;AA554R<P3C0X09=293P9P1P;P<P1C0X09=2941131]1X2:P2P;P<P2C0X09%;9R=529g00;d11=2eW1P0P5P5f5R0P;P<P0C0X09=2941130]1f6R=P;P<P=C0X09A5923529A5912/1=]1[^>:P4f8R>P;P<P>C0X09=294113>]1f9R>P;P<P>C0X091712=593529P9f:R?P;P<P?C0X09R@f4RA/71RBP2P4D@P@PBO1160?19?A'=#V111?g00KTR?#;%<?P51:52P31:51CU%T5%Q5R?P6P7P7P8P?P6P7P7P8P5g00L@R@#I,85RCg00LeRD185@REC4,3?P5%D@,85R@g00MLRFPCC4,3?FF%C7P?P6P7P7P8P?P6P7P7P8P5PEPFPCC4,3?P5PCPDP@C4,3?FGEHGB1J?8P4P2g00N3R?g00NSR8'K1L42=M?8dg00O3=N53C?b9b:b;X35X45X55P3P4P2P3C016321921'=g00OQ[[^35^45^55P4P0f;R8P=P3O4b8P2P9P8P;P<P8C0X09170AP1P3DOO1CPb6A59B2/1>eW1W7X2:X=5X?5P3P4O2n2001100000121101101X<9P2P4E>W1X@5W2o"). Qed.

Lemma outside_app : forall (A B : list (Z * Z)) x, outside (A ++ B) x <-> outside A x /\ outside B x.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HXmpI2 ()) [] "p'0h02H2h12H0h22H3h31Hh42H1h52H6h61Ah71Bh82H4h92H5h:2H7h;2IHh<1ah=2hih>1lh?5lemmah@2lohA1xi001pi011zp;2p;1p;4p;5p;3p;;p;9g0033R0j2GTg003Sj1FTg00<@j21Tg00OnR1j27Tg00=[R2j20Tg0093j46Tg00PGj53Tg006Sj1;Tg0073j3:Tg00:0j25Tg00=?j24Tg00>6j19Tg00Pdj4ETg00QKj3DTg00RAj4CTg00S4l;BTg00Soj2?Tg00T[l9>Tg00UUj2@Tg00:fj4ATg009Nj5=Tg00V4j3<Tf3R3f2R4f1R53<f0R6'1p=21145/06p=8g00;FR7/G7R8#FR9P8P8P6P4P5C21145R:9865'7X691156R;g00VQR</0:[10<;R=P:[P<P:g00;dP6C6X3;P<P:P:1134P6W4X1<P6D3X3=C6P8%;8R=P5P6C2A8=6;'7eP0P7P7P8P6f4R0P3C211039863'7P8A:845R=f5R;P0C211;098=0'7[^>9P6P8P6f7R=f6R<C211=<986<'7P8P5f8R:P=C2R>115=R?11:=R@'0RA'7p-0RBP1g00Vm150:14:3'0#9RCP8P4f9RDP:C2RE'0114:RF11D:RG'0RH,0CPBPB^7BP1PBPBP1P1CEP2g00W^PCPBP1g00XP9DB1PCCCPEPHP6M;B10CF/0GRGPG1?BGM9>W?P6PH\>R>PE\A153=14=4'0#9RE/0A10E?/0@'7P8P3f:REPDC2\H113DRHf;R?/1ERAP411;?RGf<RB/1?RFP5P6C6O1W0W4P8P;PBP?C2\A\H15<E14E;'0#9RH110ER0/0A'0RC15=?14?<'0#9R1/0GR2/0FRI[10H0/0ARA10GFRG,01R0[P1PGPIf=RI/1BRG98<B11=IR<f>RH/1IRJ15DI14I:'0#9RK/0</0Jf?RL/1HP;P5O1f@RM/1LP8PEfARNPMC2RO[RPP6P5O1RQPOPDP6O1RDfBRR/1N98?NR?11BRRBfCRS/1RRT15HR14RI'0#9RI/0B/0TfDRU/1SRV15MURUfERW/4MRMPEfFRE,5RRX14ENRYP5P6C6RZO1W5W2g00OQR[\M\UR\15NW/0MRN#9R]11LWRL'011EWREP]PLPXPYP[fG/4RRRP3P5O1RWfH/4SP[[RSPQP[1@[6R^b2b0W:X5XP6D3X0NP]eP4C6P5C6b2W9X3BP6D3b2b4b2W8X1<P6D3W2X01P6D3X1CP2PFP0PKP<10<J,0K11:HP;P6O1PPP6P3O1POPDP?PBPT10BT,0IP:PZO1X5MX0UP\P]10LEPXPYP[PWPSPQP[P^b0b1X:RX5XP6D3X1NP]ePLPEP4P5C6C6b0X9VX3BP6D3b0b4b0W8X1KP5D3X2GX02P6D3X1AC6b4W1X3>P6D3O2P8P7P7P3P4CA=:85R3P:P=C2A83=@'7eW;X69X=7X@7P5P6O2n2001100000121101101X<8P4D=XA7X79W6o"). Qed.

Lemma munch_app_trans : forall (W1 W2 : list (Z * Z)) m1 m2 m3, munch W1 m1 m2 -> munch W2 m2 m3 -> munch (W1 ++ W2) m1 m3.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HXmpI2 ()) [] "h01xh11Ah21Bh32Hxh41Hh52H1h62H2h72M1h82M2h92W1h:2W2h;2m1h<2m2h=2m3h>1op;2p;1p;3p;6g0033j2=Tg003Sj1<Tg00@Tj11Tg00Y@j17Tg00Y^j18Tg00ZAj1:Tg00Zcj35Tg00V4j34Tg00[`j22Tg00<@j20Tg00=[R0j23Tg00\Jj39Tg00GFj36Tg002Uj6;Tg00;FR1/=1R2#<R3g00L@#1#1#1R4#1#1#1#7R5#8R6%74#8#:R4[R7f4R8f2R9f1R:35R;f7R<f6R=542f0R>,25'0P0A429:/0>f3R?/0:109:'3[R@109>10:>'3A42?9/0:RA[108910?9'3\AA99:>P:n2001000000120000000X01X23X13P@^01^23^13P>f9R1f8R@1259RAP:O4101A10@A'3P0f:R0125?R?'0101?P<P8O1P1P8O1564P>f<R?f5RA,25'0125=,0?P4f;P<O1f=P@O1964>X>4P1P<P:O2P0P<O1P@P<P>O2E;W6W5P:P>O2n2001000000120000000b3b4W3X06A42=A?589eX8;W7X=7X<7W;X:3W9o"). Qed.

Definition srT : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (13%bv, EVar 34); (19%bv, ELit SHBASE)].
Definition KNT : list kentry := [KWr (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 33)) (EVar 34)) 0) (ELit 8)].
Definition SCR_T := SCR [false; false] [] [].

Section EmpI2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spz : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc key : Z) (ents : list (Z * (Z * Z))).
  Variables (lo B shi : Z) (m0 : mem) (mo0 : Model).

  Abbreviation IPREx := (IPRE H ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).
  Abbreviation QIx := (QI H ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).

  Lemma front_post : forall (s : as_St H) (msF : machine_state) (mo : Model) (m M2 : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (ents2 : list (Z * (Z * Z))) (rehashed : bool) (W : list (Z * Z)),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 (spf spz)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 (obj + 24)) y19 y20 y21 y22 y23 y24 y25 (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_END) fc None M2 (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ents2 rehashed ->
    munch W m M2 -> wmono asegs m M2 -> mem_grows m M2 -> mem_inv asegs M2 -> stk asegs M2 lo spz ->
    Forall (fun iv => iv = (p, p + 8) \/ iv = (obj + 16, obj + 24) \/ (bl2 <= fst iv /\ snd iv <= bl2 + 8 * bc2)) W ->
    rw_cells asegs M2 p [C8 (Z_to_bv 64 (hdaddr ents2))] -> rw_cells asegs M2 (obj + 16) [C8 (Z_to_bv 64 p)] ->
    (forall i, 0 <= i < bc2 -> exists b', cell8 ASEGS M2 (bl2 + 8 * i) b' /\ bucket_ok obj bc2 ((p, (key, 0)) :: ents2) i b') ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m M2 F fc y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31
      errv' LB' LBm' p bl2 bc2 ents2 rehashed W VIS FRZ KR IP MU2 WM2 MG2 MI2 ST2 FW Cn2 Cs2 CB2.
    assert (FW' : Forall (fun iv => iv = (p, p + 8) \/ iv = (LbB_HEmpK.lasta (obj + 16) [], LbB_HEmpK.lasta (obj + 16) [] + 8)
                                    \/ (bl2 <= fst iv /\ snd iv <= bl2 + 8 * bc2)) W).
    { eapply Forall_impl; [|exact FW]. intros iv [-> | [-> | Hb]];
        [left; reflexivity | right; left; cbn [LbB_HEmpK.lasta]; f_equal; lia | right; right; exact Hb]. }
    exact (ins_post H HH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
             s msF mo m M2 F fc y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31
             errv' LB' LBm' p bl2 bc2 [] ents2 rehashed W VIS FRZ KR IP MU2 WM2 MG2 MI2 ST2 FW' Cn2 Cs2 CB2).
  Qed.

  Lemma front_tail : forall (s : as_St H) (msF : machine_state) (mo : Model) (m M1 : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y8 y9 y12 y14 y15 y16 y17 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (fn k1 v1 : Z) (rest : list (Z * (Z * Z))) (rehashed : bool),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 (spf spz)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) (Z_to_bv 64 (hmod k1 bc2)) y12
                             (Z_to_bv 64 bl2) y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) y20 y21 y22 y23 y24 y25
                             (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_J2) fc None M1 (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ((fn, (k1, v1)) :: rest) rehashed ->
    munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * hmod key bc2, bl2 + 8 * hmod key bc2 + 8)] m M1 -> wmono asegs m M1 ->
    mem_grows m M1 -> mem_inv asegs M1 -> stk asegs M1 lo spz ->
    rw_cells asegs M1 p [C8 (Z_to_bv 64 fn)] -> rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)] ->
    rw_cells asegs M1 (bl2 + 8 * hmod key bc2) [C8 (Z_to_bv 64 (obj + 16))] ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m M1 F fc y1 y5 y6 y7 y8 y9 y12 y14 y15 y16 y17 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31
      errv' LB' LBm' p bl2 bc2 fn k1 v1 rest rehashed VIS FRZ KR IP MU1 WM1 MG1 MI1 ST1 Cn1 Cs1 Cb1.
    pose proof IP as IP0.
    destruct IP0 as (MP & FR & SP16 & SPL & SPH & RAE & MI & ST & ERR & RA & TPV & ACL & LFO & U2 & SH2 & PERM2 & BC2 & LOAD & KR32
                     & AD & WR & P0 & P1 & P16 & PO & PA & NC & ADP & CR3 & CR4 & RH & PE & PM & OWN & XP & RF & AC & S0 & AL).
    pose proof (obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (u_obj_lo U2) as Ho0. pose proof (u_obj_hi U2) as Ho1.
    pose proof (u_bl_lo U2 BC2) as Hbl0. pose proof (u_bl_hi U2) as Hbl1. pose proof (u_bl_obj U2 BC2) as Hblo. unfold apart in Hblo.
    pose proof (u_bl_al U2) as Hbla.
    pose proof (LbB_HFind.BSEQ_boundA bc2 (u_bseq U2)) as BCR.
    destruct (u_node U2 fn k1 v1 (or_introl eq_refl)) as (_ & Fn0 & Fn1 & _ & _ & _ & K1R & _ & _ & _).
    destruct SH2 as [SHb SHn]. unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn. cbn [Datatypes.fst Datatypes.snd] in SHb, SHn.
    assert (INBL : In (bl2, 8 * bc2) (umap_blocks 24 bl2 bc2 ((fn, (k1, v1)) :: rest)))
      by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc2 0); [lia | left; reflexivity]).
    assert (PBL : p + 24 <= bl2 \/ bl2 + 8 * bc2 <= p) by (pose proof (PA bl2 (8 * bc2) INBL) as Hap; unfold apart in Hap; exact Hap).
    destruct (lbl_in_inv LBm' bl2 (8 * bc2) (Permutation_in _ (Permutation_sym PM) (or_intror INBL))) as (qbl & QBm).
    pose proof (lb_own_In LBm' m _ OWN QBm) as WRB. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in WRB.
    pose proof PO as PO'. unfold apart in PO'.
    set (idx := hmod key bc2) in *.
    assert (IDX : 0 <= idx < bc2) by (subst idx; unfold hmod; apply Z.mod_pos_bound; lia).
    set (idx2 := hmod k1 bc2) in *.
    assert (IDX2 : 0 <= idx2 < bc2) by (subst idx2; unfold hmod; apply Z.mod_pos_bound; lia).

    assert (QBL : In (qbl, bl2, 8 * bc2) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact QBm).
    pose proof (ah_blocks H HH _ _ _ _ RH QBL) as (_ & _ & _ & BIM & BCE & _ & BAPP).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in BIM, BCE, BAPP.
    destruct (lbl_in_inv LBm' p 24 (Permutation_in _ (Permutation_sym PM) (or_introl eq_refl))) as (qp & QPm).
    assert (QPL : In (qp, p, 24) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact QPm).
    pose proof (ah_blocks H HH _ _ _ _ RH QPL) as (_ & _ & _ & PIM & PCE & _ & PAPP).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in PIM, PCE, PAPP. unfold AIMG_TOP in PIM, BIM.

    assert (FAPP1 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv)
                      [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * idx, bl2 + 8 * idx + 8)]).
    { unfold aapp, aapp_lo, aapp_hi in VA, PAPP, BAPP.
      apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia | apply Forall_nil]. }
    assert (GZB1 : gz M1 bl2 (8 * bc2)).
    { apply gzA; [| rewrite Z.mul_comm, Z_mod_mult; reflexivity].
      eapply addressable_transport; [exact (SHb BC2) | exact MU1 | exact WM1 | apply dsh_app; [exact FAPP1 | lia | lia | lia]]. }
    assert (WRK : wr_at asegs M1 (bl2 + 8 * idx2) 8)
      by exact (wr_at_subE M1 bl2 (8 * bc2) (bl2 + 8 * idx2) 8 (wr_at_wmono _ _ _ _ WRB WM1) ltac:(lia) ltac:(lia) ltac:(lia)).
    remember (mkR y1 (Z_to_bv 64 (spf spz)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) (Z_to_bv 64 idx2) y12
                  (Z_to_bv 64 bl2) y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) y20 y21 y22 y23 y24 y25
                  (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 idx2; Z_to_bv 64 bl2]).
    assert (HR : regs_ok E srT R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]).
      apply Forall_nil. }
    assert (HK : know_ok asegs E M1 (kn_fix 20 [E_END] SCR_T E_J2 srT KNT 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WRK | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_J2 M1 (seg_rom asegs) HR HK 20%nat [E_END] SCR_T 50%N.
    { split_scs; first [ sckI | sc_shdj
                       | eapply (sc_flat _ _ _ _ (8 * idx2 + bl2)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia] ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E M1 lg) in Hms; set (M2 := mem_denot E M1 lg) in Hms end end.
    set (bk2 := bl2 + 8 * idx2) in *.
    assert (MU12 : munch [(bk2, bk2 + 8)] M1 M2).
    { subst M2. apply munch_mem_denot; [exact Hlf|].
      apply Forall_cons; [|apply Forall_nil]. cbn [e_addr e_width]. unfold estart; evs. rewrite ?w_mul, ?w_add, ?u64_of_Z by lia.
      cbn [inside a_off Z.of_nat Pos.of_succ_nat Pos.succ]. left. lia. }
    assert (WM12 : wmono asegs M1 M2) by (subst M2; apply wmono_mem_denot).
    assert (MG12 : mem_grows M1 M2) by (subst M2; apply mem_denot_grows).
    assert (MI2 : mem_inv asegs M2) by exact (msteps_mem_inv asegs _ _ Hms MI1).
    assert (ST2 : stk asegs M2 lo spz) by (subst M2; apply stk_mem_denot; exact ST1).
    assert (Cb2 : rw_cells asegs M2 bk2 [C8 (Z_to_bv 64 p)]) by (subst M2; rwc_new Hlf WRK).
    assert (Cn2 : rw_cells asegs M2 p [C8 (Z_to_bv 64 fn)])
      by (eapply rw_cells_transport; [exact Cn1 | exact MU12 | exact WM12 | cbn [disjoint_from cells_size csize Z.of_nat]; subst bk2; lia]).
    assert (Cs2 : rw_cells asegs M2 (obj + 16) [C8 (Z_to_bv 64 p)])
      by (eapply rw_cells_transport; [exact Cs1 | exact MU12 | exact WM12 | cbn [disjoint_from cells_size csize Z.of_nat]; subst bk2; lia]).
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 10%bv G10. rewrite G10 in HRe.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (front_post s msF1 mo1 m M2 F fc) with
      (W := [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * idx, bl2 + 8 * idx + 8); (bk2, bk2 + 8)]) (ents2 := (fn, (k1, v1)) :: rest);
      [ exact VIS1 | exact FRZ | exact KR1 | | | | | | | | | | ].
    - destruct IP as (MPx & IPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact IPr].
    - exact (munch_app_trans [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * idx, bl2 + 8 * idx + 8)] [(bk2, bk2 + 8)] m M1 M2 MU1 MU12).
    - exact (wmono_trans asegs _ _ _ WM1 WM12).
    - exact (mem_grows_trans _ _ _ MG1 MG12).
    - exact MI2.
    - exact ST2.
    - apply Forall_cons; [left; reflexivity|]. apply Forall_cons; [right; left; reflexivity|].
      apply Forall_cons; [right; right; cbn; lia|]. apply Forall_cons; [right; right; cbn; subst bk2; lia | apply Forall_nil].
    - exact Cn2.
    - exact Cs2.
    - intros i Hi. destruct (Z.eq_dec i idx2) as [->|Hne2].
      + exists p. split; [exact (cellw8_of_rw_cells M2 bk2 p Cb2 ltac:(lia) ltac:(lia))|]. right; left; left; reflexivity.
      + destruct (Z.eq_dec i idx) as [->|Hne1].
        * exists (obj + 16). split.
          -- assert (C1 : rw_cells asegs M2 (bl2 + 8 * idx) [C8 (Z_to_bv 64 (obj + 16))]).
             { eapply rw_cells_transport; [exact Cb1 | exact MU12 | exact WM12 |]. cbn [disjoint_from cells_size csize Z.of_nat]. subst bk2. lia. }
             exact (cellw8_of_rw_cells M2 (bl2 + 8 * idx) (obj + 16) C1 ltac:(lia) ltac:(lia)).
          -- right; right. split; [reflexivity|]. split; [discriminate|]. reflexivity.
        * destruct (u_bkt U2 i Hi) as (b' & Cb' & Hok'). exists b'. split.
          -- eapply cellw_agree; [exact Cb' | | lia | cbn; lia]. intros j Hj.
             rewrite (MU12 (Z_to_bv 64 (bl2 + 8 * i + j))) by (rewrite u64_of_Z by lia; cbn [outside]; subst bk2; split; [lia | exact I]).
             apply MU1. rewrite u64_of_Z by lia. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I].
          -- destruct Hok' as [H0 | [Hn | (Hs & Hne & Hi')]]; [left; exact H0 | right; left; right; exact Hn |].
             exfalso. apply Hne2. rewrite Hi'. reflexivity.
  Qed.
End EmpI2.
