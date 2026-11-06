(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HWord HLib HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_HEmpS LbB_HEmpK LbB_HEmpD LbB_HEmpI LbB_HEmpI2 LbB_HEmpI3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_HEmpI4 () := "C69OSSVerify5KrLib3bpB2Rt7BsIface5blockC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C46Stdlib5Lists4List8nil_consC46Stdlib7Sorting;Permutation>Permutation_inC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib3bpB2Rt7BsIface5as_StC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpI6ISTATEC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7FPSteps8frm_zeroC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib3bpB2Rt7BsIface8as_AKRELC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpI4IPREC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib7LibHash4HRep4hmodC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep5cell8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface8as_MPRESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpD5FRAMEC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib3bpB3Lib9LbB_HEmpD3spfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes4list01C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib3bpB2Rt8BsShadow5aceilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_HEmpStmt>map_live_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep6nval24C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7LibHash4HRep7ZlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib7LibHash4HRep5apartC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib7LibHash4HRep9bseq_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5as_ALC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib3bpB2Rt9RtB_Iface3ICMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpI2QIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB3lblC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface;as_rauxv_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow;addressableC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib3bpB2Rt7BsIface8as_RHEAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib7LbB_Own6lb_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt6BXXRep5xpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface6as_RFSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsConst6ACONSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsStack06stack0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpD9obj_placeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow4aappC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface6as_FSBC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib3bpB2Rt8BsShadow;aceil_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF8BeapCeil5hceilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep8u_obj_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep8u_obj_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep7u_bl_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep7u_bl_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep8u_bl_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HFind;BSEQ_boundAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep5u_hdrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7LibHash4HRep3hdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts3t3aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts3t3cC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:in_app_iffK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3notK47Corelib4Init5Logic2or01C46Stdlib7Sorting;Permutation?Permutation_symK47Corelib4Init5Logic2or02C69OSSVerify5KrLib3bpB3Lib8LbB_MILB:lbl_in_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib7LbB_Own9lb_own_InC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface8blk_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface8blk_sizeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib3bpB2Rt9BsCXXHeap9ah_blocksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface<ablock_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z7compareC69OSSVerify5KrLib3bpB3Lib8LbB_ConvBsh0_of_addressableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib7LbB_Kit2gzC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC69OSSVerify5KrLib3bpB3Lib9LbB_HEmpI3gzAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpI<cells4_splitC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib6BCells8cells_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib6BCells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic5proj2C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpD:wr_at_subEC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib3bpB3Lib9LbB_HEmpD4rSheC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame3mkRC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpD4shEeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib<regs_ok_seedC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib8SymExec33SX26edenotC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib3bpB2Rt7BsIface6as_VISC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib:BLPropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BMState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib5EseedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC59OSSVerify5KrLib8SymExec33SX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpS8srl3_valC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib7LibHash4HLib;regs_ok_srsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX25saddr01C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz07C59OSSVerify5KrLib7LibHash4HLib5w_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib5w_mulC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib8SymExec33SX26a_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib=sc_read_cellwC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX28sidecond06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib7sc_flatC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX28sidecond02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib7LbB_Kit6kn_fixC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib8u64_of_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S5elenZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib7LbB_Kit3sh0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib7LbB_Kit8kshadow0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX28sidecond01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX28sidecond03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib=SymExec3Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib7LbB_Kit:div8_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib7LbB_Kit9estart_shC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9scs_denotC1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib8PropExec7FPState01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26sentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX29sym_state01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX27scripts01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX28sym_execC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7SymRun39run_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25s_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX24s_pcC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib=SymExec3Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26e_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX27e_widthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame6insideC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC69OSSVerify5KrLib3bpB3Lib8LbB_Conv?munch_mem_denotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame5munchC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC79OSSVerify5KrLib3bpB2HF3Lib6BCells6cbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib3bpB3Lib:LbB_Bridge5rfullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_Bridge9rfull_mkRC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_Bridge;msteps_fullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_Call=regs_keep_mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_Bridge>msteps_mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9BsCXXHeap>ah_mpres_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib3bpB3Lib8LbB_Conv?wmono_mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S?mem_denot_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_Conv=stk_mem_denotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib3bpB3Lib8LbB_HKitBcellw8_of_rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep5hdkeyC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7LibHash4HRep5u_bktC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC79OSSVerify5KrLib3bpB2HF3Lib7BLFrame7outsideC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib7LibHash9HRepFacts8agree_onC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash9HRepFacts;cellw_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI2:front_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_VecT9sr_blk_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI3@bseq_land_boundEC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI3:bseq_pow2EC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib7LibHash4HLib5br_neC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib5w_andC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7LibHash4HLib6w_addmC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib7LibHash4HLib5br_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI37land_1EC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI38front_j2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC4ELinuxProcessSemantics5Riscv3Sem<branch_takenC59OSSVerify5KrLib7LibHash4HLib6br_ltuC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z6ltb_geC4ELinuxProcessSemantics5Riscv3Sem7mul_divC59OSSVerify5KrLib7LibHash4HLib6w_remuC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7LibHash4HRep5umapx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep;umap_blocksC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib5BStep8rw_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2geC79OSSVerify5KrLib3bpB2HF3Lib4BMem5wr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib;LbB_PrsStmt7umap_shC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame3stkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib4BMem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5as_SRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep6u_bseqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep6hdaddrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep5cell4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts3t3bC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C47Corelib4Init9Datatypes3sndC4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib=SymExec3Sound4SX2S6reg_evC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX23env01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C35stdpp7tactics<f_equal_helpK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib7LibHash4HLib8v_addi_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26adenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_Conv<kwr_of_wr_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06I49OSSVerify5KrLib6CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib5Lists7ListDef6Forall00C69OSSVerify5KrLib3bpB3Lib8LbB_ConvDrw_cells_mem_denot_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep9bucket_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep6u_nodeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface4liveC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib3bpB3Lib8LbB_MILB4AC_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB4LY_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB4MI_AC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt5BSegs5asegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib3bpB2Rt5BSegs8AIMG_TOPC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init5Logic4True01I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith4Znat3N2Z6inj_leK4ELinuxProcessSemantics5Riscv5Instr5mulop01I59OSSVerify5KrLib8SymExec33SX26kentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C69OSSVerify5KrLib3bpB3Lib7LbB_Kit6SHBASEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26sentry00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpI5E_INSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpI3srIC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI33LGFC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C49OSSVerify5KrLib8LibIface3memC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib3bpB2Rt7BsIface3ATPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface8AFS_SIZEC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01I59OSSVerify5KrLib8SymExec33SX23env00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25sr_idC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpD5E_ENDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI24E_J2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI36SCR_F0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI33KNFC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01I59OSSVerify5KrLib8SymExec33SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX27scripts00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI36SCR_F2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI36SCR_F3C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI36SCR_F4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop08c69OSSVerify5KrLib3bpB3Lib:LbB_HEmpI4?stage_ins_frontC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_HEmpI<stage_ins_pnC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section EmpI4.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spz : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc key : Z) (ents : list (Z * (Z * Z))).
  Variables (lo B shi : Z) (m0 : mem) (mo0 : Model).

  Abbreviation IPREx := (IPRE H ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).
  Abbreviation QIx := (QI H ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).
  Abbreviation ISTATEx := (ISTATE H gp tp s11 spz obj key).

  Ltac sckH HV := eapply ck_srl; [evs; rewrite ?w_addm, ?w_and, ?w_remu by lia; rewrite HV; rewrite w_add by lia; reflexivity | lia | lia].
  Ltac shdjF := unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in *; sc_shdjX.
  Ltac fsc Rdb Flb HV :=
    lazymatch goal with
    | |- sc_denot _ _ _ (SCDisj (SA (EAlu ALU_SRL _ _) _) _ _ _) => shdjF
    | |- sc_denot _ _ _ (SCDisj _ _ (SA (EAlu ALU_SRL _ _) _) _) => shdjF
    | |- sc_denot _ _ _ (SCDisj _ _ _ _) => unfold apart in *; sc_djX
    | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_SRL _ _) _) _) => sc_shdjX
    | |- sc_denot _ _ _ (SCBr _ _ (EAlu ALU_AND (EVar 35) _) _) => sc_andE
    | |- sc_denot _ _ _ (SCBr false BC_NE (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_AND _ _) _) _) _) => sckH HV
    | |- sc_denot _ _ _ (SCBr false BC_NE (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_REMU _ _) _) _) _) => sckH HV
    | |- sc_denot _ _ _ (SCReadBase (SA (EAlu ALU_ADD (EMd _ _ _) _) _) _ _ _) => exact Rdb
    | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_ADD (EMd _ _ _) _) _) _) => exact Flb
    | |- sc_denot _ _ _ (SCBr _ _ _ _) => first [sckI | sc_br]
    | |- sc_denot _ _ _ (SCReadBase _ _ _ _) => match goal with H : cellw _ _ _ _ _ |- _ => sc_rd H end
    | |- sc_denot _ _ _ (SCFlat _ _) => sc_fl
    end.

  Lemma stage_ins_front : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (ents2 : list (Z * (Z * Z))) (rehashed : bool),
    ISTATEx msF s m F fc y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 p bc2 ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ents2 rehashed ->
    cell8 ASEGS m (bl2 + 8 * hmod key bc2) 0 ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
      errv' LB' LBm' p bl2 bc2 ents2 rehashed VIS FRZ KR IP Cb0.
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
    assert (INBL : In (bl2, 8 * bc2) (umap_blocks 24 bl2 bc2 ents2))
      by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc2 0); [lia | left; reflexivity]).
    pose proof (PA bl2 (8 * bc2) INBL) as PBL.
    assert (INM : forall q n, In (q, n) (lbl LBm') -> exists qi, In (qi, q, n) LBm' /\ In (qi, q, n) LB'
                   /\ 0 < q /\ q mod 16 = 0 /\ AIMG_TOP <= q /\ q + n <= aceil /\ aapp q n).
    { intros q n Hq. destruct (lbl_in_inv LBm' q n Hq) as (qi & Qi).
      assert (QiL : In (qi, q, n) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact Qi).
      pose proof (ah_blocks H HH _ _ _ _ RH QiL) as (B0 & B16 & Bn & BI & BC & BF & BA).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, B16, Bn, BI, BC, BF, BA.
      exists qi. repeat split; assumption. }
    destruct (INM p 24 (Permutation_in _ (Permutation_sym PM) (or_introl eq_refl))) as (qp & QPm & QPl & _ & _ & PIM & PCE & PAPP).
    destruct (INM bl2 (8 * bc2) (Permutation_in _ (Permutation_sym PM) (or_intror INBL))) as (qbl & QBm & QBl & _ & _ & BIM & BCE & BAPP).
    pose proof (lb_own_In LBm' m _ OWN QPm) as WRP. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in WRP.
    pose proof (lb_own_In LBm' m _ OWN QBm) as WRB. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in WRB.
    unfold AIMG_TOP in OB3, PIM, BIM.
    set (h := hmod key bc2) in *.
    assert (Hh : 0 <= h < bc2) by (subst h; unfold hmod; apply Z.mod_pos_bound; lia).
    assert (GZO : gz m obj 40) by (intros i Hi; eapply sh0_of_addressable; [exact AD | change (8 * (40 / 8)) with 40; lia]).
    assert (GZP : gz m p 24) by (intros i Hi; eapply sh0_of_addressable; [exact ADP | change (8 * (24 / 8)) with 24; lia]).
    assert (GZB : gz m bl2 (8 * bc2)) by (apply gzA; [exact (SHb BC2) | rewrite Z.mul_comm, Z_mod_mult; reflexivity]).
    assert (WRp8 : wr_at asegs m p 8) by exact (wr_at_subE m p 24 p 8 WRP ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (WRs : wr_at asegs m (obj + 16) 8) by exact (wr_at_subE m obj 40 (obj + 16) 8 WR ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (WRk : wr_at asegs m (bl2 + 8 * h) 8) by exact (wr_at_subE m bl2 (8 * bc2) (bl2 + 8 * h) 8 WRB ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold cell8 in Cb0, Cbl, Cp1.
    remember (mkR y1 (Z_to_bv 64 (spf spz)) gp tp y5 y6 y7 (Z_to_bv 64 obj) y9 (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) (Z_to_bv 64 bc2) (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key)
                  y23 (Z_to_bv 64 h) (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31) as R eqn:HR0.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    destruct ents2 as [|[fn [k1 v1]] rest].
    - pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc2; Z_to_bv 64 h;
                          Z_to_bv 64 bl2; Z_to_bv 64 0; Z_to_bv 64 0]).
      assert (HR : regs_ok E srI R).
      { unfold srI. apply regs_ok_srs; [apply regs_ok_seed|].
        repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; unfold shEe, rShe; evs;
                  rewrite ?w_add by lia; first [reflexivity | rewrite (LbB_HEmpS.srl3_val obj) by lia; reflexivity]] |]).
        apply Forall_nil. }
      assert (Rdb : sc_denot ASEGS m E (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 36)) (EVar 37)) 0) 8 false (EVar 38))).
      { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cb0); [cbn; lia | evs; rewrite w_mul, w_add, v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
      assert (Flb : sc_denot ASEGS m E (SCFlat (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 36)) (EVar 37)) 0) (ELit 8))).
      { eapply (sc_flat _ _ _ _ (8 * h + bl2)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia]. }
      assert (HK : know_ok asegs E m (kn_fix 20 [E_END] SCR_F0 E_INS srI KNF 50)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { eapply kwr_of_wr_at; [exact WRp8 | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
        apply Forall_cons. { eapply kwr_of_wr_at; [exact WRs | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
        apply Forall_cons. { eapply kwr_of_wr_at; [exact WRk | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R E_INS m (seg_rom asegs) HR HK 80%nat [E_END] SCR_F0 50%N.
      { split_scs; fsc Rdb Flb (eq_refl 0). }
      clear HK.
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      assert (MU1 : munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * h, bl2 + 8 * h + 8)] m M1).
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?w_mul, ?w_add, ?u64_of_Z by lia;
                                    cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
        apply Forall_nil. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      assert (MG1 : mem_grows m M1) by (subst M1; apply mem_denot_grows).
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
      assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
      assert (Cs1 : rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRs).
      assert (Ck1 : rw_cells asegs M1 (bl2 + 8 * h) [C8 (alu64 ALU_ADD (Z_to_bv 64 obj) (Z_to_bv 64 16))]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRk).
      rewrite w_add in Ck1 by lia.
      readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
      assert (Cn1 : rw_cells asegs M1 p [C8 (Z_to_bv 64 0)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRp8).
      rreg HR' 10%bv G10. rreg HR' 18%bv G18. rreg HR' 26%bv G26.
      rewrite w_add in G18 by lia.
      assert (G26' : getr R' 26%bv = rShe (Z_to_bv 64 (obj + 24))) by (rewrite G26; unfold rShe; rewrite w_add by lia; reflexivity).
      rewrite G10, G18, G26' in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply (front_post H HH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
                s msF1 mo1 m M1 F fc) with (W := [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * h, bl2 + 8 * h + 8)]) (ents2 := []);
        [ exact VIS1 | exact FRZ | exact KR1 | | exact MU1 | exact WM1 | exact MG1 | exact MI1 | exact ST1 | | exact Cn1 | exact Cs1 | ].
      + destruct IP as (MPx & IPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact IPr].
      + apply Forall_cons; [left; reflexivity|]. apply Forall_cons; [right; left; reflexivity|].
        apply Forall_cons; [right; right; cbn; lia | apply Forall_nil].
      + intros i Hi. destruct (Z.eq_dec i h) as [->|Hne].
        * exists (obj + 16). split.
          -- exact (cellw8_of_rw_cells M1 (bl2 + 8 * h) (obj + 16) Ck1 ltac:(lia) ltac:(lia)).
          -- right; right. split; [reflexivity|]. split; [discriminate|]. reflexivity.
        * destruct (u_bkt U2 i Hi) as (b' & Cb' & Hok'). exists b'. split.
          -- eapply cellw_agree; [exact Cb' | | lia | cbn; lia]. intros j Hj.
             unfold apart in PBL, Hblo. apply MU1. rewrite u64_of_Z by lia. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I].
          -- destruct Hok' as [H0 | [Hn | (Hs & Hne' & Hi')]]; [left; exact H0 | cbn in Hn; destruct Hn | exfalso; apply Hne'; reflexivity].
    - destruct (u_node U2 fn k1 v1 (or_introl eq_refl)) as (_ & Fn0 & Fn1 & Fn16 & Ck & _ & K1R & _ & FnO & FnB).
      specialize (FnB BC2).
      assert (INF : In (fn, 24) (umap_blocks 24 bl2 bc2 ((fn, (k1, v1)) :: rest)))
        by (unfold umap_blocks; apply in_app_iff; right; left; reflexivity).
      pose proof (PA fn 24 INF) as PFN.
      assert (GZF : gz m fn 24)
        by (intros i Hi; eapply sh0_of_addressable; [exact (SHn fn k1 v1 (or_introl eq_refl)) | change (8 * (24 / 8)) with 24; lia]).
      unfold cell8 in Ck.
      pose proof (bseq_land_boundE bc2 (u_bseq U2)) as LB2.
      set (idx2 := hmod k1 bc2).
      assert (IDX2 : 0 <= idx2 < bc2) by (subst idx2; unfold hmod; apply Z.mod_pos_bound; lia).
      pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc2; Z_to_bv 64 h;
                          Z_to_bv 64 bl2; Z_to_bv 64 0; Z_to_bv 64 fn; Z_to_bv 64 k1]).
      assert (HR : regs_ok E srI R).
      { unfold srI. apply regs_ok_srs; [apply regs_ok_seed|].
        repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; unfold shEe, rShe; evs;
                  rewrite ?w_add by lia; first [reflexivity | rewrite (LbB_HEmpS.srl3_val obj) by lia; reflexivity]] |]).
        apply Forall_nil. }
      assert (Rdb : sc_denot ASEGS m E (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 36)) (EVar 37)) 0) 8 false (EVar 38))).
      { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cb0); [cbn; lia | evs; rewrite w_mul, w_add, v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
      assert (Flb : sc_denot ASEGS m E (SCFlat (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 36)) (EVar 37)) 0) (ELit 8))).
      { eapply (sc_flat _ _ _ _ (8 * h + bl2)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia]. }
      destruct (bseq_pow2E bc2 (u_bseq U2) BC2) as [(Hb2 & Hl0) | (Hb3 & Hl1)].
      + assert (LAND : Z.land bc2 (bc2 + -1) = 0) by (replace (bc2 + -1) with (bc2 - 1) by lia; exact Hl0).
        assert (HV : Z.land k1 (bc2 + -1) = idx2) by (subst idx2; unfold hmod; rewrite Hb2; change (2 + -1) with 1; apply land_1E).
        assert (HK : know_ok asegs E m (kn_fix 20 [E_J2] SCR_F2 E_INS srI KNF 50)).
        { kn_eval. unfold know_ok.
          apply Forall_cons. { eapply kwr_of_wr_at; [exact WRp8 | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
          apply Forall_cons. { eapply kwr_of_wr_at; [exact WRs | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
          apply Forall_cons. { eapply kwr_of_wr_at; [exact WRk | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
          do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
          know_tac. }
        xrun_at (PropExec.mkFP F fc) asegs R E_INS m (seg_rom asegs) HR HK 100%nat [E_J2] SCR_F2 50%N.
        { split_scs; fsc Rdb Flb HV. }
        clear HK.
        lazymatch type of Hlf with log_flat _ ?lg =>
          lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
            change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
        assert (MU1 : munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * h, bl2 + 8 * h + 8)] m M1).
        { subst M1. apply munch_mem_denot; [exact Hlf|].
          repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?w_mul, ?w_add, ?u64_of_Z by lia;
                                      cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
          apply Forall_nil. }
        assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
        assert (MG1 : mem_grows m M1) by (subst M1; apply mem_denot_grows).
        assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
        assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
        assert (Cs1 : rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRs).
        assert (Ck1 : rw_cells asegs M1 (bl2 + 8 * h) [C8 (alu64 ALU_ADD (Z_to_bv 64 obj) (Z_to_bv 64 16))]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRk).
        rewrite w_add in Ck1 by lia.
        readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
        assert (Cn1 : rw_cells asegs M1 p [C8 (Z_to_bv 64 fn)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRp8).
        rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 13%bv G13. rreg HR' 18%bv G18. rreg HR' 19%bv G19. rreg HR' 26%bv G26.
        assert (G11' : getr R' 11%bv = Z_to_bv 64 idx2) by (rewrite G11; rewrite w_addm, w_and by lia; rewrite HV; reflexivity).
        assert (G19' : getr R' 19%bv = Z_to_bv 64 SHBASE) by (rewrite G19; reflexivity).
        rewrite w_add in G18 by lia.
        assert (G26' : getr R' 26%bv = rShe (Z_to_bv 64 (obj + 24))) by (rewrite G26; unfold rShe; rewrite w_add by lia; reflexivity).
        rewrite G10, G11', G13, G18, G19', G26' in HRe.
        eapply (front_j2 H HH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
                  s msF mo m M1 F fc R R');
          [ exact VIS | exact FHF | exact Hms | exact HRe | exact FRZ | exact KR | exact IP | exact MU1 | exact WM1 | exact MG1
          | exact ST1 | exact Cn1 | exact Cs1 | exact Ck1 ].
      + assert (LANDNZ : Z.land bc2 (bc2 + -1) <> 0) by (replace (bc2 + -1) with (bc2 - 1) by lia; exact Hl1).
        destruct (Z_lt_le_dec k1 bc2) as [Hlt | Hge].
        * assert (HV : k1 = idx2) by (subst idx2; unfold hmod; rewrite Z.mod_small by lia; reflexivity).
          assert (HK : know_ok asegs E m (kn_fix 20 [E_J2] SCR_F3 E_INS srI KNF 50)).
          { kn_eval. unfold know_ok.
            apply Forall_cons. { eapply kwr_of_wr_at; [exact WRp8 | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
            apply Forall_cons. { eapply kwr_of_wr_at; [exact WRs | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
            apply Forall_cons. { eapply kwr_of_wr_at; [exact WRk | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
            do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
            know_tac. }
          xrun_at (PropExec.mkFP F fc) asegs R E_INS m (seg_rom asegs) HR HK 100%nat [E_J2] SCR_F3 50%N.
          { split_scs; fsc Rdb Flb (eq_refl 0). }
          clear HK.
          lazymatch type of Hlf with log_flat _ ?lg =>
            lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
              change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
          assert (MU1 : munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * h, bl2 + 8 * h + 8)] m M1).
          { subst M1. apply munch_mem_denot; [exact Hlf|].
            repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?w_mul, ?w_add, ?u64_of_Z by lia;
                                        cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
            apply Forall_nil. }
          assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
          assert (MG1 : mem_grows m M1) by (subst M1; apply mem_denot_grows).
          assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
          assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
          assert (Cs1 : rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRs).
          assert (Ck1 : rw_cells asegs M1 (bl2 + 8 * h) [C8 (alu64 ALU_ADD (Z_to_bv 64 obj) (Z_to_bv 64 16))]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRk).
          rewrite w_add in Ck1 by lia.
          readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
          assert (Cn1 : rw_cells asegs M1 p [C8 (Z_to_bv 64 fn)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRp8).
          rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 13%bv G13. rreg HR' 18%bv G18. rreg HR' 19%bv G19. rreg HR' 26%bv G26.
          assert (G11' : getr R' 11%bv = Z_to_bv 64 idx2) by (rewrite G11, HV; reflexivity).
          assert (G19' : getr R' 19%bv = Z_to_bv 64 SHBASE) by (rewrite G19; reflexivity).
          rewrite w_add in G18 by lia.
          assert (G26' : getr R' 26%bv = rShe (Z_to_bv 64 (obj + 24))) by (rewrite G26; unfold rShe; rewrite w_add by lia; reflexivity).
          rewrite G10, G11', G13, G18, G19', G26' in HRe.
          eapply (front_j2 H HH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
                    s msF mo m M1 F fc R R');
            [ exact VIS | exact FHF | exact Hms | exact HRe | exact FRZ | exact KR | exact IP | exact MU1 | exact WM1 | exact MG1
            | exact ST1 | exact Cn1 | exact Cs1 | exact Ck1 ].
        * assert (HV : k1 mod bc2 = idx2) by reflexivity.
          assert (HK : know_ok asegs E m (kn_fix 20 [E_J2] SCR_F4 E_INS srI KNF 50)).
          { kn_eval. unfold know_ok.
            apply Forall_cons. { eapply kwr_of_wr_at; [exact WRp8 | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
            apply Forall_cons. { eapply kwr_of_wr_at; [exact WRs | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
            apply Forall_cons. { eapply kwr_of_wr_at; [exact WRk | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
            do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
            know_tac. }
          xrun_at (PropExec.mkFP F fc) asegs R E_INS m (seg_rom asegs) HR HK 100%nat [E_J2] SCR_F4 50%N.
          { split_scs; fsc Rdb Flb HV. }
          clear HK.
          lazymatch type of Hlf with log_flat _ ?lg =>
            lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
              change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
          assert (MU1 : munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * h, bl2 + 8 * h + 8)] m M1).
          { subst M1. apply munch_mem_denot; [exact Hlf|].
            repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?w_mul, ?w_add, ?u64_of_Z by lia;
                                        cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
            apply Forall_nil. }
          assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
          assert (MG1 : mem_grows m M1) by (subst M1; apply mem_denot_grows).
          assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
          assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
          assert (Cs1 : rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRs).
          assert (Ck1 : rw_cells asegs M1 (bl2 + 8 * h) [C8 (alu64 ALU_ADD (Z_to_bv 64 obj) (Z_to_bv 64 16))]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRk).
          rewrite w_add in Ck1 by lia.
          readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
          assert (Cn1 : rw_cells asegs M1 p [C8 (Z_to_bv 64 fn)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRp8).
          rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 13%bv G13. rreg HR' 18%bv G18. rreg HR' 19%bv G19. rreg HR' 26%bv G26.
          assert (G11' : getr R' 11%bv = Z_to_bv 64 idx2) by (rewrite G11; rewrite w_remu by lia; rewrite HV; reflexivity).
          assert (G19' : getr R' 19%bv = Z_to_bv 64 SHBASE) by (rewrite G19; reflexivity).
          rewrite w_add in G18 by lia.
          assert (G26' : getr R' 26%bv = rShe (Z_to_bv 64 (obj + 24))) by (rewrite G26; unfold rShe; rewrite w_add by lia; reflexivity).
          rewrite G10, G11', G13, G18, G19', G26' in HRe.
          eapply (front_j2 H HH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
                    s msF mo m M1 F fc R R');
            [ exact VIS | exact FHF | exact Hms | exact HRe | exact FRZ | exact KR | exact IP | exact MU1 | exact WM1 | exact MG1
            | exact ST1 | exact Cn1 | exact Cs1 | exact Ck1 ].
  Qed.

  Lemma stage_ins : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (ents2 : list (Z * (Z * Z))) (rehashed : bool),
    ISTATEx msF s m F fc y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 p bc2 ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ents2 rehashed ->
    as_SR H QIx (mkCfg msF mo).
  Proof using All.
    intros s msF mo m F fc y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
      errv' LB' LBm' p bl2 bc2 ents2 rehashed VIS FRZ KR IP.
    pose proof IP as IP0.
    destruct IP0 as (MP & FR & SP16 & SPL & SPH & RAE & MI & ST & ERR & RA & TPV & ACL & LFO & U2 & SH2 & PERM2 & BC2 & LOAD & KR32 & _).
    pose proof (LbB_HFind.BSEQ_boundA bc2 (u_bseq U2)) as BCR.
    assert (Hh : 0 <= hmod key bc2 < bc2) by (unfold hmod; apply Z.mod_pos_bound; lia).
    destruct (u_bkt U2 (hmod key bc2) Hh) as (b & Cb & Hok).
    destruct (Z.eq_dec b 0) as [Hb0 | Hbnz].
    - subst b. exact (stage_ins_front s msF mo m F fc y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
                        errv' LB' LBm' p bl2 bc2 ents2 rehashed VIS FRZ KR IP Cb).
    - exact (stage_ins_pn H HH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
               s msF mo m F fc y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
               errv' LB' LBm' p bl2 bc2 ents2 rehashed b VIS FRZ KR IP Cb Hok Hbnz).
  Qed.
End EmpI4.
