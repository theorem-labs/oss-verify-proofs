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
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_HEmpS LbB_HEmpK LbB_HEmpD LbB_HEmpI LbB_HEmpI2 LbB_HEmpI3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_HEmpI4 () := "C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockI46Stdlib7Sorting;Permutation;Permutation00C46Stdlib5Lists4List8nil_consC46Stdlib7Sorting;Permutation>Permutation_inC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI6ISTATEC4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI4IPREK47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4hmodC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell8C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_MPRESC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD5FRAMEC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3powC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD3spfC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes4list01C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt>map_live_frameC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6nval24K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7ZlengthC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5apartK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9bseq_nextC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_ALC56Stdlib6ZArith6BinInt1Z3mulC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface3ICMC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI2QIC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB3lblC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;as_rauxv_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC46Stdlib5Lists4List2InC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_RHEAPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own6lb_ownC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep5xpresC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_RFSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack06stack0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD9obj_placeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBI47Corelib4Init5Logic3and00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_hiC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_bl_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_bl_hiC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_bl_objC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HFind;BSEQ_boundAC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5u_hdrI5ARocqVerifyHarness?AgentSubmission7LibHash4HRep3hdr00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7definedC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3aC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3cC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:in_app_iffK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3notK47Corelib4Init5Logic2or01C46Stdlib7Sorting;Permutation?Permutation_symK47Corelib4Init5Logic2or02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB:lbl_in_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own9lb_own_InC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_sizeC46Stdlib5Lists4List9in_or_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap9ah_blocksC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ablock_rangeK46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z7compareC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvBsh0_of_addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit2gzC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI3gzAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI<cells4_splitC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells8cells_atC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD:wr_at_subEK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3subC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD4rSheC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD4shEeC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedK45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC47Corelib4Init5Logic9False_indC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS8srl3_valC47Corelib4Init5Logic6eq_symK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01C56Stdlib6NArith6BinNat1N2leC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz07C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_mulC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib=sc_read_cellwK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond06C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib7sc_flatK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6kn_fixC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3sh0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8kshadow0C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond03C56Stdlib6ZArith6BinInt1Z3eqbK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit:div8_boundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit9estart_shC4ARocqVerifyHarness?AgentSubmission8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotK4ARocqVerifyHarness?AgentSubmission8PropExec7FPState01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26e_addrC5ARocqVerifyHarness?AgentSubmission8SymExec33SX27e_widthC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame6insideC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?munch_mem_denotC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells6cbytesC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes6option00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge9rfull_mkRC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge;msteps_fullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call=regs_keep_mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge>msteps_mem_invC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>ah_mpres_transK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S?mem_denot_growsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv=stk_mem_denotC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKitBcellw8_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5hdkeyK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5u_bktC56Stdlib6ZArith6BinInt1Z4of_NC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame7outsideC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts8agree_onC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts;cellw_agreeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI2:front_postC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT9sr_blk_eqC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI3@bseq_land_boundEC56Stdlib6ZArith6BinInt1Z4landC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI3:bseq_pow2EC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5br_neC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_andK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6w_addmC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5br_eqC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI37land_1EC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI38front_j2C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC4ELinuxProcessSemantics5Riscv3Sem<branch_takenC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6br_ltuC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z6ltb_geC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6w_remuI5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5umapx00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep;umap_blocksC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC56Stdlib6ZArith6BinInt1Z2geC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt7umap_shC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_bseqC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6hdaddrC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell4C5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3bK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C47Corelib4Init9Datatypes3sndC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6reg_evK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01K46Stdlib9micromega7EnvRing5PExpr07C35stdpp7tactics<f_equal_helpK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8v_addi_ZC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26adenotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<kwr_of_wr_atK46Stdlib9micromega5Tauto8GFormula06I4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib5Lists7ListDef6Forall00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvDrw_cells_mem_denot_wC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9bucket_okC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_nodeC4ARocqVerifyHarness?AgentSubmission8LibIface4liveI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4AC_AC5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4LY_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4MI_AI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init5Logic4True01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith4Znat3N2Z6inj_leK4ELinuxProcessSemantics5Riscv5Instr5mulop01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI5E_INSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI3srII47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes3nat00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI33LGFK4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ARocqVerifyHarness?AgentSubmission8LibIface3memK47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3ATPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8AFS_SIZEI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD5E_ENDC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI24E_J2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI36SCR_F0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI33KNFK47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI36SCR_F2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI36SCR_F3K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI36SCR_F4K4ELinuxProcessSemantics5Riscv5Instr5mulop08c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HEmpI4?stage_ins_frontC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI<stage_ins_pn".
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
