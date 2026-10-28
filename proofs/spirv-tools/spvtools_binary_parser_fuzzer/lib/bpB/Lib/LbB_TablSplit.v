(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_Own LbB_TablStmt LbB_TablLO.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_TablSplit () := "C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6shiftrI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions@Z_to_bv_unsignedC35stdpp7tactics<f_equal_helpK46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow:accessibleI47Corelib4Init9Datatypes6option00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3mrdC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2b8K47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7byte_okI47Corelib4Init5Logic2ex00C47Corelib4Init5Logic5proj1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_RGlAshk_of_accessibleC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3shkI47Corelib4Init5Logic2or00C4ARocqVerifyHarness?AgentSubmission8PropExec3rdnC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3memC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsC5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC4ELinuxProcessSemantics5Riscv3Sem5alu64K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_andK4ELinuxProcessSemantics5Riscv5Instr5aluop0:C5ARocqVerifyHarness?AgentSubmission7LibTabl7TablLib2sxC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_andC45stdpp9bitvector;definitions8bv_swrapC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3subC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLiaTuning9zify_doneK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission7LibTabl7TablLib9low32_litC5ARocqVerifyHarness?AgentSubmission7LibTabl7TablLib8low32_sxC45stdpp9bitvector;definitions?bv_and_unsignedC45stdpp9bitvector;definitions9bv_shiftrC45stdpp9bitvector;definitionsBbv_shiftr_unsignedC45stdpp9bitvector;definitions>bv_sign_extendC45stdpp9bitvector;definitionsGbv_sign_extend_unsignedC4ELinuxProcessSemantics5Riscv7Prelude4sextK4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt5sx32AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt7tl_cellC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9aconst_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMStateCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symc6ARocqVerifyHarness?AgentSubmission3bpB3Lib=LbB_TablSplit9shk_cell2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt7tl_postC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge9rfull_mkRK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedK45stdpp9bitvector;definitions2bv01C4ARocqVerifyHarness?AgentSubmission8PropExec4getrC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z4of_NK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01C56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst=ACONST_shbaseC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2wzK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvAkword_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv:kwr_of_stkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<kwr_of_wr_atC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okc6ARocqVerifyHarness?AgentSubmission3bpB3Lib=LbB_TablSplit6osp_shK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03C5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit7kshadowC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3sh0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8kshadow0K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr04C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission7LibTabl7TablLib5br_ltC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addc6ARocqVerifyHarness?AgentSubmission3bpB3Lib=LbB_TablSplit6w_and7K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond01C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00K4ARocqVerifyHarness?AgentSubmission8PropExec7FPState01C4ARocqVerifyHarness?AgentSubmission8PropExec4mkstC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond03C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit:div8_boundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit9estart_shC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotc6ARocqVerifyHarness?AgentSubmission3bpB3Lib=LbB_TablSplit7osp_scrK5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib7syms_idC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib=syms_id_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26e_addrC5ARocqVerifyHarness?AgentSubmission8SymExec33SX27e_widthC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame6insideC46Stdlib9micromega;ZifyClasses8or_morphC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?munch_mem_denotC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge>msteps_mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv=stk_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst>aconst_ok_highC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst<ACONST_frameK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell03C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z9mod_smallC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec=bv_wrap64_modc6ARocqVerifyHarness?AgentSubmission3bpB3Lib=LbB_TablSplit7T16_valC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3le2C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells6cbytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv@rw_cells_log_nthC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib=LbB_TablSplit7le2_modC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge;msteps_fullC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge8rfull_eqC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec6v_addiC45stdpp9bitvector;definitions6bv_notC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState6ret_pcC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState;ret_pc_foldC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitions6bv_addC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec9b_addsextK4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv7Prelude4tree01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib8BtepFast8sf_congTK4ELinuxProcessSemantics5Riscv7Prelude4tree02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec8evt_doneC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib8BtepFast;sf_evt_stepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge7mkst_MSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge=evt_of_mstepsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmtBopcode_split_stmtAC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec3evtC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6reg_evC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics5Riscv3Sem<branch_takenC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_RGl7kept_inI4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call6inb_InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt8TL_STACKI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib=LbB_TablSplit6OSP_SRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst;AGOT_SHBASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst<ASHBASE_CELLI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_lec6ARocqVerifyHarness?AgentSubmission3bpB3Lib=LbB_TablSplit7OSP_KN0K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_TablLO3KCSI5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt?AT_OPCODE_SPLITI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ARocqVerifyHarness?AgentSubmission8LibIface3memI5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idK47Corelib4Init9Datatypes:comparison02I47Corelib7Numbers7BinNums8positive00K47Corelib4Init9Datatypes:comparison03K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes4bool02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs<ASHADOW_BASEC46Stdlib9micromega8ZifyInst7Inj_Z_ZI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib=LbB_TablSplit7OSP_RETI46Stdlib5Lists4List6Exists00K47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC4ELinuxProcessSemantics5Riscv3Sem2w1C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState6w1_litI4ELinuxProcessSemantics5Riscv5Instr5instr00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition OSP_RET : Z := 0xfda74.

Lemma le2_mod : forall a b, a mod 2 ^ 16 = b mod 2 ^ 16 -> Z_to_le_bytes 2 a = Z_to_le_bytes 2 b.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_TablSplit ()) [] "h01zh12H0h22H1h33H11h43H16h52H6h64__x1h75__x10h84__x2h94__x3h:4__x4h;4__x5h<4__x6h=4__x7h>4__x8h?4__x9h@7__arithhA4__ffhB8__varmaphC5__withD3H10hE3H12hF3H13hG3H14hH3H15hI3H17hJ3H18hK3H19hL2H2hM3H21hN3H26hO2H3hP2H4hQ2H5hR2H7hS2H8hT2H9hU2HahV6__sat1hW5__x11hX5__x12hY5__x13hZ5__x14h[2b1h\2b2h]1nh^1qh_2q0h`2q1ha2q2hb1rhc2r0hd2r1he2r2hf1Hhg3H20hh3H22hi3H23hj3H24hk3H25hl3H27hm3H28hn3H29ho6__sat0hp6__sat2hq6__sat3hr1ahs1bht2q3hu2q4hv2r3hw2r4p%0p%1p&0p;1p;2p;3p;4p;8p;7p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710p8P1p1001]p4p710p8P1g002IR0p4p710p8P1p1002gp4p710p8g003_j1<Tg004Dj1YTg004bj2|Tg005?j20Tg005_j21Tg006<k10ATg006Zj1VTg007=j1yTg007]j2CTg008Cj1uTg008cj3;j2ik10GTg009Cj2pTg009cj3ATg00:=j2UTg00:Wj2GTg00;Ak30@Tg00;ej2\Tg00<Kj2QTg00<lj1}Tg00=Ej2>Tg00=bj2STg00>Ij27Tg00>ej2NTg00?LR1j2BTg00?gj2MTg00@Mj2PTg00A3j2jTg00ATj1rTg00B2j2qTg00BSj13Tg00C2k202Tg00C[j2oTg00DDj2gTg00E0k10FTg00ENk10ETg00Elk10DTg00FWj2fTg00G:k10BTg00G\j1ZTg00HAj2~Tg00Hdk20>Tg00IFk20=Tg00J2k30<Tg00JQk40;Tg00KCj2dTg00L2j8cTg00LOj2eTg00M;j2sTg00Mlk209Tg00NTk308Tg00O8j3xTg00Oaj2wTg00P^j2vTg00Q;j2kTg00QWk307Tg00R@j3ITg00Rik306Tg00SRk20:Tg00T0k405Tg00TNj4]Tg00U9j7nTg00U]k604Tg00VAj3tTg00Vdk300Tg00WGk703Tg00Wkj8aTP0k60CTg00XOR0f1R2f0R33Ap=2%<3#<p=bg00XmR49A03p=Df2R51v235A0p=81k451723'Bp=51k34p=O20203p=4B07023p=6f4R6f3R7AI0239I055I05I0p=@B06023p=JAI023p=hAI0239I05p=?AI052/e3p=R20:03p=HP0P5P2P3H05p=:P5g00YKR8g00YjR9P9g00ZJR:P0P2g00ZjR;P3C]g00[QR<Fnp=[P2P8P9P9P:P3J04p>011~03p=9At052>0003p=mP0P2g00\1P3C]p=XP2P8P9P9P:P3P<Fnp==P0P2g00\XP3C]p=_P5P8P9P9P:P2P3K03p=^At023p=WP0P5P;B00023C]p=KP6P8P9P9P:P7P5P2P8P9P9P:P3P<FnGap=EP0P2P;P3C]p>0?f6R;P8P9P9P:f5R<P6P7P8P9P9P:P5P2P3GaGap=LP;P8P9P9P:P<P8P9P9P:P6P7P5GaP2P3Gap=l1>52/v3p={1k43p=F1723,B5p=zP0P6P7P5P2P3J0Cp=T1e23,e5p=`g00]?R8#<R=#YR>%<=R?#<R@#<RA#YRB'|RC,02103C'2%Y@RD,|>RE,15&0A@RF#VRG#yRH1CF7RI1CF3%uGRJ5;GRK5;G1CF5RL1p5DS00,CF=;GJ5;G3AX00112E117E,CF=;GJ9;GIA;GLK5AHX00PHPH1iGL1CF2RK,iG%<A#bS01#<RA#YRE,15S02,CFRM=;GJ112E,CFS03=;GJPGPH\HS04&0GGRNPNPLPKQ04\G/UNS05g00]dRK%V3RO%V2RPP1%V5?A231G751G72'2R1[1G521G53'2%V7?A52[RQ%V6?A75\1B0@523P3n2001000000120000000W\W[W]S06PQ^\P^[O^]KS07P3PFPIPL1\F7S081GFIS09,23X001\F5S0:1\F6/23X001Q7ES0;%DERI#}S0<116ES0=,>E106E586[S0>1S6ES0?174ERK10<ERO?5OE[S0@1N<ES0A17E4S0B10;ERO,7E%OO'B[S0C1M;ES0Df7RO/1E#D\IS0E1POES0Ff8RP/0E/2P\IS0G11PES0HP0f9RQ/0ES0IP01QQES0JQ0<f:R1111E,>E101ES0K38[S0L1S1ES0Mf;RR/0ERS?5SE\KS0N1NRES0OQ0Bf<RT/0ERU,7E%OU'B[S0P1MTES0Qf=RU/1ES0R#D\IS0S1PUES0Tf>RV/0ES0U/2V\IS0V11VES0WP0f?RW/0ES0XP0fAS0Y%bA#b#b#bS0Z#YRA'Q%DARX#}RYfBRZ11ZA,>A10ZA38[1SZA174AR[fCS0[/0AR\?5\A[Q0[/NA17A4R\fDS0\/0AR],7A%O]'B[Q0\/MAfES0]/1A#D\XQ0]/PAfFR]/0A/2]\X11]AP0fGR^/0AP01Q^AfHR^11^A,>A10^A38\Y1S^AfIR_/0AR`?5`A\[1N_AfJR`/0ARa,7A%Oa'B\\1M`AfKS0^/1A#D\XQ0^/PAfLRa/0A/2a\X11aAP0fMS0_/0AP0P<g00^BS0`1j4A'UP[eRbO1S0aA533AS0bPUPbO1S0cA5PPAS0dQ0]Q0`1j4E'UPKeS0eO1S0ff@Rb?5bES0gQ0_Q0eO1S0hA5^^ES0ig00^hR^%r8,q0Rcg00_TRd#3Re#3Rf#3Rg#3Rh#3Ri#3Rj#3Rk#3Rl#3Rm#4Rn'6S0j%4lRl%4iRi%4fRo,6cRp%4eRe2020dRdD@1o0ERq/JdRr%3mS0k#4RmQ0jPl%4jRj,6cS0l%4hS0m%4gRg/hp3?D@g00`3Rp'g3R16cl16ciRhPo16ceS0nPdD@Pr16cmS0oPn%4kRk16cg/ho9?jiD@/gp5Rn%u^S0p5;^3;%y^S0q%HPS0r&0F0Rm7:6%H1S0s?:;m7:5%HQS0t?:<m%HO7:77:2&0E0S0u&0D0RrPr1f0ARs1f04Rt5[r-01rS0v&0B9R9%Z8Ru#ZS0w#9Rv%Z=S0x#<#9Rw%9?Rx5ms5[rP9PrPrQ0vP9Q0x#9Ry%Z?#9S0y%9uR?5ms5[rP9Pr%9=R=,Xt,=r1f0ERz,_=,=r5^rS0zP9PrPrA[rzt-01rR{P9Pr%9@R@,Wz=Kv=DEP9Pr1~08R8,Xt,=r1_8z,=r5^rS0{P9PrPrP{P9Pr%<uRu#9S0|,WzS0}=Ky8DEP9PrA[r?xP9Pr20?8=DES0~FLFLFlFl20>r:S10P3P5g00`_R:g00a?R|'U20=35=A:|dB0<042H0;S11bAbBbCX60X80X90X:0X;0X<0X=0X>0X?0X70g00a_R|\XR:A{A16R},2O[12;}\:%F7S12?z7EP|\IR|1>ERR}=81<[A566ES13A81};\|12PQ12OP[[[[[[[^60^80^90^:0^;0^<0^=0^>0^?0^70P3P;PUQ0\fSR}Q0^fTR~P<PTQ0[P`PRPZP5P_P2fPR_fRR`OAb@b2b5b3b4bebabKbJbIb4bHbdb`bGbFbEb3bDbcb_bTbSbRb5bQbbb^bPbObLb2b1Q08Q0:'2e1GFL1dF5DTQ091dF7DTO4b1GcPHPH1iGMQ03,iGPJPJPGQ04PNPNPMQ03Q05Q06Q07P3PF117ERN,CFRGPM1\FNS071GFGS06,23X00Q02,\FS05Q0=,\F/23X00Q0;Q0>Q0?Q0@Q0AQ0CQ0DQ0EQ0FQ0GQ0HP0Q0IP0Q0JQ0LQ0MQ0NQ0OQ0PQ0QQ0SQ0TQ0VQ0WP0Q0XP01QPES0XQ0<11QE,>EQ0I58Q[S0<1SQES0IQ0KQ0K;5E\KS0K1N1ER1Q0B17ES%OS'B[RS1MRERK11TE#D\IRG1PTERL10UE/2U\IRIQ0RP0Q0UP0Q0XQ0<Q0IQ0KP1PSPKPGPLPIQ0RP0Q0UP0fO/QA11_A,>A10_A58_\Y1S_AfQRI/0ARL?5LA\[1NIA10`ARI,7A%OI'B\\1M`A11}A#D\X1P}A10~A/2~\X11~AP0fURI/0AP01QIAfVRL11LA,>A10LA38\Y1SLAfWRL/0ARY?5YA\[1NLAfXRL/0AR[,7A%O['B\\1MLAfYR\/1A#D\X1P\AfZR[/0A/2[\X11[AP0f[S0U/0AP0Q0aQ0bQ0cQ0dQ0fQ0gQ0hQ0iPIQ0eO1A5__Ef]Q0eO1A5LLEQ0k#3RL#3S0k#3R_#3RI#3RX#3RY#3RG#4RK%4XRX,6c??ji%4IRI%4_R_5?d%3GRG#3RS#4R1%4GRG,6cS0e%4LRLQ0jA?kjhD@%4Y,6cRY??_i1o0AR_%3SRS#3Rj#3#3#4'J%4j,J_1J_LQ0Z#r,q0/6n1J_lD@Pd1JqeQ0m,JqPGPYD@/gp5`d5Rd5`d5`d3R16cIPkPhPgQ0n,hoD@Q0k#4RoQ0j;?eQ0ePKPnPlQ0m9?khD@%4S16c1PoQ0oQ0l9?lkD@16cK1hXI5?1Q01#Y,o0/Jd??gi/gp,ed5Rd5`d5`d5Rd5RXQ0p5;^5;^Q0qQ0r%HT7:6Q0s%HV7:;7:5Q0t%HU7:<%HR?:Om7:77:2Q0uPr1Xtx,=r1_xs,=r5^rP9PrPrQ0vP9PrQ0w#<#9,Ws=K@xDEP9PrPrQ0vP9%Zu#9=ms?9[ryP9PrQ0zP9PrPrP{P9PrQ0y%<u#9,Wz;K=DEP9PrQ0{P9PrPrP{P9PrQ0|Q0x#Z#9,Wz;K8DEP9Pr1Xtw,=r1_wz,=r5^rP9PrPrP{P9PrQ0y,Wz=K@wDEP9Pr1Xtv,=r1_vz,=r5^rP9PrPrP{P9PrQ0}=KyvDEP9Q0~FLFLFLFLFlFLQ10Q11bAbBbCX60X80X90X:0X;0X<0X=0X>0X?0X70XW0XX0XY0XZ0Q12?z7AA{AW<RA,2Q\:12OA\:Q131>EbR:=8U;\|A5<<EQ0Y,>ERA=8TO\|Q0gA8bAZ\|A5WWEQ0Y98W:\|12UV12TU[[[[[[[[[[[[^60^80^90^:0^;0^<0^=0^>0^?0^70^W0^X0^Y0^Z0P3PPPWP]Q0_P}P~fcP[Q0UfdPOPVQ0]PaP;PUQ0\P6Q0^P7P`P5P\P2f`fbOJb@b2b5b3b4bMbNbwbubnbmblbNbkbvbtbjbibhbMbgbebabKbJbIb4bHbdb`bGbFbEb3bDbcb_bTbSbRb5bQbbb^bPbObLb2b1Q07Q05'2e1GFMQ02,dFDTQ061dFNDTO4b1Gc1UHJGcGc1p2D1s2C%F2%FCRJ107C#F[[1s7CQ1210<C#F\J[209>B174>R<%FB174C[RC[%F>R7g00b<RNB08>B2UWUPJ\N^U7P2Q0`1j4>'UP<eO1PCQ0pQ0qPmQ0u1f0D,Xt,=rQ10Q11bAbBbC%FDP3b@bVbobVbpbqR39x2DDTQ00Ax5D3DT1wf51wf25AHeWfXs0Xr0o"). Qed.

Lemma shk_cell2 : forall M a, accessible M a 2 -> a mod 2 = 0 ->
  exists v, shk M a v /\ 0 <= v < 8 /\ (v = 0 \/ a mod 8 + 2 <= v).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_TablSplit ()) [] "p'0h02H0h11vh24__x1h33H10h42H5h54__x2h64__x3h74__x4h84__x5h94__x6h:4__x7h;1Hh<3Horh=7__arithh>4__ffh?8__varmaph@5__withA2H1hB3H11hC3H12hD3H13hE2H2hF2H3hG2H4hH2H6hI2H7hJ2H8hK2H9hL4__p1hM4__p2hN4__x8hO1qhP2q0hQ2q1hR1rhS2r0hT2r1hU2A2hV2HvhW1KhX1MhY6__sat3hZ1ah[1eh\1xi001xh]1zp%0p&0p;1p;3p;2p;4p;6p;7p;8g003_j1ETg004Dj1_Tg00bXk30>Tg005?j21Tg00P^j20Tg00Q;j26Tg006<j1iTg006Zk100Tg00cWj1fTg00d9j1xTg00e0k10HTg00egk30ETg00f_k10DTg00gVj2sTg009cj3PTg00h8k20BTg00i4R0j2WTg00?LR1j25Tg00iNk30=Tg00M;k30<Tg008Cj1mTg007=j1lTg00ENk109Tg00Elk105Tg00HAj2hTg00FWj2]Tg00Hdj2yTg00:=j2`Tg00IFj2wTg00J2j3vTg00JQk40GTg00iik60FTg00joj3;Tg00kgS00j29Tg00<Kj2STg00<lj1tTg005_j22Tg00=bj2QTg00>Ij24Tg00>ej2TTg00?gj2OTg00@Mj2LTg00A3j2rTg00BSj1<Tg00ATk10@Tg00B2k20?Tg00C[j2qTg00C2j2pTg00Rij3oTg00DDj2cTg00LOj2YTg008cj3\Tg00G:k10;Tg00G\j1aTg007]j2jTg00lAk408Tg00m2k607Tg00mNk304Tg00E0k103Tg00mhk302Tg00nBj4gTg00n]k406Tg00SRk201Tg00Vdk30:Tg00TNj4[Tg00U9j7bTg00WGj7~Tg00=Ej2}Tg00QWj3|Tg00R@j3dTg00T0k40ATg00U]j6{Tg00VAk30CTg00Wkj8eTg00o7j6zTg00XOR2f0R3g00XmR43Pp=31643p=Kf2R5f1R6/43'5p=I1563,55p=A20123p=JB0:263p=:P2P6g00\1P3C[p=VP6g00YKR7g00YjR8P8g00ZJR9P3g00[QR:Fbp=?P2P6g00\XP3C[p=ZP5P7P8P8P9P6P3F~p=U1156/43p=B16451463'5p=71963,55p=uf3R;1}56/035P2p=81634p=MAP263p=@1p23p==A|263p=NAd2639d25p=>Ad263p=XP2P5P6P3H0Ap=FP5P7P8P8P9P2P6g00ZjR<P3C[P:Fbp=^P6P7P8P8P9P3E{p=n1h23p=CB0C263p=GP2P6P<P3C[p=Hf4R<P7P8P8P9P;P5P6P7P8P8P9P3P:FbGep=Df6R:P7P8P8P9f5R=P<P;P7P8P8P9P5P6P3GeGep=RP6P7P8P8P9P3Ezp=kg00o[g00]?R7#ER>#_R?:0>63116?#3P;P5P?%_7R@,05P6%K5RA105?g010S'616;310;?7I3%K3RB%E>RC#ERD#_RE7I3RF%iDS01$00RG#fg011O%x5$0H80E:&0D3,sG3P20B353AX12,W2[^\2'5<0=6PAB0<;?3%K?11<?#K[g00^hRA#mRH%lAS02%J6&092S03&052RI1h27RJ1]2@RK,:JRL'V,?I1]2?RM,:JS04,ZL,?I3U1yI9S05P3P5g00`_R9g00a?RL'`1w35=P9LdAv246H0GS06b>b?b@X22103@RL,63103?7IL^22P3P=O1b=bYb0J0F10;@RL=;<3%33R9ABLE3'97AFX12,W2P0P210<@R0=;=3AB0E3,997AFX12A;:=311=E/0?/63,997AFX12,W2P3f7R010:@RL;;3ABLE3,997AFP1f8RL100@RN;;6A766E%36ABNE63uf:ROf9RP;;311PE/0?/63,997AFX12,W2P310P@=;O;%K<S07?I<E%3<10O@?BE<3uP1A7==E%3=f;R1/0@?BE='9f>RQf=RR;;311RE/0?/63,997AFX12,W2P3A700ERS%3LS0810Q@?BEL'9P2fARQf@RT;;311TE/0?S09/63,997AFX12PPf?RF=;TPS0:A7PPES0;%3PS0<11FE/0?/6P'9S0='510F@R9/SE%3ERU#tRV10T@RWPE12WES0>11WES0?C8[1QWE144ERW10Q@RX/1ERY?7YE[1TXE14E4RXfBRY/0@RZ/1ER[,4E%M['5[1OZEfCRZ/0@R[/2E#3\U1L[EfDR[/0@R\/1E/@\\U12\EP2fER\/0@/1EP2fFR]/SEfGR^PE12^E11^ES0@C8\V1Q^EfHR^/1ER_?7_E\W1T^EfIR_/1ER`,4E%M`'5\X1O_EfJR`/2E#3\U1L`EfKRa/1E/@a\U12aEP2fLS0A/1EP2fMS0B/S?%3?Rb#tS0CfNRcP?12c?11c?C8[1Qc?144?RdfORe/1?Rf?7f?[1Te?14?4S0DfPRf/1?Rg,4?%Mg'5[1Of?fQRh/2?#3\b1Lh?fRRi/1?Rj/@i\b12i?P2fSRk/1?P2P=g00^BRl1r4?'`PdeO1S0EAIB3?S0FPR1r4E,`lPWeRlO1S0GA7LLES0HP\PlO1S0IA7TTES0Jg00_TRl#<RR#<RB#<Rm#<S0K#<Rn#<Ro#<Rp#=Rq&0@7-0?2Rr%=nRn'N%=mRm%=BRB1q2E1p2lRl5o2S0L3>3>g00`3Rs'c%<pRp#=Rt,Nr%=oRo%=RRu,NrRv,Xn3>%<p#=1Nrm/XB7>n%_C,q2=o2B9>ul/cs'Y'Y=\AH5\AQ02%J<%J:Rp7F5%J=%J07F;Rw7F6Q03PIPI1]24R49^IM,nIS0M&0;8R8PI%CCRC%a7R7#a#CRx,GM%C7Ry':'HDDP8PI%E7#CR7,V4,?I1]2ERz,Z7,?I5UIP8PIPIA^Iz4,nIR{P8PI%C>R|,Gz/:7,HCDDP8PI%a>#CR>,V4,?I1Z>z,?I5UIP8PIPIP{P8PI1:CK1GzJ/:>'HDDP8PIA^Iy4S0NP8A^IJ|FRFRFRQ05Q06b>b?b@X22X52X62X72X82X92X:2g00a_R}\bR~P<P?P0P;C8[A7::EP}\UR}P:PEP<PLC8[10L@PEP=PPC8\}%301@:0[[\S[[[^22^52^62^72^82^92^:2P3P=P1PYfXS0OP<f<RSPZPOP5PQP6P^fVO=b=b0b4b3bTbQbDbCbBb3bKbSbPbJbIbHb4bGbRbObFbEbAb0b;129E12FE'@P2Q0>%lGRF#fg012FPY%ED#E#E#ig013d,03'jPRH08Q01/j1%mG5\G,sF3PX]2P:12TEP3J07b0Q0:eQ0;Q0=P6Q00Q0<AB9EP%3OR9Q09/6O'9P3%31RT11QE/0?/61RF<043X<9P3O1Q0?/4O1SQEPYPE12YE11YEC8\V1QYE11ZER9?79E\W1TZE11[ER9,4E%M9'5\X1O[E12\E#3\U1L\E11]E/@]\U12]EP2Q0@P210^@/SE10_@R]PE12]E11]EC8\V1Q]E10`@R`/1ER]?7]E\W1T`E10a@Ra/1ER`,4E%M`'5\X1OaEQ0A/0@Ra/2E#3\U1LaEQ0B/0@Ra/1E/@a\U12aEP210c@/1EP21Se?Q0CPfP?12f?PgC8[1Qf?11h?Rf?7f?\d1Th?Q0D14?j%Mj'5[1Oi?12k?#3\b1Lk?fTRk/1?/@k\b12k?P2fU/1?P2Q0EQ0FQ0GQ0HQ0IQ0Jp-0Rb1NrqQ0K#=1Xmv3>1NroRo/XB9>tq1XulQ0LA>onm7>t/cs'Y'Y'Y=\AHQ02%JL&0327F<?F5p?F6wQ03PIPIQ0MP8PI%CD,GM/:y,H>DDP8PI1V4C,?I1kIO5UIP8PIPIP{P8PI1:>K1Gzx/:C'HDDP8PI1kI11ZJz,?I5UIP8PIPIP{P8PI1Gz7/:J,H>DDP8PI1ZC|,?IP8PIQ0NP8PIQ04/V|DDFRFRFRQ05Q06b>b?b@X22X52X62X72X82X92X:2XN2XLbWMP=P?PLP;C8\~Q07/5PPNPEPPP:C8\}AIS;EPPPEPOP=C8\}14L:Q08100?/6L[[[[[[[^22^52^62^72^82^92^:2^N2^Lb^MbP3%KY141EP=PSPZfZP1P<PkPYPOP5PQP6P^P_Q0OOAb=b0b4b3bTbQbDbCbBb3bKbSbPbJbIbHb4bGbRbObFbEbAb0b;:02TFW<P3O1n200100000021000011000CgCgH06W<WVP6P3O2n2001000000121000000W0WWP6P3O2n2001000000121000000W0X12P6P3O2n2001000000121100000b[WUW;XZ2WXo"). Qed.

Lemma w_and7 : forall a, 0 <= a < 2 ^ 64 -> alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 7) = Z_to_bv 64 (a mod 8).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_TablSplit ()) [] "h06__sat1h12Hah27__arithh34__ffh46__sat0h58__varmaph65__with74__x1h81ah91bh:1zp;1p;2p;3p;4p;6p;8p;7g003_j11Tg004Dj13Tg004bj2?Tg00>Ij24Tg00?Lj2<Tg006<j1RTg006Zj1JTg00G\j1>Tg014_j2@Tg007]j26j1]Tg005?j28Tg009cj3:Tg00:=j27Tg015=j1VTg00Mlj2UTg00NTj3TTg00A3j2STg008Cj1QTg007=j1NTg00E0j1MTg00ENj1ITg00Elj1HTg00FWj25Tg00Hdj2GTg00IFj2FTg00J2j3KTg00JQj4LTg015[j3ETg002Ij6=Tg00L2j8DTg016>j3CTg00SRj2OTg00HAj2PTg016fj3BTg00TNj4;Tg00G:j1\Tg00Wkj8[Tg017Ij4ZTg00Q;j2WTg00U9j7XTg00WGj7YTg00XmR0f0R1'Wp=0g00XOR2f1R3g00\1P1C;p=9P3g00YKR4g00YjR5P5g00ZJR6P1g00[QFXp=2f2R7P4P5P5P6P3P1FYp=A%01g00]?R8#1R9#3R:%19#1R9#1#1#1R;#3R<'?R=,41'<R>%R;R;#JR?%>8R@#>#3RA,@3RB,6;%39R9,87RC,6;9:?1X9?P2P?%];RDPDPB1839R9P?\2/7DP2%3@R@,?:,83A:21CX:21729%V@,@31U:<R9140:RC%0<140=[RD[R?%0:RBg00b<REAT:<3UW1R<%0=\E^1BRBP3g00^B1S0:'7PCeO1RCPDg00^hRE#QRF%NERE%M2RG%I2RH%H2RI1520RJ152@'9'21GI6RKP1P7g00`_RLg00a?RM'71F17=:LMdAK203CLR0b3b5b6%0@P1b2b0b4b09E3@E=GDg018@16;316;A3CP3PAP9P?P<PBPCPDPFPE1O23PHPIP4P5P5P61P28R8,9J,2IP2P8g00\XR8152:=B2;R;C;,2I5AIR:%\5P:G[PKP0b3b5b6X72%03143='<\>^72P1f5f4O2b2b0b4b0P9P?P<PBPCPDPFPEPGPH152ARH,9J,2IP2PHP8P;C;,2I5AIPKP0b3b5b6%0A14A='<P1b2b0b4b0CZE=W1X82o"). Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma T16_val : forall w, 0 <= w < 2 ^ 32 ->
  bv_unsigned (sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 (TablLib.sx w))) (low32 (Z_to_bv 64 16)))) = w / 2 ^ 16.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_TablSplit ()) [] "h06__sat1h11zh22Hah31ah47__arithh54__ffh66__sat0h78__varmaph85__with94__x1h:2zhh;1Hh<2H0h=3H12h>3H18h?2H6h@6__sat2hA6__sat3hB6__sat4hC6__sat8hD6__sat9hE4__x2hF4__x3hG4__x4hH4__x5hI4__x6hJ4__x7hK4__x8hL4__x9hM2H1hN3H10hO3H11hP3H13hQ3H14hR3H15hS3H16hT3H17hU3H19hV2H2hW3H20hX3H21hY3H22hZ2H3h[2H4h\2H5h]2H7h^2H8h_2H9h`2Hwha6__sat5hb6__sat6hc6__sat7hd1wp%0p&0p;1p;2p;3p;4p;6p;7p;8g003_j10Tg004Dj1FTg004bj2tTg006<j1}Tg018lk10:Tg007]j2hTg019cj1uTg01:Kk30QTg01;3k205Tg00;ej2<Tg005_j26Tg00:Wj2@Tg00G\j15Tg01;[k30ZTg009Cj2BTg01<@j2UTg014_j2ZTg005?j21Tg00:=j2YTg00P^j2ATg00Mlj2rTg00>Ij28Tg00NTj3pTg00M;k204Tg01<gk202Tg01=Xj2PTg00<Kj2eTg00<lj1dTg00=bj2fTg00>ej2oTg00Q;j2VTg00?Lj2XTg00?gj2nTg00@Mj2lTg01>5j2kTg00A3j2jTg00BSj12Tg00C2k20;Tg00ATj1{Tg00B2j2_Tg01?9k40WTg01?Zk30VTg00DDj2vTg01@;k30TTg00LOj2mTg008Ck10STg008ck306Tg007=k10RTg00SRj2]Tg00E0k10PTg00T0j4\Tg00ENk10OTg00Elk10MTg00FWj2qTg016fj3sTg00G:k10HTg00Vdj3aTg00VAj3iTg00HAk200Tg01@gk30GTg00Hdk20FTg00IFk20ETg009cj3cTg00J2k30DTg00JQk40BTg00O8k30CTg00m2k60ATg00KCk20@Tg01AJk20?Tg01BHk20ITg01CEk30JTg01D3k30>Tg01D[k30KTg01ELk30LTg01F9k30=Tg01Fok30<Tg00=Ek20NTg00R@j3TTg00QWk301Tg00C[k207Tg00Rij3~Tg00TNj4wTg00U9j7xTg00WGk70]Tg00U]k60\Tg00Wkj8|Tg002Ik60[Tg00XmR0f2R1'Vf1R2f0R3'8'Xp=9g00XOR4?c23p=4%53#5p=G1112/P3p>081V03p=71612/A3p=N1A12/13p>03f4R5f3R6'6/A1/12/P3p=?Ac430p=H20N12/A39c46p=I20;43p=3AT4239T41p=`B01412=T43p=^%03#0p=S%03#0#0#0#0#0#0#0p=;B01423p=W%53#0p=C%03#5p=z%F3-074p=EA~423p>0YA~412=T43p=:%03#0#0#0p>0X%53#5#5#5#5#5#5#5p=OAT423p=y20743p>0U1m23,m1p>09AT412/m3p=R20043p=DP1g00YKR7g00YjR8P8g00ZJR9P4P2g00\1P3Cwg00[QR:Fxp=>P4P2g00\XP3Cwp=LP2P7P8P8P9P3P:Fxp=MP1P7P8P8P9P2P3K0]p=KP1P7P8P8P9P4P2g00ZjP3CwP:Fxp==P2P7P8P8P9P3J0\p=gP6P7P8P8P9P1P2P3G|p=[f6R:P7P8P8P9f5R;P5P6P7P8P8P9P1P2P3G|G|p=Q1823,X1p=bP4P5P6P1P2P3J0[p=Jg00]?R7#0R<#FR=%0<R>#0S00#0R?#0R@#FRA'tRB9933S01%0@RC#}RD%}@R@g01GZ&0:2,hD#uRE%F?RF,hD#uRG40QRH+05'<S021t=FRI,61RJ,43X141@@ES03%57RK#5RL#GS04#FRM,h@RN:0Z@GRO,@@S05'B1U@3,<D/4JX141@@GS061@@NRP'ZRQ&0:1,hD#u,@@/B3,U@,<D/4JX14P21B3Q,U@,<D/4JX14PF1Z3P,B1,U@,<D/4JX141<@MS071ZF3,B1,U@,<D/4JX1411MB,ZFRQ,Y414FQP4PF1B6316B=RR'A@08BR%FCRS,t=RT'1166IRU'4X14PJ1A3R@08BR/1T/4UX141r=ARU180=RJ%7A180BRV[RW[RX%7=RYg00b<RZAp=A2UW2RA%7BR[\Z^2YR\AN5IRR]004B%7]16:I@03RBR]#7\[[202B=%7R\Y\[1P]RR]004T%7]%7TR]f8R^PIPRPBPRD?/1T#7[[1r=F%7FR_180IR`[Ra\JAp=F2VZX2Y%7IRb\Z^2Y1r=S%7S180TRc[Rd\JAp=S2VZX2YP]\Z^2Yf;RS002I%7SRef=Rf/6IRg#7\b[f<S08/eI%HIRh#dPfPIPg11fICI[1ffIf>Rg/1IRi?9iI\`1ogI18I0f?Rg/1IRi,8I1Vi0'X[1ngIf@Rg/6I#H\h1lgIfARg/1I/4g\hg01HFRi1kgIRgePg1eB=%H=Rg#dPBP=PR11B=RjCI[1fB=A9jj=Rk\J1oB=18=018=j1Vj0'X[1nB=%HR\g1lB=14jB\gPi1kB=RlePlfHPIPRPBPRD?/eT%HTRl#dfIS09PIPRPBPRD?RmPT16mT11mTCI[1fmTfJPIPRPBPRD?Rm/1TRn?9nT\c1omT18T0fKPIPRPBPRD?Rm/1TRn,8T1Vn0'X[1nmTfLPIPRPBPRD?Rm/6T#H\l1lmTfMPIPRPBPRD?Rm/1T/4m\lPi1kmTRmePmfN?NIR/eB%HBRm#dfOS0:?NIRRnPB16nB11nBCI[1fnBfPRn?NIRRo/1BRp?9pB\V1ooB18B0fQ?NIRRo/1BRp,8B1Vp0'X[1noBfR?NIRRo/6B#H\m1loBfS?NIRRo/1B/4o\mPi1koBRoePoP5g00^BRo1j0B'YPVeO1fTRV/6IRi@03RBRp?9pBPS1j0T,YoPceO1fURcPIPRPBPRD?/1TRq?9qTfB1j0=,YoPJeRJO1PkQ091j0I,YoP`eO1fW/1IR`?9`IP5PZQ0:P3P2O2X3YP]^3YPnPJO1Pdf7RdPZPVP3P2O2X3YPb^3YPcPJO1Paf:RaPZf\P3P2O2X3YP[^3Yf]PJO1PWg00^hRYg00_TR[#2RZ#2RV#2Rn#2R]#2R`#2#2Ro#2Rk#3Rq%3oRo20;4[R[%2k#2Rk#2Rr#2Rs#2Rt#2Ru#2Rv#3%3uRu%3]3`%{7,_4R]%2vRv#3Rw%3tRt%3nRn5^]3^%SC#;RC#{,_4Rx%2vRv#3'W%3kRk1W]q%3`R`3`%5<Rq#0#C#C#C#C#C#CRy#G#C#S#G#C#S#G#zRz#0#;#;#;#;#E%3ZRZ+0Y%0y#z#G#S#z#G#S#GRy#0#ER{%2vRv#2R|#2R}#3R~%Ey%{y,_4%3s'W7:u5:{7:[P4%0C#;#;R{#0#S$0X#;Rs#;#;Ry#F,_4P7Q04#5#G#O#O#O#O#O#O#O#F,_4H0W:0V4L%Ez1yZ`7:[g00`3Rz'v%2}R}#3%3|%3vRv%3rRr3`%2}#2R}#31W]u=`wr5^x&0U=Rw%E{%0y#E%2}#2#2#31W]v,y~5:w7:n7:Z7:[/vz609[3R40T,m[3R3R609[3R3R1yk[%Es%EC1W]`%3V5`o9^xr7:t9^xu7:[/vz5Rt&0SYRt606Y406&0RYRYP4P4P41]4^P5&0P4RzC\P11]4:C\P2P4P4f9R[,]4P;PzC\P61]4dC\C\&0O4Rx&0M4Ru1q40Rr%DqRq5>u1q4=Ro=s4@RV,Lq,Mu5Ku&0H8R8PuPuA=uVr,guP8%D<R<%D>R`5a4%5>#D9i4V=a4q5=uC[P8Pu20047R79>urR>As4oDR],L7,Mu5KuP8PuPuA=u]r,guP8B0G4q`Q00#D9i4]=a475=uC[P8Pu%DLRL9>ur1LLo,Mu5KuP8PuPuA=uor,guP8Ai4o`=a4L9=uVC[P8Pu%0K#DRL9>ur%}?9s4oRo,LL,Mu5KuP8PuPuA=uor,guP8%DKRKAi4o<=a4L5=uC[P8PuPuA>urKRLP8PuA>uroP8A>ur<FQP8Pu1LKV,Mu9KuLP8A=u7<FQFQFQFQFQ20Fu9R9P3P1g00`_R<g00a?RL'Y20E31=c<LdB0D402H0BR0b5b7b8X94XE4XF4XG4XH4XI4XJ4XK4XL4A955Bg00a_RL\m1A6;PBPaP:CI[A911TPL\l1P^dPTPSP5CI[%7aRd?ba=PL\gPBP=P[Q08CI[AbeSIPL\hPaPIP[PfCI[Pe\b\dAbeSB14aS[[[[[[[[[[^94^E4^F4^G4^H4^I4^J4^K4^L4P3fbRe/6IRd/ARRb/6B11bBRb/PRR[/6TPj11eIPbPRPePd11[TPffCQ08Q09PSQ0:PaPcfVfaOCb4bDbCb:bBbAb:b@b0b:b<b?b=b>1PpR/1T/4iebYbXbWbUb>bTbSbRbQbPb=bObNb_b^b]b?b\b[bZbVbMb<b;b6b0b@bAbBbabbbcbCbD1B1FPUPXPAP\P2PJO1RJPWPtPYPzPx1q4FRi9>urRrP9P0b5b7b8P_P3b4b0b6b0:0C1FDJPQP3J0Ab;Q07,ZF,B2,U@,<D162IRI'4ePP20@@MDJQ06PUPXPAP\PJPWPtPYPzPx1LiV,Mu9KurP9P0b5b7b8Ab_FBP3b4b0b6b0-0?FDJQ03PUPXPAP\PJPWPtPY1]42PxPu1L7V,Mu9Ku>R>P8P>C[P9P0b5b7b8X94Q01A922B[^94P3P;P5O2b4b0b6b0-0I2DJQ05B0J@GNDJB0>@EORN,@@B0K@EODJ205@N,<D/4IeQ02/4IeB0L@DH,@DB0=@DHDJB0<@DH,@D/4IeW`Xd4o"). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition OSP_SR : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (2%bv, EVar 35); (1%bv, EVar 36)].
Definition OSP_KN0 : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
    KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
    KWr (SA (EVar 35) (-16)) (ELit 16); KWr (SA (EVar 33) 0) (ELit 2); KWr (SA (EVar 34) 0) (ELit 2);
    KRange (EVar 35) (2 ^ 45) (2 ^ 47); KRange (EVar 33) 0x6e8000 (2 ^ 47 - 2); KRange (EVar 34) 0x6e8000 (2 ^ 47 - 2) ].

Definition osp_sh (e : expr) (vo : option expr) : list kentry :=
  match vo with
  | None => [KWord (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) 1 (ELit 0)]
  | Some ev => [KWord (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) 1 ev; KRange ev 1 7]
  end.
Definition osp_scr (w p : bool) : scripts := SCR ((if w then [true] else []) ++ (if p then [true] else [])) [] [].
Definition OSP_KA : list kentry := [KAlign (EVar 33) 2; KAlign (EVar 34) 2].
Definition OSP_LG : list sentry :=
  [SE (SA (EVar 34) 0) 2 (EVar 32); SE (SA (EVar 33) 0) 2 (EAluw ALU_SRL (EVar 32) (ELit 16));
   SE (SA (EVar 35) (-8)) 8 (EVar 36)].

Ltac osp_close E M LG R0 Hsp :=
  idtac;
  lazymatch goal with HR' : regs_ok _ _ ?R', Hms : CatSim.msteps _ _ _, Hlf : log_flat _ _ |- _ =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) => change mm with (mem_denot E M LG) in Hms end;
    exists R'; split; [exact Hms|]; split; [exact Hlf|];
    split; [intros rr Hrr; eapply (syms_id_sound R0 _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|];
    let G1 := fresh "G1" in let G2 := fresh "G2" in
    rreg HR' 1%bv G1; rreg HR' 2%bv G2; split; [exact G1 | rewrite G2; symmetry; exact Hsp]
  end.

Section Split.
  Context {HCEIL : HeapCeil}.

  Theorem opcode_split_okA : opcode_split_stmtA.
Proof.
    intros [[w pwc] pop] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC PRE.
    destruct PRE as (Hw & Ha0 & Ha1 & Ha2 & Ep & Eo & (WRp & APp & AOp & SPp & BDp) & (WRo & APo & AOo & SPo & BDo) & DJ).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr.
    unfold TL_STACK in *.
    pose proof (ACONST_shbase m AC) as [CG CS].
    assert (Hsx : 0 <= sx32A w < 2 ^ 64) by (unfold sx32A; rewrite <- TablStmts.sx32_prs; apply TablLib.sx32_range; lia).
    assert (Hlo16 : 0 <= w mod 2 ^ 16 < 2 ^ 16) by (apply Z.mod_pos_bound; lia).
    assert (Hhi16 : 0 <= w / 2 ^ 16 < 2 ^ 16) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    destruct (shk_cell2 m pwc APp Ep) as (vp & Shp & Vp & Bp).
    destruct (shk_cell2 m pop APo Eo) as (vo & Sho & Vo & Bo).
    pose (E := Eseed (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     [Z_to_bv 64 (sx32A w); Z_to_bv 64 pwc; Z_to_bv 64 pop; sp; ra; Z_to_bv 64 vp; Z_to_bv 64 vo]).
    assert (HR : regs_ok E OSP_SR (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)).
    { subst E. unfold OSP_SR. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat apply Forall_cons; try apply Forall_nil; (split; [intros X; discriminate X|]); evs;
        first [exact Ha0 | exact Ha1 | exact Ha2 | reflexivity]. }
    assert (RUN : exists R' : bvmap 5 word,
        CatSim.msteps asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AT_OPCODE_SPLIT) fc None m (seg_rom asegs))
                            (MS R' F (Z_to_bv 64 OSP_RET) fc None (mem_denot E m OSP_LG) (seg_rom asegs))
        /\ log_flat E OSP_LG /\ kept_in KCS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) R' /\ getr R' 1 = ra /\ getr R' 2 = sp).
    { destruct (Z.eq_dec vp 0) as [Zp|Np]; destruct (Z.eq_dec vo 0) as [Zo|No].
      - assert (HK : know_ok asegs E m (OSP_KN0 ++ OSP_KA ++ osp_sh (EVar 33) None ++ osp_sh (EVar 34) None)).
        { unfold know_ok, OSP_KN0, OSP_KA, osp_sh. cbn [app].
          apply Forall_cons.
          { eapply (kword_of_rw_cells asegs _ m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
          apply Forall_cons.
          { eapply (kword_of_rw_cells asegs _ m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
          apply Forall_cons.
          { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons.
          { eapply (kwr_of_wr_at asegs _ m pwc 2); [exact WRp | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
            | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons.
          { eapply (kwr_of_wr_at asegs _ m pop 2); [exact WRo | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
            | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons; [cbn [kentry_ok]; evs; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; split; [lia | exact Ep]|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; split; [lia | exact Eo]|].
          apply Forall_cons; [eapply kshadow0; [evs; reflexivity | lia | rewrite Zp in Shp; exact Shp]|].
          apply Forall_cons; [eapply kshadow0; [evs; reflexivity | lia | rewrite Zo in Sho; exact Sho]|].
          apply Forall_nil. }
        xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          AT_OPCODE_SPLIT m (seg_rom asegs) HR HK 40%nat [OSP_RET] (osp_scr false false) 39%N.
        { split_scs. all: first [ cbn [sc_denot]; evs; rewrite w_and7 by lia;
                 match goal with |- context [?x mod 8] => pose proof (Z.mod_pos_bound x 8 ltac:(lia)) end;
                 rewrite w_add by lia; rewrite br_lts_small by lia; apply Z.ltb_lt; lia
               | sc_dj
               | cbn [sc_denot]; unfold flat, estart, elenZ; evs; rewrite HWord.w_srl by lia; change (2 ^ 3) with 8;
                 rewrite ?u64_of_Z by (Z.div_mod_to_equations; lia); cbn [a_off a_base]; unfold LbB_Kit.SHBASE;
                 Z.div_mod_to_equations; lia ]. }
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m OSP_LG) in Hms end.
        exists R'. split; [exact Hms|]. split; [exact Hlf|].
        split; [intros rr Hrr; subst E; eapply (syms_id_sound _ _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
        rreg HR' 1%bv G1. rreg HR' 2%bv G2. split; [exact G1 | exact G2].
      - assert (HK : know_ok asegs E m (OSP_KN0 ++ OSP_KA ++ osp_sh (EVar 33) None ++ osp_sh (EVar 34) (Some (EVar 38)))).
        { unfold know_ok, OSP_KN0, OSP_KA, osp_sh. cbn [app].
          apply Forall_cons.
          { eapply (kword_of_rw_cells asegs _ m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
          apply Forall_cons.
          { eapply (kword_of_rw_cells asegs _ m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
          apply Forall_cons.
          { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons.
          { eapply (kwr_of_wr_at asegs _ m pwc 2); [exact WRp | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
            | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons.
          { eapply (kwr_of_wr_at asegs _ m pop 2); [exact WRo | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
            | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons; [cbn [kentry_ok]; evs; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; split; [lia | exact Ep]|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; split; [lia | exact Eo]|].
          apply Forall_cons; [eapply kshadow0; [evs; reflexivity | lia | rewrite Zp in Shp; exact Shp]|].
          apply Forall_cons; [eapply (kshadow _ _ _ pop vo); [evs; reflexivity | lia | lia | evs; reflexivity | exact Sho]|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_nil. }
        xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          AT_OPCODE_SPLIT m (seg_rom asegs) HR HK 40%nat [OSP_RET] (osp_scr false true) 39%N.
        { split_scs. all: first [ cbn [sc_denot]; evs; rewrite w_and7 by lia;
                 match goal with |- context [?x mod 8] => pose proof (Z.mod_pos_bound x 8 ltac:(lia)) end;
                 rewrite w_add by lia; rewrite br_lts_small by lia; apply Z.ltb_lt; lia
               | sc_dj
               | cbn [sc_denot]; unfold flat, estart, elenZ; evs; rewrite HWord.w_srl by lia; change (2 ^ 3) with 8;
                 rewrite ?u64_of_Z by (Z.div_mod_to_equations; lia); cbn [a_off a_base]; unfold LbB_Kit.SHBASE;
                 Z.div_mod_to_equations; lia ]. }
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m OSP_LG) in Hms end.
        exists R'. split; [exact Hms|]. split; [exact Hlf|].
        split; [intros rr Hrr; subst E; eapply (syms_id_sound _ _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
        rreg HR' 1%bv G1. rreg HR' 2%bv G2. split; [exact G1 | exact G2].
      - assert (HK : know_ok asegs E m (OSP_KN0 ++ OSP_KA ++ osp_sh (EVar 33) (Some (EVar 37)) ++ osp_sh (EVar 34) None)).
        { unfold know_ok, OSP_KN0, OSP_KA, osp_sh. cbn [app].
          apply Forall_cons.
          { eapply (kword_of_rw_cells asegs _ m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
          apply Forall_cons.
          { eapply (kword_of_rw_cells asegs _ m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
          apply Forall_cons.
          { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons.
          { eapply (kwr_of_wr_at asegs _ m pwc 2); [exact WRp | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
            | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons.
          { eapply (kwr_of_wr_at asegs _ m pop 2); [exact WRo | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
            | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons; [cbn [kentry_ok]; evs; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; split; [lia | exact Ep]|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; split; [lia | exact Eo]|].
          apply Forall_cons; [eapply (kshadow _ _ _ pwc vp); [evs; reflexivity | lia | lia | evs; reflexivity | exact Shp]|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_cons; [eapply kshadow0; [evs; reflexivity | lia | rewrite Zo in Sho; exact Sho]|].
          apply Forall_nil. }
        xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          AT_OPCODE_SPLIT m (seg_rom asegs) HR HK 40%nat [OSP_RET] (osp_scr true false) 39%N.
        { split_scs. all: first [ cbn [sc_denot]; evs; rewrite w_and7 by lia;
                 match goal with |- context [?x mod 8] => pose proof (Z.mod_pos_bound x 8 ltac:(lia)) end;
                 rewrite w_add by lia; rewrite br_lts_small by lia; apply Z.ltb_lt; lia
               | sc_dj
               | cbn [sc_denot]; unfold flat, estart, elenZ; evs; rewrite HWord.w_srl by lia; change (2 ^ 3) with 8;
                 rewrite ?u64_of_Z by (Z.div_mod_to_equations; lia); cbn [a_off a_base]; unfold LbB_Kit.SHBASE;
                 Z.div_mod_to_equations; lia ]. }
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m OSP_LG) in Hms end.
        exists R'. split; [exact Hms|]. split; [exact Hlf|].
        split; [intros rr Hrr; subst E; eapply (syms_id_sound _ _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
        rreg HR' 1%bv G1. rreg HR' 2%bv G2. split; [exact G1 | exact G2].
      - assert (HK : know_ok asegs E m (OSP_KN0 ++ OSP_KA ++ osp_sh (EVar 33) (Some (EVar 37)) ++ osp_sh (EVar 34) (Some (EVar 38)))).
        { unfold know_ok, OSP_KN0, OSP_KA, osp_sh. cbn [app].
          apply Forall_cons.
          { eapply (kword_of_rw_cells asegs _ m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
          apply Forall_cons.
          { eapply (kword_of_rw_cells asegs _ m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
          apply Forall_cons.
          { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons.
          { eapply (kwr_of_wr_at asegs _ m pwc 2); [exact WRp | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
            | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons.
          { eapply (kwr_of_wr_at asegs _ m pop 2); [exact WRo | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
            | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons; [cbn [kentry_ok]; evs; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; split; [lia | exact Ep]|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; split; [lia | exact Eo]|].
          apply Forall_cons; [eapply (kshadow _ _ _ pwc vp); [evs; reflexivity | lia | lia | evs; reflexivity | exact Shp]|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_cons; [eapply (kshadow _ _ _ pop vo); [evs; reflexivity | lia | lia | evs; reflexivity | exact Sho]|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_nil. }
        xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          AT_OPCODE_SPLIT m (seg_rom asegs) HR HK 40%nat [OSP_RET] (osp_scr true true) 39%N.
        { split_scs. all: first [ cbn [sc_denot]; evs; rewrite w_and7 by lia;
                 match goal with |- context [?x mod 8] => pose proof (Z.mod_pos_bound x 8 ltac:(lia)) end;
                 rewrite w_add by lia; rewrite br_lts_small by lia; apply Z.ltb_lt; lia
               | sc_dj
               | cbn [sc_denot]; unfold flat, estart, elenZ; evs; rewrite HWord.w_srl by lia; change (2 ^ 3) with 8;
                 rewrite ?u64_of_Z by (Z.div_mod_to_equations; lia); cbn [a_off a_base]; unfold LbB_Kit.SHBASE;
                 Z.div_mod_to_equations; lia ]. }
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m OSP_LG) in Hms end.
        exists R'. split; [exact Hms|]. split; [exact Hlf|].
        split; [intros rr Hrr; subst E; eapply (syms_id_sound _ _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
        rreg HR' 1%bv G1. rreg HR' 2%bv G2. split; [exact G1 | exact G2]. }
    destruct RUN as (R' & HMS & Hlf & KK & G1 & G2).
    assert (RF : rfull R') by (exact (msteps_full asegs _ _ HMS (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))).
    assert (E3 : R' = mkR ra sp gp tp (getr R' 5) (getr R' 6) (getr R' 7) s0 s1 (getr R' 10) (getr R' 11) (getr R' 12)
                          (getr R' 13) (getr R' 14) (getr R' 15) (getr R' 16) (getr R' 17) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          (getr R' 28) (getr R' 29) (getr R' 30) (getr R' 31)).
    { rewrite (rfull_eq R' RF) at 1.
      rewrite G1, G2, (KK 3%bv ltac:(inb)), (KK 4%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK 9%bv ltac:(inb)),
              (KK 18%bv ltac:(inb)), (KK 19%bv ltac:(inb)), (KK 20%bv ltac:(inb)), (KK 21%bv ltac:(inb)), (KK 22%bv ltac:(inb)),
              (KK 23%bv ltac:(inb)), (KK 24%bv ltac:(inb)), (KK 25%bv ltac:(inb)), (KK 26%bv ltac:(inb)), (KK 27%bv ltac:(inb)).
      reflexivity. }
    assert (MU : munch ((bv_unsigned sp - 64, bv_unsigned sp) :: [(pwc, pwc + 2); (pop, pop + 2)]) m (mem_denot E m OSP_LG)).
    { apply munch_mem_denot; [exact Hlf|]. unfold OSP_LG. subst E.
      repeat apply Forall_cons; try apply Forall_nil; cbn [inside e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; lia. }
    assert (WM : wmono asegs m (mem_denot E m OSP_LG)) by apply wmono_mem_denot.
    assert (MI1 : mem_inv asegs (mem_denot E m OSP_LG)) by exact (msteps_mem_inv asegs _ _ HMS MI).
    assert (ST1 : stk asegs (mem_denot E m OSP_LG) lo (bv_unsigned sp)) by (apply stk_mem_denot; exact ST).
    assert (AC1 : ACONST (mem_denot E m OSP_LG)).
    { eapply (ACONST_frame _ _ _ AC MU WM).
      apply Forall_cons; [|apply Forall_cons; [exact AOp | apply Forall_cons; [exact AOo | apply Forall_nil]]].
      apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia]. }
    assert (QP : rw_cells asegs (mem_denot E m OSP_LG) pwc [C2 (Z_to_bv 64 (w / 2 ^ 16))]).
    { eapply (rw_cells_log_nth E m OSP_LG 1%nat _ _ _ pwc (C2 (Z_to_bv 64 (w / 2 ^ 16))));
        [exact Hlf | reflexivity | | | exact WRp | reflexivity | exact I |].
      - unfold OSP_LG. cbn [firstn]. apply Forall_cons; [|apply Forall_nil]. cbn [e_addr e_width]. unfold estart. subst E. evs.
        rewrite ?u64_of_Z by lia. lia.
      - unfold estart. subst E. evs. rewrite ?u64_of_Z by lia. lia.
      - cbn [cbytes]. unfold le2, word_to_le_bytes. subst E. evs. rewrite (u64_of_Z (w / 2 ^ 16)) by lia.
        replace (sx32A w) with (TablLib.sx w) by (unfold sx32A, TablLib.sx; rewrite TablStmts.sx32_prs; reflexivity).
        rewrite T16_val by lia. reflexivity. }
    assert (QO : rw_cells asegs (mem_denot E m OSP_LG) pop [C2 (Z_to_bv 64 (w mod 2 ^ 16))]).
    { eapply (rw_cells_log_nth E m OSP_LG 0%nat _ _ _ pop (C2 (Z_to_bv 64 (w mod 2 ^ 16))));
        [exact Hlf | reflexivity | cbn [firstn]; apply Forall_nil | | exact WRo | reflexivity | exact I |].
      - unfold estart. subst E. evs. rewrite ?u64_of_Z by lia. lia.
      - cbn [cbytes]. unfold le2, word_to_le_bytes. subst E. evs. rewrite !u64_of_Z by lia. apply le2_mod.
        rewrite Z.mod_mod by lia. unfold sx32A. rewrite <- TablStmts.sx32_prs, TablLib.sx32_mod16 by lia. reflexivity. }
    eapply evt_of_msteps; [exact HMS|]. rewrite E3.
    step.
    apply evt_done.
    exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 10), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14),
      (getr R' 15), (getr R' 16), (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), (mem_denot E m OSP_LG).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AC1|].
    split; [exact QP | exact QO].
  Qed.
End Split.
