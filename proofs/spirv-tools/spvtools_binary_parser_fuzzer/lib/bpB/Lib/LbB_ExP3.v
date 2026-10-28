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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td LbB_TdKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtorR1 LbB_DPdK LbB_PmXp LbB_PmSL.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_WoGen LbB_ExDefs LbB_ExKit LbB_ExT LbB_ExR1 LbB_ExE0.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_ExC LbB_ExS LbB_ExL.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ExA LbB_ExTA.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmGlue LbB_PcOvf.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ExR7.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_ExP3 () := "C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockI46Stdlib7Sorting;Permutation;Permutation00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6fframeC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4fentI46Stdlib5Lists4List6Exists00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes4list01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4wenvK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8srl3_valK47Corelib7Numbers7BinNums8positive01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv3Sem5alu64C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr03C35stdpp7tactics<f_equal_helpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PcOvf7w_add_gC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMStateCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01K46Stdlib9micromega=RingMicromega3Op201C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs<ASHADOW_BASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow@ASHADOW_BASE_valC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS4xsr3K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StI47Corelib4Init9Datatypes4prod00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_moC4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_LBC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_ALC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs3x_sC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init5Logic2ex00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELI47Corelib4Init9Datatypes6option00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT2WxC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs3xS1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT2PxC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT9ex_rangesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs3xSPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2or00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT7ex_valsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs6x_thisC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs7x_pconsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT7ex_winsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_loC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_ExKit8xpre_geoC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs5x_shiC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_tpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_ExKit9xS1_factsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_raC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_gpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_s0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_s1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_s2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_s3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_s4C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_s5C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_s6C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_s7C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_s8C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_s9C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs5x_s10C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs5x_s11C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState6ret_pcK47Corelib4Init9Datatypes4list02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2b8K47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8ftbl_nilC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4ftblC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT2tSK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4prod01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT3tFwC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT3tHwC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT9tabs_wf3wC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT3wokC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT9Px_step3wC47Corelib4Init9Datatypes3appK5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry04K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit6wboundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8rtbl_okbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit3finC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT9tabs_ok3wI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT9kst_ex_okK47Corelib5Lists7ListDef6Forall01K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN4fknTC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN6swinsTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit:sym_insideC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC46Stdlib5Lists4List7forallbC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8rtbl_chkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4rtblC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN4tupdC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5ftblsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5winsTC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC46Stdlib5Lists4List?Forall_cons_iffC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC46Stdlib5Lists4List2InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit7rtbl_InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_DCtorK7inb_In'C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ExP36w_shffC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_spC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT7ex_keepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat7LINV_P5C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_LFC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_RFSC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_WoGen>wr_at_rw_cellsC56Stdlib6ZArith6BinInt1Z6to_natK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell05C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface?set_shadow_postC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap8ah_setf5C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow<poison_bytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_ExKit4xwinK47Corelib4Init5Logic2or02K47Corelib5Lists7ListDef6Forall02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExC6Px_winC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap;fresh_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_RHEAPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack06stack0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs3x_BC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs6xsavedK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs2XEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs3x_mC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap:fs_scratchC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;as_rauxv_okK46Stdlib9micromega7EnvRing5PExpr04C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ExR73xe2C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions9bv_signedC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec6v_addiC45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState;ret_pc_foldC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec9b_addsextK4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib8BtepFast8sf_congTC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec8evt_doneC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib8BtepFast;sf_evt_stepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge=evt_of_mstepsC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState;ret_pc_evenC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec7evt_cutC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call:MS_full_eqC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN7dk_runNC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_MPRESC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_ExKit<xframe_factsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep5xpresC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4xpreC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_fcC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface8lb_smallC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface6nlargeC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_CHC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_chainC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_TRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5pf_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt8ds_tr_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs6x_ioffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs5x_opcC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_tyC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt6ds_objC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs8x_nwordsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs6x_widxC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs8x_icountC4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface=aimg_client_wC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_sizeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3nshK47Corelib4Init5Logic2or01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface@aclient_write_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib6LbB_SR=aconst_ok_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9aconst_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack0>stack0_ok_aappC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack09stack0_okC57Corelib7BinNums6PosDef3Pos3addC57Corelib7BinNums6PosDef3Pos3mulC57Corelib7BinNums6PosDef3Pos;pred_doubleC47Corelib4Init5Logic7f_equalC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>ah_mpres_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_WoGen9stk_wmonoC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=disjoint_fromC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula01C46Stdlib9micromega;ZifyClasses;rew_iff_revC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_ExKit:xerrno_ATPC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrameBrw_cells_transportC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>ah_rauxv_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>ah_RHEAP_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeapCfs_scratch_of_freshC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_ExKit8xpre_RH0C6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep7rin_ivsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep;rin_ivs_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3fszC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface4fshnC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep>xpres_of_munchC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep;xpres_transC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap:ah_releaseC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<afs_write_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface9lf_removeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>lf_remove_headC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst<ACONST_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack0@stack0_transportC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_TdKit@LINV_P5_munch_hiC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ExP35xpostC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap7ah_doneC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<ahh_evt_thenC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExC4xcutC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3mrdC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec3evtC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28expr_eqbC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7existsbK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02I4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt7DS_SIZEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ExTA6EX_RTcC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExA5EX_SFC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memI47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00K47Corelib4Init5Logic4True01K46Stdlib9micromega:ZMicromega;ZArithProof01I7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs8EX_FLAGPC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs9EX_DS_OFFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs9AEX_STACKC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AFS_HDRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8AFS_SIZEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface9AFS_FLAGSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9ALOWSH_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3ATPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN3tabC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT6kst_exC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface>ASET_SHADOW_F5K47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4xent00I47Corelib7Numbers7BinNums8positive00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs8EX_SAVEDC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6RtB_Td6ATDLOCC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ExR78EX_F5_RAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ExR76EX_RETC4ELinuxProcessSemantics5Riscv3Sem2w1C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState6w1_litI4ELinuxProcessSemantics5Riscv5Instr5instr00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<RT_SMALL_MAXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface:RT_CNT_MAXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<RT_LARGE_MAXC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs9EX_FRAMESC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface>AFS_MAXLIVE_BPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt9DS_EXH_PFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs7EX_COSTC46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op204".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ExP3.
  Local Notation PD_SHB := LbB_DPdK.PD_SHB (only parsing).

  Local Notation kst_ex := LbB_ExT.kst_ex (only parsing).
  Local Notation shT := LbB_ExT.shT (only parsing).
  Local Notation kT := LbB_ExT.kT (only parsing).
  Local Notation wok := LbB_ExT.wok (only parsing).
  Local Notation wok_facts := LbB_ExT.wok_facts (only parsing).
  Local Notation wk_win := LbB_ExT.wk_win (only parsing).
  Local Notation fin_wider := LbB_ExT.fin_wider (only parsing).
  Local Notation rtbl_sw := LbB_ExT.rtbl_sw (only parsing).
  Local Notation ftbl_sw := LbB_ExT.ftbl_sw (only parsing).
  Local Notation ds_cost_le := LbB_ExS.ds_cost_le (only parsing).
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable e : xent H.
  Variables (ff fp : Z).

  Variables (p1 n1 p2 n2 : Z).
  Hypothesis HP : xpre H e.
  Hypothesis FF : fresh_frame H (x_LF e) 3 ff fp.

  Hypothesis THI : obj_inframe (x_LF e) (x_this e) 288.
  Hypothesis PCI : obj_inframe (x_LF e) (x_pcons e) 48.

  Local Notation ftbl_xpres := (@LbB_ExT.ftbl_xpres HCEIL H) (only parsing).
  Local Notation Wx := (@LbB_ExT.Wx H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation Px := (@LbB_ExT.Px HCEIL H e ff fp) (only parsing).
  Local Notation ex_ranges := (@LbB_ExT.ex_ranges HCEIL H e ff fp HP FF) (only parsing).
  Local Notation ex_vals := (@LbB_ExT.ex_vals HCEIL H e ff fp HP FF) (only parsing).
  Local Notation ex_wins := (@LbB_ExT.ex_wins HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xobj_range := (@LbB_ExT.xobj_range HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation ex_keepT := (@LbB_ExT.ex_keepT HCEIL H HHbp e ff fp HP FF THI PCI) (only parsing).
  Local Notation ex_keep := (@LbB_ExT.ex_keep HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation evWx := (@LbB_ExT.evWx H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation kst_ex_ok := (@LbB_ExT.kst_ex_ok HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation evT := (@LbB_ExT.evT HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation shT_start := (@LbB_ExT.shT_start HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation shT_apart := (@LbB_ExT.shT_apart HCEIL H HHbp e ff fp HP FF THI) (only parsing).
  Local Notation shb_eq0 := (@LbB_ExT.shb_eq0 ff) (only parsing).
  Local Notation this_apart := (@LbB_ExT.this_apart HCEIL H HHbp e ff fp HP FF THI) (only parsing).
  Local Notation kT_ok := (@LbB_ExT.kT_ok HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF THI PCI) (only parsing).
  Local Notation scT_flat := (@LbB_ExT.scT_flat HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation scP_flat := (@LbB_ExT.scP_flat HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tS := (@LbB_ExT.tS H e) (only parsing).
  Local Notation tFw := (@LbB_ExT.tFw ff) (only parsing).
  Local Notation tHw := (@LbB_ExT.tHw ff) (only parsing).
  Local Notation tF := (@LbB_ExT.tF ff) (only parsing).
  Local Notation tH := (@LbB_ExT.tH ff) (only parsing).
  Local Notation tab_vals := (@LbB_ExT.tab_vals HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_wf3w := (@LbB_ExT.tabs_wf3w HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_wf3 := (@LbB_ExT.tabs_wf3 HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation wk_stk := (@LbB_ExT.wk_stk HCEIL H e ff fp HP FF) (only parsing).
  Local Notation shb_eq := (@LbB_ExT.shb_eq ff) (only parsing).
  Local Notation tabs_ok3w := (@LbB_ExT.tabs_ok3w HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_ok3 := (@LbB_ExT.tabs_ok3 HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation Px_step3w := (@LbB_ExT.Px_step3w HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation Px_step3 := (@LbB_ExT.Px_step3 HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation Wx_sw1 := (@LbB_ExT.Wx_sw1 HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation Wx_sw := (@LbB_ExT.Wx_sw HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation ex_shvis := (@LbB_ExC.ex_shvis HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation fr_app := (@LbB_ExC.fr_app HCEIL H e ff fp HP FF) (only parsing).
  Local Notation fr_addr := (@LbB_ExC.fr_addr HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation fr_str := (@LbB_ExC.fr_str HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xwin_stk := (@LbB_ExC.xwin_stk HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xwin_fr := (@LbB_ExC.xwin_fr H e ff) (only parsing).
  Local Notation Px_win := (@LbB_ExC.Px_win HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation obj_apart := (@LbB_ExC.obj_apart HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation blk_apart := (@LbB_ExC.blk_apart HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xds_run := (@LbB_ExC.xds_run HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xcut := (@LbB_ExC.xcut HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation xchain_call := (@LbB_ExS.xchain_call HCEIL H HHbp e ff fp HP) (only parsing).
  Local Notation xsess := (@LbB_ExS.xsess H e ff) (only parsing).
  Local Notation xsess_facts := (@LbB_ExS.xsess_facts HCEIL H e ff HP) (only parsing).
  Local Notation x_ds_pre := (@LbB_ExS.x_ds_pre HCEIL H HHbp e ff fp HP) (only parsing).
  Local Notation sf_xpres := (@LbB_ExS.sf_xpres HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation x_ds_back := (@LbB_ExS.x_ds_back HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xsr := (@LbB_ExS.xsr HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation rcall := (@LbB_ExS.rcall H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation x_ds_obj := (@LbB_ExS.x_ds_obj HCEIL H e ff fp HP FF) (only parsing).
  Local Notation x_cseq := (@LbB_ExS.x_cseq HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation rcall1 := (@LbB_ExS.rcall1 H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation rcall0 := (@LbB_ExS.rcall0 H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation x_u64 := (@LbB_ExS.x_u64 HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xsr3 := (@LbB_ExS.xsr3 HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation x_dtor := (@LbB_ExS.x_dtor HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation x_run := (@LbB_ExS.x_run HCEIL H HHbp e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation xsess_win := (@LbB_ExS.xsess_win HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation x_stk_back := (@LbB_ExS.x_stk_back HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation x_strlen := (@LbB_ExS.x_strlen HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xsess_run := (@LbB_ExS.xsess_run HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation xsr_mono := (@LbB_ExS.xsr_mono HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation x_ts := (@LbB_ExL.x_ts HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation x_os := (@LbB_ExL.x_os HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Notation SP := (xSP e) (only parsing).
  Notation this := (x_this e) (only parsing).
  Notation pcons := (x_pcons e) (only parsing).

  Ltac evwx := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wx;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

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

  Ltac exrun3 HRT HSF HFT HHT HPX HMI fuel stops kx := exrun3w 504 64 HRT HSF HFT HHT HPX HMI fuel stops kx.

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

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Local Notation ds := (ff + EX_DS_OFF) (only parsing).

  Ltac lit_acc p gsz grz :=
    let M' := fresh "M'" in let ACM' := fresh "ACM'" in
    intros M' ACM'; eapply (addressable_accessible M' p gsz); [| lia | lia | unfold AAPP_HI; lia];
    eapply (ACONST_global_addressable M' p gsz grz ACM'); [| lia]; unfold aglobals; repeat (first [left; reflexivity | right]).
  Ltac lit_bytes p n :=
    let r := eval vm_compute in (PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 p) n) in
    lazymatch r with Some ?bs => exists bs; split; [reflexivity |
      let M' := fresh "M'" in let MIM' := fresh "MIM'" in let B' := fresh "B'" in
      intros M' MIM'; edestruct (LbB_PmGlue.img_lit M' p n bs MIM') as [B' _]; [lia | cbn; lia | vm_compute; reflexivity | exact B']] end.
  Ltac scT := unfold scs_denot; repeat (apply Forall_cons; [cbn [sc_denot]; unfold elenZ; cbn [edenot]; rewrite ?unsigned_lit by (clear; lia);
                                           first [apply scT_flat; clear; lia | apply scP_flat; clear; lia] |]); apply Forall_nil.

  Ltac rc3 := let R := fresh "R" in let HRT := fresh "HRT" in intros R HRT;
    let G1 := fresh in let G2 := fresh in let G8 := fresh in let G4 := fresh in let G10 := fresh in let G11 := fresh in let G12 := fresh in
    rgetx HRT (1%bv : reg) G1; rgetx HRT (2%bv : reg) G2; rgetx HRT (8%bv : reg) G8; rgetx HRT (4%bv : reg) G4;
    rgetx HRT (10%bv : reg) G10; rgetx HRT (11%bv : reg) G11; rgetx HRT (12%bv : reg) G12;
    exact (conj G1 (conj G2 (conj (eq_trans G8 (eq_sym (Z_to_bv_bv_unsigned (x_sp e)))) (conj G4 (conj G10 (conj G11 G12)))))).
  Ltac rc1 := let R := fresh "R" in let HRT := fresh "HRT" in intros R HRT;
    let G1 := fresh in let G2 := fresh in let G8 := fresh in let G4 := fresh in let G10 := fresh in let G11 := fresh in
    rgetx HRT (1%bv : reg) G1; rgetx HRT (2%bv : reg) G2; rgetx HRT (8%bv : reg) G8; rgetx HRT (4%bv : reg) G4;
    rgetx HRT (10%bv : reg) G10; rgetx HRT (11%bv : reg) G11;
    exact (conj G1 (conj G2 (conj (eq_trans G8 (eq_sym (Z_to_bv_bv_unsigned (x_sp e)))) (conj G4 (conj G10 G11))))).
  Ltac rc0 := let R := fresh "R" in let HRT := fresh "HRT" in intros R HRT;
    let G1 := fresh in let G2 := fresh in let G8 := fresh in let G4 := fresh in let G10 := fresh in
    rgetx HRT (1%bv : reg) G1; rgetx HRT (2%bv : reg) G2; rgetx HRT (8%bv : reg) G8; rgetx HRT (4%bv : reg) G4;
    rgetx HRT (10%bv : reg) G10;
    exact (conj G1 (conj G2 (conj (eq_trans G8 (eq_sym (Z_to_bv_bv_unsigned (x_sp e)))) (conj G4 G10)))).

  Ltac xn X :=
    lazymatch type of X with
    | (xsr ?pc ?rt ?sf ?l ?sp ?c) =>
        let rt' := eval vm_compute in rt in
        tryif constr_eq rt rt' then idtac else
          (let E := fresh "E" in assert (E : rt = rt') by (vm_cast_no_check (@eq_refl _ rt')); rewrite E in X; clear E)
    end.

  Ltac xseg0 dirs stops kx :=
    let R := fresh "R" in let F := fresh "F" in let fc := fresh "fc" in let m := fresh "m" in let XSc := fresh "XSc" in
    let s := fresh "s" in let LBc := fresh "LBc" in let DB := fresh "DB" in
    let RFx := fresh "RFx" in let HRTx := fresh "HRTx" in let HSFx := fresh "HSFx" in let HIx := fresh "HIx" in
    let MIx := fresh "MIx" in let SSx := fresh "SSx" in let HFTx := fresh "HFTx" in let HHTx := fresh "HHTx" in
    intros R F fc m XSc s LBc DB RFx HRTx HSFx HIx MIx SSx;
    assert (HFTx : ftbl Wx ff m []) by apply ftbl_nil; assert (HHTx : ftbl Wx (ff / 8) m []) by apply ftbl_nil;
    exrun3wd dirs 0 0 HRTx HSFx HFTx HHTx HIx MIx 1000%nat stops kx.
  Ltac xseg_done :=
    let R' := fresh "R'" in let m' := fresh "m'" in
    let RFy := fresh "RFy" in let HRTy := fresh "HRTy" in let HTSy := fresh "HTSy" in let HPy := fresh "HPy" in
    let HMIy := fresh "HMIy" in let MUy := fresh "MUy" in let WMy := fresh "WMy" in
    let HSFy := fresh "HSFy" in let HFTy := fresh "HFTy" in let HHTy := fresh "HHTy" in
    intros R' m' RFy HRTy HTSy HPy HMIy MUy WMy; tsplit HTSy HSFy HFTy HHTy; cbn [s_pc];
    apply evt_done; exists R', m'; split; [reflexivity|]; split; [exact RFy|]; split; [exact HRTy|]; split; [exact HSFy|];
    split; [exact HPy|]; split; [exact HMIy|];
    lazymatch goal with HIx : Px _ ?s ?LBc ?m, SSx : xsess ?LBc ?len ?DB ?m |- _ =>
      eapply (xsess_run s LBc len DB m m' 0 0 _ _ _ _ _ _ eq_refl ltac:(clear; lia) ltac:(clear; lia));
        [let RHx := fresh "RHx" in destruct HIx as (_ & _ & RHx & _); exact RHx | exact SSx | exact MUy | exact WMy] end.
  Ltac xclose := first [apply Forall_nil | unfold scs_denot; apply Forall_nil | scT].

  Lemma w_shff : forall x, 0 <= x < 2 ^ 47 ->
    alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 2147450880) = Z_to_bv 64 (sh x).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_ExP3 ()) ["ExP3"] "h02Hah16__sat4h24__x1h37__arithh44__ffh56__sat3h66__sat5h76__sat6h88__varmaph95__with:1bh;1zh<2Hxh=1Kh>1xp;1p;2p;3p;4p;8p;5p;6p;7p10000p4p70p1000ip4p710p8p1001Tp4p70g002NR0p4p710R1p8p1002jp4p7210g003VR2p4p710p8p10044p4p70R3P1p8P3p1004np4p710p8g005Kj17Tg0060j16Tg006Nj2KTg006kj29Tg007Gj2ETg007bj1DTg008@j1WTg008cj1ATg009Cj1QTg00:=j1FTg00;5j2MTg00;mj2;Tg00<Gj2HTg00<oj3ITg00=Sj2]Tg00>4j1\Tg00>Tj2[Tg00?2j1ZTg00?Pj1YTg00@;j2?Tg00@^j2XTg00AAj4<Tg00Alj3CTg00BOj1VTg00C1j8UTg00CUj2TTg00D7j2STg00Dcj34Tg00E=j3RTg00E\j4PTg00FNj5OTg00GKj1>Tg00H0j3NTg00Hhj2BTg00IRj28Tg00Ioj20j1fTg00JUj3=Tg00K=j1LTg00L4j25Tg00LQj2eTg00MBj3JTg00Mej8dTP2j6@Tg00NBj2_Tg00O@j1^TP0j6`Tg00PKj2aTg00Pgj7bTg00QKj7cTg00QoR0f0R2'ap=1%>2#>p=2%72#7p=3f1R3g00RMR1g00RlR4P4g00SLR5P2g00SlFbp=:f2R6P1P4P4P5P3P2Fcp=Gg00TLR7%12g00TjR8#7R9#6R:%29#2R;#6R<'KR=,92'ER>%39R9#7#3R?#DR@#WRA#A#QRB%F3RCP31MBC,;A1H:<RD190:RE%1<190=[RF[RG%1:RHg00UORIAI:<3UW0R<%1=\I^0HR=%6?R?,H:%1?1K:?RJ,90[RK\EAI:?3VIX0H%1J\I^0HP3g00Uk1]0:';PEeREO1RHPKf4RKPEO1PFg00VQRE#ARI%\ERE1[73R?%Z7RL%Y7RMP1P4P4P5P71?70g00W=1X78R1C<,:MRNP7P1g00WdRO1?7:R:%D;5C7C<,:M5GM%V4P7P1POAC7:@C<,:M9GMNGU1TM5R5P2P6g00XKRNg00XkR:';1S26=4N:dAR703CPR0b4b8b9X27%13193J'E\>^27P2f8f7R>O2b3b7b1b5b1b6b7DOg00YKRJ%>8R8#6R:#F7NC,MB,B@%69R9,83547PA10@610@:5=JRJ,B@R:,0@g00Z7R3%28#2#2#2#2#2#2#7#3#3#3#3#3#3#3#6R8,0@RB7=2f3RC#L,0@RN54AX:AP71869RO10@2==3B=4ANX;7PA15O8R4,0@R;A4A2NX:AP7P818C9RC/58,0@152C,0@54AX;7P7PA%f@RCPCP4158OPA\7/;C1e69%16%1918K9#1[[PDPGP<P=PHPFPIPEP?PLP71?78RL9J71g00ZcAJ7L1C<,:MP5P0b4b8b9X2715281582547^27P218>9O1b3b1b5b1b6Gdg00[Jg00\HE@%L6,0@94A;e10@O==3B1_O8E@P:P2E@PJ%^JE`b=W<W>o"). Qed.

  Definition xpost : config -> Prop :=
    ds_post H LINV_P5 (x_ra e) (x_sp e) (x_gp e) (x_tp e) (x_s0 e) (x_s1 e) (x_s2 e) (x_s3 e) (x_s4 e) (x_s5 e) (x_s6 e)
      (x_s7 e) (x_s8 e) (x_s9 e) (x_s10 e) (x_s11 e) (x_F e) (x_fc e) (x_s e) (x_LB e) (x_LB e) (x_LF e)
      [(RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] (2 ^ 20) (x_lo e) (x_B e) (x_shi e) (x_m e) (x_mo e) (Some (2 ^ 64 - 4))
      (fun LB' _ => Permutation LB' (x_LB e)).

  Lemma x_end : forall c, xsr3 0xf8f14 EX_RTc EX_SF 294912 c -> as_SR H xpost c.
Proof.
    intros [msF mo] (s & F & fc & XSc & LBc & KR & MP & FZ & CUT & AL).
    cbn [cfg_ms cfg_model] in *.
    destruct CUT as (R & m & VIS & RF & HRT & HSF & HI & MI & (PM & DA)).
    pose proof ex_ranges as (SPR & ACS & SPH & FSB1 & FSB2 & F64 & FP1 & FSB3 & FSB4 & FSB5 & FSB6 & ACE).
    pose proof ex_vals as (FFR & FPR & TH0 & TH1 & TH8 & PC0 & PC1).
    pose proof ex_wins as WIN.
    pose proof (xS1_facts H e HP) as (S32 & S1SP & S1L & SPH2 & LOS1 & ACL).
    pose proof (xpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (xframe_facts H _ _ _ FF)
      as (XF1 & XF2 & XF3 & XF4 & XF5 & XF6 & XF7 & XF8 & XF9 & XAPP & XF11 & XF12 & XF13 & XF14 & XF15 & XF16).
    set (P := fun ms : machine_state => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 m3,
        ms = MS (mkR (x_ra e) (x_sp e) (x_gp e) (x_tp e) t0 t1 t2 (x_s0 e) (x_s1 e) (Z_to_bv 64 (2 ^ 64 - 4)) a1 a2 a3 a4 a5 a6 a7
                     (x_s2 e) (x_s3 e) (x_s4 e) (x_s5 e) (x_s6 e) (x_s7 e) (x_s8 e) (x_s9 e) (x_s10 e) (x_s11 e) t3 t4 t5 t6)
                F (ret_pc (x_ra e)) fc None m3 (seg_rom asegs)
        /\ Px XSc s LBc m2 /\ munch [(fp, fp + 1)] m2 m3 /\ wmono asegs m2 m3 /\ mem_inv asegs m3
        /\ mrd asegs m3 (wa fp) = Some (b8 0) /\ stk asegs m3 (x_lo e) (xSP e)).
    eapply (ahh_evt_then H HH P xpost s msF _ mo KR VIS).
    - assert (HFT : ftbl Wx ff m []) by apply ftbl_nil. assert (HHT : ftbl Wx (ff / 8) m []) by apply ftbl_nil.
      exrun3w 8 64 HRT HSF HFT HHT HI MI 1000%nat [ASET_SHADOW_F5] (@nil kentry);
        [ xclose .. | ].
      intros R1 m1 RF1 HRT1 HTS1 HP1 MI1 MU1 WM1. cbn [s_pc].
      rgetx HRT1 (1%bv : reg) G1. rgetx HRT1 (2%bv : reg) G2. rgetx HRT1 (3%bv : reg) G3. rgetx HRT1 (4%bv : reg) G4.
      rgetx HRT1 (8%bv : reg) G8. rgetx HRT1 (10%bv : reg) G10. rgetx HRT1 (11%bv : reg) G11.
      rgetx HRT1 (18%bv : reg) G18. rgetx HRT1 (20%bv : reg) G20.
      rewrite w_shff in G10 by lia.
      rewrite (MS_full_eq R1 _ _ _ _ _ RF1).
      pose proof (ex_keep _ _ _ _ HP1) as (AC1 & LV1 & MI1' & STK1 & WF1 & WS1 & RFS1).
      destruct (wr_at_rw_cells m1 (sh ff) 64 WS1 ltac:(lia) ltac:(lia)) as [junk SJ].
      eapply evt_cut.
      { eapply (ah_setf5 H HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (sh ff) 64 junk);
          [exact G10 | exact G11 | lia | exact SJ | exact MI1 | exact AC1]. }
      intros ms2 (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & EQ2 & MU2 & WM2 & MI2 & SH2).
      subst ms2.
      assert (HP2 : Px XSc s LBc m2).
      { eapply Px_win; [exact HP1 | exact MU2 | exact WM2 | exact MI2 |].
        apply Forall_cons; [| apply Forall_nil]. unfold xwin; cbn [fst snd]. right; right; lia. }
      pose proof HP2 as (RFS2 & _ & RH2 & AC2 & _ & S02 & RX2 & ER2 & STK2 & SAV2 & FLG2 & WF2 & WP2 & XP2 & SCR2 & LV2).
      rewrite G1, G2, G8, G18, G20.
      rewrite ret_pc_even by (first [lia | reflexivity]).
      rewrite <- (Z_to_bv_bv_unsigned (x_sp e)).
      change 1019900 with EX_F5_RA.
      edestruct xe2 with (ff := ff) (fp := fp) (SP := xSP e) (S1 := xS1 e) (r := 18446744073709551612) (m := m2)
          (ra' := x_ra e) (s0' := x_s0 e) (s1' := x_s1 e) (s2' := x_s2 e) (s3' := x_s3 e) (s4' := x_s4 e) (s5' := x_s5 e)
          (s6' := x_s6 e) (s7' := x_s7 e) (s8' := x_s8 e) (s9' := x_s9 e) (s10' := x_s10 e) (s11' := x_s11 e)
        as (R3 & M3 & STP & ER3 & MU3 & WM3 & MI3 & STK3 & FL3);
        [ first [lia | exact SAV2 | exact FLG2 | exact WP2 | exact MI2] .. | ].
      eapply (evt_of_msteps _ _ _ _ STP).
      subst R3. rewrite G3, G4.
      zstep.
      apply evt_done.
      exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m2, M3.
      split.
      { unfold xSP; rewrite Z_to_bv_bv_unsigned; reflexivity. }
      split; [exact HP2|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact FL3|].
      exact (STK3 _ _ STK2).
    - intros msF' mo' KR' MP' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & m3
                               & VIS3 & HP2 & MU3 & WM3 & MI3 & FL3 & STK3).
      pose proof HP2 as (RFS2 & _ & RH2 & AC2 & _ & S02 & RX2 & (errv & ER2) & STK2 & SAV2 & FLG2 & WF2 & WP2 & XP2 & SCR2 & LV2).
      assert (FPW : forall LB, Forall (aclient_write_ok H LB) [(fp, fp + 1)]).
      { intros LB; apply Forall_cons; [| apply Forall_nil].
        unfold aclient_write_ok; cbn [fst snd]; right; right; right; right; left; lia. }
      apply (ah_done H HH). unfold xpost, ds_post.
      exists t0, t1, t2, (Z_to_bv 64 (2 ^ 64 - 4)), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m3, errv, s, LBc,
        (XE H ff fp ++ XSc), F, fc.
      split; [exact VIS3|]. split; [exact FZ|].
      split; [intros d Hd; injection Hd as <-; reflexivity|].
      split; [exact KR'|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP')|].
      split; [exact MI3|]. split; [exact STK3|].
      split.
      { pose proof (xerrno_ATP H e TP) as EA.
        eapply (rw_cells_transport _ _ _ _ _ _ ER2 MU3 WM3); cbn [disjoint_from cells_size].
        split; [| exact I]. rewrite EA. change (Z.of_nat (csize (C4 errv) + 0)) with 4. left. unfold ATP. lia. }
      split.
      { exact (ah_rauxv_frame H HH (x_LB e) _ _ _ _ RX2 MU3 WM3 (FPW _)). }
      split.
      { exact (ah_RHEAP_frame H HH _ _ _ _ _ RH2 MU3 WM3 (FPW _)). }
      split; [exact PM|].
      split.
      { apply Forall_app; split; [exact (fs_scratch_of_fresh H _ _ _ _ FF) | exact SCR2]. }
      split.
      { eapply (xpres_trans H _ _ _ _ m2); [exact XP2 |].
        eapply (xpres_of_munch H (x_s e) _ _ _ _ (x_m e)); [exact HH | exact (xpre_RH0 H e HP) | exact MU3 | exact WM3 |].
        apply Forall_cons; [| apply Forall_nil]. right. intros a Ha. cbn [fst snd] in Ha.
        cbn [rin_ivs XE app fst snd]. right; right; left. lia. }
      split.
      { rewrite <- (lf_remove_head 3 ff fp (x_LF e)).
        eapply (ah_release H HH _ m2 m3 [(fp, fp + 1)] 3 ff fp RFS2); [left; reflexivity | exact MU3 | exact WM3 | | exact FL3].
        apply Forall_cons; [| apply Forall_nil]. right; split; reflexivity. }
      split.
      { eapply (ACONST_frame _ _ _ AC2 MU3 WM3). apply Forall_cons; [| apply Forall_nil].
        eapply (aconst_ok_app _ _ _ _ XAPP); lia. }
      split.
      { eapply (stack0_transport _ _ _ _ _ S02 MU3 WM3). apply Forall_cons; [| apply Forall_nil].
        eapply (stack0_ok_aapp _ _ _ _ XAPP); lia. }
      split.
      { eapply (LbB_TdKit.LINV_P5_munch_hi _ _ _ LV2 MU3). apply Forall_cons; [| apply Forall_nil]. cbn [fst]; lia. }
      lia.
  Qed.
End ExP3.
