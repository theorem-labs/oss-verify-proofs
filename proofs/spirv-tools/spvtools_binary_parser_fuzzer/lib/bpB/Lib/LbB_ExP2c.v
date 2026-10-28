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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_ExP2c () := "C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4fentC47Corelib4Init5Logic6eq_indI46Stdlib5Lists4List6Exists00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3mulC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_modC47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions@Z_to_bv_unsignedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PcOvf7w_add_gC4ELinuxProcessSemantics5Riscv3Sem7mul_divC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PcOvf7w_mul_gK46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5mulop01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt5cstrAK47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes4prod00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5keptkK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS3xsrC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS4xsr3C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow:in_app_memC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow:accessibleC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5shvisI47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3oppI47Corelib4Init5Logic2ex00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4xpreC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_fcC4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs3x_sC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_LBC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs3x_mC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_RHEAPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface8lb_smallC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface6nlargeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs3x_BC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;as_rauxv_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs3xSPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_loC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_tpK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_raC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat7LINV_P5C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_LFC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_RFSC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs5x_shiC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack06stack0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_s0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_CHC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_chainC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_TRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5pf_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt8ds_tr_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_ALC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs6x_ioffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs5x_opcC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_tyC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs6x_thisC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt6ds_objC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs7x_pconsK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs8x_nwordsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs6x_widxC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs8x_icountC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmSL9cstrA_imgC56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT2WxC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4rtblC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs3xS1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4ftblC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT2PxC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS5xsessC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8ftbl_nilC56Stdlib6ZArith6BinInt1Z3divC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT2tSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT3tFwC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT3tHwC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT9tabs_wf3wC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT3wokC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT9Px_step3wC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExC4xcutC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romK5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry04K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit6wboundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8rtbl_okbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit3finC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT9tabs_ok3wI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT9kst_ex_okK47Corelib5Lists7ListDef6Forall01K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN4fknTC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN6swinsTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit:sym_insideC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8rtbl_chkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN4tupdC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5ftblsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5winsTC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC46Stdlib5Lists4List?Forall_cons_iffC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcK47Corelib4Init9Datatypes6option02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap;fresh_frameC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs6xsavedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs2XEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep5xpresC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap:fs_scratchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS9xsess_runK47Corelib4Init5Logic2ex01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN7dk_runNC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit5fkeysC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_DCtorK7inb_In'C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit7rtbl_InC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4wenvC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4x_spC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMStateCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS6rcall0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT7ex_valsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT7ex_winsI47Corelib4Init5Logic2or00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS5rcallK47Corelib4Init5Logic2or01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConstIACONST_global_addressableC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadowFaddressable_accessibleC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init9Datatypes6option01C4ARocqVerifyHarness?AgentSubmission8PropExec3rdnC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue7img_litK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT2kTK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT8ex_keepTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT5kT_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT8scP_flatC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState<unsigned_litC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT8scT_flatK47Corelib5Lists7ListDef6Forall02c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_ExP2c8wsub_valC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS6rcall1C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DRep8ds_repA0I46Stdlib7Sorting;Permutation;Permutation00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own6lb_ownC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DRep9ds_laws_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt7dla_errC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses5mkrelC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvAkword_of_rw_cellsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS6x_dtorC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS5x_runC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS6x_cseqC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS5x_u64C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExS8x_strlenK45stdpp9bitvector;definitions2bv01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem8bytes_atC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC46Stdlib5Lists4List7forallbC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec3evtC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec8evt_doneC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28expr_eqbC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7existsbK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init5Logic2or02C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib4Init5Logic4True01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00I47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExT6kst_exI5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K46Stdlib9micromega=RingMicromega3Op203C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs8EX_FLAGPK46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ExTA6EX_RTbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_ExA5EX_SFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ExTA6EX_RTcK4ELinuxProcessSemantics5Riscv5Instr5aluop07C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs7AIMG_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3memC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<RT_SMALL_MAXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface:RT_CNT_MAXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface<RT_LARGE_MAXC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs9AEX_STACKC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3ATPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6fframeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs9EX_FRAMESC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface>AFS_MAXLIVE_BPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt9DS_EXH_PFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs7EX_COSTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN3tabC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ASTRLEN_STUBK47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEI6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs4xent00I47Corelib7Numbers7BinNums8positive00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init9Datatypes4bool02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs8EX_SAVEDC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6RtB_Td6ATDLOCC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt9APUT_CSEQK46Stdlib9micromega:ZMicromega;ZArithProof01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_ExDefs9EX_DS_OFFC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst8aglobalsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIC46Stdlib9micromega8ZifyInst7Inj_Z_ZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt8APUT_U64C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt8ADS_DTORC4ARocqVerifyHarness?AgentSubmission8LibIface3memC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt:DS_ERR_OFF".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ExP2c.
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

  Hypothesis HCSEQ : put_cseq_stmtA H LINV_P5 ds_repA0.
  Hypothesis HU64 : put_u64_stmtA H LINV_P5 ds_repA0.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV_P5 ds_repA0.

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
  Ltac xseg stops := xseg0 (@nil bool) stops (@nil kentry); [ xclose .. | xseg_done ].
  Ltac kTg := lazymatch goal with HIx : Px ?XSc ?sk ?LBk ?m |- _ =>
    let KN := fresh "KN" in let KW := fresh "KW" in
    pose proof (ex_keepT XSc sk LBk m HIx) as (_ & _ & KN & KW & _);
    eapply kT_ok; [exact HIx | lia | lia | reflexivity | eassumption | evwx; reflexivity] end.
  Ltac kDs := lazymatch goal with SSx : xsess ?LBc ?len ?DB ?m |- _ =>
    let EW := fresh "EW" in
    pose proof (dla_err _ _ (ds_laws_A LINV_P5 (fun m0 h => h)) _ _ _ _ _ _ (proj1 SSx)) as EW;
    apply Forall_cons; [| apply Forall_nil];
    eapply (kword_of_rw_cells _ _ _ _ _ 0%nat _ _ _ 4%nat EW);
      [ reflexivity | reflexivity | lia
      | evwx; rewrite ?unsigned_lit by (pose proof ex_vals; lia); unfold EX_DS_OFF, DS_ERR_OFF; cbn [Z.of_nat]; lia
      | pose proof ex_vals; pose proof ex_wins; unfold EX_DS_OFF, DS_ERR_OFF; lia
      | pose proof ex_vals; pose proof ex_wins; unfold EX_DS_OFF, DS_ERR_OFF; lia
      | reflexivity ] end.
  Ltac rc1w WS := let R := fresh "R" in let HRT := fresh "HRT" in intros R HRT;
    let G1 := fresh in let G2 := fresh in let G8 := fresh in let G4 := fresh in let G10 := fresh in let G11 := fresh in
    rgetx HRT (1%bv : reg) G1; rgetx HRT (2%bv : reg) G2; rgetx HRT (8%bv : reg) G8; rgetx HRT (4%bv : reg) G4;
    rgetx HRT (10%bv : reg) G10; rgetx HRT (11%bv : reg) G11; rewrite ?WS in G11;
    exact (conj G1 (conj G2 (conj (eq_trans G8 (eq_sym (Z_to_bv_bv_unsigned (x_sp e)))) (conj G4 (conj G10 G11))))).

  Lemma xp_rng : 0 <= x_ioff e < 2 ^ 63 /\ 0 <= x_nwords e < 2 ^ 63 /\ 0 <= x_widx e < 2 ^ 63.
  Proof.
    pose proof HP as Hx. unfold xpre in Hx. cbv zeta in Hx.
    repeat match type of Hx with ?A /\ ?B => let Ha := fresh "Ha" in destruct Hx as [Ha Hx] end.
    repeat split; lia.
  Qed.

  Lemma wsub_val : forall a b,
    alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 b)) (Z_to_bv 64 a) = Z_to_bv 64 ((a - b) mod 2 ^ 64).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_ExP2c ()) ["ExP2c"] "h01zh11bh22H0h32Hah47__arithh54__ffh67__sat66h78__varmaph85__with94__x1h:4__x2h;2b1h<2b2h=1nh>7__sat65h?1ap;1p;2p;3p;4p;6p;7p10000p4p70R0g000jR1p4p710p8P0p1001Fp4p710p8g001cj16Tg002Hj1bTg002fj14Tg003Ij1ITg003gj2>Tg004Dj21Tg004jj3DTg005Rj28Tg005oj1ATg006Mj2KTg006jj25Tg007Jj32Tg007dj29Tg008Aj23Tg008kj3ZTg009Oj2=Tg00:5j1WTg00:Uj1VTg00;5j2UTg00;Sj1TTg00<1j4STg00<Oj1PTg00<mj1OTg00=Xj2BTg00>;j3MTg00>^j2:Tg00?Aj3LTg00?dj3JTg00@Gj4@Tg00A2j2HTg00ATj2;Tg00Anj2NTg00BZj3GTg00C9j4QTg00Ckj2RTg00DSj2CTg00Doj2<Tg00EKj3FTg00Eoj2aTg00FPj3`Tg00G3j6_Tg00GWj3^Tg00H8j67TP1j6]Tg00HVj2ETg00IEj2[Tg00JCj4\Tg00Jmj2YTg00Kkj7XTg00LOR1f1R0f0R232p=0P0g00LmR3g00MLR4P4g00MlR5P2g00NLFXp=?g00NlR6#6R7#6#6#6#6#6R8#bR9#4R:%I6R;/>2R<,19R=g00OQR>f2R?,197D218?0R@%A7RA%A8R8'KRB'5RC,19RD52:X1:P:19<0,19A2:2DX1:g00P=R:%42RE%40RFg00P[%4??202f3RG/3?13G0'0RH[13?013?2'0%4G?2?0[RIf4RJ#4?2G?\HAZ?02P2n2001000000120000000W<W;W=PI^<F^;E^=:P2P91>;0R:/9?RE,19RFPDP11=9ERI18G?RH/5BRK,19,39,02X01P11=9CRL1>;?/9GRM,=9/02X01g00Q6RN#WRO%VNRNP11U1?P0%T1RPCS%P1RQ%O1RRP11B16R61B17R75M1g00QbRS1:1;=L17=J16C@'?1HR5R6P2P?g00RIR7g00RiRT';1N2?=27Tdg00SIRT=G10CQR7b5b7b8X91X:1182019:2'0^91^:1P2P?PGO2b410@EP1PH152B18JG/5BRJ/5B'0X01P1PK10J2X011;1K15KB1RA81CTARK1<T81CTB[RJ[1<TARGg00SgR@AFA80UW31<TB\@^3GP0g00TC1aTA';PKeO1PJPOPNPPPQPRP3P4P4P5P11:1A=`19PS1:1TC@,?RE_P6P7b5b7b8A21BTg00Ti[P2b4b6b>b69^HBE7PMP2E]b210ILe139D1E9CE7139F1E9EE7O4b211909D>=1[<0E7P9g00UF119;1192C\1Y;2E7X11X?1o"). Qed.

  Lemma seg_C : forall (Q : config -> Prop) c len0, cstrA p2 n2 -> 0 <= len0 <= 348 ->
    xsr 0xf8eb0 (keptk EX_RTb ++ [(10%bv, EVar 61)]) EX_SF len0 163840 c ->
    (forall c', xsr3 0xf8f14 EX_RTc EX_SF 294912 c' -> as_SR H Q c') ->
    as_SR H Q c.
Proof.
    intros Q c len0 CS HL X K.
    pose proof xp_rng as (RIO & RNW & RWI).
    xn X.
    eapply (x_run Q 0xf8eb0 _ EX_SF _ _ ASTRLEN_STUB _ EX_SF c X); [xseg [ASTRLEN_STUB] |].
    intros c1 X1. xn X1.
    eapply (x_strlen Q _ EX_SF _ _ 0xf8eb8 p2 n2 62%N c1 X1);
      [vm_compute; reflexivity | rc0 | reflexivity | lia | exact CS
      | reflexivity | ].
    intros c2 X2. xn X2.
    eapply (x_run Q 0xf8eb8 _ EX_SF _ _ APUT_CSEQ _ EX_SF c2 X2); [xseg [APUT_CSEQ] |].
    intros c3 X3. xn X3.
    assert (MI0 : exists m, mem_inv asegs m)
      by (destruct X3 as (s & F & fc & XSc & LBc & DB & _ & _ & _ & (R & m & _ & _ & _ & _ & _ & MI & _) & _); exists m; exact MI).
    destruct MI0 as [m0 MI0].
    destruct (LbB_PmSL.cstrA_img p2 n2 m0 CS MI0) as (S1 & S2 & S3 & S4 & S5).
    pose proof CS as (_ & CN2 & _).
    eapply (x_cseq HCSEQ Q _ EX_SF _ _ 0xf8ec8 p2 n2 c3 X3);
      [vm_compute; reflexivity | rc3 | reflexivity | lia | exact S3 | exact S1 | exact S2 | exact S4 | exact S5
      | lia | unfold EX_COST; lia | ].
    intros c4 X4. xn X4.
    eapply (x_run Q 0xf8ec8 _ EX_SF _ _ APUT_CSEQ _ EX_SF c4 X4); [xseg [APUT_CSEQ] |].
    intros c5 X5. xn X5.
    eapply (x_cseq HCSEQ Q _ EX_SF _ _ 0xf8edc 0x24d60 24 c5 X5);
      [vm_compute; reflexivity | rc3 | reflexivity | lia | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc 0x24d60 25 64 | lit_bytes 0x24d60 24%nat | lia | unfold EX_COST; lia | ].
    intros c6 X6. xn X6.
    eapply (x_run Q 0xf8edc _ EX_SF _ _ APUT_U64 _ EX_SF c6 X6);
      [xseg0 (@nil bool) [APUT_U64] (kT 72 (EVar 57)); [ first [ kTg | xclose ] .. | xseg_done ] |].
    intros c7 X7. xn X7.
    eapply (x_u64 HU64 Q _ EX_SF _ _ 0xf8ef4 ((x_widx e - x_ioff e) mod 2 ^ 64) c7 X7);
      [vm_compute; reflexivity | rc1w wsub_val | reflexivity | lia
      | apply Z.mod_pos_bound; lia | lia | unfold EX_COST; lia | ].
    intros c8 X8. xn X8.
    eapply (x_run Q 0xf8ef4 _ EX_SF _ _ APUT_CSEQ _ EX_SF c8 X8); [xseg [APUT_CSEQ] |].
    intros c9 X9. xn X9.
    eapply (x_cseq HCSEQ Q _ EX_SF _ _ 0xf8f08 0x244a0 1 c9 X9);
      [vm_compute; reflexivity | rc3 | reflexivity | lia | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc 0x244a0 2 32 | lit_bytes 0x244a0 1%nat | lia | unfold EX_COST; lia | ].
    intros c10 X10. xn X10.
    eapply (x_run Q 0xf8f08 _ EX_SF _ _ ADS_DTOR _ EX_SF c10 X10);
      [xseg0 (@nil bool) [ADS_DTOR] [KWord (SA (EVar 52) 392) 4 (ELit 4294967292)];
         [ first [ kDs | xclose ] .. | xseg_done ] |].
    intros c11 X11. xn X11.
    eapply (x_dtor HDTOR Q _ EX_SF _ _ c11 X11); [vm_compute; reflexivity | rc0 | unfold EX_COST; lia | ].
    exact K.
  Qed.
End ExP2c.
