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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_PmBase LbB_FSlots LbB_Regs LbB_PmEntry.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmEntry2 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:map_repeatK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z8lt_transK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8srl3_valK47Corelib7Numbers7BinNums8positive01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3divC4ELinuxProcessSemantics5Riscv3Sem5alu64C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z8add_commC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec=bv_wrap64_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00K47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PmEntry4pmS1C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3fszC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappK47Corelib4Init9Datatypes3nat02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow<poison_bytesC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4SHADK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell05K47Corelib4Init7Decimal4uint06K47Corelib4Init7Decimal4uint05K47Corelib4Init7Decimal4uint08K47Corelib4Init7Decimal4uint03K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01I47Corelib4Init5Logic2ex00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invI47Corelib4Init9Datatypes6option00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_MPRESC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullI47Corelib4Init9Datatypes4prod00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6pm_fshC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMStateCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init9Datatypes3appC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BellsX<rw_cells_appC47Corelib4Init5Logic5proj1C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells8cells_atK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedK45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6reg_evK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem8bytes_atC47Corelib4Init9Datatypes6lengthC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2b8C47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List=repeat_lengthC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<kwr_of_wr_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv:kwr_of_stkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit9estart_shC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond02C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotK4ARocqVerifyHarness?AgentSubmission8PropExec7FPState01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib7syms_idC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib=syms_id_soundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit6othersC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit7fsh_patK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6to_natC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit6lbytesC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26e_addrC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28expr_eqbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit:sym_insideC47Corelib4Init9Datatypes3orbC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC56Stdlib6NArith6BinNat1N3ltbC56Stdlib6ZArith6BinInt1Z4of_NC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7aapp_loC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7aapp_hiK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission8SymExec33SX27e_widthC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit?lmiss_of_othersC47Corelib5Lists7ListDef3mapC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BArr5u8arrC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit?u8arr_mem_denotI47Corelib5Lists7ListDef6Forall00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit8num_winsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots<omiss_of_symC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C47Corelib4Init5Logic7f_equalC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots=rdn_slot_someC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots<rw_C8_of_rdnC46Stdlib5Lists4List9nth_errorC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots<rw_cells_C8sC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3mrdC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit9munch_symC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge7mkst_MSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<asan_rt_hypsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCasan_rt_hyps_bp_extC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCalloc_ok_of_live_bpC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface9RHEAP_ahmC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceAannotate_gen_stmtC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface7cost_bpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge9rfull_mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge>msteps_mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv=stk_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs:getr_mkR_2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs:getr_mkR_8C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs:getr_mkR_9C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs;getr_mkR_18C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs;getr_mkR_19C45stdpp9bitvector;definitions6bv_andC45stdpp9bitvector;definitions9bv_shiftrC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C45stdpp9bitvector;definitions?bv_and_unsignedC45stdpp9bitvector;definitionsBbv_shiftr_unsignedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs;getr_mkR_20C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs;getr_mkR_21C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs;getr_mkR_22C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs;getr_mkR_27c6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_PmEntry2;sh_expr_valC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs;getr_mkR_26C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots5omissC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call6inb_InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs:getr_mkR_3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs:getr_mkR_4C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs;getr_mkR_23C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs;getr_mkR_24C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Regs;getr_mkR_25C6ARocqVerifyHarness?AgentSubmission3bpB3Lib6LbB_SR6sr_blkC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr03C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots5lwordC46Stdlib5Lists4List7forallbK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC4ARocqVerifyHarness?AgentSubmission8PropExec3rdnC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec4getrI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsK47Corelib4Init5Logic4True01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PmEntry9PM_SM8_RAC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AFS_HDRK47Corelib4Init7Decimal4uint01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_PmEntry28PM_E2_PCC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8PM_MAGICC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7PM_DESCC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PmEntry8PM_ENTRYI47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idK47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7PM_OBJSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6PM_NSHC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9ALOWSH_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOC5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segments".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma sh_expr_val : forall E e x (s6 : expr), edenot E e = Z_to_bv 64 x -> edenot E s6 = Z_to_bv 64 SHBASE -> 0 <= x < 2 ^ 47 ->
  edenot E (EAlu ALU_ADD (EAlu ALU_SRL e (ELit 3)) s6) = Z_to_bv 64 (sh x).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmEntry2 ()) [] "h01zh12Hah27__sat66h37__sat68h41Hh54__p1h64__x1h77__arithh84__ffh97__sat65h:7__sat67h;7__sat69h<8__varmaph=5__with>7__sat70h?2b1h@2b2hA1nhB1EhC2HehD2HshE2HxhF4Hx64hG2S3hH7__sat71hI1ahJ1bhK1ehL2s6hM1xp;1p;2p;3p;5p;4p;6p;7p;8p10000p4p7210R0p1000\p4p710p8P0g0018R0p4p710R1p8p1001Vp4p7210P1p8g0025j1=Tg002Zj1GTg0038j1<Tg003[j2?Tg004Sj2BTg0059j39Tg005Sj1;Tg0061j2ITg006Nj21Tg006jR1j2>Tg007Ej2CTg007_j5rTg008Aj4MTg008\j5kTg009Yj1HTg00:>j1fTg00;6j3OTg00;nj24Tg00<Xj2ATg00=5j3^Tg00=]j1NTg00>Tj3]Tg00?8j3\Tg00?]j23Tg00@:j2:Tg00@`j27Tg00A@j2[Tg00B1j2FTg00BYj3ETg00C=j2ZTg00C^j1YTg00D>j1XTg00D^j2WTg00E<j1VTg00EZj1UTg00FEj2DTg00Fhj2sTg00GKj4TTg00H6j6qTg00HZj1pTg00I<j2oTg00I^j2nTg00JJj3jTg00Jij4iTg00K[j1hTg00L9j4gTg00LZj3PTg00M=j3eTg00M`j2cTg00N=j5dTg00Nij2bTg00OKj1KTg00PSj2QTg00QBj3aTP0j6LTg00R0j2`Tg00RLj7lTg00S0j7mTg00STj8_Tf0R0#=#=p=5g00T8R2/`0p=0%H0#Hp=6g00TVR3f1R4;90p=2P4g00U4R5g00USR6P6g00V3R7P0g00VSFlp=@f2R8P5P6P6P7P4P0Fmp=Sf3R9P5P6P6P7P8P4P0G_p=RP3P4g00W3P0CTp=JP3f4R:P9P8P4P0ELp=8g00WZg00XQR;g00YIR<#=R=#5R>#=#5R?#GR@#<RA1?981B@4391?:4g00YnRB,B@RC59A%09%;=RD%6=R=#6RE#;RF'IRG,19'>%0:RH%;?R?,IDRI,1:RJP1PH11:GRKf5RL#0P0P4n2001000000120000000PHP0b4P:PGPIP1PHPK11LGP0P0n2001000000120000000PKP0b4g00ZiRKg00[O'CDrCM1>HJf7RJf6RHPLP9P0Dkg00\5RM%H<RN#;#fRO7OH,?J,4@%;>R>,AL'2f8RLAOMJO'?PAPAPCg00\a?^40%NLRO,B@RM59AXJAg00]MRA%<0RP%<4RQP1%<8?94014981494'2R1[14841480'2%<9?984[RR%<:?998\1A]840P0n2001000000120000000W@W?WAPR^@Q^?P^AAP0P@A\@4CRAPM14@4RP14@CRQ'3,:@f9RR#NR1,B@,4@RS,20X031AL>RT130Q,:@/2SX031:@BRU1AR>RV/30RW,:@/2SX031:@ORS13VU,:@/20X0313TURX/7I1:@1R1,20X0317BIRY17WI/21X0317OIR113VY/7I/20X03%0TRW%5=R=#;RZ,IDR[,1TR\PLP>1[L>R]%0L%0>f:/A>R^#0[[R_1FDFR`112DRa%0F112G[Rb[Rc%0DRdg00]kReAEDF4UW1RF%0G\e^1dRf1FD?Rg%0?112I[Rh\aRiAED?4VeX1dR?%0I\e^1dRjP41Z2D,CKPaeRKO1RkPhP:PKO1RlPbp-0Rmg00^GRn#YRo%XnRn1W34Rp%V3Rq%U3RrP31D32Rsg00_31s3<R<CT,@rRtPrP5P6P6P7P9EqR95Sr%p6R6PtCR1or7R7P0P8g00_ZRtg00`:R5'C1n08=9t5dAj324CiR5b8b<b=X63W5%00/>4%04[^63^5mP0f@Rt/1GPtf<O3b7b3b2b9b2b:b3b;P]P_P`PcPFPfPgPiP?PjPkPhPlPbPoPn%h3Pq1D3>Rt,Js,@rP7P5b8b<b=112>P0b7b3b2b9b2b:b3b;RsCgPLP>P[PsP]P_1FDZ%0Z112[[R2\aAEDZ4VeX1d%0[\e^1dP`PcPFPfPgPiP?PjPkPhPlPbPJPKO1P2PoPnPpPqPr1D3DRD%GE5P3,J<,@r9Sr9P6%G=9P3D9e3t,J<,@rCRP7P5b8b<b=X63X5m110G,>41c>[,14[^63^5mP0fCRm#0Pmf?O3b7b>b3b2b9b2b:b3b;b>bHDdCM1>W\%6N#6#6#6#6#6#6#=#5#5#5#5#5#5#5#;RN/3VR\170I13N^/7I'2X0317\I,C313VN1bVND8b413TY/7I/21ePS%KOD8PU%KBD81:@X%KXD814@M1Q@OD8PQ1Q@BD8PPP8D814@AAa@4CD8O4b41?RHP:ELbIbGbFWEWDWCXL;XM3WKWBo"). Qed.

Lemma wr_at_sub8 : forall m A n k, wr_at asegs m A n -> 0 <= k -> k + 8 <= n -> wr_at asegs m (A + k) 8.
Proof. intros m A n k (W0 & W1 & W) Hk Hkn. split; [lia|]. split; [lia|]. intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply W. lia. Qed.

Section Entry2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.

  Definition PM_E2_PC : Z := 0xf069c.

  Definition E2_SR : list expr :=
    srs sr_id [(10%bv, EVar 33); (2%bv, EVar 35); (9%bv, EVar 35); (8%bv, EVar 34); (23%bv, EVar 32); (25%bv, ELit SHBASE)].
  Definition E2_FSHB : expr := EAlu ALU_SRL (EVar 33) (ELit 3).
  Definition E2_KN : list kentry :=
    [ KRange (EVar 33) (AIMG_TOP + AFS_HDR) (2 ^ 47); KAlign (EVar 33) 64;
      KRange (EVar 35) (2 ^ 20) (2 ^ 47); KAlign (EVar 35) 32; KRange (EVar 32) 1 (2 ^ 47);
      KWr (SA (EVar 33) 0) (ELit 24); KWr (SA (EVar 35) 680) (ELit 8); KWr (SA E2_FSHB SHBASE) (ELit 1448) ].
  Definition E2_WINS : list (expr * Z * Z) := [(EVar 35, 680, 688); (EVar 33, 0, 24); (E2_FSHB, SHBASE, SHBASE + 1448)].

  Lemma pm_e2 : forall (sp gp tp s2 s3 s4 s5 s6 s8 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (p ff fp lo : Z) (Q : config -> Prop),
    let spz := bv_unsigned sp in let S1 := pmS1 spz in
    as_VIS H s msF = MS (mkR (Z_to_bv 64 PM_SM8_RA) (Z_to_bv 64 S1) gp tp t0 t1 t2 sp (Z_to_bv 64 S1) (Z_to_bv 64 ff)
                             a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 p) s8 (Z_to_bv 64 SHBASE) s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 PM_SM8_RA) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) ->
    stk asegs m lo spz -> aceil <= lo -> lo <= spz - 32768 -> spz mod 16 = 0 -> spz <= 2 ^ 47 ->
    AIMG_TOP + AFS_HDR <= ff -> ff + fsz 8 <= aceil -> ff mod 64 = 0 -> aapp ff (fsz 8) ->
    SHAD m ff (poison_bytes 1448 0) -> (exists j1 j2, rw_cells asegs m ff [CB 24 j1; C8 (Z_to_bv 64 S1); CB 16344 j2; C8 (Z_to_bv 64 fp)]) ->
    0 < p -> p + 288 <= aceil -> mem_inv asegs m ->
    (forall msF1 mo1 m1 (R1 : bvmap 5 word),
       as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 PM_E2_PC) fc None m1 (seg_rom asegs) -> rfull R1 ->
       munch [(S1 + 680, S1 + 688); (ff, ff + 24); (sh ff, sh ff + 1448)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       stk asegs m1 lo spz ->
       SHAD m1 ff (pm_fsh []) ->
       rw_cells asegs m1 ff [C8 (Z_to_bv 64 PM_MAGIC); C8 (Z_to_bv 64 PM_DESC); C8 (Z_to_bv 64 PM_ENTRY)] ->
       rw_cells asegs m1 (S1 + 680) [C8 (Z_to_bv 64 ff)] ->
       getr R1 2 = Z_to_bv 64 S1 -> getr R1 8 = sp -> getr R1 9 = Z_to_bv 64 S1 -> getr R1 18 = Z_to_bv 64 ff ->
       getr R1 23 = Z_to_bv 64 p -> getr R1 20 = Z_to_bv 64 (sh ff) -> getr R1 10 = Z_to_bv 64 (p + 80) ->
       getr R1 25 = Z_to_bv 64 SHBASE -> getr R1 16 = Z_to_bv 64 ff -> getr R1 11 = Z_to_bv 64 (sh (p + 80)) ->
       getr R1 3 = gp -> getr R1 4 = tp ->
       getr R1 19 = s3 -> getr R1 21 = s5 -> getr R1 22 = s6 -> getr R1 24 = s8 -> getr R1 26 = s10 -> getr R1 27 = s11 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros until Q. intros spz S1 VIS KR ST CE LO SP16 SP47 FF1 FF2 FF64 FAPP SH0 HDR P0 P1 MI K.
    assert (ES1 : S1 = pmS1 spz) by reflexivity. assert (Espz : spz = bv_unsigned sp) by reflexivity. clearbody S1 spz.
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr. rewrite <- Espz in Hspr.
    assert (Hsp : sp = Z_to_bv 64 spz) by (rewrite Espz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    change (fsz 8) with 16384 in *.
    assert (S1r : spz - 864 <= S1 <= spz - 832 /\ S1 mod 32 = 0).
    { rewrite ES1. unfold pmS1. pose proof (Z.mod_pos_bound (spz - 832) 32 ltac:(lia)). split; [lia|].
      pose proof (Z.div_mod (spz - 832) 32 ltac:(lia)). Z.div_mod_to_equations. lia. }
    assert (SHf : sh ff = ff / 8 + SHBASE) by (unfold sh, SHBASE; rewrite ASHADOW_BASE_val; lia).
    assert (FFb : 0 <= ff < 2 ^ 64) by (unfold AIMG_TOP, AFS_HDR in FF1; lia).
    destruct HDR as (j1 & j2 & HDR).
    pose proof (rw_cells_wr_at _ _ _ _ 24 HDR ltac:(cbn; lia)) as WH.
    destruct SH0 as (SA0 & SA8 & U0).
    assert (LZ : length (poison_bytes 1448 0) = 1448%nat) by (vm_compute; reflexivity).
    pose proof (proj2 U0) as WS. rewrite LZ in WS. change (Z.of_nat 1448) with 1448 in WS.
    assert (DSF : sh ff + 1448 <= ff \/ ff + 16384 <= sh ff).
    { rewrite SHf. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in FAPP. unfold SHBASE. clear - FAPP ACF1 ACF2 ACF3 ACF4 FFb. Z.div_mod_to_equations. lia. }
    assert (DSS : sh ff + 1448 <= S1 + 680).
    { rewrite SHf. unfold SHBASE. clear - FFb FF2 CE LO S1r ACF1 ACF2 ACF3 ACF4. Z.div_mod_to_equations. lia. }
    remember (mkR (Z_to_bv 64 PM_SM8_RA) (Z_to_bv 64 S1) gp tp t0 t1 t2 sp (Z_to_bv 64 S1) (Z_to_bv 64 ff)
                  a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 p) s8 (Z_to_bv 64 SHBASE) s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 ff; Z_to_bv 64 spz; Z_to_bv 64 S1]).
    assert (E32 : edenot E (EVar 32) = Z_to_bv 64 p) by (subst E; reflexivity).
    assert (E33 : edenot E (EVar 33) = Z_to_bv 64 ff) by (subst E; reflexivity).
    assert (E34 : edenot E (EVar 34) = Z_to_bv 64 spz) by (subst E; reflexivity).
    assert (E35 : edenot E (EVar 35) = Z_to_bv 64 S1) by (subst E; reflexivity).
    assert (EB : bv_unsigned (edenot E E2_FSHB) = ff / 8) by exact (srl3_val E (EVar 33) ff E33 FFb).
    assert (HR : regs_ok E E2_SR R).
    { unfold E2_SR. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity; exact Hsp. }
    assert (HK : know_ok asegs E m E2_KN).
    { unfold E2_KN, know_ok.
      apply Forall_cons. { cbn [kentry_ok]. rewrite E33, u64_of_Z by exact FFb. clear - FF1 FF2 ACF1 ACF2 ACF3 ACF4. unfold AIMG_TOP, AFS_HDR in *. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite E33, u64_of_Z by exact FFb. split; [lia | exact FF64]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite E35, u64_of_Z by lia. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite E35, u64_of_Z by lia. split; [lia | exact (proj2 S1r)]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite E32, u64_of_Z by lia. lia. }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WH | | | ]; unfold estart, elenZ; cbn [a_base a_off]; rewrite ?E33; cbn [edenot]; rewrite ?u64_of_Z by lia; lia. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | | | ]; unfold estart, elenZ; cbn [a_base a_off]; rewrite ?E35; cbn [edenot]; rewrite ?u64_of_Z by lia; lia. }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WS | | | ]; unfold estart, elenZ; cbn [a_base a_off]; rewrite ?EB; cbn [edenot]; rewrite ?u64_of_Z by lia; rewrite ?SHf; lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R PM_SM8_RA m (seg_rom asegs) HR HK 1600%nat [PM_E2_PC] (SCR [] [] []) 36%N.
    { split_scs. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms; set (LOG1 := lg) in Hlf, M1 end end.
    rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 10%bv G10. rreg HR' 11%bv G11.
    rreg HR' 16%bv G16. rreg HR' 18%bv G18. rreg HR' 20%bv G20. rreg HR' 23%bv G23. rreg HR' 25%bv G25.
    assert (GK : forall r, In r [3; 4; 19; 21; 22; 24; 26; 27]%bv -> getr R' r = getr R r).
    { intros r Hr. lazymatch type of HR' with regs_ok (Eseed R ?vals) ?sr' R' =>
        exact (syms_id_sound R vals sr' R' [3; 4; 19; 21; 22; 24; 26; 27]%bv HR' ltac:(vm_cast_no_check (@eq_refl bool true)) r Hr) end. }
    set (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 ff; Z_to_bv 64 spz; Z_to_bv 64 S1]) in *.
    assert (SYM : forallb (sym_inside E2_WINS) LOG1 = true) by (subst LOG1; vm_cast_no_check (@eq_refl bool true)).
    assert (WINS : num_wins E E2_WINS = [(S1 + 680, S1 + 688); (ff, ff + 24); (sh ff, sh ff + 1448)]).
    { unfold num_wins, E2_WINS. cbn [map]. rewrite E35, E33, EB, !u64_of_Z by lia. rewrite SHf, Z.add_0_r, (Z.add_assoc (ff / 8)). reflexivity. }
    assert (INS : forall se, In se LOG1 ->
              (expr_eqb (a_base (e_addr se)) (EVar 35) = true /\ S1 + 680 <= estart E (e_addr se) /\ estart E (e_addr se) + Z.of_nat (e_width se) <= S1 + 688)
              \/ (expr_eqb (a_base (e_addr se)) (EVar 33) = true /\ ff <= estart E (e_addr se) /\ estart E (e_addr se) + Z.of_nat (e_width se) <= ff + 24)
              \/ (expr_eqb (a_base (e_addr se)) E2_FSHB = true /\ sh ff <= estart E (e_addr se) /\ estart E (e_addr se) + Z.of_nat (e_width se) <= sh ff + 1448)).
    { intros se Hse. pose proof (proj1 (forallb_forall _ _) SYM se Hse) as HS. unfold E2_WINS, sym_inside, sym_in1 in HS.
      rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in HS. unfold estart.
      destruct HS as [((Hb & H1) & H2)|[((Hb & H1) & H2)|[((Hb & H1) & H2)|HF]]]; [left | right; left | right; right | discriminate].
      - pose proof (expr_eqb_true _ _ Hb) as Hb'. rewrite Hb', E35, u64_of_Z by lia. split; [vm_compute; reflexivity | lia].
      - pose proof (expr_eqb_true _ _ Hb) as Hb'. rewrite Hb', E33, u64_of_Z by lia. split; [vm_compute; reflexivity | lia].
      - pose proof (expr_eqb_true _ _ Hb) as Hb'. rewrite Hb', EB, SHf. split; [vm_compute; reflexivity | lia]. }
    assert (MU1 : munch [(S1 + 680, S1 + 688); (ff, ff + 24); (sh ff, sh ff + 1448)] m M1).
    { rewrite <- WINS. subst M1. exact (munch_sym E m LOG1 E2_WINS Hlf SYM). }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (OM33 : forall y, ff <= y -> y + 8 <= ff + 24 -> Forall (omiss E (EVar 33) y 8) LOG1).
    { intros y Hy1 Hy2. apply Forall_forall. intros se Hse Hne. destruct (INS se Hse) as [(Hb & I)|[(Hb & I)|(Hb & I)]];
        [lia | rewrite Hb in Hne; discriminate | lia]. }
    assert (OM35 : Forall (omiss E (EVar 35) (S1 + 680) 8) LOG1).
    { apply Forall_forall. intros se Hse Hne. destruct (INS se Hse) as [(Hb & I)|[(Hb & I)|(Hb & I)]];
        [rewrite Hb in Hne; discriminate | lia | lia]. }
    rewrite !mkst_MS in Hms. subst R.
    eapply (sr_blk H (HH H HHbp)); [exact KR | exact VIS | apply rfull_mkR | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (K msF1 mo1 M1).
    - exact KR1.
    - exact MP1.
    - exact VIS1.
    - apply rfull_mkR.
    - exact MU1.
    - exact WM1.
    - exact MI1.
    - exact ST1.
    - split; [lia|]. split; [lia|].
      unfold pm_fsh. replace (sh ff) with (bv_unsigned (edenot E E2_FSHB) + SHBASE) by (rewrite EB, SHf; reflexivity).
      assert (PZ : poison_bytes 1448 0 = map (Z_to_bv 8) (repeat 0 1448%nat)) by (vm_compute; reflexivity).
      rewrite PZ in U0.
      eapply (u8arr_mem_denot E m LOG1 E2_FSHB SHBASE (repeat 0 1448%nat) _ Hlf).
      + intros i Hi. apply Forall_forall. intros se Hse. unfold lmiss.
        destruct (expr_eqb (a_base (e_addr se)) E2_FSHB) eqn:Eb; [left; reflexivity|]. right.
        rewrite repeat_length in Hi. change (Z.of_nat 1448) with 1448 in Hi. rewrite EB.
        destruct (INS se Hse) as [(Hb & I)|[(Hb & I)|(Hb & I)]]; [lia | lia | rewrite Hb in Eb; discriminate].
      + rewrite EB. unfold SHBASE. Z.div_mod_to_equations. lia.
      + rewrite EB, repeat_length. change (Z.of_nat 1448) with 1448. unfold SHBASE. Z.div_mod_to_equations. lia.
      + rewrite EB, <- SHf. exact U0.
      + subst LOG1. vm_compute. reflexivity.
    - assert (WH1 : wr_at asegs M1 ff 24) by exact (wr_at_transport asegs m M1 ff 24 WH WM1).
      change ([C8 (Z_to_bv 64 PM_MAGIC); C8 (Z_to_bv 64 PM_DESC); C8 (Z_to_bv 64 PM_ENTRY)]) with (map C8 [Z_to_bv 64 PM_MAGIC; Z_to_bv 64 PM_DESC; Z_to_bv 64 PM_ENTRY]).
      apply rw_cells_C8s; [lia | cbn; lia |]. intros i x Hx.
      do 3 (destruct i as [|i]; [ cbn in Hx; injection Hx as <-;
        apply rw_C8_of_rdn; [lia | lia | | apply (wr_at_sub8 _ _ _ _ WH1); cbn; lia ];
        match goal with |- PropExec.rdn _ _ (Z_to_bv 64 (ff + 8 * Z.of_nat ?k)) _ = _ =>
          let kk := eval cbn in (8 * Z.of_nat k) in
          let v := eval vm_compute in (lword LOG1 (EVar 33) kk) in
          lazymatch v with Some (Some ?ve) =>
            replace (ff + 8 * Z.of_nat k) with (bv_unsigned (edenot E (EVar 33)) + kk) by (rewrite E33, u64_of_Z by lia; cbn; lia);
            unfold M1; rewrite (rdn_slot_some asegs E m LOG1 (EVar 33) kk ve Hlf
                                 (OM33 (bv_unsigned (edenot E (EVar 33)) + kk) ltac:(rewrite E33, u64_of_Z by lia; lia) ltac:(rewrite E33, u64_of_Z by lia; lia))
                                 ltac:(vm_cast_no_check (@eq_refl _ v))
                                 ltac:(rewrite E33, u64_of_Z by lia; lia) ltac:(rewrite E33, u64_of_Z by lia; lia));
            reflexivity
          end
        end | ]).
      destruct i; cbn in Hx; discriminate.
    - assert (WS1 : wr_at asegs M1 (S1 + 680) 8).
      { pose proof (wr_at_of_stk _ _ _ _ ST1) as W. replace (S1 + 680) with (lo + (S1 + 680 - lo)) by lia.
        apply (wr_at_sub8 _ _ _ _ W); lia. }
      apply rw_C8_of_rdn; [lia | lia | | exact WS1].
      lazymatch eval vm_compute in (lword LOG1 (EVar 35) 680) with Some (Some ?ve) =>
        replace (S1 + 680) with (bv_unsigned (edenot E (EVar 35)) + 680) by (rewrite E35, u64_of_Z by lia; lia);
        unfold M1; rewrite (rdn_slot_some asegs E m LOG1 (EVar 35) 680 ve Hlf ltac:(rewrite E35, u64_of_Z by lia; exact OM35) ltac:(vm_cast_no_check (@eq_refl (option (option expr)) (Some (Some ve))))
                               ltac:(rewrite E35, u64_of_Z by lia; lia) ltac:(rewrite E35, u64_of_Z by lia; lia));
        rewrite ?E33; reflexivity
      end.
    - etransitivity; [reflexivity|]. rewrite G2. exact E35.
    - etransitivity; [reflexivity|]. rewrite G8. exact (eq_trans E34 (eq_sym Hsp)).
    - etransitivity; [reflexivity|]. rewrite G9. exact E35.
    - etransitivity; [reflexivity|]. rewrite G18. exact E33.
    - etransitivity; [reflexivity|]. rewrite G23. exact E32.
    - etransitivity; [reflexivity|]. rewrite G20. exact (sh_expr_val E (EVar 33) ff (ELit SHBASE) E33 eq_refl ltac:(lia)).
    - etransitivity; [reflexivity|]. rewrite G10. change (edenot E (EAlu ALU_ADD (EVar 32) (ELit 80)) = Z_to_bv 64 (p + 80)).
      transitivity (alu64 ALU_ADD (Z_to_bv 64 p) (Z_to_bv 64 80)); [rewrite <- E32; reflexivity | apply w_add; lia].
    - etransitivity; [reflexivity|]. rewrite G25. reflexivity.
    - etransitivity; [reflexivity|]. rewrite G16. exact E33.
    - etransitivity; [reflexivity|]. rewrite G11. assert (EA : edenot E (EAlu ALU_ADD (EVar 32) (ELit 80)) = Z_to_bv 64 (p + 80)).
      { transitivity (alu64 ALU_ADD (Z_to_bv 64 p) (Z_to_bv 64 80)); [rewrite <- E32; reflexivity | apply w_add; lia]. }
      exact (sh_expr_val E _ (p + 80) (ELit SHBASE) EA eq_refl ltac:(lia)).
    - etransitivity; [reflexivity|]. rewrite (GK 3%bv ltac:(inb)). reflexivity.
    - etransitivity; [reflexivity|]. rewrite (GK 4%bv ltac:(inb)). reflexivity.
    - etransitivity; [reflexivity|]. rewrite (GK 19%bv ltac:(inb)). reflexivity.
    - etransitivity; [reflexivity|]. rewrite (GK 21%bv ltac:(inb)). reflexivity.
    - etransitivity; [reflexivity|]. rewrite (GK 22%bv ltac:(inb)). reflexivity.
    - etransitivity; [reflexivity|]. rewrite (GK 24%bv ltac:(inb)). reflexivity.
    - etransitivity; [reflexivity|]. rewrite (GK 26%bv ltac:(inb)). reflexivity.
    - etransitivity; [reflexivity|]. rewrite (GK 27%bv ltac:(inb)). reflexivity.
  Qed.
End Entry2.
