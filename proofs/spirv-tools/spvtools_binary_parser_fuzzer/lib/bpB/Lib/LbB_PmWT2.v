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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmGlue LbB_PmVops LbB_PmHdr LbB_PmLH LbB_PmOL LbB_TablStmt LbB_DiagStmt LbB_PmDS LbB_PmWEx LbB_PmWords LbB_PmU2K LbB_PmWT1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmOLX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmWT2 () := "C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedC4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT2:w_add_lit2K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03I5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00C4ELinuxProcessSemantics5Riscv3Sem7mul_divC56Stdlib6ZArith6BinInt1Z3mulC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PmWords:w_mul_litAK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05K4ELinuxProcessSemantics5Riscv5Instr5mulop01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<asan_rt_hypsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCasan_rt_hyps_bp_extC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCalloc_ok_of_live_bpC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface9RHEAP_ahmC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceAannotate_gen_stmtC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface7cost_bpC47Corelib4Init5Logic5proj1I6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4pmwA00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn7pmw_okA00I47Corelib4Init9Datatypes4prod00I6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5PMXAT00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K7ffkeepXK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9regs_tblXK45stdpp9bitvector;definitions2bv01C4ARocqVerifyHarness?AgentSubmission8PropExec4getrC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_gpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_tpC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase6c_widxC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_icountC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_endianC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase9c_reqconvC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_nC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9set_scalAc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT28tl_headKC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7pm_geomC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_ffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_s1C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_loC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6wa_sp0C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac:pmw_boundsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_consC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8wa_wordsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn4wk_nC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7xa_scalC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut>env_world_seedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9env_worldK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry05K47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut:pm_kn_baseC47Corelib4Init9Datatypes3appK5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut<regs_tbl_extC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6xboundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7tbl_okXK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut:tbl_closedC47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7keys_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut8fkeys_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut=pm_kn_base_okC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac8pmk_sh_pK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit:sym_insideC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC46Stdlib5Lists4List7forallbI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit7fsh_patC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit6lbytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots9upd_slotsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots9add_slotsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut=sr_tbl_checkXC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7scal_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots6lfieldC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots4svalK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut:scal_afterC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_blocksC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase=pm_phi_blocksC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8pm_progzC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase=pm_progz_stepC47Corelib4Init5Logic6eq_indC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6pm_phiC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCutAregs_tbl_restrictC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sr_getC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac<ev_world_allC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_userC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_diagC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit9munch_symC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit8num_winsC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC56Stdlib6ZArith6BinInt1Z3divC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8srl3_valC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac<pmw_apart_ffC47Corelib4Init5Logic3notC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops<ffkeep_munchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K;ffkeepX_nilC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List2InC46Stdlib5Lists4List4inclC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K=ffkeepX_transI47Corelib4Init5Logic2or00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9wenv_valsC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula06C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut8pm_runSXC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEK4ELinuxProcessSemantics5Riscv5Instr5aluop07I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00I5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase3pmc00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT23HHmC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6S_OPERC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL9TBL_EEF44C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL6RT_OLJC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7S_INSTRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL8RT_EEF44C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockC4ARocqVerifyHarness?AgentSubmission8LibIface3memI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7PM_STRKc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT26TL_FFXC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsK47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AFS_HDRK47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL7OL_HEADI5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI46Stdlib5Lists4List6Exists00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6PM_OWNC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut4FSHBC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7PM_OBJSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6PM_NSHC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5WV_S1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5WV_FFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4WV_PC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase7O_FLAGSC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase6O_WIDXC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8O_ICOUNTC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8O_ENDIANC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase:PM_RESERVEC5ARocqVerifyHarness?AgentSubmission6LibPrs6PrsInv;PARSER_SIZEI47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt5sx32AK46Stdlib9micromega=RingMicromega3Op201C4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroC5ARocqVerifyHarness?AgentSubmission6LibPrs9PmODefsS14i_opC5ARocqVerifyHarness?AgentSubmission6LibPrs9PmODefsS14i_ioC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_trC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase6pm_budK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell03C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL6ipureAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL7CHECKKAc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT27tl_cutLC5ARocqVerifyHarness?AgentSubmission6LibPrs9PmODefsS1<ipure_rangesC5ARocqVerifyHarness?AgentSubmission6LibPrs9PmODefsS15i_iwcC5ARocqVerifyHarness?AgentSubmission6LibPrs9PmODefsS14i_fwC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmHdr4WADDC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac6ev_addC47Corelib4Init5Logic6eq_symC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut<regs_tbl_appC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac=pmk_scal_widxI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells6cbytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvAkword_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission7LibCont4CRep3fldC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8xa_flagsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut<kword_of_fldK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr07C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K=edenot_zext16c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT27ev_add2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT27ev_mul4K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6NArith6BinNat1N3lebC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac8ev_xseedK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond01C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6br_geuC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9scal_noneC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall;keys_nonnegC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue6rt_getC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC46Stdlib5Lists4List9in_or_appC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS9regs_keepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS7rt_keepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call6inb_InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWEx<pm_exhaustedC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K<ffkeepX_reflc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT26tl_finK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z7add_0_rc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT2;sx32A_smallC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K=edenot_sext32C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac?pmk_scal_endianC4ELinuxProcessSemantics5Riscv3Sem<branch_takenC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5br_eqc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT26ev_litC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH7rt_subbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH<regs_tbl_subC5ARocqVerifyHarness?AgentSubmission6LibPrs:PrsGrammar4g_opC5ARocqVerifyHarness?AgentSubmission6LibPrs9PmODefsS13i_lC5ARocqVerifyHarness?AgentSubmission6LibPrs9PmODefsS13i_dC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt6idescAC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib5Lists4List9nth_errorC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue9rt_lookupC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6pm_runK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission7LibTabl;TablGrammar2TGC5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt:AEXHAUSTEDK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K47Corelib4Init9Datatypes4bool02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface9APC0_FREEc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT25RT_B0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT26RT_EXHc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT25RT_L0I5ARocqVerifyHarness?AgentSubmission6LibPrs9PmODefsS15ictxR00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT16RT_TLAI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C46Stdlib9micromega8ZifyInst7Inj_Z_Zc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT2<HTLbAPmWT2_0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt;PM_DTOR_RASC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt:PM_EXH_RASC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt5PM_PFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall9KEPT_REGSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL8OL_CHECKc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT2<HTLbAPmWT2_1c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT2<HTLbAPmWT2_2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT2<HTLbAPmWT2_3K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT28RT_LOOPC".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma w_add_lit2 : forall a b, 0 <= a -> 0 <= b -> a + b < 2 ^ 64 -> alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmWT2 ()) [] "h01zh16__sat1h24__x1h34__x2h42Hah57__arithh64__ffh76__sat0h88__varmaph95__with:2b1h;2b2h<1nh=1Hh>3Habh?2Hbh@1ahA1bp;2p;1p;3p;4p;7p;8p;6g0000j20Tg000Mj18Tg0012j1KTg001Pj2iTg001mj25Tg002Ij1:Tg002lj3<Tg003Fj22Tg0040j3STg004Tj1QTg0052j2=Tg005Xj3hTg006=j24Tg006cj2;Tg007Cj2CTg007]j2\Tg008Ej3[Tg008ij2ZTg009Jj1DTg009ij2?Tg00:Rj3>Tg00;;j2BTg00;gj1YTg00<Gj3ATg00<gj1XTg00=Gj2WTg00=ej1VTg00>Cj4UTg00>aj1TTg00??j1RTg00?jj2JTg00@Mj3HTg00A0j2ITg00ASj3PTg00B6j1OTg00BXj2gTg00C:j2fTg00Cfj3eTg00DEj4`Tg00E7R0j2LTg00ERj3ETg00F5j2GTg00Fdj3^Tg00GRj3]Tg00H:j2_Tg00HVj4MTg00IAj7aTg00Iej7bTg00JIj8cTg00Jmj6dTg00KKR1f0R2'_p=6g00KiR3f1R4;<2p=1P3P4g00LGP2CMp=FP4g00LnR5g00MMR6P6g00MmR7P2g00NMFap=9P3P4g00NmP2CMp=@f2R8P5P6P6P7P4P2Fbp=Nf3R9P5P6P6P7P8P4P2Gcp=3P3f4R5P9P8P4P2Edp=7%64R:1098g00OTR;#8R<#KR=%8<#8#8#8#8R>#KR?'iR@'5g00P9RA%:2RB%:4RCP0%:8?<4212981294'1R0[12841282'1%:9?<84[RD%:5?<98\0AS842P2n2001000000120000000W;W:W<PD^;C^:B^<AP2%Q>R>f5RA,=>RB1=>5RC5h>RD10A5R0,=>RE12>BRF12>CRG'0,4>f6RH/0ARI,=>,2>RJ,12X0314>ARK102F,4>/1JX0314>5RL14>HRM/02,4>/1JX0314>0RJ10MK,4>/12X03PA1;A@RM,02/;@1;I@RI'1X03P510H2/;@/1IX03P01122X031C301;0@1\=?RI151=RN%6?151@[RO[RP%6=RQg00PWRRA[=?4UW4R?%6@\R^4QRQP4g00Q31Z1='CPNeO1RNPOg00QYRRg00RERS#DRT#DRU,?3RV1?3T1?3SRS5>3RT5>3g00RdRW'B%YRRX3A%XRRYP31W38P4%V3CURZ%T3R[%R3R\1J3;R;1J3<R<5H3R]1I3==P3>R='F,9\R^%O6R6P\1I31R_/@<,9\R`P6P\1@_;,9\RaP61@_],9\=N\^C3C3C31g\7R7P2P8g00SPR_g00T0R]'C1f28=<_]dAe314C`R1b6b8b9X23X331024/5@R]%68R81095R_#615_@'L\8[[^23^33P2f8R_f9RbPAPHf7RcO5Rdb5b1b7b19E0@D71;5@PIPPP?PQPNPO%DU,?3RU=>3T/BW=ARXPYPZP[P\AH3<;/F=,9\P6P\PaP6P\P`P61F;=,9\9N\aR=C3C3C3P7P1b6b8b9X23X331042/5@%69R4159@,L4R4[\:[^23^33P2PbP_PAPHPcO5b5b1b7b19E5@D7PMPIPPP?PQPNPOA>3VS9>3U/BW=ARXPYPZP[P\P^P6P\P`P6P\PaP6P=C3C3C3P7P1b6b8b9X23X33P4\8\8\]^23^33Pdb5b1b7b19EA@D710KL,4>/1Je12>E1G>0D7PG1G>5D7PF1G>AD712>DA^>BCD7O4b=%:>g00TP1=>97]C1059,=>3<eW>X?:W4XA3X@3o"). Qed.
Lemma ev_add2 : forall E a b x y, edenot E a = Z_to_bv 64 x -> edenot E b = Z_to_bv 64 y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  edenot E (EAlu ALU_ADD a b) = Z_to_bv 64 (x + y).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmWT2 ()) [] "h06__sat1h14__x1h22Hah37__arithh46__sat0h51bh64__ffh78__varmaph85__with94__x2h:1Eh;2Hbh<2Hxh=3Hxyh>2Hyh?1ah@1xhA1yp;1p;2p;3p;4p;5p;6p;7p;8g000Mj14Tg004Tj1XTg002Ij1GTg00U<j22Tg0052j20Tg002lj33Tg0000j26Tg0012j1>Tg001Pj2ETg001mj25Tg00GRj3=Tg007]j2ATg008Ej3WTg008ij2UTg007Cj2@Tg00;gj1QTg00<gj1PTg00=Gj28Tg00>aj1MTg00??j1LTg00A0j2<Tg00?jj2;Tg00HVj49Tg00B6j1FTg00BXj2HTg00C:j2ITg00Cfj3JTg00DEj4KTg00=ej1DTg00>Cj4CTg00@Mj3NTg00ASj3BTg00V4j5OTg00Jmj6?Tg00W5j3RTg00H:j2STg00IAj7TTg00JIj8VTg00KKR0f0R1'Sp=1f1R2g00LnR3g00MMR4P4g00MmR5P1g00NMFTp=:f3R6P3P4P4P5f2R3P2P1GVp=7g00Wmg00XdR7g00KiR8g00OTR9#4R:#4#4#4#4#4R;#XR<#GR=f4R>/2610<2R?33f5R@/26=3=?%16R?16@>%>:RA%>;R;'ERB'5P=f6RC,0<g00TPRDf:REf8RF'27=1f7RG/6C,0<RH53=X5=P=10<@10<G==D1=3=HX5=PCP@1AA;RH150ARI%1;150B[RJ[RK%1ARLg00PWRMAWA;2UW2R;%1B\M^2LRLP2g00Q31U0A'@PIeO1RIPJg00QYRM#QRN%PMRM1882%M8RO%L8RPP81<80g00Nm1;89R9C9,:PRQ%F4R4PQC71HP5R5P1P3g00SPRQg00T0RR'@1I13=3QRdAJ802CKR0b6b7b8X18RR%11%12[^18RQP1PEPCO2b3b0b4b0PHPKP;PLPIPJPRPQP1f9RQP@O2b3b0b4b0PHPKP;PLPIPJPNPMP81883P2%D8CCPOPPP81;8:9N89g00LG1<8A=B8<C9,:PRPP4PPC7P5P0b6b7b8X18X981612/5B1623/5B[^18^98P1PQPEP>O3b3b0b4b0DO12QGP6E?12QFP>E?ARDFG,2Q16C@,0<53=eW=X>?W<W;W2XA8W@X57W?W:o"). Qed.
Lemma ev_mul4 : forall E a x, edenot E a = Z_to_bv 64 x -> edenot E (EMd M_MUL (ELit 4) a) = Z_to_bv 64 (4 * x).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmWT2 ()) [] "h01Eh12Hah21ah31bh41xp;1p;2p;3p;4p;6g000Mj10Tg004Tj1<Tg002Ij18Tg00U<j22Tg0052j21Tg002lj33Tg0012j1;Tg00Y\j47Tg00ZFj24Tg00Zcj26Tg00Jmj65Tg00[fj19Tg00\^j3:Tg00Wmg00Xdg00Kig00OT#0#0R0#0#0#0#0#<R1#8R2f2R3f1R4'2f0R5,1133P21114P1g00]VR6%;0R0,11P5C71403,11532X321604f3R7/23P5E5%90=:63,271404,11532eW1W4W2W0o"). Qed.
Lemma ev_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmWT2 ()) [] "h01Eh11zp;1p;2g000Mj10Tg004Tj14Tg002Ij12Tg0052j21Tg007Cj23Tg00Wmg00Kig00OT#0#0#0#0#0#0#4R0#2f0,10'3W1W0o"). Qed.

Section TLB.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis HOWN : rt_own H.
  Hypothesis HEX : exhausted_stmtA H LINV.

  Lemma HHm : asan_rt_hyps H.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmWT2 ()) ["TLB"] "p;2p;1p;3g00^Bj27Tg00_Bj26Tg00`Kj12Tg00aTj21Tg00bSj15Tg00cZj13Tg00E7j20Tg00dWj34Tp,5HCEILR0p,1HR1'71601%211101%50%31'0'0'0'0p,4HHbp34o"). Qed.

  Definition TL_FFX : list (Z * Z) := [(64, 8); (96, 4)].

Definition RT_FIN : list (reg * expr) :=
  [(2%bv, EVar WV_S1);
   (8%bv, EVar WV_SP0);
   (9%bv, EVar WV_S1);
   (20%bv, SH_FF);
   (24%bv, WADD WV_FF 7984);
   (26%bv, WADD WV_FF 112);
   (27%bv, ELit 18446744073709551608)].

  Definition tl_headK (w : pmwA H) (s : as_St H) LB LBs (m0 : mem) (c' : pmc) F fc (Q : config -> Prop) : Prop :=
    forall msF1 mo1 m1 R1,
      as_AKREL H s (mkCfg msF1 mo1) ->
      as_VIS H s msF1 = MS R1 F (Z_to_bv 64 OL_HEAD) fc None m1 (seg_rom asegs) -> rfull R1 ->
      PMXA H LINV w s LB LBs m1 mo1 c' S_INSTR TBL_EEF44 [] ->
      regs_tbl w R1 RT_EEF44 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      ffkeepX w TL_FFX m0 m1 ->
      as_SR H Q (mkCfg msF1 mo1).

  Lemma tl_fin : forall (spal : Z) (w : pmwA H) s LB LBs (m0 m : mem) mo (c cX : pmc) msF R F fc (nw : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo cX S_OPER TBL_EEF44 [] [] spal -> 0 <= spal <= PM_STRK * nw -> ffkeepX w TL_FFX m0 m ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1ab4) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_FIN -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 19%bv = Z_to_bv 64 (c_widx c + nw) ->
    c_widx cX = c_widx c -> c_icount cX = c_icount c -> c_endian cX = c_endian c -> c_reqconv cX = c_reqconv c ->
    0 <= nw -> c_widx c + nw <= wa_n w ->
    tl_headK w s LB LBs m0 (set_scalA cX (c_widx c + nw) (c_icount c) (c_endian c) (c_reqconv c)) F fc Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros spal w s LB LBs m0 m mo c cX msF R F fc nw Q OK X0 Hsp FK0 KR VIS RF HT G3 G4 G19 Ew Ei Ee Er Hnw Hn K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    pose proof (p_apart_ff H w OK) as PAF. unfold O_WIDX, PARSER_SIZE in PAF.
    set (c' := set_scalA cX (c_widx c + nw) (c_icount c) (c_endian c) (c_reqconv c)).
    pm_goSX HHm LINV_frame OK X0 KR VIS RF HT (@nil word) (@nil kentry) 300%nat [OL_HEAD] (@nil bool) 41%N S_INSTR (@nil Z) (@nil Z)
      TBL_EEF44 (@nil (Z * expr)) RT_EEF44 c' 0.
    - split_scs.
    - unfold scal_after, c'. subst SSr. cbn [s_log]. unfold sval. lfield_rw. cbv beta iota.
      f_equal; [| rewrite Ei; reflexivity | rewrite Ee; reflexivity | rewrite Er; reflexivity].
      cbn [edenot]. rewrite Eseed_reg by lia. replace (Z_to_bv 5 (Z.of_N 19)) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G19, u64_of_Z by lia. reflexivity.
    - subst c'. cbn [set_scalA c_widx c_icount c_endian c_reqconv]. lia.
    - subst c'. cbn [set_scalA c_widx c_icount c_endian c_reqconv]. lia.
    - subst c'. cbn [set_scalA c_widx c_icount c_endian c_reqconv]. rewrite <- Ee. exact B3.
    - subst c'. cbn [set_scalA c_widx c_icount c_endian c_reqconv]. rewrite <- Er. exact B4.
    - unfold PM_RESERVE. lia.
    - unfold pm_phi, pm_prog. change (c_blocks c') with (c_blocks cX). subst c'. cbn [set_scalA c_widx]. rewrite Ew.
      rewrite pm_progz_step by lia. lia.
    - intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      pose proof (env_world_seed H w R (@nil word)) as HE.
      pose proof (ev_world_all H w _ HE) as (E32 & E33 & _).
      pose proof (munch_sym (Eseed R (wenv_vals w ++ [])) m _ [(FSHB, SHBASE, SHBASE + 2048); (EVar WV_P, 72, 80)] Hlf1 ltac:(vm_compute; reflexivity)) as MU.
      cbn [num_wins map] in MU. unfold FSHB, WV_FF in MU.
      rewrite (srl3_val _ (EVar 33) (wa_ff w) E33 ltac:(lia)), (ev_p H w _ OK HE) in MU.
      apply (K msF1 mo1 _ R1 KR1 VIS1 RF1 X1 HTx1).
      + rewrite (HR1 3%bv). exact G3.
      + rewrite (HR1 4%bv). exact G4.
      + eapply (ffkeepX_trans w _ [] _ _ _ _ FK0); [| apply incl_refl | intros x9 Hx9; destruct Hx9].
        apply ffkeepX_nil. apply (ffkeep_munch w _ _ _ MU (wmono_mem_denot _ _ _)).
        apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
        * rewrite Q13 in Q6. unfold SHBASE in *. destruct Q6 as [Q6|Q6]; [left | right]; lia.
        * lia.
  Qed.

Definition RT_LOOPC : list (reg * expr) :=
  [(2%bv, EVar WV_S1);
   (8%bv, EVar WV_SP0);
   (9%bv, EVar WV_S1);
   (10%bv, ELit 4);
   (20%bv, SH_FF);
   (24%bv, WADD WV_FF 7984);
   (25%bv, ELit SHBASE);
   (26%bv, WADD WV_FF 112);
   (27%bv, ELit 18446744073709551608)].

  Definition tl_cutL (spal : Z) (w : pmwA H) (s : as_St H) LB LBs (m : mem) (c c1 : pmc) F fc (nw : Z) (Q : config -> Prop) : Prop :=
    forall m2 msF2 mo2 R2,
      as_AKREL H s (mkCfg msF2 mo2) ->
      as_VIS H s msF2 = MS R2 F (Z_to_bv 64 0xf1df4) fc None m2 (seg_rom asegs) -> rfull R2 ->
      PMXAT H LINV w s LB LBs m2 mo2 c1 (2 :: 1 :: S_OPER)%nat TBL_EEF44 [] [] spal ->
      regs_tbl w R2 RT_LOOPC -> PropExec.getr R2 3%bv = wa_gp w -> PropExec.getr R2 4%bv = wa_tp w ->
      PropExec.getr R2 18%bv = Z_to_bv 64 (c_endian c) -> PropExec.getr R2 19%bv = Z_to_bv 64 (c_widx c + nw) ->
      PropExec.getr R2 21%bv = Z_to_bv 64 (wa_words w + 4 * c_widx c) -> PropExec.getr R2 23%bv = Z_to_bv 64 (wa_words w + 4 * c_widx c) ->
      PropExec.getr R2 22%bv = Z_to_bv 64 (wa_words w + 4 * (c_widx c + nw)) ->
      ffkeepX w TL_FFX m m2 -> rw_cells asegs m2 (wa_ff w + 64) [C8 (Z_to_bv 64 (wa_p w + 240))] ->
      c_reqconv c = 1 -> 1 <= nw -> c_widx c + nw <= wa_n w ->
      as_SR H Q (mkCfg msF2 mo2).

  Definition RT_EXH : list (reg * expr) :=
    [(1%bv, ELit 0xf19d4); (2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (10%bv, EVar WV_P); (20%bv, SH_FF);
     (24%bv, WADD WV_FF 7984); (26%bv, WADD WV_FF 112); (27%bv, ELit 18446744073709551608)].
  Definition RT_B0 : list (reg * expr) := (10%bv, ELit 18446744073709551612) :: rt_keep RT_EXH.


  Lemma sx32A_small : forall x, 0 <= x < 2 ^ 31 -> sx32A x = x.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmWT2 ()) ["TLB"] "p'0h02Hah16__sat2h24__x1h32H0h47__arithh54__ffh64__p1h76__sat1h86__sat4h96__sat6h:8__varmaph;5__with<2Hxh=6__sat3h>6__sat5h?1bi001bh@2b0hA1xp;1p;2p;3p;4p;6p;7p;8g000Mj12Tg0012j16Tg00fij18Tg001Pj2=Tg001mj21Tg00E7j2BTg03?Dj2OTg00H:j23Tg03?fj2?Tg03@CR0j3GTg0000j2ATg03@gj2>Tg002lj34Tg007]j2<Tg008Ej39Tg008ij2WTg007Cj2CTg00;gj1VTg00<gj1UTg00=Gj2TTg00>aj1RTg00??j1NTg00?jj2MTg00HVj45Tg00BXj2LTg00C:j2KTg00Cfj3HTg00DEj4ITg00A0j2JTg004Tj1:Tg00ASj3;Tg00B6j1FTg02Vij6ETg00Iej7PTg00@Mj3QTg03ADj3DTg03Agj1STg00IAj7YTg00JIj8XTg00KKR1f0R2'3p=0f1R3g00LnR4g00MMR5P5g00MmR6P2g00NMFYp=7f3R7P4P5P5P6f2R8P3P2GXp=@g00KiR9%02g00OTR:#2R;#6R<%8:#8#8#8R=#6R>'=R?,12'B1O3?113?R@13?31?3?3G1?8?g00SPRAP0117?13?7PAP9P3f5R0%2;#2#2#2R;#2RB#6RC,=<RD,A0%6;RE,=<RF'>n0100000020000=490P3f4R0/1?1<<>RG111<RH%0>111?[RI[RJ%0<RKg00PWRLA9<>3UW0R>%0?\L^0KRMP3g00Q31W1<'CPHeRNO1ROPIg00QYRP#VRQ%UPRP1T93RR%R9RS%N9RTP91M9:R:g03BfRUP:C5'71LT6RVP2P8g00T0RW,CA1K28=4AWdAH913CIRWb5b:b;X29A4922^29P2f9O1b4b1b7b1W3P2O113?01<<E%0E111F[RA\HA9<E3VLX0K%0F\L^0K1<<C%0C111D[R1\HA9<C3VLX0K%0D\L^0KPGPJP>PMPOPIP0PNO1P1f7PNO1PAp-0RAPQPPPRPSPTP91J9<R<%:=5;9R=g00NmP:C5,7T%F5RSPTPTP4P5P5P6PTP4P5P5P6P7EEP9P:g00LGP=C5,7TFPPSP9%:B9;9<9Q9:%:;9;9<5D9PUP:C5,7TC@C@PVPWb5b:b;X29W613?21B8@1A8D/>F=498[[^29^6AP2f?RA#0PAf:f>O4b4b9b8b1b7b1b=b8b>b9W3P2O1n200210000000021000011000b@b?%S3=493eW<WAo"). Qed.

#[local] Definition HTLbAPmWT2_0 : list kentry := [KWord (SA (EVar 32) 72) 8 (EVar 41); KWord (SA (EVar 33) 114) 2 (EVar 42)].
#[local] Definition HTLbAPmWT2_1 : list kentry := [KWord (SA (EVar 32) 72) 8 (EVar 41); KWord (SA (EVar 33) 114) 2 (EVar 42); KWord (SA (EVar 32) 92) 1 (ELit 0)].
#[local] Definition HTLbAPmWT2_2 : list kentry := [KWord (SA (EVar 32) 72) 8 (EVar 41); KWord (SA (EVar 33) 114) 2 (EVar 42); KWord (SA (EVar 32) 92) 1 (ELit 1); KWord (SA (EVar 32) 88) 4 (EVar 43)].

  Lemma tlb_add : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
  Proof.
    intros a b. cbn [alu64 alu]. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
  Qed.
  Lemma tlb_mul : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
  Proof.
    intros a b. apply bv_eq. cbn [mul_div]. rewrite bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite <- Zmult_mod. reflexivity.
  Qed.
  Lemma tlb_srl62 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 62) = Z_to_bv 64 (x / 2 ^ 62).
  Proof.
    intros x Hx. apply bv_eq. cbn [alu64 alu]. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small x) by lia.
    replace (bv_unsigned (bv_and (Z_to_bv 64 62) (Z_to_bv 64 63))) with 62 by (vm_compute; reflexivity).
    rewrite Z.shiftr_div_pow2 by lia.
    assert (0 <= x / 2 ^ 62 < 2 ^ 64) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    rewrite !(Z.mod_small (x / 2 ^ 62)) by lia. reflexivity.
  Qed.
  Lemma tlb_sltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
    alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
  Proof. intros a b Ha Hb. cbn [alu64 alu]. unfold bv_ltu. rewrite !u64_of_Z by lia. destruct (a <? b); reflexivity. Qed.
  Lemma tlb_lt : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
    branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
  Proof.
    assert (S : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z).
    { intros z Hz. unfold bv_signed. rewrite (SymExec3.SX2.swrap_small 64 (bv_unsigned (Z_to_bv 64 z)) (2 ^ 63) (2 ^ 64));
        [| reflexivity | reflexivity | rewrite u64_of_Z by lia; lia | lia].
      rewrite u64_of_Z by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia. }
    intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !S by lia. reflexivity.
  Qed.

  Ltac tlb_rw :=
    repeat match goal with
    | Hv : ev ?E ?n = Z_to_bv 64 _ |- context [ev ?E ?n] => rewrite Hv
    end.
  Ltac tlb_ext :=
    repeat match goal with
    | Hx : ext_val ?s ?l ?k ?a = _ |- context [ext_val ?s ?l ?k ?a] => rewrite Hx
    end.
  Ltac tlb_land :=
    repeat match goal with
    | Hx : Z.land ?a ?b = _ |- context [Z.land ?a ?b] => rewrite Hx
    end.
  Ltac tlb_ltb :=
    repeat match goal with
    | |- context [?a <? ?b] => first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia]
    end.
  Ltac tlb_arith := tlb_rw; rewrite ?tlb_mul, ?tlb_add; tlb_ext; rewrite ?tlb_mul, ?tlb_add.
  Ltac tlb_sc :=
    cbn [sc_denot edenot]; tlb_arith; rewrite ?w_and, ?tlb_srl62, ?tlb_sltu by lia; tlb_land; rewrite ?Z.div_small by lia;
    tlb_ltb; cbv iota; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu, ?tlb_lt by lia; bool_lia.
  Ltac tlb_reg HR r :=
    rewrite (HR r);
    lazymatch goal with |- context [sr_get ?sr r] =>
      let x := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with x end.
  Ltac tlb_val := cbn [edenot]; tlb_arith; first [reflexivity | f_equal; lia].
  Lemma tl_segB : forall (spal : Z) (w : pmwA H) (I : ictxR) s LB LBs m mo (c c1 : pmc) msF R F fc (t nw : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c1 S_OPER TBL_EEF44 [] [] spal -> 0 <= spal <= PM_STRK * nw ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1970) fc None m (seg_rom asegs) -> rfull R -> frm_zero fc ->
    regs_tbl w R RT_TLA -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 22%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R 25%bv = Z_to_bv 64 (i_io I) -> PropExec.getr R 18%bv = Z_to_bv 64 t ->
    PropExec.getr R 23%bv = Z_to_bv 64 (t3a (c_v1 c1) + OPND_SZ * t3b (c_v1 c1)) -> 1 <= t3b (c_v1 c1) ->
    c_widx c1 = c_widx c -> c_icount c1 = c_icount c -> c_endian c1 = c_endian c -> c_reqconv c1 = c_reqconv c ->
    c_tr c1 = [] -> pm_bud (wa_n w) c1 -> (forall q k, In (q, k) (c_blocks c1) -> k <= 2 ^ 40) ->
    rw_cells asegs m (wa_ff w + 114) [C2 (Z_to_bv 64 nw)] -> 0 <= nw < 2 ^ 16 ->
    ipureA I -> i_io I + 1 <= c_widx c -> 0 <= t < 2 ^ 32 ->
    c_endian c = c_reqconv c /\ (c_endian c = 0 \/ c_endian c = 1) -> wa_words w <> 0 ->
    CHECKKA H LINV w Q ->
    (c_widx c + nw <= wa_n w -> tl_headK w s LB LBs m (set_scalA c1 (c_widx c + nw) (c_icount c) (c_endian c) (c_reqconv c)) F fc Q) ->
    tl_cutL spal w s LB LBs m c c1 F fc nw Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros spal w I s LB LBs m mo c c1 msF R F fc t nw Q OK X0 Hsp KR VIS RF FZ HT G3 G4 G22 G25 G18 G23 Hn1 Ew Ei Ee Er
           Htr BUD Hbsz Cnw Hnw IP Hio Ht [Hend Hend01] Hw KC KH KL.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    rewrite Ew in B1. rewrite Ee in B3. rewrite Er in B4.
    assert (IPR : 0 <= i_io I /\ 0 <= i_op I < 2 ^ 16).
    { unfold ipureA, PmODefsS1.ipure in IP. destruct IP as (_ & Hop & _ & _ & _ & _ & Hio0).
      split; [exact Hio0 | rewrite Hop; apply Z.mod_pos_bound; lia]. }
    destruct IPR as (Hio0 & Hop).
    assert (WW : wa_words w mod 16 = 0 /\ 0 < wa_words w).
    { destruct (wk_words H w OK) as [[W0 _] | (pw & k & _ & _ & Wp & W16 & _)]; [contradiction | split; [exact W16 | exact Wp]]. }
    destruct WW as (W16 & Wp).
    pose proof (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (_ & _ & _ & Hlen & Hb & _).
    assert (HB1 : 0 < t3a (c_v1 c1) /\ t3a (c_v1 c1) mod 16 = 0 /\ t3a (c_v1 c1) + 20 * t3b (c_v1 c1) <= 2 ^ 63).
    { unfold OPND_SZ in *. destruct Hb as [[B0 C0] | (Bp & B16 & Cp & Bhi & _)]; [lia | split; [exact Bp | split; [exact B16 | lia]]]. }
    destruct HB1 as (Bp & B16 & Bhi).
    set (e := t3a (c_v1 c1) + OPND_SZ * t3b (c_v1 c1)) in G23.
    assert (Eev : e = t3a (c_v1 c1) + 20 * t3b (c_v1 c1)) by reflexivity.
    assert (He : 20 < e <= 2 ^ 63) by lia.
    assert (LE20 : Z.land (e + -20) 3 = 0).
    { change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Eev. Z.div_mod_to_equations. lia. }
    assert (LA : Z.land (wa_words w + 4 * c_widx c) 3 = 0).
    { change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. Z.div_mod_to_equations. lia. }
    set (Xs := [Z_to_bv 64 (c_widx c); Z_to_bv 64 nw; Z_to_bv 64 (c_endian c)]).
    pose proof (env_world_seed H w R Xs) as HE.
    pose proof (ev_world_all H w _ HE) as (E32 & E33 & _ & _ & E36 & E37 & _).
    assert (Y41 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 (c_widx c)) by (ev_xs; reflexivity).
    assert (Y42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 nw) by (ev_xs; reflexivity).
    assert (Y43 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 43) = Z_to_bv 64 (c_endian c)) by (ev_xs; reflexivity).
    assert (YR : forall (r : N) (x : bv 5) (v : word), (r < 32)%N -> Z_to_bv 5 (Z.of_N r) = x -> PropExec.getr R x = v ->
               edenot (Eseed R (wenv_vals w ++ Xs)) (EVar r) = v).
    { intros r x v Hr Hx Hv. cbn [edenot]. rewrite Eseed_reg by exact Hr. rewrite Hx. exact Hv. }
    assert (Y23 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 23) = Z_to_bv 64 e)
      by (apply (YR 23%N 23%bv); [lia | apply bv_eq; reflexivity | exact G23]).
    assert (Y25 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 25) = Z_to_bv 64 (i_io I))
      by (apply (YR 25%N 25%bv); [lia | apply bv_eq; reflexivity | exact G25]).
    assert (Y22 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 22) = Z_to_bv 64 (i_op I))
      by (apply (YR 22%N 22%bv); [lia | apply bv_eq; reflexivity | exact G22]).
    assert (Y18 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 18) = Z_to_bv 64 t)
      by (apply (YR 18%N 18%bv); [lia | apply bv_eq; reflexivity | exact G18]).
    assert (V23 : ev (Eseed R (wenv_vals w ++ Xs)) 23 = Z_to_bv 64 e) by exact Y23.
    assert (V32 : ev (Eseed R (wenv_vals w ++ Xs)) 32 = Z_to_bv 64 (wa_p w)) by exact E32.
    assert (V36 : ev (Eseed R (wenv_vals w ++ Xs)) 36 = Z_to_bv 64 (wa_words w)) by exact E36.
    assert (V37 : ev (Eseed R (wenv_vals w ++ Xs)) 37 = Z_to_bv 64 (wa_n w)) by exact E37.
    assert (V41 : ev (Eseed R (wenv_vals w ++ Xs)) 41 = Z_to_bv 64 (c_widx c)) by exact Y41.
    assert (V42 : ev (Eseed R (wenv_vals w ++ Xs)) 42 = Z_to_bv 64 nw) by exact Y42.
    assert (V43 : ev (Eseed R (wenv_vals w ++ Xs)) 43 = Z_to_bv 64 (c_endian c)) by exact Y43.
    assert (ZX42 : ext_val false 0 2 (Z_to_bv 64 nw) = Z_to_bv 64 nw).
    { pose proof (edenot_zext16 _ 42 nw Y42 ltac:(lia)) as S. cbn [edenot] in S. rewrite V42 in S. exact S. }
    assert (SX43 : ext_val true 0 4 (Z_to_bv 64 (c_endian c)) = Z_to_bv 64 (c_endian c)).
    { pose proof (edenot_sext32 _ 43 (c_endian c) Y43 ltac:(lia)) as S. cbn [edenot] in S. rewrite V43, sx32A_small in S by lia. exact S. }
    assert (KWI : kentry_ok ASEGS (Eseed R (wenv_vals w ++ Xs)) m (KWord (SA (EVar 32) 72) 8 (EVar 41))).
    { eapply pmk_scal_widx with (1 := OK) (2 := X0) (3 := HE). rewrite Ew. exact Y41. }
    assert (KNW : kentry_ok ASEGS (Eseed R (wenv_vals w ++ Xs)) m (KWord (SA (EVar 33) 114) 2 (EVar 42))).
    { eapply (kword_of_rw_cells asegs _ m (wa_ff w + 114) _ 0 (C2 (Z_to_bv 64 nw))); [exact Cnw | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off]; rewrite E33, u64_of_Z by lia; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia
        | rewrite Y42; reflexivity]. }
    assert (KEN : kentry_ok ASEGS (Eseed R (wenv_vals w ++ Xs)) m (KWord (SA (EVar 32) 88) 4 (EVar 43))).
    { eapply pmk_scal_endian with (1 := OK) (2 := X0) (3 := HE). rewrite Ee. exact Y43. }
    assert (KFL : forall k, c_reqconv c = k -> kentry_ok ASEGS (Eseed R (wenv_vals w ++ Xs)) m (KWord (SA (EVar 32) 92) 1 (ELit k))).
    { intros k Hk. apply (kword_of_fld _ m (wa_p w + O_FLAGS) 1 (c_reqconv c1)); [exact (xa_flags _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | | | |];
        [unfold estart; cbn [a_base a_off]; rewrite E32, u64_of_Z by lia; unfold O_FLAGS; lia | unfold O_FLAGS, PARSER_SIZE in *; lia
        | unfold O_FLAGS, PARSER_SIZE in *; cbn; lia | cbn [edenot]; rewrite Er, Hk; reflexivity]. }
    assert (FKM : forall LOG, log_flat (Eseed R (wenv_vals w ++ Xs)) LOG ->
              forallb (sym_inside [(FSHB, SHBASE, SHBASE + 2048); (EVar WV_FF, 64, 72)]) LOG = true ->
              ffkeepX w TL_FFX m (mem_denot (Eseed R (wenv_vals w ++ Xs)) m LOG)).
    { intros LOG Hlf Hin. pose proof (munch_sym _ m _ _ Hlf Hin) as MU.
      cbn [num_wins map] in MU. unfold FSHB, WV_FF in MU.
      rewrite (srl3_val _ (EVar 33) (wa_ff w) E33 ltac:(lia)), E33, u64_of_Z in MU by lia.
      apply (ffkeepX_munch w _ _ _ _ MU (wmono_mem_denot _ _ _)).
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
      - rewrite Q13 in Q6. unfold SHBASE in *. destruct Q6 as [Q6|Q6]; [left | right; left]; lia.
      - right; right. apply Exists_cons_hd. cbn [fst snd]. lia. }
    destruct (Z_le_gt_dec (c_widx c + nw) (wa_n w)) as [LE | GT].
    2: {
      assert (HK0 : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m HTLbAPmWT2_0)
        by (apply Forall_cons; [exact KWI | apply Forall_cons; [exact KNW | apply Forall_nil]]).
      pm_goX HHm LINV_frame OK X0 KR VIS RF HT Xs HTLbAPmWT2_0 HK0 200%nat [AEXHAUSTED; 0xf1ab4; 0xf1df4] [false; false; false; false] 44%N
        S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_EXH.
      { split_scs. all: tlb_sc. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      assert (HT1 : regs_tbl w R1 RT_EXH) by exact (regs_tbl_restrict w [] _ R1 RT_EXH HTx1 ltac:(vm_compute; reflexivity)).
      assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3).
      assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4).
      eapply (pm_exhausted H HHbp LINV HEX w s LB LBs _ mo1 c1 S_OPER TBL_EEF44 [] spal msF1 R1 F fc 0xf19d4 (i_io I) (i_op I) t Q).
      - exact OK.
      - exact X1.
      - vm_compute; reflexivity.
      - vm_compute; reflexivity.
      - exact KR1.
      - exact VIS1.
      - exact RF1.
      - exact FZ.
      - rtf HT1.
      - reflexivity.
      - lia.
      - rtf HT1.
      - rtf HT1.
      - exact G4_1.
      - rtf HT1.
      - tlb_reg HR1 (11%bv : bv 5). exact Y25.
      - tlb_reg HR1 (12%bv : bv 5). exact Y22.
      - tlb_reg HR1 (13%bv : bv 5). exact Y18.
      - lia.
      - lia.
      - lia.
      - unfold PM_RESERVE, PM_STRK in *. lia.
      - unfold PM_PF. apply in_or_app. right. apply in_or_app. left. apply in_map_iff. exists 0xf19d4. split; [reflexivity | cbn; tauto].
      - intros msF2 mo2 m2 R2 F2 fc2 s2 LB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 G10_2 _.
        assert (HT2 : regs_tbl w R2 RT_B0).
        { unfold regs_tblX, RT_B0. apply Forall_cons; [cbn [fst snd]; rewrite G10_2; reflexivity |].
          exact (regs_keep w [] R1 R2 RT_EXH HT1 KEEP2). }
        assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inb)); exact G3_1).
        assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inb)); exact G4_1).
        pm_goX HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word) (@nil kentry) (Forall_nil (kentry_ok ASEGS (Eseed R2 (wenv_vals w ++ [])) m2))
          100%nat [OL_CHECK] (@nil bool) 41%N (OB_PARSED_OPERAND :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_CHECK.
        { split_scs. }
        intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
        eapply (KC s2 LB2 LBs _ mo3 c1 msF3 R3 F2 fc2 TBL_EEF44 (spal + 2 ^ 20) (2 ^ 32 - 4) X3 (incl_refl _) Htr BUD Hbsz KR3 VIS3 RF3 FZ2 HTx3).
        + rewrite (HR3 3%bv). exact G3_2.
        + rewrite (HR3 4%bv). exact G4_2.
        + tlb_reg HR3 (23%bv : bv 5). apply bv_eq. vm_compute. reflexivity.
        + lia. }
    destruct (Z.eq_dec (c_reqconv c) 0) as [RC0 | RC1].
    - assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m HTLbAPmWT2_1)
        by (apply Forall_cons; [exact KWI | apply Forall_cons; [exact KNW | apply Forall_cons; [exact (KFL 0 RC0) | apply Forall_nil]]]).
      pm_goX HHm LINV_frame OK X0 KR VIS RF HT Xs HTLbAPmWT2_1 HK1 200%nat [AEXHAUSTED; 0xf1ab4; 0xf1df4] [false; false; false; true] 44%N
        S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_FIN.
      { split_scs. all: tlb_sc. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      pose proof (FKM _ Hlf1 ltac:(vm_compute; reflexivity)) as FK0.
      eapply (tl_fin spal w s LB LBs m _ mo1 c c1 msF1 R1 F fc nw Q OK X1 Hsp FK0 KR1 VIS1 RF1
                (regs_tbl_restrict w [] _ R1 RT_FIN HTx1 ltac:(vm_compute; reflexivity))).
      + rewrite (HR1 3%bv); exact G3.
      + rewrite (HR1 4%bv); exact G4.
      + tlb_reg HR1 (19%bv : bv 5). tlb_val.
      + exact Ew.
      + exact Ei.
      + exact Ee.
      + exact Er.
      + lia.
      + exact LE.
      + exact (KH LE).
    - assert (RC : c_reqconv c = 1) by lia.
      assert (HK2 : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m HTLbAPmWT2_2)
        by (apply Forall_cons; [exact KWI | apply Forall_cons; [exact KNW | apply Forall_cons; [exact (KFL 1 RC) | apply Forall_cons; [exact KEN | apply Forall_nil]]]]).
      destruct (Z.eq_dec nw 0) as [NW0 | NW1].
      + pm_goX HHm LINV_frame OK X0 KR VIS RF HT Xs HTLbAPmWT2_2 HK2 200%nat [AEXHAUSTED; 0xf1ab4; 0xf1df4]
          [false; false; false; true; false; false; false; false; false; false; false; true; true] 44%N
          S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_FIN.
        { split_scs. all: tlb_sc. }
        intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
        pose proof (FKM _ Hlf1 ltac:(vm_compute; reflexivity)) as FK0.
        eapply (tl_fin spal w s LB LBs m _ mo1 c c1 msF1 R1 F fc nw Q OK X1 Hsp FK0 KR1 VIS1 RF1
                  (regs_tbl_restrict w [] _ R1 RT_FIN HTx1 ltac:(vm_compute; reflexivity))).
        * rewrite (HR1 3%bv); exact G3.
        * rewrite (HR1 4%bv); exact G4.
        * tlb_reg HR1 (19%bv : bv 5). tlb_val.
        * exact Ew.
        * exact Ei.
        * exact Ee.
        * exact Er.
        * lia.
        * exact LE.
        * exact (KH LE).
      + pm_goX HHm LINV_frame OK X0 KR VIS RF HT Xs HTLbAPmWT2_2 HK2 200%nat [AEXHAUSTED; 0xf1ab4; 0xf1df4]
          [false; false; false; true; false; false; false; false; false; false; false; true; false; false] 44%N
          (2 :: 1 :: S_OPER)%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_LOOPC.
        { split_scs. all: tlb_sc. }
        intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
        apply (KL _ msF1 mo1 R1 KR1 VIS1 RF1 X1 (regs_tbl_restrict w [] _ R1 RT_LOOPC HTx1 ltac:(vm_compute; reflexivity))).
        * rewrite (HR1 3%bv); exact G3.
        * rewrite (HR1 4%bv); exact G4.
        * tlb_reg HR1 (18%bv : bv 5). tlb_val.
        * tlb_reg HR1 (19%bv : bv 5). tlb_val.
        * tlb_reg HR1 (21%bv : bv 5). tlb_val.
        * tlb_reg HR1 (23%bv : bv 5). tlb_val.
        * tlb_reg HR1 (22%bv : bv 5). tlb_val.
        * exact (FKM _ Hlf1 ltac:(vm_compute; reflexivity)).
        * pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (_ & _ & W2). change (fsz PM_FCLASS) with 16384 in W2.
          subst SSr. cbn [s_log] in Hlf1 |- *.
          eapply (rw_cells_mem_denot_w _ m [_] (SA (EVar 33) 64) 8 (EAlu ALU_ADD (EVar 32) (ELit 240)) [_] (wa_ff w + 64)
                    (C8 (Z_to_bv 64 (wa_p w + 240)))).
          -- exact Hlf1.
          -- apply Forall_cons; [| apply Forall_nil]. unfold estart. cbn [a_base a_off e_addr e_width Z.of_nat].
             rewrite (srl3_val _ (EVar 33) (wa_ff w) E33 ltac:(lia)), E33, u64_of_Z by lia.
             rewrite Q13 in Q6. unfold SHBASE in Q6. destruct Q6 as [Q6|Q6]; [right | left]; lia.
          -- apply estart_var; [exact E33 | lia].
          -- split; [lia|]. split; [lia|]. intros i Hi. replace (wa_ff w + 64 + i) with (wa_ff w + (64 + i)) by lia.
             apply W2. unfold AFS_HDR. lia.
          -- reflexivity.
          -- exact Logic.I.
          -- rewrite (ev_add _ 32 (wa_p w) 240 E32) by lia. reflexivity.
        * exact RC.
        * lia.
        * exact LE.
  Qed.
End TLB.
