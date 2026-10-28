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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts StrLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require PmStep5S1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmVup LbB_PmExit2 LbB_PmGlue LbB_PmU2K LbB_PmLH LbB_PmLeaf LbB_DiagStmt LbB_PmDS LbB_ContStmt LbB_PmVops LbB_PmU2 LbB_DStat LbB_TablStmt LbB_PmOL LbB_PmOLX LbB_HEmpStmt LbB_PmWM3 LbB_PmWEx LbB_PmU3L LbB_PmU3XK LbB_PmU6R LbB_StrPb LbB_MkStr LbB_PmStr LbB_PmStrD LbB_PmStrI LbB_PmS8K LbB_PmS8a LbB_PmS8b LbB_PmS8d LbB_PmS8i LbB_PmEmhB.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmS8 () := "I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_blocksC46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmStr7set_trAC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_trC47Corelib4Init9Datatypes3appC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmStr@c_blocks_tr_permC46Stdlib7Sorting;Permutation?Permutation_symK47Corelib4Init5Logic2or02C46Stdlib5Lists4List9in_or_appC46Stdlib7Sorting;Permutation>Permutation_inC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmStr:set_trA_idC47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes4prod01I47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase3pmc00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2ltC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWM37set_m3AC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase6pm_budC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep;umap_blocksC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWM37rest_m3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWM37cbk_m3'I47Corelib4Init5Logic2or00C46Stdlib5Lists4List:in_app_iffC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4list02C47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_m1C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7ZlengthC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_m2C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_m3C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWM35mblk3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWM36cbk_m3C5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3aC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3bC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3cC47Corelib4Init9Datatypes3fstC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_v1C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_v2C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_v3K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission7LibCont4CRep7OPND_SZC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C46Stdlib5Lists4List8nil_consI47Corelib4Init9Datatypes4bool00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C46Stdlib5Lists4List8map_consC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH6macctAC5ARocqVerifyHarness?AgentSubmission7LibCont4CRep4ZlenC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH5m3okAC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission6LibPrs9PmStep5S1<bseq_next_leC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9bseq_nextC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4BSEQC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts9BSEQ_LASTK46Stdlib9micromega=RingMicromega3Op201I6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4pmwA00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmS85shdrAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops6ffkeepC56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_ffC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeK47Corelib4Init5Logic2ex01K5ARocqVerifyHarness?AgentSubmission7LibCont4CRep4sbuf02C45stdpp9bitvector;definitions7Z_to_bvC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2b8K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell04C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01I7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI47Corelib4Init9Datatypes3nat00C4ARocqVerifyHarness?AgentSubmission8LibIface3memI5ARocqVerifyHarness?AgentSubmission7LibCont4CRep4sbuf00K5ARocqVerifyHarness?AgentSubmission7LibCont4CRep4sbuf01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StI45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn7pmw_okA00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmStr5tr_ofK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8K6RT_S8DC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9regs_tblXC4ARocqVerifyHarness?AgentSubmission8PropExec4getrK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase=pm_phi_blocksI47Corelib4Init9Datatypes6option00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib5Lists4List:fold_rightC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_nC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_gpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_tpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K7ffkeepXK47Corelib5Lists7ListDef6Forall01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8d9pm_s8d_s1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8d9pm_s8d_s0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_s1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6wa_sp0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall;keys_nonnegK47Corelib4Init5Logic2or01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS9regs_keepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS7rt_keepc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmS8>bsz_set_tr_nilC47Corelib4Init5Logic6or_indC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8d8pm_s8d_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8d8pm_s8d_cC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmStrD:pm_str_delC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8d9pm_s8d_l1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8d9pm_s8d_l0I6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5PMXAT00K45stdpp9bitvector;definitions2bv01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8K5S_STRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL9TBL_EEF44I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6S_OPERC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL6RT_OLJC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall9KEPT_REGSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase:PM_RESERVEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL8OL_PUSHKC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL8OL_CHECKC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9ICM_LARGEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL8RT_PUSHKC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL8RT_CHECKC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AOPDEL2C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface9APC0_FREEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt5PM_PFC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<asan_rt_hypsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCasan_rt_hyps_bp_extC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCalloc_ok_of_live_bpC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface9RHEAP_ahmC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceAannotate_gen_stmtC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface7cost_bpC47Corelib4Init5Logic5proj1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7pm_geomC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_loC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac:pmw_boundsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_consC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8wa_wordsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn4wk_nC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt9emp_entryC46Stdlib5Lists4List:incl_nil_lC46Stdlib5Lists4List9incl_reflC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K=ffkeepX_transC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes3orbC46Stdlib5Lists4List7forallbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K<ffkeepX_cellC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6xa_fshC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall6acc_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall=ff_accessibleC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow:accessibleC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall9obj_sh_okC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3b2zC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge9rfull_mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K;ffkeepX_nilC46Stdlib5Lists4List8in_splitc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmS8;bsz_set_m3AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8xa_rheapC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_RHEAPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6xa_ownC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6wa_LB0I46Stdlib7Sorting;Permutation;Permutation00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB3lblC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase6c_widxC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_icountC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_endianC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase9c_reqconvK5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase3pmc01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmVup8xb_factsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ablock_rangeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmXp<blk_apart_ffC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_sizeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5xa_shC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6pmc_shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt7umap_shC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8vsh_opndC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5vsh32C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula07C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt5sx32AC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appK47Corelib5Lists7ListDef6Forall02C46Stdlib7Sorting;PermutationBPermutation_ForallI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC46Stdlib5Lists4List?Forall_inv_tailc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmS8=macct_set_m3AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU6R<regs_tbl_eqRC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic6eq_symC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8i9pm_s8i_h3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmStrI8pm_sw_m3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8i9pm_s8i_h1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWM3=pm_emplace_m3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8i9pm_s8i_ebC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8i9pm_s8i_eaC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEK47Corelib4Init9Datatypes4bool02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface4bptrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8K6RT_S8CC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8K7RT_S8D1C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AFS_HDRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_HEmpStmt7EMP_EXTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8K6RT_S8MC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmS83HHiC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8AFS_SIZEC5ARocqVerifyHarness?AgentSubmission6LibPrs6PrsInv;PARSER_SIZEI46Stdlib5Lists4List6Exists00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac inlistS := cbn; repeat (first [left; reflexivity | right]).

Lemma bsz_set_tr_nil : forall c, (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
  forall q k, In (q, k) (c_blocks (set_trA c [])) -> k <= 2 ^ 40.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmS8 ()) [] "h01ch11kh21qh32Hbh43Hinp;2p;1p;3p;4p;5p;6g0000j2DTg000Pj11Tg001Kj30Tg001bj12Tg002Gj15Tg002ej1;Tg003Jj29Tg003gj28Tg004Cj17Tg004cj23Tg005aj16Tg006Xj3:Tg0075j2CTg008<j4BTg008ij3ATg009Cj5<Tg009aj6=Tg00:Mj1>Tg00;Nj6?Tg00;jj4@Tg00<JR0P0f1R1f0R2C@p=4g00<hR31D00R41412R5f2R6#130g00=`#2R7#5%;7#2#2#2#5'9,81[^10^20f3R7%74R8'3#19045P7P6P1P3f4R5%65R9'3R:1476%12504X03P41358#1R89:49R3%1:R:1461R6P4P:P31C59CBP4P9P8P6A0469A0468;A2D<E=P5%>5E?O3W4X10X20W3W0o"). Qed.

Lemma bsz_set_m3A : forall n c t, 0 <= n < 2 ^ 24 ->
  (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> pm_bud n (set_m3A c t) ->
  forall q k, In (q, k) (c_blocks (set_m3A c t)) -> k <= 2 ^ 40.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmS8 ()) [] "p'0h01Hh13Hinh21bi001bh31Ah41lh51xi011xh62Hah72_Hh81ah91eh:2l'h;1Bh<1kh=1Eh>7__arithh?4__ffh@4__p1hA4__p2hB6__sat1hC6__sat3hD6__sat5hE6__sat7hF8__varmaphG5__withH4__x1hI4__x2hJ2e0hK1fhL1qhM1yhN2B3hO2HbhP2HnhQ3_H0hR3_H1hS3_H2hT6__sat0hU6__sat2hV6__sat4hW6__sat6hX1chY1nhZ1ti021pi031zp%0p&0p;2p;1p;3p;5p;6p;4p;7p;8g0000R0j2RTg00>Ej1ETg001bj1>Tg002Gj1=Tg002ej1QTg003Jj2PTg00>ej2XTg000Pj1\Tg001Kj30Tg003gj22Tg00?Aj25Tg00@?k20MTg00A8j5_Tg00B5j1MTg006Xj3UTg00C3k20ETg009aj6qTg00D1R1j2TTg00DKk40:Tg00Djj2YTg004Cj1hTg00EGj26Tg00Edj3OTg00FDj4WTg00F`j2~Tg00G?j3<Tg00GYj6[Tg00H6j1STg00Hmj2@Tg00Ifj2KTg00JCj1FTg00K:j1?Tg005aj19Tg00L1k30LTg00LNj2xTg00M6j3wTg00MZk20HTg00N;j2vTg00NUj2fTg00O>k20GTg00Ogj3sTg00PPj1eTg00Poj3rTg00QXk20DTg00RDk20CTg00S0k20?Tg00SNk10>Tg00Slk40=Tg00TJk10<Tg00Thk10;Tg00USj2aTg00V6j2nTg00VYj3gTg00W<k309Tg00W_k108Tg00XAj1iTg00X_j3kTg00YBj4tTg00Ymk207Tg00ZOk206Tg00[;k305Tg00[Zk404Tg00\LR2j24Tg00;Nj6lTg00\gS00j2^Tg00]Ak503Tg00]`j1oTg00^\k102Tg008<k401Tg008ik300Tg00;jk40@Tg00_Yk40ATg00`Pj4uTg00aGj4]Tg00b>j3}Tg00b[k10BTg00cRj1|Tg00dIj1{Tg00e@k60FTg00edj7zTg00fHk70ITg00flk80JTf0R3#>#>p=Gg00gPR4f1R5'2/43p=Ig00<JR6P6P5P3H0@p=1P6P6P5P3H0Ap=;P6P6P5P3Cup=:P6P6P5P3C]p=7A}653p=Nf2R7P6P6P5P3Cu'6p=3A<653p=C1675/23p=J1275/43p=c1675/K3p=Lg00gnP6P6P6&0B3C]'6p=DP6P5P6%|3C],67p=AP6P5P6%{3C],67p=B1253,47p=yf3R8/@7/25/43p=bf6R9,24f5R:f4R;'2'412481275'4/43'4p=8124912:;'41@87/25/43'4p=`1K53,27p=V124;/481247/45/43'4p>0K1243p=HP5g00hgR<g00iFR=P=g00ifR>P3J0Fp=pP6P5g00jFP3Ctp=dP5P<P=P=P>P3g00jmFzp=ZP7P<P=P=P>P5P3K0Ip=mP8P<P=P=P>P7P5P3L0Jp=jg00<h1R66R<1R6<R?#ER@'Rg00=`RA#>RB#=RC%QARD#>RE#GRF#=RG'PRH,X7RI,I71153RJ%\;50<%QBRK#GRL#>RM#=RN,PCRO,25[^<6^L61587-0M;159:#\90<JP<f7RJ/59#\PGP61;@91:@917@9D_%MJ5U<RP1175RQ20EJ9P3EqA0<QPg00kMp4p710RQ%E3RP%E5RRP2AU8759083A0;58A0;57'TRS[RTA0837A0835'TAU;8790;5RU[RVA0:7;A0:78'T\UP8P7P5P3H0:S01P5n2001000000120000000X87W:W4W3RUPT^87^:R^4P^3QRWP3P<PGP6f8RX,;@1:@X17@XD_RYf9RZ#MR[11;8R\P5O5A0<\YA0<\['TP111:;R\PGP61;@Z1:@Z17@ZD_50<f:R[#M90<\12:OP3119:R\PGP61;@[1:@[17@[D_50<PUPWP3P<g00kjRW%E<RUf<RY,:@R]/Y4%h<R^1;@Y%>BR_#>R`#=Ra/6]'1=O<^n0100000020000R]P?P<1N<3/1GRbX9?Rc17@YCWRd11XJReP5O5A0<e]A0<ed'TP111ZXRdPWPUf=R],:@Rf/Y4P^1;@]16af'1=O<^n010000002000050<P?P<Pc17@]CW90<d12ZOP311[ZR[PWPUf>Rd,:@Rf/Y4P^1;@d16af'1=O<^n010000002000050<f?Rf,:@/Y4PWPW11]YRgPWPUP3P^fARU,;@A3a@U'1Rh=O<^n010000002000050<12]ORi]1P3f;Rj,1YRk=0<^12YO/~3W1f@Rl,;@A3a@l'1=O<^90<kP1A<<hgA0<g^PiP3fBRh,;@A3a@h'111d]R15<<P<P6P0P6P6P6P3P3n2001102000120103103S02X9<fCRm,;@A3a@mRn'111fdP3E[1CndP<P6P0P6P6P6P3P5n2001102000120103103S03X9<fDR0,;@RnA3a@0'111lfRoP5E[1CnlfERn,;@/CUfFRp93a@/CUP6fGRq93a@123OX<6S04P2fHRr/5qRs#SRt,7@,@?,6CfIRu/KCRv1R<6,R6,R6Rw%EwRx%FsRy'7'@,6C%=DRz%?sR{,7@,@?1Kuz3J7cv3cA3a@tRtPt%>`#G#G#G#G#=R`9LauRtA3axyRyPyPtA3a@{R{P{Pt%DsRtPt%QK#Q#=,PCRK%=_R_%E6Rt;AsR{P{%=L,PCRLAB_tsR{P{%QE#>#=,PCREP<%9sPC15ur#990<3B0L665Rs,X4%QD#G#=,PC7ysRs[^2<CbF8F8F81:@r=JaOP0fJRD/5uRu#S,7@,@?,6CfKR{/KCRy%Fu,7x,@w,6C%?u,7@,@?1K{z5Jz7cy3c15{DRD#S93a@RyPyfLRy=La`Rz%FD93axRuPuPz%?D93a@RuPuPz%DDRzPzPKAA_tDRzPzPLAB_tDRzPzPEP<%9DPC15y{R{#9RD90<3Ps[^2<CbF8F8F8P2%S{93a@RzfMRu=La`Rw,2z'I%F{93axRzPzPw%?{93a@RzPzPw%D{RwPwPKAA_t{RwPwPLAB_t{R{P{PEP<PDPC15uy#990<3Ps[^2<F`F8F81:@y=JaOP3fNRy/5u#S93a@RufORD,6a=Vu`'I15DyRy#F93axRuPufPRu=La`R{%?y93a@RwPwP{%DyR{P{PKAA_tyR{P{PLAB_tyR{P{PEP<%9yPC15uDRD#9Ry90<3Ps[^2<F`F8F8P2%FD93axR{fQRw=La`Rz,2{'I%?D93a@R{P{Pz%DDRzPzPKAA_tDRzPzPLAB_tDRDPDPEP<PyPC15wu#990<3Ps[^2<CbF8F81:@u=JaOP3fRRu/5w#F93axRxfSRw,6a=Vx`'I15wuRu#?93a@RxfTRy,6a=Vx`%DuRx12xKAA_tuRxPxPLAB_tuRxPxPEP<%9uPC15ywRw#9Ru90<3Ps[^2<CbF8I0KP2%?w93a@RxfURD,6a=Vx`'I%DwRxPxPKAA_twRxPxPLAB_twRwPwPEP<PuPC15Dy#990<3Ps[^2<F`F81:@y=JaOP3fVRy/5D#?93a@RDfWRu,6a=VD`'I15uyRy#DRDPDPKAA_tyRKPKPLAB_tyRtPtPEP<%9yPCfX/5u#990<3Ps[^2<F`F81xCNRs1X4CRu%HN1X4O[Ry[RE%HCRtg00lJR_AwCN5UW6RN%HO\_^6tRL1xCGRK%HG1X4H[RD\uRwAwCG5V_X6tRx%HH\_^6tRtP5g00lf20H4C'vPueRuO1R_PDP;PuO1RuPyp-0RHg00mLRzg00n8R{,f6Rv20G6aR|=s6v%e{#eR{#e,f61f6{9s6|5r65r6g00nW+0D+0C%hzR|3O%EzRzP620?67P5&0>6R{H0=&0<6Rv&0;6R}1p};1a6aR~1n6A5g6RA1n6BRB9g6~1a6`6096'd,Z}5m}&08=R=P}1p}:P6PBg00oC1a6CRC%iF5k6Ct,Z}5m}P=%iM9k6CRC,dA,Z}CjCj207}>R>P3P7g00ojRA,vW20637=<WAdB05645H04R4b?bFbGXH6XI6X@HWA16a3ALa5`5y714;IAJa7O[[^H6^I6^@H^AHP3f`RH#Hf^,:@RI,6a#HPHPIPXf]O6b>bEbDbVbDbWbEWSWNP5P3O2n2001000000121000000W0WRP5P3O2n2011000000121000000W0WQP5P3O2n2011000000121000000W0W7P5P3O2n2011000000121000000PhP3ElW0W7P3O1b0P3O1b0W=P3O1A0<1^g010J12fOP3n010000000W0P3O1n200100000021100010000W1n0110000020001P5O1b2W1P3O1P?P<Pc17@dCW90<[g010gR[p4p710RdP[p4p7210R[P5\5Rf%E7R^P2P;P8P7P5CW9083P;P3O1=<:7A0938'4X5:,^:[RXP8P3O1=<;5A0:37'4X5;,^;P:P;P8P7CW90;5RI[P:P3O1=<98A0J3;'4X59,^9\IP;P8P7P5P3I03P5n2001000000120000000XM7W4WKW;W3PX^M7^4^^Kf^;[^3dP3P?P<Pc17@lPkP5O6A<<bg17@U90?3'4X5?,^?Q00P?A<<b117@h90?3'4X5?PiP3A<<bo17@090?3'4P21N<5/1G11Ul5<<17@n90?512UOP31N<8/1G11mh5<<17@r90?;P<P6Q02XJ<1N<:/1G11n0P5E[1CG0P<P6Q03XJ<1N<9R0/1G11pnP7E[1C0p1N<J/Cq1CGqP6PGQ04PsPEPNPLPKPwPxPtP_PDPuPyP|PzP{Pv1a6G/dC,Z}P>P4b?bFbG12GOP3b>bCbBbTbBbUbCPrP3ElW0W7P3O1b0P3O1b0W7W=P5P3O2n2001000000121000000W0X9?P5P3O2n2001000000121101000b1b0W1P3O1n200100000021100011000b1b0W1P3O1%Mj90<\PZPJP9P<%oY%MY5U<RZ%\YR\11J9P<P\PZ&02YH01P2PTPVAU:;890:7\SQ01P3n2001000000120000000X87X:RX4PX3QPV^87^:R^4P^3QP3P<%o]RQ%M]R]PeA0<eQA0<e]<005O5b0EqO3W1P3O1n200100000021100010000b1b0b1W1X<6XL6W;WOWPWZWXXY6o"). Qed.

Lemma macct_set_m3A : forall c t, macctA c ->
  Zlength (t3c (c_m3 c)) <= Zlength (t3c t) ->
  (t3b t = t3b (c_m3 c) \/ ((t3b (c_m3 c) = 0 \/ Zlength (t3c (c_m3 c)) = t3b (c_m3 c)) /\ t3b t = bseq_next (t3b (c_m3 c)))) ->
  In (t3b (c_m3 c)) BSEQ -> t3b (c_m3 c) <> BSEQ_LAST -> m3okA (t3c t) ->
  macctA (set_m3A c t).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmS8 ()) [] "h01Hh14__x1h24__x2h34__x3h44__p1h57__arithh64__ffh78__varmaph85__with94cstrh:5cstr0h;5cstr1h<5cstr2h=4__x4h>1zh?2E0h@5EfullhA2HKhB2HbhC3HinhD5HlasthE4HlenhF2HnhG2M1hH2M2hI2M3hJ3M3KhK2_HhL1chM1tp&0p;2p;1p;3p;4p;6p;7p;8g0000j2OTg00>Ej1mTg011Dj1XTg001bj1>Tg002Gj1TTg00H6j1RTg002ej1YTg00JCj1ATg00K:j11Tg012@j28Tg0136j17Tg003gj24Tg00\LR0j23Tg00D1R1j2WTg0141j1ZTg00?Aj2cTg00EGj22Tg00Hmj2`Tg014Jj3wTg015Lj1HTg00>ej2[Tg003Jj2vTg016Gj1ETg00NUj2dTg00O>j2pTg00Ogj3bTg00PPj1aTg00QXj2oTg00RDj2nTg004Ck10>Tg00Edj3lTg00S0j2kTg00SNk10=Tg00TJk10<Tg00Thk10;Tg00V6j2_Tg00W_k106Tg00USj2STg00VYj3^Tg00W<j3jTg00Ymk205Tg00N;k204Tg00ZOk203Tg00G?j3ITg00[;k302Tg00[Zk401Tg016lj6iTg00YBj4gTg017Jj1~Tg017hj2}Tg018Ij3|Tg0192j4fTg00aGj4NTg00Ifj2JTg00`Pj4eTg001Kj3{Tg019Mj2qTg019mj1tTg00Poj3zTg00Slk407Tg00edk708Tg00flj8yTg00e@k609Tg00fHk70:Tf4R2f3R3g00<JR4P4f2R5f1R6CN'8'2f0R7'Jp=GP4P4P5P6Ce,23/47p=9P4P4P6P7Ce,25p=LP4P4P6P7CN,85p=VP4P4P6P7CNp=61235/J6,42/37p==P4P4P6P7CN,`5p=;P4P4P6P7Cep=0AI467p=<g00gPR89I45AI467'Wp=@%H79I46p=:g01:M9{47p=\g01;C9I47p=]12231256/J7'4p=M1856,23/J7p=x1J67,45p=K1256/47p=UP4P4P6P7CN,q5#tp=51256/J7p=uP4P4P6P7CN,q5p=F%t7,48p=?Az467p=CP4P5P6P7H07p=QP4P6g00jFP7Cgp=PP6g00hgR9g00iFR:P:g00ifR;P7g00jmK08p=DP3P9P:P:P;P5P6P7Gyp=BAI478p=hP6P9P:P:P;P7J09p=sP5P9P:P:P;P6P7K0:p=r1487p>00g00<h1O44R91O49R<#mR='O%X6P0g00=`R>#>R?#>#>R@#TRAP=%R5RB%>@#TRCP<P=PB%Y>#YRB#Y#Y#YRD#>#>#>#TREDGC91O94,O4,O4R9#mRF%A5RG5LAPCAV9FGPE%15RG9LA=PC16=GRG,8<PE%7GD=D=%139;<=A;<=5'410=3RG%12RH,0=RI'<A;<=H=@II1:GI'3'Wf5RI#1RG,0=RH#\f6RJ#1RK,0=RL#]#Z16=JRM#7f8RNf7RO'c#X[[[[[P7PAP=%R2RPPCP<P=PPPEDGC9%AIRP9LAFPCAV9FPPE12AHPC16=GRG,8<PE%7GD=D=P0PAPF%AJRGPCP9PFPGPEDGC912ALPC16=KRK,8<PE%7KD=%1O9;<=1`<M'410=ORO%1NRM,0=RK'<A;<=M=@KK1:OK'3'Wf9#1RK,0=RO#\f:RM#1RL,0=RG#]#Z16=MRH#7f<RPf;RQ'c#X[[[[[P7PAPF%ANRRPCP9PFPRPEDGC912AOPC16=KRK,8<PE%7KD=P0PAPGPC16=LRL,8<PEDM%7L%1Q9;<=1`<H'410=QRQ%1PRP,0=RH'<16=PRP,`<=@HH1:QH'3'Wf=RQ#1RL,0=#\f>RG#1RK,0=#]#Z16=G#7f@ROf?RR'c#X[[[[[P7PAPHPC18<PPEDM16=L#7A;<=KA;<=Q'410=GRQ%1RRR,0=RK'<A;<=R=@KK1:QK'3'W%1O,0=#\fARK#1,0=#]#Z16=K#7PAP=fCRK#RRQPCP<P=PQPEDGC9PAPF%AKRQPCP9PFPQPEDGC9RQPAP=fBRRPCP<16=RRLPECxC9RP%7LRL'3RH'3PGPQPHPMPPPL%1K,0=RL?w56%HLRP,[L%T?RM/2L%TDRD5KP'3%>B#>#T,vMRL9UAP'3P0fDRP#1,0=RH%HHRQ'[12MH=KQD'3AUAQLPAP=PPPCP<P=PPPEDGC9P7fFRP#1,0=RQ%HQRH'[12MQ=KHD'3fGRH#1,0=#H=UALP110=HRLfHRQ#1RS,0=RT'<A5<=S=@TT1:LT'3PA10=QRTPCA5<=QPEDMPNfIRN#1RQ,0=RS,<TP4fJRU#1RV,0=RW12A7RXA5<=U=uCERY'4X>4%AU9F9FRZ#E%?ZfK#19F<=RZ#E%?ZfLRZ#R9F<=R[#E%?[AF<=ZR[#E%?[g00mLR[g00n8R\,d4R]1p4A=b4]1p4C%a\#aR\#aR^,d4R_5b41d4\R\'C'Cg00nWR`'o'n&0>[Ra3l%m[Rb1k45&0=4Rc1k43Rd7Q37Q6Re&0<4Rf&0;4Rg1_4BRB1_4?Rh'P,Dg&06:R:Pg1S4A1_4>R>5^4Ri1S4CRj=^4B1S4ERk5j4'P,DgP:A^4jh=j4k,Pi,DgRiCBCB205g;R;P7P5g00kjRkg00ojRj+0420375=IkjdB02486H01Rjb6b7b8X14X24X341456AuC3ERk9UA6AUA5k[[^14^24^34P7fORk#1Rl95<=fNRm95<=Rn10=lRlPOPRO5b5b<b;b:b910=NRNP7EiW0P7O1A5<=Q=@SS1:TS'3P0A5<=V=@WW1:NWPAP=PUPYC9P7%1ZRZ,0=RYA5<=Z;@YP1fMR1#1RY,0=RZ#hA5<=Y/<Z10=1%1mR1,0=RZ':PA10=mRmPCPnPEDM[P7%hZ1:mlRmP4fPRl#1,0=#HRnA5<=l,2C=KXEX>4RX%Al9F9FRl#ERY%?lRlfQ#19F<=RU#ERN%?URUfRRW#R9F<=RV#ER0%?VRVAF<=WRW#ERS%?WRWp-0RT1p4MRQ%a^,d4R^5b4Ab4Q\RQ,C_'C,C]/o`,n]=l[aPbPePfPg1S48R8/Ph,DgP:Pg1sgI1S4M=^4B1S4D5j4,P>,DgR>5rgP:PgP4PBg01<@ReP8Cg,DgP:PiCBCBCBP;Pjb6b7b8X14X24X34W4&00612M3=K6D,32%h2PAP3PCP2PEDMR8[[[^14^24^34^4TP7fU#1R\,0=RO%HORo'[RpPOfT95<=RqPoP6PGPJO7b5b<b;b:b910=kRkP7EiW0W?P7O1A5<=1/<ZP4PnPXPYPlPNPUP0PVPSPW%~?,}4=|4_/CQ,C^,C]/o`,n]=l[aPb1k42?Q2c?Q5cAQc2d7Q6PfPg1sgJ=rg>P:PgP41_4@R@PePBCg,DgP:Pg1P@h,DgP:PiCBCBCBP;Pjb6b7b8X14X24X34X=4X4T12M5=K7D,321<2314I3P8[[[^14^24^34^=4^4TP7PpA5<=\POPqPoPGPJPPO8b5b<b;b:b9PkP7EiX0mW@P7O1n200100000021100011000W0P6P7O2n2001000000121000000W0P7O1n200100000021100011000PAPLPCAV<=HPEDMeWKWFP6P7O2n2001000000121000000b0P7CfCfCf1cKRRR#RRK9LA=PCAV<=KPE%ARRK9LAFPCAV9FKPE%1RRK9LA=PC16=KRK,8<PE%7KD=D=D=e%XReWAWDWCWBWEWJWIP6P7O2n2001000000121000000W0WHP6P7O2n2001000000121000000W0WGP6P7O2n2001000000121000000W0WMWLo"). Qed.

Section DT.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis HOWN : rt_own H.

  Definition shdrA (w : pmwA H) (m : mem) (sb : sbuf) : Prop :=
    match sb with
    | SShort => exists b0, rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] /\ 0 <= b0 < 256 /\ b0 mod 2 = 0
    | SLong d asz => exists b0 cp, rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] /\ 0 <= b0 < 256 /\ b0 mod 2 = 1
                     /\ rw_cells asegs m (wa_ff w + 5936) [C8 (Z_to_bv 64 cp)]
                     /\ rw_cells asegs m (wa_ff w + 5952) [C8 (Z_to_bv 64 d)] /\ 0 <= d < 2 ^ 64
    end.
  Lemma shdrA_keep : forall (w : pmwA H) m m' sb, shdrA w m sb -> ffkeep w m m' -> shdrA w m' sb.
  Proof.
    intros w m m' [|d asz] SH K; cbn [shdrA] in *.
    - destruct SH as (b0 & B0 & Hb). exists b0. split; [exact (K 5936 [C1 (b8 b0)] ltac:(lia) ltac:(cbn; lia) B0) | exact Hb].
    - destruct SH as (b0 & cp & B0 & Hb & Ho & CP & DP & Hd). exists b0, cp.
      split; [exact (K 5936 [C1 (b8 b0)] ltac:(lia) ltac:(cbn; lia) B0)|]. split; [exact Hb|]. split; [exact Ho|].
      split; [exact (K 5936 [C8 (Z_to_bv 64 cp)] ltac:(lia) ltac:(cbn; lia) CP)|].
      split; [exact (K 5952 [C8 (Z_to_bv 64 d)] ltac:(lia) ltac:(cbn; lia) DP) | exact Hd].
  Qed.

  Lemma str_dtor : forall (fl : bool) (w : pmwA H) s LB LBs m mo c msF R F fc (spal ty : Z) (sb : sbuf) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c S_STR TBL_EEF44 [] [] spal ->
    c_tr c = tr_of sb -> pm_bud (wa_n w) c -> (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf4164) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R (RT_S8D (if fl then 1 else 0)) -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    shdrA w m sb -> rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
    spal + pm_phi_blocks (tr_of sb) <= PM_RESERVE ->
    (forall (s1 : as_St H) (LB1 LBs1 : list block) msF1 mo1 m1 R1,
       as_AKREL H s1 (mkCfg msF1 mo1) ->
       as_VIS H s1 msF1 = MS R1 F (Z_to_bv 64 (if fl then OL_PUSHK else OL_CHECK)) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s1 LB1 LBs1 m1 mo1 (set_trA c []) (if fl then S_OPER else OB_PARSED_OPERAND :: S_INSTR) TBL_EEF44 [] [] (spal + pm_phi_blocks (tr_of sb)) ->
       pm_bud (wa_n w) (set_trA c []) ->
       regs_tbl w R1 RT_CHECK -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       (forall rr : reg, In rr [18%bv; 19%bv; 22%bv; 23%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) ->
       ffkeep w m m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros fl w s LB LBs m mo c msF R F fc spal ty sb Q OK X0 Htr BUD Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 SH TY SPAL KC.
    destruct sb as [|d asz]; cbn [shdrA] in SH.
    - destruct SH as (b0 & B0 & Hb0 & Hev).
      assert (CT : set_trA c [] = c) by (pose proof (set_trA_id c) as E; rewrite Htr in E; exact E).
      assert (SP0 : spal + pm_phi_blocks (tr_of SShort) = spal) by (rewrite pm_phi_tr_of; lia).
      destruct fl; cbn in HT0.
      + eapply (pm_s8d_s1 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc spal b0 ty Q OK X0 I Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 B0 (conj Hb0 Hev) TY).
        intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 KX1 FK1.
        apply (KC s LB LBs msF1 mo1 m1 R1 KR1 VIS1 RF1).
        * rewrite CT, SP0. exact X1.
        * rewrite CT. exact BUD.
        * exact (regs_tbl_sub w [] R1 _ RT_CHECK HT1 ltac:(vm_compute; reflexivity)).
        * exact G3_1.
        * exact G4_1.
        * exact KX1.
        * intros k cs Hk Hn C. exact (FK1 k cs Hk ltac:(lia) (Forall_nil _) C).
      + eapply (pm_s8d_s0 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc spal b0 ty Q OK X0 I Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 B0 (conj Hb0 Hev) TY).
        intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 KX1 FK1.
        apply (KC s LB LBs msF1 mo1 m1 R1 KR1 VIS1 RF1).
        * rewrite CT, SP0. exact X1.
        * rewrite CT. exact BUD.
        * exact (regs_tbl_sub w [] R1 _ RT_CHECK HT1 ltac:(vm_compute; reflexivity)).
        * exact G3_1.
        * exact G4_1.
        * exact KX1.
        * intros k cs Hk Hn C. exact (FK1 k cs Hk ltac:(lia) (Forall_nil _) C).
    - destruct SH as (b0 & cp & B0 & Hb0 & Hodd & CP & DP & Hd).
      assert (Htr' : c_tr c = [(d, asz)]) by (rewrite Htr; reflexivity).
      assert (TY0 : forall (N : Z) m1 m2, ffkeepX w [] m m1 ->
                (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= N -> rw_cells asegs m1 (wa_ff w + k) cs -> rw_cells asegs m2 (wa_ff w + k) cs) ->
                120 <= N -> rw_cells asegs m2 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)]).
      { intros N m1 m2 K1 K2 HN. apply (K2 116 [C4 (Z_to_bv 64 ty)] ltac:(lia) ltac:(cbn; lia)). exact (K1 116 [C4 (Z_to_bv 64 ty)] ltac:(lia) ltac:(cbn; lia) (Forall_nil _) TY). }
      destruct fl; cbn in HT0.
      + eapply (pm_s8d_l1 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc spal b0 cp d ty Q OK X0 I Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 B0 (conj Hb0 Hodd) CP DP Hd TY).
        intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G1_1 G2_1 G8_1 G10_1 KX1 FK1.
        eapply (pm_str_del H HHbp LINV LINV_cl HOWN w s LB LBs m1 mo1 c _ TBL_EEF44 [] spal msF1 R1 F fc 0xf4188 d asz Q OK X1
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Htr' BUD KR1 VIS1 RF1 G1_1 ltac:(reflexivity) ltac:(lia)
                  G2_1 G8_1 G4_1 G10_1 ltac:(unfold PM_PF; cbn; tauto) SPAL).
        intros msF2 mo2 m2 R2 s2 LB2 LBs2 KR2 VIS2 RF2 X2 BUD2 KEEP2 FK2.
        pose proof (regs_keep w [] R1 R2 RT_S8D1 HT1 KEEP2) as HT2. replace (rt_keep RT_S8D1) with RT_S8D1 in HT2 by (vm_compute; reflexivity).
        assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inlistS)); exact G3_1).
        assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inlistS)); exact G4_1).
        eapply (pm_s8d_p H HHbp LINV LINV_frame w s2 LB2 LBs2 m2 mo2 (set_trA c []) msF2 R2 F fc (spal + pm_phi_blocks [(d, asz)]) ty Q
                  OK X2 I (bsz_set_tr_nil c Hbsz) KR2 VIS2 RF2 FZ0 HT2 G3_2 G4_2 (TY0 _ m1 m2 FK1 FK2 ltac:(lia))).
        intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 KX3 FK3.
        apply (KC s2 LB2 LBs2 msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 BUD2).
        * exact (regs_tbl_sub w [] R3 _ RT_CHECK HT3 ltac:(vm_compute; reflexivity)).
        * exact G3_3.
        * exact G4_3.
        * intros rr Hrr. rewrite (KX3 rr Hrr), (KEEP2 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlistS)), (KX1 rr Hrr). reflexivity.
        * intros k cs Hk Hn C. apply (FK3 k cs Hk ltac:(lia) (Forall_nil _)). apply (FK2 k cs Hk ltac:(lia)). exact (FK1 k cs Hk ltac:(lia) (Forall_nil _) C).
      + eapply (pm_s8d_l0 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc spal b0 cp d ty Q OK X0 I Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 B0 (conj Hb0 Hodd) CP DP Hd TY).
        intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G1_1 G2_1 G8_1 G10_1 KX1 FK1.
        eapply (pm_str_del H HHbp LINV LINV_cl HOWN w s LB LBs m1 mo1 c _ TBL_EEF44 [] spal msF1 R1 F fc 0xf4188 d asz Q OK X1
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Htr' BUD KR1 VIS1 RF1 G1_1 ltac:(reflexivity) ltac:(lia)
                  G2_1 G8_1 G4_1 G10_1 ltac:(unfold PM_PF; cbn; tauto) SPAL).
        intros msF2 mo2 m2 R2 s2 LB2 LBs2 KR2 VIS2 RF2 X2 BUD2 KEEP2 FK2.
        pose proof (regs_keep w [] R1 R2 RT_S8D0 HT1 KEEP2) as HT2. replace (rt_keep RT_S8D0) with RT_S8D0 in HT2 by (vm_compute; reflexivity).
        assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inlistS)); exact G3_1).
        assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inlistS)); exact G4_1).
        eapply (pm_s8d_c H HHbp LINV LINV_frame w s2 LB2 LBs2 m2 mo2 (set_trA c []) msF2 R2 F fc (spal + pm_phi_blocks [(d, asz)]) ty Q
                  OK X2 I (bsz_set_tr_nil c Hbsz) KR2 VIS2 RF2 FZ0 HT2 G3_2 G4_2 (TY0 _ m1 m2 FK1 FK2 ltac:(lia))).
        intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 KX3 FK3.
        apply (KC s2 LB2 LBs2 msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 BUD2).
        * exact (regs_tbl_sub w [] R3 _ RT_CHECK HT3 ltac:(vm_compute; reflexivity)).
        * exact G3_3.
        * exact G4_3.
        * intros rr Hrr. rewrite (KX3 rr Hrr), (KEEP2 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlistS)), (KX1 rr Hrr). reflexivity.
        * intros k cs Hk Hn C. apply (FK3 k cs Hk ltac:(lia) (Forall_nil _)). apply (FK2 k cs Hk ltac:(lia)). exact (FK1 k cs Hk ltac:(lia) (Forall_nil _) C).
  Qed.
End DT.

Section IM.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HOWN : rt_own H.
  #[local] Notation ent := (Z * (Z * Z))%type (only parsing).

  Lemma HHi : asan_rt_hyps H.
  Proof. exact (proj1 HHbp). Qed.

  Lemma str_import_ok : forall (w : pmwA H) s LB LBs m mo c msF R F fc (r rid : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_STR TBL_EEF44 [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> pm_bud (wa_n w) c -> macctA c ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf31d8) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8C -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 r -> 0 < r < 2 ^ 31 ->
    rw_cells asegs m (wa_ff w + 9060) [C4 (Z_to_bv 64 rid)] -> 0 <= rid < 2 ^ 32 ->
    3 * (Zlength (t3c (c_m3 c)) + 1) <= wa_n w + 3 ->
    (forall (s1 : as_St H) (LB1 LBs1 : list block) msF1 mo1 m1 R1 F1 fc1 (t : Z * Z * list ent),
       as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 0xf4164) fc1 None m1 (seg_rom asegs) -> rfull R1 ->
       frm_zero fc1 ->
       PMXA H LINV w s1 LB1 LBs1 m1 mo1 (set_m3A c t) S_STR TBL_EEF44 [] ->
       pm_bud (wa_n w) (set_m3A c t) -> (forall q k, In (q, k) (c_blocks (set_m3A c t)) -> k <= 2 ^ 40) -> macctA (set_m3A c t) ->
       Zlength (t3c (c_m3 c)) <= Zlength (t3c t) <= Zlength (t3c (c_m3 c)) + 1 ->
       regs_tbl w R1 RT_S8D1 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       (forall rr : reg, In rr [18%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) ->
       ffkeepX w [] m m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc r rid Q OK X0 Hbsz BUD MAC KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX10 Hr CD0 Hrid ACC KC.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_n H w OK) as WN.

    eapply (pm_s8i_ea H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc r Q OK X0 I Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX10 Hr).
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G21_1 FK1 KX1.

    eapply (pm_s8i_eb H HHbp LINV LINV_frame w s LB LBs m1 mo1 c msF1 R1 F fc Q OK X1 I Hbsz KR1 VIS1 RF1 FZ0 HT1 G3_1 G4_1).
    intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 G1_2 G2_2 G10_2 G11_2 FK2 KX2.
    assert (FK12 : ffkeepX w [] m m2) by (eapply (ffkeepX_trans w [] [] [] m m1 m2 FK1 FK2); apply incl_refl).
    assert (CD2 : rw_cells asegs m2 (wa_ff w + 9060) [C4 (Z_to_bv 64 rid)])
      by (eapply (ffkeepX_cell w _ m m2); [exact FK12 | exact CD0 | lia | cbn; lia | vm_compute; reflexivity]).
    assert (AK2 : accessible m2 (wa_ff w + 9060) 4).
    { apply (ff_accessible m2 (wa_ff w) _ 9060 4 (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2)); [lia | lia | lia | lia | unfold AAPP_HI; lia | vm_compute; reflexivity]. }

    eapply (pm_emh_m3 H HHbp LINV LINV_cl LINV_relro HOWN w s LB LBs m2 mo2 c _ TBL_EEF44 [] msF2 R2 F fc 0xf31f4 9060 rid Q
              OK X2 ltac:(vm_compute; reflexivity) ltac:(reflexivity) KR2 VIS2 RF2 FZ0 G1_2 eq_refl ltac:(lia) G2_2 G4_2 G10_2 G11_2
              AK2 ltac:(lia) ltac:(lia) eq_refl CD2 Hrid BUD ACC).
    intros msF7 mo7 m7 s7 LB7 LBs7 F7 fc7 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 p v tt inserted
           KR7 VIS7 FZ7 X7 Hin7 Hv7 Hlen7 Hni7 Hins7 BUD7 Hbk7 Hbs7 Hlast7 FFC7.
    match type of VIS7 with _ = MS ?RR _ _ _ _ _ _ => set (R7 := RR) in * end.
    assert (RF7 : rfull R7) by apply rfull_mkR.
    assert (KEEP7 : forall r0, In r0 KEPT_REGS -> PropExec.getr R7 r0 = PropExec.getr R2 r0).
    { intros r0 Hr0. unfold KEPT_REGS in Hr0. cbn [In] in Hr0.
      destruct Hr0 as [<-|Hr0]; [rewrite G1_2; reflexivity|].
      repeat (destruct Hr0 as [<-|Hr0]; [reflexivity|]). destruct Hr0. }
    assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (KEEP7 3%bv ltac:(inlistR)); exact G3_2).
    assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (KEEP7 4%bv ltac:(inlistR)); exact G4_2).
    assert (G10_7 : PropExec.getr R7 10%bv = Z_to_bv 64 (p + 20)) by reflexivity.
    pose proof (regs_keep w [] R2 R7 RT_S8M HT2 KEEP7) as HT7. change (rt_keep RT_S8M) with RT_S8M in HT7.
    pose proof (ffkeepX_nil w m2 m7 FFC7) as FK7.

    destruct tt as [[bl bc] ents]. cbn [t3a t3b t3c fst snd] in Hin7, Hlen7, Hni7, Hins7, Hbk7.
    destruct (in_split _ _ Hin7) as (l1 & l2 & Eents).
    assert (M3c : m3okA (t3c (c_m3 c))) by (destruct MAC as (_ & _ & _ & M); exact M).
    assert (M3E : m3okA ents).
    { destruct inserted.
      - destruct (Hins7 eq_refl) as [_ HP]. unfold m3okA in M3c |- *. rewrite Forall_forall in M3c |- *. intros e He.
        apply (Permutation_in _ HP) in He. destruct He as [<- | He]; [cbn; lia | exact (M3c e He)].
      - rewrite (Hni7 eq_refl). exact M3c. }
    set (c7 := set_m3A c (bl, bc, ents)) in *.
    assert (Hbsz7 : forall q0 k0, In (q0, k0) (c_blocks c7) -> k0 <= 2 ^ 40) by (exact (bsz_set_m3A (wa_n w) c (bl, bc, ents) WN Hbsz BUD7)).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7) as RH7.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7) as [OWN1 OWN2].
    assert (XBc : In (p, 24) (c_blocks c7)).
    { apply (Permutation_in _ (Permutation_sym (cbk_m3 c7))). apply in_or_app; left. unfold mblk3, c7, set_m3A. cbn [c_m1 c_m2 c_m3 t3a t3b t3c fst snd].
      unfold umap_blocks. apply in_or_app; right. apply in_map_iff. exists (p, (rid, v)). split; [reflexivity | exact Hin7]. }
    destruct (xb_facts H HHi w s7 LB7 LBs7 [] m7 c7 (p, 24) OK RH7 OWN1 OWN2 XBc) as (pid & XB1 & XB2 & XB3 & XBR). cbn [fst snd] in XB1, XB2, XB3, XBR.
    pose proof XBR as (R0 & R16 & Rn & RI & RC & RF' & RAPP).
    pose proof (blk_apart_ff H HHi w s7 LB7 m7 _ OK RH7 XB2) as HQF. cbn [blk_addr blk_size fst snd] in HQF.
    pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7) as (SHc7 & _).
    pose proof (proj1 (proj2 (proj2 SHc7))) as SH37. unfold c7 in SH37. cbn [set_m3A c_m3 t3a t3b t3c fst snd] in SH37.
    assert (AD7 : addressable m7 p 24) by (exact (proj2 SH37 p rid v Hin7)).

    eapply (pm_s8i_h1 H HHbp LINV LINV_frame w s7 LB7 LBs7 m7 mo7 c7 msF7 R7 F7 fc7 p Q OK X7 I Hbsz7 KR7 VIS7 RF7 FZ7 HT7 G3_7 G4_7 G10_7
              ltac:(clear - R0 R16 RC AC1 AC2; split; [Z.div_mod_to_equations; lia | lia]) AD7 HQF).
    intros msF8 mo8 m8 R8 KR8 VIS8 RF8 X8 HT8 G3_8 G4_8 G10_8 FK8 KX8.
    assert (G21_8 : PropExec.getr R8 21%bv = Z_to_bv 64 (sx32A r)).
    { rewrite (KX8 21%bv ltac:(inlistS)), (KEEP7 21%bv ltac:(inlistR)), (KX2 21%bv ltac:(inlistS)), G21_1, HX10.
      unfold sx32A, PrsGrammar.sx32. replace (r <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    unfold c7 in X8. rewrite Eents in X8.

    eapply (pm_sw_m3 H HHbp LINV LINV_cl w s7 LB7 LBs7 m8 mo8 c _ TBL_EEF44 [] msF8 R8 F7 fc7 bl bc l1 l2 p rid v r Q
              OK X8 ltac:(vm_compute; reflexivity) ltac:(reflexivity) KR8 VIS8 RF8 G10_8 G21_8 ltac:(lia)).
    intros msF9 mo9 m9 R9 KR9 VIS9 RF9 X9 HR9 FFC9.
    assert (Elen : Zlength (l1 ++ (p, (rid, r)) :: l2) = Zlength ents) by (rewrite Eents; unfold Zlength; rewrite !length_app; reflexivity).
    assert (M3F : m3okA (l1 ++ (p, (rid, r)) :: l2)).
    { unfold m3okA in M3E |- *. rewrite Eents in M3E. apply Forall_app in M3E as [A1 A2]. apply Forall_cons_iff in A2 as [_ A3].
      apply Forall_app. split; [exact A1 | apply Forall_cons; [cbn; lia | exact A3]]. }
    set (c9 := set_m3A c (bl, bc, l1 ++ (p, (rid, r)) :: l2)) in *.
    assert (BUD9 : pm_bud (wa_n w) c9).
    { clear - BUD7 Elen. unfold c7 in BUD7. unfold pm_bud in BUD7 |- *. unfold c9.
      cbn [set_m3A c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd] in BUD7 |- *. rewrite Elen. exact BUD7. }
    assert (Hbsz9 : forall q0 k0, In (q0, k0) (c_blocks c9) -> k0 <= 2 ^ 40) by (exact (bsz_set_m3A (wa_n w) c _ WN Hbsz BUD9)).
    assert (MAC9 : macctA c9).
    { apply (macct_set_m3A c _ MAC); cbn [t3a t3b t3c fst snd]; [rewrite Elen; lia | exact Hbk7 | exact Hbs7 | exact Hlast7 | exact M3F]. }
    assert (LEN9 : Zlength (t3c (c_m3 c)) <= Zlength (t3c (bl, bc, l1 ++ (p, (rid, r)) :: l2)) <= Zlength (t3c (c_m3 c)) + 1)
      by (cbn [t3c fst snd]; rewrite Elen; exact Hlen7).
    pose proof (regs_tbl_eqR w R8 R9 RT_S8M HT8 HR9) as HT9.
    assert (G3_9 : PropExec.getr R9 3%bv = wa_gp w) by (rewrite (HR9 3%bv); exact G3_8).
    assert (G4_9 : PropExec.getr R9 4%bv = wa_tp w) by (rewrite (HR9 4%bv); exact G4_8).

    eapply (pm_s8i_h3 H HHbp LINV LINV_frame w s7 LB7 LBs7 m9 mo9 c9 msF9 R9 F7 fc7 Q OK X9 I Hbsz9 KR9 VIS9 RF9 FZ7 HT9 G3_9 G4_9).
    intros msF10 mo10 m10 R10 KR10 VIS10 RF10 X10 HT10 G3_10 G4_10 KX10 EM10. subst m10.
    assert (FKA : ffkeepX w [] m m9).
    { eapply (ffkeepX_trans w [] [] [] m m2 m9 FK12); [| apply incl_refl | apply incl_refl].
      eapply (ffkeepX_trans w [] [] [] m2 m7 m9 FK7); [| apply incl_refl | apply incl_refl].
      eapply (ffkeepX_trans w [] [] [] m7 m8 m9 FK8 (ffkeepX_nil w m8 m9 FFC9)); apply incl_refl. }
    assert (KXA : forall rr : reg, In rr [18%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv] -> PropExec.getr R10 rr = PropExec.getr R rr).
    { intros rr Hrr. cbn in Hrr. destruct Hrr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
      - rewrite (KX10 18%bv ltac:(inlistS)), (HR9 18%bv), (KX8 18%bv ltac:(inlistS)), (KEEP7 18%bv ltac:(inlistR)), (KX2 18%bv ltac:(inlistS)). exact (KX1 18%bv ltac:(inlistS)).
      - rewrite (KX10 22%bv ltac:(inlistS)), (HR9 22%bv), (KX8 22%bv ltac:(inlistS)), (KEEP7 22%bv ltac:(inlistR)), (KX2 22%bv ltac:(inlistS)). exact (KX1 22%bv ltac:(inlistS)).
      - rewrite (KX10 23%bv ltac:(inlistS)), (HR9 23%bv), (rt_get w [] R8 RT_S8M 23%bv (EVar 32) HT8 eq_refl), (rt_get w [] R RT_S8C 23%bv (EVar 32) HT0 eq_refl). reflexivity.
      - rewrite (rt_get w [] R10 RT_S8D1 24%bv (EAlu ALU_ADD (EVar 33) (ELit 7984)) HT10 eq_refl), (rt_get w [] R RT_S8C 24%bv (EAlu ALU_ADD (EVar 33) (ELit 7984)) HT0 eq_refl). reflexivity.
      - rewrite (KX10 25%bv ltac:(inlistS)), (HR9 25%bv), (KX8 25%bv ltac:(inlistS)), (KEEP7 25%bv ltac:(inlistR)), (KX2 25%bv ltac:(inlistS)). exact (KX1 25%bv ltac:(inlistS)).
      - rewrite (rt_get w [] R10 RT_S8D1 26%bv (EAlu ALU_ADD (EVar 33) (ELit 112)) HT10 eq_refl), (rt_get w [] R RT_S8C 26%bv (EAlu ALU_ADD (EVar 33) (ELit 112)) HT0 eq_refl). reflexivity. }
    exact (KC s7 LB7 LBs7 msF10 mo10 m9 R10 F7 fc7 (bl, bc, l1 ++ (p, (rid, r)) :: l2) KR10 VIS10 RF10 FZ7 X10 BUD9 Hbsz9 MAC9 LEN9 HT10 G3_10 G4_10 KXA FKA).
  Qed.
End IM.
