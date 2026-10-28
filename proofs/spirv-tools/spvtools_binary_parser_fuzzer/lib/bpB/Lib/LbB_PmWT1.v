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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec LbB_PmVup LbB_PmGlue LbB_PmVops LbB_PmHdr LbB_PmExit2 LbB_PmLH LbB_PmOL LbB_PmVS LbB_ContStmt LbB_PmWKit LbB_PmWG LbB_PmWVo LbB_PmWP1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmOLX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmWT1 () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List2InI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01C47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28expr_eqbC47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX2=expr_eqb_trueC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic3notC47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3orbI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<asan_rt_hypsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCasan_rt_hyps_bp_extC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCalloc_ok_of_live_bpC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface9RHEAP_ahmC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceAannotate_gen_stmtC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface7cost_bpI47Corelib4Init5Logic3and00C47Corelib4Init5Logic5proj1I6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4pmwA00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn7pmw_okA00I6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOLX4OBAS00C46Stdlib5Lists4List4inclK47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission6LibPrs9PmODefsS14i_opC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission6LibPrs9PmODefsS14i_ioC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC5ARocqVerifyHarness?AgentSubmission7LibCont4CRep4mdefC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_v1c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT17tl_cutAI6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5PMXAT00K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISK47Corelib4Init9Datatypes6option02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9regs_tblXC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_gpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_tpC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_trC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_blocksC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL6ipureAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL5ictxAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL4ifrAC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_icountC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_endianC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase9c_reqconvC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8wa_wordsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_nC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH6macctAC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_v3C5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3bI47Corelib5Lists7ListDef6Forall00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PmExit2=pmxa_restrictC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7pm_geomC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_ffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_s1C56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_loC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6wa_sp0C56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC56Stdlib6ZArith6BinInt1Z2ltC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac:pmw_boundsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_consC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5xa_v1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB3lblK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission7LibCont4CRep3fldC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z3mulC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6xa_fwrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3fszC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atI47Corelib4Init9Datatypes6option00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_OwnArw_cells_of_wr_hiC56Stdlib6ZArith6BinInt1Z6to_natK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell05C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut>env_world_seedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9env_worldK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry05K47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut:pm_kn_baseC47Corelib4Init9Datatypes3appK5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond06C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut<regs_tbl_extC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6xboundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7tbl_okXC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut:tbl_closedC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7keys_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut8fkeys_okK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac<ev_world_allC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9wenv_valsC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5br_eqC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC56Stdlib6NArith6BinNat1N3lebC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC46Stdlib5Lists4List9nth_errorC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac8ev_xseedC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26adenotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac8estart_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv@adenot_of_estartC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue:sc_rd_fld8C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic5proj2K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6br_geuC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit:sym_insideC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC46Stdlib5Lists4List7forallbK47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit7fsh_patC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit6lbytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots9upd_slotsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots9add_slotsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut=sr_tbl_checkXC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9scal_noneC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall;keys_nonnegc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT18intbl_InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall9obj_sh_okC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac6ev_addC56Stdlib6NArith6BinNat1N6of_natC56Stdlib6NArith6BinNat1N3addC56Stdlib6NArith6BinNat1N2leC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut@wenv_vals_lengthC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut<edenot_app_xC47Corelib4Init5Logic6eq_symC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue6rt_getC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops6ffkeepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmVup7set_v1AC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List9app_nil_rC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_m1C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_m2C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_m3C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_v2C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7ZlengthC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase6c_widxK5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase3pmc01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP19pm_vpush1C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmHdr4WADDC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_TRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8trace_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn5wk_trI47Corelib4Init5Logic2or00C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission7LibCont9ContStmts5vgrowC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_ContStmt8v4_newLBC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<as_lb_removeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ablock_rangeC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmVS3E_PC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmVS4E_SHC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega5Tauto8GFormula06C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops<ffkeep_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmVS?pm_vstore_same1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWVo9pm_vopnd1K45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3cC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase6pm_budC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC56Stdlib6ZArith6BinInt1Z3divC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3aC5ARocqVerifyHarness?AgentSubmission7LibCont4CRep8vec_opndC4ARocqVerifyHarness?AgentSubmission8LibIface4liveK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula08C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut=pm_kn_base_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac8pmk_sh_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_diagC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_userC4ELinuxProcessSemantics5Riscv3Sem<branch_takenK46Stdlib9micromega5Tauto8GFormula07C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue9rt_lookupC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call6inb_InC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sr_getC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6pm_runI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1Z01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6S_OPERC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL9TBL_EEF44C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4O_V1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4AC_AC5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4LY_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4MI_AC5ARocqVerifyHarness?AgentSubmission7LibCont4CRep7OPND_SZC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsK46Stdlib9micromega=RingMicromega3Op201I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT13HHmK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT18RT_TLA_FC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP16ESH224I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib6ZArith4Znat7nat_N_ZC56Stdlib6ZArith4Znat3N2Z7inj_addC56Stdlib6ZArith4Znat3N2Z6inj_lec6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT16RT_TLAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP18VP1_KEPTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmHdr5SH_FFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL8OL_PUSHKc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWT18RT_TLA_SC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_ContStmt<VOPND_DEL_RAC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface4bptrC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmWG7V4_KEPTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmVS8VSO_KEPTI5ARocqVerifyHarness?AgentSubmission6LibPrs9PmODefsS15ictxR00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockC4ARocqVerifyHarness?AgentSubmission8LibIface3memI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase3pmc00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL8RT_PUSHKC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AFS_HDRK47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes:comparison00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt9PM_FCLASSI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00K47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5WV_S1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6WV_SP0C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<AANNOTATE_CCC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_ContStmt@VOPND_SLOW_ENTRYI5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI46Stdlib5Lists4List6Exists00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4WV_PC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6PM_OWNC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut4FSHBC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7PM_OBJSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6PM_NSHC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5WV_FFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP14E912C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP14E944C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP14E896C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface9APC0_FREEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt:PM_DEL_RAS".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma intbl_In : forall (k : Z) (e : expr) (l : list (Z * expr)),
  existsb (fun p : Z * expr => Z.eqb k (fst p) && expr_eqb e (snd p)) l = true -> In (k, e) l.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmWT1 ()) [] "p'0h01pi001ph12Hxh22EEh31lh41bi011bh51ei021eh62e0h72k'h81Hh92IHh:2NEh;1ah<2e'h=1kh>1ri031ri041ni051zp;2p;1p;3p;6p;5p;4p10000p4p710g000MR0p4p710p8g000iR1j2LTg001Ij1KTg001ij3DTg002Fj3@Tg002cj34Tg003?j31Tg003Vj32TP0j6;Tg0040j1?Tg004Pj2>Tg004oj37Tg005Oj2JTg0061j2:Tg006NR0j2ITg0071j28Tg007kj29Tg008Ij2=Tg008cj3FTg009bj6CTg00:@j3ETg00:Zj3<Tg00;4j1BTg00;Mj5GTg00;oj4HTg00<Oj2ATf3R2f2R3':f1R4f0R5'8'9p=3g00<lR6g00=LR7725p=6g00=lR8g00>JR9P4P5CHp=01A45=267p=51L89R:#KR;P:f4R<AD895R=P2A@895R>C3X0:=4:5#610<2R?=1:4[X3;g00?BR@=267P6P@P6p-0P5g00?bRAg00@?n0110100020000X66g00@[P7P5E;PA%?:RA91:?/>5b8W1P2P=P3P>C3X0:=4:A#61023RB=1:A[eP1P8P9f6R1P=f5RAP>C3X0:=4:5#6101A=1:4[f7RCP=P1P>C3X0:A7:3454:#610C1A7:2351:[[^3;P5f9RDP=f8REP>C3X0:=4:5#610DERF=1:4[PDP2PEP3C3f:R2P=PDP>C3X0:RG=4:4'51J2<A282<1:2<'If;R</:AP6P0f<R0=281f=RA/8CRH,94f?RIP=f>RJP>C3X0:=4:1RK'510IJRLA7:FC51:]1P4A28ACRMP8PJ18JERJ,97f@RNP=PIP>C3X0:=4:C'510NI104D=7:E51:]1X78197H/5KPJP61=6518ID=265P6fA/8<=265fDRIP=fCRJP>C3X0:=4:<,5410IJ10IARA=7:051:]1]2P418N2RN#6PJP=fBR=P>C3X0:=4:2R>,5710J0R710J=RJ52:ROA1:J<RJP9P010I592:AX591=:7P=AF=04EC3EW1W2A26N@15@>P2P5O19<OJW1W2n0110100020000P5P3O2b2b4W1PEP5E;W6P5O1%BM19@H/5KA2:FLA1:LCP1P5O13<W1W:P5O1n10210110300021110210104P3O1b4b>W1A7:B494:G#6102DA7:?351:[eW9X3;X<9X78P4P5O2n2001100000121105102X;:P5DGW3X59X=8o"). Qed.
Ltac intbl := apply intbl_In; vm_cast_no_check (@eq_refl bool true).

Definition RT_TLA : list (reg * expr) :=
  [(2%bv, EVar WV_S1);
   (8%bv, EVar WV_SP0);
   (9%bv, EVar WV_S1);
   (10%bv, WADD WV_P 224);
   (11%bv, ELit 20);
   (20%bv, SH_FF);
   (24%bv, WADD WV_FF 7984);
   (26%bv, WADD WV_FF 112);
   (27%bv, ELit 18446744073709551608)].

Definition RT_TLA_F : list (reg * expr) :=
  [(1%bv, ELit 0xf1928); (2%bv, EVar WV_S1); (9%bv, EVar WV_S1); (10%bv, EVar 43); (11%bv, EVar 42); (12%bv, EVar 41);
   (13%bv, EAlu ALU_ADD (EVar 41) (ELit 20)); (21%bv, EVar 41); (23%bv, EAlu ALU_ADD (EVar 41) (ELit 20)); (26%bv, WADD WV_FF 112); (8%bv, EVar WV_SP0); (20%bv, SH_FF); (24%bv, WADD WV_FF 7984); (27%bv, ELit 18446744073709551608)].

Definition RT_TLA_S : list (reg * expr) :=
  [(1%bv, ELit 0xf1950); (2%bv, EVar WV_S1); (9%bv, EVar WV_S1); (10%bv, WADD WV_P 216); (11%bv, WADD WV_FF 112); (26%bv, WADD WV_FF 112); (8%bv, EVar WV_SP0); (20%bv, SH_FF); (24%bv, WADD WV_FF 7984); (27%bv, ELit 18446744073709551608)].

Definition RT_VS1 : list (reg * expr) := [(9%bv, EVar WV_S1); (10%bv, EVar 41)].
Definition RT_VS1' : list (reg * expr) := [(9%bv, EVar WV_S1); (10%bv, WADD WV_P 224); (11%bv, ELit 20); (23%bv, EVar 41)].
Definition VS1_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv.

Section TLA.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis HOWN : rt_own H.
  Hypothesis HVO : vopnd_slow_stmt H.

  Lemma HHm : asan_rt_hyps H.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmWT1 ()) ["TLA"] "p;2p;1p;3g00A7j27Tg00B7j26Tg00C@j12Tg00DIj21Tg00EHj15Tg00FOj13Tg00GLj20Tg00Ggj34Tp,5HCEILR0p,1HR1'71601%211101%50%31'0'0'0'0p,4HHbp34o"). Qed.

  Lemma tl_vsame1 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1950) fc None m (seg_rom asegs) -> rfull R ->
    tbl_closed tbl = true -> keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true ->
    tbl_closed ftbl = true -> fkeys_ok (map fst ftbl) = true ->
    In (448, E896) tbl -> In (464, ESH224) tbl ->
    PropExec.getr R 9%bv = Z_to_bv 64 (wa_s1 w) ->
    PropExec.getr R 10%bv = Z_to_bv 64 (t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c)) ->
    (forall msF2 mo2 m2 R2, as_AKREL H s (mkCfg msF2 mo2) ->
       as_VIS H s msF2 = MS R2 F (Z_to_bv 64 0xf1970) fc None m2 (seg_rom asegs) -> rfull R2 ->
       PMXAT H LINV w s LB LBs m2 mo2 c ins tbl ftbl TB spal ->
       (forall r, In r VS1_KEPT -> PropExec.getr R2 r = PropExec.getr R r) ->
       PropExec.getr R2 10%bv = Z_to_bv 64 (wa_p w + 224) -> PropExec.getr R2 11%bv = Z_to_bv 64 20 ->
       PropExec.getr R2 23%bv = Z_to_bv 64 (t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c)) ->
       ffkeep w m m2 ->
       as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc Q OK X KR VIS RF Hc Hk Hknn Hfc Hfk H448 H464 G9 G10 K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as V1.
    destruct (c_v1 c) as [[b n] cap] eqn:EV1. cbn [t3a t3b t3c fst snd] in *.
    pose proof V1 as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2).
    set (e := b + OPND_SZ * n) in *.
    assert (Hbr : 0 <= b /\ b + OPND_SZ * cap <= 2 ^ 63) by (destruct Hb as [[-> ->]|(B1 & B2 & B3 & B4 & _)]; unfold OPND_SZ in *; lia).
    assert (He : 0 <= e <= b + OPND_SZ * cap) by (unfold e, OPND_SZ in *; lia).
    set (Xv := [Z_to_bv 64 e]) in *.
    assert (HE : env_world H w (Eseed R (wenv_vals w ++ Xv))) by apply env_world_seed.
    pose proof (ev_p H w _ OK HE) as EP.
    assert (HTv : regs_tblX w Xv R RT_VS1).
    { unfold regs_tblX, RT_VS1. repeat (apply Forall_cons); [| | apply Forall_nil]; cbn [fst snd].
      - rewrite G9. reflexivity. - rewrite G10. reflexivity. }
    assert (HK0 : know_ok asegs (Eseed R (wenv_vals w ++ Xv)) m
              (PM_KN_FIX ++ slot_kn [(464, ESH224); (448, E896)] ++ [KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) SHBASE) 1 (ELit 0)])).
    { destruct (pm_kn_fix_ok H HHm LINV w s LB LBs m mo c ins tbl ftbl TB spal _ OK X HE Hc Hk Hfc Hfk) as (K1 & K2 & _).
      unfold know_ok. apply Forall_app. split; [exact K1|]. apply Forall_app. split.
      - cbn [slot_kn map fst snd]. apply Forall_cons; [exact (K2 _ _ H464)|]. apply Forall_cons; [exact (K2 _ _ H448) | apply Forall_nil].
      - unfold know_ok. pmk_list H HHm w OK X HE. }
    pm_goR0 HHm (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) KR VIS RF HTv Xv
      (PM_KN_FIX ++ slot_kn [(464, ESH224); (448, E896)] ++ [KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) SHBASE) 1 (ELit 0)])
      HK0 40%nat [0xf1970] (@nil bool) 42%N RT_VS1'.
    { split_scs. }
    intros msF1 mo1 R1 KR1 MP1 VIS1 RF1 MI1 HT1 HR1 Hlf1.
    lazymatch type of VIS1 with _ = MS _ _ _ _ _ ?mm _ => set (M1 := mm) in * end.
    pose proof (munch_sym (Eseed R (wenv_vals w ++ Xv)) m _ [(EVar WV_P, 224, 232)] Hlf1 ltac:(vm_compute; reflexivity)) as MU1.
    cbn [num_wins map] in MU1. rewrite EP in MU1. fold M1 in MU1.
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK.
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) STK ltac:(lia)) as [STK1 _].
    assert (OMP : forall y k, Forall (omiss (Eseed R (wenv_vals w ++ Xv)) (EVar WV_P) y k) (s_log SSr)).
    { intros y k. subst SSr. cbn [s_log]. apply Forall_cons; [| apply Forall_nil]. intros Hne. cbn in Hne. discriminate. }
    assert (X1 : PMXAT H LINV w s LB LBs M1 mo1 c ins tbl ftbl TB spal).
    { assert (CV : set_v1A c (c_v1 c) = c) by (destruct c; reflexivity).
      rewrite <- CV. rewrite EV1.
      replace (b, n, cap) with (t3a (c_v1 c), n, t3c (c_v1 c)) by (rewrite EV1; reflexivity).
      eapply (pmxa_vupd1 H HHm LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal M1 mo1 [(wa_p w + 224, wa_p w + 232)] []);
        [exact OK | exact X | exact Hknn | exact Hfk | rewrite app_nil_r; exact MU1 | apply wmono_mem_denot
        | intros x Hx; apply mem_denot_defined; exact Hx | exact MP1 | exact MI1 | subst M1; apply stk_mem_denot; exact STK1
        | apply Forall_cons; [| apply Forall_nil] | apply Forall_nil | |].
      - split; [cbn; lia|]. left. cbn [fst snd]. unfold O_V1. lia.
      - rewrite EV1. cbn [t3a t3c fst snd]. unfold vec_opnd.
        split; [exact Hv|]. split; [exact Hv'|]. split; [intros i Hi; apply mem_denot_defined; apply HD; lia|].
        split; [exact Hlen|]. split; [exact Hb|]. split; [| split].
        + replace (wa_p w + O_V1) with (wa_p w + 216) by reflexivity.
          eapply (fld_field_after (Eseed R (wenv_vals w ++ Xv)) m _ (EVar WV_P) (wa_p w) 216 8 b Hlf1 EP);
            [apply OMP | vm_compute; reflexivity | lia | cbn; lia | exact F0].
        + replace (wa_p w + O_V1 + 8) with (wa_p w + 224) by (unfold O_V1; lia).
          assert (SV : sval (Eseed R (wenv_vals w ++ Xv)) (s_log SSr) (EVar WV_P) 224 8 e = e).
          { unfold sval. subst SSr. cbn [s_log]. lfield_rw. cbv beta iota. ev_xs. rewrite u64_of_Z by lia. reflexivity. }
          enough (FF1 : fld ASEGS M1 (wa_p w + 224) 8 (sval (Eseed R (wenv_vals w ++ Xv)) (s_log SSr) (EVar WV_P) 224 8 e)) by (rewrite SV in FF1; exact FF1).
          eapply (fld_field_after (Eseed R (wenv_vals w ++ Xv)) m _ (EVar WV_P) (wa_p w) 224 8 e Hlf1 EP);
            [apply OMP | vm_compute; reflexivity | lia | cbn; lia | replace (wa_p w + 224) with (wa_p w + O_V1 + 8) by (unfold O_V1; lia); exact F1].
        + replace (wa_p w + O_V1 + 16) with (wa_p w + 232) by (unfold O_V1; lia).
          eapply (fld_field_after (Eseed R (wenv_vals w ++ Xv)) m _ (EVar WV_P) (wa_p w) 232 8 (b + OPND_SZ * cap) Hlf1 EP);
            [apply OMP | vm_compute; reflexivity | lia | cbn; lia | replace (wa_p w + 232) with (wa_p w + O_V1 + 16) by (unfold O_V1; lia); exact F2].
      - rewrite EV1. cbn [t3a t3b t3c fst snd]. intros NZ. cbn [t3a t3b t3c fst snd] in NZ |- *.
        pose proof (proj1 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)) as (_ & _ & _ & S4 & _). rewrite EV1 in S4. specialize (S4 NZ). cbn [t3a t3b t3c fst snd] in S4.
        destruct Hb as [[B0 C0]|(Bpos & B16 & Cpos & Bhi & Hlive & Bapart)]; [exfalso; lia|].
        pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
        assert (BLK : exists pid, In (pid, b, OPND_SZ * cap) LBs /\ In (pid, b, OPND_SZ * cap) LB /\ In (b, OPND_SZ * cap) (lbl LB) /\ ablock_range H b (OPND_SZ * cap) /\ OPND_SZ * cap <= 2 ^ 31).
        { apply (cblk_facts H HHm LINV w s LB LBs m mo c ins tbl ftbl TB spal b (OPND_SZ * cap) OK X).
          unfold c_blocks. rewrite EV1. cbn [t3a t3c fst snd]. rewrite !in_app_iff. right; right; right; left.
          unfold vec_opnd_blocks. destruct (Z.eqb_spec b 0); [lia | left; reflexivity]. }
        destruct BLK as (pid & _ & _ & _ & (R0 & R16 & Rn & RI & RC & RF' & RAPP) & SZ).
        pose proof (aapp_bounds _ _ RAPP Rn) as (AB1 & AB2 & AB3 & AB4 & AB5).
        pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE b (OPND_SZ * cap) PA ltac:(lia) ltac:(lia) ltac:(lia)) as DSH.
        eapply SHAD_transport; [exact S4 | exact MU1 | apply wmono_mem_denot |].
        rewrite RtB_Iface.cc_gen_length by lia. cbn [disjoint_from]. unfold PARSER_SIZE in DSH. split; [lia | exact I]. }
    eapply (K msF1 mo1 M1 R1 KR1 VIS1 RF1 X1).
    - intros r0 Hr0. rewrite (HR1 r0). unfold VS1_KEPT in Hr0.
      repeat (destruct Hr0 as [<-|Hr0]; [first [rewrite G9; reflexivity | reflexivity] |]). destruct Hr0.
    - rtf HT1.
    - rtf HT1.
    - rtf HT1.
    - apply (ffkeep_munch w _ m M1 MU1 (wmono_mem_denot _ _ _)). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      pose proof (p_apart_ff H w OK) as PAF. unfold O_WIDX, PARSER_SIZE in PAF. lia.
  Qed.

  Definition tl_cutA (spal : Z) (w : pmwA H) (I : ictxR) (c : pmc) (t : Z) (m : mem) (F : bvmap 5 word) (fc : bv 32) (Q : config -> Prop) : Prop :=
    forall s1 LB1 LBs1 msF1 mo1 m1 R1 (b1 cap1 : Z),
      as_AKREL H s1 (mkCfg msF1 mo1) ->
      as_VIS H s1 msF1 = MS R1 F (Z_to_bv 64 0xf1970) fc None m1 (seg_rom asegs) -> rfull R1 ->
      PMXAT H LINV w s1 LB1 LBs1 m1 mo1 (set_v1A c (b1, t3b (c_v1 c) + 1, cap1)) S_OPER TBL_EEF44 [] [] spal ->
      regs_tbl w R1 RT_TLA -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      PropExec.getr R1 22%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R1 25%bv = Z_to_bv 64 (i_io I) -> PropExec.getr R1 18%bv = Z_to_bv 64 t ->
      PropExec.getr R1 23%bv = Z_to_bv 64 (b1 + OPND_SZ * (t3b (c_v1 c) + 1)) ->
      pm_bud (wa_n w) (set_v1A c (b1, t3b (c_v1 c) + 1, cap1)) -> t3b (c_v1 c) + 1 <= cap1 ->
      ffkeep w m m1 ->
      as_SR H Q (mkCfg msF1 mo1).

  Lemma tl_segA : forall (spal : Z) (w : pmwA H) (I : ictxR) s LB LBs m mo c msF R F fc tbl (t : Z) (Q : config -> Prop),
    pmw_okA H w -> OBAS H LINV w s LB LBs m mo c msF R F fc I OL_PUSHK RT_PUSHK S_OPER tbl spal -> incl TBL_EEF44 tbl ->
    PropExec.getr R 22%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R 25%bv = Z_to_bv 64 (i_io I) -> PropExec.getr R 18%bv = Z_to_bv 64 t ->
    mdef m (wa_ff w + 112) 20 ->

    (t3b (c_v1 c) = t3c (c_v1 c) -> forall b'' n'', pm_bud (wa_n w) (set_v1A c (b'', n'', vgrow (t3c (c_v1 c))))) ->
    tl_cutA spal w I c t m F fc Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros spal w I s LB LBs m mo c msF R F fc tbl t Q OK OB INCL G22 G25 G18 MD BUDG CUT.
    destruct OB as [X00 KR VIS RF FZ HT G3 G4 TR BSZ BUD IP ICTX IFR IC END WW ACC V3R].
    assert (X0 : PMXAT H LINV w s LB LBs m mo c S_OPER TBL_EEF44 [] [] spal).
    { eapply pmxa_restrict; first [exact HHm | exact LINV_frame | exact OK | exact X00 | exact INCL | apply incl_refl | idtac].
      all: first [exact HHm | exact LINV_frame | exact OK | exact X00 | exact INCL | apply incl_refl]. }
    clear X00.
    unfold tl_cutA in CUT.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    assert (EL : forall E z, edenot E (ELit z) = Z_to_bv 64 z) by reflexivity.
    assert (FSZ : 132 <= fsz PM_FCLASS) by (vm_compute; discriminate).
    assert (W112 : wr_at asegs m (wa_ff w + 112) 20).
    { apply (wr_at_sub asegs m (wa_ff w) (fsz PM_FCLASS)); [exact (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia | lia]. }
    destruct (rw_cells_of_wr_hi m (wa_ff w + 112) 20 W112 ltac:(unfold AFS_HDR in *; lia) ltac:(lia)) as (bs & C112).
    pose proof (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as V1.
    destruct (c_v1 c) as [[b n] cap] eqn:EV1. cbn [t3a t3b t3c fst snd] in *.
    destruct V1 as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2).
    unfold OPND_SZ, O_V1 in *.
    replace (wa_p w + 216 + 8) with (wa_p w + 224) in F1 by lia.
    replace (wa_p w + 216 + 16) with (wa_p w + 232) in F2 by lia.
    assert (Hbr : 0 <= b /\ b + 20 * cap <= 2 ^ 63) by (destruct Hb as [[-> ->]|(B1 & B2 & B3 & B4 & _)]; lia).
    set (e := b + 20 * n) in *.
    assert (Ee : e = b + 20 * n) by reflexivity.
    destruct (Z_lt_ge_dec n cap) as [LT | GE].
    -
      destruct Hb as [[B0 C0] | (Bpos & B16 & Cpos & Bhi & Hlive & Bapart)]; [exfalso; lia |].
      set (Xs := [Z_to_bv 64 e; Z_to_bv 64 (b + 20 * cap); Z_to_bv 64 b]).
      pose proof (env_world_seed H w R Xs) as HE.
      assert (Y41 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 e) by (ev_xs; reflexivity).
      assert (Y42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 (b + 20 * cap)) by (ev_xs; reflexivity).
      assert (Y43 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 43) = Z_to_bv 64 b) by (ev_xs; reflexivity).
      assert (HKX : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m []) by apply Forall_nil.
      pm_goX HHm LINV_frame OK X0 KR VIS RF HT Xs (@nil kentry) HKX
            100%nat [AANNOTATE_CC; VOPND_SLOW_ENTRY] [false; false; false; false; false] 41%N S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_TLA_F.
      { split_scs. all: first
          [ eapply (sc_rd_fld8 _ _ _ _ _ _ F0); [rewrite (adenot_of_estart _ _ (wa_p w + 216)); [reflexivity | rewrite (estart_p H w _ _ OK HE); lia | lia] | ev_xs; reflexivity]
          | eapply (sc_rd_fld8 _ _ _ _ _ _ F1); [rewrite (adenot_of_estart _ _ (wa_p w + 224)); [reflexivity | rewrite (estart_p H w _ _ OK HE); lia | lia] | ev_xs; reflexivity]
          | eapply (sc_rd_fld8 _ _ _ _ _ _ F2); [rewrite (adenot_of_estart _ _ (wa_p w + 232)); [reflexivity | rewrite (estart_p H w _ _ OK HE); lia | lia] | ev_xs; reflexivity]
          | cbn [sc_denot]; rewrite ?Y41, ?Y42, ?Y43, ?EL; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in X1 end.
      change (mem_denot _ m _) with m in VIS1.
      eapply (pm_vpush1 H); try exact HHbp; try exact LINV_frame;
        [ exact OK | exact X1 | exact KR1 | exact VIS1 | exact RF1 | vm_compute; reflexivity | vm_compute; reflexivity
        | intbl | intbl | rewrite EV1; cbn [t3a t3b t3c fst snd]; lia | vm_compute; reflexivity | exact C112 | reflexivity
        | rtf HTx1 | rtf HTx1 | rtf HTx1
        | rewrite EV1; cbn [t3a t3b t3c fst snd]; rtf HTx1 | rewrite EV1; cbn [t3a t3b t3c fst snd]; unfold OPND_SZ; rtf HTx1
        | rewrite EV1; cbn [t3a t3b t3c fst snd]; unfold OPND_SZ; rtf HTx1 | rewrite EV1; cbn [t3a t3b t3c fst snd]; unfold OPND_SZ; rtf HTx1
        | rewrite EV1; cbn [t3a t3b t3c fst snd]; unfold OPND_SZ; rtf HTx1 | rewrite EV1; cbn [t3a t3b t3c fst snd]; unfold OPND_SZ; rtf HTx1
        | rtf HTx1 | ].
      intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 KP3 G10_3 G11_3 FK3.
      rewrite EV1 in X3. cbn [t3a t3b t3c fst snd] in X3.
      eapply (CUT s LB LBs msF3 mo3 m3 R3 b cap KR3 VIS3 RF3 X3).
      + unfold regs_tblX, RT_TLA. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        all: first [ rewrite G10_3; unfold WADD; symmetry; apply ev_add; [reflexivity | lia | lia]
                   | rewrite G11_3; reflexivity
                   | rewrite (KP3 _ ltac:(inb)); rtf HTx1 ].
      + rewrite (KP3 3%bv ltac:(inb)), (HR1 3%bv). exact G3.
      + rewrite (KP3 4%bv ltac:(inb)), (HR1 4%bv). exact G4.
      + rewrite (KP3 22%bv ltac:(inb)), (HR1 22%bv). exact G22.
      + rewrite (KP3 25%bv ltac:(inb)), (HR1 25%bv). exact G25.
      + rewrite (KP3 18%bv ltac:(inb)), (HR1 18%bv). exact G18.
      + rewrite (KP3 23%bv ltac:(inb)). unfold OPND_SZ. replace (b + 20 * (n + 1)) with (e + 20) by lia. rtf HTx1.
      + unfold pm_bud, set_v1A in BUD |- *. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd] in BUD |- *.
        rewrite EV1 in BUD. cbn [t3a t3b t3c fst snd] in BUD. exact BUD.
      + lia.
      + exact FK3.
    -
      assert (NC : n = cap) by lia. subst n.
      set (Xs := [Z_to_bv 64 e; Z_to_bv 64 (b + 20 * cap)]).
      pose proof (env_world_seed H w R Xs) as HE.
      assert (Y41 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 e) by (ev_xs; reflexivity).
      assert (Y42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 (b + 20 * cap)) by (ev_xs; reflexivity).
      assert (HKX : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m []) by apply Forall_nil.
      pm_goX HHm LINV_frame OK X0 KR VIS RF HT Xs (@nil kentry) HKX
            100%nat [AANNOTATE_CC; VOPND_SLOW_ENTRY] [true] 41%N S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_TLA_S.
      { split_scs. all: first
          [ eapply (sc_rd_fld8 _ _ _ _ _ _ F1); [rewrite (adenot_of_estart _ _ (wa_p w + 224)); [reflexivity | rewrite (estart_p H w _ _ OK HE); lia | lia] | ev_xs; reflexivity]
          | eapply (sc_rd_fld8 _ _ _ _ _ _ F2); [rewrite (adenot_of_estart _ _ (wa_p w + 232)); [reflexivity | rewrite (estart_p H w _ _ OK HE); lia | lia] | ev_xs; reflexivity]
          | cbn [sc_denot]; rewrite ?Y41, ?Y42, ?EL; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in X1 end.
      change (mem_denot _ m _) with m in VIS1.
      pose proof (wk_tr H w OK) as TRK. unfold pm_tr_ok in TRK. rewrite Forall_forall in TRK.
      eapply (pm_vopnd1 H); try exact HHbp; try exact LINV_cl; try exact HOWN;
        [ exact HVO | exact OK | exact X1 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR1 | exact VIS1 | exact RF1
        | rtf HTx1 | reflexivity | lia | rtf HTx1 | rewrite (HR1 4%bv); exact G4 | unfold O_V1; rtf HTx1 | rtf HTx1
        | rewrite EV1; reflexivity | vm_compute; reflexivity | lia | lia | exact C112 | reflexivity
        | rewrite EV1; cbn [t3a t3b t3c fst snd]; exact (BUDG eq_refl)
        | apply TRK; unfold PM_DEL_RAS, VOPND_DEL_RA; repeat (first [left; reflexivity | right]) | ].
      intros msF2 mo2 m2 R2 s2 pid pid' b' KR2 VIS2 RF2 X2 KP2 G10_2 ABR2 BUD2 FK2.
      eapply (tl_vsame1 w s2 _ _ m2 mo2 _ S_OPER TBL_EEF44 [] [] spal msF2 R2 F fc Q OK X2 KR2 VIS2 RF2);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | intbl | intbl | rewrite (KP2 9%bv ltac:(inb)); rtf HTx1 | exact G10_2 | ].
      intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 KP3 G10_3 G11_3 G23_3 FK3.
      rewrite EV1 in X3, G23_3, BUD2. cbn [t3a t3b t3c fst snd] in X3, G23_3, BUD2.
      eapply (CUT s2 _ _ msF3 mo3 m3 R3 b' (vgrow cap) KR3 VIS3 RF3 X3).
      + unfold regs_tblX, RT_TLA. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        all: first [ rewrite G10_3; unfold WADD; symmetry; apply ev_add; [reflexivity | lia | lia]
                   | rewrite G11_3; reflexivity
                   | rewrite (KP3 _ ltac:(inb)), (KP2 _ ltac:(inb)); rtf HTx1 ].
      + rewrite (KP3 3%bv ltac:(inb)), (KP2 3%bv ltac:(inb)), (HR1 3%bv). exact G3.
      + rewrite (KP3 4%bv ltac:(inb)), (KP2 4%bv ltac:(inb)), (HR1 4%bv). exact G4.
      + rewrite (KP3 22%bv ltac:(inb)), (KP2 22%bv ltac:(inb)), (HR1 22%bv). exact G22.
      + rewrite (KP3 25%bv ltac:(inb)), (KP2 25%bv ltac:(inb)), (HR1 25%bv). exact G25.
      + rewrite (KP3 18%bv ltac:(inb)), (KP2 18%bv ltac:(inb)), (HR1 18%bv). exact G18.
      + exact G23_3.
      + exact BUD2.
      + unfold vgrow. lia.
      + exact (ffkeep_trans w _ _ _ FK2 FK3).
  Qed.
End TLA.
