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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHdr2 LbB_PmHex LbB_TablStmt LbB_TablImg LbB_PmLeaf LbB_PmLH LbB_PmOL LbB_PmVops LbB_PmExit2 LbB_PmU2K LbB_PmSL LbB_PmWX1 LbB_PmWX2 LbB_PmWXK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmWXd1 () := "C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockC47Corelib4Init5Logic8eq_ind_rC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<asan_rt_hypsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCasan_rt_hyps_bp_extC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCalloc_ok_of_live_bpC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface9RHEAP_ahmC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceAannotate_gen_stmtC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface7cost_bpI47Corelib4Init5Logic3and00C47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmInit8pm_worldI6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4pmwA00I6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn7pmw_okA00K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01I6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5PMXAT00C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_trI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_blocksC46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9regs_tblXC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_nC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase6pm_budC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt6idescAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7pm_geomC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_ffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_s1C56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_loC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6wa_sp0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt7pm_postC56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC56Stdlib6ZArith6BinInt1Z2ltC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn4wk_nK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry05K47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut:pm_kn_baseK47Corelib4Init9Datatypes4list02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond06K47Corelib4Init5Logic2eq01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut<regs_tbl_extC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6xboundK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsK5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_icountC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut>env_world_seedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut:tbl_closedC47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7keys_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut8fkeys_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut=pm_kn_base_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac:pmw_boundsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_consC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8wa_wordsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac<ev_world_allC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareI46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac6ev_addC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac<pmw_apart_ffK46Stdlib9micromega6VarMap1t01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac>pmk_sh_fshdisjC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac8pmk_sh_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7xa_scalC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase6c_widxC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_endianC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase9c_reqconvI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9xa_icountC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26adenotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac8estart_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv@adenot_of_estartC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue:sc_rd_fld8K47Corelib5Lists7ListDef6Forall02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit:sym_insideC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC46Stdlib5Lists4List7forallbI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots9upd_slotsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots9add_slotsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9scal_noneC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sr_getC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCutAregs_tbl_restrictC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut5ev_ffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut5ev_s1C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit9munch_symC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC56Stdlib6ZArith6BinInt1Z3divC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8srl3_valC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotI46Stdlib5Lists4List6Exists00K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init5Logic2or01K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K=ffkeepX_munchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K7ffkeepXC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses;rew_iff_revC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K<ffkeepX_cellC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue6rt_getC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall6acc_okC46Stdlib5Lists4List9incl_reflC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall;keys_nonnegC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall;fkeys_apartC56Stdlib6ZArith6BinInt1Z6to_natC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow<poison_bytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call6inb_InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS9regs_keepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS7rt_keepC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib5Lists4List6Exists01K46Stdlib5Lists4List6Exists02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7ev_fshbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6xa_fwrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3fszC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01C47Corelib5Lists7ListDef6firstnC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv5tb_okC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvCrw_cells_log_nth_2bC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue7ff_junkI47Corelib4Init5Logic2ex00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BellsX<rw_cells_appK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell05C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z3mulC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue;ff_u64_junkC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BArr6u64arrC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall9obj_sh_okK47Corelib5Lists7ListDef6Forall01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS9PM_OWN_DSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS:ds_rep_runC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9xa_aconstC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9xa_meminvC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConstIACONST_global_addressableC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadowFaddressable_accessibleC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C4ARocqVerifyHarness?AgentSubmission8PropExec3rdnC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue7img_litK47Corelib4Init5Logic2ex01K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3le8C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells6cbytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt5cstrAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt>tla_idesc_nameC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9wenv_valsC56Stdlib6ZArith6BinInt1Z3subC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmSL;ds_rep_leafK46Stdlib9micromega7EnvRing5PExpr04C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=disjoint_fromC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrameBrw_cells_transportC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow:in_app_memC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow:accessibleC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5shvisC47Corelib4Init5Logic3notC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap9ah_strlenC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmSLAstrlen_cstr_tleafC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC47Corelib4Init5Logic8eq_transK46Stdlib9micromega:ZMicromega;ZArithProof03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt7ds_costC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3le2K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr07C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K=edenot_zext16C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt7dla_errK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K8tbl_subbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K8tbl_inclC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PmExit28pm_epi_eC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6pm_runC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS:pm_ds_dtorC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS?pm_put_cseq_imgC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS:pm_put_numC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmSL@pm_put_cseq_cstrC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmSL8pm_leafSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmLeaf8pm_leaf0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS4ds_KC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmDS:pm_ds_ctorC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall9pm_memsetK45stdpp9bitvector;definitions2bv01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7tbl_okXC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_diagC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_userK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit7fsh_patC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit6lbytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut=sr_tbl_checkXC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit8num_winsC47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes3sndK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init5Logic2or02C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue9rt_lookupC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK46Stdlib9micromega7EnvRing5PExpr05C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvAkword_of_rw_cellsC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem8bytes_atI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01I7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsK47Corelib7Numbers7BinNums1Z01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEK4ELinuxProcessSemantics5Riscv5Instr5aluop01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C5ARocqVerifyHarness?AgentSubmission6LibPrs6PrsInv;PARSER_SIZEI5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7PM_OBJSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6PM_NSHC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut4FSHBc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1<HTbAPmWXd1_0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd13HHmK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1;RT_PM_XD1_3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt7DS_SIZEC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1;RT_PM_XD1_5C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt9DS_MAXLENC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase:PM_RESERVEc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1<RT_PM_XD1_13c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1<RT_PM_XD1_17c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1<RT_PM_XD1_21C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface9APC0_FREEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWXK6TBL_XDC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWX17RT_255Cc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1;RT_PM_XD1_1K47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission6LibPrs6PrsInv7parserC00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6fframeC4ARocqVerifyHarness?AgentSubmission8LibIface3memI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase3pmc00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AFS_HDRK47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<AASAN_MEMSETK47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8O_ICOUNTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4WV_PC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6PM_OWNC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5WV_S1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5WV_FFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall9KEPT_REGSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt8ADS_CTORC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt9PM_FCLASSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt9APUT_CSEQC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs7AIMG_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3memC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst8aglobalsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt=AT_IDESC_NAMEc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1;RT_PM_XD1_7C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ASTRLEN_STUBc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1;RT_PM_XD1_9c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1<RT_PM_XD1_11C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt8APUT_U64c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1<RT_PM_XD1_15C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt8APUT_U16c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1<RT_PM_XD1_19C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt:DS_ERR_OFFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt8ADS_DTORc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1<RT_PM_XD1_23C6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt5PM_PFc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWXd1<RT_PM_XD1_25C6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PmExit28TBL_EXIT".

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmPD.
Definition RT_XD1K : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (19%bv, WADD WV_FF 10640); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 9136); (22%bv, WADD WV_FF 10112); (24%bv, WADD WV_FF 7984); (25%bv, WADD WV_P 264); (26%bv, WADD WV_FF 112)].
Definition RT_PM_XD1_3 : list (reg * expr) := [(1%bv, ELit 0xf4c18); (10%bv, WADD WV_FF 10640); (11%bv, EVar WV_P); (12%bv, ELit 18446744073709551612); (23%bv, EVar WV_P); (27%bv, ELit 18446744073709551608)] ++ RT_XD1K.
Definition RT_PM_XD1_5 : list (reg * expr) := [(1%bv, ELit 0xf4c2c); (10%bv, WADD WV_FF 10640); (11%bv, ELit 148672); (12%bv, ELit 38); (23%bv, EVar WV_P); (27%bv, ELit 18446744073709551608)] ++ RT_XD1K.
Definition RT_PM_XD1_7 : list (reg * expr) := [(1%bv, ELit 0xf4c50); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XD1K.
Definition RT_PM_XD1_9 : list (reg * expr) := [(1%bv, ELit 0xf4c58); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XD1K.
Definition RT_PM_XD1_11 : list (reg * expr) := [(1%bv, ELit 0xf4c68); (10%bv, WADD WV_FF 10640); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XD1K.
Definition RT_PM_XD1_13 : list (reg * expr) := [(1%bv, ELit 0xf4c7c); (10%bv, WADD WV_FF 10640); (11%bv, ELit 148384); (12%bv, ELit 18); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XD1K.
Definition RT_PM_XD1_15 : list (reg * expr) := [(1%bv, ELit 0xf4c88); (10%bv, WADD WV_FF 10640); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XD1K.
Definition RT_PM_XD1_17 : list (reg * expr) := [(1%bv, ELit 0xf4c9c); (10%bv, WADD WV_FF 10640); (11%bv, ELit 148768); (12%bv, ELit 31); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XD1K.
Definition RT_PM_XD1_19 : list (reg * expr) := [(1%bv, ELit 0xf4ca8); (10%bv, WADD WV_FF 10640); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XD1K.
Definition RT_PM_XD1_21 : list (reg * expr) := [(1%bv, ELit 0xf4cbc); (10%bv, WADD WV_FF 10640); (11%bv, ELit 148832); (12%bv, ELit 7); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XD1K.
Definition RT_PM_XD1_23 : list (reg * expr) := [(1%bv, ELit 0xf4cc8); (10%bv, WADD WV_FF 10640); (27%bv, EVar WV_FF)] ++ RT_XD1K.


Section XD1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HU16 : put_u16_stmtA H LINV ds_repA.
  Hypothesis HU64 : put_u64_stmtA H LINV ds_repA.
  Hypothesis HTL : tabl_leavesA.

  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.
  Lemma HHm : asan_rt_hyps H.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmWXd1 ()) ["XD1"] "p;2p;1p;3p10000p4p70p1000ip4p710p8g001Gj27Tg002Gj26Tg003Pj12Tg004Yj21Tg005Xj15Tg006_j13Tg007\j20Tg0087j34Tp,5HCEILR0p,1HR1'71601%211101%50%31'0'0'0'0p,4HHbp34o"). Qed.

  Lemma xd1_in3 : forall (l : list (Z * Z * Z)) a b c,
    existsb (fun u => match u with (x, y, z) => ((x =? a) && (y =? b) && (z =? c))%bool end) l = true -> In (a, b, c) l.
  Proof.
    induction l as [|[[x y] z] l IH]; intros a b c Hx; [discriminate Hx|].
    cbn [existsb] in Hx. apply orb_prop in Hx as [E|E].
    - left. apply andb_prop in E as [E Ez]. apply andb_prop in E as [Ex Ey].
      apply Z.eqb_eq in Ex. apply Z.eqb_eq in Ey. apply Z.eqb_eq in Ez. subst. reflexivity.
    - right. exact (IH a b c E).
  Qed.

  Lemma xd1_lit : forall p n sz rz, In (p, sz, rz) aglobals -> 0 <= n <= sz -> p + sz <= AAPP_HI ->
    AIMG_LO <= p -> p + n <= 0x17e000 ->
    (exists bs, PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 p) (Z.to_nat n) = Some bs) ->
    (forall m', ACONST m' -> accessible m' p n) /\
    (exists bs, length bs = Z.to_nat n /\ forall m', mem_inv asegs m' -> bytes_at asegs m' p bs).
  Proof.
    intros p n sz rz HG Hn Hs H0 H1 (bs & RD). unfold AIMG_LO in H0. split.
    - intros m' AC. eapply addressable_accessible; [eapply ACONST_global_addressable; [exact AC | exact HG | lia] | lia | lia | lia].
    - exists bs. split; [exact (rdn_length _ _ _ _ _ RD)|].
      intros m' MI. exact (proj1 (img_lit m' p (Z.to_nat n) bs MI ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) RD)).
  Qed.

  Ltac xd1_rdn := lazymatch goal with |- exists bs, ?t = Some bs =>
    let r := eval vm_compute in t in lazymatch r with Some ?b => exists b; vm_compute; reflexivity end end.
  Ltac xd1_glob := apply xd1_in3; vm_compute; reflexivity.
  Ltac xd1_lit_at p n sz rz := exact (xd1_lit p n sz rz ltac:(xd1_glob) ltac:(lia) ltac:(unfold AAPP_HI; lia)
                                               ltac:(unfold AIMG_LO; lia) ltac:(lia) ltac:(xd1_rdn)).
  Lemma pm_xd1 : forall (w : pmwA H) s LB LBs m mo (c : pmc) msF R F fc (io iwc op d lw : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf4b3c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_255C -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 10112) [C8 (Z_to_bv 64 io)] -> 0 <= io < 2 ^ 63 ->
    rw_cells asegs m (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)] -> 0 <= iwc < 2 ^ 16 ->
    rw_cells asegs m (wa_ff w + 9616) [C8 (Z_to_bv 64 d)] -> idescA d op ->
    EXITKA H LINV w lw Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc io iwc op d lw Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Cio Hio Ciwc Hiwc Cd Hd KX.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    destruct (idescA_facts d op Hd) as (ri & _ & _ & _ & Hd1 & Hd2 & Hd4 & _).
    assert (EA : forall E0 a b, edenot E0 (EAlu ALU_AND a b) = alu64 ALU_AND (edenot E0 a) (edenot E0 b)) by reflexivity.
    assert (EL : forall E0 z, edenot E0 (ELit z) = Z_to_bv 64 z) by reflexivity.
    assert (KC8 : forall R0 m0 Xs k v (e : expr),
              rw_cells asegs m0 (wa_ff w + k) [C8 (Z_to_bv 64 v)] -> 0 <= k -> k + 8 <= 16384 ->
              edenot (Eseed R0 (wenv_vals w ++ Xs)) e = Z_to_bv 64 v ->
              kentry_ok ASEGS (Eseed R0 (wenv_vals w ++ Xs)) m0 (KWord (SA (EVar 33) k) 8 e)).
    { intros R0 m0 Xs k v e C Hk Hk2 He. pose proof (ev_world_all H w _ (env_world_seed H w R0 Xs)) as (_ & E33 & _).
      eapply (kword_of_rw_cells asegs _ m0 (wa_ff w + k) _ 0 (C8 (Z_to_bv 64 v))); [exact C | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off]; rewrite E33, u64_of_Z by lia; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia
        | rewrite He; reflexivity]. }
    assert (KC4 : forall R0 m0 Xs k v (e : expr),
              rw_cells asegs m0 (wa_ff w + k) [C4 (Z_to_bv 64 v)] -> 0 <= k -> k + 4 <= 16384 ->
              edenot (Eseed R0 (wenv_vals w ++ Xs)) e = Z_to_bv 64 v ->
              kentry_ok ASEGS (Eseed R0 (wenv_vals w ++ Xs)) m0 (KWord (SA (EVar 33) k) 4 e)).
    { intros R0 m0 Xs k v e C Hk Hk2 He. pose proof (ev_world_all H w _ (env_world_seed H w R0 Xs)) as (_ & E33 & _).
      eapply (kword_of_rw_cells asegs _ m0 (wa_ff w + k) _ 0 (C4 (Z_to_bv 64 v))); [exact C | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off]; rewrite E33, u64_of_Z by lia; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia
        | rewrite He; reflexivity]. }
    assert (KC2 : forall R0 m0 Xs k v (e : expr),
              rw_cells asegs m0 (wa_ff w + k) [C2 (Z_to_bv 64 v)] -> 0 <= k -> k + 2 <= 16384 ->
              edenot (Eseed R0 (wenv_vals w ++ Xs)) e = Z_to_bv 64 v ->
              kentry_ok ASEGS (Eseed R0 (wenv_vals w ++ Xs)) m0 (KWord (SA (EVar 33) k) 2 e)).
    { intros R0 m0 Xs k v e C Hk Hk2 He. pose proof (ev_world_all H w _ (env_world_seed H w R0 Xs)) as (_ & E33 & _).
      eapply (kword_of_rw_cells asegs _ m0 (wa_ff w + k) _ 0 (C2 (Z_to_bv 64 v))); [exact C | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off]; rewrite E33, u64_of_Z by lia; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia
        | rewrite He; reflexivity]. }
    assert (FKS : forall m1 m2 STK, munch [(wa_s1 w - STK, wa_s1 w)] m1 m2 -> wmono asegs m1 m2 -> 0 <= STK <= 4096 -> ffkeep w m1 m2).
    { intros m1 m2 STK MU WM HS. apply (ffkeep_munch w _ _ _ MU WM). apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }

    assert (HKa : know_ok asegs (Eseed R (wenv_vals w ++ [])) m []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word) (@nil kentry) HKa
          200%nat [APDIAG] (@nil bool) 41%N (48%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XD1_3.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HT1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in X1, VIS1 end.
    assert (FK1 : ffkeep w m M1).
    { lazymatch type of Hlf1 with log_flat _ ?lg =>
        assert (INS : forallb (sym_inside [(FSHB, SHBASE, SHBASE + 2048)]) lg = true) by (vm_compute; reflexivity) end.
      pose proof (munch_sym _ m _ _ Hlf1 INS) as MU. cbn [num_wins map] in MU.
      rewrite (ev_fshb H w _ OK (env_world_seed H w R [])) in MU.
      apply (ffkeep_munch w _ m M1 MU (wmono_mem_denot _ _ _)).
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    eapply (pm_pdiag H HHbp LINV ds_repA APDIAG false HPDIAG0 w s LB LBs M1 mo1 c (48%nat :: S_INSTR) TBL_EEF44 [] 0 msF1 R1 F fc
              10640 0xf4c18 (-4) Q);
      [ exact OK | exact X1 | vm_compute; reflexivity | reflexivity | exact KR1 | exact VIS1 | exact RF1 | exact FZ0
      | rtf HT1 | reflexivity | lia | rtf HT1 | rtf HT1 | exact G4_1 | rtf HT1 | rtf HT1 | rtf HT1 | reflexivity
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | ].
    intros msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 [-> DS2] CL2.
    assert (Cio2 : rw_cells asegs m2 (wa_ff w + 10112) [C8 (Z_to_bv 64 io)])
      by (apply CL2; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | apply FK1; [lia | cbn; lia | exact Cio]]).
    assert (Ciwc2 : rw_cells asegs m2 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)])
      by (apply CL2; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | apply FK1; [lia | cbn; lia | exact Ciwc]]).
    assert (Cd2 : rw_cells asegs m2 (wa_ff w + 9616) [C8 (Z_to_bv 64 d)])
      by (apply CL2; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | apply FK1; [lia | cbn; lia | exact Cd]]).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inb)); exact G3_1).
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inb)); exact G4_1).
    pose proof (regs_keep w [] R1 R2 RT_PM_XD1_3 HT1 KEEP2) as HT2.
    clear Cio Ciwc Cd FK1 CL2.

    assert (HKb : know_ok asegs (Eseed R2 (wenv_vals w ++ [])) m2 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word) (@nil kentry) HKb
          200%nat [APUT_CSEQ] (@nil bool) 41%N (48%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XD1_5.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HT3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m2 in X3 end.
    change (mem_denot _ m2 _) with m2 in VIS3.
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
    assert (L1 : (forall m', ACONST m' -> accessible m' 148672 38) /\
                 (exists bs, length bs = Z.to_nat 38 /\ forall m', mem_inv asegs m' -> bytes_at asegs m' 148672 bs))
      by xd1_lit_at 148672 38 39 96.
    destruct L1 as [ACC1 BYT1].
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF3 R3 _ _ 10640 0xf4c2c 148672 38 (-4) 0 Q);
      [ exact OK | exact X3 | vm_compute; reflexivity | reflexivity | exact KR3 | exact VIS3 | exact RF3 | exact FZ2
      | rtf HT3 | reflexivity | lia | rtf HT3 | rtf HT3 | exact G4_3 | rtf HT3 | rtf HT3 | rtf HT3
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | exact ACC1 | exact BYT1 | exact DS2 | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF4 mo4 R4 F4 fc4 s4 LB4 m4 TB4 KR4 VIS4 RF4 FZ4 X4 KEEP4 [DS4 _] CL4.
    assert (Cio4 : rw_cells asegs m4 (wa_ff w + 10112) [C8 (Z_to_bv 64 io)]) by (apply CL4; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Cio2]).
    assert (Ciwc4 : rw_cells asegs m4 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply CL4; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Ciwc2]).
    assert (Cd4 : rw_cells asegs m4 (wa_ff w + 9616) [C8 (Z_to_bv 64 d)]) by (apply CL4; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Cd2]).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (rewrite (KEEP4 3%bv ltac:(inb)); exact G3_3).
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (rewrite (KEEP4 4%bv ltac:(inb)); exact G4_3).
    pose proof (regs_keep w [] R3 R4 RT_PM_XD1_5 HT3 KEEP4) as HT4.
    clear Cio2 Ciwc2 Cd2 CL4.

    set (Xc := [Z_to_bv 64 d]).
    assert (Y41c : edenot (Eseed R4 (wenv_vals w ++ Xc)) (EVar 41) = Z_to_bv 64 d) by (ev_xs; reflexivity).
    assert (HKc : know_ok asegs (Eseed R4 (wenv_vals w ++ Xc)) m4 [KWord (SA (EVar 33) 9616) 8 (EVar 41)]).
    { apply Forall_cons; [apply (KC8 R4 m4 Xc 9616 d); [exact Cd4 | lia | lia | exact Y41c] | apply Forall_nil]. }
    pm_goX HHm LINV_frame OK X4 KR4 VIS4 RF4 HT4 Xc [KWord (SA (EVar 33) 9616) 8 (EVar 41)] HKc
          200%nat [AT_IDESC_NAME] [true; true] 42%N (48%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XD1_7.
    { split_scs.
      - cbn [sc_denot]. rewrite EA. rewrite Y41c. rewrite !EL. rewrite w_and by lia.
        replace (Z.land d 3) with 0 by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
        rewrite br_eq by lia. reflexivity.
      - cbn [sc_denot]. rewrite Y41c. rewrite EL. rewrite br_ne by lia. bool_lia. }
    intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HT5 HR5 Hlf5.
    lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m4 in X5 end.
    change (mem_denot _ m4 _) with m4 in VIS5.
    assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (HR5 3%bv); exact G3_4).
    assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (HR5 4%bv); exact G4_4).
    eapply (pm_leaf0 H HHm LINV LINV_frame AT_IDESC_NAME TL_STACK _ _ _ (tla_idesc_name HTL) (d, op) w _ _ LBs _ _ c _ TBL_EEF44 [] _ _
              msF5 R5 _ _ 0xf4c50 Q);
      [ exact OK | exact X5 | exact KR5 | exact VIS5 | exact RF5 | rtf HT5 | rtf HT5 | reflexivity | lia | unfold TL_STACK; lia | reflexivity
      | cbv beta iota; split; [exact Hd | rewrite (HR5 10%bv); exact Y41c] | vm_compute; reflexivity | reflexivity | ].
    intros msF6 mo6 m6 R6 KR6 VIS6 RF6 X6 KEEP6 MU6 WM6 LQ6.
    destruct LQ6 as (pn & nn & CS & Epn).
    pose proof CS as (CS1 & CS2 & _).
    pose proof (ds_rep_leaf H HHbp LINV ds_repA DSL w _ _ _ _ _ _ _ _ _ _ _ m6 TL_STACK 10640 (-4) _ OK X5 MU6
                  ltac:(unfold TL_STACK; lia) ltac:(lia) ltac:(unfold DS_SIZE; lia) DS4) as DS6.
    pose proof (FKS m4 m6 TL_STACK MU6 WM6 ltac:(unfold TL_STACK; lia)) as FK6.
    assert (Cio6 : rw_cells asegs m6 (wa_ff w + 10112) [C8 (Z_to_bv 64 io)]) by (apply FK6; [lia | cbn; lia | exact Cio4]).
    assert (Ciwc6 : rw_cells asegs m6 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply FK6; [lia | cbn; lia | exact Ciwc4]).
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (rewrite (KEEP6 3%bv ltac:(inb)); exact G3_5).
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (rewrite (KEEP6 4%bv ltac:(inb)); exact G4_5).
    pose proof (regs_keep w [] R5 R6 RT_PM_XD1_7 (regs_tbl_restrict w [] Xc R5 RT_PM_XD1_7 HT5 ltac:(vm_compute; reflexivity)) KEEP6) as HT6.
    clear Cio4 Ciwc4 Cd4 FK6 DS4.

    assert (HKd : know_ok asegs (Eseed R6 (wenv_vals w ++ [])) m6 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X6 KR6 VIS6 RF6 HT6 (@nil word) (@nil kentry) HKd
          200%nat [ASTRLEN_STUB] (@nil bool) 41%N (48%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XD1_9.
    { split_scs. }
    intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HT7 HR7 Hlf7.
    lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m6 in X7 end.
    change (mem_denot _ m6 _) with m6 in VIS7.
    assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (HR7 3%bv); exact G3_6).
    assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (HR7 4%bv); exact G4_6).
    assert (P18 : PropExec.getr R7 18%bv = Z_to_bv 64 pn) by (rewrite (HR7 18%bv); exact Epn).
    eapply (pm_leafS H HHm LINV LINV_frame ASTRLEN_STUB AINTRIN_STACK _ _ _ (strlen_cstr_tleaf (ah_strlen H HHm)) (pn, nn) w _ _ LBs _ _ c _
              TBL_EEF44 [] _ _ msF7 R7 _ _ 0xf4c58 Q);
      [ exact OK | exact X7 | exact KR7 | exact VIS7 | exact RF7 | rtf HT7 | rtf HT7 | reflexivity | lia | unfold AINTRIN_STACK; lia | reflexivity
      | cbv beta; cbn [fst snd]; split; [exact CS | rewrite (HR7 10%bv); exact Epn] | vm_compute; reflexivity | reflexivity | ].
    intros msF8 mo8 m8 R8 KR8 VIS8 RF8 X8 KEEP8 MU8 WM8 LQ8.
    cbv beta in LQ8. cbn [snd] in LQ8.
    pose proof (ds_rep_leaf H HHbp LINV ds_repA DSL w _ _ _ _ _ _ _ _ _ _ _ m8 AINTRIN_STACK 10640 (-4) _ OK X7 MU8
                  ltac:(unfold AINTRIN_STACK; lia) ltac:(lia) ltac:(unfold DS_SIZE; lia) DS6) as DS8.
    pose proof (FKS m6 m8 AINTRIN_STACK MU8 WM8 ltac:(unfold AINTRIN_STACK; lia)) as FK8.
    assert (Cio8 : rw_cells asegs m8 (wa_ff w + 10112) [C8 (Z_to_bv 64 io)]) by (apply FK8; [lia | cbn; lia | exact Cio6]).
    assert (Ciwc8 : rw_cells asegs m8 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply FK8; [lia | cbn; lia | exact Ciwc6]).
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (rewrite (KEEP8 3%bv ltac:(inb)); exact G3_7).
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (rewrite (KEEP8 4%bv ltac:(inb)); exact G4_7).
    assert (P18' : PropExec.getr R8 18%bv = Z_to_bv 64 pn) by (rewrite (KEEP8 18%bv ltac:(inb)); exact P18).
    pose proof (regs_keep w [] R7 R8 RT_PM_XD1_9 HT7 KEEP8) as HT8.
    clear Cio6 Ciwc6 FK8 DS6.

    assert (HKe : know_ok asegs (Eseed R8 (wenv_vals w ++ [])) m8 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X8 KR8 VIS8 RF8 HT8 (@nil word) (@nil kentry) HKe
          200%nat [APUT_CSEQ] (@nil bool) 41%N (48%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XD1_11.
    { split_scs. }
    intros msF9 mo9 R9 KR9 VIS9 RF9 X9 HT9 HR9 Hlf9.
    lazymatch type of X9 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m8 in X9 end.
    change (mem_denot _ m8 _) with m8 in VIS9.
    assert (G3_9 : PropExec.getr R9 3%bv = wa_gp w) by (rewrite (HR9 3%bv); exact G3_8).
    assert (G4_9 : PropExec.getr R9 4%bv = wa_tp w) by (rewrite (HR9 4%bv); exact G4_8).
    eapply (pm_put_cseq_cstr H HHbp LINV ds_repA DSL HCSEQ w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF9 R9 _ _ 10640 0xf4c68 pn nn (-4) (0 + 38) Q);
      [ exact OK | exact X9 | vm_compute; reflexivity | reflexivity | exact KR9 | exact VIS9 | exact RF9 | exact FZ4
      | rtf HT9 | reflexivity | lia | rtf HT9 | rtf HT9 | exact G4_9 | rtf HT9 | rewrite (HR9 11%bv); exact P18' | rewrite (HR9 12%bv); exact LQ8
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | exact CS | exact DS8 | unfold DS_MAXLEN; lia
      | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF10 mo10 R10 F10 fc10 s10 LB10 m10 TB10 KR10 VIS10 RF10 FZ10 X10 KEEP10 [DS10 _] CL10.
    assert (Cio10 : rw_cells asegs m10 (wa_ff w + 10112) [C8 (Z_to_bv 64 io)]) by (apply CL10; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Cio8]).
    assert (Ciwc10 : rw_cells asegs m10 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply CL10; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Ciwc8]).
    assert (G3_10 : PropExec.getr R10 3%bv = wa_gp w) by (rewrite (KEEP10 3%bv ltac:(inb)); exact G3_9).
    assert (G4_10 : PropExec.getr R10 4%bv = wa_tp w) by (rewrite (KEEP10 4%bv ltac:(inb)); exact G4_9).
    pose proof (regs_keep w [] R9 R10 RT_PM_XD1_11 HT9 KEEP10) as HT10.
    clear Cio8 Ciwc8 CL10 DS8.

    assert (HKf : know_ok asegs (Eseed R10 (wenv_vals w ++ [])) m10 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X10 KR10 VIS10 RF10 HT10 (@nil word) (@nil kentry) HKf
          200%nat [APUT_CSEQ] (@nil bool) 41%N (48%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XD1_13.
    { split_scs. }
    intros msF11 mo11 R11 KR11 VIS11 RF11 X11 HT11 HR11 Hlf11.
    lazymatch type of X11 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m10 in X11 end.
    change (mem_denot _ m10 _) with m10 in VIS11.
    assert (G3_11 : PropExec.getr R11 3%bv = wa_gp w) by (rewrite (HR11 3%bv); exact G3_10).
    assert (G4_11 : PropExec.getr R11 4%bv = wa_tp w) by (rewrite (HR11 4%bv); exact G4_10).
    assert (L2 : (forall m', ACONST m' -> accessible m' 148384 18) /\
                 (exists bs, length bs = Z.to_nat 18 /\ forall m', mem_inv asegs m' -> bytes_at asegs m' 148384 bs))
      by xd1_lit_at 148384 18 19 64.
    destruct L2 as [ACC2 BYT2].
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF11 R11 _ _ 10640 0xf4c7c 148384 18 (-4)
              (0 + 38 + nn) Q);
      [ exact OK | exact X11 | vm_compute; reflexivity | reflexivity | exact KR11 | exact VIS11 | exact RF11 | exact FZ10
      | rtf HT11 | reflexivity | lia | rtf HT11 | rtf HT11 | exact G4_11 | rtf HT11 | rtf HT11 | rtf HT11
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | exact ACC2 | exact BYT2 | exact DS10 | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF12 mo12 R12 F12 fc12 s12 LB12 m12 TB12 KR12 VIS12 RF12 FZ12 X12 KEEP12 [DS12 _] CL12.
    assert (Cio12 : rw_cells asegs m12 (wa_ff w + 10112) [C8 (Z_to_bv 64 io)]) by (apply CL12; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Cio10]).
    assert (Ciwc12 : rw_cells asegs m12 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply CL12; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Ciwc10]).
    assert (G3_12 : PropExec.getr R12 3%bv = wa_gp w) by (rewrite (KEEP12 3%bv ltac:(inb)); exact G3_11).
    assert (G4_12 : PropExec.getr R12 4%bv = wa_tp w) by (rewrite (KEEP12 4%bv ltac:(inb)); exact G4_11).
    pose proof (regs_keep w [] R11 R12 RT_PM_XD1_13 HT11 KEEP12) as HT12.
    clear Cio10 Ciwc10 CL12 DS10.

    set (Xg := [Z_to_bv 64 io]).
    assert (Y41g : edenot (Eseed R12 (wenv_vals w ++ Xg)) (EVar 41) = Z_to_bv 64 io) by (ev_xs; reflexivity).
    assert (HKg : know_ok asegs (Eseed R12 (wenv_vals w ++ Xg)) m12 [KWord (SA (EVar 33) 10112) 8 (EVar 41)]).
    { apply Forall_cons; [apply (KC8 R12 m12 Xg 10112 io); [exact Cio12 | lia | lia | exact Y41g] | apply Forall_nil]. }
    pm_goX HHm LINV_frame OK X12 KR12 VIS12 RF12 HT12 Xg [KWord (SA (EVar 33) 10112) 8 (EVar 41)] HKg
          200%nat [APUT_U64] (@nil bool) 42%N (48%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XD1_15.
    { split_scs. }
    intros msF13 mo13 R13 KR13 VIS13 RF13 X13 HT13 HR13 Hlf13.
    lazymatch type of X13 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m12 in X13 end.
    change (mem_denot _ m12 _) with m12 in VIS13.
    assert (G3_13 : PropExec.getr R13 3%bv = wa_gp w) by (rewrite (HR13 3%bv); exact G3_12).
    assert (G4_13 : PropExec.getr R13 4%bv = wa_tp w) by (rewrite (HR13 4%bv); exact G4_12).
    eapply (pm_put_num H HHbp LINV ds_repA DSL APUT_U64 0 (2 ^ 64) (fun x => x) HU64 w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF13 R13 _ _
              10640 0xf4c88 io (-4) (0 + 38 + nn + 18) Q);
      [ exact OK | exact X13 | vm_compute; reflexivity | reflexivity | exact KR13 | exact VIS13 | exact RF13 | exact FZ12
      | rtf HT13 | reflexivity | lia | rtf HT13 | rtf HT13 | exact G4_13 | rtf HT13 | cbv beta; rewrite (HR13 11%bv); exact Y41g | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | exact DS12 | unfold DS_MAXLEN; lia
      | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF14 mo14 R14 F14 fc14 s14 LB14 m14 TB14 KR14 VIS14 RF14 FZ14 X14 KEEP14 [DS14 _] CL14.
    assert (Ciwc14 : rw_cells asegs m14 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply CL14; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Ciwc12]).
    assert (G3_14 : PropExec.getr R14 3%bv = wa_gp w) by (rewrite (KEEP14 3%bv ltac:(inb)); exact G3_13).
    assert (G4_14 : PropExec.getr R14 4%bv = wa_tp w) by (rewrite (KEEP14 4%bv ltac:(inb)); exact G4_13).
    pose proof (regs_keep w [] R13 R14 RT_PM_XD1_15 (regs_tbl_restrict w [] Xg R13 RT_PM_XD1_15 HT13 ltac:(vm_compute; reflexivity)) KEEP14) as HT14.
    clear Cio12 Ciwc12 CL14 DS12.

    assert (HKh : know_ok asegs (Eseed R14 (wenv_vals w ++ [])) m14 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X14 KR14 VIS14 RF14 HT14 (@nil word) (@nil kentry) HKh
          200%nat [APUT_CSEQ] (@nil bool) 41%N (48%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XD1_17.
    { split_scs. }
    intros msF15 mo15 R15 KR15 VIS15 RF15 X15 HT15 HR15 Hlf15.
    lazymatch type of X15 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m14 in X15 end.
    change (mem_denot _ m14 _) with m14 in VIS15.
    assert (G3_15 : PropExec.getr R15 3%bv = wa_gp w) by (rewrite (HR15 3%bv); exact G3_14).
    assert (G4_15 : PropExec.getr R15 4%bv = wa_tp w) by (rewrite (HR15 4%bv); exact G4_14).
    assert (L3 : (forall m', ACONST m' -> accessible m' 148768 31) /\
                 (exists bs, length bs = Z.to_nat 31 /\ forall m', mem_inv asegs m' -> bytes_at asegs m' 148768 bs))
      by xd1_lit_at 148768 31 32 64.
    destruct L3 as [ACC3 BYT3].
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF15 R15 _ _ 10640 0xf4c9c 148768 31 (-4)
              (0 + 38 + nn + 18 + 24) Q);
      [ exact OK | exact X15 | vm_compute; reflexivity | reflexivity | exact KR15 | exact VIS15 | exact RF15 | exact FZ14
      | rtf HT15 | reflexivity | lia | rtf HT15 | rtf HT15 | exact G4_15 | rtf HT15 | rtf HT15 | rtf HT15
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | exact ACC3 | exact BYT3 | exact DS14 | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF16 mo16 R16 F16 fc16 s16 LB16 m16 TB16 KR16 VIS16 RF16 FZ16 X16 KEEP16 [DS16 _] CL16.
    assert (Ciwc16 : rw_cells asegs m16 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply CL16; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Ciwc14]).
    assert (G3_16 : PropExec.getr R16 3%bv = wa_gp w) by (rewrite (KEEP16 3%bv ltac:(inb)); exact G3_15).
    assert (G4_16 : PropExec.getr R16 4%bv = wa_tp w) by (rewrite (KEEP16 4%bv ltac:(inb)); exact G4_15).
    pose proof (regs_keep w [] R15 R16 RT_PM_XD1_17 HT15 KEEP16) as HT16.
    clear Ciwc14 CL16 DS14.

    set (Xi := [Z_to_bv 64 iwc]).
    assert (Y41i : edenot (Eseed R16 (wenv_vals w ++ Xi)) (EVar 41) = Z_to_bv 64 iwc) by (ev_xs; reflexivity).
    assert (HKi : know_ok asegs (Eseed R16 (wenv_vals w ++ Xi)) m16 [KWord (SA (EVar 33) 9136) 2 (EVar 41)]).
    { apply Forall_cons; [apply (KC2 R16 m16 Xi 9136 iwc); [exact Ciwc16 | lia | lia | exact Y41i] | apply Forall_nil]. }
    pm_goX HHm LINV_frame OK X16 KR16 VIS16 RF16 HT16 Xi [KWord (SA (EVar 33) 9136) 2 (EVar 41)] HKi
          200%nat [APUT_U16] (@nil bool) 42%N (48%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XD1_19.
    { split_scs. }
    intros msF17 mo17 R17 KR17 VIS17 RF17 X17 HT17 HR17 Hlf17.
    lazymatch type of X17 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m16 in X17 end.
    change (mem_denot _ m16 _) with m16 in VIS17.
    assert (G3_17 : PropExec.getr R17 3%bv = wa_gp w) by (rewrite (HR17 3%bv); exact G3_16).
    assert (G4_17 : PropExec.getr R17 4%bv = wa_tp w) by (rewrite (HR17 4%bv); exact G4_16).
    eapply (pm_put_num H HHbp LINV ds_repA DSL APUT_U16 0 (2 ^ 16) (fun x => x) HU16 w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF17 R17 _ _
              10640 0xf4ca8 iwc (-4) (0 + 38 + nn + 18 + 24 + 31) Q);
      [ exact OK | exact X17 | vm_compute; reflexivity | reflexivity | exact KR17 | exact VIS17 | exact RF17 | exact FZ16
      | rtf HT17 | reflexivity | lia | rtf HT17 | rtf HT17 | exact G4_17 | rtf HT17
      | cbv beta; rewrite (HR17 11%bv);
        transitivity (edenot (Eseed R16 (wenv_vals w ++ Xi)) (EExt false 0 2 (EVar 41))); [reflexivity | apply edenot_zext16; [exact Y41i | lia]] | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | exact DS16 | unfold DS_MAXLEN; lia
      | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF18 mo18 R18 F18 fc18 s18 LB18 m18 TB18 KR18 VIS18 RF18 FZ18 X18 KEEP18 [DS18 _] CL18.
    assert (G3_18 : PropExec.getr R18 3%bv = wa_gp w) by (rewrite (KEEP18 3%bv ltac:(inb)); exact G3_17).
    assert (G4_18 : PropExec.getr R18 4%bv = wa_tp w) by (rewrite (KEEP18 4%bv ltac:(inb)); exact G4_17).
    pose proof (regs_keep w [] R17 R18 RT_PM_XD1_19 (regs_tbl_restrict w [] Xi R17 RT_PM_XD1_19 HT17 ltac:(vm_compute; reflexivity)) KEEP18) as HT18.
    clear Ciwc16 CL18 DS16.

    assert (HKj : know_ok asegs (Eseed R18 (wenv_vals w ++ [])) m18 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X18 KR18 VIS18 RF18 HT18 (@nil word) (@nil kentry) HKj
          200%nat [APUT_CSEQ] (@nil bool) 41%N (48%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XD1_21.
    { split_scs. }
    intros msF19 mo19 R19 KR19 VIS19 RF19 X19 HT19 HR19 Hlf19.
    lazymatch type of X19 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m18 in X19 end.
    change (mem_denot _ m18 _) with m18 in VIS19.
    assert (G3_19 : PropExec.getr R19 3%bv = wa_gp w) by (rewrite (HR19 3%bv); exact G3_18).
    assert (G4_19 : PropExec.getr R19 4%bv = wa_tp w) by (rewrite (HR19 4%bv); exact G4_18).
    assert (L4 : (forall m', ACONST m' -> accessible m' 148832 7) /\
                 (exists bs, length bs = Z.to_nat 7 /\ forall m', mem_inv asegs m' -> bytes_at asegs m' 148832 bs))
      by xd1_lit_at 148832 7 8 32.
    destruct L4 as [ACC4 BYT4].
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF19 R19 _ _ 10640 0xf4cbc 148832 7 (-4)
              (0 + 38 + nn + 18 + 24 + 31 + 24) Q);
      [ exact OK | exact X19 | vm_compute; reflexivity | reflexivity | exact KR19 | exact VIS19 | exact RF19 | exact FZ18
      | rtf HT19 | reflexivity | lia | rtf HT19 | rtf HT19 | exact G4_19 | rtf HT19 | rtf HT19 | rtf HT19
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | exact ACC4 | exact BYT4 | exact DS18 | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF20 mo20 R20 F20 fc20 s20 LB20 m20 TB20 KR20 VIS20 RF20 FZ20 X20 KEEP20 [DS20 _] CL20.
    assert (G3_20 : PropExec.getr R20 3%bv = wa_gp w) by (rewrite (KEEP20 3%bv ltac:(inb)); exact G3_19).
    assert (G4_20 : PropExec.getr R20 4%bv = wa_tp w) by (rewrite (KEEP20 4%bv ltac:(inb)); exact G4_19).
    pose proof (regs_keep w [] R19 R20 RT_PM_XD1_21 HT19 KEEP20) as HT20.
    clear CL20 DS18.

    pose proof (dla_err LINV ds_repA DSL _ _ _ _ _ _ DS20) as CE20.
    replace (wa_ff w + 10640 + DS_ERR_OFF) with (wa_ff w + 11000) in CE20 by (unfold DS_ERR_OFF; lia).
    assert (HKk : know_ok asegs (Eseed R20 (wenv_vals w ++ [])) m20 [KWord (SA (EVar 33) 11000) 4 (ELit 4294967292)]).
    { apply Forall_cons; [apply (KC4 R20 m20 [] 11000 ((-4) mod 2 ^ 32)); [exact CE20 | lia | lia | rewrite EL; reflexivity] | apply Forall_nil]. }
    pm_goX HHm LINV_frame OK X20 KR20 VIS20 RF20 HT20 (@nil word) [KWord (SA (EVar 33) 11000) 4 (ELit 4294967292)] HKk
          200%nat [ADS_DTOR] (@nil bool) 41%N (48%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XD1_23.
    { split_scs. }
    intros msF21 mo21 R21 KR21 VIS21 RF21 X21 HT21 HR21 Hlf21.
    lazymatch type of X21 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m20 in X21 end.
    change (mem_denot _ m20 _) with m20 in VIS21.
    assert (G3_21 : PropExec.getr R21 3%bv = wa_gp w) by (rewrite (HR21 3%bv); exact G3_20).
    assert (G4_21 : PropExec.getr R21 4%bv = wa_tp w) by (rewrite (HR21 4%bv); exact G4_20).
    assert (G23_21 : PropExec.getr R21 23%bv = Z_to_bv 64 (-4)) by (rewrite (HR21 23%bv); apply bv_eq; vm_compute; reflexivity).
    eapply (pm_ds_dtor H HHbp LINV ds_repA HDTOR w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF21 R21 _ _ 10640 0xf4cc8 (-4) _ Q);
      [ exact OK | exact X21 | vm_compute; reflexivity | reflexivity | exact KR21 | exact VIS21 | exact RF21 | exact FZ20
      | rtf HT21 | reflexivity | lia | rtf HT21 | rtf HT21 | exact G4_21 | rtf HT21
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | exact DS20 | unfold PM_PF, PM_DTOR_RAS; inlist | ].
    intros msF22 mo22 R22 F22 fc22 s22 LB22 m22 TB22 KR22 VIS22 RF22 FZ22 X22 KEEP22 [-> _] _.
    assert (G3_22 : PropExec.getr R22 3%bv = wa_gp w) by (rewrite (KEEP22 3%bv ltac:(inb)); exact G3_21).
    assert (G4_22 : PropExec.getr R22 4%bv = wa_tp w) by (rewrite (KEEP22 4%bv ltac:(inb)); exact G4_21).
    assert (G23_22 : PropExec.getr R22 23%bv = Z_to_bv 64 (-4)) by (rewrite (KEEP22 23%bv ltac:(inb)); exact G23_21).
    pose proof (regs_keep w [] R21 R22 RT_PM_XD1_23 HT21 KEEP22) as HT22.

    assert (HKl : know_ok asegs (Eseed R22 (wenv_vals w ++ [])) m22 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X22 KR22 VIS22 RF22 HT22 (@nil word) (@nil kentry) HKl
          200%nat [EXIT_OPC] (@nil bool) 41%N [OB_INST; OB_FIRST_WORD; OB_INST_WC; OB_OPCODE_DESC] (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_EXIT.
    { split_scs. }
    intros msF23 mo23 R23 KR23 VIS23 RF23 X23 HT23 HR23 Hlf23.
    eapply (KX _ _ LBs _ mo23 c msF23 R23 F22 fc22 EXIT_OPC [OB_INST; OB_FIRST_WORD; OB_INST_WC; OB_OPCODE_DESC] (-4)); [| right; left; split; reflexivity].
    constructor.
    - do 2 eexists. split; [exact X23|]. split; [apply tbl_incl; vm_compute; reflexivity | intros Hr; discriminate Hr].
    - exact KR23.
    - exact VIS23.
    - exact RF23.
    - exact FZ22.
    - exact HT23.
    - rewrite (HR23 3%bv); exact G3_22.
    - rewrite (HR23 4%bv); exact G4_22.
    - split; [rewrite (HR23 23%bv); exact G23_22 | lia].
    - exact Htr.
    - exact Hbsz.
    - intros Hr; discriminate Hr.
  Qed.

End XD1.
