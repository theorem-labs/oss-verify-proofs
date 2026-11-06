(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHdr2 LbB_PmHex LbB_TablStmt LbB_TablImg LbB_PmLeaf LbB_PmLH LbB_PmOL LbB_PmVops LbB_PmExit2 LbB_PmU2K LbB_PmSL LbB_PmWXK.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmWZ7g () := "C69OSSVerify5KrLib3bpB2Rt7BsIface5blockC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib3bpB2Rt7BsIface<asan_rt_hypsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_IfaceCasan_rt_hyps_bp_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_IfaceCalloc_ok_of_live_bpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_Iface9RHEAP_ahmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_IfaceAannotate_gen_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_Iface7cost_bpC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib3bpB2Rt7BsIface5as_StC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib3bpB3Lib:LbB_PmInit8pm_worldC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4pmwA00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpB3Lib9LbB_PmOwn7pmw_okA00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01I69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5PMXAT00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase4c_trC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib6LibPrs6PmBase8c_blocksC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib3bpB2Rt7BsIface8as_AKRELC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C79OSSVerify5KrLib3bpB2HF3Lib:BLPropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BMState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_Bridge5rfullC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7FPSteps8frm_zeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut9regs_tblXC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4wa_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase6pm_budC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase6c_widxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib3bpB3Lib<LbB_TablStmt6idescAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase4c_v3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7pm_geomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_ffC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_s1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow5aceilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow2shC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase6wa_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib;LbB_PrsStmt7pm_postC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib3bpB2Rt8BsShadow;aceil_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF8BeapCeil5hceilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmOwn4wk_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut>env_world_seedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut5ev_ffC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac:pmw_boundsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4wa_pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7wa_consC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase8wa_wordsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase8c_icountC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac=pmk_scal_widxC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflK46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C59OSSVerify5KrLib8SymExec33SX26a_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25a_offC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02C79OSSVerify5KrLib3bpB2HF3Lib4BMem3le8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib8SymExec33SX26edenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib6BCells6cbytesC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib4BMem3le2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5xa_v3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB3lblC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib7LibCont4CRep4ZnthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibCont4CRep4mdefC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S6estartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac8estart_pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut<kword_of_fldC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec33SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut:pm_kn_baseC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib8SymExec33SX27scripts01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX28sidecond06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX28sidecond01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut<regs_tbl_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut6xboundC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7LibHash4HLib3srsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX29sym_state01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC69OSSVerify5KrLib3bpB3Lib9LbB_PmCut:tbl_closedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7keys_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut8fkeys_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut=pm_kn_base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac<ev_world_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac6ev_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac<pmw_apart_ffC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac>pmk_sh_fshdisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7xa_scalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase8c_endianC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase9c_reqconvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmU2K=edenot_zext16C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07C69OSSVerify5KrLib3bpB3Lib9LbB_PmWT27ev_add2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase9xa_icountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_Conv@adenot_of_estartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmGlue:sc_rd_fld8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase9wenv_valsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib7LibHash4HLib5br_neC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3lebC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib3bpB3Lib9LbB_PmTac8ev_xseedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem<branch_takenC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib7LibHash4HLib6br_ltuC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib3bpB3Lib8LbB_FKit:sym_insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25s_logC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib3bpB3Lib:LbB_FSlots9upd_slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_FSlots9add_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut9scal_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26sr_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCutAregs_tbl_restrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut5ev_s1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5as_SRC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib3bpB3Lib8LbB_FKit9munch_symC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame5munchC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC69OSSVerify5KrLib3bpB3Lib7LbB_Kit8srl3_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_Conv?wmono_mem_denotC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C69OSSVerify5KrLib3bpB3Lib9LbB_PmU2K=ffkeepX_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmU2K7ffkeepXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmU2K<ffkeepX_cellC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC69OSSVerify5KrLib3bpB3Lib:LbB_PmGlue6rt_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmCall6acc_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC69OSSVerify5KrLib3bpB3Lib:LbB_PmCall;keys_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmCall;fkeys_apartC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z6to_natC69OSSVerify5KrLib3bpB2Rt8BsShadow<poison_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_Call6inb_InC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmDS9regs_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmDS7rt_keepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib6BCells:cells_sizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib5Lists4List6Exists01K46Stdlib5Lists4List6Exists02C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7ev_fshbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase6xa_fwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface3fszC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib4BMem5wr_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib4BMem2waC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26sentry01C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC69OSSVerify5KrLib3bpB3Lib8LbB_Conv5tb_okC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init5Logic3and01C69OSSVerify5KrLib3bpB3Lib8LbB_ConvCrw_cells_log_nth_2bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmGlue7ff_junkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C79OSSVerify5KrLib3bpB2HF3Lib6BellsX<rw_cells_appC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmGlue;ff_u64_junkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib4BArr6u64arrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib3bpB3Lib:LbB_PmCall9obj_sh_okC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib3bpB2Rt7BsIface6as_VISC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmDS9PM_OWN_DSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmDS:ds_rep_runC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib3bpB3Lib9LbB_PmWXK=ev_sub_normD2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase9xa_aconstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsConst6ACONSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase9xa_meminvC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib4BMem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsConstIACONST_global_addressableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadowFaddressable_accessibleC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmGlue7img_litC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib3bpB3Lib<LbB_TablStmt5cstrAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_TablStmt>tla_idesc_nameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmSL;ds_rep_leafC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame=disjoint_fromC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow:in_app_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow:accessibleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow5shvisC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib3bpB2Rt9BsCXXHeap9ah_strlenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmSLAstrlen_cstr_tleafC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib5EseedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib3bpB3Lib<LbB_DiagStmt7ds_costC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmWXK=ev_zext16_shDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_DiagStmt7dla_errC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow;addressableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmU2K8tbl_subbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmU2K8tbl_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib;LbB_PmExit28pm_epi_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut6pm_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmDS:pm_ds_dtorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmDS?pm_put_cseq_imgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmDS:pm_put_numC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmSL@pm_put_cseq_cstrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmSL8pm_leafSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmLeaf8pm_leaf0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmDS4ds_KC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmDS:pm_ds_ctorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmCall9pm_memsetC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib3bpB2HF3Lib5BStep8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts3t3bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts3t3aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibCont4CRep4ZlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib3bpB3Lib8LbB_ConvAkword_of_rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts3t3cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibCont4CRep5vec32C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface4liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibCont4CRep3fldC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib=SymExec3Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7tbl_okXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX28sym_execC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac8pmk_sh_pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7wa_diagC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7wa_userC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib=SymExec3Sound4SX2S9scs_denotC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz05C69OSSVerify5KrLib3bpB3Lib8LbB_FKit7fsh_patC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_FKit6lbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut=sr_tbl_checkXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib8u64_of_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_FKit8num_winsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes3sndK47Corelib4Init5Logic2or02C69OSSVerify5KrLib3bpB3Lib:LbB_PmGlue9rt_lookupC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC79OSSVerify5KrLib3bpB2HF3Lib4BMem8bytes_atC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01I79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt5BSegs5asegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib3bpB3Lib7LbB_Kit6SHBASEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26kentry00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib6LibPrs6PmBase4O_V3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB4AC_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB4LY_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB4MI_AC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26sentry00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmWXK6TBL_XZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PrsInv;PARSER_SIZEC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7PM_OBJSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase6PM_NSHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut4FSHBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g<HTbAPmWZ7g_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g3HHmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25sr_idC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g;RT_PM_XZ7_3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_DiagStmt7DS_SIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmCall9KEPT_REGSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g;RT_PM_XZ7_5C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_DiagStmt9DS_MAXLENC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase:PM_RESERVEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g<RT_PM_XZ7_13C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g<RT_PM_XZ7_17C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g<RT_PM_XZ7_21C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g<RT_PM_XZ7_25C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface9APC0_FREEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_DiagStmt8APUT_U16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmOL8RT_EEF44C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g;RT_PM_XZ7_1C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib6LibPrs6PrsInv7parserC00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface6fframeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface3memC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I59OSSVerify5KrLib6LibPrs6PmBase3pmc00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt5BSegs8AIMG_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface7AFS_HDRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5WV_FFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4WV_PC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase6O_WIDXC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib7Numbers7BinNums1N01I59OSSVerify5KrLib8SymExec33SX29sym_state00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface<AASAN_MEMSETC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I59OSSVerify5KrLib8SymExec33SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase8O_ICOUNTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut6PM_OWNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5WV_S1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_DiagStmt8ADS_CTORC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib;LbB_PrsStmt9PM_FCLASSC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01C69OSSVerify5KrLib3bpB3Lib<LbB_DiagStmt9APUT_CSEQC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt5BSegs7AIMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow3memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsConst8aglobalsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow7AAPP_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_TablStmt=AT_IDESC_NAMEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g;RT_PM_XZ7_7C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface<ASTRLEN_STUBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g;RT_PM_XZ7_9C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g<RT_PM_XZ7_11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_DiagStmt8APUT_U64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g<RT_PM_XZ7_15C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g<RT_PM_XZ7_19C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g<RT_PM_XZ7_23C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_DiagStmt:DS_ERR_OFFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_DiagStmt8ADS_DTORC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g<RT_PM_XZ7_27C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib;LbB_PrsStmt5PM_PFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmWZ7g<RT_PM_XZ7_29C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib;LbB_PmExit28TBL_EXITC1?~~~~~~~~~~~~~~~".

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmPD.
Definition RT_XZ7K : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (20%bv, SH_FF); (21%bv, WADD WV_FF 9136);
   (22%bv, WADD WV_FF 10112); (24%bv, WADD WV_FF 10176); (25%bv, WADD WV_P 264); (26%bv, WADD WV_FF 112)].
Definition RT_PM_XZ7_3 : list (reg * expr) := [(1%bv, ELit 0xf46a8); (10%bv, WADD WV_FF 10176); (11%bv, EVar WV_P); (12%bv, ELit 18446744073709551612); (23%bv, EVar WV_P); (27%bv, ELit 18446744073709551608)] ++ RT_XZ7K.
Definition RT_PM_XZ7_5 : list (reg * expr) := [(1%bv, ELit 0xf46bc); (10%bv, WADD WV_FF 10176); (11%bv, ELit 148320); (12%bv, ELit 22); (23%bv, EVar WV_P); (27%bv, ELit 18446744073709551608)] ++ RT_XZ7K.
Definition RT_PM_XZ7_7 : list (reg * expr) := [(1%bv, ELit 0xf46e4); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XZ7K.
Definition RT_PM_XZ7_9 : list (reg * expr) := [(1%bv, ELit 0xf46ec); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XZ7K.
Definition RT_PM_XZ7_11 : list (reg * expr) := [(1%bv, ELit 0xf46fc); (10%bv, WADD WV_FF 10176); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XZ7K.
Definition RT_PM_XZ7_13 : list (reg * expr) := [(1%bv, ELit 0xf4710); (10%bv, WADD WV_FF 10176); (11%bv, ELit 148384); (12%bv, ELit 18); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XZ7K.
Definition RT_PM_XZ7_15 : list (reg * expr) := [(1%bv, ELit 0xf471c); (10%bv, WADD WV_FF 10176); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XZ7K.
Definition RT_PM_XZ7_17 : list (reg * expr) := [(1%bv, ELit 0xf4730); (10%bv, WADD WV_FF 10176); (11%bv, ELit 148448); (12%bv, ELit 34); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XZ7K.
Definition RT_PM_XZ7_19 : list (reg * expr) := [(1%bv, ELit 0xf4740); (10%bv, WADD WV_FF 10176); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XZ7K.
Definition RT_PM_XZ7_21 : list (reg * expr) := [(1%bv, ELit 0xf4754); (10%bv, WADD WV_FF 10176); (11%bv, ELit 148544); (12%bv, ELit 33); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XZ7K.
Definition RT_PM_XZ7_23 : list (reg * expr) := [(1%bv, ELit 0xf4760); (10%bv, WADD WV_FF 10176); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XZ7K.
Definition RT_PM_XZ7_25 : list (reg * expr) := [(1%bv, ELit 0xf4774); (10%bv, WADD WV_FF 10176); (11%bv, ELit 148640); (12%bv, ELit 1); (23%bv, EVar WV_P); (27%bv, EVar WV_FF)] ++ RT_XZ7K.
Definition RT_PM_XZ7_27 : list (reg * expr) := [(1%bv, ELit 0xf4780); (10%bv, WADD WV_FF 10176); (27%bv, EVar WV_FF)] ++ RT_XZ7K.


Section XZ7.
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
ltac2:(KReplay.run1 (kr_t_LbB_PmWZ7g ()) ["XZ7"] "p;2p;1p;3p10000p4p70p1000ip4p710p8g001Gj27Tg002Gj26Tg003Pj12Tg004Yj21Tg005Xj15Tg006_j13Tg007\j20Tg0087j34Tp,5HCEILR0p,1HR1'71601%211101%50%31'0'0'0'0p,4HHbp34o"). Qed.

  Lemma xz7_in3 : forall (l : list (Z * Z * Z)) a b c,
    existsb (fun u => match u with (x, y, z) => ((x =? a) && (y =? b) && (z =? c))%bool end) l = true -> In (a, b, c) l.
  Proof.
    induction l as [|[[x y] z] l IH]; intros a b c Hx; [discriminate Hx|].
    cbn [existsb] in Hx. apply orb_prop in Hx as [E|E].
    - left. apply andb_prop in E as [E Ez]. apply andb_prop in E as [Ex Ey].
      apply Z.eqb_eq in Ex. apply Z.eqb_eq in Ey. apply Z.eqb_eq in Ez. subst. reflexivity.
    - right. exact (IH a b c E).
  Qed.

  Lemma xz7_lit : forall p n sz rz, In (p, sz, rz) aglobals -> 0 <= n <= sz -> p + sz <= AAPP_HI ->
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

  Ltac xz7_rdn := lazymatch goal with |- exists bs, ?t = Some bs =>
    let r := eval vm_compute in t in lazymatch r with Some ?b => exists b; vm_compute; reflexivity end end.
  Ltac xz7_glob := apply xz7_in3; vm_compute; reflexivity.
  Ltac xz7_lit_at p n sz rz := exact (xz7_lit p n sz rz ltac:(xz7_glob) ltac:(lia) ltac:(unfold AAPP_HI; lia)
                                               ltac:(unfold AIMG_LO; lia) ltac:(lia) ltac:(xz7_rdn)).
  Lemma xz7_t16 : forall E (n : N) v, edenot E (EVar n) = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 ->
    edenot E (EAlu ALU_SRL (EMd M_MUL (ELit 281474976710656) (EVar n)) (ELit 48)) = Z_to_bv 64 v.
  Proof.
    intros E n v He Hv. cbn [edenot]. change (ev E n) with (edenot E (EVar n)). rewrite He.
    rewrite (HLib.w_mul 281474976710656 v) by lia.
    apply bv_eq. rewrite u_srl64, !u_lit64a.
    assert (E1 : (281474976710656 * v) mod 2 ^ 64 = v * 2 ^ 48) by (rewrite Z.mod_small by lia; lia).
    assert (E2 : 48 mod 2 ^ 64 mod 64 = 48) by reflexivity.
    rewrite E1, E2, Z.div_mul by lia. rewrite Z.mod_small by lia. reflexivity.
  Qed.
  Lemma pm_xz7 : forall (w : pmwA H) s LB LBs m mo (c : pmc) msF R F fc (io iwc op d lw : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 OL_HEAD) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_EEF44 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 10112) [C8 (Z_to_bv 64 io)] -> 0 <= io -> io + 1 <= c_widx c -> c_widx c < io + iwc ->
    rw_cells asegs m (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)] -> 0 <= iwc < 2 ^ 16 ->
    rw_cells asegs m (wa_ff w + 9616) [C8 (Z_to_bv 64 d)] -> idescA d op -> t3b (c_v3 c) = [] ->
    EXITKA H LINV w lw Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc io iwc op d lw Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Cio Hio Hio1 HLT2 Ciwc Hiwc Cd Hd HNIL KX.
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
    pose proof (wk_n H w OK) as WN.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    pose proof (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as V3. unfold O_V3 in V3.
    destruct V3 as (Vv & Vv' & VD & Hlen3 & Hb3 & F30 & F31 & F32 & FE3).
    set (b3 := t3a (c_v3 c)) in *. set (xs3 := t3b (c_v3 c)) in *.
    pose proof HNIL as EMP.
    assert (KWI : forall Xs (e : expr), let E := Eseed R (wenv_vals w ++ Xs) in
              edenot E e = Z_to_bv 64 (c_widx c) -> kentry_ok ASEGS E m (KWord (SA (EVar 32) 72) 8 e)).
    { intros Xs e. lazy zeta. intros He. pose proof (ev_world_all H w _ (env_world_seed H w R Xs)) as (E32 & _).
      apply (kword_of_fld _ m (wa_p w + O_WIDX) 8 (c_widx c)); [exact (xa_widx _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | | | | exact He];
        [unfold estart; cbn [a_base a_off]; rewrite E32, u64_of_Z by lia; unfold O_WIDX; lia | unfold O_WIDX, PARSER_SIZE in *; lia
        | unfold O_WIDX, PARSER_SIZE in *; cbn; lia]. }
    set (Xs := [Z_to_bv 64 io; Z_to_bv 64 iwc; Z_to_bv 64 (c_widx c); Z_to_bv 64 b3; Z_to_bv 64 (b3 + 4 * Zlen xs3)]).
    pose proof (env_world_seed H w R Xs) as HE.
    assert (Y41 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 io) by (ev_xs; reflexivity).
    assert (Y42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 iwc) by (ev_xs; reflexivity).
    assert (Y43 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 43) = Z_to_bv 64 (c_widx c)) by (ev_xs; reflexivity).
    assert (Y44 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 44) = Z_to_bv 64 b3) by (ev_xs; reflexivity).
    assert (Y45 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 45) = Z_to_bv 64 (b3 + 4 * Zlen xs3)) by (ev_xs; reflexivity).
    assert (Z42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EExt false 0 2 (EVar 42)) = Z_to_bv 64 iwc) by (apply edenot_zext16; [exact Y42 | lia]).
    assert (YIO : edenot (Eseed R (wenv_vals w ++ Xs)) (EAlu ALU_ADD (EVar 41) (EExt false 0 2 (EVar 42))) = Z_to_bv 64 (io + iwc))
      by (apply ev_add2; [exact Y41 | exact Z42 | lia | lia | lia]).
    assert (Hz : Zlen xs3 = 0) by (rewrite EMP; reflexivity).
    assert (HKX : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m [KWord (SA (EVar 33) 10112) 8 (EVar 41); KWord (SA (EVar 33) 9136) 2 (EVar 42); KWord (SA (EVar 32) 72) 8 (EVar 43)]).
    { apply Forall_cons; [apply (KC8 R m Xs 10112 io); [exact Cio | lia | lia | exact Y41]|].
      apply Forall_cons; [apply (KC2 R m Xs 9136 iwc); [exact Ciwc | lia | lia | exact Y42]|].
      apply Forall_cons; [apply KWI; exact Y43 | apply Forall_nil]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs [KWord (SA (EVar 33) 10112) 8 (EVar 41); KWord (SA (EVar 33) 9136) 2 (EVar 42); KWord (SA (EVar 32) 72) 8 (EVar 43)] HKX
          400%nat [APDIAG] [true; false] 44%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_3.
    { split_scs. all: first
        [ eapply (sc_rd_fld8 _ _ _ _ _ _ F30); [rewrite (adenot_of_estart _ _ (wa_p w + 264)); [reflexivity | rewrite (estart_p H w _ _ OK HE); lia | lia] | ev_xs; reflexivity]
        | eapply (sc_rd_fld8 _ _ _ _ _ _ F31); [rewrite (adenot_of_estart _ _ (wa_p w + 264 + 8)); [reflexivity | rewrite (estart_p H w _ _ OK HE); lia | lia] | ev_xs; reflexivity]
        | cbn [sc_denot]; rewrite ?Y43, ?Y44, ?Y45, ?YIO; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HT1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in X1, VIS1 end.
    assert (FK1 : ffkeep w m M1).
    { lazymatch type of Hlf1 with log_flat _ ?lg =>
        assert (INS : forallb (sym_inside [(FSHB, SHBASE, SHBASE + 2048)]) lg = true) by (vm_compute; reflexivity) end.
      pose proof (munch_sym _ m _ _ Hlf1 INS) as MU. cbn [num_wins map] in MU.
      rewrite (ev_fshb H w _ OK (env_world_seed H w R Xs)) in MU.
      apply (ffkeep_munch w _ m M1 MU (wmono_mem_denot _ _ _)).
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    assert (S18_1 : PropExec.getr R1 18%bv = Z_to_bv 64 io) by (rewrite (HR1 18%bv); exact Y41).
    assert (S19_1 : PropExec.getr R1 19%bv = Z_to_bv 64 (c_widx c)) by (rewrite (HR1 19%bv); exact Y43).
    eapply (pm_pdiag H HHbp LINV ds_repA APDIAG false HPDIAG0 w s LB LBs M1 mo1 c (47%nat :: S_INSTR) TBL_EEF44 [] 0 msF1 R1 F fc
              10176 0xf46a8 (-4) Q);
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
    assert (S18_2 : PropExec.getr R2 18%bv = Z_to_bv 64 io) by (rewrite (KEEP2 18%bv ltac:(inb)); exact S18_1).
    assert (S19_2 : PropExec.getr R2 19%bv = Z_to_bv 64 (c_widx c)) by (rewrite (KEEP2 19%bv ltac:(inb)); exact S19_1).
    pose proof (regs_keep w [] R1 R2 RT_PM_XZ7_3 (regs_tbl_restrict w [] Xs R1 RT_PM_XZ7_3 HT1 ltac:(vm_compute; reflexivity)) KEEP2) as HT2.
    clear Cio Ciwc Cd FK1 CL2.

    assert (HKb : know_ok asegs (Eseed R2 (wenv_vals w ++ [])) m2 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word) (@nil kentry)  HKb
          200%nat [APUT_CSEQ] (@nil bool) 41%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_5.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HT3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m2 in X3 end.
    change (mem_denot _ m2 _) with m2 in VIS3.
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
    assert (S18_3 : PropExec.getr R3 18%bv = Z_to_bv 64 io) by (rewrite (HR3 18%bv); exact S18_2).
    assert (S19_3 : PropExec.getr R3 19%bv = Z_to_bv 64 (c_widx c)) by (rewrite (HR3 19%bv); exact S19_2).
    assert (L1 : (forall m', ACONST m' -> accessible m' 148320 22) /\
                 (exists bs, length bs = Z.to_nat 22 /\ forall m', mem_inv asegs m' -> bytes_at asegs m' 148320 bs))
      by xz7_lit_at 148320 22 23 64.
    destruct L1 as [ACX3 BYX3].
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF3 R3 _ _ 10176 0xf46bc 148320 22 (-4)
              0 Q);
      [ exact OK | exact X3 | vm_compute; reflexivity | reflexivity | exact KR3 | exact VIS3 | exact RF3 | exact FZ2
      | rtf HT3 | reflexivity | lia | rtf HT3 | rtf HT3 | exact G4_3 | rtf HT3 | rtf HT3 | rtf HT3
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | exact ACX3 | exact BYX3 | exact DS2 | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF4 mo4 R4 F4 fc4 s4 LB4 m4 TB4 KR4 VIS4 RF4 FZ4 X4 KEEP4 [DS4 _] CL4.
    assert (Cio4 : rw_cells asegs m4 (wa_ff w + 10112) [C8 (Z_to_bv 64 io)]) by (apply CL4; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Cio2]).
    assert (Ciwc4 : rw_cells asegs m4 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply CL4; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Ciwc2]).
    assert (Cd4 : rw_cells asegs m4 (wa_ff w + 9616) [C8 (Z_to_bv 64 d)]) by (apply CL4; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Cd2]).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (rewrite (KEEP4 3%bv ltac:(inb)); exact G3_3).
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (rewrite (KEEP4 4%bv ltac:(inb)); exact G4_3).
    assert (S18_4 : PropExec.getr R4 18%bv = Z_to_bv 64 io) by (rewrite (KEEP4 18%bv ltac:(inb)); exact S18_3).
    assert (S19_4 : PropExec.getr R4 19%bv = Z_to_bv 64 (c_widx c)) by (rewrite (KEEP4 19%bv ltac:(inb)); exact S19_3).
    pose proof (regs_keep w [] R3 R4 RT_PM_XZ7_5 HT3 KEEP4) as HT4.
    clear Cio2 Ciwc2 Cd2 CL4.

    set (Xc := [Z_to_bv 64 d]).
    assert (Y41c : edenot (Eseed R4 (wenv_vals w ++ Xc)) (EVar 41) = Z_to_bv 64 d) by (ev_xs; reflexivity).
    assert (HKc : know_ok asegs (Eseed R4 (wenv_vals w ++ Xc)) m4 [KWord (SA (EVar 33) 9616) 8 (EVar 41)]).
    { apply Forall_cons; [apply (KC8 R4 m4 Xc 9616 d); [exact Cd4 | lia | lia | exact Y41c] | apply Forall_nil]. }
    pm_goX HHm LINV_frame OK X4 KR4 VIS4 RF4 HT4 Xc [KWord (SA (EVar 33) 9616) 8 (EVar 41)] HKc
          200%nat [AT_IDESC_NAME] [true; true] 42%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_7.
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
    assert (S19_5 : PropExec.getr R5 19%bv = Z_to_bv 64 (c_widx c - io)) by (rewrite (HR5 19%bv); apply ev_subw_small; [exact S19_4 | exact S18_4 | lia | lia]).
    eapply (pm_leaf0 H HHm LINV LINV_frame AT_IDESC_NAME TL_STACK _ _ _ (tla_idesc_name HTL) (d, op) w _ _ LBs _ _ c _ TBL_EEF44 [] _ _
              msF5 R5 _ _ 0xf46e4 Q);
      [ exact OK | exact X5 | exact KR5 | exact VIS5 | exact RF5 | rtf HT5 | rtf HT5 | reflexivity | lia | unfold TL_STACK; lia | reflexivity
      | cbv beta iota; split; [exact Hd | rewrite (HR5 10%bv); exact Y41c] | vm_compute; reflexivity | reflexivity | ].
    intros msF6 mo6 m6 R6 KR6 VIS6 RF6 X6 KEEP6 MU6 WM6 LQ6.
    destruct LQ6 as (pn & nn & CS & Epn).
    pose proof CS as (CS1 & CS2 & _).
    pose proof (ds_rep_leaf H HHbp LINV ds_repA DSL w _ _ _ _ _ _ _ _ _ _ _ m6 TL_STACK 10176 (-4) _ OK X5 MU6
                  ltac:(unfold TL_STACK; lia) ltac:(lia) ltac:(unfold DS_SIZE; lia) DS4) as DS6.
    pose proof (FKS m4 m6 TL_STACK MU6 WM6 ltac:(unfold TL_STACK; lia)) as FK6.
    assert (Cio6 : rw_cells asegs m6 (wa_ff w + 10112) [C8 (Z_to_bv 64 io)]) by (apply FK6; [lia | cbn; lia | exact Cio4]).
    assert (Ciwc6 : rw_cells asegs m6 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply FK6; [lia | cbn; lia | exact Ciwc4]).
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (rewrite (KEEP6 3%bv ltac:(inb)); exact G3_5).
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (rewrite (KEEP6 4%bv ltac:(inb)); exact G4_5).
    assert (S19_6 : PropExec.getr R6 19%bv = Z_to_bv 64 (c_widx c - io)) by (rewrite (KEEP6 19%bv ltac:(inb)); exact S19_5).
    pose proof (regs_keep w [] R5 R6 RT_PM_XZ7_7 (regs_tbl_restrict w [] Xc R5 RT_PM_XZ7_7 HT5 ltac:(vm_compute; reflexivity)) KEEP6) as HT6.
    clear Cio4 Ciwc4 Cd4 FK6 DS4.

    assert (HKd : know_ok asegs (Eseed R6 (wenv_vals w ++ [])) m6 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X6 KR6 VIS6 RF6 HT6 (@nil word) (@nil kentry) HKd
          200%nat [ASTRLEN_STUB] (@nil bool) 41%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_9.
    { split_scs. }
    intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HT7 HR7 Hlf7.
    lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m6 in X7 end.
    change (mem_denot _ m6 _) with m6 in VIS7.
    assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (HR7 3%bv); exact G3_6).
    assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (HR7 4%bv); exact G4_6).
    assert (S19_7 : PropExec.getr R7 19%bv = Z_to_bv 64 (c_widx c - io)) by (rewrite (HR7 19%bv); exact S19_6).
    assert (P18 : PropExec.getr R7 18%bv = Z_to_bv 64 pn) by (rewrite (HR7 18%bv); exact Epn).
    eapply (pm_leafS H HHm LINV LINV_frame ASTRLEN_STUB AINTRIN_STACK _ _ _ (strlen_cstr_tleaf (ah_strlen H HHm)) (pn, nn) w _ _ LBs _ _ c _
              TBL_EEF44 [] _ _ msF7 R7 _ _ 0xf46ec Q);
      [ exact OK | exact X7 | exact KR7 | exact VIS7 | exact RF7 | rtf HT7 | rtf HT7 | reflexivity | lia | unfold AINTRIN_STACK; lia | reflexivity
      | cbv beta; cbn [fst snd]; split; [exact CS | rewrite (HR7 10%bv); exact Epn] | vm_compute; reflexivity | reflexivity | ].
    intros msF8 mo8 m8 R8 KR8 VIS8 RF8 X8 KEEP8 MU8 WM8 LQ8.
    cbv beta in LQ8. cbn [snd] in LQ8.
    pose proof (ds_rep_leaf H HHbp LINV ds_repA DSL w _ _ _ _ _ _ _ _ _ _ _ m8 AINTRIN_STACK 10176 (-4) _ OK X7 MU8
                  ltac:(unfold AINTRIN_STACK; lia) ltac:(lia) ltac:(unfold DS_SIZE; lia) DS6) as DS8.
    pose proof (FKS m6 m8 AINTRIN_STACK MU8 WM8 ltac:(unfold AINTRIN_STACK; lia)) as FK8.
    assert (Cio8 : rw_cells asegs m8 (wa_ff w + 10112) [C8 (Z_to_bv 64 io)]) by (apply FK8; [lia | cbn; lia | exact Cio6]).
    assert (Ciwc8 : rw_cells asegs m8 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply FK8; [lia | cbn; lia | exact Ciwc6]).
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (rewrite (KEEP8 3%bv ltac:(inb)); exact G3_7).
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (rewrite (KEEP8 4%bv ltac:(inb)); exact G4_7).
    assert (S19_8 : PropExec.getr R8 19%bv = Z_to_bv 64 (c_widx c - io)) by (rewrite (KEEP8 19%bv ltac:(inb)); exact S19_7).
    assert (P18' : PropExec.getr R8 18%bv = Z_to_bv 64 pn) by (rewrite (KEEP8 18%bv ltac:(inb)); exact P18).
    pose proof (regs_keep w [] R7 R8 RT_PM_XZ7_9 HT7 KEEP8) as HT8.
    clear Cio6 Ciwc6 FK8 DS6.

    assert (HKe : know_ok asegs (Eseed R8 (wenv_vals w ++ [])) m8 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X8 KR8 VIS8 RF8 HT8 (@nil word) (@nil kentry) HKe
          200%nat [APUT_CSEQ] (@nil bool) 41%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_11.
    { split_scs. }
    intros msF9 mo9 R9 KR9 VIS9 RF9 X9 HT9 HR9 Hlf9.
    lazymatch type of X9 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m8 in X9 end.
    change (mem_denot _ m8 _) with m8 in VIS9.
    assert (G3_9 : PropExec.getr R9 3%bv = wa_gp w) by (rewrite (HR9 3%bv); exact G3_8).
    assert (G4_9 : PropExec.getr R9 4%bv = wa_tp w) by (rewrite (HR9 4%bv); exact G4_8).
    assert (S19_9 : PropExec.getr R9 19%bv = Z_to_bv 64 (c_widx c - io)) by (rewrite (HR9 19%bv); exact S19_8).
    eapply (pm_put_cseq_cstr H HHbp LINV ds_repA DSL HCSEQ w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF9 R9 _ _ 10176 0xf46fc pn nn (-4) (0 + 22) Q);
      [ exact OK | exact X9 | vm_compute; reflexivity | reflexivity | exact KR9 | exact VIS9 | exact RF9 | exact FZ4
      | rtf HT9 | reflexivity | lia | rtf HT9 | rtf HT9 | exact G4_9 | rtf HT9 | rewrite (HR9 11%bv); exact P18' | rewrite (HR9 12%bv); exact LQ8
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | exact CS | exact DS8 | unfold DS_MAXLEN; lia
      | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF10 mo10 R10 F10 fc10 s10 LB10 m10 TB10 KR10 VIS10 RF10 FZ10 X10 KEEP10 [DS10 _] CL10.
    assert (Cio10 : rw_cells asegs m10 (wa_ff w + 10112) [C8 (Z_to_bv 64 io)]) by (apply CL10; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Cio8]).
    assert (Ciwc10 : rw_cells asegs m10 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply CL10; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Ciwc8]).
    assert (G3_10 : PropExec.getr R10 3%bv = wa_gp w) by (rewrite (KEEP10 3%bv ltac:(inb)); exact G3_9).
    assert (G4_10 : PropExec.getr R10 4%bv = wa_tp w) by (rewrite (KEEP10 4%bv ltac:(inb)); exact G4_9).
    assert (S19_10 : PropExec.getr R10 19%bv = Z_to_bv 64 (c_widx c - io)) by (rewrite (KEEP10 19%bv ltac:(inb)); exact S19_9).
    pose proof (regs_keep w [] R9 R10 RT_PM_XZ7_11 HT9 KEEP10) as HT10.
    clear Cio8 Ciwc8 CL10 DS8.

    assert (HKf : know_ok asegs (Eseed R10 (wenv_vals w ++ [])) m10 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X10 KR10 VIS10 RF10 HT10 (@nil word) (@nil kentry) HKf
          200%nat [APUT_CSEQ] (@nil bool) 41%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_13.
    { split_scs. }
    intros msF11 mo11 R11 KR11 VIS11 RF11 X11 HT11 HR11 Hlf11.
    lazymatch type of X11 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m10 in X11 end.
    change (mem_denot _ m10 _) with m10 in VIS11.
    assert (G3_11 : PropExec.getr R11 3%bv = wa_gp w) by (rewrite (HR11 3%bv); exact G3_10).
    assert (G4_11 : PropExec.getr R11 4%bv = wa_tp w) by (rewrite (HR11 4%bv); exact G4_10).
    assert (S19_11 : PropExec.getr R11 19%bv = Z_to_bv 64 (c_widx c - io)) by (rewrite (HR11 19%bv); exact S19_10).
    assert (L2 : (forall m', ACONST m' -> accessible m' 148384 18) /\
                 (exists bs, length bs = Z.to_nat 18 /\ forall m', mem_inv asegs m' -> bytes_at asegs m' 148384 bs))
      by xz7_lit_at 148384 18 19 64.
    destruct L2 as [ACC2 BYT2].
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF11 R11 _ _ 10176 0xf4710 148384 18 (-4)
              (0 + 22 + nn) Q);
      [ exact OK | exact X11 | vm_compute; reflexivity | reflexivity | exact KR11 | exact VIS11 | exact RF11 | exact FZ10
      | rtf HT11 | reflexivity | lia | rtf HT11 | rtf HT11 | exact G4_11 | rtf HT11 | rtf HT11 | rtf HT11
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | exact ACC2 | exact BYT2 | exact DS10 | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF12 mo12 R12 F12 fc12 s12 LB12 m12 TB12 KR12 VIS12 RF12 FZ12 X12 KEEP12 [DS12 _] CL12.
    assert (Cio12 : rw_cells asegs m12 (wa_ff w + 10112) [C8 (Z_to_bv 64 io)]) by (apply CL12; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Cio10]).
    assert (Ciwc12 : rw_cells asegs m12 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply CL12; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Ciwc10]).
    assert (G3_12 : PropExec.getr R12 3%bv = wa_gp w) by (rewrite (KEEP12 3%bv ltac:(inb)); exact G3_11).
    assert (G4_12 : PropExec.getr R12 4%bv = wa_tp w) by (rewrite (KEEP12 4%bv ltac:(inb)); exact G4_11).
    assert (S19_12 : PropExec.getr R12 19%bv = Z_to_bv 64 (c_widx c - io)) by (rewrite (KEEP12 19%bv ltac:(inb)); exact S19_11).
    pose proof (regs_keep w [] R11 R12 RT_PM_XZ7_13 HT11 KEEP12) as HT12.
    clear Cio10 Ciwc10 CL12 DS10.

    set (Xg := [Z_to_bv 64 io]).
    assert (Y41g : edenot (Eseed R12 (wenv_vals w ++ Xg)) (EVar 41) = Z_to_bv 64 io) by (ev_xs; reflexivity).
    assert (HKg : know_ok asegs (Eseed R12 (wenv_vals w ++ Xg)) m12 [KWord (SA (EVar 33) 10112) 8 (EVar 41)]).
    { apply Forall_cons; [apply (KC8 R12 m12 Xg 10112 io); [exact Cio12 | lia | lia | exact Y41g] | apply Forall_nil]. }
    pm_goX HHm LINV_frame OK X12 KR12 VIS12 RF12 HT12 Xg [KWord (SA (EVar 33) 10112) 8 (EVar 41)] HKg
          200%nat [APUT_U64] (@nil bool) 42%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_15.
    { split_scs. }
    intros msF13 mo13 R13 KR13 VIS13 RF13 X13 HT13 HR13 Hlf13.
    lazymatch type of X13 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m12 in X13 end.
    change (mem_denot _ m12 _) with m12 in VIS13.
    assert (G3_13 : PropExec.getr R13 3%bv = wa_gp w) by (rewrite (HR13 3%bv); exact G3_12).
    assert (G4_13 : PropExec.getr R13 4%bv = wa_tp w) by (rewrite (HR13 4%bv); exact G4_12).
    assert (S19_13 : PropExec.getr R13 19%bv = Z_to_bv 64 (c_widx c - io)) by (rewrite (HR13 19%bv); exact S19_12).
    eapply (pm_put_num H HHbp LINV ds_repA DSL APUT_U64 0 (2 ^ 64) (fun x => x) HU64 w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF13 R13 _ _
              10176 0xf471c io (-4) (0 + 22 + nn + 18) Q);
      [ exact OK | exact X13 | vm_compute; reflexivity | reflexivity | exact KR13 | exact VIS13 | exact RF13 | exact FZ12
      | rtf HT13 | reflexivity | lia | rtf HT13 | rtf HT13 | exact G4_13 | rtf HT13 | cbv beta; rewrite (HR13 11%bv); exact Y41g | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | exact DS12 | unfold DS_MAXLEN; lia
      | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF14 mo14 R14 F14 fc14 s14 LB14 m14 TB14 KR14 VIS14 RF14 FZ14 X14 KEEP14 [DS14 _] CL14.
    assert (Ciwc14 : rw_cells asegs m14 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply CL14; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Ciwc12]).
    assert (G3_14 : PropExec.getr R14 3%bv = wa_gp w) by (rewrite (KEEP14 3%bv ltac:(inb)); exact G3_13).
    assert (G4_14 : PropExec.getr R14 4%bv = wa_tp w) by (rewrite (KEEP14 4%bv ltac:(inb)); exact G4_13).
    assert (S19_14 : PropExec.getr R14 19%bv = Z_to_bv 64 (c_widx c - io)) by (rewrite (KEEP14 19%bv ltac:(inb)); exact S19_13).
    pose proof (regs_keep w [] R13 R14 RT_PM_XZ7_15 (regs_tbl_restrict w [] Xg R13 RT_PM_XZ7_15 HT13 ltac:(vm_compute; reflexivity)) KEEP14) as HT14.
    clear Cio12 Ciwc12 CL14 DS12.

    assert (HKh : know_ok asegs (Eseed R14 (wenv_vals w ++ [])) m14 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X14 KR14 VIS14 RF14 HT14 (@nil word) (@nil kentry)  HKh
          200%nat [APUT_CSEQ] (@nil bool) 41%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_17.
    { split_scs. }
    intros msF15 mo15 R15 KR15 VIS15 RF15 X15 HT15 HR15 Hlf15.
    lazymatch type of X15 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m14 in X15 end.
    change (mem_denot _ m14 _) with m14 in VIS15.
    assert (G3_15 : PropExec.getr R15 3%bv = wa_gp w) by (rewrite (HR15 3%bv); exact G3_14).
    assert (G4_15 : PropExec.getr R15 4%bv = wa_tp w) by (rewrite (HR15 4%bv); exact G4_14).
    assert (S19_15 : PropExec.getr R15 19%bv = Z_to_bv 64 (c_widx c - io)) by (rewrite (HR15 19%bv); exact S19_14).
    assert (L3 : (forall m', ACONST m' -> accessible m' 148448 34) /\
                 (exists bs, length bs = Z.to_nat 34 /\ forall m', mem_inv asegs m' -> bytes_at asegs m' 148448 bs))
      by xz7_lit_at 148448 34 35 96.
    destruct L3 as [ACC15 BYT15].
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF15 R15 _ _ 10176 0xf4730 148448 34 (-4)
              (0 + 22 + nn + 18 + 24) Q);
      [ exact OK | exact X15 | vm_compute; reflexivity | reflexivity | exact KR15 | exact VIS15 | exact RF15 | exact FZ14
      | rtf HT15 | reflexivity | lia | rtf HT15 | rtf HT15 | exact G4_15 | rtf HT15 | rtf HT15 | rtf HT15
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | exact ACC15 | exact BYT15 | exact DS14 | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF16 mo16 R16 F16 fc16 s16 LB16 m16 TB16 KR16 VIS16 RF16 FZ16 X16 KEEP16 [DS16 _] CL16.
    assert (Ciwc16 : rw_cells asegs m16 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply CL16; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Ciwc14]).
    assert (G3_16 : PropExec.getr R16 3%bv = wa_gp w) by (rewrite (KEEP16 3%bv ltac:(inb)); exact G3_15).
    assert (G4_16 : PropExec.getr R16 4%bv = wa_tp w) by (rewrite (KEEP16 4%bv ltac:(inb)); exact G4_15).
    assert (S19_16 : PropExec.getr R16 19%bv = Z_to_bv 64 (c_widx c - io)) by (rewrite (KEEP16 19%bv ltac:(inb)); exact S19_15).
    pose proof (regs_keep w [] R15 R16 RT_PM_XZ7_17 HT15 KEEP16) as HT16.
    clear Ciwc14 CL16 DS14.

    assert (HKi : know_ok asegs (Eseed R16 (wenv_vals w ++ [])) m16 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X16 KR16 VIS16 RF16 HT16 (@nil word) (@nil kentry)  HKi
          200%nat [APUT_U16] (@nil bool) 41%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_19.
    { split_scs. }
    intros msF17 mo17 R17 KR17 VIS17 RF17 X17 HT17 HR17 Hlf17.
    lazymatch type of X17 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m16 in X17 end.
    change (mem_denot _ m16 _) with m16 in VIS17.
    assert (G3_17 : PropExec.getr R17 3%bv = wa_gp w) by (rewrite (HR17 3%bv); exact G3_16).
    assert (G4_17 : PropExec.getr R17 4%bv = wa_tp w) by (rewrite (HR17 4%bv); exact G4_16).
    eapply (pm_put_num H HHbp LINV ds_repA DSL APUT_U16 0 (2 ^ 16) (fun x => x) HU16 w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF17 R17 _ _
              10176 0xf4740 (c_widx c - io) (-4) (0 + 22 + nn + 18 + 24 + 34) Q);
      [ exact OK | exact X17 | vm_compute; reflexivity | reflexivity | exact KR17 | exact VIS17 | exact RF17 | exact FZ16
      | rtf HT17 | reflexivity | lia | rtf HT17 | rtf HT17 | exact G4_17 | rtf HT17
      | cbv beta; rewrite (HR17 11%bv); apply xz7_t16; [exact S19_16 | lia] | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | exact DS16 | unfold DS_MAXLEN; lia
      | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF18 mo18 R18 F18 fc18 s18 LB18 m18 TB18 KR18 VIS18 RF18 FZ18 X18 KEEP18 [DS18 _] CL18.
    assert (Ciwc18 : rw_cells asegs m18 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply CL18; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Ciwc16]).
    assert (G3_18 : PropExec.getr R18 3%bv = wa_gp w) by (rewrite (KEEP18 3%bv ltac:(inb)); exact G3_17).
    assert (G4_18 : PropExec.getr R18 4%bv = wa_tp w) by (rewrite (KEEP18 4%bv ltac:(inb)); exact G4_17).
    pose proof (regs_keep w [] R17 R18 RT_PM_XZ7_19 HT17 KEEP18) as HT18.
    clear Ciwc16 CL18 DS16.

    assert (HKj : know_ok asegs (Eseed R18 (wenv_vals w ++ [])) m18 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X18 KR18 VIS18 RF18 HT18 (@nil word) (@nil kentry)  HKj
          200%nat [APUT_CSEQ] (@nil bool) 41%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_21.
    { split_scs. }
    intros msF19 mo19 R19 KR19 VIS19 RF19 X19 HT19 HR19 Hlf19.
    lazymatch type of X19 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m18 in X19 end.
    change (mem_denot _ m18 _) with m18 in VIS19.
    assert (G3_19 : PropExec.getr R19 3%bv = wa_gp w) by (rewrite (HR19 3%bv); exact G3_18).
    assert (G4_19 : PropExec.getr R19 4%bv = wa_tp w) by (rewrite (HR19 4%bv); exact G4_18).
    assert (L4 : (forall m', ACONST m' -> accessible m' 148544 33) /\
                 (exists bs, length bs = Z.to_nat 33 /\ forall m', mem_inv asegs m' -> bytes_at asegs m' 148544 bs))
      by xz7_lit_at 148544 33 34 96.
    destruct L4 as [ACC19 BYT19].
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF19 R19 _ _ 10176 0xf4754 148544 33 (-4)
              (0 + 22 + nn + 18 + 24 + 34 + 24) Q);
      [ exact OK | exact X19 | vm_compute; reflexivity | reflexivity | exact KR19 | exact VIS19 | exact RF19 | exact FZ18
      | rtf HT19 | reflexivity | lia | rtf HT19 | rtf HT19 | exact G4_19 | rtf HT19 | rtf HT19 | rtf HT19
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | exact ACC19 | exact BYT19 | exact DS18 | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF20 mo20 R20 F20 fc20 s20 LB20 m20 TB20 KR20 VIS20 RF20 FZ20 X20 KEEP20 [DS20 _] CL20.
    assert (Ciwc20 : rw_cells asegs m20 (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)]) by (apply CL20; [lia | cbn; lia | cbn; unfold DS_SIZE; lia | exact Ciwc18]).
    assert (G3_20 : PropExec.getr R20 3%bv = wa_gp w) by (rewrite (KEEP20 3%bv ltac:(inb)); exact G3_19).
    assert (G4_20 : PropExec.getr R20 4%bv = wa_tp w) by (rewrite (KEEP20 4%bv ltac:(inb)); exact G4_19).
    pose proof (regs_keep w [] R19 R20 RT_PM_XZ7_21 HT19 KEEP20) as HT20.
    clear Ciwc18 CL20 DS18.

    set (Xi := [Z_to_bv 64 iwc]).
    assert (Y41i : edenot (Eseed R20 (wenv_vals w ++ Xi)) (EVar 41) = Z_to_bv 64 iwc) by (ev_xs; reflexivity).
    assert (HKk : know_ok asegs (Eseed R20 (wenv_vals w ++ Xi)) m20 [KWord (SA (EVar 33) 9136) 2 (EVar 41)]).
    { apply Forall_cons; [apply (KC2 R20 m20 Xi 9136 iwc); [exact Ciwc20 | lia | lia | exact Y41i] | apply Forall_nil]. }
    pm_goX HHm LINV_frame OK X20 KR20 VIS20 RF20 HT20 Xi [KWord (SA (EVar 33) 9136) 2 (EVar 41)] HKk
          200%nat [APUT_U16] (@nil bool) 42%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_23.
    { split_scs. }
    intros msF21 mo21 R21 KR21 VIS21 RF21 X21 HT21 HR21 Hlf21.
    lazymatch type of X21 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m20 in X21 end.
    change (mem_denot _ m20 _) with m20 in VIS21.
    assert (G3_21 : PropExec.getr R21 3%bv = wa_gp w) by (rewrite (HR21 3%bv); exact G3_20).
    assert (G4_21 : PropExec.getr R21 4%bv = wa_tp w) by (rewrite (HR21 4%bv); exact G4_20).
    eapply (pm_put_num H HHbp LINV ds_repA DSL APUT_U16 0 (2 ^ 16) (fun x => x) HU16 w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF21 R21 _ _
              10176 0xf4760 iwc (-4) (0 + 22 + nn + 18 + 24 + 34 + 24 + 33) Q);
      [ exact OK | exact X21 | vm_compute; reflexivity | reflexivity | exact KR21 | exact VIS21 | exact RF21 | exact FZ20
      | rtf HT21 | reflexivity | lia | rtf HT21 | rtf HT21 | exact G4_21 | rtf HT21
      | cbv beta; rewrite (HR21 11%bv);
        transitivity (edenot (Eseed R20 (wenv_vals w ++ Xi)) (EExt false 0 2 (EVar 41))); [reflexivity | apply edenot_zext16; [exact Y41i | lia]] | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | exact DS20 | unfold DS_MAXLEN; lia
      | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF22 mo22 R22 F22 fc22 s22 LB22 m22 TB22 KR22 VIS22 RF22 FZ22 X22 KEEP22 [DS22 _] CL22.
    assert (G3_22 : PropExec.getr R22 3%bv = wa_gp w) by (rewrite (KEEP22 3%bv ltac:(inb)); exact G3_21).
    assert (G4_22 : PropExec.getr R22 4%bv = wa_tp w) by (rewrite (KEEP22 4%bv ltac:(inb)); exact G4_21).
    pose proof (regs_keep w [] R21 R22 RT_PM_XZ7_23 (regs_tbl_restrict w [] Xi R21 RT_PM_XZ7_23 HT21 ltac:(vm_compute; reflexivity)) KEEP22) as HT22.
    clear Ciwc20 CL22 DS20.

    assert (HKl : know_ok asegs (Eseed R22 (wenv_vals w ++ [])) m22 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X22 KR22 VIS22 RF22 HT22 (@nil word) (@nil kentry)  HKl
          200%nat [APUT_CSEQ] (@nil bool) 41%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_25.
    { split_scs. }
    intros msF23 mo23 R23 KR23 VIS23 RF23 X23 HT23 HR23 Hlf23.
    lazymatch type of X23 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m22 in X23 end.
    change (mem_denot _ m22 _) with m22 in VIS23.
    assert (G3_23 : PropExec.getr R23 3%bv = wa_gp w) by (rewrite (HR23 3%bv); exact G3_22).
    assert (G4_23 : PropExec.getr R23 4%bv = wa_tp w) by (rewrite (HR23 4%bv); exact G4_22).
    assert (L5 : (forall m', ACONST m' -> accessible m' 148640 1) /\
                 (exists bs, length bs = Z.to_nat 1 /\ forall m', mem_inv asegs m' -> bytes_at asegs m' 148640 bs))
      by xz7_lit_at 148640 1 2 32.
    destruct L5 as [ACC23 BYT23].
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF23 R23 _ _ 10176 0xf4774 148640 1 (-4)
              (0 + 22 + nn + 18 + 24 + 34 + 24 + 33 + 24) Q);
      [ exact OK | exact X23 | vm_compute; reflexivity | reflexivity | exact KR23 | exact VIS23 | exact RF23 | exact FZ22
      | rtf HT23 | reflexivity | lia | rtf HT23 | rtf HT23 | exact G4_23 | rtf HT23 | rtf HT23 | rtf HT23
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | exact ACC23 | exact BYT23 | exact DS22 | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF24 mo24 R24 F24 fc24 s24 LB24 m24 TB24 KR24 VIS24 RF24 FZ24 X24 KEEP24 [DS24 _] CL24.
    assert (G3_24 : PropExec.getr R24 3%bv = wa_gp w) by (rewrite (KEEP24 3%bv ltac:(inb)); exact G3_23).
    assert (G4_24 : PropExec.getr R24 4%bv = wa_tp w) by (rewrite (KEEP24 4%bv ltac:(inb)); exact G4_23).
    pose proof (regs_keep w [] R23 R24 RT_PM_XZ7_25 HT23 KEEP24) as HT24.
    clear CL24 DS22.

    pose proof (dla_err LINV ds_repA DSL _ _ _ _ _ _ DS24) as CE24.
    replace (wa_ff w + 10176 + DS_ERR_OFF) with (wa_ff w + 10536) in CE24 by (unfold DS_ERR_OFF; lia).
    assert (HKn : know_ok asegs (Eseed R24 (wenv_vals w ++ [])) m24 [KWord (SA (EVar 33) 10536) 4 (ELit 4294967292)]).
    { apply Forall_cons; [apply (KC4 R24 m24 [] 10536 ((-4) mod 2 ^ 32)); [exact CE24 | lia | lia | rewrite EL; reflexivity] | apply Forall_nil]. }
    pm_goX HHm LINV_frame OK X24 KR24 VIS24 RF24 HT24 (@nil word) [KWord (SA (EVar 33) 10536) 4 (ELit 4294967292)] HKn
          200%nat [ADS_DTOR] (@nil bool) 41%N (47%nat :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_XZ7_27.
    { split_scs. }
    intros msF25 mo25 R25 KR25 VIS25 RF25 X25 HT25 HR25 Hlf25.
    lazymatch type of X25 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m24 in X25 end.
    change (mem_denot _ m24 _) with m24 in VIS25.
    assert (G3_25 : PropExec.getr R25 3%bv = wa_gp w) by (rewrite (HR25 3%bv); exact G3_24).
    assert (G4_25 : PropExec.getr R25 4%bv = wa_tp w) by (rewrite (HR25 4%bv); exact G4_24).
    assert (G23_25 : PropExec.getr R25 23%bv = Z_to_bv 64 (-4)) by (rewrite (HR25 23%bv); apply bv_eq; vm_compute; reflexivity).
    eapply (pm_ds_dtor H HHbp LINV ds_repA HDTOR w _ _ LBs _ _ c _ TBL_EEF44 [] _ _ msF25 R25 _ _ 10176 0xf4780 (-4) _ Q);
      [ exact OK | exact X25 | vm_compute; reflexivity | reflexivity | exact KR25 | exact VIS25 | exact RF25 | exact FZ24
      | rtf HT25 | reflexivity | lia | rtf HT25 | rtf HT25 | exact G4_25 | rtf HT25
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | exact DS24 | unfold PM_PF, PM_DTOR_RAS; inlist | ].
    intros msF26 mo26 R26 F26 fc26 s26 LB26 m26 TB26 KR26 VIS26 RF26 FZ26 X26 KEEP26 [-> _] _.
    assert (G3_26 : PropExec.getr R26 3%bv = wa_gp w) by (rewrite (KEEP26 3%bv ltac:(inb)); exact G3_25).
    assert (G4_26 : PropExec.getr R26 4%bv = wa_tp w) by (rewrite (KEEP26 4%bv ltac:(inb)); exact G4_25).
    assert (G23_26 : PropExec.getr R26 23%bv = Z_to_bv 64 (-4)) by (rewrite (KEEP26 23%bv ltac:(inb)); exact G23_25).
    pose proof (regs_keep w [] R25 R26 RT_PM_XZ7_27 HT25 KEEP26) as HT26.

    assert (HKo : know_ok asegs (Eseed R26 (wenv_vals w ++ [])) m26 []) by apply Forall_nil.
    pm_goX HHm LINV_frame OK X26 KR26 VIS26 RF26 HT26 (@nil word) (@nil kentry) HKo
          200%nat [EXIT_OPC] (@nil bool) 41%N [OB_INST; OB_FIRST_WORD; OB_INST_WC; OB_OPCODE_DESC] (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_EXIT.
    { split_scs. }
    intros msF27 mo27 R27 KR27 VIS27 RF27 X27 HT27 HR27 Hlf27.
    eapply (KX _ _ LBs _ mo27 c msF27 R27 F26 fc26 EXIT_OPC [OB_INST; OB_FIRST_WORD; OB_INST_WC; OB_OPCODE_DESC] (-4)); [| right; left; split; reflexivity].
    constructor.
    - do 2 eexists. split; [exact X27|]. split; [apply tbl_incl; vm_compute; reflexivity | intros Hr; discriminate Hr].
    - exact KR27.
    - exact VIS27.
    - exact RF27.
    - exact FZ26.
    - exact HT27.
    - rewrite (HR27 3%bv); exact G3_26.
    - rewrite (HR27 4%bv); exact G4_26.
    - split; [rewrite (HR27 23%bv); exact G23_26 | lia].
    - exact Htr.
    - exact Hbsz.
    - intros Hr; discriminate Hr.
  Qed.

End XZ7.
