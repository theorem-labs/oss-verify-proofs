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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmGlue LbB_PmVops LbB_PmHdr LbB_PmExit2 LbB_PmLH LbB_PmOL LbB_TablStmt LbB_PmU2K.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmWX5 () := "C69OSSVerify5KrLib3bpB2Rt7BsIface<asan_rt_hypsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_IfaceCasan_rt_hyps_bp_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_IfaceCalloc_ok_of_live_bpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_Iface9RHEAP_ahmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_IfaceAannotate_gen_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_Iface7cost_bpC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic5proj1I69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4pmwA00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5as_StC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI69OSSVerify5KrLib3bpB3Lib9LbB_PmOwn7pmw_okA00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5PMXAT00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib3bpB2Rt7BsIface8as_AKRELC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface6as_VISC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C79OSSVerify5KrLib3bpB2HF3Lib:BLPropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BMState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib3bpB3Lib:LbB_Bridge5rfullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut9regs_tblXC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_gpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_tpC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List2InC69OSSVerify5KrLib3bpB3Lib;LbB_PmExit2=pmxa_restrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7pm_geomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_ffC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_s1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib3bpB2Rt8BsShadow5aceilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow2shC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase6wa_sp0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib3bpB2Rt8BsShadow;aceil_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF8BeapCeil5hceilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib3bpB3Lib9LbB_PmTac:pmw_boundsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4wa_pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7wa_consC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase8wa_wordsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4wa_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5xa_v1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB3lblC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase4c_v1C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib7LibCont4CRep4mdefC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib7LibCont4CRep3fldC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut>env_world_seedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut9env_worldC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec33SX24expr05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX29sym_state01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut:pm_kn_baseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK59OSSVerify5KrLib8SymExec33SX27scripts01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX28sidecond06C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut<regs_tbl_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut6xboundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7tbl_okXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib3srsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX28sym_execC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib=SymExec3Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut:tbl_closedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7keys_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut8fkeys_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut=pm_kn_base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac<ev_world_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac6ev_addC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K47Corelib4Init5Logic3and01C59OSSVerify5KrLib=SymExec3Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26adenotC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib=SymExec3Sound4SX2S6estartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac8estart_pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_Conv@adenot_of_estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26edenotC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3lebC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib3bpB3Lib9LbB_PmTac8ev_xseedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmGlue:sc_rd_fld8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_FKit:sym_insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25s_logC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib3bpB3Lib8LbB_FKit7fsh_patC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_FKit6lbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_FSlots9upd_slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_FSlots9add_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut=sr_tbl_checkXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut9scal_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmU2K8tbl_subbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmU2K8tbl_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCutAregs_tbl_restrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26sr_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5as_SRC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib7LibHash6HStmts3t3aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts3t3bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts3t3cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibCont4CRep8vec_opndC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface4liveC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase9wenv_valsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib5EseedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26sentry01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac8pmk_sh_pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7wa_diagC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7wa_userC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac=pmk_sh_ffdisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut6pm_runC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib3bpB3Lib7LbB_Kit6SHBASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase4O_V1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB4AC_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB4LY_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_MILB4MI_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibCont4CRep7OPND_SZC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26sentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26kentry00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7S_INSTRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_PmWX56TBL_X5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_PmWX54HHx5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_PmWX55RT_X5C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase8S_MODULEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmLH8RT_EE648C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5blockC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface3memC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I59OSSVerify5KrLib6LibPrs6PmBase3pmc00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib3bpB2Rt5BSegs5asegsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib3bpB3Lib8LbB_PmLH9TBL_EE648C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt5BSegs8AIMG_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface7AFS_HDRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5mulop01I59OSSVerify5KrLib8SymExec33SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib8SymExec33SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25sr_idC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4WV_PC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut6PM_OWNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut4FSHBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7PM_OBJSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase6PM_NSHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5WV_S1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5WV_FFC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition TBL_X5 : list (Z * expr) :=
  [(32, WADD WV_FF 5472);
   (40, WADD WV_FF 4496);
   (48, WADD WV_FF 2048);
   (56, WADD WV_FF 4032);
   (64, WADD WV_FF 3056);
   (72, WADD WV_FF 3008);
   (80, WADD WV_FF 5008);
   (88, WADD WV_FF 32);
   (96, WADD WV_FF 4000);
   (104, ELit 65535);
   (112, WADD WV_FF 6000);
   (120, WADD WV_FF 6464);
   (128, WADD WV_FF 7952);
   (136, WADD WV_FF 3024);
   (144, WADD WV_FF 656);
   (152, WADD WV_FF 192);
   (160, WADD WV_FF 1120);
   (168, WADD WV_FF 3520);
   (176, ELit 262140);
   (184, WADD WV_P 176);
   (192, WADD WV_FF 5937);
   (200, WADD WV_FF 4544);
   (208, WADD WV_FF 2512);
   (216, WADD WV_FF 1584);
   (224, WADD WV_FF 3536);
   (232, WADD WV_FF 8576);
   (240, WADD WV_FF 7456);
   (248, WADD WV_FF 4528);
   (256, WADD WV_FF 7488);
   (264, WADD WV_FF 10640);
   (272, WADD WV_P 96);
   (280, WADD WV_FF 9056);
   (288, WADD WV_FF 11104);
   (296, WADD WV_FF 8544);
   (304, WADD WV_FF 9060);
   (312, WADD WV_FF 2976);
   (320, WADD WV_FF 5936);
   (328, WADD WV_FF 10176);
   (336, WADD WV_FF 8512);
   (344, WADD WV_FF 8016);
   (352, WADD WV_FF 7424);
   (360, WADD WV_P 92);
   (368, WADD WV_P 93);
   (376, WADD WV_P 40);
   (384, WADD WV_FF 6928);
   (392, WADD WV_FF 6960);
   (400, WADD WV_FF 9616);
   (408, WADD WV_P 216);
   (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit SHBASE));
   (424, WADD WV_FF 96);
   (432, WADD WV_P 232);
   (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit SHBASE));
   (448, WADD WV_P 224);
   (456, WADD WV_FF 64);
   (464, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit SHBASE));
   (472, WADD WV_FF 176);
   (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit SHBASE));
   (488, WADD WV_FF 8480);
   (496, WADD WV_FF 10112);
   (504, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit SHBASE));
   (512, WADD WV_P 88);
   (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit SHBASE));
   (528, WADD WV_P 48);
   (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit SHBASE));
   (544, ELit 2305843009213693952);
   (552, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit SHBASE));
   (560, WADD WV_P 240);
   (568, EVar WV_FF);
   (576, EVar WV_FF);
   (616, ELit SHBASE);
   (624, WADD WV_FF 9040);
   (648, EVar WV_P);
   (680, EVar WV_FF);
   (688, WADD WV_FF 10112);
   (696, WADD WV_FF 9136);
   (704, EVar WV_P);
   (712, WADD WV_FF 9120);
   (720, WADD WV_FF 9040)].

Definition RT_X5 : list (reg * expr) :=
  [(2%bv, EVar WV_S1);
   (8%bv, EVar WV_SP0);
   (9%bv, EVar WV_S1);
   (19%bv, WADD WV_FF 9040);
   (20%bv, SH_FF);
   (23%bv, EVar WV_P);
   (26%bv, WADD WV_P 216);
   (27%bv, EVar WV_FF)].

Section TX5.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma HHx5 : asan_rt_hyps H.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmWX5 ()) ["TX5"] "p;2p;1p;3g0000j27Tg0010j26Tg0029j12Tg003Bj21Tg004Aj15Tg005Hj13Tg006Ej20Tg006`j34Tp,5HCEILR0p,1HR1'71601%211101%50%31'0'0'0'0p,4HHbp34o"). Qed.

  Lemma tl_x5 : forall (w : pmwA H) s LB LBs m mo (c : pmc) tbl msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR tbl [] -> incl TBL_X5 tbl ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf5d28) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_X5 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1,
       as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 EXIT_RET) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w s LB LBs m1 mo1 c S_INSTR TBL_X5 [] ->
       regs_tbl w R1 RT_EXIT -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 23%bv = Z_to_bv 64 0 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c tbl msF R F fc Q OK X00 INCL KR0 VIS0 RF0 HT0 G3_0 G4_0 K.
    assert (X0 : PMXA H LINV w s LB LBs m mo c S_INSTR TBL_X5 []).
    { eapply pmxa_restrict; first [exact HHx5 | exact LINV_frame | exact OK | exact X00 | exact INCL | apply incl_refl | idtac].
      all: first [exact HHx5 | exact LINV_frame | exact OK | exact X00 | exact INCL | apply incl_refl]. }
    clear X00.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as V1. unfold O_V1 in V1.
    destruct V1 as (Vv & Vv' & VD & Hn1 & Hb1 & F10 & F11 & F12).
    assert (Rb1 : 0 <= t3a (c_v1 c) /\ t3a (c_v1 c) + OPND_SZ * t3c (c_v1 c) <= 2 ^ 63).
    { destruct Hb1 as [[Bz Cz] | (Bp & B16 & Cp & Bq & _)]; [rewrite Bz, Cz; lia | lia]. }
    set (Xs := [Z_to_bv 64 (t3a (c_v1 c)); Z_to_bv 64 (t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c))]).
    pose proof (env_world_seed H w R Xs) as HE.
    pm_go HHx5 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs (@nil kentry)
          400%nat [EXIT_RET; EXIT_OPC; EXIT_IWC] (@nil bool) 41%N S_INSTR (@nil Z) (@nil Z) TBL_X5 (@nil (Z * expr)) RT_EXIT.
    { split_scs. all: first
        [ eapply (sc_rd_fld8 _ _ _ _ _ _ F10); [rewrite (adenot_of_estart _ _ (wa_p w + 216)); [reflexivity | rewrite (estart_p H w _ _ OK HE); lia | lia] | ev_xs; reflexivity]
        | eapply (sc_rd_fld8 _ _ _ _ _ _ F11); [rewrite (adenot_of_estart _ _ (wa_p w + 216 + 8)); [reflexivity | rewrite (estart_p H w _ _ OK HE); lia | lia] | ev_xs; reflexivity]
        | match goal with |- ?g => idtac "SCLEFT" g end ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    eapply (K msF1 mo1 _ R1 KR1 VIS1 RF1 X1);
      [exact (regs_tbl_restrict w [] _ R1 RT_EXIT HTx1 ltac:(vm_compute; reflexivity))
      | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0 | rewrite (HR1 23%bv); reflexivity].
  Qed.
End TX5.
