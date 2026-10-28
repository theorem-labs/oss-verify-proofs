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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmGlue LbB_PmVops LbB_PmHdr LbB_PmExit2 LbB_PmLH LbB_PmOL LbB_TablStmt LbB_PmU2K.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmWX5 () := "C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<asan_rt_hypsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCasan_rt_hyps_bp_extC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCalloc_ok_of_live_bpC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface9RHEAP_ahmC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceAannotate_gen_stmtC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface7cost_bpI47Corelib4Init5Logic3and00C47Corelib4Init5Logic5proj1I6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4pmwA00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn7pmw_okA00K47Corelib4Init9Datatypes4list01I6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5PMXAT00C46Stdlib5Lists4List4inclK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSI47Corelib4Init5Logic2eq00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9regs_tblXK47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C4ARocqVerifyHarness?AgentSubmission8PropExec4getrC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_gpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_tpI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List2InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PmExit2=pmxa_restrictC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7pm_geomC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_ffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_s1C56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC56Stdlib6ZArith6BinInt1Z2leC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_loC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6wa_sp0C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC56Stdlib6ZArith6BinInt1Z2ltC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac:pmw_boundsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_consC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8wa_wordsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_nC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5xa_v1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB3lblC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_v1K47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission7LibCont4CRep4mdefK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission7LibCont4CRep3fldK47Corelib4Init9Datatypes4prod01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut>env_world_seedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9env_worldK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut:pm_kn_baseC47Corelib4Init9Datatypes3appK5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond06K47Corelib4Init9Datatypes4list02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut<regs_tbl_extC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6xboundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7tbl_okXC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut:tbl_closedC47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7keys_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut8fkeys_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut=pm_kn_base_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac<ev_world_allC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac6ev_addK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26adenotK46Stdlib9micromega=RingMicromega7Formula01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac8estart_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv@adenot_of_estartC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC56Stdlib6NArith6BinNat1N3lebC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC46Stdlib5Lists4List9nth_errorC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac8ev_xseedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue:sc_rd_fld8C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit:sym_insideC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC46Stdlib5Lists4List7forallbK47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit7fsh_patC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit6lbytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots9upd_slotsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots9add_slotsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut=sr_tbl_checkXC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9scal_noneC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K8tbl_subbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K8tbl_inclC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCutAregs_tbl_restrictC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sr_getC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3aC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3bC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3cC5ARocqVerifyHarness?AgentSubmission7LibCont4CRep8vec_opndC4ARocqVerifyHarness?AgentSubmission8LibIface4liveK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9wenv_valsC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac8pmk_sh_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_diagC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_userK46Stdlib9micromega5Tauto8GFormula03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac=pmk_sh_ffdisjC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6pm_runK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4O_V1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4AC_AC5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4LY_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4MI_AC5ARocqVerifyHarness?AgentSubmission7LibCont4CRep7OPND_SZC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7S_INSTRc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWX56TBL_X5c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWX54HHx5c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWX55RT_X5C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8S_MODULEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH8RT_EE648C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockC4ARocqVerifyHarness?AgentSubmission8LibIface3memI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase3pmc00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsK47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH9TBL_EE648C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AFS_HDRK47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5mulop01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00K47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI46Stdlib5Lists4List6Exists00K46Stdlib9micromega=RingMicromega3Op201C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4WV_PC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6PM_OWNC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut4FSHBC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7PM_OBJSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6PM_NSHC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5WV_S1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5WV_FF".
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
