(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Ox Require F06.
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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_ContStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmWXK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HWord HUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmS8a () := "C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<asan_rt_hypsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCasan_rt_hyps_bp_extC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceCalloc_ok_of_live_bpC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface9RHEAP_ahmC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_IfaceAannotate_gen_stmtC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface7cost_bpI47Corelib4Init5Logic3and00C47Corelib4Init5Logic5proj1I6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4pmwA00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn7pmw_okA00K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4prod00I6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5PMXAT00C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_trI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_blocksC46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC4ARocqVerifyHarness?AgentSubmission7FPSteps8frm_zeroC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9regs_tblXC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_gpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_tpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8wa_wordsC47Corelib4Init5Logic3notI47Corelib4Init9Datatypes6option00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_ffC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase6c_widxC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_nC56Stdlib6ZArith6BinInt1Z3subC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K7ffkeepXK47Corelib4Init9Datatypes4list02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7pm_geomC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_s1C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_loC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6wa_sp0C56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC56Stdlib6ZArith6BinInt1Z2ltC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn4wk_nK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05K47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut:pm_kn_baseC47Corelib4Init9Datatypes3appK5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K47Corelib4Init5Logic2eq01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut<regs_tbl_extC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6xboundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7tbl_okXK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut>env_world_seedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut:tbl_closedC47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7keys_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut8fkeys_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut=pm_kn_base_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac:pmw_boundsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_consC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac=pmk_scal_widxC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac<ev_world_allK46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac6ev_addC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac<pmw_apart_ffK46Stdlib9micromega5Tauto8GFormula07C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac>pmk_sh_fshdisjK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit:sym_insideC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC46Stdlib5Lists4List7forallbK47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit7fsh_patC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit6lbytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots9upd_slotsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlots9add_slotsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut=sr_tbl_checkXC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9scal_noneC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC47Corelib4Init5Logic8eq_ind_rC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCutAregs_tbl_restrictC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7xa_scalC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_icountC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_endianC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase9c_reqconvI47Corelib4Init5Logic2or00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH<regs_tbl_subC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9wenv_valsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue9rt_lookupC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue6rt_getC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6NArith6BinNat1N3lebC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC46Stdlib5Lists4List9nth_errorC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac8ev_xseedK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr05C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K8ev_idx4bC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sr_getC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWXK<ev_sub_normDC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut5ev_ffC45stdpp9bitvector;definitions;bv_unsignedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit9munch_symC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit8num_winsC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8srl3_valC47Corelib4Init5Logic6eq_indC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotI46Stdlib5Lists4List6Exists00K47Corelib4Init5Logic2or01K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init5Logic2or02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmU2K=ffkeepX_munchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6pm_runK45stdpp9bitvector;definitions2bv01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac8pmk_sh_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_diagC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_userK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes3sndI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL9TBL_EEF44K46Stdlib9micromega=RingMicromega3Op201C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockC4ARocqVerifyHarness?AgentSubmission8LibIface3memI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase3pmc00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00K47Corelib4Init9Datatypes3nat01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmOL6RT_ARMC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_ContStmt;MKSTR_ENTRYc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8a9RT_S8CALLC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AFS_HDRK47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5mulop01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8a3HHmC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4WV_PC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase6O_WIDXI5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmS8a;RT_PM_S8A_1I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00C5ARocqVerifyHarness?AgentSubmission6LibPrs6PrsInv;PARSER_SIZEI47Corelib4Init5Logic5False00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6PM_OWNC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut4FSHBC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7PM_OBJSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6PM_NSHC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5WV_S1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5WV_FFK46Stdlib9micromega:ZMicromega;ZArithProof01".

Definition RT_S8CALL : list (reg * expr) :=
  [(1%bv, ELit 990940); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 5936)); (13%bv, ELit 0);
   (19%bv, EAlu ALU_ADD (EVar 33) (ELit 5936)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880));
   (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Definition RT_PM_S8A_1 : list (reg * expr) := [(1%bv, ELit 990940); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 5936)); (13%bv, ELit 0); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 5936)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section S8a.
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

  Lemma HHm : asan_rt_hyps H.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmS8a ()) ["S8a"] "p;2p;1p;3g0000j27Tg0010j26Tg0029j12Tg003Bj21Tg004Aj15Tg005Hj13Tg006Ej20Tg006`j34Tp,5HCEILR0p,1HR1'71601%211101%50%31'0'0'0'0p,4HHbp34o"). Qed.

  Lemma pm_s8a : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1e48) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    wa_words w <> 0 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 MKSTR_ENTRY) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_S8CALL -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf1edc -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_ff w + 5936) -> PropExec.getr R1 11%bv = Z_to_bv 64 (wa_words w + 4 * c_widx c) -> PropExec.getr R1 12%bv = Z_to_bv 64 (wa_n w - c_widx c) -> PropExec.getr R1 13%bv = Z_to_bv 64 0 -> PropExec.getr R1 21%bv = Z_to_bv 64 (wa_n w - c_widx c) -> ffkeepX w [] m m1 -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HW KC.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (SC1 & SC2 & SC3).
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 (c_widx c)]
          [KWord (SA (EVar WV_P) O_WIDX) 8 (EVar 41)] 100%nat [MKSTR_ENTRY] [false; false; false] 42%N
          [3; 4; 24; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8A_1.
    { pose proof (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 (c_widx c)])) as (S32 & S33 & S34 & S35 & S36 & S37 & _).
      assert (S41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 (c_widx c)])) (EVar 41) = Z_to_bv 64 (c_widx c)) by reflexivity.
      set (E := Eseed R (wenv_vals w ++ [Z_to_bv 64 (c_widx c)])) in *.
      assert (EM4 : edenot E (EMd M_MUL (ELit 4) (EVar 41)) = Z_to_bv 64 (4 * c_widx c)).
      { change (mul_div M_MUL (Z_to_bv 64 4) (edenot E (EVar 41)) = Z_to_bv 64 (4 * c_widx c)). rewrite S41. apply HLib.w_mul; lia. }
      assert (EW : edenot E (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 41))) = Z_to_bv 64 (wa_words w + 4 * c_widx c)).
      { change (alu64 ALU_ADD (edenot E (EVar 36)) (edenot E (EMd M_MUL (ELit 4) (EVar 41))) = Z_to_bv 64 (wa_words w + 4 * c_widx c)).
        rewrite S36, EM4. apply HLib.w_add; lia. }
      assert (EA : edenot E (EAlu ALU_ADD (EVar 41) (ELit 2305843009213693952)) = Z_to_bv 64 (c_widx c + 2305843009213693952)).
      { change (alu64 ALU_ADD (edenot E (EVar 41)) (Z_to_bv 64 2305843009213693952) = Z_to_bv 64 (c_widx c + 2305843009213693952)).
        rewrite S41. apply HLib.w_add; lia. }
      assert (EL1 : edenot E (EAlu ALU_SLTU (ELit 0) (EVar 36)) = Z_to_bv 64 1).
      { change (alu64 ALU_SLTU (Z_to_bv 64 0) (edenot E (EVar 36)) = Z_to_bv 64 1).
        rewrite S36, w_sltu by lia. replace (0 <? wa_words w) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
      assert (EL2 : edenot E (EAlu ALU_SLTU (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 41))) (ELit 1)) = Z_to_bv 64 0).
      { change (alu64 ALU_SLTU (edenot E (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 41)))) (Z_to_bv 64 1) = Z_to_bv 64 0).
        rewrite EW, w_sltu by lia. replace (wa_words w + 4 * c_widx c <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
      - cbn [sc_denot]. rewrite EW, S36, HLib.br_ltu by lia. apply Z.ltb_ge; lia.
      - cbn [sc_denot].
        change (edenot E (EAlu ALU_SRL (EAlu ALU_ADD (EVar 41) (ELit 2305843009213693952)) (ELit 62)))
          with (alu64 ALU_SRL (edenot E (EAlu ALU_ADD (EVar 41) (ELit 2305843009213693952))) (Z_to_bv 64 62)).
        rewrite EA, w_srl by lia. rewrite Z.div_small by lia. change (edenot E (ELit 0)) with (Z_to_bv 64 0).
        rewrite HLib.br_ne by lia. reflexivity.
      - cbn [sc_denot]. rewrite EL1, EL2, HLib.br_eq by lia. reflexivity. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] [Z_to_bv 64 (c_widx c)] R1 RT_PM_S8A_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 (c_widx c)])) as TEF1. change (EVar WV_FF) with (EVar 33%N) in TEF1.
    destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 (c_widx c)])) as (TEA1 & TEB1 & TEC1 & TED1 & TEE1 & TEG1 & _).
    assert (TFK1 : ffkeepX w [] m M1).
    { pose proof (munch_sym (Eseed R (wenv_vals w ++ [Z_to_bv 64 (c_widx c)])) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147451622, 2147451625)] Hlf1 ltac:(vm_compute; reflexivity)) as TMU. cbn [num_wins map] in TMU.
      rewrite ?(srl3_val _ (EVar 33) (wa_ff w) TEB1 ltac:(lia)) in TMU.
      apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)).
      repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia | (destruct Q6 as [Q6'|Q6']; [left | right; left]; unfold SHBASE in *; lia) | right; right; apply Exists_cons_hd; cbn [fst snd]; lia] |]); apply Forall_nil. }
    replace (s_pc SSr) with MKSTR_ENTRY in VIS1 by reflexivity.
    eapply (KC msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8CALL HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1).
    all: try first [ rtf HT1 | exact TFK1
            | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 22%bv) | rewrite (HR1 25%bv)]; reflexivity)
            | (rewrite (HR1 _); cbn [sr_get s_regs nth]; first [reflexivity | (eapply ev_add; [reflexivity | lia | lia]) | (cbn [edenot]; ev_xs; rewrite ?TEE1, ?TEG1; first [reflexivity | (rewrite u64_of_Z by lia; reflexivity) | (rewrite ?w_add, ?w_mul by lia; f_equal; lia)])]) ].
    all: rewrite (HR1 _); cbn [sr_get s_regs nth];
      first [ apply (ev_idx4b _ 36 41 (wa_words w) (c_widx c)); [exact TEE1 | reflexivity | lia | lia | lia]
            | apply (ev_sub_normD _ 37 41 (wa_n w) (c_widx c)); [exact TEG1 | reflexivity | lia | lia] ].
  Qed.

End S8a.
