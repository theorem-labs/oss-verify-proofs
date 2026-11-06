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

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_ContStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmWXK LbB_PmS8K LbB_PmU6K.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmS8b () := "C69OSSVerify5KrLib3bpB2Rt7BsIface<asan_rt_hypsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_IfaceCasan_rt_hyps_bp_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_IfaceCalloc_ok_of_live_bpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_Iface9RHEAP_ahmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_IfaceAannotate_gen_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt9RtB_Iface7cost_bpC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic5proj1I69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4pmwA00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5as_StC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI69OSSVerify5KrLib3bpB3Lib9LbB_PmOwn7pmw_okA00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5PMXAT00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase8c_blocksC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib3bpB2Rt7BsIface8as_AKRELC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface6as_VISC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C79OSSVerify5KrLib3bpB2HF3Lib:BLPropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BMState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib3bpB3Lib:LbB_Bridge5rfullC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7FPSteps8frm_zeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut9regs_tblXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_gpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_ffC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC79OSSVerify5KrLib3bpB2HF3Lib4BacX2b8C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4wa_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase6c_widxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init5Logic3notI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z3divK79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmU2K7ffkeepXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7pm_geomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_s1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow5aceilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt8BsShadow2shC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase6wa_sp0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib3bpB2Rt8BsShadow;aceil_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF8BeapCeil5hceilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib3bpB3Lib9LbB_PmOwn4wk_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7xa_scalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase8c_icountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase8c_endianC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase9c_reqconvC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut>env_world_seedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut5ev_ffC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C59OSSVerify5KrLib8SymExec33SX26a_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S6estartC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K5w1_b8C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib8SymExec33SX26edenotC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib3bpB2HF3Lib6BCells6cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_ConvAkword_of_rw_cellsC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib=SymExec3Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26sentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec33SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX29sym_state01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut:pm_kn_baseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK59OSSVerify5KrLib8SymExec33SX27scripts01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX28sidecond01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut<regs_tbl_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut6xboundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7tbl_okXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7LibHash4HLib3srsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX28sym_execC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC69OSSVerify5KrLib3bpB3Lib9LbB_PmCut:tbl_closedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7keys_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut8fkeys_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut=pm_kn_base_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib=SymExec3Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K9even2_modC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem<branch_takenC69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K=sc_b0_long_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K8sc_op_neC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K9even2_divC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K<sc_len_shortC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K=sc_b0_long_neC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_FKit:sym_insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25s_logC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC69OSSVerify5KrLib3bpB3Lib8LbB_FKit7fsh_patC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_FKit6lbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_FSlots9upd_slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_FSlots9add_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut=sr_tbl_checkXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut9scal_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26sr_getC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCutAregs_tbl_restrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut5ev_s1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac<ev_world_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4wa_pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase8wa_wordsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7wa_consC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7wa_userC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7wa_diagC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib3bpB3Lib9LbB_PmTac:pmw_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib8u64_of_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac<pmw_apart_ffC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_FKit9munch_symC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_FKit8num_winsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib7LbB_Kit8srl3_valC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib3bpB3Lib8LbB_Conv?wmono_mem_denotC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K46Stdlib5Lists4List6Exists01K46Stdlib5Lists4List6Exists02C69OSSVerify5KrLib3bpB3Lib9LbB_PmU2K=ffkeepX_munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib6BCells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmU2K<ffkeepX_cellC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase6xa_fwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface3fszC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib4BMem5wr_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib4BMem2waC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC46Stdlib5Lists4List=Forall_forallC59OSSVerify5KrLib8SymExec33SX26e_addrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses7rew_iffC79OSSVerify5KrLib3bpB2HF3Lib4BMem3le2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K8ev_s8_nwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_Conv@rw_cells_log_nthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmLH<regs_tbl_subC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib3bpB2HF3Lib5BStep8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5as_SRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase9wenv_valsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib5EseedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init9Datatypes3sndC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib8SymExec33SX27e_widthC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut6pm_runC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib4Init5Logic4True01I79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt5BSegs5asegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib3bpB3Lib7LbB_Kit6SHBASEC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00I59OSSVerify5KrLib8SymExec33SX26kentry00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib8SymExec33SX26sentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c69OSSVerify5KrLib3bpB3Lib9LbB_PmS8b3HHmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmOL9TBL_EEF44C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K6RT_S8BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_PmS8b<HTLbAPmS8b_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_PmS8b>RT_PM_S8B_SP_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5blockC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface3memC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I59OSSVerify5KrLib6LibPrs6PmBase3pmc00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I47Corelib4Init5Logic4True00C69OSSVerify5KrLib3bpB3Lib8LbB_PmOL8OL_PUSHKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase6S_OPERC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_PmOL8RT_PUSHKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt5BSegs8AIMG_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface7AFS_HDRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5WV_FFC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5mulop01I59OSSVerify5KrLib8SymExec33SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I59OSSVerify5KrLib8SymExec33SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25sr_idC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut6PM_OWNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut4FSHBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7PM_OBJSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase6PM_NSHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5WV_S1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PrsInv;PARSER_SIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib;LbB_PrsStmt9PM_FCLASSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K8s8b_winsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BLFrame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC69OSSVerify5KrLib3bpB3Lib:LbB_PmGlue9rt_lookupC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmGlue6rt_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac6ev_addC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_PmS8b>RT_PM_S8B_SI_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_TablStmtBAT_IMPORT_TYPE_GETC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K5S_STRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K6RT_S8CC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_PmS8b>RT_PM_S8B_SX_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib<LbB_DiagStmt:AEXHAUSTEDC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF3Lib6BCells4cell01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib4BMem3le8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K:sc_size_neC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_PmS8b>RT_PM_S8B_LX_1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K;sc_size_geuC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K9ev_s8_nwlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_PmS8b>RT_PM_S8B_LI_1C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06C56Stdlib6ZArith6BinInt1Z6ltb_gec69OSSVerify5KrLib3bpB3Lib9LbB_PmS8b>RT_PM_S8B_LG_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib9LbB_PmS8b>RT_PM_S8B_LQ_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmS8K7RT_S8D1C1?~~~~~~~~~~~~~~~".

Definition RT_PM_S8B_SP_1 : list (reg * expr) := [(1%bv, ELit 990940); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 0); (11%bv, ELit 11); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 1); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8B_SI_1 : list (reg * expr) := [(1%bv, ELit 995800); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 5937)); (11%bv, ELit 11); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8B_SX_1 : list (reg * expr) := [(1%bv, ELit 994796); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EVar 32); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8B_LX_1 : list (reg * expr) := [(1%bv, ELit 994796); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EVar 32); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8B_LI_1 : list (reg * expr) := [(1%bv, ELit 995800); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (11%bv, ELit 262140); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8B_LG_1 : list (reg * expr) := [(1%bv, ELit 990940); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (11%bv, ELit 262140); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8B_LQ_1 : list (reg * expr) := [(1%bv, ELit 990940); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 11); (11%bv, ELit 262140); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 1); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section S8b.
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
ltac2:(KReplay.run1 (kr_t_LbB_PmS8b ()) ["S8b"] "p;2p;1p;3g0000j27Tg0010j26Tg0029j12Tg003Bj21Tg004Aj15Tg005Hj13Tg006Ej20Tg006`j34Tp,5HCEILR0p,1HR1'71601%211101%50%31'0'0'0'0p,4HHbp34o"). Qed.

  Ltac s8b_close :=
    rewrite ?even2_mod, ?even2_div;
    first [ reflexivity
          | (apply Z.eqb_eq; lia) | (apply Z.eqb_neq; lia)
          | (apply negb_true_iff; apply Z.eqb_neq; lia) | (apply negb_false_iff; apply Z.eqb_eq; lia)
          | (apply negb_true_iff; apply Z.ltb_ge; lia) | (apply negb_false_iff; apply Z.ltb_lt; lia) ].

  Ltac s8b_fk Q6 :=
    repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia
              | (destruct Q6 as [Q6'|Q6']; [left | right; left]; unfold SHBASE in *; lia)
              | right; right; first [apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; lia]] |]);
    apply Forall_nil.

  Ltac s8b_kept HR1 :=
    intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 22%bv) | rewrite (HR1 25%bv)]; reflexivity.

  Lemma pm_s8b_sp : forall (w : pmwA H) s LB LBs m mo c msF R F fc (len op : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1edc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8B -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 (2 * len))] ->
    0 <= len <= 22 ->
    PropExec.getr R 21%bv = Z_to_bv 64 (wa_n w - c_widx c) ->
    PropExec.getr R 22%bv = Z_to_bv 64 op ->
    0 <= op < 2 ^ 16 ->
    4 * (wa_n w - c_widx c) <> len ->
    op <> 11 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 OL_PUSHK) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c S_OPER TBL_EEF44 [] -> regs_tbl w R1 RT_PUSHK -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> rw_cells asegs m1 (wa_ff w + 114) [C2 (Z_to_bv 64 (len / 4 + 1))] -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 11)] -> ffkeepX w [(116, 4); (114, 2)] m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc len op Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HB0 HLEN G21 G22 HOP HNE HOP11 KC.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (SC1 & SC2 & SC3).
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2.
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 (2 * len)])) as EF.
    pose proof EF as TEF. change (EVar WV_FF) with (EVar 33%N) in TEF.
    destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 (2 * len)])) as (TEA & TEB & _).
    assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 (2 * len)])) (EVar 41) = Z_to_bv 64 (2 * len)) by reflexivity.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 (2 * len)])) m [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41)]).
    { apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C1 (b8 (2 * len))));
        [exact HB0 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; symmetry; apply w1_b8; lia]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 (2 * len)]
          [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41)] HK1 200%nat [OL_PUSHK] [false; false; true; true] 42%N
          S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8B_SP_1.
    { set (E := Eseed R (wenv_vals w ++ [Z_to_bv 64 (2 * len)])) in *.
      assert (E21 : edenot E (EVar 21) = Z_to_bv 64 (wa_n w - c_widx c)) by exact G21.
      assert (E22 : edenot E (EVar 22) = Z_to_bv 64 op) by exact G22.
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
      all: cbn [sc_denot];
        first [ rewrite (sc_b0_long_eq E 41 (2 * len) E41 ltac:(lia))
              | rewrite (sc_b0_long_ne E 41 (2 * len) E41 ltac:(lia))
              | rewrite (sc_op_ne E 22 op 11 E22 ltac:(lia) ltac:(lia))
              | rewrite (sc_len_short E 41 21 (2 * len) (wa_n w - c_widx c) E41 ltac:(lia) E21 ltac:(lia)) ];
        s8b_close. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] [Z_to_bv 64 (2 * len)] R1 RT_PM_S8B_SP_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (munch_sym (Eseed R (wenv_vals w ++ [Z_to_bv 64 (2 * len)])) m (s_log SSr)
                  [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928); (EVar 33, 116, 120); (EVar 33, 114, 116)]
                  Hlf1 ltac:(vm_compute; reflexivity)) as TMU.
    cbn [num_wins map] in TMU. rewrite ?(srl3_val _ (EVar 33) (wa_ff w) TEB ltac:(lia)), ?TEF in TMU.
    assert (TFK : ffkeepX w [(116, 4); (114, 2)] m M1).
    { apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)). s8b_fk Q6. }
    assert (RW116 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 11)]).
    { subst M1. eapply (rw_cells_log_nth_ff H w _ m _ 3%nat 116 4 _ _ OK (env_world_seed H w R [Z_to_bv 64 (2 * len)]));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | lia | cbn [Z.of_nat]; lia
        | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 116 + i) with (wa_ff w + (116 + i)) by lia; apply FW2; lia
        | reflexivity | exact Logic.I | reflexivity ]. }
    assert (RW114 : rw_cells asegs M1 (wa_ff w + 114) [C2 (Z_to_bv 64 (len / 4 + 1))]).
    { subst M1. eapply (rw_cells_log_nth_ff H w _ m _ 4%nat 114 2 _ _ OK (env_world_seed H w R [Z_to_bv 64 (2 * len)]));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | lia | cbn [Z.of_nat]; lia
        | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 114 + i) with (wa_ff w + (114 + i)) by lia; apply FW2; lia
        | reflexivity | exact Logic.I
        | cbn [cbytes]; rewrite (ev_s8_nw _ 41 (2 * len) E41 ltac:(lia)), even2_div; reflexivity ]. }
    replace (s_pc SSr) with OL_PUSHK in VIS1 by reflexivity.
    eapply (KC msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_PUSHK HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1).
    all: first [ exact RW114 | exact RW116 | exact TFK | s8b_kept HR1 ].
  Qed.

  Lemma pm_s8b_si : forall (w : pmwA H) s LB LBs m mo c msF R F fc (len op : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1edc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8B -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 (2 * len))] ->
    0 <= len <= 22 ->
    PropExec.getr R 21%bv = Z_to_bv 64 (wa_n w - c_widx c) ->
    PropExec.getr R 22%bv = Z_to_bv 64 op ->
    0 <= op < 2 ^ 16 ->
    4 * (wa_n w - c_widx c) <> len ->
    op = 11 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_IMPORT_TYPE_GET) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c S_STR TBL_EEF44 [] -> regs_tbl w R1 RT_S8C -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf31d8 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 8%bv = Z_to_bv 64 (wa_sp0 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_ff w + 5937) -> rw_cells asegs m1 (wa_ff w + 114) [C2 (Z_to_bv 64 (len / 4 + 1))] -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 11)] -> ffkeepX w [(116, 4); (114, 2)] m m1 -> munch (s8b_wins (wa_ff w)) m m1 -> wmono asegs m m1 -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc len op Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HB0 HLEN G21 G22 HOP HNE HOP11 KC.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (SC1 & SC2 & SC3).
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2.
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 (2 * len)])) as EF.
    pose proof EF as TEF. change (EVar WV_FF) with (EVar 33%N) in TEF.
    destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 (2 * len)])) as (TEA & TEB & _).
    assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 (2 * len)])) (EVar 41) = Z_to_bv 64 (2 * len)) by reflexivity.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 (2 * len)])) m [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41)]).
    { apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C1 (b8 (2 * len))));
        [exact HB0 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; symmetry; apply w1_b8; lia]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 (2 * len)]
          [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41)] HK1 200%nat [AT_IMPORT_TYPE_GET] [false; false; false] 42%N
          S_STR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8B_SI_1.
    { set (E := Eseed R (wenv_vals w ++ [Z_to_bv 64 (2 * len)])) in *.
      assert (E21 : edenot E (EVar 21) = Z_to_bv 64 (wa_n w - c_widx c)) by exact G21.
      assert (E22 : edenot E (EVar 22) = Z_to_bv 64 op) by exact G22.
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
      all: cbn [sc_denot];
        first [ rewrite (sc_b0_long_ne E 41 (2 * len) E41 ltac:(lia))
              | rewrite (sc_op_ne E 22 op 11 E22 ltac:(lia) ltac:(lia))
              | rewrite (sc_len_short E 41 21 (2 * len) (wa_n w - c_widx c) E41 ltac:(lia) E21 ltac:(lia)) ];
        s8b_close. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] [Z_to_bv 64 (2 * len)] R1 RT_PM_S8B_SI_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (munch_sym (Eseed R (wenv_vals w ++ [Z_to_bv 64 (2 * len)])) m (s_log SSr)
                  [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928); (EVar 33, 116, 120); (EVar 33, 114, 116)]
                  Hlf1 ltac:(vm_compute; reflexivity)) as TMU.
    cbn [num_wins map] in TMU. rewrite ?(srl3_val _ (EVar 33) (wa_ff w) TEB ltac:(lia)), ?TEF in TMU.
    assert (TFK : ffkeepX w [(116, 4); (114, 2)] m M1).
    { apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)). s8b_fk Q6. }
    assert (RW116 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 11)]).
    { subst M1. eapply (rw_cells_log_nth_ff H w _ m _ 0%nat 116 4 _ _ OK (env_world_seed H w R [Z_to_bv 64 (2 * len)]));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | lia | cbn [Z.of_nat]; lia
        | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 116 + i) with (wa_ff w + (116 + i)) by lia; apply FW2; lia
        | reflexivity | exact Logic.I | reflexivity ]. }
    assert (RW114 : rw_cells asegs M1 (wa_ff w + 114) [C2 (Z_to_bv 64 (len / 4 + 1))]).
    { subst M1. eapply (rw_cells_log_nth_ff H w _ m _ 1%nat 114 2 _ _ OK (env_world_seed H w R [Z_to_bv 64 (2 * len)]));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | lia | cbn [Z.of_nat]; lia
        | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 114 + i) with (wa_ff w + (114 + i)) by lia; apply FW2; lia
        | reflexivity | exact Logic.I
        | cbn [cbytes]; rewrite (ev_s8_nw _ 41 (2 * len) E41 ltac:(lia)), even2_div; reflexivity ]. }
    replace (s_pc SSr) with AT_IMPORT_TYPE_GET in VIS1 by reflexivity.
    eapply (KC msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8C HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1).
    all: first [ rtf HT1 | exact RW114 | exact RW116 | exact TFK | exact TMU | exact (wmono_mem_denot _ _ _) | s8b_kept HR1 ].
  Qed.

  Lemma pm_s8b_sx : forall (w : pmwA H) s LB LBs m mo c msF R F fc (len op : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1edc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8B -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 (2 * len))] ->
    0 <= len <= 22 ->
    PropExec.getr R 21%bv = Z_to_bv 64 (wa_n w - c_widx c) ->
    PropExec.getr R 22%bv = Z_to_bv 64 op ->
    0 <= op < 2 ^ 16 ->
    4 * (wa_n w - c_widx c) = len ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AEXHAUSTED) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c S_STR TBL_EEF44 [] -> regs_tbl w R1 RT_S8C -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf2dec -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 8%bv = Z_to_bv 64 (wa_sp0 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_p w) -> PropExec.getr R1 11%bv = PropExec.getr R 25%bv -> PropExec.getr R1 12%bv = PropExec.getr R 22%bv -> PropExec.getr R1 13%bv = PropExec.getr R 18%bv -> m1 = m -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc len op Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HB0 HLEN G21 G22 HOP HEQ KC.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (SC1 & SC2 & SC3).
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 (2 * len)])) as EF.
    assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 (2 * len)])) (EVar 41) = Z_to_bv 64 (2 * len)) by reflexivity.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 (2 * len)])) m [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41)]).
    { apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C1 (b8 (2 * len))));
        [exact HB0 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; symmetry; apply w1_b8; lia]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 (2 * len)]
          [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41)] HK1 200%nat [AEXHAUSTED] [false; true] 42%N
          S_STR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8B_SX_1.
    { set (E := Eseed R (wenv_vals w ++ [Z_to_bv 64 (2 * len)])) in *.
      assert (E21 : edenot E (EVar 21) = Z_to_bv 64 (wa_n w - c_widx c)) by exact G21.
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      all: cbn [sc_denot];
        first [ rewrite (sc_b0_long_ne E 41 (2 * len) E41 ltac:(lia))
              | rewrite (sc_len_short E 41 21 (2 * len) (wa_n w - c_widx c) E41 ltac:(lia) E21 ltac:(lia)) ];
        s8b_close. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] [Z_to_bv 64 (2 * len)] R1 RT_PM_S8B_SX_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with AEXHAUSTED in VIS1 by reflexivity.
    eapply (KC msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8C HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1).
    all: first [ rtf HT1 | reflexivity | s8b_kept HR1 | (rewrite (HR1 _); cbn [sr_get s_regs nth]; reflexivity) ].
  Qed.

  Lemma pm_s8b_lx : forall (w : pmwA H) s LB LBs m mo c msF R F fc (b0 sz cp dp op : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1edc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8B -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] ->
    0 <= b0 < 256 /\ b0 mod 2 = 1 ->
    rw_cells asegs m (wa_ff w + 5944) [C8 (Z_to_bv 64 sz)] ->
    0 <= sz < 2 ^ 28 ->
    rw_cells asegs m (wa_ff w + 5936) [C8 (Z_to_bv 64 cp)] ->
    rw_cells asegs m (wa_ff w + 5952) [C8 (Z_to_bv 64 dp)] ->
    0 <= dp < 2 ^ 64 ->
    PropExec.getr R 21%bv = Z_to_bv 64 (wa_n w - c_widx c) ->
    PropExec.getr R 22%bv = Z_to_bv 64 op ->
    0 <= op < 2 ^ 16 ->
    sz = 4 * (wa_n w - c_widx c) ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AEXHAUSTED) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c S_STR TBL_EEF44 [] -> regs_tbl w R1 RT_S8C -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf2dec -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 8%bv = Z_to_bv 64 (wa_sp0 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_p w) -> PropExec.getr R1 11%bv = PropExec.getr R 25%bv -> PropExec.getr R1 12%bv = PropExec.getr R 22%bv -> PropExec.getr R1 13%bv = PropExec.getr R 18%bv -> m1 = m -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc b0 sz cp dp op Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0
           HB0 HB0R HSZ HSZR HCP HDP HDPR G21 G22 HOP HEQ KC.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (SC1 & SC2 & SC3).
    destruct HB0R as [HB0a HB0b].
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) as EF.
    assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 41) = Z_to_bv 64 b0) by reflexivity.
    assert (E42 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 42) = Z_to_bv 64 sz) by reflexivity.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) m
                    [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5944) 8 (EVar 42)]).
    { apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C1 (b8 b0)));
          [exact HB0 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; symmetry; apply w1_b8; lia].
      - eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5944) _ 0%nat (C8 (Z_to_bv 64 sz)));
          [exact HSZ | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E42; reflexivity]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp]
          [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5944) 8 (EVar 42)] HK1 200%nat [AEXHAUSTED] [true; false] 45%N
          S_STR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8B_LX_1.
    { set (E := Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) in *.
      assert (E21 : edenot E (EVar 21) = Z_to_bv 64 (wa_n w - c_widx c)) by exact G21.
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      all: cbn [sc_denot];
        first [ rewrite (sc_b0_long_ne E 41 b0 E41 HB0a)
              | rewrite (sc_size_ne E 42 21 sz (wa_n w - c_widx c) E42 ltac:(lia) E21 ltac:(lia)) ];
        s8b_close. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp] R1 RT_PM_S8B_LX_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with AEXHAUSTED in VIS1 by reflexivity.
    eapply (KC msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8C HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1).
    all: first [ rtf HT1 | reflexivity | s8b_kept HR1 | (rewrite (HR1 _); cbn [sr_get s_regs nth]; reflexivity) ].
  Qed.

  Lemma pm_s8b_li : forall (w : pmwA H) s LB LBs m mo c msF R F fc (b0 sz cp dp op : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1edc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8B -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] ->
    0 <= b0 < 256 /\ b0 mod 2 = 1 ->
    rw_cells asegs m (wa_ff w + 5944) [C8 (Z_to_bv 64 sz)] ->
    0 <= sz < 2 ^ 28 ->
    rw_cells asegs m (wa_ff w + 5936) [C8 (Z_to_bv 64 cp)] ->
    rw_cells asegs m (wa_ff w + 5952) [C8 (Z_to_bv 64 dp)] ->
    0 <= dp < 2 ^ 64 ->
    PropExec.getr R 21%bv = Z_to_bv 64 (wa_n w - c_widx c) ->
    PropExec.getr R 22%bv = Z_to_bv 64 op ->
    0 <= op < 2 ^ 16 ->
    sz <> 4 * (wa_n w - c_widx c) ->
    sz < 262140 ->
    op = 11 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_IMPORT_TYPE_GET) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c S_STR TBL_EEF44 [] -> regs_tbl w R1 RT_S8C -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf31d8 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 8%bv = Z_to_bv 64 (wa_sp0 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 dp -> rw_cells asegs m1 (wa_ff w + 114) [C2 (Z_to_bv 64 (sz / 4 + 1))] -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 11)] -> ffkeepX w [(116, 4); (114, 2)] m m1 -> munch (s8b_wins (wa_ff w)) m m1 -> wmono asegs m m1 -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc b0 sz cp dp op Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0
           HB0 HB0R HSZ HSZR HCP HDP HDPR G21 G22 HOP HNE HLT HOP11 KC.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (SC1 & SC2 & SC3).
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2.
    destruct HB0R as [HB0a HB0b].
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) as EF.
    pose proof EF as TEF. change (EVar WV_FF) with (EVar 33%N) in TEF.
    destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) as (TEA & TEB & _).
    assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 41) = Z_to_bv 64 b0) by reflexivity.
    assert (E42 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 42) = Z_to_bv 64 sz) by reflexivity.
    assert (E44 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 44) = Z_to_bv 64 dp) by reflexivity.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) m
                    [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5944) 8 (EVar 42); KWord (SA (EVar WV_FF) 5952) 8 (EVar 44)]).
    { apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
      - eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C1 (b8 b0)));
          [exact HB0 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; symmetry; apply w1_b8; lia].
      - eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5944) _ 0%nat (C8 (Z_to_bv 64 sz)));
          [exact HSZ | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E42; reflexivity].
      - eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5952) _ 0%nat (C8 (Z_to_bv 64 dp)));
          [exact HDP | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E44; reflexivity]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp]
          [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5944) 8 (EVar 42); KWord (SA (EVar WV_FF) 5952) 8 (EVar 44)] HK1
          200%nat [AT_IMPORT_TYPE_GET] [true; true; false; false] 45%N
          S_STR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8B_LI_1.
    { set (E := Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) in *.
      assert (E21 : edenot E (EVar 21) = Z_to_bv 64 (wa_n w - c_widx c)) by exact G21.
      assert (E22 : edenot E (EVar 22) = Z_to_bv 64 op) by exact G22.
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
      all: cbn [sc_denot];
        first [ rewrite (sc_b0_long_ne E 41 b0 E41 HB0a)
              | rewrite (sc_op_ne E 22 op 11 E22 ltac:(lia) ltac:(lia))
              | rewrite (sc_size_ne E 42 21 sz (wa_n w - c_widx c) E42 ltac:(lia) E21 ltac:(lia))
              | rewrite (sc_size_geu E 42 sz 262140 E42 ltac:(lia) ltac:(lia)) ];
        s8b_close. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp] R1 RT_PM_S8B_LI_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (munch_sym (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) m (s_log SSr)
                  [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928); (EVar 33, 116, 120); (EVar 33, 114, 116)]
                  Hlf1 ltac:(vm_compute; reflexivity)) as TMU.
    cbn [num_wins map] in TMU. rewrite ?(srl3_val _ (EVar 33) (wa_ff w) TEB ltac:(lia)), ?TEF in TMU.
    assert (TFK : ffkeepX w [(116, 4); (114, 2)] m M1).
    { apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)). s8b_fk Q6. }
    assert (RW116 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 11)]).
    { subst M1. eapply (rw_cells_log_nth_ff H w _ m _ 0%nat 116 4 _ _ OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp]));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | lia | cbn [Z.of_nat]; lia
        | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 116 + i) with (wa_ff w + (116 + i)) by lia; apply FW2; lia
        | reflexivity | exact Logic.I | reflexivity ]. }
    assert (RW114 : rw_cells asegs M1 (wa_ff w + 114) [C2 (Z_to_bv 64 (sz / 4 + 1))]).
    { subst M1. eapply (rw_cells_log_nth_ff H w _ m _ 1%nat 114 2 _ _ OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp]));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | lia | cbn [Z.of_nat]; lia
        | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 114 + i) with (wa_ff w + (114 + i)) by lia; apply FW2; lia
        | reflexivity | exact Logic.I
        | cbn [cbytes]; rewrite (ev_s8_nwl _ 42 sz E42 ltac:(lia)); reflexivity ]. }
    replace (s_pc SSr) with AT_IMPORT_TYPE_GET in VIS1 by reflexivity.
    eapply (KC msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8C HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1).
    all: first [ rtf HT1 | exact RW114 | exact RW116 | exact TFK | exact TMU | exact (wmono_mem_denot _ _ _) | s8b_kept HR1
               | (rewrite (HR1 _); cbn [sr_get s_regs nth]; reflexivity) ].
  Qed.

  Lemma pm_s8b_lg : forall (w : pmwA H) s LB LBs m mo c msF R F fc (b0 sz cp dp op : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1edc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8B -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] ->
    0 <= b0 < 256 /\ b0 mod 2 = 1 ->
    rw_cells asegs m (wa_ff w + 5944) [C8 (Z_to_bv 64 sz)] ->
    0 <= sz < 2 ^ 28 ->
    rw_cells asegs m (wa_ff w + 5936) [C8 (Z_to_bv 64 cp)] ->
    rw_cells asegs m (wa_ff w + 5952) [C8 (Z_to_bv 64 dp)] ->
    0 <= dp < 2 ^ 64 ->
    PropExec.getr R 21%bv = Z_to_bv 64 (wa_n w - c_widx c) ->
    PropExec.getr R 22%bv = Z_to_bv 64 op ->
    0 <= op < 2 ^ 16 ->
    sz <> 4 * (wa_n w - c_widx c) ->
    262140 <= sz ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf36a4) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c S_STR TBL_EEF44 [] -> regs_tbl w R1 RT_S8C -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = Z_to_bv 64 (sz / 4 + 1) -> m1 = m -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc b0 sz cp dp op Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0
           HB0 HB0R HSZ HSZR HCP HDP HDPR G21 G22 HOP HNE HGE KC.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (SC1 & SC2 & SC3).
    destruct HB0R as [HB0a HB0b].
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) as EF.
    assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 41) = Z_to_bv 64 b0) by reflexivity.
    assert (E42 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 42) = Z_to_bv 64 sz) by reflexivity.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) m
                    [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5944) 8 (EVar 42)]).
    { apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C1 (b8 b0)));
          [exact HB0 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; symmetry; apply w1_b8; lia].
      - eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5944) _ 0%nat (C8 (Z_to_bv 64 sz)));
          [exact HSZ | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E42; reflexivity]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp]
          [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5944) 8 (EVar 42)] HK1 200%nat [0xf36a4] [true; true; true] 45%N
          S_STR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8B_LG_1.
    { set (E := Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) in *.
      assert (E21 : edenot E (EVar 21) = Z_to_bv 64 (wa_n w - c_widx c)) by exact G21.
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
      all: cbn [sc_denot];
        first [ rewrite (sc_b0_long_ne E 41 b0 E41 HB0a)
              | rewrite (sc_size_ne E 42 21 sz (wa_n w - c_widx c) E42 ltac:(lia) E21 ltac:(lia))
              | rewrite (sc_size_geu E 42 sz 262140 E42 ltac:(lia) ltac:(lia)) ];
        s8b_close. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp] R1 RT_PM_S8B_LG_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with 0xf36a4 in VIS1 by reflexivity.
    eapply (KC msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8C HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1).
    all: first [ reflexivity | s8b_kept HR1
               | (rewrite (HR1 _); cbn [sr_get s_regs nth]; apply (ev_s8_nwl _ 42 sz E42 ltac:(lia))) ].
  Qed.

  Lemma pm_s8b_lq : forall (w : pmwA H) s LB LBs m mo c msF R F fc (b0 sz cp dp op : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1edc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8B -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] ->
    0 <= b0 < 256 /\ b0 mod 2 = 1 ->
    rw_cells asegs m (wa_ff w + 5944) [C8 (Z_to_bv 64 sz)] ->
    0 <= sz < 2 ^ 28 ->
    rw_cells asegs m (wa_ff w + 5936) [C8 (Z_to_bv 64 cp)] ->
    rw_cells asegs m (wa_ff w + 5952) [C8 (Z_to_bv 64 dp)] ->
    0 <= dp < 2 ^ 64 ->
    PropExec.getr R 21%bv = Z_to_bv 64 (wa_n w - c_widx c) ->
    PropExec.getr R 22%bv = Z_to_bv 64 op ->
    0 <= op < 2 ^ 16 ->
    sz <> 4 * (wa_n w - c_widx c) ->
    sz < 262140 ->
    op <> 11 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf4164) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c S_STR TBL_EEF44 [] -> regs_tbl w R1 RT_S8D1 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> rw_cells asegs m1 (wa_ff w + 114) [C2 (Z_to_bv 64 (sz / 4 + 1))] -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 11)] -> ffkeepX w [(116, 4); (114, 2)] m m1 -> munch (s8b_wins (wa_ff w)) m m1 -> wmono asegs m m1 -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc b0 sz cp dp op Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0
           HB0 HB0R HSZ HSZR HCP HDP HDPR G21 G22 HOP HNE HLT HOP11 KC.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (SC1 & SC2 & SC3).
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2.
    destruct HB0R as [HB0a HB0b].
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) as EF.
    pose proof EF as TEF. change (EVar WV_FF) with (EVar 33%N) in TEF.
    destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) as (TEA & TEB & _).
    assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 41) = Z_to_bv 64 b0) by reflexivity.
    assert (E42 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 42) = Z_to_bv 64 sz) by reflexivity.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) m
                    [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5944) 8 (EVar 42)]).
    { apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C1 (b8 b0)));
          [exact HB0 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; symmetry; apply w1_b8; lia].
      - eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5944) _ 0%nat (C8 (Z_to_bv 64 sz)));
          [exact HSZ | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E42; reflexivity]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp]
          [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5944) 8 (EVar 42)] HK1 200%nat [0xf4164] [true; true; false; true] 45%N
          S_STR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8B_LQ_1.
    { set (E := Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) in *.
      assert (E21 : edenot E (EVar 21) = Z_to_bv 64 (wa_n w - c_widx c)) by exact G21.
      assert (E22 : edenot E (EVar 22) = Z_to_bv 64 op) by exact G22.
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
      all: cbn [sc_denot];
        first [ rewrite (sc_b0_long_ne E 41 b0 E41 HB0a)
              | rewrite (sc_op_ne E 22 op 11 E22 ltac:(lia) ltac:(lia))
              | rewrite (sc_size_ne E 42 21 sz (wa_n w - c_widx c) E42 ltac:(lia) E21 ltac:(lia))
              | rewrite (sc_size_geu E 42 sz 262140 E42 ltac:(lia) ltac:(lia)) ];
        s8b_close. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp] R1 RT_PM_S8B_LQ_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (munch_sym (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp])) m (s_log SSr)
                  [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928); (EVar 33, 116, 120); (EVar 33, 114, 116)]
                  Hlf1 ltac:(vm_compute; reflexivity)) as TMU.
    cbn [num_wins map] in TMU. rewrite ?(srl3_val _ (EVar 33) (wa_ff w) TEB ltac:(lia)), ?TEF in TMU.
    assert (TFK : ffkeepX w [(116, 4); (114, 2)] m M1).
    { apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)). s8b_fk Q6. }
    assert (RW116 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 11)]).
    { subst M1. eapply (rw_cells_log_nth_ff H w _ m _ 0%nat 116 4 _ _ OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp]));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | lia | cbn [Z.of_nat]; lia
        | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 116 + i) with (wa_ff w + (116 + i)) by lia; apply FW2; lia
        | reflexivity | exact Logic.I | reflexivity ]. }
    assert (RW114 : rw_cells asegs M1 (wa_ff w + 114) [C2 (Z_to_bv 64 (sz / 4 + 1))]).
    { subst M1. eapply (rw_cells_log_nth_ff H w _ m _ 1%nat 114 2 _ _ OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 cp; Z_to_bv 64 dp]));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | lia | cbn [Z.of_nat]; lia
        | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 114 + i) with (wa_ff w + (114 + i)) by lia; apply FW2; lia
        | reflexivity | exact Logic.I
        | cbn [cbytes]; rewrite (ev_s8_nwl _ 42 sz E42 ltac:(lia)); reflexivity ]. }
    replace (s_pc SSr) with 0xf4164 in VIS1 by reflexivity.
    eapply (KC msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8D1 HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1).
    all: first [ exact RW114 | exact RW116 | exact TFK | exact TMU | exact (wmono_mem_denot _ _ _) | s8b_kept HR1 ].
  Qed.

End S8b.
