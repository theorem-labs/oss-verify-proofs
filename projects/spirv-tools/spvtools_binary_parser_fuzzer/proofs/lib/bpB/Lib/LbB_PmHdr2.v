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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_Conv LbB_MILB LbB_PrsStmt LbB_HKit LbB_HStKit LbB_PmExit LbB_PiStmt LbB_PiInit LbB_PmTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_RwStm LbB_PmHTK LbB_PmMagRS.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoBP LbB_PmMagK LbB_Own LbB_RwStm LbB_PmMagRS LbB_PmMagW LbB_PmHTK.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmHdr2 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib8SymExec33SX26adenotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02C79OSSVerify5KrLib3bpB2HF3Lib:BLPropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib8SymExec33SX26edenotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmHdr23b8wC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib=SymExec3Sound4SX2S4extzC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lorK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z7lor_0_rC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z:shiftl_0_lK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K59OSSVerify5KrLib8SymExec33SX28sidecond06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib8SymExec33SX25saddr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt5BSegs5asegsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4pmwA00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5as_StC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI69OSSVerify5KrLib3bpB3Lib9LbB_PmOwn7pmw_okA00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5PMXAT00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib3bpB2Rt7BsIface8as_AKRELC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface6as_VISC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C79OSSVerify5KrLib3bpB2HF3Lib:BLPropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF3Lib7BMState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_Bridge5rfullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut9regs_tblXC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_gpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase8wa_wordsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4wa_nC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltc69OSSVerify5KrLib3bpB3Lib:LbB_PmHdr2:hdr_good_KC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac:pmw_boundsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4wa_pC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7wa_consC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_ffC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5wa_s1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase6wa_sp0C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec33SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX29sym_state01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut:pm_kn_baseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init9Datatypes3appK59OSSVerify5KrLib8SymExec33SX27scripts01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX28sidecond01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase6c_widxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase8c_icountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut<regs_tbl_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut6xboundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7tbl_okXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7LibHash4HLib3srsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX28sym_execC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib=SymExec3Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut>env_world_seedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut:tbl_closedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7keys_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut8fkeys_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut=pm_kn_base_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib3bpB3Lib9LbB_PmTac<pmk_words_s1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac<pmk_words_ffC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib3bpB3Lib9LbB_PmTac<ev_world_allC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac6ev_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib3bpB3Lib9LbB_PmTac=pmk_sh_words0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut6fsh_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac<pmk_sh_pdisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac8pmk_sh_pC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib=SymExec3Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic5proj2C59OSSVerify5KrLib7LibHash4HLib6br_geuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib7LibHash4HLib5br_eqC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib7LibHash4HLib5br_neC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3lebC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib3bpB3Lib9LbB_PmTac8ev_xseedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26a_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib8adenot_ZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmHdr2:sc_rd_byteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_FKit:sym_insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25s_logC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC69OSSVerify5KrLib3bpB3Lib8LbB_FKit7fsh_patC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib8LbB_FKit6lbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_FSlots9upd_slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_FSlots9add_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut=sr_tbl_checkXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7scal_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_FSlots6lfieldC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_FSlots4svalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase8c_endianC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase9c_reqconvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase9set_scalAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut:scal_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7xa_scalC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib8SymExec33SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCutAregs_tbl_restrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26sr_getC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26sentry01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase9wenv_valsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib5EseedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7wa_diagC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7wa_userC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac=pmk_sh_ffdisjC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac<pmk_sh_wordsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmTac9pmk_sh_ffC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C4ELinuxProcessSemantics5Riscv3Sem<branch_takenI47Corelib4Init5Logic2or00C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut7pm_runSC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I59OSSVerify5KrLib8SymExec33SX26sentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26kentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C69OSSVerify5KrLib3bpB3Lib9LbB_PmHdr9TBL_ED90CC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I59OSSVerify5KrLib6LibPrs6PmBase3pmc00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmHdr8RT_ED90CC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmHdr29TBL_EDFD8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmHdr2:FTBL_EDFD8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Lib:LbB_PmHdr28RT_EDFD8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2Rt7BsIface5blockC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface3memC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase9OB_BINARYC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1N01I59OSSVerify5KrLib8SymExec33SX29sym_state00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase8WV_WORDSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5WV_S1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut8PM_RF_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase5WV_FFC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25sr_idC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut6PM_OWNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib9LbB_PmCut4FSHBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib7LbB_Kit6SHBASEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase7PM_OBJSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase6PM_NSHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Lib:LbB_PmBase4WV_PC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase7O_FLAGSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase6O_WIDXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase8O_ICOUNTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase8O_ENDIANC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition SH_P88 : expr := EAlu ALU_ADD (EAlu ALU_SRL (WADD WV_P 88) (ELit 3)) (ELit SHBASE).
Definition SH_P92 : expr := EAlu ALU_ADD (EAlu ALU_SRL (WADD WV_P 92) (ELit 3)) (ELit SHBASE).

Definition RT_EDFD8 : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (10%bv, EVar WV_WORDS); (11%bv, EVar WV_N);
   (13%bv, WADD WV_P 92); (18%bv, ELit SHBASE); (19%bv, EVar WV_P); (20%bv, SH_FF); (21%bv, ELit SHBASE);
   (22%bv, WADD WV_P 88); (23%bv, WADD WV_FF 13584); (24%bv, WADD WV_FF 14640); (25%bv, WADD WV_FF 11488);
   (26%bv, SH_P48); (27%bv, WADD WV_P 56)].

Definition TBL_EDFD8 : list (Z * expr) :=
  TBL_ED90C ++ [(1000, WADD WV_P 48); (1008, SH_P48); (936, SH_P88); (944, WADD WV_P 56); (960, WADD WV_FF 11488); (712, SH_P92)].
Definition FTBL_EDFD8 : list (Z * expr) := [(14640, EVar WV_WORDS); (14648, EVar WV_N)].

Definition b8w (b : byte) : word := Z_to_bv 64 (bv_unsigned b).

Lemma sc_rd_byte : forall E m (sa : saddr) (a : Z) (b : byte) (e : expr),
  adenot E sa = Z_to_bv 64 a -> rdn asegs m (Z_to_bv 64 a) 1 = Some [b] -> edenot E e = b8w b ->
  sc_denot asegs m E (SCReadBase sa 1 false e).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmHdr2 ()) [] "h01bh11zh21Eh32Hah42Heh52Hrh61ah72bsh81eh91mh:2sap;1p;2p;3p;4p;6g0000j12Tg000Uj1?Tg0013j1>Tg001Vj1<Tg0028j29Tg0030j21Tg003Vj30Tg0040j1MTg004Pj1DTg004oj4CTg005mj1BTg006Mj35Tg006mj24Tg007Oj2:Tg008Gj1ATg009Bj46Tg00:3j18Tg00;0j37Tg00;lj2@Tg00<Gj2;Tg00=1j2=Tg00=Nj2NTg00=hj1LTg00>Ij63Tg00>gj1KTg00?Ej2ETg00?ej1FTg00@Ij4GTg00@dj4HTg00A>j4ITg00B:j4JTg00C:g00D1#2#2#2R0#2#2#2#?R1#>R2%?0R3#>R4#<[g00DVg00EOR5g00Emf5R6f3R7'9f2R8,11502%M4R9#<R:g00FeR;P61117g00G\#DR<CC%B4R=9548,4930f7R>/:8%A7502P9P;f8R?f9R@/9>P<C6f0RA,4950:g00H;RB%8A77<,11f4RC,:@R@502'@X79A54C=RDP21116REP;P?PAP<C6A546=R=,4950:%8=97B<,11R==02@'@X02P;P>PEP<C6149D50:%8DRD97B<,11R:1:?7R9502f1P2%ACREA02=AX02P5g00H[R=1;36R6/=A,111116R6502X15P51;3CRC111A=026X15111CR5,N21=C=%LCE3%K0R0,E=%F0E3111D=025eA02:EeP9PAE3CGf6RA,9?P8E3CHP;P>P?PAP<PBP7CICJeW4W5W3W8X04W6W:W9W2o"). Qed.

Ltac hdr_sc H w E HE :=
  first [ pm_br H w E HE
        | cbn [sc_denot]; ev_xs; cbn [edenot]; unfold b8w; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia
        | eapply sc_rd_byte;
          [ rewrite (adenot_Z E _ (wa_words w)); [reflexivity | cbn [a_base]; pm_evx H w HE | lia]
          | eassumption
          | ev_xs; reflexivity ] ].

Section Hdr2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma nth_error_b8 : forall (l : list Z) k, (k < length l)%nat -> nth k l 1 = 0 ->
    nth_error (map (Z_to_bv 8) l) k = Some (Z_to_bv 8 0).
  Proof.
    induction l as [|z l IH]; intros k Hk Hn; [cbn in Hk; lia|].
    destruct k as [|k]; cbn in Hn |- *; [subst z; reflexivity | apply IH; [cbn in Hk; lia | exact Hn]].
  Qed.

  Lemma u8arr_byte0 : forall m A (l : list Z) k, u8arr asegs m A (map (Z_to_bv 8) l) -> (k < length l)%nat ->
    nth k l 1 = 0 -> fldA m (A + Z.of_nat k) 1 0.
  Proof.
    intros m A l k U Hk Hn. destruct U as [(B0 & B1 & B) _].
    pose proof (B k ltac:(rewrite length_map; lia)) as Bk.
    rewrite (nth_error_b8 l k Hk Hn) in Bk.
    unfold fldA, fld. change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
    exact (rdn1_of_mrd _ _ _ _ Bk).
  Qed.

  Lemma mag_pre_of : forall e ff fp XSc s LB m R (b0 b1 b2 b3 : byte),
    wpre H e -> winv H e ff fp XSc s LB m -> bp_shad ff [14; 20; 21]%nat m -> bp_rc H e ff R -> bp_rmag H e ff R ->
    w_words e <> 0 -> 5 <= w_n e ->
    PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 0)) 1 = Some [b0] -> PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 1)) 1 = Some [b1] ->
    PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 2)) 1 = Some [b2] -> PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 3)) 1 = Some [b3] ->
    hdrR_mg_pre R m (ff / 32) (wS1 e) (w_words e) (w_n e)
      (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
  Proof.
    intros e ff fp XSc s LB m R b0 b1 b2 b3 HP HI SH RC RM HW HN R0 R1 R2 R3.
    pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    pose proof HI as (RF & FF & RH & AC & MI & S0 & RA & ER & ST & SV & SF & WF & WFP & XP & FS & LVI).
    destruct (hdr_words H HH e ff fp XSc s LB m HP HI HW HN) as (W16le & W16 & WHI & SHw & _).
    pose proof HP as (_ & _ & N24 & WOK & RH0 & _).
    destruct WOK as [[E0 _] | (pw & k & Hin & Rg & W0 & _ & Whi & _)]; [contradiction |].
    destruct (blk_range H HH (w_s e) (w_LB e) (w_m e) pw (w_words e) k RH0 Hin) as (BA0 & _ & BN & _ & BAC & BAF & BAA).
    pose proof (bytes4_x b0 b1 b2 b3) as (XR & _).
    pose proof (rdn4_fld m (w_words e) b0 b1 b2 b3 ltac:(lia) ltac:(lia) R0 R1 R2 R3) as FX.
    set (x := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) in *.
    set (q := ff / 32).
    assert (Hq : ff = 32 * q) by (subst q; clear - G1; Z.div_mod_to_equations; lia).
    assert (SHq : sh ff = 4 * q + 2147450880).
    { unfold sh. rewrite ASHADOW_BASE_val, Hq. replace (32 * q) with ((4 * q) * 8) by ring. rewrite Z.div_mul by lia. lia. }
    destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
    destruct RM as (M10 & M11 & M18 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
    assert (WL : length (wo_sh [14; 20; 21]%nat) = 476%nat) by (vm_compute; reflexivity).
    assert (SB : forall k0, (k0 < 476)%nat -> nth k0 (wo_sh [14; 20; 21]%nat) 1 = 0 -> fldA m (sh ff + Z.of_nat k0) 1 0).
    { intros k0 Hk Hz. apply (u8arr_byte0 m (sh ff) _ k0 SH); [rewrite WL; exact Hk | exact Hz]. }
    unfold WO_FLAGP in WF.
    destruct ST as (T0 & T1 & T).
    unfold hdrR_mg_pre.
    split; [exact C2 |]. split; [exact M10 |]. split; [exact M11 |].
    split; [rewrite M18, Hq; reflexivity |].
    split; [rewrite C19, SHq, ASHADOW_BASE_val; reflexivity |].
    split; [rewrite C20, Hq; reflexivity |].
    split; [rewrite M25, Hq; reflexivity |].
    split; [exact AC |]. split; [exact FX |].
    split; [rewrite <- Hq; apply (wr_at_sub m ff 4088); [exact WF | lia | lia | lia] |].
    split; [rewrite <- Hq; apply (wr_at_sub m ff 4088); [exact WF | lia | lia | lia] |].
    split; [rewrite <- Hq; apply (wr_at_sub m ff 4088); [exact WF | lia | lia | lia] |].
    split; [replace (4 * q + 2147451096) with (sh ff + Z.of_nat 216) by (rewrite SHq; lia); apply SB; [lia | vm_compute; reflexivity] |].
    split; [replace (4 * q + 2147451097) with (sh ff + Z.of_nat 217) by (rewrite SHq; lia); apply SB; [lia | vm_compute; reflexivity] |].
    split; [replace (4 * q + 2147451323) with (sh ff + Z.of_nat 443) by (rewrite SHq; lia); apply SB; [lia | vm_compute; reflexivity] |].
    split; [split; [lia | split; [lia | intros i Hi; apply (T (wS1 e - 16 + i)); lia]] |].
    split; [lia |].
    split; [clear - G14; Z.div_mod_to_equations; lia |].
    split; [lia |]. split; [lia |]. split; [exact W16 |]. split; [lia |]. split; [lia |].
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
    split; [exact SHw |].
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
    split; [destruct G6 as [G6|G6]; unfold aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in G6; lia |].
    lia.
  Qed.
  Lemma good_of_post : forall e ff fp Q mo0 s LB LBs m mo R F fc XSc w c msF1 mo1 R' M' en,
    (en = 0 \/ en = 1) -> frm_zero fc -> as_MPRES H mo0 mo ->
    wpre H e -> winv H e ff fp XSc s LB m -> bp_slots H e ff m -> bp_shad ff [14; 20; 21]%nat m ->
    bp_rc H e ff R -> bp_rmag H e ff R -> bp_wl H e ff w ->
    bp_pfresh H w s LB LBs m c -> w_words e <> 0 -> 5 <= w_n e ->
    as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    as_VIS H s msF1 = MS R' F (wz (0xea7c4 + 5632)) fc None M' (seg_rom asegs) -> rfull R' ->
    CatSim.msteps asegs (MS R F (wz (0xea7c4 + 4784)) fc None m (seg_rom asegs)) (MS R' F (wz (0xea7c4 + 5632)) fc None M' (seg_rom asegs)) ->
    munch [((32 * (ff / 32) + 1728), (32 * (ff / 32) + 1744)); ((32 * (ff / 32) + 3544), (32 * (ff / 32) + 3549)); ((wS1 e - 8), wS1 e)] m M' ->
    wmono asegs m M' ->
    fldA M' (32 * (ff / 32) + 3548) 1 en -> fldA M' (32 * (ff / 32) + 3544) 4 en ->
    fldA M' (32 * (ff / 32) + 1736) 8 (w_n e) -> fldA M' (32 * (ff / 32) + 1728) 8 (w_words e) ->
    getr R' 2 = wz (wS1 e) -> getr R' 18 = wz ((32 * (ff / 32)) + 3456) -> getr R' 19 = wz ((4 * (ff / 32)) + ASHADOW_BASE) ->
    getr R' 20 = wz (32 * (ff / 32)) -> getr R' 24 = wz ((32 * (ff / 32)) + 3544) -> getr R' 25 = wz ((32 * (ff / 32)) + 1728) ->
    (forall r, In r [3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r) ->
    bp_kgood H e ff fp Q mo0 -> as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros e ff fp Q mo0 s LB LBs m mo R F fc XSc w c msF1 mo1 R' M' en Hen FZ MP HP HI SL SH RC RM WL PF HW HN
           KR1 MP1 VIS1 RF1 MS MU WM F92 F88 FBn FBw G2 G18 G19 G20 G24 G25 KEEP K.
    pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16).
    assert (Hq : 32 * (ff / 32) = ff) by (clear - E1; Z.div_mod_to_equations; lia).
    assert (F8 : ff mod 8 = 0) by (clear - E1; Z.div_mod_to_equations; lia).
    assert (SHq : 4 * (ff / 32) + ASHADOW_BASE = sh ff).
    { unfold sh. rewrite <- Hq at 2. replace (32 * (ff / 32)) with ((4 * (ff / 32)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
    rewrite Hq in MU, F92, F88, FBn, FBw, G18, G20, G24, G25. rewrite SHq in G19.
    set (W := [(ff + 1728, ff + 1744); (ff + 3544, ff + 3549); (wS1 e - 8, wS1 e)]) in MU.
    pose proof HI as (RF & FF & RH & AC & MI & S0 & RA & ER & ST & SV & SF & WF & WFP & XP & FS & LVI).
    pose proof aceil_facts as ((AC1 & AC2) & _).
    assert (REG : forall iv, In iv W -> (ff <= fst iv /\ snd iv <= ff + WO_FLAGP) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 512)
                                 \/ (w_lo e <= fst iv /\ snd iv <= wS1 e)).
    { intros iv Hiv. subst W. cbn in Hiv. unfold WO_FLAGP. destruct Hiv as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia. }
    assert (MI' : mem_inv asegs M') by exact (msteps_mem_inv asegs _ _ MS MI).
    assert (ST' : stk asegs M' (w_lo e) (wSP e)) by (apply (stk_keepW W m M'); [exact ST | exact MU | exact WM | unfold AIMG_TOP; lia]).
    assert (FW : Forall (wwin H e ff) W).
    { subst W. repeat constructor; unfold wwin; cbn [fst snd]; unfold WO_FLAGP, WO_SAVED; lia. }
    assert (HI' : winv H e ff fp XSc s LB M') by exact (winv_munch H HH e ff fp XSc s LB m M' W HP HI MU WM MI' ST' FW).
    destruct WL as (Wp & Wc & Ww & Wn & WLB & Ws0 & Wlo & WB & Wshi).
    destruct PF as (PP & FR & AL & CC).
    pose proof PP as (PR & PSH & HC & HU & HD & SOWN & LBOWN & CWR).
    rewrite Wc in HC.
    assert (BLK : forall b, In b (state_blocks (pc_state c)) -> exists pid, In (pid, fst b, snd b) LB).
    { intros b Hb. exact (stblk_in LB (pw_LB0 H w) LBs _ b SOWN Hb). }
    assert (PP' : bp_pp H w LB LBs M' (pc_e c en)).
    { apply (bp_pp_endian H w LB LBs m M' c W en PP MU WM); rewrite ?Wp, ?HC.
      - unfold AIMG_TOP. lia.
      - lia.
      - lia.
      - exact (proj2 FR).
      - exact Hen.
      - intros a Ha Hn. unfold PARSER_SIZE in Ha. apply (munch_at W m M' a MU); [lia |].
        intros iv Hiv. subst W. cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
      - intros a b Hb Hab. destruct (BLK b Hb) as (pid & Hin).
        destruct (blk_range H HH s LB m pid (fst b) (snd b) RH Hin) as (A0 & _ & N0 & _ & BAC & _).
        apply (munch_at W m M' a MU); [lia |]. intros iv Hiv.
        destruct (blk_disj_reg H HH e ff fp XSc s LB m iv pid (fst b) (snd b) HP HI (REG iv Hiv) Hin) as [D _]. lia.
      - intros a Ha. apply (munch_at W m M' a MU); [lia |].
        intros iv Hiv. subst W. cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
      - replace (ff + 3456 + 88) with (ff + 3544) by lia. exact F88.
      - replace (ff + 3456 + 92) with (ff + 3548) by lia. exact F92.
      - apply disj_of_all. intros iv Hiv.
        assert (SP : sh (ff + 3456) = sh ff + 432) by (replace (ff + 3456) with (ff + 8 * 432) by lia; apply sh_add8; lia).
        rewrite SP. unfold PARSER_SIZE. change (nsh 288) with 36.
        subst W. cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
      - apply disj_of_all. intros iv Hiv.
        assert (SC : sh (ff + 3376) = sh ff + 422) by (replace (ff + 3376) with (ff + 8 * 422) by lia; apply sh_add8; lia).
        rewrite SC. change (nsh 48) with 6.
        subst W. cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
      - intros b Hb. destruct (BLK b Hb) as (pid & Hin). apply disj_of_all. intros iv Hiv.
        destruct (blk_disj_reg H HH e ff fp XSc s LB m iv pid (fst b) (snd b) HP HI (REG iv Hiv) Hin) as [_ D]. lia. }
    assert (WL : bp_wl H e ff w) by (repeat split; assumption).
    unfold bp_kgood, bp_hdr0 in K.
    apply (K s LB LBs M' mo1 msF1 R' F fc XSc w (pc_e c en)).
    - rewrite VIS1. reflexivity.
    - exact RF1.
    - exact FZ.
    - exact KR1.
    - exact (ah_mpres_trans H HH mo0 mo mo1 MP MP1).
    - exact HP.
    - exact HI'.
    - destruct SL as (SL1 & SL2 & SL3).
      split; [| split].
      + eapply rw_cells_transport; [exact SL1 | exact MU | exact WM |]. subst W. cbn. lia.
      + eapply rw_cells_transport; [exact SL2 | exact MU | exact WM |]. subst W. cbn. lia.
      + eapply rw_cells_transport; [exact SL3 | exact MU | exact WM |]. subst W. cbn. lia.
    - eapply u8arr_transport; [exact SH | exact MU | exact WM |].
      rewrite length_map. replace (Z.of_nat (length (wo_sh [14; 20; 21]%nat))) with 476 by (vm_compute; reflexivity).
      subst W. cbn. lia.
    - destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      split; [exact G2 |].
      split; [etransitivity; [exact (KEEP 3%bv ltac:(repeat (first [left; reflexivity | right]))) | exact C3] |].
      split; [etransitivity; [exact (KEEP 4%bv ltac:(repeat (first [left; reflexivity | right]))) | exact C4] |].
      split; [etransitivity; [exact (KEEP 8%bv ltac:(repeat (first [left; reflexivity | right]))) | exact C8] |].
      split; [etransitivity; [exact (KEEP 9%bv ltac:(repeat (first [left; reflexivity | right]))) | exact C9] |].
      split; [exact G19 | exact G20].
    - destruct RM as (M10 & M11 & M18 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
      split; [exact G18 |].
      split; [etransitivity; [exact (KEEP 21%bv ltac:(repeat (first [left; reflexivity | right]))) | exact M21] |].
      split; [etransitivity; [exact (KEEP 22%bv ltac:(repeat (first [left; reflexivity | right]))) | exact M22] |].
      split; [etransitivity; [exact (KEEP 23%bv ltac:(repeat (first [left; reflexivity | right]))) | exact M23] |].
      split; [exact G24 |]. split; [exact G25 |].
      split; [etransitivity; [exact (KEEP 26%bv ltac:(repeat (first [left; reflexivity | right]))) | exact M26] |].
      etransitivity; [exact (KEEP 27%bv ltac:(repeat (first [left; reflexivity | right]))) | exact M27].
    - exact WL.
    - exists en.
      split; [exact (bp_piw H HH e ff fp XSc s LB M' w LBs (pc_e c en) HP HI' WL PP' HW) |].
      split; [exact PP' |].
      split.
      { destruct FR as (PH & _). unfold pi_hdr in PH |- *.
        cbn [bp_ste bp_st5 st_e pc_e pc_state st_words st_nwords st_diag st_widx st_icount st_endian st_flags
             st_m1 st_m2 st_m3 st_v1 st_v2 st_v3] in PH |- *.
        destruct PH as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
        repeat split; assumption. }
      split; [exact AL |].
      split.
      { unfold bp_bin. split; [exact FBw |]. split; [exact FBn |]. split; [exact HW | exact HN]. }
      eapply rw_cells_transport; [exact CC | exact MU | exact WM |]. rewrite Wc. subst W. cbn. lia.
  Qed.
  Definition hdr_good_K (e : went H) (ff fp : Z) (Q : config -> Prop) (mo0 : Model) : Prop := bp_kgood H e ff fp Q mo0.

  Lemma pm_hdr_b_le : forall e ff fp Q mo0 (b0 b1 b2 b3 : byte),
    bv_unsigned b0 = 3 -> bv_unsigned b1 = 2 -> bv_unsigned b2 = 35 -> bv_unsigned b3 = 7 ->
    hdr_good_K e ff fp Q mo0 ->
    bp_hdr0 H e ff fp [14; 20; 21]%nat BP_MAG (bp_rmag H e ff)
      (fun w s LB LBs m c => bp_pfresh H w s LB LBs m c /\ w_words e <> 0 /\ 5 <= w_n e /\
         (PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 0)) 1 = Some [b0] /\ PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 1)) 1 = Some [b1]
          /\ PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 2)) 1 = Some [b2] /\ PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 3)) 1 = Some [b3])) Q mo0.
  Proof.
    intros e ff fp Q mo0 b0 b1 b2 b3 E0 E1 E2 E3 K.
    intros s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL (PF & HW & HN & R0 & R1 & R2 & R3).
    pose proof (bytes4_x b0 b1 b2 b3) as (XR & X0 & X1 & X2 & X3).
    pose proof (mag_pre_of e ff fp XSc s LB m R b0 b1 b2 b3 HP HI SH RC RM HW HN R0 R1 R2 R3) as PRE.
    eapply (hdr_mgL_sr H HH s msF mo R F fc m (ff / 32) (wS1 e) (w_words e) (w_n e) _ Q KR);
      [rewrite VIS; reflexivity | exact RF | exact PRE | lia | lia | lia | lia |].
    intros msF1 mo1 R' M' KR1 MP1 VIS1 RF1 PST. unfold hdrR_mgL_post in PST.
    destruct PST as (MS & MU & WM & F92 & F88 & _ & FBn & FBw & _ & G2 & _ & _ & _ & _ & _ & _ & _ & _ & G18 & G19 & G20 & G24 & G25 & KEEP).
    exact (good_of_post e ff fp Q mo0 s LB LBs m mo R F fc XSc w c msF1 mo1 R' M' 0 (or_introl eq_refl) FZ MP HP HI SL SH RC RM WL PF HW HN
             KR1 MP1 VIS1 RF1 MS MU WM F92 F88 FBn FBw G2 G18 G19 G20 G24 G25 KEEP K).
  Qed.

  Lemma pm_hdr_b_be : forall e ff fp Q mo0 (b0 b1 b2 b3 : byte),
    bv_unsigned b0 = 7 -> bv_unsigned b1 = 35 -> bv_unsigned b2 = 2 -> bv_unsigned b3 = 3 ->
    hdr_good_K e ff fp Q mo0 ->
    bp_hdr0 H e ff fp [14; 20; 21]%nat BP_MAG (bp_rmag H e ff)
      (fun w s LB LBs m c => bp_pfresh H w s LB LBs m c /\ w_words e <> 0 /\ 5 <= w_n e /\
         (PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 0)) 1 = Some [b0] /\ PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 1)) 1 = Some [b1]
          /\ PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 2)) 1 = Some [b2] /\ PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 3)) 1 = Some [b3])) Q mo0.
  Proof.
    intros e ff fp Q mo0 b0 b1 b2 b3 E0 E1 E2 E3 K.
    intros s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL (PF & HW & HN & R0 & R1 & R2 & R3).
    pose proof (bytes4_x b0 b1 b2 b3) as (XR & X0 & X1 & X2 & X3).
    pose proof (mag_pre_of e ff fp XSc s LB m R b0 b1 b2 b3 HP HI SH RC RM HW HN R0 R1 R2 R3) as PRE.
    eapply (hdr_mgB_sr H HH s msF mo R F fc m (ff / 32) (wS1 e) (w_words e) (w_n e) _ Q KR);
      [rewrite VIS; reflexivity | exact RF | exact PRE | lia | lia | lia | lia |].
    intros msF1 mo1 R' M' KR1 MP1 VIS1 RF1 PST. unfold hdrR_mgB_post in PST.
    destruct PST as (MS & MU & WM & F92 & F88 & _ & FBn & FBw & _ & G2 & _ & _ & _ & _ & _ & _ & _ & _ & G18 & G19 & G20 & G24 & G25 & KEEP).
    exact (good_of_post e ff fp Q mo0 s LB LBs m mo R F fc XSc w c msF1 mo1 R' M' 1 (or_intror eq_refl) FZ MP HP HI SL SH RC RM WL PF HW HN
             KR1 MP1 VIS1 RF1 MS MU WM F92 F88 FBn FBw G2 G18 G19 G20 G24 G25 KEEP K).
  Qed.
End Hdr2.
