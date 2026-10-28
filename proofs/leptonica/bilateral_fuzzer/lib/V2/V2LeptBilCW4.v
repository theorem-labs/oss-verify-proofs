(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB LeptBracketB LeptCellsB LeptRecs LeptRoomPC LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptPixCreateT2 V2LeptPixCopyST V2LeptPixaCreate V2LeptPixaAdd V2LeptLinePtrs V2LeptPixaGLP V2LeptBl_iface V2LeptBilSegs V2LeptBilCSegs V2LeptBilCW1 V2LeptBilCW2 V2LeptBilCW3.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2LeptBilCW4 () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB4cellC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:asr_callocI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4lctx00C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc8aic_baseC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase2ASK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3Cok00I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs1W00C45stdpp9bitvector;definitions7Z_to_bvC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase4liveK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9DitherLib4rinvC47Corelib4Init5Logic3notC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5w_invC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase<ai_live_hullC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface7round16C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC5ARocqVerifyHarness?AgentSubmission6Common5Hoare3at_C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase5ownedK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission6Common:AllocIface8al_in_roC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface8al_in_rwI47Corelib4Init5Logic2or00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:round16_geC56Stdlib6ZArith6BinInt1Z2leC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase@ai_live_disjointC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common7StepTac6u_Z2bvK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW39rinv_out1K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase5LLU16I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8sub_liveC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW36bc_memC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_A0C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW38sub_noneK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_vmC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith6wpl_ofC56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPixCopyST3hdvC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5PIXatC5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW26bc_blkC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7rdn_extC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_Zc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bil_objc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW46bw_bscc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_minvc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_maxvc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_ncc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_kxc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_kfc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_spatc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW46bw_rngC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW26bc_bl2c5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_pac5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_lsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB7cellsAtC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptArithB6nc_valC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilSegs7kidx_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6set_rcc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW48bw_datasc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_parrc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_bac5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_barrC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptPixaCreate9pixa_blksC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_wC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_hc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW48bw_pixesc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW48bw_datadc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW49bw_linesfC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptPixaCreate:pixa_cellsc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW49bil_chainC4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecW;exW_blk_rngI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6pix_wf00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs9pix_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8bytes_atC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptLinePtrs7lp_rowsC46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB9agree_winC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB:cells_keepK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05c5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW4<rdn_keep_blkI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs;PIXat_frameC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW3=pixa_blks_subK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW3;bc_mem_keepC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs>sub_live_transC47Corelib5Lists7ListDef3mapI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs4pixv00i5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW44bilw00C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C5ARocqVerifyHarness?AgentSubmission6Common7FPSteps8frm_zeroC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_topC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBl_iface6bl_srcC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure5aroomc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45RB_bcC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs7cs_keptC4ELinuxProcessSemantics5Riscv3Sem7reg_getC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBl_iface6RB_ambC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface6al_romC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW49bil_frameC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_cmapC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixHdr6hdr_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5p_wplC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_dataC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6ll_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_img64C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ro_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_roC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_lg_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_lgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ag_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_agC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=pin_errno_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_errnoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_hcellC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3inZC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_hcellC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;pin_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:ll_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs<pin_ro_belowC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW3<RB_it_nonnegC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW35RB_itC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure?alloc_margin_geC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure<alloc_marginC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL>RB_pixT_nonnegC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW16bc_fl1C5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPixCreate8pixr_newC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface<callee_savedK5ARocqVerifyHarness?AgentSubmission6Common8PropExec7FPState01C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic9False_indC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LIVKC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots9LIVK_byteC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs4p_rcC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs9PIX_rd_rcC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecW=exW_blk_apartC5ARocqVerifyHarness?AgentSubmission6Common8VmLedgerBwith_vmmaps_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB5LIVKcC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB>agree_of_LIVKcC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8heap_gapC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3winC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface:al_globalsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8blk_byteC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB<PIXat_rc_setC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW36bc_cstC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW36bc_fl3C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW36bc_invC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW35bc_krC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB=agree_of_LIVKC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase8p16_segsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecW;exW_sok_blkC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6w_pureC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilCSegs4bc_UC5ARocqVerifyHarness?AgentSubmission6Common5Hoare:regs_agreeK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB8rinv_WPcc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW4?field_store_outK47Corelib4Init5Logic2or01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB=agree_of_rinvK47Corelib4Init5Logic2or02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB;cellsAt_nilC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB<cellsAt_consC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB;cellsAt_appC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB?POSTMc_of_POSTMC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB:POSTMc_subC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB<POSTMc_transC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9POSTM_subC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith4dvalC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith<wpl_of_rangeC56Stdlib6ZArith6BinInt1Z;mul_pos_posC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptPixaGLP:pixa_mem10C56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec6v_jalrC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptPixaGLP;lineset_newC5ARocqVerifyHarness?AgentSubmission6Common8VmLedgerAwith_vmmaps_twiceC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptPixaGLP9lset_uptoC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptPixaGLP8lset_subC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW3;bc_mem_livkC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB<agree_of_FRMC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:POSTM_monoC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW38bc_kr_csC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24ridxC46Stdlib5Lists4List9nth_errorC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB;cellsAt_nthC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilCSegs4bc_Vk5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW44bilw01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=cs_kept_introc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW4:bc_blk_refc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW4:bc_mem_refC47Corelib4Init5Logic6or_indC45stdpp9bitvector;definitions9bv_eq_decC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8WalksLib8zbv_selfC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW1:fs_notin_VC5ARocqVerifyHarness?AgentSubmission6Common5Reach8rz_reachC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptPixaGLPApixaGetLinePtrs_WC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW39bc_comp_WC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW2;bc_arrays_WC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW19bc_head_WC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5POSTMK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB6POSTMcC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_xresC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_yresC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_dC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_sp0C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixHdr7pix_hdrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8set_dataC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3FRMK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB5c_offC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecB7fs_listC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom6RK_pixK46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSetC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LSTKC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW16BC_WINc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45RK_bcI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8LSTK_valC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW35RK_itI47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00K46Stdlib9micromega=RingMicromega3Op204".
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

(* [comment removed for export] *)
Ltac NEbil Lb := let EQ := fresh "EQ" in intros EQ; let Lb' := fresh "Lb" in pose proof Lb as Lb'; rewrite <- EQ in Lb';
  match goal with LX : live _ _ = Some _ |- _ => rewrite LX in Lb'; discriminate Lb' end.

Section BilCW4.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Hypothesis H_amb : forall fx : FPState, @pixAddMirroredBorder_contract fx AL CL ASR.
Hypothesis H_gev : forall fx : FPState, @pixGetExtremeValue_contract fx AL CL ASR.

Lemma bc4_u_rng : forall x : word, (0 <= bv_unsigned x < 2 ^ 64)%Z.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.

(* [comment removed for export] *)
Lemma field_store_out : forall C A (m M : word -> option byte) md (b off : Z) (nb : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 b) = Some nb -> (0 <= b < 2 ^ 64)%Z ->
  (0 <= off)%Z -> (off + 8 <= nb)%Z -> rinv [((b + off)%Z, 8%Z)] m M ->
  forall (q : word) k (x : word), live A q = Some k -> q <> Z_to_bv 64 b -> (u q <= u x < u q + k)%Z -> M x = m x.
Proof.
  intros C A m M md b off nb Cok0 W0 Lb Hb Hoff Hnb RI q k x Lq Hqb Hx.
  destruct RI as [_ RI]. apply RI. intros r Hr. cbn [In] in Hr. destruct Hr as [Hr | []]. subst r. cbn [fst snd]. unfold inreg. intros Hin.
  pose proof (bc4_u_rng q) as Hq. pose proof (bc4_u_rng x) as Hx'.
  assert (Hne : b <> u q) by (intros E; apply Hqb; rewrite E, Z_to_bv_bv_unsigned; reflexivity).
  pose proof (exW_blk_apart C A m md b (u q) nb k Cok0 W0 Lb ltac:(rewrite Z_to_bv_bv_unsigned; exact Lq) Hne Hb Hq ltac:(lia) ltac:(lia)) as AP.
  lia.
Qed.
Lemma bc_mem_ref : forall C A A7 Af (m : word -> option byte) parr w h i pix data, sub_live A A7 -> bc_mem C A7 Af m parr w h i pix data -> bc_mem C A Af m parr w h i pix data.
Proof.
  intros C A A7 Af m parr w h i pix data S (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  unfold bc_mem. refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj _ (conj _ (conj H8 (conj H9 (conj H10 (conj H11 (conj H12 H13)))))))))))).
  all: match goal with |- live ?X ?q = None => destruct (live X q) eqn:E; [apply S in E; congruence | reflexivity] end.
Qed.
Lemma bc_blk_ref : forall C A A1 A7 Af X n, sub_live A A1 -> sub_live A7 Af -> bc_blk C A1 A7 X n -> bc_blk C A Af X n.
Proof.
  intros C A A1 A7 Af X n S1 S2 (H1 & H2 & H3 & H4 & H5 & H6).
  unfold bc_blk. refine (conj H1 (conj H2 (conj H3 (conj (S2 _ _ H4) (conj _ H6))))).
  destruct (live A (Z_to_bv 64 X)) eqn:E; [apply S1 in E; congruence | reflexivity].
Qed.

(* [comment removed for export] *)
Definition RK_bc : Z := (RK_pix + 6 + 4 + 10 * RK_it + 11)%Z.
Definition RB_bc (w h : Z) : Z := (RB_amb w h 11 + 6 * 131072 + 4 * 2 ^ 17 + 10 * RB_it w h + (alloc_margin 80 + 10 * alloc_margin (8 * h)))%Z.

(* [comment removed for export] *)
Record bilw : Type := BILW {
  bw_bsc : Z; bw_datas : Z; bw_nc : Z; bw_kx : Z; bw_kf : Z; bw_spat : Z; bw_rng : Z; bw_pa : Z; bw_parr : Z; bw_ba : Z; bw_barr : Z; bw_ls : Z;
  bw_minv : Z; bw_maxv : Z; bw_pixes : Z -> Z; bw_datad : Z -> Z; bw_linesf : Z -> Z }.

(* [comment removed for export] *)
Definition bil_chain (C : lctx) (Af : AS) (bil : Z) (v : pixv) (b : bilw) : Prop :=
  exists A1 A7 A3 : AS, sub_live A1 A7 /\ sub_live A7 A3 /\ sub_live A3 Af /\
    live A1 (Z_to_bv 64 (bw_bsc b)) = Some 64%Z /\ live A1 (Z_to_bv 64 (bw_datas b)) = Some (4 * (wpl_of (p_w v + 22) 8 * (p_h v + 22)))%Z /\ bw_bsc b <> bw_datas b /\
    bc_blk C A1 A7 bil 104 /\ bc_blk C A1 A7 (bw_nc b) 40 /\ bc_blk C A1 A7 (bw_kx b) 1024 /\ bc_blk C A1 A7 (bw_kf b) 1024 /\ bc_blk C A1 A7 (bw_spat b) 44 /\ bc_blk C A1 A7 (bw_rng b) 1024 /\
    (bw_kx b <> bw_kf b /\ bw_kx b <> bw_rng b /\ bw_kf b <> bw_rng b) /\
    live A7 (Z_to_bv 64 (bw_pa b)) = None /\ live A7 (Z_to_bv 64 (bw_parr b)) = None /\ live A7 (Z_to_bv 64 (bw_ba b)) = None /\ live A7 (Z_to_bv 64 (bw_barr b)) = None /\
    pixa_blks C A3 (bw_pa b) (bw_parr b) (bw_ba b) (bw_barr b) /\ bw_parr b <> bw_barr b /\
    (forall i, (0 <= i < 10)%Z -> live A7 (Z_to_bv 64 (bw_pixes b i)) = None /\ live A7 (Z_to_bv 64 (bw_datad b i)) = None /\
                                  live A3 (Z_to_bv 64 (bw_pixes b i)) = Some 64%Z /\ live A3 (Z_to_bv 64 (bw_datad b i)) = Some (4 * (wpl_of (p_w v) 8 * p_h v))%Z) /\
    (forall i j, (0 <= i < j)%Z -> (j < 10)%Z -> bw_datad b i <> bw_datad b j /\ bw_pixes b i <> bw_pixes b j /\ bw_pixes b i <> bw_datad b j /\ bw_datad b i <> bw_pixes b j) /\
    live A3 (Z_to_bv 64 (bw_ls b)) = None /\ (forall k, (0 <= k < 10)%Z -> live A3 (Z_to_bv 64 (bw_linesf b k)) = None) /\
    (forall k k', (0 <= k < k')%Z -> (k' < 10)%Z -> bw_linesf b k <> bw_linesf b k') /\
    (forall i, (0 <= i < 10)%Z -> ~ In (Z_to_bv 64 (bw_pixes b i)) (map (Z_to_bv 64) [bw_pa b; bw_parr b; bw_ba b; bw_barr b]) /\ ~ In (Z_to_bv 64 (bw_datad b i)) (map (Z_to_bv 64) [bw_pa b; bw_parr b; bw_ba b; bw_barr b])).

Definition bil_obj (C : lctx) (A Af : AS) (m : word -> option byte) (bil pixs : Z) (v : pixv) (b : bilw) : Prop :=
    cellsAt SEGS m bil (bc_bl2 pixs (bw_bsc b) (bw_minv b) (bw_maxv b) (bw_nc b) (bw_kx b) (bw_kf b) (bw_spat b) (bw_rng b) ++ [(88%Z, 8%nat, bw_pa b); (96%Z, 8%nat, bw_ls b)]) /\
    bc_blk C A Af bil 104 /\ bc_blk C A Af (bw_nc b) 40 /\ bc_blk C A Af (bw_kx b) 1024 /\ bc_blk C A Af (bw_kf b) 1024 /\ bc_blk C A Af (bw_spat b) 44 /\ bc_blk C A Af (bw_rng b) 1024 /\
    (0 <= bw_minv b <= 255)%Z /\ (0 <= bw_maxv b <= 255)%Z /\
    (forall j, (0 <= j < 10)%Z -> rdn SEGS m (Z_to_bv 64 (bw_nc b + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val (bw_minv b) (bw_maxv b) j))) /\ kidx_ok (bw_kx b) m /\ kfr_ok (bw_kf b) m /\
    PIXat m pixs (set_rc v 2) /\
    PIXat m (bw_bsc b) (hdv (p_w v + 22) (p_h v + 22) 8 0 (bw_datas b)) /\ bc_blk C A Af (bw_bsc b) 64 /\ bc_blk C A Af (bw_datas b) (4 * (wpl_of (p_w v + 22) 8 * (p_h v + 22))) /\
    pixa_cells m (bw_pa b) (bw_parr b) (bw_ba b) (bw_barr b) 10 /\ pixa_blks C Af (bw_pa b) (bw_parr b) (bw_ba b) (bw_barr b) /\
    live A (Z_to_bv 64 (bw_pa b)) = None /\ live A (Z_to_bv 64 (bw_parr b)) = None /\ live A (Z_to_bv 64 (bw_ba b)) = None /\ live A (Z_to_bv 64 (bw_barr b)) = None /\
    (forall i, (0 <= i < 10)%Z -> bc_mem C A Af m (bw_parr b) (p_w v) (p_h v) i (bw_pixes b i) (bw_datad b i)) /\
    (0 <= bw_ls b < 2 ^ 64)%Z /\ live A (Z_to_bv 64 (bw_ls b)) = None /\ live (c_A0 C) (Z_to_bv 64 (bw_ls b)) = None /\ live Af (Z_to_bv 64 (bw_ls b)) = Some 80%Z /\
    (forall k, (0 <= k < 10)%Z ->
       (0 <= bw_linesf b k < 2 ^ 64)%Z /\ live Af (Z_to_bv 64 (bw_linesf b k)) = Some (8 * p_h v)%Z /\ live A (Z_to_bv 64 (bw_linesf b k)) = None /\
       live (c_A0 C) (Z_to_bv 64 (bw_linesf b k)) = None /\ bw_linesf b k <> bw_ls b /\
       rdn SEGS m (Z_to_bv 64 (bw_ls b + 8 * k)) 8 = Some (Z_to_le_bytes 8 (bw_linesf b k)) /\ lp_rows m (bw_linesf b k) (bw_datad b k) (4 * wpl_of (p_w v) 8) (p_h v)) /\
    bil_chain C Af bil v b.

(* [comment removed for export] *)
Definition bil_frame (A Af : AS) (bil : Z) (b : bilw) : Prop :=
  forall q : word, ~ In q (map (Z_to_bv 64) [bil; bw_nc b; bw_kx b; bw_kf b; bw_spat b; bw_rng b; bw_bsc b; bw_datas b; bw_pa b; bw_parr b; bw_ba b; bw_barr b; bw_ls b]) ->
    (forall i, (0 <= i < 10)%Z -> q <> Z_to_bv 64 (bw_pixes b i) /\ q <> Z_to_bv 64 (bw_datad b i) /\ q <> Z_to_bv 64 (bw_linesf b i)) -> live Af q = live A q.

Lemma rdn_keep_blk : forall (m m' : word -> option byte) (q k a : Z) (n : nat), (forall x : word, (q <= u x < q + k)%Z -> m' x = m x) ->
  (q <= a)%Z -> (a + Z.of_nat n <= q + k)%Z -> (0 <= q)%Z -> (q + k <= 2 ^ 64)%Z -> rdn SEGS m' (Z_to_bv 64 a) n = rdn SEGS m (Z_to_bv 64 a) n.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilCW4 ()) ["BilCW4"] "p'0h04__x1h14__x2h21xh34__x3h44__x4h52H0h62H2h77__arithh84__ffh97__sat17h:7__sat18h;8__varmaph<5__with=4cstrh>2Hah?4__x5h@1mhA1ni001nhB1yhC1zhD2H1hE2H3hF2H4hG2HxhH3Hx0hI1KhJ1ahK1khL2m'hM2n'hN1qp;1p;2p;3p;4p;6p;<p;7p;Bp;8g00:?j1;Tg00:dj1^Tg00;Bj1XTg00;ej1UTg00Egj2GTg00RER0j21Tg00BMR1j20Tg00FQR2j24Tg00[Bj2:Tg00@Xj3ATg01<nR3j12Tg00A2j1TTg00APj2uTg00U<j1]Tg00>Mj2QTg017gj4PTg00Xkj2OTg00]:R4j19Tg01=Nj1JTg01=lj4fTg01>Oj4LTg01?6j1VTg00T0j2dTg00TXj3cTg00]Yj2?Tg00^kj2BTg00CJj1bTg00Cjj3@Tg00U\j2FTg00_Wj1aTg00dSj4>Tg00V:j1`Tg00VXj1vTg00Wfj2=Tg00WCj2STg00`5j1_Tg00NBj1tTg00[]j3sTg00XIj2rTg00YEj2qTg00Z1j3pTg00ZPj4oTg01?[j4nTg00\@j3iTg001<j6[Tg01@Fl<ZTg01@kj6hTg01ATj7jTg01BPl<\Tg01C5lBkTg00^Bj3lTg00e1j3mTg00aXj4ITg00bCj7HTg00coj8WTg00cKj7eTf2R5f1R6'0f0R7'1p=5g00f8R8/17p=7g00fVR9/O7p=3g01C[R:P:P9P9P4P3P3f3R4g01D:P5P6P7M<\p=NP:P9P9P9P3P3f5R3f4R;P4P5P6P7M<\p=DP9P9P9P9P9P9P1P7P6P5P1P4P;P3f6R1f7R<f8R=f9R>MBkp=CP9P9P0P<P0P1P3P;P4P5P6P7M<Zp=MAl967p=<Am967p=6P5g00g4R0g00gSR?P?g00h3R@P9P6g00hSRAP7CIg00i:RBFHp=EP3P0P?P?P@P;P0P?P?P@P9P4PAP5CIPBFHP6P7GWp=8P9P6g00iZP7CIp=KP6P0P?P?P@P7PBFHp=RP5P0P?P?P@P6P7Fep=YP4P0P?P?P@P5P6P7GWp=gg00jAR0#;RB#;RA#;RC#;#;#;RD#^RE#XRF%^C#XRC#URG[RH1GE7RI,1;10;4,4I':P1P6O1P<P6O15AG[^2F11;5RJ%25RK103;554%71%TBRL%TDRD'uRM95<1P:%27RN10>=55<%]C#URCg01:aROf;RP1QE=RQP6CPPOf<RRPQP6CP3A]6P3g00n\RQ#210=<551POPP1QE<PQCP,OCW6%97#2f:RC/0>55=PO%96ROPRf=RS1QE>RTP9P>%95#2RU=57MXC9%2ORV,0>RW/1M%26RX%T0RY'0RZ,0>R[/1MP7X29R\1167#JXB9X29R]PWP[P\P\P\P9P9g01D^1067Cf#3X@9XA9R^P>P>%3>R_PVPZP\P\%3NX2:RNPOPZ107YX29RZP6PX%3XCNR`EDM:CPMPM%3MGM10PCRa,1W11[aR[P\P]PWP\PZPXO1RXO1RW,0>P\P\P\P^P>P>P_PVPWP\P\PNPOPXP`EDM:CPaPa%3aGMP7CLRaP[%V5R`%7KRK1dLDRX148L%7D148M[[RO%7LRWg00lTRVAcLD6UW>RD%7M\V^>WRWg00m0RV%9QR_#9Rb,?9Rc1?9_1?9QRQ'<R_'<Rdg00o;Re'B%bVRf3@Rg%]VRhP9P91F9;P5%a9RiC>RjP61F94C>Rk%`9Rl%v9RmPm1=90Rn1=9BRo1S9YRp'6'6Rq%_0,=9R01=9ARA'6Rr%t?R?PmPmPr1S9L=s9ERLP?AEmqLE8E81rm@R@P7P5g00m\Rqg00n<Rr'O1q75=AqrdAp986CoRrb8b;b<X09X19X39X49106Y1054Rq557A54;MRs104Y=55M[[^09^19^39^49P7f?Rtf@Ru%21R1f>RvP;P=O6b7b9b:b=b5Cn1GETRTPaP[P`PKPXPOPDPWPgPhP91F95P6PiC>PlPmPm1S98R8PoP?PmPmPoPnP?AEm8nE8E8P@Prb8b;b<X09X19%761156%75[[^09^19P7PuPvP>PPO4b7b9b:b=b5PaP[P`PKPXPOPDPW%9bRb,?9RK/<d/Be=@VfPhPkPlPmPmP8PAP?PmPm16Ap,6n16o0R8P?PmPmP8PLP?1KnL,RmE8E8E8P@Prb8b;b<X09X19X39X49%7410;YRL=56q144M\s[[^09^19^39^49P7P1PtPuPvP4P;P=O7b7b9b:b=b55i>R=E[P9P>116I%94R1#2Rs,06,4I':PtP6O1PuP6O15AG[^2FXC911CI10CU,4I':P>P61GE6RI,1PRU10PsRC,4IRG':%24Ru/0Y,0P,4I,:URtPUPGPUP\PZPuO1RGO1RM,0PRq,4I%JUP9P9P2P\P21467#JXB9X29PIPI%3IPCPqP\P\P\P^PPPP%3PPsPMP\P\PNP1PGPZP4Pu%3uCNEDM:CM<ZEhP7CLPt%9;Rt#2Ru,0RRG10vSRS'1%2;R1/0Y=5RSRMP\P]PGP\PZP1O1RGO1R],0RP\P\P\P^PRPR%3RPuP]P\P\PNPtPGPZP;P1%31CNEDM:CPSPS%3SGMP4CLPM%V3%23#7PXPOPDPW%9b,?91<cQ'</Be1<K_/Be=@Vf5@VPhP9PjP6P91F93P4PiC>C>PlPmPm%_B,=9/6p,6ARp16n0R0P?PmAEmAo1Kop,Rm5YmP?PmPmPnPAP?AEmno1Ko0,Rm5YmE8CgE8P@Prb8b;b<X09X19X39X49X?91075954L103Y,0;,45,:J1153114;1043,4;':[[[^09^19^39^49^?9P7%2>fAfB1GE<fCP;P3PvO8b7b9b:b=b5bHO2WGX2FPTP=E[FjW6XM:P7O1n0110000020011100P5O1WFWEW6WDWIXA:XJ9XK9XN9XLHW@o"). Qed.

Lemma bc4_frame : forall Af (m m' : word -> option byte) (X n : Z),
  (forall (q : word) k (x : word), live Af q = Some k -> (u q <= u x < u q + k)%Z -> m' x = m x) ->
  live Af (Z_to_bv 64 X) = Some n -> (0 <= X < 2 ^ 64)%Z -> forall x : word, (X <= u x < X + n)%Z -> m' x = m x.
Proof.
  intros Af m m' X n Hk LX HX x Hx. apply (Hk (Z_to_bv 64 X) n x LX). rewrite Z_to_bv_small; [exact Hx | exact HX].
Qed.
Lemma bc4_rdn_keep : forall C Af (m m' : word -> option byte) md (X n a : Z) (k : nat), Cok C -> W C Af m md ->
  (forall (q : word) kk (x : word), live Af q = Some kk -> (u q <= u x < u q + kk)%Z -> m' x = m x) ->
  live Af (Z_to_bv 64 X) = Some n -> (0 <= X < 2 ^ 64)%Z -> (0 < n)%Z -> (X <= a)%Z -> (a + Z.of_nat k <= X + n)%Z ->
  rdn SEGS m' (Z_to_bv 64 a) k = rdn SEGS m (Z_to_bv 64 a) k.
Proof.
  intros C Af m m' md X n a k Cok0 W0 Hk LX HX Hn Ha1 Ha2.
  pose proof (exW_blk_rng C Af m md X n Cok0 W0 LX HX Hn) as (R1 & R2 & R3).
  apply (rdn_keep_blk m m' X n a k); try lia.
  exact (bc4_frame Af m m' X n Hk LX HX).
Qed.
Lemma bc4_cells_keep : forall C Af (m m' : word -> option byte) md (X n base : Z) (L : list cell), Cok C -> W C Af m md ->
  (forall (q : word) kk (x : word), live Af q = Some kk -> (u q <= u x < u q + kk)%Z -> m' x = m x) ->
  live Af (Z_to_bv 64 X) = Some n -> (0 <= X < 2 ^ 64)%Z -> (0 < n)%Z ->
  Forall (fun c : cell => (X <= base + c_off c)%Z /\ (base + c_off c + Z.of_nat (c_len c) <= X + n)%Z) L ->
  cellsAt SEGS m base L -> cellsAt SEGS m' base L.
Proof.
  intros C Af m m' md X n base L Cok0 W0 Hk LX HX Hn HF HC. unfold cellsAt in *.
  rewrite Forall_forall in HF, HC |- *. intros c Hc. destruct (HF c Hc) as [B1 B2].
  rewrite (bc4_rdn_keep C Af m m' md X n (base + c_off c) (c_len c) Cok0 W0 Hk LX HX Hn B1 B2). exact (HC c Hc).
Qed.
Lemma bc4_blk_rng : forall C A Af X n, bc_blk C A Af X n -> (0 < n)%Z -> (0 <= X < 2 ^ 64)%Z /\ live Af (Z_to_bv 64 X) = Some n.
Proof.
  intros C A Af X n (B1 & B2 & B3 & B4 & B5 & B6) Hn. pose proof (alloc_top_lt_errno (c_vm C)) as T.
  rewrite stack_max_size_val in T. split; [lia | exact B4].
Qed.
Lemma bc4_blk_up : forall C A Af Af' X n, sub_live Af Af' -> bc_blk C A Af X n -> bc_blk C A Af' X n.
Proof. intros C A Af Af' X n Hs H. exact (bc_blk_ref C A A Af Af' X n (sub_live_refl A) Hs H). Qed.
Lemma bc4_mem_keep : forall C A Af Af' (m m' : word -> option byte) md parr w h i pix data, Cok C -> W C Af m md ->
  (forall (q : word) kk (x : word), live Af q = Some kk -> (u q <= u x < u q + kk)%Z -> m' x = m x) -> sub_live Af Af' ->
  live Af (Z_to_bv 64 parr) = Some 80%Z -> (0 <= parr < 2 ^ 64)%Z -> (0 <= i < 10)%Z ->
  bc_mem C A Af m parr w h i pix data -> bc_mem C A Af' m' parr w h i pix data.
Proof.
  intros C A Af Af' m m' md parr w h i pix data Cok0 W0 Hk Hs Lp Rp Hi (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  pose proof (alloc_top_lt_errno (c_vm C)) as T. rewrite stack_max_size_val in T.
  unfold bc_mem. refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj (Hs _ _ H10) (conj (Hs _ _ H11) (conj _ _)))))))))))).
  - eapply PIXat_frame; [exact H12 | exact (bc4_frame Af m m' pix 64 Hk H10 ltac:(lia))].
  - rewrite (bc4_rdn_keep C Af m m' md parr 80 (parr + 8 * i) 8 Cok0 W0 Hk Lp Rp ltac:(lia) ltac:(lia) ltac:(lia)). exact H13.
Qed.

(* [comment removed for export] *)
Lemma bil_obj_keep : forall C A Af Af' (m m' : word -> option byte) md bil pixs v b, Cok C -> W C Af m md ->
  bil_obj C A Af m bil pixs v b -> live Af (Z_to_bv 64 pixs) = Some 64%Z ->
  (forall (q : word) k (x : word), live Af q = Some k -> (u q <= u x < u q + k)%Z -> m' x = m x) -> sub_live Af Af' ->
  bil_obj C A Af' m' bil pixs v b.
Proof.
  intros C A Af Af' m m' md bil pixs v b Cok0 W0 OB Lpix Hk Hs.
  destruct OB as (Hcl & Bbil & Bnc & Bkx & Bkf & Bsp & Brg & Hmin & Hmax & Hnc & Hkidx & Hkfr & Hpix & Hbsc & Bbsc & Bdat & Hpc & Hpb &
    La1 & La2 & La3 & La4 & Hmem & Hls1 & Hls2 & Hls3 & Hls4 & Hlf & Hch).
  destruct (bc4_blk_rng _ _ _ _ _ Bbil ltac:(lia)) as [Rbil Lbil].
  destruct (bc4_blk_rng _ _ _ _ _ Bnc ltac:(lia)) as [Rnc Lnc].
  destruct (bc4_blk_rng _ _ _ _ _ Bkx ltac:(lia)) as [Rkx Lkx].
  destruct (bc4_blk_rng _ _ _ _ _ Bkf ltac:(lia)) as [Rkf Lkf].
  destruct (bc4_blk_rng _ _ _ _ _ Bbsc ltac:(lia)) as [Rbsc Lbsc].
  pose proof Hpb as (Rpa & Rparr & Rba & Rbarr & Lpa & Lparr & Lba & Lbarr & _).
  assert (Rpix : (0 <= pixs < 2 ^ 64)%Z) by (destruct Hpix as (P1 & P2 & _); lia).
  unfold bil_obj.
  refine (conj _ (conj (bc4_blk_up _ _ _ _ _ _ Hs Bbil) (conj (bc4_blk_up _ _ _ _ _ _ Hs Bnc) (conj (bc4_blk_up _ _ _ _ _ _ Hs Bkx)
    (conj (bc4_blk_up _ _ _ _ _ _ Hs Bkf) (conj (bc4_blk_up _ _ _ _ _ _ Hs Bsp) (conj (bc4_blk_up _ _ _ _ _ _ Hs Brg) (conj Hmin (conj Hmax
    (conj _ (conj _ (conj _ (conj _ (conj _ (conj (bc4_blk_up _ _ _ _ _ _ Hs Bbsc) (conj (bc4_blk_up _ _ _ _ _ _ Hs Bdat) (conj _ (conj _
    (conj La1 (conj La2 (conj La3 (conj La4 (conj _ (conj Hls1 (conj Hls2 (conj Hls3 (conj (Hs _ _ Hls4) (conj _ _)))))))))))))))))))))))))))).
  - eapply (bc4_cells_keep C Af m m' md bil 104 bil); [exact Cok0 | exact W0 | exact Hk | exact Lbil | exact Rbil | lia | | exact Hcl].
    unfold bc_bl2. cbn [app]. repeat first [apply Forall_nil | apply Forall_cons]. all: unfold c_off, c_len; cbn [fst snd]; lia.
  - intros j Hj. rewrite (bc4_rdn_keep C Af m m' md (bw_nc b) 40 (bw_nc b + 4 * j) 4 Cok0 W0 Hk Lnc Rnc ltac:(lia) ltac:(lia) ltac:(lia)).
    exact (Hnc j Hj).
  - unfold kidx_ok in *. intros v0 Hv. destruct (Hkidx v0 Hv) as (kv & E & R). exists kv. split; [|exact R].
    rewrite (bc4_rdn_keep C Af m m' md (bw_kx b) 1024 (bw_kx b + 4 * v0) 4 Cok0 W0 Hk Lkx Rkx ltac:(lia) ltac:(lia) ltac:(lia)). exact E.
  - unfold kfr_ok in *. intros v0 Hv. destruct (Hkfr v0 Hv) as (kv & E & R). exists kv. split; [|exact R].
    rewrite (bc4_rdn_keep C Af m m' md (bw_kf b) 1024 (bw_kf b + 4 * v0) 4 Cok0 W0 Hk Lkf Rkf ltac:(lia) ltac:(lia) ltac:(lia)). exact E.
  - eapply PIXat_frame; [exact Hpix | exact (bc4_frame Af m m' pixs 64 Hk Lpix Rpix)].
  - eapply PIXat_frame; [exact Hbsc | exact (bc4_frame Af m m' (bw_bsc b) 64 Hk Lbsc Rbsc)].
  - unfold pixa_cells in *. repeat match goal with |- _ /\ _ => split end.
    all: first [ erewrite (bc4_rdn_keep _ _ _ _ _ (bw_pa b) 32 _ _ Cok0 W0 Hk Lpa Rpa) by lia; tauto
               | erewrite (bc4_rdn_keep _ _ _ _ _ (bw_ba b) 24 _ _ Cok0 W0 Hk Lba Rba) by lia; tauto ].
  - unfold pixa_blks in *. destruct Hpb as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
    exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj (Hs _ _ Q5) (conj (Hs _ _ Q6) (conj (Hs _ _ Q7) (conj (Hs _ _ Q8) (conj Q9 (conj Q10 (conj Q11 Q12))))))))))).
  - intros i Hi. exact (bc4_mem_keep C A Af Af' m m' md (bw_parr b) _ _ i _ _ Cok0 W0 Hk Hs Lparr Rparr Hi (Hmem i Hi)).
  - intros k Hkk. destruct (Hlf k Hkk) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    refine (conj F1 (conj (Hs _ _ F2) (conj F3 (conj F4 (conj F5 (conj _ _)))))).
    + rewrite (bc4_rdn_keep C Af m m' md (bw_ls b) 80 (bw_ls b + 8 * k) 8 Cok0 W0 Hk Hls4 Hls1 ltac:(lia) ltac:(lia) ltac:(lia)). exact F6.
    + unfold lp_rows in *. intros i Hi.
      rewrite (bc4_rdn_keep C Af m m' md (bw_linesf b k) (8 * p_h v) (bw_linesf b k + 8 * i) 8 Cok0 W0 Hk F2 F1 ltac:(lia) ltac:(lia) ltac:(lia)).
      exact (F7 i Hi).
  - unfold bil_chain in *. destruct Hch as (A1 & A7 & A3 & S1 & S2 & S3 & Rest). exists A1, A7, A3.
    exact (conj S1 (conj S2 (conj (sub_live_trans _ _ _ S3 Hs) Rest))).
Qed.

Lemma bc4_u_lit : forall z : Z, (0 <= z < 2 ^ 64)%Z -> u (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. exact Hz. Qed.
Lemma bc4_at_u : forall (X : Z) (x : word), (0 <= X < 2 ^ 64)%Z -> (X <= u x)%Z -> at_ (Z_to_bv 64 X) (u x - X) = x.
Proof.
  intros X x HX Hx. unfold at_. rewrite Z_to_bv_small by exact HX.
  replace (X + (u x - X))%Z with (u x) by lia. apply Z_to_bv_bv_unsigned.
Qed.
Lemma bc4_livk_pt : forall A (m m' : word -> option byte) (X k : Z), LIVK A m m' -> live A (Z_to_bv 64 X) = Some k ->
  (0 <= X)%Z -> (X + k <= 2 ^ 64)%Z -> forall x : word, (X <= u x < X + k)%Z -> m' x = m x.
Proof.
  intros A m m' X k LK LX H0 H1 x Hx. assert (HX : (0 <= X < 2 ^ 64)%Z) by lia.
  rewrite <- (bc4_at_u X x HX ltac:(lia)). apply (LK (Z_to_bv 64 X) k (u x - X)%Z LX). lia.
Qed.
Lemma bc4_livkc_pt : forall A (c n : Z) (m m' : word -> option byte) (X k : Z), LIVKc A c n m m' -> live A (Z_to_bv 64 X) = Some k ->
  (0 <= X)%Z -> (X + k <= 2 ^ 64)%Z -> forall x : word, (X <= u x < X + k)%Z -> ~ (c <= u x < c + n)%Z -> m' x = m x.
Proof.
  intros A c n m m' X k LK LX H0 H1 x Hx Hc. assert (HX : (0 <= X < 2 ^ 64)%Z) by lia.
  rewrite <- (bc4_at_u X x HX ltac:(lia)). apply (LK (Z_to_bv 64 X) k (u x - X)%Z LX); [lia|].
  rewrite Z_to_bv_small by exact HX. replace (X + (u x - X))%Z with (u x) by lia. exact Hc.
Qed.
Lemma bc4_none : forall (A A' : AS) (q : word), sub_live A A' -> live A' q = None -> live A q = None.
Proof. intros A A' q S H. destruct (live A q) eqn:E; [apply S in E; congruence | reflexivity]. Qed.
Definition bc4_fk (Af : AS) (m m' : word -> option byte) : Prop :=
  forall (q : word) (k : Z) (x : word), live Af q = Some k -> k <> 104%Z -> (u q <= u x < u q + k)%Z -> m' x = m x.
Lemma bc4_fk_trans : forall Af (m1 m2 m3 : word -> option byte), bc4_fk Af m1 m2 -> bc4_fk Af m2 m3 -> bc4_fk Af m1 m3.
Proof. intros Af m1 m2 m3 H1 H2 q k x L Hk Hx. rewrite (H2 q k x L Hk Hx). exact (H1 q k x L Hk Hx). Qed.
Lemma bc4_fk_sub : forall A Af (m m' : word -> option byte), sub_live A Af -> bc4_fk Af m m' -> bc4_fk A m m'.
Proof. intros A Af m m' S H q k x L Hk Hx. exact (H q k x (S _ _ L) Hk Hx). Qed.
Lemma bc4_fk_livk : forall Af (m m' : word -> option byte), LIVK Af m m' -> bc4_fk Af m m'.
Proof.
  intros Af m m' LK q k x L Hk Hx. pose proof (bc4_u_rng q) as Hq.
  rewrite <- (bc4_at_u (u q) x Hq ltac:(lia)). rewrite Z_to_bv_bv_unsigned. apply (LK q k (u x - u q)%Z L). lia.
Qed.
Lemma bc4_fk_st : forall C Af (m M : word -> option byte) md (b off : Z), Cok C -> W C Af m md ->
  live Af (Z_to_bv 64 b) = Some 104%Z -> (0 <= b < 2 ^ 64)%Z -> (0 <= off)%Z -> (off + 8 <= 104)%Z ->
  rinv [((b + off)%Z, 8%Z)] m M -> bc4_fk Af m M.
Proof.
  intros C Af m M md b off Cok0 W0 Lb Hb Ho1 Ho2 RI q k x Lq Hk Hx.
  apply (field_store_out C Af m M md b off 104 Cok0 W0 Lb Hb Ho1 Ho2 RI q k x Lq); [|exact Hx].
  intros E. subst q. rewrite Lb in Lq. injection Lq as Lq. lia.
Qed.
Lemma bc4_fk_pt : forall Af (m m' : word -> option byte) (X n : Z), bc4_fk Af m m' -> live Af (Z_to_bv 64 X) = Some n -> n <> 104%Z ->
  (0 <= X < 2 ^ 64)%Z -> forall x : word, (X <= u x < X + n)%Z -> m' x = m x.
Proof. intros Af m m' X n H L Hn HX x Hx. apply (H (Z_to_bv 64 X) n x L Hn). rewrite Z_to_bv_small by exact HX. exact Hx. Qed.
Lemma bc4_fk_rdn : forall C Af (m m' : word -> option byte) md (X n a : Z) (k : nat), Cok C -> W C Af m md -> bc4_fk Af m m' ->
  live Af (Z_to_bv 64 X) = Some n -> n <> 104%Z -> (0 <= X < 2 ^ 64)%Z -> (0 < n)%Z -> (X <= a)%Z -> (a + Z.of_nat k <= X + n)%Z ->
  rdn SEGS m' (Z_to_bv 64 a) k = rdn SEGS m (Z_to_bv 64 a) k.
Proof.
  intros C Af m m' md X n a k Cok0 W0 H LX Hn HX Hn0 Ha1 Ha2.
  pose proof (exW_blk_rng C Af m md X n Cok0 W0 LX HX Hn0) as (R1 & R2 & R3).
  apply (rdn_keep_blk m m' X n a k); try lia.
  exact (bc4_fk_pt Af m m' X n H LX Hn HX).
Qed.
Lemma bc4_mem_fk : forall C A Af Af' (m m' : word -> option byte) md parr w h i pix data, Cok C -> W C Af m md ->
  bc4_fk Af m m' -> sub_live Af Af' -> live Af (Z_to_bv 64 parr) = Some 80%Z -> (0 <= parr < 2 ^ 64)%Z -> (0 <= i < 10)%Z ->
  bc_mem C A Af m parr w h i pix data -> bc_mem C A Af' m' parr w h i pix data.
Proof.
  intros C A Af Af' m m' md parr w h i pix data Cok0 W0 Hk Hs Lp Rp Hi (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  pose proof (alloc_top_lt_errno (c_vm C)) as T. rewrite stack_max_size_val in T.
  unfold bc_mem. refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj (Hs _ _ H10) (conj (Hs _ _ H11) (conj _ _)))))))))))).
  - eapply PIXat_frame; [exact H12 | exact (bc4_fk_pt Af m m' pix 64 Hk H10 ltac:(lia) ltac:(lia))].
  - rewrite (bc4_fk_rdn C Af m m' md parr 80 (parr + 8 * i) 8 Cok0 W0 Hk Lp ltac:(lia) Rp ltac:(lia) ltac:(lia) ltac:(lia)). exact H13.
Qed.
Lemma bc4_cin : forall (m : word -> option byte) (base : Z) (L : list cell) (o : Z) (n : nat) (z a : Z),
  cellsAt SEGS m base L -> In (o, n, z) L -> a = (base + o)%Z -> rdn SEGS m (Z_to_bv 64 a) n = Some (Z_to_le_bytes n z).
Proof. intros m base L o n z a H Hin ->. unfold cellsAt in H. rewrite Forall_forall in H. exact (H _ Hin). Qed.
Lemma bc4_cincl : forall (m : word -> option byte) (base : Z) (L1 L2 : list cell),
  cellsAt SEGS m base L1 -> (forall c, In c L2 -> In c L1) -> cellsAt SEGS m base L2.
Proof. intros m base L1 L2 H Hi. unfold cellsAt in *. rewrite Forall_forall in *. intros c Hc. exact (H c (Hi c Hc)). Qed.
Ltac bc4_in := first [ reflexivity | left; bc4_in | right; bc4_in ].
Lemma bc4_cells_tail : forall C A8 (m8 MU m9 : word -> option byte) (bil s : Z) (L : list cell), Cok C ->
  rinv [((bil + 88)%Z, 8%Z)] m8 MU -> (0 <= bil)%Z -> (bil + 104 <= s - 320)%Z -> POSTM C A8 (s - 320) MU m9 ->
  (c_top C - LSTK <= s - 320)%Z -> (s <= c_top C)%Z ->
  Forall (fun c : cell => (0 <= c_off c)%Z /\ (c_off c + Z.of_nat (c_len c) <= 320)%Z) L ->
  cellsAt SEGS m8 (s - 320) L -> cellsAt SEGS m9 (s - 320) L.
Proof.
  intros C A8 m8 MU m9 bil s L Cok0 RI Hb0 Hb PM Hs1 Hs2 HL HC.
  pose proof Cok0 as [Ctop Csp0 Csp0hi Cal Cimg]. pose proof (bc4_u_rng (c_sp0 C)) as Usp.
  unfold cellsAt in *. rewrite Forall_forall in *. intros c Hc. specialize (HL c Hc). specialize (HC c Hc).
  pose proof (FRM_rdn_above C (s - 320) MU m9 (s - 320 + c_off c) (c_len c) Cok0 (proj1 PM) ltac:(lia) ltac:(lia) Hs1) as E.
  rewrite p16_segs in E. rewrite E.
  rewrite (rdn_keep_blk m8 MU (s - 320) 320 (s - 320 + c_off c) (c_len c)); [exact HC | | lia | lia | lia | lia].
  intros x Hx. destruct RI as [_ RI]. apply RI. intros r Hr. cbn [In] in Hr. destruct Hr as [<- | []]. unfold inreg. cbn [fst snd]. lia.
Qed.
Lemma bc4_bil_win : forall (m7 m8 MU m9 MV : word -> option byte) (bil : Z),
  (forall x : word, (bil <= u x < bil + 104)%Z -> m8 x = m7 x) -> rinv [((bil + 88)%Z, 8%Z)] m8 MU ->
  (forall x : word, (bil <= u x < bil + 104)%Z -> m9 x = MU x) -> rinv [((bil + 96)%Z, 8%Z)] m9 MV ->
  agree_win bil 104 [(88%Z, 8%Z); (96%Z, 8%Z)] m7 MV.
Proof.
  intros m7 m8 MU m9 MV bil H1 [_ R1] H3 [_ R2] a Ha Hro.
  pose proof (Hro (88%Z, 8%Z) (or_introl eq_refl)) as N1. pose proof (Hro (96%Z, 8%Z) (or_intror (or_introl eq_refl))) as N2.
  cbn [fst snd] in N1, N2.
  rewrite R2, H3, R1, H1 by (first [exact Ha | intros r Hr; cbn [In] in Hr; destruct Hr as [<- | []]; unfold inreg; cbn [fst snd]; lia]).
  reflexivity.
Qed.
Lemma bc4_fs12 : forall r : reg, In (u r) fs_list -> r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv.
Proof. intros r Hr. unfold fs_list in Hr. cbn [In] in Hr. repeat split; intros E; subst r; vm_compute in Hr; lia. Qed.

(* [comment removed for export] *)
Lemma bilateralCreate_W : forall fr cs C A m md regs (s pixs : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  bl_src A m pixs v -> p_rc v = 1%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None -> (22 <= p_w v)%Z -> (22 <= p_h v)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_bc <= kR)%Z -> (RB_bc (p_w v) (p_h v) <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 0 -> (forall q, live A' q = live A q) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     aroom A' vm' (kR - RK_pix) (bR - RB_amb (p_w v) (p_h v) 11) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  (forall fr' cs' A' m' vm' regs' (bil : Z) (b : bilw), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> sub_live A A' ->
     POSTMc C A s (pixs + 20) 4 m m' -> getr regs' 10 = Z_to_bv 64 bil -> bil_obj C A A' m' bil pixs v b -> bil_frame A A' bil b ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     aroom A' vm' (kR - RK_bc) (bR - RB_bc (p_w v) (p_h v)) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 235748) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pixs v ret S Cok0 W0 Fz0 Hsp Hal Hwin Htop H1 Hret H4 H10 H11 H12 F10 F11 SRC RC LA0 Hw Hh
         kR bR AR HkR HbR K0 K1.
  pose proof SRC as (Px & Pd & Pcm & Phdr & Pw1 & Ph1 & Pwpl & Lpx & Ldat & Pxr & Pyr).
  assert (Rpx : (0 <= pixs < 2 ^ 64)%Z) by (destruct Px as (P1 & P2 & _); lia).
  pose proof (alloc_top_lt_errno (c_vm C)) as T. rewrite stack_max_size_val in T.
  assert (RBn : (0 <= RB_it (p_w v) (p_h v))%Z /\ (0 <= RB_amb (p_w v) (p_h v) 11)%Z /\ (80 <= alloc_margin 80)%Z /\
                (8 * p_h v <= alloc_margin (8 * p_h v))%Z).
  { unfold RB_it, RB_amb. pose proof (RB_pixT_nonneg (4 * (wpl_of (p_w v + 22) 8 * (p_h v + 22)))).
    pose proof (RB_pixT_nonneg (4 * (wpl_of (p_w v) 8 * p_h v))). pose proof (RB_pixT_nonneg (4 * (wpl_of (p_w v + 2 * 11) 8 * (p_h v + 2 * 11)))).
    pose proof (alloc_margin_ge 80 ltac:(lia)). pose proof (alloc_margin_ge (8 * p_h v) ltac:(lia)). lia. }
  assert (RKn : (RK_bc = RK_pix + 6 + 4 + 10 * RK_it + 11 /\ 0 <= RK_it /\ RK_pix = 2)%Z) by (unfold RK_bc, RK_it, RK_pixcopy, RK_cmapcopy, RK_pix; lia).
  unfold RB_bc in HbR.
  eapply bc_head_W; try (exact H_amb); try (exact H_gev); try eassumption.
  - lia.
  - lia.
  - intros fr1 cs1 A1 m1 vm1 regs1 bsc datasc minv maxv W1 Fz1 PM1 CL1 Hmin Hmax HO PN R1 R2 R4 R10 R11 R9 R22 R24 RCS1 F8 F9 FS1 AR1.
    pose proof PN as (Pb1 & Pb2 & Pb3 & Pd1 & Pd2 & Pd3 & Pne & LbA & LdA & Lb0 & Ld0 & LbA1 & LdA1 & Loth & PxB & PdB).
    assert (S01 : sub_live A A1) by (eapply sub_live_new2; [exact LbA | exact LdA | exact LbA1 | exact LdA1 | exact Loth]).
    assert (RC1 : rdn SEGS m1 (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1)).
    { destruct PM1 as [_ LK]. rewrite (LIVK_rdn A m m1 (Z_to_bv 64 pixs) 64 (pixs + 20) 4 LK Lpx).
      - rewrite (PIX_rd_rc SEGS m pixs v Px), RC. reflexivity.
      - rewrite Z_to_bv_small by exact Rpx. lia.
      - rewrite Z_to_bv_small by exact Rpx. cbn [Z.of_nat Pos.of_succ_nat]. lia.
      - rewrite Z_to_bv_small by exact Rpx. destruct Px as (P1 & P2 & _). lia. }
    eapply (bc_arrays_W fr1 cs1 C A1 m1 (with_vmmaps vm1 md) regs1 regs fr s pixs bsc minv maxv S (getr regs1 3));
      try eassumption; try reflexivity.
    + lia.
    + exact (S01 _ _ Lpx).
    + lia.
    + lia.
    + intros fr7 cs7 A7 m7 vm7 r7 bil nc kx kf spat rng W7 Fz7 S17 PM7 RC7 CL7 CB7 NC7 KI7 KF7 KS7 KG7 Bbil Bnc Bkx Bkf Bsp Brg Dif7 Liv7
        Q1 Q2 Q4 Q10 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q3 RCS7 G8 G9 G18 FS7 AR7.
      rewrite with_vmmaps_twice in W7 |- *.
      destruct (bc4_blk_rng _ _ _ _ _ Bbil ltac:(lia)) as [Rbil Lbil].
      destruct (bc4_blk_rng _ _ _ _ _ Bnc ltac:(lia)) as [Rnc Lnc].
      destruct (bc4_blk_rng _ _ _ _ _ Bsp ltac:(lia)) as [Rsp Lsp].
      destruct (bc4_blk_rng _ _ _ _ _ Brg ltac:(lia)) as [Rrg Lrg].
      assert (SpA : (spat mod 16 = 0)%Z) by (destruct Bsp as (_ & _ & SpA & _); exact SpA).
      assert (Lpx7 : live A7 (Z_to_bv 64 pixs) = Some 64%Z) by exact (S17 _ _ (S01 _ _ Lpx)).
      assert (Px7 : PIXat m7 pixs (set_rc v 2)).
      { pose proof PM1 as [_ LK1]. pose proof PM7 as [_ LK7]. pose proof Px as (P1 & P2 & _).
        eapply (PIXat_rc_set SEGS m m7 pixs 2 v Px).
        - intros x Hx Hnc.
          rewrite (bc4_livkc_pt A1 (pixs + 20) 4 m1 m7 pixs 64 LK7 (S01 _ _ Lpx) ltac:(lia) ltac:(lia) x Hx ltac:(intros ?; apply Hnc; lia)).
          exact (bc4_livk_pt A m m1 pixs 64 LK1 Lpx ltac:(lia) ltac:(lia) x Hx).
        - intros j Hj. refine (proj1 (proj2 (blk_byte C A7 m7 (with_vmmaps vm7 md) (Z_to_bv 64 pixs) 64 _ Cok0 W7 Lpx7 _))).
          rewrite (bc4_u_lit pixs Rpx), (bc4_u_lit (pixs + 20 + j)) by lia. lia.
        - exact RC7.
        - lia. }
      assert (BS1 : (0 <= bsc < 2 ^ 64)%Z) by lia.
      assert (PxB7 : PIXat m7 bsc (hdv (p_w v + 22) (p_h v + 22) 8 0 datasc)).
      { pose proof PM7 as [_ LK7]. eapply PIXat_frame; [exact PxB|]. intros x Hx.
        apply (bc4_livkc_pt A1 (pixs + 20) 4 m1 m7 bsc 64 LK7 LbA1 ltac:(lia) ltac:(lia) x Hx).
        pose proof (exW_blk_apart C A1 m1 (with_vmmaps vm1 md) bsc pixs 64 64 Cok0 W1 LbA1 (S01 _ _ Lpx)) as AP.
        intros Hc. assert (Hne : bsc <> pixs) by (intros E; subst bsc; rewrite LbA in Lpx; discriminate Lpx).
        specialize (AP Hne BS1 Rpx ltac:(lia) ltac:(lia)). lia. }
      eapply (bc_comp_W fr7 cs7 C A7 m7 md vm7 r7 (bc_fl1 regs fr bsc minv maxv) s pixs bsc datasc nc spat rng (p_w v) (p_h v)
        minv maxv bil (set_rc v 2) S (getr regs1 3)); try eassumption; try reflexivity.
      * unfold bc_cst.
        split; [exact HO|]. split; [exact Phdr|]. split; [exact Pw1|]. split; [exact Ph1|]. split; [exact PxB7|].
        split; [exact (S17 _ _ LbA1)|]. split; [exact (S17 _ _ LdA1)|]. split; [exact Rnc|]. split; [exact Lnc|].
        split; [exact NC7|]. split; [exact Hmin|]. split; [exact Hmax|]. split; [exact Rsp|]. split; [exact Lsp|].
        split; [exact Rrg|]. exact Lrg.
      * unfold bc_fl_ok, bc_fl1, bc_saved. cbn [app].
        repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
      * apply (bc4_cincl m7 (s - 320) _ _ CL7). intros c Hc. unfold bc_fl2 in Hc. apply in_app_iff in Hc. apply in_app_iff.
        destruct Hc as [Hc|Hc]; [left; exact Hc|]. cbn [In] in Hc.
        destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
          first [right; cbn [In]; bc4_in | left; unfold bc_fl1; apply in_app_iff; right; cbn [In]; bc4_in].
      * lia.
      * lia.
      * intros fr8 cq8 A8 m8 vm8 r8 pa parr ba barr pixes datad W8 Fz8 INV R8a R8b R8c FR8 AR8.
        destruct INV as (S78 & PM78 & CL8 & PC8 & PB8 & La1 & La2 & La3 & La4 & MEM8 & LIV8 & Dpb & DIS8 & NIN8).
        pose proof Cok0 as [Ctop Csp0 Csp0hi Cal Cimg]. pose proof LSTK_val as LS. pose proof (bc4_u_rng (c_sp0 C)) as Usp.
        unfold BC_WIN in Hwin.
        destruct (bc4_blk_rng _ _ _ _ _ Bkx ltac:(lia)) as [Rkx Lkx].
        destruct (bc4_blk_rng _ _ _ _ _ Bkf ltac:(lia)) as [Rkf Lkf].
        pose proof Bbil as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5 & Bb6).
        pose proof PB8 as (Rpa & Rparr & Rba & Rbarr & Lpa & Lparr & Lba & Lbarr & L0pa & L0parr & L0ba & L0barr).
        pose proof PC8 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
        assert (SA7 : sub_live A A7) by exact (sub_live_trans _ _ _ S01 S17).
        assert (SA8 : sub_live A A8) by exact (sub_live_trans _ _ _ SA7 S78).
        assert (Lbil8 : live A8 (Z_to_bv 64 bil) = Some 104%Z) by exact (S78 _ _ Lbil).
        assert (LAbil : live A (Z_to_bv 64 bil) = None) by exact (bc4_none _ _ _ S01 Bb5).
        assert (FL8 : Forall (fun c : cell => (0 <= c_off c)%Z /\ (c_off c + Z.of_nat (c_len c) <= 320)%Z)
                       (bc_fl2 (bc_fl1 regs fr bsc minv maxv) bil bsc nc ++ [(8%Z, 8%nat, pa)])).
        { unfold bc_fl2, bc_fl1, bc_saved. cbn [app]. repeat (apply Forall_cons; [unfold c_off, c_len; cbn [fst snd]; lia|]). apply Forall_nil. }
        eapply rz_reach; [exact (w_pure _ _ _ _ W8) | exact (bc_U al_rom (mkFP fr8 cq8) r8 m8 s bil pa ltac:(lia) Bb1 ltac:(lia) Rpa
          (bc4_cin m8 (s - 320) _ 16 8 bil (s - 304) CL8 ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
          (bc4_cin m8 (s - 320) _ 8 8 pa (s - 312) CL8 ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
          (exW_sok_blk SEGS C A8 m8 _ bil 104 bil 104 p16_segs Cok0 W8 Lbil8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) R8a) |].
        intros fin (rU & MU & -> & RIU & RDU & U1 & U2 & U8 & U10 & U11 & AGU).
        assert (LRU : local_regions C A8 A s [((bil + 88)%Z, 8%Z)]).
        { apply Forall_cons; [|apply Forall_nil]. right. exists (Z_to_bv 64 bil), 104%Z. cbn [fst snd].
          rewrite (bc4_u_lit bil Rbil). refine (conj Lbil8 (conj LAbil (conj Bb6 _))). lia. }
        destruct (rinv_WP2 C A A8 m8 (with_vmmaps vm8 md) MU [((bil + 88)%Z, 8%Z)] s Cok0 W8 SA8 Htop RIU LRU) as (WU & PMU).
        assert (FKU : bc4_fk A8 m8 MU) by exact (bc4_fk_st C A8 m8 MU (with_vmmaps vm8 md) bil 88 Cok0 W8 Lbil8 Rbil ltac:(lia) ltac:(lia) RIU).
        assert (PM10 : pixa_mem10 C A8 MU parr (p_w v) (wpl_of (p_w v) 8) (p_h v) pixes datad (fun i => hdv (p_w v) (p_h v) 8 0 (datad i))).
        { intros i Hi.
          pose proof (bc4_mem_fk C A7 A8 A8 m8 MU _ parr (p_w v) (p_h v) i (pixes i) (datad i) Cok0 W8 FKU (sub_live_refl A8) Lparr Rparr Hi (MEM8 i Hi))
            as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
          refine (conj _ (conj M10 (conj M8 (conj M13 (conj M12 (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
            (conj eq_refl (conj _ _)))))))))))); lia. }
        assert (RPA0 : rdn SEGS MU (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10)).
        { rewrite (bc4_fk_rdn C A8 m8 MU _ pa 32 pa 4 Cok0 W8 FKU Lpa ltac:(lia) Rpa ltac:(lia) ltac:(lia) ltac:(lia)).
          rewrite Z.add_0_r in C1. exact C1. }
        assert (RPA16 : rdn SEGS MU (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr)).
        { rewrite (bc4_fk_rdn C A8 m8 MU _ pa 32 (pa + 16) 8 Cok0 W8 FKU Lpa ltac:(lia) Rpa ltac:(lia) ltac:(lia) ltac:(lia)). exact C4. }
        refine (pixaGetLinePtrs_W (mkFP fr8 cq8) C A8 MU (with_vmmaps vm8 md) rU (s - 320) pa parr (p_w v) (wpl_of (p_w v) 8) (p_h v) pixes datad
          (fun i => hdv (p_w v) (p_h v) 8 0 (datad i)) (Z_to_bv 64 0x3a53c) S Cok0 WU U2 (bc_msub s 320 16 ltac:(lia) Hal eq_refl)
          ltac:(unfold GLP_WIN, CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity)
          (ag_keep _ r8 rU 4%bv _ AGU eq_refl R8b) U10 U11 Rpa Rparr Lpa Lparr RPA0 RPA16 PM10
          ltac:(destruct Phdr as (_ & _ & P2 & _); lia)
          ltac:(pose proof (wpl_of_range (p_w v) 8 ltac:(destruct Phdr as (_ & P1 & _); lia) ltac:(destruct Phdr as (P0 & _); exact P0)); destruct Phdr as (_ & P1 & _); lia)
          _ _ AR8 ltac:(lia) ltac:(lia) _).
        intros A9 m9 vm9 r9 ls linesf W9 CS9 PM9 R9l LSN AR9.
        rewrite with_vmmaps_twice in W9 |- *.
        destruct LSN as (Rls & LAls & L0ls & L9ls & LU).
        pose proof LU as (LU1 & LU2 & LU3).
        assert (S89 : sub_live A8 A9) by exact (lset_sub C A8 A9 m9 ls (wpl_of (p_w v) 8) (p_h v) linesf datad 10 LU LAls).
        assert (Lbil9 : live A9 (Z_to_bv 64 bil) = Some 104%Z) by exact (S89 _ _ Lbil8).
        assert (SA9 : sub_live A A9) by exact (sub_live_trans _ _ _ SA8 S89).
        assert (S79 : sub_live A7 A9) by exact (sub_live_trans _ _ _ S78 S89).
        assert (SA19 : sub_live A1 A9) by exact (sub_live_trans _ _ _ S17 S79).
        assert (CL9 : cellsAt SEGS m9 (s - 320) (bc_fl2 (bc_fl1 regs fr bsc minv maxv) bil bsc nc ++ [(8%Z, 8%nat, pa)]))
          by exact (bc4_cells_tail C A8 m8 MU m9 bil s _ Cok0 RIU ltac:(lia) ltac:(lia) PM9 ltac:(lia) Htop FL8 CL8).
        assert (RS : forall (o a : Z) (x : word), In (o, 8%nat, u x) (bc_fl2 (bc_fl1 regs fr bsc minv maxv) bil bsc nc ++ [(8%Z, 8%nat, pa)]) ->
                  a = (s - 320 + o)%Z -> rdn SEGS m9 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 x)).
        { intros o a x Hin Ea. rewrite bc_w2b. exact (bc4_cin m9 (s - 320) _ o 8 (u x) a CL9 Hin Ea). }
        eapply rz_reach; [exact (w_pure _ _ _ _ W9) | exact (bc_V al_rom fr8 cq8 r9 m9 s bil ls ret (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (Z_to_bv 64 (u (reg_get fr 8))) (Z_to_bv 64 (u (reg_get fr 9))) (Z_to_bv 64 (u (reg_get fr 18)))
            Fz8 ltac:(lia) Hret H1 Bb1 ltac:(lia) Rls (exW_sok_blk SEGS C A9 m9 _ bil 104 bil 104 p16_segs Cok0 W9 Lbil9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
            (eq_trans (cs_kept_get rU r9 8%bv CS9 cs8) U8) R9l
            (RS 312%Z (s - 8)%Z (getr regs 1) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 304%Z (s - 16)%Z (getr regs 8) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 296%Z (s - 24)%Z (getr regs 9) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 288%Z (s - 32)%Z (getr regs 18) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 280%Z (s - 40)%Z (getr regs 19) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 272%Z (s - 48)%Z (getr regs 20) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 264%Z (s - 56)%Z (getr regs 21) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 256%Z (s - 64)%Z (getr regs 22) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 248%Z (s - 72)%Z (getr regs 23) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 240%Z (s - 80)%Z (getr regs 24) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 232%Z (s - 88)%Z (getr regs 25) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 224%Z (s - 96)%Z (getr regs 26) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 216%Z (s - 104)%Z (getr regs 27) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 208%Z (s - 112)%Z (Z_to_bv 64 (u (reg_get fr 8))) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 200%Z (s - 120)%Z (Z_to_bv 64 (u (reg_get fr 9))) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (RS 192%Z (s - 128)%Z (Z_to_bv 64 (u (reg_get fr 18))) ltac:(cbn [bc_fl2 bc_fl1 bc_saved app In]; bc4_in) ltac:(lia))
            (eq_trans (cs_kept_get rU r9 2%bv CS9 cs2) U2)) |].
        intros fin (frV & csV & rV & MV & -> & FzV & RIV & RDV & V10 & V2 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27 &
          AGV & GV8 & GV9 & GV18 & FRV).
        assert (LRV : local_regions C A9 A s [((bil + 96)%Z, 8%Z)]).
        { apply Forall_cons; [|apply Forall_nil]. right. exists (Z_to_bv 64 bil), 104%Z. cbn [fst snd].
          rewrite (bc4_u_lit bil Rbil). refine (conj Lbil9 (conj LAbil (conj Bb6 _))). lia. }
        destruct (rinv_WP2 C A A9 m9 (with_vmmaps vm9 md) MV [((bil + 96)%Z, 8%Z)] s Cok0 W9 SA9 Htop RIV LRV) as (WV & PMV).
        assert (FK9 : bc4_fk A9 m9 MV) by exact (bc4_fk_st C A9 m9 MV (with_vmmaps vm9 md) bil 96 Cok0 W9 Lbil9 Rbil ltac:(lia) ltac:(lia) RIV).
        assert (FK8 : bc4_fk A8 m8 MV)
          by exact (bc4_fk_trans A8 m8 MU MV FKU (bc4_fk_trans A8 MU m9 MV (bc4_fk_livk A8 MU m9 (proj2 PM9)) (bc4_fk_sub A8 A9 m9 MV S89 FK9))).
        assert (FK7 : bc4_fk A7 m7 MV) by exact (bc4_fk_trans A7 m7 m8 MV (bc4_fk_livk A7 m7 m8 (proj2 PM78)) (bc4_fk_sub A7 A8 m8 MV S78 FK8)).
        assert (PMc : POSTMc C A s (pixs + 20) 4 m MV).
        { apply (POSTMc_trans C A s (pixs + 20) 4 m m1 MV); [exact (POSTMc_of_POSTM C A s (pixs + 20) 4 m m1 PM1)|].
          apply (POSTMc_trans C A s (pixs + 20) 4 m1 m7 MV); [exact (POSTMc_sub C A A1 s (pixs + 20) 4 m1 m7 S01 PM7)|].
          apply POSTMc_of_POSTM.
          apply (POSTM_trans C A s m7 m8 MV); [exact (POSTM_sub C A A7 s m7 m8 SA7 PM78)|].
          apply (POSTM_trans C A s m8 MU MV); [exact PMU|].
          apply (POSTM_trans C A s MU m9 MV); [exact (POSTM_sub C A A8 s MU m9 SA8 (POSTM_mono C A8 (s - 320) s MU m9 ltac:(lia) PM9))|].
          exact PMV. }
        assert (OBJ : bil_obj C A A9 MV bil pixs v (BILW bsc datasc nc kx kf spat rng pa parr ba barr ls minv maxv pixes datad linesf)).
        { unfold bil_obj. cbn [bw_bsc bw_datas bw_nc bw_kx bw_kf bw_spat bw_rng bw_pa bw_parr bw_ba bw_barr bw_ls bw_minv bw_maxv bw_pixes bw_datad bw_linesf].
          split.
          { apply cellsAt_app.
            - apply (cells_keep SEGS bil 104 [(88%Z, 8%Z); (96%Z, 8%Z)] m7 MV); [lia | lia | | reflexivity | exact CB7].
              apply (bc4_bil_win m7 m8 MU m9 MV bil); [| exact RIU | | exact RIV].
              + exact (bc4_livk_pt A7 m7 m8 bil 104 (proj2 PM78) Lbil ltac:(lia) ltac:(lia)).
              + exact (bc4_livk_pt A8 MU m9 bil 104 (proj2 PM9) Lbil8 ltac:(lia) ltac:(lia)).
            - apply (cellsAt_cons SEGS MV bil _ 88 8 pa (bil + 88)); [reflexivity | | ].
              + rewrite (rdn_keep_blk m9 MV (bil + 88) 8 (bil + 88) 8); [| | lia | lia | lia | lia].
                * rewrite (rdn_keep_blk MU m9 bil 104 (bil + 88) 8); [exact RDU | exact (bc4_livk_pt A8 MU m9 bil 104 (proj2 PM9) Lbil8 ltac:(lia) ltac:(lia)) | lia | lia | lia | lia].
                * intros x Hx. destruct RIV as [_ RIV']. apply RIV'. intros r Hr. cbn [In] in Hr. destruct Hr as [<- | []]. unfold inreg. cbn [fst snd]. lia.
              + apply (cellsAt_cons SEGS MV bil _ 96 8 ls (bil + 96)); [reflexivity | exact RDV | apply cellsAt_nil]. }
          split; [exact (bc_blk_ref C A A1 A7 A9 bil 104 S01 S79 Bbil)|].
          split; [exact (bc_blk_ref C A A1 A7 A9 nc 40 S01 S79 Bnc)|].
          split; [exact (bc_blk_ref C A A1 A7 A9 kx 1024 S01 S79 Bkx)|].
          split; [exact (bc_blk_ref C A A1 A7 A9 kf 1024 S01 S79 Bkf)|].
          split; [exact (bc_blk_ref C A A1 A7 A9 spat 44 S01 S79 Bsp)|].
          split; [exact (bc_blk_ref C A A1 A7 A9 rng 1024 S01 S79 Brg)|].
          split; [exact Hmin|]. split; [exact Hmax|].
          split.
          { intros j Hj. rewrite (bc4_fk_rdn C A7 m7 MV _ nc 40 (nc + 4 * j) 4 Cok0 W7 FK7 Lnc ltac:(lia) Rnc ltac:(lia) ltac:(lia) ltac:(lia)).
            exact (NC7 j Hj). }
          split.
          { unfold kidx_ok in KI7 |- *. intros v0 Hv. destruct (KI7 v0 Hv) as (kv & E & R). exists kv. split; [|exact R].
            rewrite (bc4_fk_rdn C A7 m7 MV _ kx 1024 (kx + 4 * v0) 4 Cok0 W7 FK7 Lkx ltac:(lia) Rkx ltac:(lia) ltac:(lia) ltac:(lia)). exact E. }
          split.
          { unfold kfr_ok in KF7 |- *. intros v0 Hv. destruct (KF7 v0 Hv) as (kv & E & R). exists kv. split; [|exact R].
            rewrite (bc4_fk_rdn C A7 m7 MV _ kf 1024 (kf + 4 * v0) 4 Cok0 W7 FK7 Lkf ltac:(lia) Rkf ltac:(lia) ltac:(lia) ltac:(lia)). exact E. }
          split; [eapply PIXat_frame; [exact Px7 | exact (bc4_fk_pt A7 m7 MV pixs 64 FK7 Lpx7 ltac:(lia) Rpx)]|].
          split; [eapply PIXat_frame; [exact PxB7 | exact (bc4_fk_pt A7 m7 MV bsc 64 FK7 (S17 _ _ LbA1) ltac:(lia) BS1)]|].
          split; [exact (bc4_blk_up C A A1 A9 bsc 64 SA19 (conj Pb1 (conj Pb2 (conj Pb3 (conj LbA1 (conj LbA Lb0))))))|].
          split; [exact (bc4_blk_up C A A1 A9 datasc _ SA19 (conj Pd1 (conj Pd2 (conj Pd3 (conj LdA1 (conj LdA Ld0))))))|].
          split.
          { unfold pixa_cells. repeat match goal with |- _ /\ _ => split end.
            all: first [ erewrite (bc4_fk_rdn C A8 m8 MV _ pa 32 _ _ Cok0 W8 FK8 Lpa) by lia; assumption
                       | erewrite (bc4_fk_rdn C A8 m8 MV _ ba 24 _ _ Cok0 W8 FK8 Lba) by lia; assumption ]. }
          split; [exact (conj Rpa (conj Rparr (conj Rba (conj Rbarr (conj (S89 _ _ Lpa) (conj (S89 _ _ Lparr) (conj (S89 _ _ Lba) (conj (S89 _ _ Lbarr)
            (conj L0pa (conj L0parr (conj L0ba L0barr)))))))))))|].
          split; [exact (bc4_none _ _ _ SA7 La1)|]. split; [exact (bc4_none _ _ _ SA7 La2)|].
          split; [exact (bc4_none _ _ _ SA7 La3)|]. split; [exact (bc4_none _ _ _ SA7 La4)|].
          split.
          { intros i Hi. exact (bc4_mem_fk C A A8 A9 m8 MV _ parr (p_w v) (p_h v) i (pixes i) (datad i) Cok0 W8 FK8 S89 Lparr Rparr Hi
              (bc_mem_ref C A A7 A8 m8 parr (p_w v) (p_h v) i (pixes i) (datad i) SA7 (MEM8 i Hi))). }
          split; [exact Rls|]. split; [exact (bc4_none _ _ _ SA8 LAls)|]. split; [exact L0ls|]. split; [exact L9ls|].
          split.
          { intros k Hk. destruct (LU1 k Hk) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
            refine (conj F1 (conj F2 (conj (bc4_none _ _ _ SA8 F3) (conj F4 (conj F5 (conj _ _)))))).
            - rewrite (bc4_fk_rdn C A9 m9 MV _ ls 80 (ls + 8 * k) 8 Cok0 W9 FK9 L9ls ltac:(lia) Rls ltac:(lia) ltac:(lia) ltac:(lia)). exact F6.
            - unfold lp_rows in F7 |- *. intros i Hi.
              rewrite (bc4_fk_rdn C A9 m9 MV _ (linesf k) (8 * p_h v) (linesf k + 8 * i) 8 Cok0 W9 FK9 F2 ltac:(lia) F1 ltac:(lia) ltac:(lia) ltac:(lia)).
              exact (F7 i Hi). }
          exists A1, A7, A8.
          refine (conj S17 (conj S78 (conj S89 (conj LbA1 (conj LdA1 (conj Pne (conj Bbil (conj Bnc (conj Bkx (conj Bkf (conj Bsp (conj Brg (conj Dif7
            (conj La1 (conj La2 (conj La3 (conj La4 (conj PB8 (conj Dpb (conj _ (conj DIS8 (conj LAls (conj _ (conj LU3 NIN8)))))))))))))))))))))))).
          - intros i Hi. destruct (MEM8 i Hi) as (_ & _ & _ & _ & _ & M6 & M7 & _ & _ & M10 & M11 & _). exact (conj M6 (conj M7 (conj M10 M11))).
          - intros k Hk. destruct (LU1 k Hk) as (_ & _ & F3 & _). exact F3. }
        assert (FRMb : bil_frame A A9 bil (BILW bsc datasc nc kx kf spat rng pa parr ba barr ls minv maxv pixes datad linesf)).
        { intros q Hq Hi. cbn [bw_bsc bw_datas bw_nc bw_kx bw_kf bw_spat bw_rng bw_pa bw_parr bw_ba bw_barr bw_ls bw_pixes bw_datad bw_linesf map In] in Hq, Hi.
          rewrite (LU2 q ltac:(intros E; apply Hq; subst q; bc4_in) ltac:(intros k Hk; exact (proj2 (proj2 (Hi k Hk))))).
          rewrite (LIV8 q ltac:(cbn [map In]; intros HH; apply Hq; tauto) ltac:(intros i0 Hi0; exact (conj (proj1 (Hi i0 Hi0)) (proj1 (proj2 (Hi i0 Hi0)))))).
          rewrite (Liv7 q ltac:(cbn [map In]; intros HH; apply Hq; tauto)).
          apply Loth; intros E; apply Hq; subst q; bc4_in. }
        refine (K1 frV csV A9 MV vm9 rV bil (BILW bsc datasc nc kx kf spat rng pa parr ba barr ls minv maxv pixes datad linesf) WV FzV _ SA9 PMc V10 OBJ FRMb _ _).
        { apply cs_kept_intro.
        - rewrite V2, Hsp; reflexivity.
        - rewrite (AGV 3%bv ltac:(notin_lit)), (cs_kept_get rU r9 3%bv CS9 cs3), (AGU 3%bv ltac:(notin_lit)), R8c. exact (RCS1 3%bv cs3 ltac:(notin_lit)).
        - rewrite (AGV 4%bv ltac:(notin_lit)), (cs_kept_get rU r9 4%bv CS9 cs4), (AGU 4%bv ltac:(notin_lit)), R8b, H4. reflexivity.
        - rewrite V8. reflexivity.
        - rewrite V9. reflexivity.
        - rewrite V18. reflexivity.
        - rewrite V19. reflexivity.
        - rewrite V20. reflexivity.
        - rewrite V21. reflexivity.
        - rewrite V22. reflexivity.
        - rewrite V23. reflexivity.
        - rewrite V24. reflexivity.
        - rewrite V25. reflexivity.
        - rewrite V26. reflexivity.
        - rewrite V27. reflexivity.
        }
        { intros r Hr.
          destruct (bv_eq_dec _ r 8%bv) as [->|N8]; [rewrite GV8, Z_to_bv_bv_unsigned; reflexivity|].
          destruct (bv_eq_dec _ r 9%bv) as [->|N9]; [rewrite GV9, Z_to_bv_bv_unsigned; reflexivity|].
          destruct (bv_eq_dec _ r 18%bv) as [->|N18]; [rewrite GV18, Z_to_bv_bv_unsigned; reflexivity|].
          destruct (bc4_fs12 r Hr) as (N12 & N13 & N14 & N15).
          rewrite (FRV r (fs_notin_V r N8 N9 N18)), (FR8 r N8 N9 N12 N13 N14 N15 N18), (FS7 r Hr N8 N9 N18). exact (FS1 r Hr N8 N9). }
        { match type of AR9 with aroom _ _ ?k ?b =>
            replace (kR - RK_bc)%Z with k by (unfold RK_bc; lia); replace (bR - RB_bc (p_w v) (p_h v))%Z with b by (unfold RB_bc; lia) end.
          exact AR9. }
Qed.
End BilCW4.
