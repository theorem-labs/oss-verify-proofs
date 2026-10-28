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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptPixCreateT2 V2LeptPixCopyTR V2LeptPixaCreate V2LeptLinePtrs V2LeptBl_iface V2LeptBilSegs V2LeptBilCW1 V2LeptBilCW2 V2LeptBilCW3 V2LeptBilCW4 V2LeptBilApW V2LeptBilD_iface V2LeptBilGrayRun.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2LeptBilGrayW () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8WalksLib9rostr_chkI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C7ARocqVerifyHarness?AgentSubmission6Common9Leptonica8SumSpecs3SSP9rostr_winC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00C5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB4cellI47Corelib5Lists7ListDef6Forall00C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:asr_callocI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4lctx00C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc8aic_baseC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase2ASK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bil_objC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilD_iface:bil_blocksC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW46bw_bscC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_minvC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_maxvC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_ncC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_kxC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_kfC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_spatC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW46bw_rngC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW26bc_bl2I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_paC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_lsK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB7cellsAtC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW26bc_blkC56Stdlib6ZArith6BinInt1Z3mulC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptArithB6nc_valC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilSegs7kidx_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6set_rcC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW48bw_datasC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_parrC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_baC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_barrC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptPixaCreate9pixa_blksC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_wC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_hC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW48bw_pixesC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW48bw_datadC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW36bc_memC56Stdlib6ZArith6BinInt1Z3powC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase4liveC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW49bw_linesfC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW49bil_chainC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptPixaCreate:pixa_cellsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_A0C56Stdlib6ZArith6BinInt1Z6moduloC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List2InC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith6wpl_ofC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptLinePtrs7lp_rowsC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPixCopyST3hdvC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5PIXatI47Corelib4Init5Logic2ex00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_vmC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topK47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2or00I47Corelib4Init5Logic5False00I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs4pixv00I5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW44bilw00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C45stdpp9bitvector;definitions9bv_eq_decC46Stdlib5Lists4List6in_decI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z6eq_decK46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op201C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24ridxC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula02C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecB7fs_listK47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega:ZMicromega;ZArithProof01I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3Cok00C5ARocqVerifyHarness?AgentSubmission6Common7FPSteps8frm_zeroC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_topC5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixHdr6hdr_okC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure5aroomc5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilGrayW5RB_bgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs7cs_keptC4ELinuxProcessSemantics5Riscv3Sem7reg_getC56Stdlib6ZArith6BinInt1Z3subK5ARocqVerifyHarness?AgentSubmission6Common8PropExec7FPState01C5ARocqVerifyHarness?AgentSubmission6Common:AllocIface6al_romC5ARocqVerifyHarness?AgentSubmission2V2AV2LeptPixCreateT28pixr_newC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_sp0C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6ll_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_img64C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ro_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_roC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_lg_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_lgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ag_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_agC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=pin_errno_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_errnoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_hcellC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3inZC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_hcellC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;pin_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:ll_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs<pin_ro_belowC4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr07I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6pix_wf00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs9pix_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8bytes_atC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecW;exW_blk_rngC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL>RB_pixT_nonnegC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL7RB_pixTC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs9PIX_rd_rcC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs;PIX_rd_cmapC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8PIX_rd_dC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase9W_sok_winC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilGrayRun5gr_A1C5ARocqVerifyHarness?AgentSubmission6Common5Hoare:regs_agreeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=sub_live_reflK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptCmapArr8rinv_WP2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB5c_offC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB5c_lenC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB5c_valc5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilGrayW8gr_savedC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilGrayRun6gr_A1bC5ARocqVerifyHarness?AgentSubmission6Common8FPStepsV<fpv_get_sameC5ARocqVerifyHarness?AgentSubmission6Common8FPStepsV=fpv_get_otherC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilGrayRun5gr_A2C5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilGrayRun6gr_A2bC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilGrayRun5gr_A3C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LIVKC5ARocqVerifyHarness?AgentSubmission6Common7StepTac6u_Z2bvC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots9LIVK_byteC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs;PIXat_frameC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith4dvalC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_xresC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_yresC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_dC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_cmapC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5p_wplC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_dataC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBl_iface6bl_srcC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface<callee_savedC47Corelib4Init5Logic7and_indc5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilGrayW:fs_notin_gC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW3<RB_it_nonnegC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW35RB_itC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure?alloc_margin_geC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure<alloc_marginK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBl_iface6RB_ambC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45RB_bcC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec6v_jalrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs4p_rcC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8sub_liveC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB<agree_of_FRMC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB9agree_winC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB:cells_keepC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW19W_clr_gotC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW19W_clr_sevC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilGrayRun5gr_BnC5ARocqVerifyHarness?AgentSubmission6Common7StoreOk9mem_growsC47Corelib4Init5Logic6eq_symC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=cs_kept_introC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:POSTM_monoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;POSTM_rangeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9POSTM_subC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;POSTM_transC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8WalksLib8zbv_selfK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:aroom_monoC5ARocqVerifyHarness?AgentSubmission2V29V2LeptErr@returnErrorPtr_WC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB6POSTMcC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW49bil_frameC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB5LIVKcC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilGrayRun4gr_BC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB=agree_of_rinvC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB<cellsAt_consC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilApW=rinv_scr_keepC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW4<bil_obj_keepC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB?POSTMc_of_POSTMC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB;POSTMc_monoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB<POSTMc_transC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixHdr7pix_hdrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8set_dataC47Corelib4Init5Logic8eq_transC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilGrayRun4gr_CC5ARocqVerifyHarness?AgentSubmission6Common8VmLedgerAwith_vmmaps_twiceC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW3<cellsAt_tailC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW3>agree_win_joinC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilGrayRun4gr_Dc5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilGrayW@bil_blocks_factsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB:POSTMc_subC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs=PIXat_definedC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilD_iface?POSTM_of_POSTMcC5ARocqVerifyHarness?AgentSubmission6Common8VmLedgerBwith_vmmaps_vmmapsc5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilGrayW>bil_blocks_decC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecW=exW_blk_apartC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB>agree_of_LIVKcC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW38sub_noneC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilApW@bilateralApply_WC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW4AbilateralCreate_WI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs1W00C5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPixCopyTR3hdvC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5POSTMK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9DitherLib4rinvC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6w_pureC46Stdlib9micromega;ZifyClasses6mkapp2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3FRMC47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List9nth_errorC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB;cellsAt_nthC5ARocqVerifyHarness?AgentSubmission6Common5Reach8rz_reachC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom6roomtrC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase5LLU16C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LSTKI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45RK_bcI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSetc5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilGrayW6BG_WINc5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilGrayW5RK_bgI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8LSTK_valC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64I47Corelib4Init5Logic4True00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW35RK_itC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom6RK_pixc5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilGrayW:str_gr_msgc5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilGrayW;str_gr_procC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase3LSFK47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomPC:RK_pixcopy".
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Lemma str_gr_msg : str16 73322 12.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilGrayW ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;3p;2p;4p;7p10000p4p70R0p1000`p4p710R1p8P0p1001<p4p710R0p8p1001Zp4p70R2P1p8P2P0p8p1002Hp4p7210P0p8p10034p4p70R2P1p8P2P0p8g003jj10Tg004Oj11Tg0054j15Tg005Rj3LTg006Zj3=Tg0074j26Tg007Pj27Tg007kj2ATg0097j2<Tg009Tj2?Tg009nj1OTg00:Nj1NTg00:nj1MTg00;Lj1KTg00;jj1HTg00<Uj2>Tg00=8j3ETg00=[j2DTg00>=j2CTg00>ij3FTg00?Hj4GTg00@:j4BTg00@Uj4ITg00A@j7JTg00Adj7@Tf0R0#0#0p=2%10#0p=:%00#0#0#0p=4g00BHR2/>0p=3P2f1R1g00BfP0CIp=8P1g00CMR3g00ClR4P4g00DLR5P0g00DlFJp=9f2R6P3P4P4P5P1P0F@p=;g00ELR4g00Elg00G>R3#0#2#1#1#1#1#2#1#:#:#:#5R7%13#2R8#5R93Lg00GcR:3=R;g00HCR</69%:8#2#5R8,69'7R=%03R>#0#2#4#4#4#5R?/67R@1A79,<7%03#2#1#2#4#4#4#5R3'6'7'71?4:RAP;dg00HaR;#O%N;%M2%K2%H2R;1>2<%39R9'8,9;%38,89,9;5;;%3?%37R?'8,9;%1>#2#5R>#39E2?%33'8,9;5;;3;1D;5P0P6PA1C06==4:dAF2<1CGb1b2b31<7>/63,7@,7=P0b0CBo"). Qed.
Lemma str_gr_proc : str16 68782 16.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilGrayW ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;3p;2p;4p;7g004Oj11Tg003jj10Tg0054j14Tg005Rj3FTg006Zj3<Tg0074j26Tg007Pj27Tg007kj2@Tg0097j2;Tg009Tj2?Tg009nj1>Tg00:Nj1NTg00:nj1MTg00;Lj1LTg00;jj1ETg00<Uj2=Tg00=8j3CTg00=[j2BTg00>=j2DTg00>ij3ATg00?Hj4GTg00@:j4HTg00@Uj4ITg00A@j7JTg00Adj7KTf0R0#0#0#0#0p=2%00#0p=5g00BHR1/=0p=3P1f1R2g00BfP0CIp=8P2g00CMR3g00ClR4P4g00DLR5P0g00DlFJp=9f2R6P3P4P4P5P2P0FKp=:g00ELR4g00Elg00G>R3#2#1#1#5#1#0#1#0#1#1#1#0#4R7%23R8#4R93Fg00GcR:3<R;g00HCR</69%13#5R=#1#0#5#4R>,69'7R?%28#2#2#4R8/67R@1@79,;7%03#5#1#5#2#2#2#4R3'6'7'71?4:RAP;dg00HaR;#>%N;%M1%L1%E1R;1=1<%39R9'8,9;%3>,89,9;5:;%38%37R8'8,9;%0=#4R=#39C18%33'8,9;5:;3:1B;5P0P6PA1D06=<4:dAA1<2CGb1b2b31;7=/63,7@,7?P0b0CHo"). Qed.

Section BilGrayW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Existing Instance exf_fxd | 100.
Hypothesis H_amb : forall fx : FPState, @pixAddMirroredBorder_contract fx AL CL ASR.
Hypothesis H_gev : forall fx : FPState, @pixGetExtremeValue_contract fx AL CL ASR.
Hypothesis H_bd : forall fx : FPState, bilateralDestroy_contract (fx := fx).

Definition BG_WIN : Z := 64 + BC_WIN.
Definition RK_bg : Z := (RK_bc + RK_pixcopy)%Z.
Definition RB_bg (w h : Z) : Z := (RB_bc w h + RB_pixT (4 * (wpl_of w 8 * h)))%Z.
(* [comment removed for export] *)
Definition gr_saved (regs fr : bvmap 5 word) : list cell :=
  [(56%Z, 8%nat, u (getr regs 1)); (48%Z, 8%nat, u (getr regs 8)); (40%Z, 8%nat, u (getr regs 9)); (32%Z, 8%nat, u (getr regs 18));
   (24%Z, 8%nat, u (Z_to_bv 64 (u (reg_get fr 8)))); (16%Z, 8%nat, u (Z_to_bv 64 (u (reg_get fr 9))))].

(* [comment removed for export] *)
Lemma bil_blocks_facts : forall C A Af (m : word -> option byte) bil pixs v b (q : word), bil_obj C A Af m bil pixs v b -> bil_blocks bil b q ->
  live A q = None /\ exists n, live Af q = Some n.
Proof.
  intros C A Af m bil pixs v b q OB BQ. unfold bil_obj in OB. unfold bil_blocks in BQ.
  destruct OB as (_ & (_&_&_&Lbil&Nbil&_) & (_&_&_&Lnc&Nnc&_) & (_&_&_&Lkx&Nkx&_) & (_&_&_&Lkf&Nkf&_) & (_&_&_&Lsp&Nsp&_) & (_&_&_&Lrg&Nrg&_) &
                  _ & _ & _ & _ & _ & _ & _ & (_&_&_&Lbsc&Nbsc&_) & (_&_&_&Ldat&Ndat&_) & _ & (_&_&_&_&Lpa&Lparr&Lba&Lbarr&_) &
                  Npa & Nparr & Nba & Nbarr & MEM & _ & Nls & _ & Lls & LF & _).
  destruct BQ as [BQ | (i & Hi & BQ)].
  - cbn [map In] in BQ.
    repeat match type of BQ with
      | False => destruct BQ
      | _ \/ _ => destruct BQ as [BQ|BQ]; [subst q; split; [assumption | eexists; eassumption] |]
      | _ = q => subst q; split; [assumption | eexists; eassumption]
    end.
  - destruct (MEM i Hi) as (_&_&_&_&_&Np&Nd&_&_&Lp&Ld&_). destruct (LF i Hi) as (_&Ll&Nl&_).
    destruct BQ as [BQ|[BQ|BQ]]; subst q; split; first [assumption | eexists; eassumption].
Qed.

(* [comment removed for export] *)
Lemma bil_blocks_dec : forall bil b (q : word), bil_blocks bil b q \/ ~ bil_blocks bil b q.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilGrayW ()) ["BilGrayW"] "p'0h01ii001ih11Hh24__x1h32Hih42Pih52H0h67__arithh74__ffh88__varmaph95__with:4__x2h;1ni011nh<1xi021xh=1Xh>4cstrh?1dh@3Hi0hA1IhB2NOhC4__p1hD1ohE1si031shF1DhG2E1hH2E2hI2E3hJ2IHhK2N1hL2N2hM2N3hN2NEhO2NIhP3NPnhQ1PhR2PDhS2PnhT2_HhU1bhV3bilhW1ei041ehX1qhY1yp%0p&0p;1p;4p;3p;2p;6p;8p;<p;7g003jj1GTg00OKk10PTg00Oik10:Tg01Dbj1zj3[Tg00imk10Oj2CTg009nj1oTg01EJj4yTg016Rj3dTg01;`j10Tg01EeR0j2UTg004Ok10ITg0054j1lTg01@jR1j25Tg007PR2j23Tg01FEj3?Tg006Zj37Tg00n<j2FTg01F_j3BTg01G9j2rTg01GXj6qTg01H4R3j12Tg017oR4j29Tg009Tj2NTg01HTj3ZTg01I:k10NTg01IXj6XTg01JAj4pTg00:Nk10HTg01Jhj2nTg00;Lk10FTg00;jk10ETg00<Uj2kTg01KFj2jTg00@Uj4_Tg00jSk10DTg01Kik60CTg00=[k20BTg00>=k20ATg00>ik30@Tg00?Hk409Tg00[`R5j1<Tg0097j2ITg01LMj1\Tg00:nk108Tg01M2k403Tg00=8j3gTg01MPj4fTg00@:j4QTg01@Pj4RTg01N;k202Tg001<k801Tg01N[k600Tg01O?j4}Tg00Qjk305Tg00Rmj1|Tg00e<k106Tg00\_k107Tg00f9j1{Tg00g5k10;Tg00gok10<Tg00]Yj1xTg00^Sj3:Tg00VZk10=Tg00WTj1wTg00XNk10>Tg00YJk10?Tg00U`j1hTg0166j4iTg0074j2vTg011Tj2mTg00m?j2`Tg01>;R6k20GTg01O`l<bTg01PEm<0JTg00A@j7sTg00Adk70KTg01Pjk80LTg00BHR7f7R8#|f6R9$06f5R:$07f4R;#{f3R<$0;f2R=$0<f1R>#xf0R?5:75:75:75:75:75:73:p==&0=;%w<&0>=&0?>=:7?5:75:75:7p=@%h>=:7?p>04P7P<P=A:7>?Cip=~P7P;P<%h>=:7?9:7=Ci9d9:p=Ag00HCR@/v?p=>19>?,3=p=11m>?,C=97;<p=61F=>,C<97:;/5?p=;1`=>,C<97:;/5?,39p=E20G7?p=4%0?,5>p=81`>?,C=p=HA7<=>/5?p=J1`>?,C=97;<p=L1C>?97<=p=O15>?,5=p=u1F>?,C=p=t1m>?,C=p=aA7=>?,5<p=c1N7?p=Mg01CdRAP7P7P7P3P3P<P=P>g01DCRBP@P?M<bp>0MP7P7P4P8P4P9P:P;P<P=P>P?N<0Jp=YP>g00CMR4g00ClRCPCg00DLRDP?g00DlFsp=KP7P>g01QNP?C_p=VP=P4PCPCPDP>P?K0Kp=WP<P4PCPCPDP=P>P?L0Lp=T%2>,9=,3</3?p=D13=>/3?p=SPAPAP7P7P5P3P3P<g01R5P=P>P?M<bp=^PAP7P7P7P3P3P:P;P<P=P>P?M<bp=]%<?#2p=e%<?#<p=Pg01Big00G>R3#GR5#G#G#G#G#G$0PRE$0:RFPF%zEP?PF&0OERGP=P>P>P>P>P>P>P>P>P>P>P>%o7RHG=D@-04>C~RICyAdF?IRI%0I'UP0PFP>PFPGP<P=P=P=P=P=P=P=P=P=P=P=P=PHG=D@FARI%0IPFP=PFPGP;P<P<P<P<P<P<P<P<P<P<P<P<PHG=D@FARI%>?RJ&0I5#G#lRK71?RLPFP<PEP;P?PFP<PEP;P?PFP<PEP;P?D6E;FEX07#4'5RM/8MP?PFP<PFPGP:P;P;P;P;P;P;P;P;P;P;P;P;PHG=D@FARMPFP;AHE:?PFP;PEP:P?PFP;PEP:P?D6E;CJRN,3LX07#4RO'5RP%0PA?MO?3?XAIP?O1%0IPNX07p-0RN^07AHE9?RI9[E:A7F:IRI%0I'UP0PFP9PEP8P>DLRI%0IPFP8PEf8RIP=DLROPFP8PE1FI=COPFP8PEPIP=D63uRM/8MP?PFPIPEf9RMP<DLRPAtEM<RQ97FIRRPFPIAaEM<CcRS'5RT%0TA?PS?3?XGOP?O1%0OA[EIQ%0R,URP0PFPMPEf:RR/F;CORQ%0QPFPRf;RQ=HE:PFPRPE1FQ:COROPFPRAaEQ:CcCJRS/8SP?PFPQPEf<RSP9DLRPPFPQPE1FS9CORTAaES9RU97FQRV'5RW'5RX%0XA?TV?9BPW3?XHOP?O1%0OA[EQU%0V,UVP0PFPSPEf=RVP8D6RU%0UPFPVf>RU=HEIPFPVPEPUPIPFPVPEPUPID6ROE;CJRW/8WP?PFPUPEf?RWPMDLRPPFPUPE1FWMCORTPFPUPEPWPMD6RX'5RY'5RZ%0ZR[ABTX?9BPY3?XIOP?O1%0OPFPWPEf@ROPRDLRYPFPWPEPOPRPFPWPEPOPRD6E;RPg01ADRXPSfBRTO1PNPMP>O1S00PX1rX?R\b1b=X5YPFPOPEfARY/FQCOR]PFPOPEPYPQD6R^PXPVfCR_O1R`PNP8P>O1RaPXP\b5b=X1]P`PNP;P>O1PXP\b5b=X1^P?EqX5PP?EqX1ZP[e9BZ[WMP?O1n200110300021110411101b?WLP?O1n200110300021110411101b?WKP?O1n200110300021110411101b?P>P?O1R[/8[R[eX07P[^07%2>91J?R[P;P?O1RZ'3X07#4RP/8PRPX;A%2BR^91J?R\P<P?O1R`'3X07#4R]%0]RbP6P713\ZX07PXP?P9P?O1Rc,3\P2%>>R\?1>^PaPXP?%><Ra?1<^PRP;O1%>:Rd19:^Re'3A1d:@RfPdPePdP?X<7ReP@O1Rg,9:1NNdRhA7Ndde9ZddPe19>?$0NXY7X<7RiP:P:%M:RjP^PgPePe%2?#MX<ARg1N7@H0MGYEXP>CpPfg00HaRf#oR^&0HfRf1n7>S01&0F7Rk&0E7RlP71k7@Rmg00Bf1j73RnC_,KlRo1Vnm,Kl5Wl&0DCRmPlP4PCPCPDP<J0CCT20BlDRpP?P=g00ELRqg00GcRr'N20A?==7qrdB0@7@>H09Rrb7b8b9X27XCNA1J?@P=[^27^CNP?PXP8P>O3b6b@WTW3P>P?O2n2001000000121000000W1X07P>P?O2n2001000000121102000X1]Pbe3BP1PJP?P=P:P?O1RbCDX07#4R]%0]PJP?%<<PcCDX07#4R]/8]P?%2<R],9?=SJcX07#4R@P6P7%2;Rq,9?P8P?O15SJX07PJP?%<:PIP?O1RsCDX07#4Rt/8tP?%29Rt,9?PMP?O1Ru5SJP2%2891\>PRP>O1PJP?%<MPSP?O1CDX07#4Rv/8vP?%2M91a<PVP;O1PJP?%<SPWP?O1CDX07Rv#4Rw%0wP7PvP:%<QRv#2Rw,9:Rx,3dRyPUP:O1Py%2QRy%l3R3'IRz,9:R{,3dPdPxPdP{AZddhPePiP:P:PjPwPzPePePgPvPz1I?3X<7RzPQPy%MyC^E]GYEX%\Q%>yP^PfP71n7=P>&087H03RyPkPl1j75R5,Vn,Kl9WloS02Pm1k73Rv9g75,Vn,Kl9WloRjCTPpPrb7b8b9X27X:7A1J?>1I=391\>[^27^:7P?%2VP8P<O3b6b>CfP?CQCR3?W4W3P>P?O2n2001000000121000000W1X07P>P?O2n2001000000121102000W1P?O1%0@P:P]O1P9P]O1R]/8]P1P8PqO1Rq%0q%<9Rq#2R],9?=SJuX07#4R@/8@P?PI%2:O1R@PJP?%<8PRP?O1CDX07Rh#4R{%0{RxP7PhPt%>tRh19t]R|'3R}PMPtO1P}1It3R},9tR~,3hPhP|PhP~1NNh9ZhhPePiPtPt%MtR~P]P}PePePgPqP}PzP9PtP~C^E]GYEX%\9PhP^PfQ01PkPlPoPmAg7nv,Vn,Kl9WloCTPpPrb7b8b9X271I>3Ro91\>\J^27P?%2IP>O2b6b>CfP?CQCR3?WSP?O1%0@P6P7PJP?%<IPQP?O1CDX07PXP?PJP?%<RPVP?O1CDP2A1\>wPUP>O1PXP?%eV91a<PYP;O1%2WRw-02:A77:wRw%0w'UP0%2O9779R9%09PXP?%2Y9778R8P7%2TR9%e_91J?fGP>O1PX]4]3X07%>9%<TR0#2Rw719fFR@%2_RvO1PUP?O1W4W3PIP?P;P<L01WWP?O1%08PWP719?vP@P?O15SJX07PI%>IR@?1I9fER8PIO119IwRh,3@1I9391@IR3P@PhP@PePzP9O1RhO1R~,9I1NN@A7N@@e9Z@@PePiPIPI%MIPwP~PePePgP0PhPzPTP9%M9C^E]GYEXP;CpP3%\_%>vP^PfPyPkPlPjPmPlPlP4PCPCPDP7Png01RYP5C_,KlJ00PmQ02CTCTPpPrb7b8b9X27X:7A1J?oA77>=PX[%>=?1=<[[^27^:7P?%28PQP=P<O4b6b>b@P<CQCRO1WNP?O1n200110300021010411101bEW4W3P>P?O2n2001000000121000000W1X07P>P?O2n2001000000121102000X1{Pxe9B{xWPP?O1n200100000021100011000bDWBP?O1n200100000021100011000XJPX;AP?C}X;A13[`X07#4R[/8[^;AP?%PB#P#P#P#PRBO1%2BRB91J?RJ/3`X07#4R`/8`P113JZX07#4RZ%0ZPFPIPFPGPRPMPMPMPMPMPMPMPMPMPMPMPMPHG=D@FAPLPFPMPEPRP?PFPMPEPRP?PFPMPEPRP?D6E;FEX07#4'5RI/8IP?13JbX07#4RbP6P713JcX07PFPRPFPGPSPQPQPQPQPQPQPQPQPQPQPQPQPHG=D@FARcPLPFPQPEPSP?PFPQPEPSP?PFPQPEPSP?D6E;FEX07#4RI'5RZ/8ZP?13JsP2A1\>BQ00PFPUPFPGPOPWPWPWPWPWPWPWPWPWPWPWPWPHG=D@FAPLPFPWPEPOP?PFPWPEPOP?PFPWPEPOP?D6E;FERWX07#4'5Rs/8sP?A1a<BPSP;O1PFPYPFPGP_PTPTPTPTPTPTPTPTPTPTPTPTPHG=D@FARsPLPFPTPEP_P?PFPTPEP_P?PFPTPEP_P?D6E;FEX07RZ#4R`'5RA%0AP7PZP:A1d:KPFPYAHET:PFPYPEPTP:PFPYPEPTP:D6E;CJP>P?CQCR9Bs`3?W4W3P>P?O2n2001000010121000000W1X07P>P?O2n2001000010121102000W1P?O1%0bPFPMPFPGPQPRPRPRPRPRPRPRPRPRPRPRPRPHG=D@FAPLPFPRPEPQP?PFPRPEPQP?PFPRPEPQP?D6E;FEX07#4'5RR%0RRMP1PcPIPXP?PFPQPFPGPVPSPSPSPSPSPSPSPSPSPSPSPSPHG=D@FAPuWAP?O1PLPFPSPEPVP?PFPSPEPVP?PFPSPEPVP?D6E;FEX07#4P6P7PLPFPVPEPUP?PFPVPEPUP?PFPVPEPUP?D6E;FEX07PXP?P2A1\>KPFPOAHEY>PFPOPEPYP>PFPOPEPYP>D6E;CJPXP?A1a<KPFP_fDRa=HE;PFP_PEPaP;PFP_PEPaP;D6E;CJPQP7PYP?O1,3JX07P:A1d:BPOP:O1P>P?CQCRO1W4W3P>P?O2n2001000000120000000X1WX07P>P?O2n2001000000121102000W1P?O1n200100000021000011000X1RPMe3BWBP?O1n200100001021100011000bDbFbRbQWOP?O1n200110301021110011101bEB05=>?R?/8?eWXWUXV7o"). Qed.

(* [comment removed for export] *)
Lemma fs_notin_g : forall (r : reg) (L : list nat), In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> (forall x, In x L -> In x [8; 9; 10; 11; 14; 15]%nat) -> ~ In (ridx r) L.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilGrayW ()) ["BilGrayW"] "h02H0h14__p1h24__p2h34__x1h44__x2h51Eh62E0h73H17h87__arithh94__ffh:8__varmaph;5__with<3z17h=1xh>2HLh?2b1h@2b2hA1nhB1HhC2HrhD1LhE2N8hF2N9hG1XhH1rhI1yp&0p;1p;2p;3p;4p;5p;<p;6p;7p;8g003jj1?Tg004Oj1=Tg00OKj1tTg00Oij1HTg00:Nj1gTg01S@j21Tg016Rj3OTg0054j15Tg01Sjj2]Tg01TMj3STg006Zj34j1\Tg01;`j1VTg00[`j17Tg009nj1hTg01U0j1eTg01V7k207Tg0074j2dTg01Vjk102Tg017oj2`Tg007PR0j26Tg01WSR1j1:Tg01X3j3nTg01H4R2j1fTg01XWj2jTg01Y:j3iTg01JAj4LTg01@jR3j23Tg01YWk10:Tg01Z5k209Tg01ZVj2UTg01[?j3YTg01[hj2XTg00:nk108Tg01Jhk206Tg01M2k405Tg00;Lk104Tg00;jk103Tg01KFj2bTg00<Uj2ZTg00jSj1zTg01\Tj5yTg00=[j2wTg009Tj2^Tg00>=j2sTg00>ij3rTg00?Hj4qTg00^Sj3DTg01]8j2|Tg01O`l<}Tg01PEl<~Tg01]Uj2mTg01^7k300Tg01Kik601Tg00@Uj4WTg00A@j7QTg00Adj7lTg01^`j7TTg01Pjj8kTg01CdR4f1R5f0R63Dp=KA4456p=2A4456g01ADR7'3p=Nf4R8f3R9544f2R:=445/36'3p=Cg00BHR;?456p=0g00HCR</|6p=91^;6p=<P;P4P;P;P1P8P2P9g01_DP:P5P6M<}p=GP4P;P6P2P5P:P9P8f5R2f6R1f7R=f8R>M<~p=F1m<6p=M1`<6p=>1d6<p=;A4;6<p=EB00;56p=Ig00HaR?AD?569D?:9D?97D8p=BP5g00CMR@g00ClRAPAg00DLRBP6J01p=cP:P@PAPAPBP;P5g01RYRCP6CWg00DlRDFQp=AP:P@PAPAPBP5P6Flp=aP:P@PAPAPBP5P6FTp={1Z;6p=JP;P5PCP6CWp=_P8P@PAPAPBP9P@PAPAPBP;1Z;:PCP5CWPDFQP6FTp=@P1P@PAPAPBP2P@PAPAPBP8PDFQP9P@PAPAPBP:P@PAPAPBP5PDFQP6FTFTp=xP9P@PAPAPBP:P5P6Gkp=81367p=uA4;:5/36p=vA4;89A4;:5/36'3p=R1356,3:p=pA449:A4456/37'3p=PAD?56p=[AD?569D?:p=og00G>RD#?RC#=RE#tRF#HRG%g411F5g01`15O;%?CRC#?#5RHg01a8RI1]FHd5SF94G:#V%=CRC#5RJPI1]FJd5SF94G9#VAO468g01DCRG#7RK#7RL#7RM#7#7#7#7#7RN%7NRO%7ORP%7PRQ%7Q#7#7RR%7RRS%h4'K'K'K'K'K'KRT9O45[^=4%e2=O48RUP5%e1R1P6O2AO41T207F=11F=R1,d<&02F,`1'6P311F>#:R1,2NPOP1PPP1PQP1PRP11NS1DCDCP7P5f9,1F#:R1,2NP=g01aTR=%H6RT%H5RVP0%H:?456119:1195'0R0[11:511:6'0%H9?4:5[RW%H8?49:\0An:56P6n2001000000120000000W@W?WAR0PW^@V^?T^A=R=P6PFf;RTASFHIRV11FTRW#:RX,2N%9W,0HRY%\4RZ%\;R[%f5%f6'012561j563iXI4X=4R4PNPH%<HPX%96X=;RNPWO1P6X=;R\PNPWPW%<WDGM9FP5CLPYf<,1FRY#M%>Y%9YRW/0Y'6%;Y%EW'6'3f=RW,1FR]#9R^P;p-0R_&0:D-09;R`1U;MRM5Y;Ra1U;LRL9Y;`Rb1U;G'I'Ig01b2RG'XRcPcPcPcPcPcPcPcPcPcPcPc%h?RdDBDBDB%g?R?P;&08;P5206;:H05Re&04;Rf&03;Rg1cg8%=DR8,b;Rh1b;DRD5Ag5ag1cg21Z;<9Agh5ag5{gR2%zARiPg%JHRj=AghPiPgPgPg1_jDPgPg%JJRk/_DPgPg%?C#5RlPDPgPg%=C#5RCPDPgPg%?ERm#?#5RnPDPgPg%=m#5RoPDPgPg%=ERE#?#5RpPDPgPg%=E#5RqPDPgPg%?8Rr#?Rs#?#5RtPDPgPg%=s#5RsPDPgPg%=rRr#?#5RuPDPgPg%=r#5RrPDPgP@PAPAPBDyD@D@D@D@D@D@D@D@D@D@FxRAPiAAgDjC8RjC8C81wgBRBP6P:g00ELR@g00GcRv'^1s6:=4@vdAr;<5CqR<b9b:b;X3;X4;X1_W21056,6:%E5,69'3Rv10H:R@10J:RwPlP:PCP:PnP:PoP:PpP:PqP:PtP:PsP:10r:#u9vu:DRDRDRDR5p@R@109H[RH[[^3;^4;^1_^2_P6f?Ru,1FRr#;%>rP5PrP:P9PWO7b8b<b7b6O4b0O1W5P6O1POP1PPP1PQP1PRP11NS1DCDCP3f:,1F#:R1,2OPPP1PQP1PRP1PSP1CPDCP7P612OXP>P0P=P6PFPWASFJI%:]RI,2O10J^R^PZP[P4POPJ%<JPIPNP]O1P\PNP]P]%<]DGM9FP5CLP^f>,1FR^#M%>^%9^R]/0^'6%;^%E]'6'3%9rR]P;Pc1U;KRK,Ib,Ia/XGRaPaPaPaPaPaPaPaPaPaAY;`K,IL,IM/XGRG1[GdRdDBDBDBP?PePfPgP2PiPgAAgkhPiPgPAPiAAgDkC8C8C8PBP<b9b:b;X3;X4;X1_X2_109J\@\w\v^3;^4;^1_^2_P6fARw,1FR@#;%>@P5P@P:P9PuO7b8b<b7b6O4b0O1W5P6O1PPPXPQPXPRPXPSPXCPDCP3%:YRY,2PPQPYPRPY1NSYDCP7P612PIPTP0P=P6PFPuPV%:rRT,2P%5mRm/0]R]PZP[P4PPPm%<mPTPNPrO1P\PNPrPr%<rDGM9FP5CLP]f@,1FR]#M%>]%9]Rr/0]'6%;]%Er'6'3%9@RrP;PGPaPaPaPaPaPaPa1[ad9oaaDBDBRaP?PePfPgP2PiPg%Jm=AghPiPjC8C8PBP<b9b:b;X3;X4;X1_X2_10m:PH[\v^3;^4;^1_^2_P6fCRm,1FRd#;%>dP5PdP:P9PwO7b8b<b7b6O4b0O1W5P6O1PQPIPRPI1NSIDCP3%:^R^,2QPRP^PSP^CPP7P612QTPWP0P=P6PFPwPV%:@RW,2Q%5ERE/0rRrPZP[P4PQPE%<EPWPNP@O1P\PNP@P@%<@DGM9FP5CLPrfB,1FRr#M%>r%9rR@/0r'6%;r%E@'6'3%9dR@P;PaP?PePfPgP2PiPg%JE=AghPiPjC8C8PBP<b9b:b;X3;X4;X1_X2_10E:PH[\v^3;^4;^1_^2_P6fERE,1FRQ#;%>QP5PQP:P9PmO7b8b<b7b6O4b0O1W5P6O1PRPTPSPTCPP3%:]R],2R1NS]P7P612RWPuP0P=P6PFPmPV%:dRm,2R%=8R8#?#5Ru/0@R@PZP[P4PRPu%<uPmPNPdO1P\PNPdPd%<dDGM9FP5CLP@fD,1FR@#M%>@%9@Rd/0@'6%;@%Ed'6'3%9QRdP;PaP?PePfPgP2PiPg%Ju=AghPiPjC8C8PBP<b9b:b;X3;X4;X1_X2_10u:PH[\v^3;^4;^1_^2_P6fGRu,1FR@#;%>@P5P@P:P9PEO7b8b<b7b6O4b0O1W5P6O11NSWP3%:r,2SP7P7P612SmPwP0P=P6PFPEPV%:QRV,2S%=8#5R8/0dRdPZP[P4PSP8%<8PVPNPQO1P\PNPQPQ%<QDGM9FP5CLPdfF,1FRd#M%>d%9dRQ/0d'6%;d%EQ'6'3%9@P;PaP?PePfPgP2PiPg%J8=AghPiPjC8C8PBP<b9b:b;X3;X4;X1_X2_108:PH[\v^3;^4;^1_^2_P6fI,1FRF#;%>FP5PFP:P9PuO7b8b<b7b6O4b0O1W5P6O1P7P7P6n010000000X07P6O1n200100000021100010000W0P6O1n200100000021100011000W0P6O1n200100000021100011000W0P6O1n200100000021100011000W0P6O1n200100000021100011000W0P6O1n200100000021100011000bBb>WG%VUeW>WFWEWCWDWHo"). Qed.

Lemma gr_agree_join : forall base len o n (m m' : word -> option byte),
  (forall a : word, (base <= bv_unsigned a < base + o)%Z -> m' a = m a) ->
  agree_win (base + o + n) (len - o - n) [] m m' -> agree_win base len [(o, n)] m m'.
Proof.
  unfold agree_win. intros base len o n m m' P Q a Ha Hro.
  pose proof (Hro (o, n) (or_introl eq_refl)) as Hx. cbn [fst snd] in Hx.
  destruct (Z_lt_le_dec (bv_unsigned a) (base + o)) as [Lt|Ge].
  - apply P. lia.
  - apply Q; [lia | intros r Hr; destruct Hr].
Qed.

Local Ltac neqbv := let E := fresh in intro E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.
Local Ltac nin := let H := fresh in intro H; vm_compute in H; intuition discriminate.

(* [comment removed for export] *)
Lemma pixBilateralGray_W : forall fr cs C A m md regs (s pixs w h datas : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BG_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  PIXat m pixs (hdv w h 8 0 datas) -> hdr_ok w h 8 -> (22 <= w)%Z -> (22 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 8 * h))%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_bg <= kR)%Z -> (RB_bg w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 0 -> (forall q, live A' q = live A q) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bg) (bR - RB_bg w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  (forall fr' cs' A' m' vm' regs' (pixd datad : Z), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pixd -> pixr_new C A A' m' pixd datad (set_data (pix_hdr w h 8) datad) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bg) (bR - RB_bg w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 235128) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pixs w h datas ret S HC HW FZ R2 Hs16 HsL HsU R1 Hret R4 R10 R11 R12 F10 F11 HP Hhdr Hw Hh
    Lp Ld L0p kR bR HR HkR HbR K0 K1.
  pose proof (ck_top C HC) as CT. pose proof (ck_sp0 C HC) as CK0. pose proof (ck_sp0hi C HC) as CK1.
  pose proof (ck_img C HC) as CI. pose proof LSTK_val as LV.
  cbv [ll_img LLU16 snd] in CI. unfold BG_WIN, BC_WIN in HsL.
  assert (Hs : (4096 + 64 <= s <= 2 ^ 47)%Z) by lia.
  pose proof HP as (HP0 & HP1 & _).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  destruct (exW_blk_rng C A m md pixs 64 HC HW Lp ltac:(lia) ltac:(lia)) as (Pp0 & Pp1 & Pp2).
  assert (Hs64 : ((s - 64) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  assert (Hs56 : ((s - 56) mod 8 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, (mod16_mod8 s Hs16); reflexivity).
  assert (RKE : RK_bg = (RK_bc + RK_pixcopy)%Z) by reflexivity.
  assert (RBE : RB_bg w h = (RB_bc w h + RB_pixT (4 * (wpl_of w 8 * h)))%Z) by reflexivity.
  assert (RKs : (0 <= RK_pixcopy /\ RK_pix <= RK_bc)%Z) by (unfold RK_bc, RK_it, RK_pixcopy, RK_pix, RK_cmapcopy; lia).
  assert (RBs : (0 <= RB_pixT (4 * (wpl_of w 8 * h)) /\ RB_amb w h 11 <= RB_bc w h)%Z).
  { pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))). assert (0 <= RB_it w h)%Z by (unfold RB_it; pose proof (RB_pixT_nonneg (4 * (wpl_of (w + 22) 8 * (h + 22)))); pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))); lia).
    pose proof (alloc_margin_ge 80 ltac:(lia)). pose proof (alloc_margin_ge (8 * h) ltac:(lia)). unfold RB_bc. lia. }
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | apply (gr_A1 al_rom fr cs regs m s pixs) |].
  all: try first [ exact FZ | exact Hs | exact R2 | exact R10 | exact R11 | exact R12 | exact F10 | exact F11 | lia
                 | apply mod16_mod8; exact ALp | exact (PIX_rd_cmap _ _ _ _ HP) | exact (PIX_rd_d _ _ _ _ HP)
                 | exact (W_sok_win C A m md (s - 64) 64 HC HW ltac:(lia) ltac:(lia)) ].
  intros fin (fr1 & cs1 & r1 & M1 & -> & FZ1 & RV1 & C8 & C16 & C24 & C32 & C40 & C48 & Q2 & Q8 & Q9 & Q18 & AG1 & G8 & G9 & GK1).
  assert (LR1 : local_regions C A A s [((s - 64)%Z, 64%Z)]) by (constructor; [left; cbn [fst snd]; lia | constructor]).
  destruct (rinv_WP2 C A A m md M1 _ s HC HW (sub_live_refl A) HsU RV1 LR1) as [HW1 PM1].
  unfold word_to_le_bytes in C8, C16, C24, C32, C40, C48.
  assert (CS1 : cellsAt SEGS M1 (s - 64) (gr_saved regs fr)).
  { unfold gr_saved.
    eapply cellsAt_cons with (a := (s - 8)%Z); [lia | exact C8 |].
    eapply cellsAt_cons with (a := (s - 16)%Z); [lia | exact C16 |].
    eapply cellsAt_cons with (a := (s - 24)%Z); [lia | exact C24 |].
    eapply cellsAt_cons with (a := (s - 32)%Z); [lia | exact C32 |].
    eapply cellsAt_cons with (a := (s - 40)%Z); [lia | exact C40 |].
    eapply cellsAt_cons with (a := (s - 48)%Z); [lia | exact C48 |].
    apply cellsAt_nil. }
  unfold gr_saved in CS1. clear C8 C16 C24 C32 C40 C48.
  assert (PM1x : forall x : word, (pixs <= u x < pixs + 64)%Z -> M1 x = m x).
  { intros x Hx. apply (proj2 RV1). intros r Hr. destruct Hr as [<- | []]. unfold inreg. cbn [fst snd]. lia. }
  eapply rz_reach; [exact (w_pure _ _ _ _ HW1) | exact (gr_A1b al_rom fr1 cs1 r1 M1 FZ1 Q8) |].
  intros fin (cs2 & -> & FZ2).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW1) | apply (gr_A2 al_rom _ cs2 r1 M1 s FZ2 Hs Q2 Q9) |].
  { apply fpv_get_same. }
  { rewrite fpv_get_other by neqbv. exact G9. }
  { rewrite fpv_get_other by neqbv. exact G8. }
  intros fin (fr3 & cs3 & r3 & M3 & -> & FZ3 & -> & AG3 & GK3).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW1) | apply (gr_A2b al_rom fr3 cs3 r3 M1 FZ3) |].
  { rewrite (AG3 9%bv) by notin_lit. exact Q9. }
  intros fin (cs4 & -> & FZ4).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW1) | apply (gr_A3 al_rom _ cs4 r3 M1 s pixs FZ4 Hs ltac:(lia)) |].
  1-4: csr; reflexivity.
  { apply fpv_get_same. }
  { rewrite fpv_get_other by neqbv. rewrite GK3 by nin. rewrite fpv_get_other by neqbv. exact G9. }
  { rewrite fpv_get_other by neqbv. rewrite GK3 by nin. rewrite fpv_get_other by neqbv. exact G8. }
  intros fin (fr5 & cs5 & r5 & M5 & -> & FZ5 & -> & P1 & P2 & P10 & P11 & P12 & AG5 & H10 & H11 & GK5).
  assert (FRK5 : forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> reg_get fr5 r = reg_get fr r).
  { intros r Hr N8 N9.
    assert (N15 : r <> 15%bv) by (intro E; subst r; vm_compute in Hr; repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]); exact Hr).
    rewrite (GK5 r (fs_notin_g r [10; 11; 14; 15]%nat Hr N8 N9 ltac:(intros x Hx; cbn [In] in Hx |- *; tauto))).
    rewrite (fpv_get_other _ _ _ _ N15).
    rewrite (GK3 r (fs_notin_g r [14; 15]%nat Hr N8 N9 ltac:(intros x Hx; cbn [In] in Hx |- *; tauto))).
    rewrite (fpv_get_other _ _ _ _ N15).
    exact (GK1 r (fs_notin_g r [8; 9]%nat Hr N8 N9 ltac:(intros x Hx; cbn [In] in Hx |- *; tauto))). }
  assert (FRKx : forall frx frk : bvmap 5 word, reg_get frx 8%bv = Z_to_bv 64 (u (reg_get fr 8%bv)) ->
            reg_get frx 9%bv = Z_to_bv 64 (u (reg_get fr 9%bv)) ->
            (forall r : reg, ~ In (ridx r) [8; 9]%nat -> reg_get frx r = reg_get frk r) ->
            (forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> reg_get frk r = reg_get fr r) ->
            forall r : reg, In (u r) fs_list -> reg_get frx r = reg_get fr r).
  { intros frx frk X8 X9 XK XF r Hr.
    destruct (Z.eq_dec (u r) 8) as [E8|N8'].
    { assert (r = 8%bv) as -> by (apply bv_eq; rewrite E8; reflexivity). rewrite X8. apply Z_to_bv_bv_unsigned. }
    destruct (Z.eq_dec (u r) 9) as [E9|N9'].
    { assert (r = 9%bv) as -> by (apply bv_eq; rewrite E9; reflexivity). rewrite X9. apply Z_to_bv_bv_unsigned. }
    assert (N8 : r <> 8%bv) by (intro E; apply N8'; rewrite E; reflexivity).
    assert (N9 : r <> 9%bv) by (intro E; apply N9'; rewrite E; reflexivity).
    rewrite (XK r (fs_notin_g r [8; 9]%nat Hr N8 N9 ltac:(intros x Hx; cbn [In] in Hx |- *; tauto))).
    exact (XF r Hr N8 N9). }
  assert (BLS : bl_src A M1 pixs (hdv w h 8 0 datas)).
  { refine (conj (PIXat_frame m M1 pixs _ HP PM1x) (conj eq_refl (conj eq_refl (conj Hhdr (conj _ (conj _
             (conj eq_refl (conj Lp (conj Ld (conj eq_refl eq_refl)))))))))).
    all: unfold hdv; cbn [p_w p_h]; lia. }
  eapply bilateralCreate_W with (fr := fr5) (cs := cs5) (C := C) (A := A) (m := M1) (md := md) (regs := r5) (s := (s - 64)%Z)
    (pixs := pixs) (v := hdv w h 8 0 datas) (S := S) (kR := kR) (bR := bR).
  all: try first [ exact H_amb | exact H_gev | exact HC | exact HW1 | exact FZ5 | exact P2 | exact P1 | exact P10 | exact P11
                 | exact P12 | exact H10 | exact H11 | exact L0p | exact HR | exact Hs64 | exact BLS | exact Hw | exact Hh
                 | reflexivity
                 | (red; apply bv_eq; reflexivity)
                 | (unfold BC_WIN; lia)
                 | (change (RB_bc w h <= bR)%Z; lia)
                 | (csr; reflexivity) ].
  - intros fr6 cs6 A6 m6 vm6 r6 HW6 FZ6 CK6 PM6 R610 LV6 FK6 AR6.
    change (aroom A6 vm6 (kR - RK_pix) (bR - RB_amb w h 11)) in AR6.
    assert (SL6 : sub_live A A6) by (intros q k Hq; rewrite LV6; exact Hq).
    assert (AGW6 : agree_win (s - 64) 64 [] M1 m6) by (apply (agree_of_FRM C (s - 64) M1 m6 (s - 64) 64 [] HC (proj1 PM6)); lia).
    keep_cells CS1 AGW6 CS6.
    eapply rz_reach; [exact (w_pure _ _ _ _ HW6) | apply (gr_Bn al_rom fr6 cs6 r6 m6 s (getr regs 1) (getr regs 8) (getr regs 9)
      (getr regs 18) (Z_to_bv 64 (u (reg_get fr 8))) (Z_to_bv 64 (u (reg_get fr 9)))) |].
    all: try first [ exact FZ6 | exact Hs | lia | (eapply (exW_clr_None C A6 m6 _ _ _ _ _ HW6); [cbv [ll_clr LLU16]; cbn [In]; left; reflexivity | lia | lia | lia | lia])
                   | (eapply (exW_clr_None C A6 m6 _ _ _ _ _ HW6); [cbv [ll_clr LLU16]; cbn [In]; right; left; reflexivity | lia | lia | lia | lia]) | cell_from CS6
                   | exact (W_sok_win C A6 m6 _ (s - 64) 64 HC HW6 ltac:(lia) ltac:(lia)) | exact R610 | (csr; reflexivity) ].
    intros fin (fr7 & cs7 & r7 & M7 & -> & FZ7 & RV7 & Q72 & Q710 & Q711 & Q712 & Q71 & Q78 & Q79 & Q718 & AG7 & G78 & G79 & GK7).
    assert (LR7 : local_regions C A6 A6 s [((s - 56)%Z, 8%Z)]) by (constructor; [left; cbn [fst snd]; lia | constructor]).
    destruct (rinv_WP2 C A6 A6 m6 (with_vmmaps vm6 md) M7 _ s HC HW6 (sub_live_refl A6) HsU RV7 LR7) as [HW7 PM7].
    replace (Z_to_bv 64 0x17ec4) with (0x17ec4 : word) by (apply bv_eq; reflexivity).
    apply (returnErrorPtr_W (fx := mkFP fr7 cs7) C A6 M7 (with_vmmaps vm6 md) r7 s 0x11e6a 0x10cae 12 16 ret (Z_to_bv 64 0) S
             HC HW7 Q72 Hs16 ltac:(unfold LSF; lia) HsU ltac:(rewrite Q71; exact R1) Hret Q710 Q711 Q712 str_gr_msg str_gr_proc).
    intros m8 r8 HW8 FR8 MG8 CK8 R810.
    apply (K0 fr7 cs7 A6 m8 vm6 r8 HW8 FZ7).
    + apply cs_kept_intro; csr; reflexivity.
    + eapply POSTM_trans; [exact PM1 |].
      eapply POSTM_trans; [exact (POSTM_mono C A (s - 64) s M1 m6 ltac:(lia) PM6) |].
      eapply POSTM_trans; [exact (POSTM_sub C A A6 s m6 M7 SL6 PM7) |].
      apply (POSTM_sub C A A6 s M7 m8 SL6).
      apply (POSTM_range C A6 M7 (with_vmmaps vm6 md) m8 (s - (16 + LSF)) s s HC HW7 FR8); unfold LSF; lia.
    + exact R810.
    + exact LV6.
    + apply (FRKx fr7 fr6 G78 G79 GK7). intros r Hr N8 N9. rewrite (FK6 r Hr). exact (FRK5 r Hr N8 N9).
    + apply (aroom_mono A6 vm6 _ _ _ _ AR6); lia.
  - intros fr6 cs6 A6 m6 vm6 r6 bil b HW6 FZ6 CK6 SL6 PM6 R610 BO BF FK6 AR6.
    change (aroom A6 vm6 (kR - RK_bc) (bR - RB_bc w h)) in AR6.
    pose proof BO as (_ & (Bb1 & Bb2 & _) & _).
    assert (BQ : forall q, bil_blocks bil b q -> live A q = None)
      by (intros q Hq; exact (proj1 (bil_blocks_facts _ _ _ _ _ _ _ _ q BO Hq))).
    assert (BQ6 : forall q, bil_blocks bil b q -> exists n, live A6 q = Some n)
      by (intros q Hq; exact (proj2 (bil_blocks_facts _ _ _ _ _ _ _ _ q BO Hq))).
    assert (BFq : forall q, ~ bil_blocks bil b q -> live A6 q = live A q).
    { intros q NB. apply BF.
      - intro HIn. apply NB. left. exact HIn.
      - intros i Hi. split; [|split]; intro E; apply NB; right; exists i; (split; [exact Hi|]);
          [left; exact E | right; left; exact E | right; right; exact E]. }
    assert (AGW6 : agree_win (s - 64) 64 [] M1 m6) by (apply (agree_of_FRM C (s - 64) M1 m6 (s - 64) 64 [] HC (proj1 PM6)); lia).
    keep_cells CS1 AGW6 CS6.
    eapply rz_reach; [exact (w_pure _ _ _ _ HW6) | apply (gr_B al_rom (mkFP fr6 cs6) r6 m6 s bil Hs ltac:(lia)
      (W_sok_win C A6 m6 _ (s - 64) 64 HC HW6 ltac:(lia) ltac:(lia)) ltac:(csr; reflexivity) R610) |].
    intros fin (r7 & M7 & -> & RV7 & C7 & Q71 & Q72 & Q710 & AG7).
    assert (LR7 : local_regions C A6 A6 s [((s - 56)%Z, 8%Z)]) by (constructor; [left; cbn [fst snd]; lia | constructor]).
    destruct (rinv_WP2 C A6 A6 m6 (with_vmmaps vm6 md) M7 _ s HC HW6 (sub_live_refl A6) HsU RV7 LR7) as [HW7 PM7].
    assert (BO7 : bil_obj C A A6 M7 bil pixs (hdv w h 8 0 datas) b).
    { eapply bil_obj_keep with (C := C) (A := A) (Af := A6) (Af' := A6) (m := m6) (m' := M7) (md := with_vmmaps vm6 md) (bil := bil)
        (pixs := pixs) (b := b).
      all: first [ exact H_amb | exact H_gev | exact HC | exact HW6 | exact BO | exact (SL6 _ _ Lp) | exact (sub_live_refl A6)
                 | exact (rinv_scr_keep C A6 m6 M7 (with_vmmaps vm6 md) (s - 56) 8 HC HW6 RV7 ltac:(lia) ltac:(lia)) ]. }
    assert (AGW7 : agree_win (s - 64) 64 [(8%Z, 8%Z)] m6 M7).
    { apply (agree_of_rinv _ _ _ _ _ _ RV7). constructor; [| constructor].
      right. exists (8%Z, 8%Z). split; [left; reflexivity | cbn [fst snd]; lia]. }
    keep_cells CS6 AGW7 CS7.
    assert (TAIL : forall fr7 cs7 A7 m7 vm7 r8 (rv : Z),
      W C A7 m7 (with_vmmaps vm7 md) -> frm_zero cs7 -> cs_kept r7 r8 -> POSTM C A6 (s - 64) M7 m7 ->
      getr r8 10 = Z_to_bv 64 rv -> (0 <= rv < 2 ^ 64)%Z -> sub_live A6 A7 ->
      (forall r : reg, In (u r) fs_list -> reg_get fr7 r = reg_get fr6 r) ->
      aroom A7 vm7 (kR - RK_bg) (bR - RB_bg w h) ->
      (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
         getr regs' 10 = Z_to_bv 64 rv -> (forall q, bil_blocks bil b q -> live A' q = None) ->
         (forall q, ~ bil_blocks bil b q -> live A' q = live A7 q) -> LIVKc A' (pixs + 20) 4 m7 m' ->
         (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bg) (bR - RB_bg w h) ->
         realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes SEGS (mkCfg (@mkst (mkFP fr7 cs7) r8 (Z_to_bv 64 0x39884) m7 al_rom) (with_vmmaps vm7 md)) S).
    { intros fr7 cs7 A7 m7 vm7 r8 rv HW8 FZ7 CK8 PM8 R810 Hrv SL7 FK7 AR7 KF.
      eapply rz_reach; [exact (w_pure _ _ _ _ HW8) | apply (gr_C al_rom (mkFP fr7 cs7) r8 m7 s rv Hs Hrv ltac:(csr; reflexivity) R810) |].
      intros fin (r9 & M9 & -> & -> & Q91 & Q92 & Q98 & Q910 & AG9).
      assert (LP7 : live A7 (Z_to_bv 64 pixs) = Some 64%Z) by exact (SL7 _ _ (SL6 _ _ Lp)).
      assert (RD9 : rdn SEGS m7 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 bil)).
      { rewrite (FRM_rdn16 C (s - 64) M7 m7 (s - 56) 8 HC (proj1 PM8)) by lia. exact C7. }
      assert (BO9 : bil_obj C A A7 m7 bil pixs (hdv w h 8 0 datas) b).
      { eapply bil_obj_keep with (C := C) (A := A) (Af := A6) (Af' := A7) (m := M7) (m' := m7) (md := with_vmmaps vm6 md) (bil := bil)
          (pixs := pixs) (b := b).
        all: first [ exact H_amb | exact H_gev | exact HC | exact HW7 | exact BO7 | exact (SL6 _ _ Lp) | exact SL7
                   | exact (fun q k x Hq Hx => LeptSlots.LIVK_byte A6 M7 m7 q k x (proj2 PM8) Hq Hx) ]. }
      assert (AGW9 : agree_win (s - 64) 64 [] M7 m7) by (apply (agree_of_FRM C (s - 64) M7 m7 (s - 64) 64 [] HC (proj1 PM8)); lia).
      keep_cells CS7 AGW9 CS9.
      apply (H_bd (mkFP fr7 cs7) C A A7 m7 (with_vmmaps vm7 md) r9 (s - 64)%Z (s - 56)%Z bil pixs w h datas b (Z_to_bv 64 0x39890) S
               HC HW8 Q92 Hs64 ltac:(unfold BD_WIN; lia) ltac:(lia) ltac:(lia) Hs56 Q91 ltac:(red; apply bv_eq; reflexivity)
               ltac:(csr; reflexivity) Q910 RD9 BO9 ltac:(lia) ltac:(lia) LP7 L0p Lp).
      intros A8 m8 vm8 r10 HW10 CK10 BN10 BK10 PM10 FR10 PX10 RZ10 RT10.
      rewrite with_vmmaps_twice in HW10 |- *. rewrite with_vmmaps_vmmaps in RT10.
      assert (AGW10 : agree_win (s - 64) 64 [(8%Z, 8%Z)] m7 m8).
      { eapply gr_agree_join; [intros a Ha; apply FR10; lia |].
        apply (agree_of_FRM C (s - 56 + 8) m7 m8 _ _ [] HC (proj1 PM10)); lia. }
      keep_cells CS9 AGW10 CS10.
      eapply rz_reach; [exact (w_pure _ _ _ _ HW10) | apply (gr_D al_rom fr7 cs7 r10 m8 s ret (getr regs 1) (getr regs 8) (getr regs 9)
        (getr regs 18) (Z_to_bv 64 (u (reg_get fr 8))) (Z_to_bv 64 (u (reg_get fr 9)))) |].
      all: try first [ exact FZ7 | exact Hs | exact Hret | exact R1 | cell_from CS10 | (csr; reflexivity) ].
      intros fin (fr11 & cs11 & r11 & M11 & -> & FZ11 & -> & Q112 & Q1110 & Q118 & Q119 & Q1118 & AG11 & G118 & G119 & GK11).
      assert (SLA8 : sub_live A A8).
      { intros q k Hq. destruct (bil_blocks_dec bil b q) as [Bq|NBq].
        - rewrite (BQ q Bq) in Hq. discriminate Hq.
        - rewrite (BK10 q NBq). exact (SL7 _ _ (SL6 _ _ Hq)). }
      apply (KF fr11 cs11 A8 m8 vm8 r11 HW10 FZ11).
      - apply cs_kept_intro; csr; reflexivity.
      - assert (PMc : POSTMc C A s (pixs + 20) 4 m m8).
        { eapply POSTMc_trans; [apply POSTMc_of_POSTM; exact PM1 |].
          eapply POSTMc_trans; [exact (POSTMc_mono C A (s - 64) s _ _ M1 m6 ltac:(lia) PM6) |].
          eapply POSTMc_trans; [apply POSTMc_of_POSTM; exact (POSTM_sub C A A6 s m6 M7 SL6 PM7) |].
          eapply POSTMc_trans; [apply POSTMc_of_POSTM; exact (POSTM_sub C A A6 s M7 m7 SL6 (POSTM_mono C A6 (s - 64) s M7 m7 ltac:(lia) PM8)) |].
          exact (POSTMc_sub C A A8 s _ _ m7 m8 SLA8 (POSTMc_mono C A8 (s - 56 + 8) s _ _ m7 m8 ltac:(lia) PM10)). }
        apply (POSTM_of_POSTMc C A m m8 md s (pixs + 20) 4%nat (Z_to_bv 64 pixs) 64 (Z_to_le_bytes 4 1) HC HW PMc Lp).
        all: try change (Z.of_nat 4) with 4%Z in *.
        + rewrite u_Z2bv by lia. lia.
        + rewrite u_Z2bv by lia. lia.
        + reflexivity.
        + intros i Hi. apply (PIXat_defined m8 pixs _ _ PX10). rewrite u_Z2bv by lia. lia.
        + exact (PIX_rd_rc _ _ _ _ HP).
        + exact (PIX_rd_rc _ _ _ _ PX10).
      - csr; reflexivity.
      - exact BN10.
      - exact BK10.
      - exact (proj2 PM10).
      - apply (FRKx fr11 fr7 G118 G119 GK11). intros r Hr N8 N9. rewrite (FK7 r Hr), (FK6 r Hr). exact (FRK5 r Hr N8 N9).
      - pose proof (RT10 _ _ AR7 ltac:(lia) ltac:(lia)) as X. rewrite !Z.sub_0_r in X. exact X. }
    apply (bilateralApply_W fr6 cs6 C A A6 M7 (with_vmmaps vm6 md) r7 (s - 64) bil pixs w h datas b (Z_to_bv 64 0x39884) S
             HC HW7 FZ6 Q72 Hs64 ltac:(unfold AP_WIN; lia) ltac:(lia) Q71 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity)
             Q710 BO7 Hhdr ltac:(lia) ltac:(lia) (SL6 _ _ Lp) (SL6 _ _ Ld) (kR - RK_bc) (bR - RB_bc w h)
             ltac:(rewrite with_vmmaps_vmmaps; exact AR6) ltac:(lia) ltac:(lia)).
    + intros fr7 cs7 A7 m7 vm7 r8 HW8 FZ7 CK8 PM8 R810 LV7 FK7 AR7.
      rewrite with_vmmaps_twice in HW8 |- *.
      assert (SL7 : sub_live A6 A7) by (intros q k Hq; rewrite LV7; exact Hq).
      apply (TAIL fr7 cs7 A7 m7 vm7 r8 0%Z HW8 FZ7 CK8 PM8 R810 ltac:(lia) SL7 FK7).
      * replace (kR - RK_bg)%Z with (kR - RK_bc - RK_pixcopy)%Z by lia.
        replace (bR - RB_bg w h)%Z with (bR - RB_bc w h - RB_pixT (4 * (wpl_of w 8 * h)))%Z by lia. exact AR7.
      * intros fr' cs' A' m' vm' regs' HWf FZf CKf PMf Rf10 BNf BKf LKf FKf ARf.
        apply (K0 fr' cs' A' m' vm' regs' HWf FZf CKf PMf Rf10); [| exact FKf | exact ARf].
        intros q. destruct (bil_blocks_dec bil b q) as [Bq|NBq].
        -- rewrite (BNf q Bq), (BQ q Bq). reflexivity.
        -- rewrite (BKf q NBq), (LV7 q). exact (BFq q NBq).
    + intros fr7 cs7 A7 m7 vm7 r8 pixd datad HW8 FZ7 CK8 PM8 R810 PN FK7 AR7.
      rewrite with_vmmaps_twice in HW8 |- *.
      pose proof PN as (Pd1 & Pd2 & Pd3 & Dd1 & Dd2 & Dd3 & Ndd & LA6p & LA6d & L0pd & L0dd & LA7p & LA7d & FRA7 & PXd & PDd).
      assert (SL7 : sub_live A6 A7).
      { intros q k Hq.
        destruct (Z.eq_dec (u q) (u (Z_to_bv 64 pixd))) as [Ep|Np'].
        { assert (q = Z_to_bv 64 pixd) as -> by (apply bv_eq; exact Ep).
          rewrite LA6p in Hq; discriminate Hq. }
        destruct (Z.eq_dec (u q) (u (Z_to_bv 64 datad))) as [Ed|Nd'].
        { assert (q = Z_to_bv 64 datad) as -> by (apply bv_eq; exact Ed).
          rewrite LA6d in Hq; discriminate Hq. }
        assert (Np : q <> Z_to_bv 64 pixd) by (intro E; apply Np'; rewrite E; reflexivity).
        assert (Nd : q <> Z_to_bv 64 datad) by (intro E; apply Nd'; rewrite E; reflexivity).
        rewrite (FRA7 q Np Nd). exact Hq. }
      apply (TAIL fr7 cs7 A7 m7 vm7 r8 pixd HW8 FZ7 CK8 PM8 R810 ltac:(lia) SL7 FK7).
      * replace (kR - RK_bg)%Z with (kR - RK_bc - RK_pixcopy)%Z by lia.
        replace (bR - RB_bg w h)%Z with (bR - RB_bc w h - RB_pixT (4 * (wpl_of w 8 * h)))%Z by lia. exact AR7.
      * intros fr' cs' A' m' vm' regs' HWf FZf CKf PMf Rf10 BNf BKf LKf FKf ARf.
        assert (NBp : ~ bil_blocks bil b (Z_to_bv 64 pixd))
          by (intro Bq; destruct (BQ6 _ Bq) as [n Hn]; rewrite LA6p in Hn; discriminate Hn).
        assert (NBd : ~ bil_blocks bil b (Z_to_bv 64 datad))
          by (intro Bq; destruct (BQ6 _ Bq) as [n Hn]; rewrite LA6d in Hn; discriminate Hn).
        assert (LAp : live A' (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite (BKf _ NBp); exact LA7p).
        assert (LAd : live A' (Z_to_bv 64 datad) = live A7 (Z_to_bv 64 datad)) by exact (BKf _ NBd).
        apply (K1 fr' cs' A' m' vm' regs' pixd datad HWf FZf CKf PMf Rf10); [| exact FKf | exact ARf].
        assert (LAp0 : live A (Z_to_bv 64 pixd) = None)
          by (destruct (live A (Z_to_bv 64 pixd)) as [k|] eqn:E; [rewrite (SL6 _ _ E) in LA6p; discriminate LA6p | reflexivity]).
        assert (LAd0 : live A (Z_to_bv 64 datad) = None)
          by (destruct (live A (Z_to_bv 64 datad)) as [k|] eqn:E; [rewrite (SL6 _ _ E) in LA6d; discriminate LA6d | reflexivity]).
        unfold pixr_new.
        refine (conj Pd1 (conj Pd2 (conj Pd3 (conj Dd1 (conj Dd2 (conj Dd3 (conj Ndd (conj LAp0
                 (conj LAd0 (conj L0pd (conj L0dd (conj LAp (conj (eq_trans LAd LA7d) (conj _ (conj _ PDd))))))))))))))).
        -- intros q Np Nd. destruct (bil_blocks_dec bil b q) as [Bq|NBq].
           ++ rewrite (BNf q Bq), (BQ q Bq). reflexivity.
           ++ rewrite (BKf q NBq), (FRA7 q Np Nd). exact (BFq q NBq).
        -- apply (PIXat_frame m7 m' pixd _ PXd). intros x Hx.
           assert (NEQ : pixd <> pixs) by (intro E; rewrite E in LA6p; rewrite (SL6 _ _ Lp) in LA6p; discriminate LA6p).
           pose proof (exW_blk_apart C A7 m7 (with_vmmaps vm7 md) pixd pixs 64 64 HC HW8 LA7p (SL7 _ _ (SL6 _ _ Lp)) NEQ
                         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as APT.
           assert (Ex : at_ (Z_to_bv 64 pixd) (u x - pixd) = x).
           { apply bv_eq. unfold at_. rewrite (u_Z2bv pixd) by lia. rewrite u_Z2bv by lia. lia. }
           rewrite <- Ex.
           apply (LKf (Z_to_bv 64 pixd) 64%Z (u x - pixd)%Z LAp ltac:(lia)).
           rewrite (u_Z2bv pixd) by lia. lia.
Qed.

End BilGrayW.
