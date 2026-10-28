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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptPixCreateT2 V2LeptPixCopyT V2LeptPixDestroyH V2LeptPixMisc V2LeptBl_iface V2LeptBl2_iface V2LeptBilCW1 V2LeptBilCW3 V2LeptBilCW4 V2LeptBilD_iface V2LeptBilDW V2LeptBilGrayW V2LeptPblRun V2LeptPbl_iface.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2LeptPblW () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8WalksLib9rostr_chkI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C7ARocqVerifyHarness?AgentSubmission6Common9Leptonica8SumSpecs3SSP9rostr_winC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00C5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z;div_le_monoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith6wpl_ofK46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixHdr6hdr_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith4dvalc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW=wpl8_le_wpl32C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib5Lists4List2InC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic3notC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24ridxC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula02C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic5False00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecB7fs_listK47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions9bv_eq_decc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW4cblkC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:asr_callocI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4lctx00C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc8aic_baseC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase2ASI47Corelib4Init9Datatypes6option00c5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW5ocompC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase4liveC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_A0C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5PIXatK46Stdlib9micromega5Tauto8GFormula07C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs;PIXat_frameK47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_vmC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptPixCopyT3hdvC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB4cellI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List6nth_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8sub_liveC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW38sub_noneC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBl2_iface8rgb_compI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3Cok00C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrC56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_topC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okC5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs7cs_keptC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface6al_romC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_sp0C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6ll_imgC47Corelib4Init9Datatypes3sndI47Corelib4Init9Datatypes4prod00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr04C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5POSTMC5ARocqVerifyHarness?AgentSubmission6Common8VmLedger@with_vmmaps_sameC47Corelib4Init5Logic9False_indC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=sub_live_reflC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots>POSTD_of_POSTMC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom;roomtr_reflC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptPixMiscApixDestroy_null_WC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs4p_rcC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_textC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_cmapC47Corelib4Init5Logic6eq_symK47Corelib4Init9Datatypes4prod01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_dataC5ARocqVerifyHarness?AgentSubmission2V2AV2LeptPixDestroyHApixDestroy_free_WI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs1W00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots5POSTDC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom6roomtrC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00C5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase5LLU16I5ARocqVerifyHarness?AgentSubmission6Common8PropExec7FPState00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSetC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LSTKC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface;ALLOC_STACKI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8LSTK_valI47Corelib4Init5Logic4True00C5ARocqVerifyHarness?AgentSubmission6Common7FPSteps8frm_zeroC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_img64C56Stdlib6ZArith6BinInt1Z3powC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ro_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_roC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_lg_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_lgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ag_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_agC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=pin_errno_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_errnoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_hcellC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3inZC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_hcellC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;pin_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:ll_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs<pin_ro_belowC4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C4ELinuxProcessSemantics5Riscv3Sem7reg_getC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6w_pureC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW19W_clr_gotC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW19W_clr_sevC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase9W_sok_winC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun5pbl_NK5ARocqVerifyHarness?AgentSubmission6Common8PropExec7FPState01C5ARocqVerifyHarness?AgentSubmission6Common5Hoare:regs_agreeK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptCmapArr8rinv_WP2C5ARocqVerifyHarness?AgentSubmission6Common7StoreOk9mem_growsC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface<callee_savedC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=cs_kept_introC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;POSTM_rangeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;POSTM_transC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW:fs_notin_pC5ARocqVerifyHarness?AgentSubmission2V29V2LeptErr@returnErrorPtr_WC5ARocqVerifyHarness?AgentSubmission6Common5Reach8rz_reachC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPbl_ifaceJpixBilateral_null_contractC47Corelib4Init9Datatypes3fstC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9DitherLib4rinvC46Stdlib9micromega;ZifyClasses6mkapp2I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPbl_iface7PBL_WINC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPbl_iface?PC_pixBilateralC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C46Stdlib9micromega8ZifyInst7Inj_Z_Zc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW<str_pbl_msgNc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW<str_pbl_procC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase3LSFI47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison03K47Corelib4Init9Datatypes:comparison02C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure5aroomC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPbl_iface6RB_pblC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPixCreate8pixr_newI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6pix_wf00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs9pix_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8bytes_atC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs7wf_cmapC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs7wf_dataC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith:dval_rangeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith<wpl_of_rangeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecW;exW_blk_rngC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPbl_iface=RB_pbl_nonnegC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs;PIX_rd_cmapC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8PIX_rd_dC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8PIX_rd_wC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8PIX_rd_hC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase7W_img16C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun8pbl_Ww_8C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun8pbl_Wh_8C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun9pbl_Ww_32C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun9pbl_Wh_32C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB5c_offC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB5c_lenc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW9pbl_savedc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW:pbl_localsC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB>agree_of_rangeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB9agree_winC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_W3C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots9LIVK_byteC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPbl_iface<RB_bc_nonnegC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45RB_bcC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL>RB_pixT_nonnegC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL7RB_pixTC56Stdlib6ZArith6BinInt1Z3eqbC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL8RB_cmapTK6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5cmapv01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6CMAPatC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptCmapValid7cmap_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5c_arrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8c_nallocC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptPixCopyT8pixt_newC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun8pbl_X_cpC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptPixCopyT5cmresC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3c_dC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3c_nC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:aroom_monoC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptPixCopyT2TKC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptPixCopyT=pixCopy_szT_WC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase>lept_stderr1_WC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun7pbl_A_8C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun8pbl_A_32C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun7pbl_A1bC5ARocqVerifyHarness?AgentSubmission6Common8FPStepsV<fpv_get_sameC5ARocqVerifyHarness?AgentSubmission6Common8FPStepsV=fpv_get_otherC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_A2C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun7pbl_A2bC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun8pbl_A3_8C5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilGrayW5RB_bgC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun8pbl_X_g8C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixHdr7pix_hdrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8set_dataC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPbl_iface8RB_pbl32C5ARocqVerifyHarness?AgentSubmission2V2AV2LeptPixCreateT28pixr_newC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilGrayWBpixBilateralGray_Wc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW;hdr_ok_32_8K46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun9pbl_A3_32C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_C9c5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW9ocomp_rgbC5ARocqVerifyHarness?AgentSubmission6Common8VmLedgerBwith_vmmaps_vmmapsC5ARocqVerifyHarness?AgentSubmission6Common8VmLedgerAwith_vmmaps_twiceC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs>sub_live_transC5ARocqVerifyHarness?AgentSubmission6Common8PropExec9u64_rangec5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW:ocomp_keepC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun7pbl_C10C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots5LIVKxC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=above_not_gapC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface:al_globalsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8pin_globC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface=al_errno_slotC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_errnoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5hcellC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs7scratchC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots6inslotC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun7pbl_C11C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun7pbl_C12C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_XEc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW8cblk_decc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblWBpixDestroy_ocomp_WC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure<aroom_nonnegC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_C7C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB=agree_of_rinvC5ARocqVerifyHarness?AgentSubmission6Common7StepTac6u_Z2bvC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_C8C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB;cellsAt_nilC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB<cellsAt_consC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB;cellsAt_appc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW9ocomp_subC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_C4C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_C5C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_C6C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_C1C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_C2C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_C3C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun5pbl_DC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun9pbl_X_errC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPblRun6pbl_CMC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPbl_ifaceEpixBilateral_contractC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC5ARocqVerifyHarness?AgentSubmission6Common5Reach5reachC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB5c_valC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB7cellsAtC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec6v_jalrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB:cells_keepC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3FRMC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LIVKC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB<agree_of_FRMC46Stdlib5Lists4List9nth_errorC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB;cellsAt_nthC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:POSTM_monoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5p_wplC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_hC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8WalksLib8zbv_selfC47Corelib4Init5Logic7f_equalC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9POSTM_subC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots4FRMxC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots>POSTD_blk_byteC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots?POSTD_POSTM_winC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9DitherLib5inregC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7rdn_extC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPbl_iface6RK_pblC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL:RB_cmapT_0C5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBilGrayW5RK_bgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom6RK_pixC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPbl_iface:RK_pbl_valC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomPC:RK_pixcopyc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW<str_pbl_fmtWc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW6in_fs8c5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW6in_fs9c5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW<str_pbl_msgD".
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Lemma str_pbl_msgN : str16 73294 27.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPblW ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;3p;2p;4p;7p10000p4p70R0p1000`p4p710R1p8P0p1001<p4p710R0p8p1001Zp4p70R2P1p8P2P0p8p1002Hp4p7210P0p8p10034p4p70R2P1p8P2P0p8g003jj10Tg004Oj11Tg0054j14Tg005Rj3NTg006Zj3=Tg0074j27Tg007Pj26Tg007kj2@Tg0097j2;Tg009Tj2?Tg009nj1>Tg00:Nj1MTg00:nj1LTg00;Lj1KTg00;jj1DTg00<Uj2<Tg00=8j3CTg00=[j2BTg00>=j2ETg00>ij3ATg00?Hj4FTg00@:j4GTg00@Uj4HTg00A@j7ITg00Adj7JTf0R0#0#0p=2%00#0#0#0p=5g00BHR2/<0p=3P2f1R1g00BfP0CHp=8P1g00CMR3g00ClR4P4g00DLR5P0g00DlFIp=9f2R6P3P4P4P5P1P0FJp=:g00ELR4g00Elg00G>R3#0#2#1#1#1#1#2#1#2#1#1#1#0#4R7%13#0R8#1#1#4R93Ng00GcR:3=R;g00HCR</79%08#1#0#2#4R8,79'6R=%03#5R>#0#2#5#5#4R?/77R@1@79,;7%03#2#1#2#5#5#5#4R3'7'6'61?4:RAP;dg00HaR;#>%M;%L2%K2%D2R;1<2<%39R9'8,9;%38,89,9;5:;%3?%37R?'8,9;%4>R>#39C2?%33'8,9;5:;3:1B;5P0P6PA1E06==4:dAA2<1CFb1b2b31;7>/73,6@,6=P0b0CGo"). Qed.
Lemma str_pbl_msgD : str16 71263 20.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPblW ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;3p;2p;4p;7g003jj11Tg004Oj10Tg0054j14Tg005Rj3NTg006Zj3=Tg0074j27Tg007Pj26Tg007kj2@Tg0097j2;Tg009Tj2?Tg009nj1>Tg00:Nj1MTg00:nj1LTg00;Lj1KTg00;jj1DTg00<Uj2<Tg00=8j3CTg00=[j2BTg00>=j2ETg00>ij3ATg00?Hj4FTg00@:j4GTg00@Uj4HTg00A@j7ITg00Adj7JTf0R0#1#1p=2%10#1#1#1p=5g00BHR1/<0p=3P1f1R2g00BfP0CHp=8P2g00CMR3g00ClR4P4g00DLR5P0g00DlFIp=9f2R6P3P4P4P5P2P0FJp=:g00ELR4g00Elg00G>R3#1#2#0#1#0#0#2#0#1#0#0#0#0#0#4R7%13R8#0R9#2#4R:3Ng00GcR;3=R<g00HCR=/7:%03#2#0#1#2#4R>,7:'6R?%18#2#5#5#5#4R8/77R@1@7:,;7%13#2#0#2#5#5#5#4R3'7'6'61?4;RAP<dg00HaR<#>%M<%L1%K1%D1R<1<1=%3:R:'8,9<%3>,8:,9<5:<%38%37R8'8,9<%09#0#4R9#39C18%33'8,9<5:<3:1B<5P0P6PA1E06==4;dAA1=2CFb1b2b31;79/73,6@,6?P0b0CGo"). Qed.
Lemma str_pbl_proc : str16 72715 12.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPblW ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;3p;2p;4p;7g003jj11Tg004Oj10Tg0054j15Tg005Rj3FTg006Zj3<Tg0074j26Tg007Pj27Tg007kj2@Tg0097j2;Tg009Tj2?Tg009nj1>Tg00:Nj1NTg00:nj1MTg00;Lj1LTg00;jj1ETg00<Uj2=Tg00=8j3CTg00=[j2BTg00>=j2DTg00>ij3ATg00?Hj4GTg00@:j4HTg00@Uj4ITg00A@j7JTg00Adj7KTf0R0#1#1p=2%10#1#1#1p=3g00BHR1/=0p=4P1f1R2g00BfP0CIp=8P2g00CMR3g00ClR4P4g00DLR5P0g00DlFJp=9f2R6P3P4P4P5P2P0FKp=:g00ELR4g00Elg00G>R3#1#2#0#0#0#2#3#0#1#0#0#5R7%03#2R8#5R93Fg00GcR:3<R;g00HCR</69%08#1#2#5R8,69'7R=%23R>#2#3#3#3#5R?/67R@1@79,;7%13#2#0#2#3#3#3#5R3'6'7'71?4:RAP;dg00HaR;#>%N;%M1%L1%E1R;1=1<%49R9'8,9;%48,89,9;5:;%4?%47R?'8,9;%0>#0#5R>#49C1?%43'8,9;5:;3:1B;5P0P6PA1D06=<4:dAA1<2CGb1b2b31;7>/63,7@,7=P0b0CHo"). Qed.
Lemma str_pbl_fmtW : str16 69395 76.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPblW ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;3p;2p;4p;7g004Oj10Tg003jj11Tg0054j15Tg005Rj3FTg006Zj3<Tg0074j26Tg007Pj27Tg007kj2@Tg0097j2;Tg009Tj2?Tg009nj1>Tg00:Nj1NTg00:nj1MTg00;Lj1LTg00;jj1ETg00<Uj2=Tg00=8j3CTg00=[j2BTg00>=j2DTg00>ij3ATg00?Hj4GTg00@:j4HTg00@Uj4ITg00A@j7JTg00Adj7KTf0R0#1#1#1#1p=3%10#1p=2g00BHR1/=0p=4P1f1R2g00BfP0CIp=8P2g00CMR3g00ClR4P4g00DLR5P0g00DlFJp=9f2R6P3P4P4P5P2P0FKp=:g00ELR4g00Elg00G>R3#3#0#0#0#0#1#2#0#2#0#0#5R7%13R8#1R9#0#0#2#5R:3Fg00GcR;3<R<g00HCR=/6:%03#2#0#1#2#5R>,6:'7R?%29#3#3#3#5R9/67R@1@7:,;7%13#2#0#2#3#3#3#5R3'6'7'71?4;RAP<dg00HaR<#>%N<%M1%L1%E1R<1=1=%4:R:'8,9<%4>,8:,9<5:<%49%47R9'8,9<%08#2#0#0#5R8#49C19%43'8,9<5:<3:1B<5P0P6PA1D06=<4;dAA1=2CGb1b2b31;78/63,7@,7?P0b0CHo"). Qed.

(* [comment removed for export] *)
Lemma wpl8_le_wpl32 : forall w, (0 <= w)%Z -> (wpl_of w 8 <= wpl_of w 32)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPblW ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h52Hwh61wp;2p;1p;4p;3p;8p;5p;7g0074j26Tg003jj10Tg0054j13Tg00IMj2<Tg004Oj12Tg0097j2=Tg009nj1MTg00:Nj1DTg00:nj1BTg00;Lj1ATg00;jj1@Tg00<Uj21Tg00@Uj45Tg00=[j2STg009Tj2RTg00>=j2QTg006Zj3PTg00>ij3OTg00?Hj4LTg00Ijj2KTg00JFj2:Tg00Joj17Tg00KNj3CTg00L7j2ETg00Lcj2FTg00MOj3GTg00Moj2HTg00NMj2ITg00O0j1JTg00ORj38Tg00=8j3;Tg00P5j8?Tg00PYj5NTg00Q>j29Tg00A@j7>Tf1R0g00CMR1g00ClR2P2g00DLR3f0R4g00DlF>p=4g00BHR5g00HCR6/64R7g00G>R8#0#0#0R9#3R:,<0%28#2#2#2#3R;'=R<%09#0#3R9,<0/=;R=P9g00HaR>#MR?%D>R@%B5%A5RA%@5RBP51156RCg00RD1159RDC5'41SB3REP4f2RFg00ELRGg00GcRH'R1Q4F=PGHdAO560CLRHb1b2b31K69P4b0g00RkR6,:5RG%76#7,:59C5Gg00SJ'E'F=G>?P@1H50PAPBP1P2P2P3P5PCg00BfRC1I58R8C5,4B%J2P5115:9858115;R;5;5PCA858D=;5;C5,4BG?PEPHb1b2b3X4516<=\7^45P4PFP0O2b0DN190:1909'6eW5W6o"). Qed.
Lemma hdr_ok_32_8 : forall w h, (0 <= w)%Z -> (0 <= h)%Z -> hdr_ok w h 32 -> hdr_ok w h 8.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPblW ()) [] "h01Hh17__arithh24__ffh38__varmaph45__with54__x1h64__x2h74__x3h82DVh92H8h:2Hhh;3Hh2h<3Hszh=2Hwh>3Hw2h?1Mh@1hhA1wp;2p;1p;3p;5p;4p;7p;8g0074j21Tg003jj10Tg0054j14Tg00T6j3?Tg00U1j1NTg004Oj1=Tg00Q>j22Tg007PR0j26Tg00V5j2PTg00W5j5OTg00IMj2>Tg009nj1bTg00:Nj1^Tg00:nj1\Tg00;Lj1[Tg00;jj1ZTg00=[j2YTg009Tj2XTg00>=j2WTg006Zj3HTg00>ij3VTg00?Hj4UTg00Wcj2<Tg00JFj2ATg00X=j2QTg00Xfj3FTg00Joj1DTg00KNj3GTg00L7j2RTg00Lcj2STg00MOj3TTg00Moj2dTg00YOj4MTg00NMj2BTg00ORj3@Tg00O0j1cTg00@:j4ETg00<Uj2aTg00@Uj4LTg00A@j7]Tg00Ymj7_Tg00P5j8`Tf0R1#0#0p=I%01#0#0#0p=:f3R2f2R3f1R4'>'>/11p=51>34/11p=Kg00BHR5/a1p=7P5P4g00ZQP1CLp=8P4g00CMR6g00ClR7P7g00DLR8P1g00DlF]p=3P3P6P7P7P8P4P1F_p=;AH541p=9P5P4g00BfP1CLp=CP2P6P7P7P8P3P4P1G`p=Jg00HCR6/14R9g00G>R:#0R;#0R<#0R=#0R>#0R?#4R@9?23P0%N@RAf4RB%=<#=#=#0#I#=#0#:#4RC'1112C%4<RD12B@P2%0?#:#:#:#:#:#4R?C5'6'6f5%4=R=7?BP1f7RB/1CREf6RF/1CPD12B@PFP?C5'6'6P0f8RF/1CPD12F@PBP?C5,6Ef9??F=P1f:RF/1CREPDf;RG/2@PFP?C5,6EP011GCPDf<R0/2@PGP?C5f=RG??0=P111GCPDf?/2@f>RGP?C5f@R0/PG120=120@'1fARE/2=RF12E@RHP0PGP1DO1>H09KF0%N=RFfBR0/1CRH11ECRCPD120=PEP?C5RE'6RG'6g00HaRI#bRJ%^IRK%\5RL%[5RM%Z5RN%7=RO%4:RP#7'8,3N%4;RQ#7,8O,3N%7DRR,8O,3N18OO,3N%4>R>#7,8O,3N%=:#0#I#4RS#7,8O,3N%7@,8O,3N5;N5;N5;N5;N5;N3;1YN8R8P1P3g00ELROg00GcRT'X1W13=HOTdAV564CUR6b2b3b419=P19=Q19=D19==19=>19=S19=@'<'<'<'<'<'<P1b1PFePHPGPBPCPEP2g00RkRE,A5RC1Q5DRB=F5C%DE#DRE#D,A59F5B1A5E5G55G5g00SJ'R'S=TIJPKP5P51d52P3PLCMP4PLCMPMPN1B5:1B5;R;5@5R:1B5<=@5;R;'C,3N%c7R7PNA@5R;%7?R;'C,3NP7A@5R:/C;,3NCJCJP8P6b2b3b4X55X65X751>349K14PDP2P3P?C5PDP3P2P?C5[[^55^65^75P1fCR?/2@P012?=P4P2O5b1CECECEb?b9W<W;P4P1O2n2001000000121000000W0W>P4P1O2n2001000000121000000W0X8AP4P1O2n2001000000121000000W0X:9W=X@5XA5o"). Qed.

Section PblW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Hypothesis H_amb : forall fx : FPState, @pixAddMirroredBorder_contract fx AL CL ASR.
Hypothesis H_gev : forall fx : FPState, @pixGetExtremeValue_contract fx AL CL ASR.
Hypothesis H_rgb : forall fx : FPState, @pixGetRGBComponent_contract AL CL ASR fx.
Hypothesis H_cri : forall fx : FPState, @pixCreateRGBImage_contract AL CL ASR fx.
Let H_bd : forall fx : FPState, bilateralDestroy_contract (fx := fx) := fun fx => bilateralDestroy_W (fx := fx).

(* [comment removed for export] *)
Definition pbl_saved (regs : bvmap 5 word) (fr : bvmap 5 word) : list cell :=
  [(104%Z, 8%nat, u (getr regs 1)); (96%Z, 8%nat, u (getr regs 8)); (88%Z, 8%nat, u (getr regs 9)); (80%Z, 8%nat, u (getr regs 18));
   (72%Z, 8%nat, u (getr regs 19)); (64%Z, 8%nat, u (getr regs 20));
   (56%Z, 8%nat, u (Z_to_bv 64 (u (reg_get fr 8)))); (48%Z, 8%nat, u (Z_to_bv 64 (u (reg_get fr 9))))].
Definition pbl_locals (w h d : Z) : list cell := [(44%Z, 4%nat, w); (40%Z, 4%nat, h); (36%Z, 4%nat, d)].

(* [comment removed for export] *)
Lemma fs_notin_p : forall (r : reg) (L : list nat), In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> (forall x, In x L -> In x [8; 9; 10; 11; 12; 13; 14; 15]%nat) -> ~ In (ridx r) L.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPblW ()) ["PblW"] "h02H0h14__p1h24__p2h34__x1h44__x2h51Eh62E0h73H17h87__arithh94__ffh:8__varmaph;5__with<3z17h=1xh>2HLh?2b1h@2b2hA1nhB1HhC2HrhD1LhE2N8hF2N9hG1XhH1rhI1yp&0p;1p;2p;3p;4p;5p;<p;6p;7p;8g003jj1:Tg004Oj1<Tg00[8j1|Tg00[Vj1LTg00:Nj1iTg00\9j20Tg00\cj3PTg0054j15Tg00]:j2aTg00]]j3RTg006Zj32j1eTg00^@j1VTg00Joj18Tg009nj1jTg00^Yj1hTg00_`k20:Tg0074j2ZTg00`Sk107Tg00Ijj2[Tg007PR0j2OTg00a<R1j17Tg00a\j3tTg00b@R2j1cTg00b`j2nTg00cCj3mTg00c`j1lTg00d>j2kTg00JFj2UTg00d_j3^Tg00L7j2]Tg00:nk10>Tg00Mok20=Tg00YOk40<Tg00;Lk10;Tg00;jk109Tg00NMj2fTg00<Uj2XTg00O0k105Tg00eHk503Tg00=[j2~Tg009Tj2WTg00>=j2}Tg00>ij3{Tg00?Hj4zTg00MOj3ATg00WcR3j29Tg00elj2rTg00fIm<00Tg00fnm<01Tg00gSj4qTg00h:j2pTg00KNk304Tg00h\j6oTg00@Uj4YTg00A@j7STg00Adk708Tg00Ymj7TTg00P5j8\Tg00i@R4f1R5f0R63Ap=DA2456p=6A2456g00i_R7'9p=Cf4R8f3R9524f2R:=245/96'9p=3g00BHR;?256p=1g00HCR</r6p=41W;6p=@P;P4P;P;P1P8P2P9g00j<P:P51W;6N<00p=IP4P;P6P2P5P:P9P8f5R2f6R1f7R=f8R>N<01p=?A2489P:P5P6Cqp=J1p<6p=E1[<8A2;9:'O1Z5<A2;6<'O'9p=>B04;56p=Ng00HaR?AA?569A?:9A?97A8p=KP5g00CMR@g00ClRAPAg00DLRBP6Eop=gP:P@PAPAPBP;P5g00ZQRCP6CYg00DlRDFSp=;P:P@PAPAPBP5P6K08p=dP:P@PAPAPBP5P6FTp>061X;6p=FP;P5PCP6CYp=bP8P@PAPAPBP9P@PAPAPBP;1X;:PCP5CYPDFSP6FTp==P1P@PAPAPBP2P@PAPAPBP8PDFSP9P@PAPAPBP:P@PAPAPBP5PDFSP6FTFTp>02P9P@PAPAPBP:P5P6G\p=`P1P@PAPAPBP2P8P9P@PAPAPBP:P5P6G\G\p=GA2;6<,O5p=yA2;:5,O9/96p=x1967p=wA2;:5/96p=vA2;89A2;:5/96'9p=Q1956,9:p=u1Z6<p=B1[<6p=HA249:A2456/97'9p=MAA?56p=_AA?569A?:p=sg00G>RD#:RC#<RE#|RF#LRG%i410F5g00ji5P;%:CRC#:#5RHg00l0RI1aFHd5RF92G:#V%<CRC#5RJPI1aFJd5RF92G9#VAP468g00RkRG#8RK#8RL#8RM#8#8#8#8#8RN%8NRO%8ORP%8PRQ%8QRR%8RRS%8SRT%8TRU%j4'D'D'D'D'D'D'D'DRV9P45[^=4%h2=P48RWP5%h1R1P6O2AP41V20:F=10F=R1,Z<&07F,[1'OP310F>#7R1,6NPOP1PPP1PQP1PRP1PSP1PTP11CU1D3D3D3P7P5f9,0F#7R1,6NP=g00lLR=%L6RV%L5RXP0%L:?256109:1095'1R0[10:510:6'1%L9?2:5[RY%L8?29:\0At:56P6n2001000000120000000W@W?WAR0PY^@X^?V^A=R=P6PFf;RVARFHIRXPN10FVRY#7RZ%4Y,1HR[%e4R\%e;R]%c5%c6'116561n563mXI4X=4R4PNPH%@HPZ%46X=;RNPYO1P6X=;R^PNPYPYPYDIM9?P5DJP[f<,0FR[#EP[%4[RYP[P[PYD>f=RY,0FR_#4R`P;p-0Ra%lD,k;Rb1U;MRM5^;Rc1U;LRL9^;bRd1U;G'N'Ng00SJRG']RePePePePePePePePePePePe%j?RfDKDKDK%i?R?P;&0>;P520=;:H0<Rg&0;;Rh&09;Ri1gi8%<DR8,f;Rj1f;DRD5;i5di1gi21X;<9;ij5di606iR2&05ARkPi%FHRl=;ijPkPiPiPi1blDPiPi%FJRm/bDPiPi%:C#5RnPDPiPi%<C#5RCPDPiPi%:ERo#:#5RpPDPiPi%<o#5RqPDPiPi%<ERE#:#5RrPDPiPi%<E#5RsPDPiPi%:8Rt#:Ru#:#5RvPDPiPi%<u#5RwPDPiPi%<tRt#:#5RxPDPiPi%<t#5RyPDPiP@PAPAPBI03D=D=D=D=D=D=D=D=D=D=K02RAPkA;iDlC`RlFG1~iBRBP6P:g00ELR@g00GcRz'W1}6:=2@zdA{;<5CzR<b9b:b;X3;X4;X1aW2P:P5P61y95CxRz11H:R@11J:R{PnP:PCP:PpP:PqP:PrP:PsP:PvP:PwP:11y:#w9vx:DQDQDQDQ5u@R@119H[RH[[^3;^4;^1a^2aP6f?Rx,0FRy#B%HyP5PyP:P9PYO7b8b<b7b6O4b0O1W5P6O1POP1PPP1PQP1PRP1PSP1PTP11CU1D3D3D3P3f:,0F#7R1,6OPPP1PQP1PRP1PSP1PTP1PUP1CMD3D3P7P616OZP>P0P=P6PFPYARFJIPO%7_RI11J`R`P\P]P4POPJ%@JPIPNP_O1P^PNP_P_P_DIM9?P5DJP`f>,0FR`#EP`%4`R_P`P`P_D>%4yR_P;Pe1U;KRK,Nd,Nc/]GRcPcPcPcPcPcPcPcPcPcA^;bK,NL,NM/]GRG1_GfRfDKDKDKP?PgPhPiP2PkPiA;imjPkPiPAPkA;iDmC`FGPBP<b9b:b;X3;X4;X1aX2a119J\@\{\z^3;^4;^1a^2aP6fAR{,0FR@#B%H@P5P@P:P9PxO7b8b<b7b6O4b0O1W5P6O1PPPZPQPZPRPZPSPZPTPZPUPZCMD3D3P3%7[R[,6PPQP[PRP[PSP[PTP[1CU[D3D3P7P616PIPVP0P=P6PFPxPXPP%7yRV%5oRo/1_R_P\P]P4PPPo%@oPVPNPyO1P^PNPyPyPyDIM9?P5DJP_f@,0FR_#EP_%4_RyP_P_PyD>%4@RyP;PGPcPcPcPcPcPcPc1_cf9sccDKDKRcP?PgPhPiP2PkPi%Fo=;ijPkPlFGPBP<b9b:b;X3;X4;X1aX2a11o:PH[\z^3;^4;^1a^2aP6fCRo,0FRf#B%HfP5PfP:P9P{O7b8b<b7b6O4b0O1W5P6O1PQPIPRPIPSPIPTPI1CUID3D3P3%7`R`,6QPRP`PSP`PTP`PUP`CMD3P7P616QVPYP0P=P6PFP{PXPQ%7@RY%5ERE/1yRyP\P]P4PQPE%@EPYPNP@O1P^PNP@P@P@DIM9?P5DJPyfB,0FRy#EPy%4yR@PyPyP@D>%4fR@P;PcP?PgPhPiP2PkPi%FE=;ijPkPlFGPBP<b9b:b;X3;X4;X1aX2a11E:PH[\z^3;^4;^1a^2aP6fERE,0FRQ#B%HQP5PQP:P9PoO7b8b<b7b6O4b0O1W5P6O1PRPVPSPVPTPVPUPVCMD3P3%7_R_,6RPSP_PTP_1CU_D3P7P616RYPxP0P=P6PFPoPXPR%7fRx%5uRu/1@R@P\P]P4PRPu%@uPxPNPfO1P^PNPfPfPfDIM9?P5DJP@fD,0FR@#EP@%4@RfP@P@PfD>%4QRfP;PcP?PgPhPiP2PkPi%Fu=;ijPkPlFGPBP<b9b:b;X3;X4;X1aX2a11u:PH[\z^3;^4;^1a^2aP6fGRu,0FRR#B%HRP5PRP:P9PEO7b8b<b7b6O4b0O1W5P6O1PSPYPTPY1CUYD3P3%7yRy,6SPTPyPUPyCMP7P616SxP{P0P=P6PFPEPXPS%7QR{%5tRt/1fRfP\P]P4PSPt%@tP{PNPQO1P^PNPQPQPQDIM9?P5DJPffF,0FRf#EPf%4fRQPfPfPQD>%4RRQP;PcP?PgPhPiP2PkPi%Ft=;ijPkPlFGPBP<b9b:b;X3;X4;X1aX2a11t:PH[\z^3;^4;^1a^2aP6fIRt,0FRS#B%HSP5PSP:P9PuO7b8b<b7b6O4b0O1W5P6O1PTPxPUPxCMP3%7@R@,6T1CU@P7P616T{PoP0P=P6PFPuPXPT%7RRu%<8R8#:#5Ro/1QRQP\P]P4PTPo%@oPuPNPRO1P^PNPRPRPRDIM9?P5DJPQfH,0FRQ#EPQ%4QRRPQPQPRD>%4SRRP;PcP?PgPhPiP2PkPi%Fo=;ijPkPlFGPBP<b9b:b;X3;X4;X1aX2a11o:PH[\z^3;^4;^1a^2aP6fKRo,0FRQ#B%HQP5PQP:P9PtO7b8b<b7b6O4b0O1W5P6O11CU{P3%7f,6UP7P7P616UuPEP0P=P6PFPtPXPU%7SRX%<8#5R8/1RRRP\P]P4PUP8%@8PXPNPSO1P^PNPSPSPSDIM9?P5DJPRfJ,0FRR#EPR%4RRSPRPRPSD>%4QP;PcP?PgPhPiP2PkPi%F8=;ijPkPlFGPBP<b9b:b;X3;X4;X1aX2a118:PH[\z^3;^4;^1a^2aP6fM,0FRF#B%HFP5PFP:P9PoO7b8b<b7b6O4b0O1W5P6O1P7P7P6n010000000X07P6O1n200100000021100010000W0P6O1n200100000021100011000W0P6O1n200100000021100011000W0P6O1n200100000021100011000W0P6O1n200100000021100011000W0P6O1n200100000021100011000W0P6O1n200100000021100011000W0P6O1n200100000021100011000bBb>WG%VWeW>WFWEWCWDWHo"). Qed.

Lemma in_fs8 : In (u (8%bv : reg)) fs_list.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPblW ()) ["PblW"] "p;1p;2p;3g003jj10Tg0054j14Tg004Oj11Tg009Tj2=Tg00ljj3;Tg00[8j1:Tg00]:j27Tg00]]j36Tg00[Vj18Tg00\9j29Tg00\cj3>Tg006Zj33Tg00Wcj25Tg00BHR0f1R1f0R233p=<f2R3#4=301/52p=?f4#4f3530%43=301/52'5p=2g00G>R2#0R1#0R3#0#4R4/<4%13R3P4%03P4%13P4%11R1#0R3#0P4%13P4%11R3#0P4%13P4%12#0R2#0R3#0P4%13P4%12R2#0P4%12g00i_7?4D2D2D2D2D21=043;%:1R1g00l01714d9614%81e'9g00ji5>0do"). Qed.
Lemma in_fs9 : In (u (9%bv : reg)) fs_list.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPblW ()) ["PblW"] "p;1p;2p;3g003jj10Tg004Oj11Tg0054j13Tg00Wcj25Tg009Tj2<Tg00ljj3;Tg00mDj3:Tg00[8j17Tg00]:j28Tg00]]j39Tg00[Vj1?Tg00\9j2>Tg00\cj3=Tg006Zj34Tg00BHR0f1R1#3f0R234p=6A4012p=@f4#3f3540f2#3=401/52'5p=2g00G>R2#0R1#0R3#0%13R3#3R4'61@44R5%03P4%13P4%11R1#0R3#0P4%13P4%11R3#0P4%13P4%12#0R2#0R3#0P4%13P4%12R2#0P4%12P4g00i_D2D2D2D2D2R2'51<049;523:%71R1g00l01814d9914%?1e'>g00ji5=0do"). Qed.

(* [comment removed for export] *)
Ltac cells_sub FC := unfold cellsAt; repeat (apply Forall_cons; [cbn [c_off c_len c_val fst snd]; cell_from FC|]); apply Forall_nil.

(* [comment removed for export] *)
Definition ocomp (C : lctx) (Ar A : AS) (m : word -> option byte) (r dr w h : Z) : Prop :=
  (r = 0%Z /\ dr = 0%Z) \/
  ((4096 <= r)%Z /\ (r + 64 <= alloc_top (c_vm C))%Z /\ (4096 <= dr)%Z /\ (dr + (4 * (wpl_of w 8 * h)) <= alloc_top (c_vm C))%Z /\ r <> dr /\
   live Ar (Z_to_bv 64 r) = None /\ live Ar (Z_to_bv 64 dr) = None /\ live (c_A0 C) (Z_to_bv 64 r) = None /\ live (c_A0 C) (Z_to_bv 64 dr) = None /\
   live A (Z_to_bv 64 r) = Some 64%Z /\ live A (Z_to_bv 64 dr) = Some (4 * (wpl_of w 8 * h))%Z /\ PIXat m r (hdv w h 8 0 dr)).
(* [comment removed for export] *)
Definition cblk (r dr : Z) (q : word) : Prop := r <> 0%Z /\ (q = Z_to_bv 64 r \/ q = Z_to_bv 64 dr).

Lemma cblk_dec : forall r dr q, cblk r dr q \/ ~ cblk r dr q.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPblW ()) ["PblW"] "p'0h01Hh12N1h21ei001eh31qh41Eh52_Hh61dh71rh82N2h92NZh:1Xh;2drh<1si011si021np;1p;2p;3p;6p;4p;7g003jj16Tg00[8j1ETg00[Vj1BTg00m^j2ATg00^@j11Tg00n>R0j2<Tg00n^j22Tg006Zj30Tg00WcR1j23Tg009Tj2=Tg00mDj3:Tg001<j6@j7DTg00oDj3?Tg007PR2j29Tg00ljj38Tg00@:j4>Tg00olj3CTg00BHR3f0R4g00HCR530p=;f2R6f1R7/34'9p=5A0345#1p=4f3R8?067/34p=7g00G>#6#6#6#6#6#6#ER9#BR:1A65%;6R;%1;'<P0%;8R;%1;f4R;#;R<#1R=129;R>90:6129890:635R?%1?'3P4P3P5%44129490:;f5R?,29R@90:;RA35RB%1B'3X73A0355#1RB1295RC90:8A0:8>35R>%1>RDP2PBP:P;PCPAC7g00i_RAP4P:f7REPCf8RC,29RF90:ERGC7P71=35O1W5X:BP7P4O2n2001000000120000000X0>PDe3:P?P4E@X2<P4O1A?98@A0:8@R@%1@'<P0f6R@,29R<90:;R;%1;%4E129ER;90:?RDA0:?<35R<%1<'3P4P:PFf9R<#4129<R?90:4A0:4F35R>%1>'3X3:%4CR>A0:FFRBA0:F;R5'3RH'9RI%1IP>PHP81=:F98B5C>38P@P4E@X2DP4O1%1DA?9@;A0:@;R;%1;'<P0PG%1Gf:RG#4129GR090:CA0:C?R?35RC%1C'3P4P:P0f<RC,29R;90:4#1f=R@#4129@90:7A0:7;35RD%1D'3]1X3:f;RD,29R590:0#1%4CRCA0:5;RBA0:55RF'3RH'9R>%1>PCPHPE1=:59:BFC>38W1P<P4P8FDX2?P4O1%1?%4DA0:<5A0:<035R0%10R<P2PCP:PGP;A0:G5C7PAP4f>R5#4P:P@f?R;,29RC129590:@C7P1f@,29R190:5A0:5CPAP4fA,2990:;PGP4O1W4P4O1A0:;1PEP4O1W4P4O1n200100000021000010000W0W5P7P4O2n2001000000120000000X00P<e3:W8P4O1n200110100021110011102b6W1P4O1n200110100021110011102b6X9=P4O1n200110100021110011102b<AC674R7%17'3eW3X;3X73o"). Qed.

Lemma pbl_sub_none : forall A A' (q : word), sub_live A A' -> live A' q = None -> live A q = None.
Proof.
  intros A A' q S N. destruct (live A q) eqn:E; [rewrite (S _ _ E) in N; discriminate | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma ocomp_keep : forall C Ar A A' m m' r dr w h, ocomp C Ar A m r dr w h ->
  (forall x : word, live A (Z_to_bv 64 r) = Some 64%Z -> (r + 64 <= alloc_top (c_vm C))%Z -> (4096 <= r)%Z -> (r <= u x < r + 64)%Z -> m' x = m x) ->
  (forall q k, cblk r dr q -> live A q = Some k -> live A' q = Some k) -> ocomp C Ar A' m' r dr w h.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPblW ()) ["PblW"] "h01Hh11xh24__x1h31Ah42A'h52Arh61Ch73F01h83F02h92F1h:2F2h;2G1h<2G2h=2G3h>2G4h?2Hxh@2KPhA2L1hB2L2hC2MKhD2NEhE2NZhF2OChG2PXhH2Z0hI7__arithhJ4__ffhK8__varmaphL5__withM2drhN1hhO1khP1mhQ2m'hR1qhS1rhT1wp;3p;2p;1p;8p;4p;6p;5p;7g010cj3xTg011lj3wTg0131j3hTg014:j2dTg003jj1MTg00[8j1\Tg00[Vj1bTg015;j1ZTg015]j89Tg00n^j21Tg0054j1NTg0074j2=Tg00\9j2WTg0097j2@Tg00Ijj2]Tg006Zj37Tg00olj3gTg007PR0j22Tg016Uj46Tg00O0j1YTg017Xj45Tg018[j3OTg00ljj3UTg009nj1vTg00:Nj1uTg00Moj2tTg00;Lj1sTg00;jj1rTg00<Uj2aTg00NMj2pTg00@Uj4`Tg019bj6oTg00P5j8nTg00=[j2mTg009Tj2PTg00>=j2lTg00>ij3kTg00?Hj4jTg00^@j1LTg00WcR1j2[Tg00@:j4GTg00mDj3^Tg01:Fj6iTg01;Sj2KTg01<5j4fTg01=8j1qTg00Q>j2QTg00IMj2DTg01>0j5cTg00A@j7eTf0R2#M#Mp=Fg00BHR3/K2p=?f5R4f4R5f3R6f2R7f1R8C6;72p=3P6P7P8P2Cf#qp=:1@78/=2p=<1=78/22p=8g00HCR99732p=C1Q78/D2,D6p=;P6P7P8P9P2Dc9O45p=4f6R:P4P5P6P7C6;78/22p=0A7:45A7678/22'2p=BA7378#L/22p=A1282,27p=JA7382#Lp=IP6P7P8P9P2Dcp=XA7678/22p=V1282,27,26,25p=E1K389767/22p=T1Q78/D2,D6,K3p=>1Q78/D2p=S1D78,K39756/22p=RP8g00CMR;g00ClR<P<g00DLR=P2g00DlFep=_P:P4P5P6P7P8P2CGCGp=Hp,2ALR>p,2CLR?p,3ASR9x>?R@3wAh>?@RA,d>RBg00G>RC#FRD#MRE#M#FRF#\RG#bRH%\E#b#ZRI[PI^1Hf9RJf8RKf7RLP4P6P7P8P2G9%Z3RMP>PAPJ11G4RN%NFRO#?RPE3P>P?P@f<RQC:RR9<:ORS%FF#F#F#NRF/=LRT1WG6RU1@KORV,]U58Kf:RUP5O1f;RWP5O157I[[[[^1HAgL:8PMP>PAPQP7%?8E3PMP>PAPQP6%?7E3[[^O3^RHP1%C:R1%C4'21=F:RI%NDRDP5%NEREP6C;RX,@4PMP>PAPW11G:RYC6RZ%Y3R[PMP>PAPWPNC6P[PMP>PAP>P?P@PQC5R\PYP[PMP>PAP\PNP[PMP>PAPUPYPPPMP>PAPUPN%?XPKP:P5P6PEP4E4F0F0F0F0FB9A:478R98F47JSf=RSPQPUPKPLP:P4P5G9P7%CLRR/21%CK/2R1=FKRRP>P?P@f>R1C:R6,=VRVPTPDP:PEP4C;RX=<L6R61IKLRNPMP>PAPS11GKR\P[E3R]PMP>PAPS11GLR^P[E3R_PMP>PAP>P?P@P1C5R`P\P[E3RaPMP>PAP`P^P[E3R`PMP>PAPWP\PPE3PMP>PAPWP^C6Rb%?XRXP:P4PEPLCXRc9OJKCV3JDEDE;U2WHP2O1PTP>P?P@PSC:Rd9<LOPIPDP4PEP5C;RI=<:dPMP>PAPQP^C6RdP[PMP>PAPQPYC6P[PMP>PAP>P?P@PSC5ReP^P[PMP>PAPePYP[PMPbPPPMPZ%?IPJPLP4P5PEP:E4FBF0F0FB9AL:DEP0PRPVPTP6PNP]P_PaP`PMP>PAPQP\PPPMPdPXAOUKcCVF0DEDEf?RcP1PQPUPJPKPLP:G9P21=FURL1@WOP>P?P@fARXC:RdPDPJPEPKC;R\=<UdPMP>PAf@Rd11GWR`C6RaP[PMP>PAPd11GUR_C6P[PMP>PAP>P?P@PXC5R]P`P[PMP>PAP]P_P[PMP>PAPcP`PPPMP>PAPcP_%?\PSPWPJPKPEPUE4F0F0F0F0FB9AWU5JL38P0P>P?P@fBRLC:R\9<QOPDPUPEPJC;R_,@WPMP>PAPX11GQR]P[PMP>PAPXP`P[PMP>PAP>P?P@PLC5RNP]P[PMP>PAPNP`P[PMP>PAPdP]PPPMPaP_P1PQPUPJPEPWE4CTF0F0F0F0F09AQW78\98FWfCR\PLPdP1PSPQPWPUG9P2P>P?P@fDRWC:9<1OPDPSPEPQC;RJ,@1P>P?P@fER_C:PMP>PAPW11GcRaC6R]P[PMP>PAPW11G1R`C6P[PMP>PAP>P?P@P_C5RNPaP[PMP>PAPNP`P[PMP>PAP\PaPPPMP>PAP\P`%?JPXPcPSPQPEP1E4F0F0F0F0FB9Ac13898F1P01=FcPDP1PEPSC;RQ,@cP>P?P@fFRJC:PMP>PAP_11GdR`P[PMP>PAP_PaP[PMP>PAP>P?P@PJC5RNP`P[PMP>PAPNPaP[PMP>PAPWP`PPPMP]PQPLPdP1PSPEPcE4CTF0F0F0F0F09Adc38fGRSPJPWPLPXPdPcP1G9P21=FXPDPXPEPdC;Rc,@LP>P?P@fIRQC:PMP>PAfHR]11G\R`C6RaP[PMP>PAP]11GLRNC6P[PMP>PAP>P?P@PQC5R6P`P[PMP>PAP6PNP[PMP>PAPSP`PPPMP>PAPSPN%?cP_P\PXPdPEPLE4F0F0F0F0FB9A\L38P0PDPLPEPXC;RdP>P?P@fJRcC:5<\PMP>PAPQ11GWRNP[PMP>PAPQP`P[PMP>PAP>P?P@PcC5R6PNP[PMP>PAP6P`P[PMP>PAP]PNPPPMPaPdPJPWPLPXPEP\E4CTF0F0F0F0F09AW\fKRXPcP]PJP_PWP\PLG9P2PDPWPEP\C;P>P?P@fLR\C:5<_PMP>PAP\11GSRdC6RaP[PMP>PAP\11GJRNC6P[PMP>PAP>P?P@fMR`C5R6PdP[PMP>PAP6PNP[PMP>PAPXPdPPPMP>PAPXPNPDP_PEPWC>PQPSP_PWPEPJE4F0F0F0F0FB9ASJP01I]SPMP>PAP`11G]RWP[PMP>PAP`PdP[PMP>PAP>P?P@fNRNC5R6PWP[PMP>PAP6PdP[PMP>PAP\PWPPPMPaPDASJE_PcP]PJP_PEPSE4DRF0F0F0F0F0fOR_PNP\PcPQP]PSPJG9P21IcQPMP>PAfPRS11GXRaC6RWP[PMP>PAPS11GcRdC6P[PMP>PAP>P?P@fQR6C5RTPaP[PMP>PAPTPdP[PMP>PAP_PaPPPMP>PAP_PdPDPQPEP]C>P`PXPQP]PEPcE4F0F0F0F0FBP0PMP>PAP611G\R]P[E3PMP>PAP6PaP[PMP>PAP>P?P@fRRdC5RTP]P[PMP>PAPTPaP[PMP>PAPSP]PPPMPWPDAScEQPNP\PcPQPEPXE4DRF0F0F0F0fSRQPdPSPNP`P\PXPcG9P2P>PAPQ11GNRXC6RW=7M[PMP>PAfTR]PXP[PMP>PAP>P?P@fURaC5RT11G_RVP[PMP>PAPTPXP[PMP>PAPQPVPPPMPWPDAS`E\P6P_P`P\PEPNE4DRF0F0F0F0P0PMP>PAPaPVP[E3PMP>PAP>P?P@fVR\C5RW11GSRXP[PMP>PAPWPVP[PMP>PAP]PXPPPMP>PAP]PVPDPNPEP`C>PdPSPNP`PEP_E4F0F0F0F0fWR`P\P]PdP6PSP_PNG9P2PMP>PAP`11G6P[E3PMP>PAP>P?P@fYR_C5RV11GQRXP[PMP>PAPV11GdRVP[PMP>PAP`PXPPPMP>PAP`PVPDP6PEPSC>PaPQP6PSPEPdE4F0F0F0F0P0PMP>PAP>P?P@fZRSC5RV11G]RWP[E3PMP>PAPVPXP[PMP>PAfXRVPWPPPMP>PAPVPXPDPdPEP6C>P\P]PdP6PEPQE4F0F0F0f[R6PSPVP\PaP]PQPdG9P2PMP>PAP>P?P@f\RQC511G\RXP[E3PMP>PAP>P?P@f]RWC5PXP[PMP>PAP611G`RTPPPMP>PAP6PXPDPaPEP]C>P_P`PaP]PEP\E4F0F0F0P0PMP>PAP>P?P@f^R]C5PTP[E3PMP>PAPQ11GVPPPMP>PAPQPTPDP\PEPaC>PSPVP\PaPEP`E4F0F0f_RaP]PQPSP_PVP`P\G9P2PMP>PAP>P?P@f`R`C511G_P[E3PMP>PAPa11G6RTPPPMP>PAPa11GSPDP_PEPVC>PWP6P_PVPEPSE4F0F0P0PMP>PAP`11GQPPE3PMP>PAP`PTPDPSPEP_C>P]PQPSP_PEP6E4F0fcR_fbRTP`P]PWPQP6PSG9P2PMP>PAPT11G]R6PPE3PMP>PAP_P6PDPWPEPQC>faR6PaPWPQPEP]E4F0P0PMP>PAfdR011GaPDP]PEPWC>E3PTP`P]PWPEPaE4fgRWffRXP0PTP6P`PaP]G9P2PMP>PAPX11G6PDP`PEPaC>E3feR]P_P6P`PEPTE4%C0R`%C_'21=F0RRP>P?P@fjR5C:R49<0OPDPTPEP6C;RI,@_PMP>PAfiRZ11G0RbP[PMP>PAPZ11G_RZP[PMP>PAP>P?P@P5C5RYPbP[PMP>PAPYPZP[PMP>PAPWPbPPPMP>PAPWPZ%?IP]P0PTP6PEP_E4F0F0F0F0F0F09A0_78498F_3Jg00HaR4#v%u41t38%s3%r3R4P;P<P<P=P31a3Fg00Bf1p3CRCC`,_4%Y<P4P;P<P<P=P3PCg00ZQ1a39C`,_4EoGn1m4=P2P7g00ELR4g00GcR='P1l27=74=dAk398CjbJbKbLX231=F2%C8g00i_[[^23P2P]PSO2bI%L`1=F]P>P?P@fkRFC:R`9<]OR9PDP_PEPTC;RD=<0`R`1I]0R=PMP>PAP511G]R4P[E3RCPMP>PAP5PbP[E3R5PMP>PAP>P?P@PFC5RFP4P[E3R@PMP>PAPFPbP[E3R[PMP>PAfhRFP4PPE3RPPMP>PAPFPb%?DE3RFP_PTPEP0CXR09OX]RE'2R_'2RA'2R>'2RM'2R?'2R<'2R;'2R6,2RRI'2PSP9PIP\PRP6PdP`P;PNP=P<PcPCP?PJP5PMPLP@P>P1P[PAPUPPP_PaP4PO%C]#LR_A7H44RPA7H4bRU'[P21PH49UPUCGP:O4PFPEPaPbPDP_A7Hb4R4A7HbbR_'[P21PHb9^4_CGP7O4PWPXP]P0P81WG2RG1@XO,]G58XPTP8PKPVPQP2O5W?X1HEiCGFHFHFHFHFHbE3^WGWBP8P2O2n2001000000121000000W0WAP8P2O2n2001000000121000000W0W8P8P2O2n2001000000121000000W0W7P8P2O2n2001000000121000000W0W:P8P2O2n2001000000121000000W0W9P8P2O2n2001000000121000000W0WDP8P2O2n2011000000121000000W0W>P8P2O2n2011000000121000000W0W=P8P2O2n2011000000121000000W0W<P8P2O2n2011000000121000000W0W;P8P2O2n2011000000121000000W0P2O1n201100000021100011000W@WCWFXN3XT3XM3XS3WQWPX4BX3BW5W6o"). Qed.

(* [comment removed for export] *)
Lemma ocomp_sub : forall C Ar Ar' A m r dr w h, sub_live Ar' Ar -> ocomp C Ar A m r dr w h -> ocomp C Ar' A m r dr w h.
Proof.
  intros C Ar Ar' A m r dr w h S [H|(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12)]; [left; exact H | right].
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj (pbl_sub_none Ar' Ar _ S H6) (conj (pbl_sub_none Ar' Ar _ S H7) (conj H8 (conj H9 (conj H10 (conj H11 H12))))))))))).
Qed.

(* [comment removed for export] *)
Lemma ocomp_rgb : forall C Ar A m r dr w h, ocomp C Ar A m r dr w h -> rgb_comp A m r w h.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPblW ()) ["PblW"] "h01Hh12drh22_Hh31rh41Ah52Arh61Ch72L1h82L2h92PXh:3_H0h;3_H1h<3_H2h=3_H3h>3_H4h?3_H5h@3_H6hA3_H7hB1hhC1mhD1wp;3p;2p;1p;8p;4p;6p;5g010cj3eTg011lj3dTg0131j3\Tg014:j2ZTg003jj1KTg00[8j1STg00[Vj1RTg015;j1QTg015]j8[Tg007PR0j27Tg0054j1JTg0074j2ATg0097j2BTg00n^j21Tg016Uj44Tg00O0j1]Tg017Xj43Tg01CLj86Tg006Zj38Tg01DLj2PTg009Tj2YTg00ljj3XTg001<j6WTg00@:j4UTg01Dfj4cTg00mDj3bTg01<5j4aTg01=8j1`Tg00Q>j2NTg00IMj2ETg01;Sj2ITg01>0j5_Tg018[j3^Tg00^@j1TTf0R1#K#Kp=Fg00BHR2g00HCR3781p=Cf3R4f2R5f1R6P1Ca#`p=91B56/A1p=>1N56/E1,E4p=;1I21p=Gf5R7f4R8P4P5P6P3P1D_3^p=2f6R9P7P8P4P5C4;86/71p=0A8978A8456/71'7p=@A8256#T/71p=:1A56/71p=<1761,75p=DP7P8P41156C4=891p==1N56/E1,E4,I2p=5P8P4P5P6C4=871p=?1I269845/71p=HA8261#Tp=O1N56/E1p=M1E56,I29884/71p=LP8P4P51161C4p=Vp,2ALR:p,2CLR;p,3ASRR<9e:;R=3dA\:;=R>,Z:R?g00G>#FR@#KRA#K#FRB#SRC#R%SA#R#Q[f7RDP9P7P8P4P5P6P1G[g00Wc%C8RE%C4'7%FB#F#F#JRF/A8RG%JBRBP:P;P=f8RHC9RI5>8%J@R@P5%JARAP6C;RJ,B4%Q2RKP:P>PD11C8RLC4RM%]2RNPKP:P>PD11C4ROC4PNPKP:P>P:P;P=PHC3RPPLPNPKP:P>PPPOPNPKP:P>P9PL%GBRPPKP:P>P9PO%GJP7P8P5P6PAP4E2F0F0F0F0F@9:847<I9<F43DP:P;P<PDP9P7P4P5G6P1%C7RI/7EP0%C9PIP:P;P<f9RIPHPDP7P8G6REP1%CHRJP2P3%CIP:P;P<f=ROf<RQP6PIPHG6[X32A8233PQP3PIPHPAP1E2PKP:P>POPCP3PPF=PKP:P>PO11C1RRP@PIPAPHC5E?3DX12,P21Y233XX2JPIP1EWW0P6P1O2n2001000000120000000W0P1O11AF7RJP:P;P=PIC9R39>7BP@P4PAP5C;RS=>83PKP:P>PH11C7R3C4RTPNPKP:P>PHPLC4PNPKP:P>P:P;P=PIC3RUP3PNPKP:P>PUPLPNPKP:P>PDP3PPPKPMPSP9P7P4P5PAP8E2CHF0F0F0F@9:785DG3DP01AF91B9BP:P;P=f:RGC9R5P@P8PAP4C;RS=>75PKP:P>PI11C9R5PNPKP:P>PIP3PNPKP:P>P:P;P=PGC3RMP5PNPKP:P>PMP3PNPKP:P>PHP5PPPKPTPSPDP9P8P4PAP7E2CHF0F0F0F0F09:975DJ3<PEP11AFHRE1BIBP:P;P=POC9RJP@PDPAP9C;R4=>HJPKP:P>PQ11CIRJC4R8PNPKP:P>PQ11CHRSC4PNPKP:P>P:P;P=POC3RTPJPNPKP:P>PTPSPNPKP:P>f;RTPJPPPKP:P>PTPS%G4PGPIPDP9PAPHE2F0F0F0F0F@9:IH5DE3<P0P:P;P=f>REC9R99>GBP@PHPAPDC;R4,BIPKP:P>PO11CGRSPNPKP:P>POPJPNPKP:P>P:P;P=PEC3R5PSPNPKP:P>P5PJPNPKP:P>PQPSPPPKP8P4PTPGPHPDPAPIE2CHF0F0F0F0F09:GI7<99<FIP:P;P<POPQPTPIPHG6P1P:P;P=f@RHC99>QBP@PTPAPGC;RB,BQP:P;P=fARIC9PKP:P>PH11COR9C4RDPNPKP:P>PH11CQR4C4PNPKP:P>P:P;P=PIC3R8P9PNPKP:P>P8P4PNPKP:P>f?R8P9PPPKP:P>P8P4%GBPEPOPTPGPAPQE2F0F0F0F0F@9:OQ3<9<FQP01AFOP@PQPAPTC;RG,BOP:P;P=fBRBC9PKP:P>PI11CER4PNPKP:P>PIP9PNPKP:P>P:P;P=PBC3RSP4PNPKP:P>PSP9PNPKP:P>PHP4PPPKPDPGP8PEPQPTPAPOE2CHF0F0F0F0F09:EO3<P:P;P<PIPHP8POPQG6P11AF8P@P8PAPEC;RF,BHP:P;P=fERQC9PKP:P>fDRO11CIRTC4RGPNPKP:P>PO11CHRDC4PNPKP:P>P:P;P=PQC3R4PTPNPKP:P>P4PDPNPKP:P>fCR4PTPPPKP:P>P4PD%GFPBPIP8PEPAPHE2F0F0F0F0F@9:IH3<P0P@PHPAP8C;REP:P;P=fFRFC95>IPKP:P>PQ11CBRDPNPKP:P>PQPTPNPKP:P>P:P;P=PFC3R9PDPNPKP:P>P9PTPNPKP:P>POPDPPPKPGPEP4PBPHP8PAPIE2CHF0F0F0F0F09:BIP:P;P<PQPOP4PIPHG6P1P@PBPAPIC;P:P;P=fHRIC95>4PKP:P>PI11CQRHC4R8PNPKP:P>PI11COREC4PNPKP:P>P:P;P=fIRGC3RDPHPNPKP:P>PDPEPNPKP:P>fGRDPHPPPKP:P>PDPEP@P4PAPBC5PFPQP4PBPAPOE2F0F0F0F0F@9:QOP01OFQPKP:P>PG11CFRBPNPKP:P>PGPHPNPKP:P>P:P;P=fJREC3RTPBPNPKP:P>PTPHPNPKP:P>PIPBPPPKP8P@AMOA4PDPFPOP4PAPQE2DLF0F0F0F0F0P:P;P<PGPIPDPQPOG6P11OIDPKP:P>fLRO11CGRQC4R4PNPKP:P>PO11CIR8C4PNPKP:P>P:P;P=fMRBC3RHPQPNPKP:P>PHP8PNPKP:P>fKRHPQPPPKP:P>PHP8P@PDPAPFC5PEPGPDPFPAPIE2F0F0F0F0F@P0PKP:P>PB11CERFPNE?PKP:P>PBPQPNPKP:P>P:P;P=fNR8C3RTPFPNPKP:P>PTPQPNPKP:P>POPFPPPKP4P@AMIADPHPEPIPDPAPGE2DLF0F0F0F0P:P;P<PBPOPHPGPIG6P1P:P>fORI11CORGC4RD=8KNPKP:P>fPR4PGPNPKP:P>P:P;P=fQRFC3RQ11CBRTPNPKP:P>PQPGPNPKP:P>PIPTPPPKPDP@AMHAEP8PBPHPEPAPOE2DLF0F0F0F0P0PKP:P>PFPTPNE?PKP:P>P:P;P=fRREC3RD11C8RGPNPKP:P>PDPTPNPKP:P>P4PGPPPKP:P>P4PTP@POPAPHC5PIP8POPHPAPBE2F0F0F0F0P:P;P<PFP4PIPBPOG6P1PKP:P>fSROPCPIPNF=PKP:P>P:P;P=fURBC3RH11CFRTPNPKP:P>PH11C4RHPNPKP:P>POPTPPPKP:P>POPHP@PIPAP8C5PEPFPIP8PAP4E2F0F0F0F0P0PKP:P>P:P;P=fVR8C3RH11CERGPNE?PKP:P>PHPTPNPKP:P>fTRHPGPPPKP:P>PHPTP@P4PAPIC5POPEP4PIPAPFE2F0F0F0P:P;P<PBPHPOPFP4G6P1PKP:P>P:P;P=fXR4C311CHRFPNE?PKP:P>P:P;P=fYRIC3PFPNPKP:P>fWRT11CBRGPPPKP:P>PTPFP@POPAPEC5P8PBPOPEPAPHE2F0F0F0P0PKP:P>P:P;P=fZREC3PGPNE?PKP:P>P4PCP8DVPPPKP:P>P4PGC4P@PHPAPOC5PTP8PHPOPAPBE2F@P:P;P<PIP4PTPBPHG6P1PKP:P>P:P;P=f\R=C3PCPTPNF=PKP:P>f[RN11CIRHPPPKP:P>PNPCP4DVP@AMTA8PEPIPTP8PAP4E2DLF0P0PKP:P>P=PCPEPPF=PKP:P>P=PHP@P4PAPTC5PNPEP4PTPAPIE2F0P:P;P<f]RTP=PNPIP4G6P1PKP:P>f^R411C=RIPPE?PKP:P>f_RHPIP@PNPAPEC5P4PTPNPEPAP=E2F0P0PKP:P>f`R0PCPTP@P=PAPNC5F=PHP4P=PNPAPTE2P:P;P<faR<P0PHPTP=G6P1PKP:P>fbR=PCPHP@P4PAPTC5F=P=P<PHP4PAP0E2%C=fdR4fcRTP<P0PAP1E2PKP:P>feR;PCPTPPF=PKP:P>P;PRP@P<PAP0C5E?3DX12RR,P2P2PRP<PTP=P0PHPAP<E2PKP:P>P4PCP=PPF=RPPKP:P>P4PCP<P@P0PAPHC5F=RH'7P1PPPHP7P6CUCUCc3bW9W8P6P1O2n2001000000121000000W0W7P6P1O2n2001000000121000000W0WAP6P1O2n2001000000121000000W0W@P6P1O2n2001000000121000000W0W?P6P1O2n2001000000121000000W0W>P6P1O2n2001000000121000000W0W=P6P1O2n2011000000121000000W0W<P6P1O2n2011000000121000000W0W;P6P1O2n2011000000121000000W0W:P6P1O2n2011000000121000000W0W2P6P1O2n2011000000121000000W0P1O1n201100000021000011000W0XB2XD2X12X32WCX4?W5W6o"). Qed.

Lemma pbl_m16_8 : forall z : Z, (z mod 16 = 0)%Z -> (z mod 8 = 0)%Z.
Proof.
  intros z H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
  destruct H as [k Hk]. exists (2 * k)%Z. lia.
Qed.

Lemma pbl_rinv_out : forall (m m' : word -> option byte) (lo hi : Z), mem_grows m m' ->
  (forall a : word, ~ (lo <= u a < hi)%Z -> m' a = m a) -> rinv [(lo, (hi - lo)%Z)] m m'.
Proof.
  intros m m' lo hi G O. split; [exact G|]. intros a Ha. apply O. intros X.
  apply (Ha (lo, (hi - lo)%Z)); [left; reflexivity | unfold inreg; cbn [fst snd]; lia].
Qed.

Lemma pbl_rdn_keep : forall (m m' : word -> option byte) (lo hi z : Z) (n : nat), mem_grows m m' ->
  (forall a : word, ~ (lo <= u a < hi)%Z -> m' a = m a) -> (0 <= z)%Z -> (z + Z.of_nat n <= 2 ^ 64)%Z ->
  (hi <= z \/ z + Z.of_nat n <= lo)%Z -> rdn SEGS m' (Z_to_bv 64 z) n = rdn SEGS m (Z_to_bv 64 z) n.
Proof.
  intros m m' lo hi z n G O Hz Hzn D.
  apply (rinv_rdn SEGS [(lo, (hi - lo)%Z)] m m' z n (pbl_rinv_out m m' lo hi G O) Hz Hzn).
  intros r [<-|[]]. cbn [fst snd]. lia.
Qed.

Lemma pbl_rinv_frame : forall (m m' : word -> option byte) (lo n : Z) (x : word), rinv [(lo, n)] m m' -> ~ (lo <= u x < lo + n)%Z -> m' x = m x.
Proof. intros m m' lo n x [_ R] Hx. apply R. intros r [<-|[]]. exact Hx. Qed.

Lemma pbl_fs_chain : forall (fr fr1 fr3 : bvmap 5 word) (L1 L3 : list nat),
  (forall x, In x L1 -> In x [8; 9; 10; 11; 12; 13; 14; 15]%nat) -> (forall x, In x L3 -> In x [8; 9; 10; 11; 12; 13; 14; 15]%nat) ->
  reg_get fr3 8 = reg_get fr 8 -> reg_get fr3 9 = reg_get fr 9 ->
  (forall r : reg, ~ In (ridx r) L1 -> reg_get fr1 r = reg_get fr r) -> (forall r : reg, ~ In (ridx r) L3 -> reg_get fr3 r = reg_get fr1 r) ->
  forall r : reg, In (u r) fs_list -> reg_get fr3 r = reg_get fr r.
Proof.
  intros fr fr1 fr3 L1 L3 HL1 HL3 E8 E9 K1 K3 r Hr.
  destruct (@bv_eq_dec 5 r 8%bv) as [->|N8]; [exact E8|].
  destruct (@bv_eq_dec 5 r 9%bv) as [->|N9]; [exact E9|].
  rewrite (K3 r (fs_notin_p r L3 Hr N8 N9 HL3)). exact (K1 r (fs_notin_p r L1 Hr N8 N9 HL1)).
Qed.

Ltac pbl_inL := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx |- *; tauto.

Ltac pw_tac C A m md HW AL :=
  first [ assumption
        | (eapply (exW_clr_None C A m md _ _ _ _ HW); [cbv [ll_clr LLU16]; cbn [In]; left; reflexivity | lia | lia | lia | lia])
        | (eapply (exW_clr_None C A m md _ _ _ _ HW); [cbv [ll_clr LLU16]; cbn [In]; right; left; reflexivity | lia | lia | lia | lia])
        | exact (pbl_m16_8 _ AL)
        | (let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply (W_img16 C A m md j HW); lia)
        | lia ].

(* [comment removed for export] *)
Lemma pixDestroy_ocomp_W : forall (fx : FPState) C Ar A m md regs (s pp c dc w h : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 ->
  getr regs 10 = Z_to_bv 64 pp -> (pp mod 8 = 0)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 c) ->
  ocomp C Ar A m c dc w h -> (0 < (4 * (wpl_of w 8 * h)))%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (forall q, cblk c dc q -> live A' q = None) -> (forall q, ~ cblk c dc q -> live A' q = live A q) -> sub_live A' A ->
     POSTD C A' s pp m m' -> roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (104492 : word) m al_rom) md) S.
Proof.
  intros fx C Ar A m md regs s pp c dc w h ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 ALpp Hpp Hpp8 Rpp OC Hn HK.
  assert (SL : slotok C A s pp None) by (unfold slotok; lia).
  unfold ocomp in OC.
  destruct OC as [[-> ->] | (G1 & T1 & G2 & T2 & NE & LAr1 & LAr2 & L01 & L02 & LA1 & LA2 & PX)].
  - apply (pixDestroy_null_W (fx := fx) C A m md regs s pp None ret S CK HW H2 Hs16 ltac:(unfold ALLOC_STACK in Hlo; lia) Hhi H1 Hret
             ALpp H10 SL Rpp).
    intros m' regs' HW' CS PM OUT.
    pose proof (HK A m' (m_vmmaps md) regs') as HK'. rewrite with_vmmaps_same in HK'.
    apply HK'; clear HK'.
    + exact HW'.
    + exact CS.
    + intros q [X _]. exfalso. apply X. reflexivity.
    + intros q _. reflexivity.
    + apply sub_live_refl.
    + exact (POSTD_of_POSTM C A A s pp m m' PM (sub_live_refl A)).
    + apply roomtr_refl; lia.
  - apply (pixDestroy_free_W (fx := fx) C A m md regs s pp c (4 * (wpl_of w 8 * h)) (hdv w h 8 0 dc) None ret S CK HW H2 Hs16 Hlo Hhi
             H1 Hret H4 ALpp H10 SL Rpp PX eq_refl eq_refl eq_refl LA1 L01 LA2 L02 Hn ltac:(cbn; lia) ltac:(intros ? ? X; discriminate X)).
    intros A' m' vm' regs' HW' CS D1 D2 KEEP SUB PD Rpp' RT.
    apply (HK A' m' vm' regs' HW' CS); [| | exact SUB | exact PD | exact RT].
    + intros q [_ [-> | ->]]; [exact D1 | exact D2].
    + intros q NQ. apply KEEP.
      * intros E. apply NQ. split; [lia | left; exact E].
      * intros E. apply NQ. split; [lia | right; exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem pixBilateral_null_W : pixBilateral_null_contract.
Proof.
  unfold pixBilateral_null_contract.
  intros fr cs C A m md regs s ret S CK HW FZ H2 Hs16 Hlo Hhi H1 Hret H4 H10 F10 F11 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (PWv : PBL_WIN = 5296%Z) by reflexivity. assert (LSFv : LSF = 3376%Z) by reflexivity.
  pose proof (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SOK.
  unfold PC_pixBilateral.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | |].
  { apply (pbl_N al_rom fr cs regs m s). all: pw_tac C A m md HW Hs16. }
  intros fin (fr1 & cs1 & r1 & M1 & -> & FZ1 & RI1 & Q2 & Q10 & Q11 & Q12 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & AG1 & G8 & G9 & GK).
  destruct (rinv_WP2 C A A m md M1 [((s - 112)%Z, 112%Z)] s CK HW (sub_live_refl A) Hhi RI1
              ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])) as [HW1 PM1].
  replace (Z_to_bv 64 97988) with (0x17ec4 : word) by (apply bv_eq; reflexivity).
  apply (returnErrorPtr_W (fx := mkFP fr1 cs1) C A M1 md r1 s 73294 72715 27 12 ret (Z_to_bv 64 0) S CK HW1 Q2 Hs16 ltac:(lia) Hhi
           (eq_trans Q1 H1) Hret Q10 Q11 Q12 str_pbl_msgN str_pbl_proc).
  intros m2 r2 HW2 OUT2 GR2 CS2 V10.
  apply (HK fr1 cs1 m2 r2).
  - exact HW2.
  - exact FZ1.
  - eapply cs_kept_trans; [|exact CS2].
    apply cs_kept_of_rest; [rewrite Q2, H2; reflexivity | exact Q8 | exact Q9 |].
    intros r Hr. cbn [In cs_rest] in Hr.
    repeat (destruct Hr as [<-|Hr]; [first [exact Q18 | exact Q19 | exact Q20 | (apply AG1; notin_lit)]|]). destruct Hr.
  - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A M1 md m2); [exact CK | exact HW1 | exact OUT2 | lia | lia | exact Hhi].
  - exact V10.
  - apply (pbl_fs_chain fr fr fr1 [] [8; 9]%nat); [intros x [] | pbl_inL | exact G8 | exact G9 | intros r _; reflexivity | exact GK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pbl_case_cm : forall fr cs C A m md regs (s pixs w h d cm datas : Z) (ret : word) (S : TSet),
  (cm <> 0)%Z ->
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PBL_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pbl <= kR)%Z -> (RB_pbl w h d <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixr_new C A A' m' pixd datad (set_data (pix_hdr w h d) datad))) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_pbl) (bR - RB_pbl w h d) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_pixBilateral) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pixs w h d cm datas ret S Hcm CK HW FZ H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 F10 F11
    PXs HOK Hw Hh Lps Lds L0ps kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (PWv : PBL_WIN = 5296%Z) by reflexivity. assert (LSFv : LSF = 3376%Z) by reflexivity.
  pose proof RK_pbl_val as RKv. pose proof (RB_pbl_nonneg w h d ltac:(lia)) as RBn.
  pose proof PXs as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  pose proof (wf_cmap _ WF) as Rcm. cbn [p_cmap hdv] in Rcm.
  pose proof (PIX_rd_cmap SEGS m pixs _ PXs) as RDcm. cbn [p_cmap hdv] in RDcm.
  pose proof (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SOK.
  unfold PC_pixBilateral.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | |].
  { apply (pbl_CM al_rom fr cs regs m s pixs cm). all: pw_tac C A m md HW ALps. }
  intros fin (fr1 & cs1 & r1 & M1 & -> & FZ1 & RI1 & Q2 & Q10 & Q11 & Q12 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & AG1 & G8 & G9 & GK).
  destruct (rinv_WP2 C A A m md M1 [((s - 112)%Z, 112%Z)] s CK HW (sub_live_refl A) Hhi RI1
              ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])) as [HW1 PM1].
  replace (Z_to_bv 64 97988) with (0x17ec4 : word) by (apply bv_eq; reflexivity).
  apply (returnErrorPtr_W (fx := mkFP fr1 cs1) C A M1 md r1 s 73294 72715 27 12 ret (Z_to_bv 64 0) S CK HW1 Q2 Hs16 ltac:(lia) Hhi
           (eq_trans Q1 H1) Hret Q10 Q11 Q12 str_pbl_msgN str_pbl_proc).
  intros m2 r2 HW2 OUT2 GR2 CS2 V10.
  pose proof (HK fr1 cs1 A m2 (m_vmmaps md) r2) as HK'. rewrite with_vmmaps_same in HK'.
  apply HK'; clear HK'.
  - exact HW2.
  - exact FZ1.
  - eapply cs_kept_trans; [|exact CS2].
    apply cs_kept_of_rest; [rewrite Q2, H2; reflexivity | exact Q8 | exact Q9 |].
    intros r Hr. cbn [In cs_rest] in Hr.
    repeat (destruct Hr as [<-|Hr]; [first [exact Q18 | exact Q19 | exact Q20 | (apply AG1; notin_lit)]|]). destruct Hr.
  - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A M1 md m2); [exact CK | exact HW1 | exact OUT2 | lia | lia | exact Hhi].
  - left. split; [exact V10 | intros q; reflexivity].
  - apply (pbl_fs_chain fr fr fr1 [] [8; 9]%nat); [intros x [] | pbl_inL | exact G8 | exact G9 | intros r _; reflexivity | exact GK].
  - apply (aroom_mono _ _ _ _ _ _ Hrm); lia.
Qed.

Lemma pbl_case_d : forall fr cs C A m md regs (s pixs w h d cm datas : Z) (ret : word) (S : TSet),
  cm = 0%Z -> (d <> 8)%Z -> (d <> 32)%Z ->
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PBL_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pbl <= kR)%Z -> (RB_pbl w h d <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixr_new C A A' m' pixd datad (set_data (pix_hdr w h d) datad))) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_pbl) (bR - RB_pbl w h d) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_pixBilateral) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pixs w h d cm datas ret S Hcm Hd8 Hd32 CK HW FZ H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 F10 F11
    PXs HOK Hw Hh Lps Lds L0ps kR bR Hrm Hrk Hrb HK.
  subst cm.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (PWv : PBL_WIN = 5296%Z) by reflexivity. assert (LSFv : LSF = 3376%Z) by reflexivity.
  pose proof RK_pbl_val as RKv. pose proof (RB_pbl_nonneg w h d ltac:(lia)) as RBn.
  pose proof PXs as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  pose proof (wf_w _ WF) as Ww. pose proof (wf_h _ WF) as Wh. pose proof (wf_d _ WF) as Wd. cbn [p_w p_h p_d hdv] in Ww, Wh, Wd.
  pose proof HOK as (DV & _ & _ & _). pose proof (dval_range d DV) as Hd1.
  pose proof (PIX_rd_cmap SEGS m pixs _ PXs) as RDcm. cbn [p_cmap hdv] in RDcm.
  pose proof (PIX_rd_w SEGS m pixs _ PXs) as RDw. pose proof (PIX_rd_h SEGS m pixs _ PXs) as RDh.
  pose proof (PIX_rd_d SEGS m pixs _ PXs) as RDd. cbn [p_w p_h p_d hdv] in RDw, RDh, RDd.
  pose proof (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SOK.
  unfold PC_pixBilateral.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | |].
  { apply (pbl_D al_rom fr cs regs m s pixs w h d). all: pw_tac C A m md HW ALps. }
  intros fin (fr1 & cs1 & r1 & M1 & -> & FZ1 & RI1 & C1 & C8 & C9 & C18 & C19 & C20 & CG8 & CG9 & CW & CH & CD &
              Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q1 & Q10 & Q11 & Q12 & AG1 & G8 & G9 & GK).
  destruct (rinv_WP2 C A A m md M1 [((s - 112)%Z, 112%Z)] s CK HW (sub_live_refl A) Hhi RI1
              ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])) as [HW1 PM1].
  replace (Z_to_bv 64 97988) with (0x17ec4 : word) by (apply bv_eq; reflexivity).
  apply (returnErrorPtr_W (fx := mkFP fr1 cs1) C A M1 md r1 (s - 112) 71263 72715 20 12 (Z_to_bv 64 234768) (Z_to_bv 64 0) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 Q12 str_pbl_msgD str_pbl_proc).
  intros m2 r2 HW2 OUT2 GR2 CS2 V10.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 112)) by (csr; reflexivity).
  assert (K : forall (z : Z) (n : nat), (s - 112 <= z)%Z -> (z + Z.of_nat n <= s)%Z -> rdn SEGS m2 (Z_to_bv 64 z) n = rdn SEGS M1 (Z_to_bv 64 z) n)
    by (intros z n Z1 Z2; apply (pbl_rdn_keep M1 m2 (s - 112 - (16 + LSF)) (s - 112) z n GR2 OUT2); lia).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW2) | |].
  { apply (pbl_X_err al_rom fr1 cs1 r2 m2 s ret (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
             (Z_to_bv 64 (u (reg_get fr 8))) (Z_to_bv 64 (u (reg_get fr 9)))).
    all: first [ assumption | (rewrite K; [assumption | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]) | lia ]. }
  intros fin (fr3 & cs3 & r3 & M3 & -> & FZ3 & -> & X2 & X10 & X8 & X9 & X18 & X19 & X20 & AG3 & XG8 & XG9 & XGK).
  pose proof (HK fr3 cs3 A m2 (m_vmmaps md) r3) as HK'. rewrite with_vmmaps_same in HK'.
  apply HK'; clear HK'.
  - exact HW2.
  - exact FZ3.
  - apply cs_kept_of_rest; [rewrite X2, H2; reflexivity | exact X8 | exact X9 |].
    intros r Hr. cbn [In cs_rest] in Hr.
    repeat (destruct Hr as [<-|Hr]; [first [exact X18 | exact X19 | exact X20 | (csr; reflexivity)]|]). destruct Hr.
  - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A M1 md m2); [exact CK | exact HW1 | exact OUT2 | lia | lia | exact Hhi].
  - left. split; [rewrite X10; exact V10 | intros q; reflexivity].
  - apply (pbl_fs_chain fr fr1 fr3 [8; 9]%nat [8; 9]%nat);
      [pbl_inL | pbl_inL | rewrite XG8; apply Z_to_bv_bv_unsigned | rewrite XG9; apply Z_to_bv_bv_unsigned | exact GK | exact XGK].
  - apply (aroom_mono _ _ _ _ _ _ Hrm); lia.
Qed.

Lemma pbl_case_w : forall fr cs C A m md regs (s pixs w h d cm datas : Z) (ret : word) (S : TSet),
  cm = 0%Z -> (d = 8 \/ d = 32)%Z -> (w < 22 \/ h < 22)%Z ->
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PBL_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pbl <= kR)%Z -> (RB_pbl w h d <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixr_new C A A' m' pixd datad (set_data (pix_hdr w h d) datad))) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_pbl) (bR - RB_pbl w h d) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_pixBilateral) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pixs w h d cm datas ret S Hcm Hd Hwh CK HW FZ H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 F10 F11
    PXs HOK Hw Hh Lps Lds L0ps kR bR Hrm Hrk Hrb HK.
  subst cm.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (PWv : PBL_WIN = 5296%Z) by reflexivity. assert (LSFv : LSF = 3376%Z) by reflexivity.
  pose proof PXs as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  pose proof (wf_w _ WF) as Ww. pose proof (wf_h _ WF) as Wh. pose proof (wf_d _ WF) as Wd. cbn [p_w p_h p_d hdv] in Ww, Wh, Wd.
  pose proof (PIX_rd_cmap SEGS m pixs _ PXs) as RDcm. cbn [p_cmap hdv] in RDcm.
  pose proof (PIX_rd_w SEGS m pixs _ PXs) as RDw. pose proof (PIX_rd_h SEGS m pixs _ PXs) as RDh.
  pose proof (PIX_rd_d SEGS m pixs _ PXs) as RDd. cbn [p_w p_h p_d hdv] in RDw, RDh, RDd.
  pose proof (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SOK.
  assert (RKB : (RK_pixcopy <= RK_pbl)%Z) by (rewrite RK_pbl_val; unfold RK_pixcopy, RK_pix, RK_cmapcopy; lia).
  assert (RBB : (RB_pixT (4 * (wpl_of w d * h)) + RB_cmapT 0 <= RB_pbl w h d)%Z).
  { assert (RBP : forall n, (0 <= RB_pixT n)%Z) by (intros n; unfold RB_pixT, RB_hdrT; lia).
    pose proof (RB_bc_nonneg w h ltac:(lia)) as RBc.
    replace (RB_cmapT 0) with 0%Z by reflexivity.
    pose proof (RBP (4 * (wpl_of w d * h))%Z). pose proof (RBP (4 * (wpl_of w 8 * h))%Z).
    unfold RB_pbl, RB_pbl32, RB_bg. destruct Hd as [-> | ->].
    - rewrite Z.eqb_refl. lia.
    - replace (32 =? 8)%Z with false by reflexivity. rewrite Z.eqb_refl. lia. }
  unfold PC_pixBilateral.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | |].
  { destruct (Z.eq_dec d 8) as [Hd8|Hd8]; destruct (Z_lt_le_dec w 22) as [Hw22|Hw22].
    - apply (pbl_Ww_8 al_rom fr cs regs m s pixs w h d). all: pw_tac C A m md HW ALps.
    - apply (pbl_Wh_8 al_rom fr cs regs m s pixs w h d). all: pw_tac C A m md HW ALps.
    - apply (pbl_Ww_32 al_rom fr cs regs m s pixs w h d). all: pw_tac C A m md HW ALps.
    - apply (pbl_Wh_32 al_rom fr cs regs m s pixs w h d). all: pw_tac C A m md HW ALps. }
  intros fin (fr1 & cs1 & r1 & M1 & -> & FZ1 & RI1 & C1 & C8 & C9 & C18 & C19 & C20 & CG8 & CG9 & CW & CH & CD &
              Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q1 & Q10 & Q11 & AG1 & G8 & G9 & GK).
  destruct (rinv_WP2 C A A m md M1 [((s - 112)%Z, 112%Z)] s CK HW (sub_live_refl A) Hhi RI1
              ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])) as [HW1 PM1].
  replace (Z_to_bv 64 97832) with (0x17e28 : word) by (apply bv_eq; reflexivity).
  apply (lept_stderr1_W (fx := mkFP fr1 cs1) C A M1 md r1 (s - 112) 69395 72715 76 12 (Z_to_bv 64 234600) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 ltac:(apply fmts1_16; cbn [In]; repeat (first [left; reflexivity | right])) str_pbl_fmtW str_pbl_proc).
  intros m2 r2 HW2 OUT2 GR2 CS2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 112)) by (csr; reflexivity).
  assert (E8 : getr r2 8 = Z_to_bv 64 pixs) by (csr; reflexivity).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW2) | apply (pbl_W3 al_rom (mkFP fr1 cs1) r2 m2 s pixs ltac:(lia) ltac:(lia) E2 E8) |].
  intros fin (r3 & M3 & -> & -> & R1 & R2 & R10 & R11 & AG3).
  replace (Z_to_bv 64 107284) with (0x1a314 : word) by (apply bv_eq; reflexivity).
  assert (E4 : getr r3 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  assert (PX2 : PIXat m2 pixs (hdv w h d 0 datas)).
  { apply (PIXat_frame M1); [apply (PIXat_frame m); [exact PXs|] |].
    - intros x Hx. apply (pbl_rinv_frame m M1 (s - 112) 112 x RI1). lia.
    - intros x Hx. apply OUT2. lia. }
  apply (pixCopy_szT_W (fx := mkFP fr1 cs1) C A m2 md r3 (s - 112) pixs w h d 0 datas (CMAPV 0 0 0 0 0) (Z_to_bv 64 234612) S CK HW2 R2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) R1 ltac:(red; apply bv_eq; reflexivity)
           E4 R10 R11 PX2 HOK Hw Hh Lps Lds (or_introl eq_refl) kR bR Hrm ltac:(lia) ltac:(lia)).
  unfold TK. intros A1 m4 vm1 r4 HW4 CS4 PM4 OUT4 RM4.
  assert (F2 : getr r4 2 = Z_to_bv 64 (s - 112)) by (csr; reflexivity).
  assert (K : forall (z : Z) (n : nat), (s - 112 <= z)%Z -> (z + Z.of_nat n <= s)%Z -> rdn SEGS m4 (Z_to_bv 64 z) n = rdn SEGS M1 (Z_to_bv 64 z) n).
  { intros z n Z1 Z2. rewrite (FRM_rdn16 C (s - 112) m2 m4 z n CK (proj1 PM4)) by lia.
    apply (pbl_rdn_keep M1 m2 (s - 112 - LSF) (s - 112) z n GR2 OUT2); lia. }
  eapply rz_reach; [exact (w_pure _ _ _ _ HW4) | |].
  { apply (pbl_X_cp al_rom fr1 cs1 r4 m4 s ret (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
             (Z_to_bv 64 (u (reg_get fr 8))) (Z_to_bv 64 (u (reg_get fr 9)))).
    all: first [ assumption | (rewrite K; [assumption | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]) | lia ]. }
  intros fin (fr3 & cs3 & r5 & M5 & -> & FZ3 & -> & X2 & X10 & X8 & X9 & X18 & X19 & X20 & AG5 & XG8 & XG9 & XGK).
  apply (HK fr3 cs3 A1 m4 vm1 r5 HW4 FZ3).
  - apply cs_kept_of_rest; [rewrite X2, H2; reflexivity | exact X8 | exact X9 |].
    intros r Hr. cbn [In cs_rest] in Hr.
    repeat (destruct Hr as [<-|Hr]; [first [exact X18 | exact X19 | exact X20 | (csr; reflexivity)]|]). destruct Hr.
  - eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans.
    + eapply (POSTM_range C A M1 md m2); [exact CK | exact HW1 | exact OUT2 | lia | lia | lia].
    + eapply POSTM_mono; [|exact PM4]. lia.
  - destruct OUT4 as [[Z10 LV] | (pixd & cd & data & P10 & PT)].
    + left. split; [rewrite X10; exact Z10 | exact LV].
    + right. exists pixd, data. split; [rewrite X10; exact P10|].
      destruct PT as (Gp & Tp & Ap & Gd & Td & Ad & NE & L1 & L2 & L3 & L4 & L5 & L6 & PXd & CR).
      destruct CR as [[-> KEEP] | (ad & CMOK & _)];
        [| exfalso; destruct CMOK as [[X|[X|[X|X]]] _]; cbn in X; discriminate X].
      exact (conj Gp (conj Tp (conj Ap (conj Gd (conj Td (conj Ad (conj NE (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 (conj L6
               (conj KEEP (conj PXd eq_refl))))))))))))))).
  - apply (pbl_fs_chain fr fr1 fr3 [8; 9; 11; 12; 13; 14; 15]%nat [8; 9]%nat);
      [pbl_inL | pbl_inL | rewrite XG8; apply Z_to_bv_bv_unsigned | rewrite XG9; apply Z_to_bv_bv_unsigned | exact GK | exact XGK].
  - apply (aroom_mono _ _ _ _ _ _ RM4); lia.
Qed.

Lemma pblg_m16_8 : forall x, (x mod 16 = 0)%Z -> (x mod 8 = 0)%Z.
Proof. intros x H. pose proof (mod16_plus_mod8 x 0 H eq_refl) as E. rewrite Z.add_0_r in E. exact E. Qed.

Lemma pblg_m16_sub : forall s, (s mod 16 = 0)%Z -> ((s - 112) mod 16 = 0)%Z.
Proof. intros s H. pose proof (mod16_plus_mod16 s (-112) H eq_refl) as E. replace (s - 112)%Z with (s + -112)%Z by lia. exact E. Qed.

Lemma pblg_ne15 : forall r : reg, In (u r) fs_list -> r <> 15%bv.
Proof. intros r H E. subst r. vm_compute in H. repeat (destruct H as [H|H]; [discriminate H|]). exact H. Qed.

Ltac pblg_bvne := let E := fresh "E" in intro E; apply bv_eq in E; cbv in E; discriminate E.
Ltac pblg_nin := let H := fresh "H" in intro H; vm_compute in H; repeat (destruct H as [H|H]; [discriminate H|]); exact H.
Ltac pblg_sub := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx |- *; intuition.
Ltac pblg_fr :=
  repeat first [ rewrite fpv_get_same
               | rewrite fpv_get_other by pblg_bvne
               | match goal with FK : forall r : reg, ~ In (ridx r) _ -> reg_get ?F r = _ |- context [reg_get ?F _] => rewrite FK by pblg_nin end ].

Lemma pbl_case_g : forall fr cs C A m md regs (s pixs w h d cm datas : Z) (ret : word) (S : TSet),
  cm = 0%Z -> d = 8%Z -> (22 <= w)%Z -> (22 <= h)%Z ->
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PBL_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pbl <= kR)%Z -> (RB_pbl w h d <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixr_new C A A' m' pixd datad (set_data (pix_hdr w h d) datad))) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_pbl) (bR - RB_pbl w h d) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_pixBilateral) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pixs w h d cm datas ret S Hcm Hd Hw22 Hh22 CK HW FZ H2 Hs16 Hslo Hshi H1 Hret H4 H10 H11 H12 F10 F11
         PX HD Hw1 Hh1 Lp Ld Lp0 kR bR AR HkR HbR HK.
  subst cm d.
  change (RB_pbl w h 8) with (RB_bg w h) in HbR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold PBL_WIN in Hslo. unfold PC_pixBilateral.
  pose proof PX as (Pp0 & Pp64 & PWF & _).
  pose proof (wf_w _ PWF) as Ww. pose proof (wf_h _ PWF) as Wh. cbn [hdv p_w p_h] in Ww, Wh.
  destruct (exW_blk_rng C A m md pixs 64 CK HW Lp ltac:(lia) ltac:(lia)) as (Pq1 & Pq2 & Pq3).
  pose proof (ai_live_hull A m (m_vmmaps md) (Z_to_bv 64 pixs) 64 (w_inv _ _ _ _ HW) Lp) as (_ & Pal & _).
  rewrite u_Z2bv in Pal by lia.
  pose proof (pblg_m16_8 pixs Pal) as Pm8.
  pose proof (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(lia)) as SOK.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | apply (pbl_A_8 al_rom fr cs regs m s pixs w h 8);
    first [ assumption | exact (PIX_rd_cmap SEGS m pixs _ PX) | exact (PIX_rd_d SEGS m pixs _ PX) | exact (PIX_rd_w SEGS m pixs _ PX)
          | exact (PIX_rd_h SEGS m pixs _ PX) | (intros j Hj; apply (W_img16 C A m md j HW); lia) | lia ] |].
  intros fin (fr1 & cs1 & regs1 & M1 & -> & FZ1 & RI1 & S1 & S8 & S9 & S18 & S19 & S20 & G8 & G9 & Lw & Lh & Ld8
              & R2 & R8 & R9 & R18 & R19 & R20 & R10 & AG1 & F18 & F19 & FK1).
  assert (LR : local_regions C A A s [((s - 112)%Z, 112%Z)]) by (constructor; [left; cbn [fst snd]; lia | constructor]).
  destruct (rinv_WP2 C A A m md M1 [((s - 112)%Z, 112%Z)] s CK HW (sub_live_refl A) Hshi RI1 LR) as [HW1 PM1].
  eapply rz_reach; [exact (w_pure _ _ _ _ HW1) | exact (pbl_A1b al_rom fr1 cs1 regs1 M1 FZ1 R9) | intros fin (cB & -> & FZ2)].
  eapply rz_reach; [exact (w_pure _ _ _ _ HW1) | apply (pbl_A2 al_rom _ cB regs1 M1 s FZ2);
    first [ lia | assumption | (pblg_fr; first [reflexivity | assumption]) ] |].
  intros fin (fr3 & cs3 & regs3 & M3 & -> & FZ3 & -> & AG3 & FK3).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW1) | apply (pbl_A2b al_rom fr3 cs3 regs3 M1 FZ3); csr; reflexivity | intros fin (cD & -> & FZ4)].
  eapply rz_reach; [exact (w_pure _ _ _ _ HW1) | apply (pbl_A3_8 al_rom _ cD regs3 M1 s pixs FZ4);
    first [ lia | (csr; reflexivity) | (pblg_fr; first [reflexivity | assumption]) ] |].
  intros fin (fr5 & cs5 & regs5 & M5 & -> & FZ5 & -> & Q1 & Q2 & Q10 & Q11 & Q12 & AG5 & F510 & F511 & FK5).
  assert (KX : forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs5 regs' -> POSTM C A (s - 112) M1 m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixr_new C A A' m' pixd datad (set_data (pix_hdr w h 8) datad))) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr5 r) -> aroom A' vm' (kR - RK_bg) (bR - RB_bg w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' (getr regs5 1) m' al_rom) (with_vmmaps vm' md)) S).
  { intros fr' cs' A' m' vm' regs' HW' FZ' CK' PM' RES FS' AR'.
    assert (KC : forall (x : Z) (n : nat) bs, (s - 112 <= x)%Z -> (x + Z.of_nat n <= s)%Z ->
                   rdn SEGS M1 (Z_to_bv 64 x) n = Some bs -> rdn SEGS m' (Z_to_bv 64 x) n = Some bs).
    { intros x n bs X1 X2 E. rewrite <- E.
      apply (agree_rdn SEGS x (Z.of_nat n)); [eapply agree_of_FRM; [exact CK | exact (proj1 PM') | lia | lia | lia] | lia | lia | lia | lia]. }
    rewrite Q1.
    eapply rz_reach; [exact (w_pure _ _ _ _ HW') |
      apply (pbl_X_g8 al_rom fr' cs' regs' m' s ret (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
               (Z_to_bv 64 (u (reg_get fr 8))) (Z_to_bv 64 (u (reg_get fr 9))) FZ' ltac:(lia) Hret H1);
      first [ (apply KC; [lia | lia | assumption]) | (rewrite (cs_kept_get regs5 regs' 2%bv CK' cs2); exact Q2) ] |].
    intros fin (fr6 & cs6 & regs6 & M6 & -> & FZ6 & -> & X2 & X10 & X8 & X9 & X18 & X19 & X20 & AG6 & G68 & G69 & FK6).
    apply (HK fr6 cs6 A' m' vm' regs6 HW' FZ6).
    - apply cs_kept_intro; csr; reflexivity.
    - exact (POSTM_trans C A s m M1 m' PM1 (POSTM_mono C A (s - 112) s M1 m' ltac:(lia) PM')).
    - rewrite X10. exact RES.
    - intros r Hr.
      destruct (decide (r = 8%bv)) as [->|N8]; [rewrite G68; apply Z_to_bv_bv_unsigned|].
      destruct (decide (r = 9%bv)) as [->|N9]; [rewrite G69; apply Z_to_bv_bv_unsigned|].
      pose proof (pblg_ne15 r Hr) as N15.
      rewrite FK6 by (apply (fs_notin_p r _ Hr N8 N9); pblg_sub).
      rewrite (FS' r Hr).
      rewrite FK5 by (apply (fs_notin_p r _ Hr N8 N9); pblg_sub).
      rewrite (fpv_get_other _ _ _ _ N15).
      rewrite FK3 by (apply (fs_notin_p r _ Hr N8 N9); pblg_sub).
      rewrite (fpv_get_other _ _ _ _ N15).
      apply FK1. apply (fs_notin_p r _ Hr N8 N9); pblg_sub.
    - assert (RKb : (RK_bg <= RK_pbl)%Z) by (pose proof RK_pbl_val as RV; unfold RK_pbl, RK_pix in *; lia).
      change (RB_pbl w h 8) with (RB_bg w h).
      apply (aroom_mono A' vm' (kR - RK_bg) (bR - RB_bg w h)); [exact AR' | lia | lia]. }
  assert (RKb : (RK_bg <= RK_pbl)%Z) by (pose proof RK_pbl_val as RV; unfold RK_pbl, RK_pix in *; lia).
  eapply (pixBilateralGray_W H_amb H_gev H_bd) with (C := C) (A := A) (s := (s - 112)%Z) (pixs := pixs) (w := w) (h := h) (datas := datas)
    (ret := getr regs5 1) (kR := kR) (bR := bR).
  - exact CK.
  - exact HW1.
  - exact FZ5.
  - exact Q2.
  - apply pblg_m16_sub. exact Hs16.
  - unfold BG_WIN, BC_WIN. lia.
  - lia.
  - reflexivity.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - csr. reflexivity.
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - exact F510.
  - exact F511.
  - eapply PIXat_frame; [exact PX |]. intros x Hx. apply (proj2 RI1). intros r [<-|[]]. unfold inreg. cbn [fst snd]. lia.
  - exact HD.
  - exact Hw22.
  - exact Hh22.
  - exact Lp.
  - exact Ld.
  - exact Lp0.
  - exact AR.
  - lia.
  - exact HbR.
  - intros fr' cs' A' m' vm' regs' HW' FZ' CK' PM' R10' LV' FS' AR'.
    apply (KX fr' cs' A' m' vm' regs' HW' FZ' CK' PM' (or_introl (conj R10' LV')) FS' AR').
  - intros fr' cs' A' m' vm' regs' pixd datad HW' FZ' CK' PM' R10' PN' FS' AR'.
    apply (KX fr' cs' A' m' vm' regs' HW' FZ' CK' PM' (or_intror (ex_intro _ pixd (ex_intro _ datad (conj R10' PN')))) FS' AR').
Qed.

Lemma rgb_rz_pc : forall (fx : FPState) regs (pc pc' : word) (m : word -> option byte) md (S : TSet),
  realizes SEGS (mkCfg (@mkst fx regs pc' m al_rom) md) S -> pc' = pc -> realizes SEGS (mkCfg (@mkst fx regs pc m al_rom) md) S.
Proof. intros fx regs pc pc' m md S H E. subst pc'. exact H. Qed.

Lemma rgb_m16_8 : forall z : Z, (z mod 16 = 0)%Z -> (z mod 8 = 0)%Z.
Proof.
  intros z H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
  destruct H as [k Hk]. exists (2 * k)%Z. lia.
Qed.

Lemma rgb_rinv_frame : forall (m m' : word -> option byte) (lo n : Z) (x : word), rinv [(lo, n)] m m' -> ~ (lo <= u x < lo + n)%Z -> m' x = m x.
Proof. intros m m' lo n x [_ R] Hx. apply R. intros r [<-|[]]. exact Hx. Qed.

Lemma rgb_frmx_rdn : forall C s pp (m m' : word -> option byte) (a : Z) (n : nat), Cok C -> FRMx C s pp m m' ->
  (s <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z -> (c_top C - LSTK <= s)%Z -> (a + Z.of_nat n <= pp \/ pp + 8 <= a)%Z ->
  rdn SEGS m' (Z_to_bv 64 a) n = rdn SEGS m (Z_to_bv 64 a) n.
Proof.
  intros C s pp m m' a n CK FX Ha Han Hs D.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
  intros x Hx. rewrite u_Z2bv in Hx by lia.
  apply FX.
  - apply above_not_gap. lia.
  - intro G. apply pin_glob in G. unfold inZ in G. lia.
  - intro G. apply pin_errno in G. unfold inZ in G. lia.
  - unfold hcell. lia.
  - unfold scratch. lia.
  - unfold inslot. lia.
Qed.

Lemma rgb_ok_range : forall C Ar A m r dr w h, ocomp C Ar A m r dr w h -> (0 <= r < 2 ^ 64)%Z.
Proof.
  intros C Ar A m r dr w h OC. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct OC as [[-> _] | (G1 & T1 & _)]; lia.
Qed.

Lemma rgb_ok_fr : forall C Ar A m r dr w h, ocomp C Ar A m r dr w h -> r <> 0%Z ->
  live Ar (Z_to_bv 64 r) = None /\ live Ar (Z_to_bv 64 dr) = None.
Proof.
  intros C Ar A m r dr w h OC Hr.
  destruct OC as [[E _] | (_ & _ & _ & _ & _ & L1 & L2 & _)]; [contradiction | split; assumption].
Qed.

Lemma rgb_ok_live : forall C Ar A m r dr w h, ocomp C Ar A m r dr w h -> r <> 0%Z ->
  live A (Z_to_bv 64 r) = Some 64%Z /\ live A (Z_to_bv 64 dr) = Some (4 * (wpl_of w 8 * h))%Z.
Proof.
  intros C Ar A m r dr w h OC Hr.
  destruct OC as [[E _] | (_ & _ & _ & _ & _ & _ & _ & _ & _ & L1 & L2 & _)]; [contradiction | split; assumption].
Qed.

Lemma rgb_disj : forall C Ar A m r dr w h (c dc : Z), ocomp C Ar A m r dr w h ->
  live A (Z_to_bv 64 c) = None -> live A (Z_to_bv 64 dc) = None -> forall q, cblk r dr q -> ~ cblk c dc q.
Proof.
  intros C Ar A m r dr w h c dc OC L1 L2 q [Hr Q] [_ Q'].
  destruct (rgb_ok_live C Ar A m r dr w h OC Hr) as [LA1 LA2].
  destruct Q as [-> | ->]; destruct Q' as [E | E]; congruence.
Qed.

Lemma rgb_ok_fresh : forall C Ar A A' (m m' : word -> option byte) r dr w h (p dp : Z), ocomp C Ar A m r dr w h ->
  live A (Z_to_bv 64 p) = None -> live A (Z_to_bv 64 dp) = None ->
  (forall q, q <> Z_to_bv 64 p -> q <> Z_to_bv 64 dp -> live A' q = live A q) ->
  (forall x : word, (4096 <= r)%Z -> (r + 64 <= alloc_top (c_vm C))%Z -> live A (Z_to_bv 64 r) = Some 64%Z -> (r <= u x < r + 64)%Z -> m' x = m x) ->
  ocomp C Ar A' m' r dr w h.
Proof.
  intros C Ar A A' m m' r dr w h p dp OC L1 L2 K MEM.
  apply (ocomp_keep C Ar A A' m m' r dr w h OC).
  - intros x LA T G X. exact (MEM x G T LA X).
  - intros q k CB LQ. rewrite K; [exact LQ | |]; intro E; rewrite E in LQ; congruence.
Qed.

Lemma rgb_ok_same : forall C Ar A A' (m m' : word -> option byte) r dr w h, ocomp C Ar A m r dr w h ->
  (forall q, live A' q = live A q) ->
  (forall x : word, (4096 <= r)%Z -> (r + 64 <= alloc_top (c_vm C))%Z -> live A (Z_to_bv 64 r) = Some 64%Z -> (r <= u x < r + 64)%Z -> m' x = m x) ->
  ocomp C Ar A' m' r dr w h.
Proof.
  intros C Ar A A' m m' r dr w h OC K MEM.
  apply (ocomp_keep C Ar A A' m m' r dr w h OC).
  - intros x LA T G X. exact (MEM x G T LA X).
  - intros q k _ LQ. rewrite K. exact LQ.
Qed.

Lemma rgb_ok_free : forall C Ar A A' (m m' : word -> option byte) r dr w h (c dc : Z), ocomp C Ar A m r dr w h ->
  (forall q, cblk r dr q -> ~ cblk c dc q) -> (forall q, ~ cblk c dc q -> live A' q = live A q) ->
  (forall x : word, (4096 <= r)%Z -> (r + 64 <= alloc_top (c_vm C))%Z -> live A' (Z_to_bv 64 r) = Some 64%Z -> (r <= u x < r + 64)%Z -> m' x = m x) ->
  ocomp C Ar A' m' r dr w h.
Proof.
  intros C Ar A A' m m' r dr w h c dc OC DJ K MEM.
  apply (ocomp_keep C Ar A A' m m' r dr w h OC).
  - intros x LA T G X. apply MEM; try assumption.
    rewrite K; [exact LA|]. apply DJ. split; [lia | left; reflexivity].
  - intros q k CB LQ. rewrite K; [exact LQ | exact (DJ q CB)].
Qed.

Lemma rgb_sub_k : forall (A Ak A' : AS) (c dc : Z), sub_live A Ak ->
  (c <> 0%Z -> live A (Z_to_bv 64 c) = None /\ live A (Z_to_bv 64 dc) = None) ->
  (forall q, ~ cblk c dc q -> live A' q = live Ak q) -> sub_live A A'.
Proof.
  intros A Ak A' c dc SL F K q k LQ. rewrite K; [exact (SL q k LQ)|].
  intros [Hc [-> | ->]]; destruct (F Hc) as [F1 F2]; congruence.
Qed.

Lemma rgb_lv : forall (A Ak A2 A3 A4 : AS) (P : word -> Prop) (c dc pt dt : Z),
  (forall q, P q -> live Ak q = live A q) ->
  live A (Z_to_bv 64 pt) = None -> live A (Z_to_bv 64 dt) = None -> pt <> 0%Z ->
  (forall q, q <> Z_to_bv 64 pt -> q <> Z_to_bv 64 dt -> live A2 q = live Ak q) ->
  (forall q, ~ cblk c dc q -> live A3 q = live A2 q) ->
  (forall q, cblk pt dt q -> live A4 q = None) -> (forall q, ~ cblk pt dt q -> live A4 q = live A3 q) ->
  forall q, P q -> ~ cblk c dc q -> live A4 q = live A q.
Proof.
  intros A Ak A2 A3 A4 P c dc pt dt LV L1 L2 Hpt K2 K3 F4 K4 q Pq Nc.
  destruct (cblk_dec pt dt q) as [CB | NCB].
  - rewrite (F4 q CB). destruct CB as [_ [-> | ->]]; symmetry; assumption.
  - rewrite (K4 q NCB), (K3 q Nc), K2.
    + exact (LV q Pq).
    + intro E. apply NCB. split; [exact Hpt | left; exact E].
    + intro E. apply NCB. split; [exact Hpt | right; exact E].
Qed.

Lemma rgb_fs_seg : forall (fr fk fk' : bvmap 5 word) (L : list nat),
  (forall x, In x L -> In x [8; 9; 10; 11; 12; 13; 14; 15]%nat) ->
  (forall x : reg, In (u x) fs_list -> x <> 8%bv -> x <> 9%bv -> reg_get fk x = reg_get fr x) ->
  (forall x : reg, ~ In (ridx x) L -> reg_get fk' x = reg_get fk x) ->
  forall x : reg, In (u x) fs_list -> x <> 8%bv -> x <> 9%bv -> reg_get fk' x = reg_get fr x.
Proof.
  intros fr fk fk' L HL F K x Hx N8 N9. rewrite (K x (fs_notin_p x L Hx N8 N9 HL)). exact (F x Hx N8 N9).
Qed.

Lemma rgb_fs_set : forall (fr fk : bvmap 5 word) v,
  (forall x : reg, In (u x) fs_list -> x <> 8%bv -> x <> 9%bv -> reg_get fk x = reg_get fr x) ->
  forall x : reg, In (u x) fs_list -> x <> 8%bv -> x <> 9%bv -> reg_get (bvmap_set 15%bv v fk) x = reg_get fr x.
Proof.
  intros fr fk v F x Hx N8 N9. rewrite fpv_get_other; [exact (F x Hx N8 N9)|].
  intros ->. vm_compute in Hx. intuition discriminate.
Qed.

Lemma rgb_fs_gray : forall (fr fk fk' : bvmap 5 word),
  (forall x : reg, In (u x) fs_list -> x <> 8%bv -> x <> 9%bv -> reg_get fk x = reg_get fr x) ->
  (forall x : reg, In (u x) fs_list -> reg_get fk' x = reg_get fk x) ->
  forall x : reg, In (u x) fs_list -> x <> 8%bv -> x <> 9%bv -> reg_get fk' x = reg_get fr x.
Proof. intros fr fk fk' F K x Hx N8 N9. rewrite (K x Hx). exact (F x Hx N8 N9). Qed.

Definition rgb_fk (m M : word -> option byte) (lo hi : Z) : Prop :=
  forall z (n : nat), (lo <= z)%Z -> (z + Z.of_nat n <= hi)%Z -> rdn SEGS m (Z_to_bv 64 z) n = rdn SEGS M (Z_to_bv 64 z) n.

Lemma rgb_fk_refl : forall M lo hi, rgb_fk M M lo hi.
Proof. intros M lo hi z n _ _. reflexivity. Qed.

Lemma rgb_fk_frm : forall C s1 (mk mk' M : word -> option byte) lo hi, Cok C -> FRM C s1 mk mk' ->
  (c_top C - LSTK <= s1)%Z -> (s1 <= lo)%Z -> (hi <= 2 ^ 64)%Z -> rgb_fk mk M lo hi -> rgb_fk mk' M lo hi.
Proof.
  intros C s1 mk mk' M lo hi CK FR Hs Hl Hh FK z n Z1 Z2.
  rewrite (FRM_rdn16 C s1 mk mk' z n CK FR) by lia. exact (FK z n Z1 Z2).
Qed.

Lemma rgb_fk_rinv : forall (mk mk' M : word -> option byte) a k lo hi, rinv [(a, k)] mk mk' ->
  (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z -> (a + k <= lo \/ hi <= a)%Z -> rgb_fk mk M lo hi -> rgb_fk mk' M lo hi.
Proof.
  intros mk mk' M a k lo hi RI Hl Hh D FK z n Z1 Z2.
  rewrite (rinv_rdn SEGS [(a, k)] mk mk' z n RI); [exact (FK z n Z1 Z2) | lia | lia |].
  intros r [<-|[]]. cbn [fst snd]. lia.
Qed.

Lemma rgb_fk_frmx : forall C s1 pp (mk mk' M : word -> option byte) lo hi, Cok C -> FRMx C s1 pp mk mk' ->
  (c_top C - LSTK <= s1)%Z -> (s1 <= lo)%Z -> (hi < 2 ^ 64)%Z -> (pp + 8 <= lo \/ hi <= pp)%Z -> rgb_fk mk M lo hi -> rgb_fk mk' M lo hi.
Proof.
  intros C s1 pp mk mk' M lo hi CK FX Hs Hl Hh D FK z n Z1 Z2.
  rewrite (rgb_frmx_rdn C s1 pp mk mk' z n CK FX) by lia. exact (FK z n Z1 Z2).
Qed.

Lemma rgb_fk_use : forall (mk M : word -> option byte) lo hi z (n : nat) v, rgb_fk mk M lo hi ->
  (lo <= z)%Z -> (z + Z.of_nat n <= hi)%Z -> rdn SEGS M (Z_to_bv 64 z) n = v -> rdn SEGS mk (Z_to_bv 64 z) n = v.
Proof. intros mk M lo hi z n v FK Z1 Z2 E. rewrite (FK z n Z1 Z2). exact E. Qed.

Lemma rgb_px_livk : forall A (m m' : word -> option byte) p v, PIXat m p v -> LIVK A m m' ->
  live A (Z_to_bv 64 p) = Some 64%Z -> PIXat m' p v.
Proof.
  intros A m m' p v PX LK L. pose proof PX as (Hp0 & Hp64 & _).
  apply (PIXat_frame m); [exact PX|]. intros x Hx.
  apply (LIVK_byte A m m' (Z_to_bv 64 p) 64 x LK L). rewrite u_Z2bv by lia. lia.
Qed.

Lemma rgb_px_rinv : forall (m m' : word -> option byte) p v lo n, PIXat m p v -> rinv [(lo, n)] m m' ->
  (p + 64 <= lo)%Z -> PIXat m' p v.
Proof.
  intros m m' p v lo n PX RI Hp.
  apply (PIXat_frame m); [exact PX|]. intros x Hx. apply (rgb_rinv_frame m m' lo n x RI). lia.
Qed.

Lemma rgb_px_postd : forall C A s pp (m m' : word -> option byte) p v, PIXat m p v -> POSTD C A s pp m m' ->
  live A (Z_to_bv 64 p) = Some 64%Z -> (p + 64 <= pp)%Z -> PIXat m' p v.
Proof.
  intros C A s pp m m' p v PX PD L Hp. pose proof PX as (Hp0 & Hp64 & _).
  apply (PIXat_frame m); [exact PX|]. intros x Hx.
  apply (POSTD_blk_byte C A s pp m m' (Z_to_bv 64 p) 64 x PD L); [rewrite u_Z2bv by lia; lia | unfold inslot; lia].
Qed.

Lemma rgb_mem_livk : forall C A (m m' : word -> option byte) (r : Z), LIVK A m m' ->
  forall x : word, (4096 <= r)%Z -> (r + 64 <= alloc_top (c_vm C))%Z -> live A (Z_to_bv 64 r) = Some 64%Z -> (r <= u x < r + 64)%Z -> m' x = m x.
Proof.
  intros C A m m' r LK x G T L X. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  apply (LIVK_byte A m m' (Z_to_bv 64 r) 64 x LK L). rewrite u_Z2bv by lia. lia.
Qed.

Lemma rgb_mem_rinv : forall C A (m m' : word -> option byte) (r lo n : Z), rinv [(lo, n)] m m' -> (alloc_top (c_vm C) <= lo)%Z ->
  forall x : word, (4096 <= r)%Z -> (r + 64 <= alloc_top (c_vm C))%Z -> live A (Z_to_bv 64 r) = Some 64%Z -> (r <= u x < r + 64)%Z -> m' x = m x.
Proof. intros C A m m' r lo n RI Hl x G T L X. apply (rgb_rinv_frame m m' lo n x RI). lia. Qed.

Lemma rgb_mem_postd : forall C A s pp (m m' : word -> option byte) (r : Z), POSTD C A s pp m m' -> (alloc_top (c_vm C) <= pp)%Z ->
  forall x : word, (4096 <= r)%Z -> (r + 64 <= alloc_top (c_vm C))%Z -> live A (Z_to_bv 64 r) = Some 64%Z -> (r <= u x < r + 64)%Z -> m' x = m x.
Proof.
  intros C A s pp m m' r PD Hp x G T L X. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  apply (POSTD_blk_byte C A s pp m m' (Z_to_bv 64 r) 64 x PD L); [rewrite u_Z2bv by lia; lia | unfold inslot; lia].
Qed.

Lemma rgb_room0 : forall A vm A' vm' k b, aroom A vm k b -> roomtr A vm A' vm' 0 0 -> aroom A' vm' k b.
Proof.
  intros A vm A' vm' k b R T. pose proof (aroom_nonneg _ _ _ _ R) as [K B].
  pose proof (T k b R ltac:(lia) ltac:(lia)) as R'. rewrite !Z.sub_0_r in R'. exact R'.
Qed.

Lemma rgb_cblk_none : forall C Ar A m r dr w h, ocomp C Ar A m r dr w h -> forall q, cblk r dr q -> live Ar q = None.
Proof.
  intros C Ar A m r dr w h OC q [Hr [-> | ->]]; destruct (rgb_ok_fr C Ar A m r dr w h OC Hr) as [L1 L2]; assumption.
Qed.

Lemma rgb_notin : forall C Ar A m r dr w h (c : Z), ocomp C Ar A m r dr w h -> live A (Z_to_bv 64 c) = None -> ~ cblk r dr (Z_to_bv 64 c).
Proof.
  intros C Ar A m r dr w h c OC L [Hr [E | E]]; destruct (rgb_ok_live C Ar A m r dr w h OC Hr) as [L1 L2]; congruence.
Qed.

Lemma rgb_lv_end : forall (A A10 A11 A12 A13 A14 : AS) (r dr g dg b db : Z) (P : word -> Prop),
  (forall q, ~ cblk r dr q -> ~ cblk g dg q -> ~ cblk b db q -> live A10 q = live A q) ->
  (forall q, cblk r dr q -> live A q = None) -> (forall q, cblk g dg q -> live A q = None) -> (forall q, cblk b db q -> live A q = None) ->
  (forall q, P q -> live A11 q = live A10 q) ->
  (forall q, cblk r dr q -> live A12 q = None) -> (forall q, ~ cblk r dr q -> live A12 q = live A11 q) ->
  (forall q, cblk g dg q -> live A13 q = None) -> (forall q, ~ cblk g dg q -> live A13 q = live A12 q) ->
  (forall q, cblk b db q -> live A14 q = None) -> (forall q, ~ cblk b db q -> live A14 q = live A13 q) ->
  forall q, P q -> live A14 q = live A q.
Proof.
  intros A A10 A11 A12 A13 A14 r dr g dg b db P LV Nr Ng Nb K11 F12 K12 F13 K13 F14 K14 q Pq.
  destruct (cblk_dec b db q) as [Cb | Cb]; [rewrite (F14 q Cb), (Nb q Cb); reflexivity|]. rewrite (K14 q Cb).
  destruct (cblk_dec g dg q) as [Cg | Cg]; [rewrite (F13 q Cg), (Ng q Cg); reflexivity|]. rewrite (K13 q Cg).
  destruct (cblk_dec r dr q) as [Cr | Cr]; [rewrite (F12 q Cr), (Nr q Cr); reflexivity|]. rewrite (K12 q Cr), (K11 q Pq).
  exact (LV q Cr Cg Cb).
Qed.

Ltac rgb_ne := let E := fresh "E" in intro E; apply bv_eq in E; cbv in E; discriminate E.
Ltac rgb_nin := vm_compute; lia.
Ltac rgb_inL := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx |- *; tauto.
Ltac rgb_fr1 :=
  match goal with
  | |- context [reg_get (bvmap_set ?r ?v ?f) ?r] => rewrite (fpv_get_same f r v)
  | |- context [reg_get (bvmap_set ?r ?v ?f) ?r'] => rewrite (fpv_get_other f r r' v) by rgb_ne
  | |- context [reg_get ?f' ?r] =>
      first [ match goal with E : reg_get f' r = _ |- _ => rewrite E end
            | match goal with K : forall x : reg, ~ In (ridx x) _ -> reg_get f' x = reg_get _ x |- _ => rewrite (K r) by rgb_nin end
            | match goal with K : forall x : reg, In (u x) fs_list -> reg_get f' x = reg_get _ x |- _ =>
                rewrite (K r) by first [exact in_fs8 | exact in_fs9] end ]
  end.
Ltac rgb_fr := repeat rgb_fr1.
Ltac rgb_pw C A m md HW AL :=
  first [ assumption
        | exact (rgb_m16_8 _ AL)
        | (let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply (W_img16 C A m md j HW); lia)
        | lia ].
Ltac rgb_lc := apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
Ltac rgb_m16 Hs16 := rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity.
Ltac rgb_m8 Hs16 := rewrite <- Zminus_mod_idemp_l, (rgb_m16_8 _ Hs16); reflexivity.
Ltac rgb_rok := red; apply bv_eq; reflexivity.
Ltac rgb_sok CK HW := apply (W_sok_win _ _ _ _ _ _ CK HW); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].

Lemma pbl_case_rgb : forall fr cs C A m md regs (s pixs w h d cm datas : Z) (ret : word) (S : TSet),
  cm = 0%Z -> d = 32%Z -> (22 <= w)%Z -> (22 <= h)%Z ->
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PBL_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pbl <= kR)%Z -> (RB_pbl w h d <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixr_new C A A' m' pixd datad (set_data (pix_hdr w h d) datad))) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_pbl) (bR - RB_pbl w h d) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_pixBilateral) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pixs w h d cm datas ret S Hcm Hd Hw22 Hh22 CK HW FZ H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 F10 F11
    PXs HOK Hw Hh Lps Lds L0ps kR bR Hrm Hrk Hrb HK.
  subst cm d.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (PWv : PBL_WIN = 5296%Z) by reflexivity. assert (LSFv : LSF = 3376%Z) by reflexivity.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXs as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  pose proof (wf_w _ WF) as Ww. pose proof (wf_h _ WF) as Wh. cbn [p_w p_h hdv] in Ww, Wh.
  pose proof (PIX_rd_cmap SEGS m pixs _ PXs) as RDcm. cbn [p_cmap hdv] in RDcm.
  pose proof (PIX_rd_w SEGS m pixs _ PXs) as RDw. pose proof (PIX_rd_h SEGS m pixs _ PXs) as RDh.
  pose proof (PIX_rd_d SEGS m pixs _ PXs) as RDd. cbn [p_w p_h p_d hdv] in RDw, RDh, RDd.
  pose proof (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SOK.
  assert (WPL8 : (1 <= wpl_of w 8)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia).
  assert (N8 : (0 < 4 * (wpl_of w 8 * h))%Z) by nia.
  pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))) as RB8. pose proof (RB_pixT_nonneg (4 * (wpl_of w 32 * h))) as RB32.
  pose proof (RB_bc_nonneg w h ltac:(lia)) as RBc.
  assert (RBg : (0 <= RB_bg w h)%Z) by (unfold RB_bg; lia).
  assert (RBv : RB_pbl w h 32 = (3 * (RB_pixT (4 * (wpl_of w 8 * h)) + RB_bg w h) + RB_pixT (4 * (wpl_of w 32 * h)))%Z) by reflexivity.
  assert (RKp : RK_pix = 2%Z) by reflexivity. assert (RKg : RK_bg = 87%Z) by reflexivity.
  assert (RKv : RK_pbl = 269%Z) by reflexivity.
  rewrite RBv in Hrb.
  assert (FS0 : forall x : reg, In (u x) fs_list -> x <> 8%bv -> x <> 9%bv -> reg_get fr x = reg_get fr x) by reflexivity.
  unfold PC_pixBilateral.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | |].
  { apply (pbl_A_32 al_rom fr cs regs m s pixs w h 32). all: rgb_pw C A m md HW ALps. }
  intros fin (fr1 & cs1 & r1 & M1 & -> & FZ1 & RI1 & C1 & C8 & C9 & C18 & C19 & C20 & CG8 & CG9 & CW & CH & CD &
              Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q10 & AG1 & G8 & G9 & GK).
  destruct (rinv_WP2 C A A m md M1 [((s - 112)%Z, 112%Z)] s CK HW (sub_live_refl A) Hhi RI1 ltac:(rgb_lc)) as [HW1 PM1].
  pose proof (rgb_fs_seg fr fr fr1 [8; 9; 11; 12; 13; 14; 15]%nat ltac:(rgb_inL) FS0 GK) as FS1.
  assert (PXs1 : PIXat M1 pixs (hdv w h 32 0 datas)).
  { apply (PIXat_frame m); [exact PXs|]. intros x Hx. apply (rgb_rinv_frame m M1 (s - 112) 112 x RI1). lia. }
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | apply (pbl_A1b al_rom fr1 cs1 r1 M1 FZ1 Q9) |].
  intros fin (cs2 & -> & FZ2).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | apply (pbl_A2 al_rom _ cs2 r1 M1 s FZ2 ltac:(lia) Q2 Q18); rgb_fr; reflexivity |].
  intros fin (fr3 & cs3 & r3 & M3 & -> & FZ3 & -> & AG3 & GK3).
  pose proof (rgb_fs_seg fr _ fr3 [14; 15]%nat ltac:(rgb_inL) (rgb_fs_set fr fr1 _ FS1) GK3) as FS3.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | apply (pbl_A2b al_rom fr3 cs3 r3 M1 FZ3); csr; reflexivity |].
  intros fin (cs4 & -> & FZ4).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | apply (pbl_A3_32 al_rom _ cs4 r3 M1 s pixs FZ4 ltac:(lia) ltac:(lia));
                    first [csr; reflexivity | rgb_fr; reflexivity] |].
  intros fin (fr5 & cs5 & r5 & M5 & -> & FZ5 & -> & Q51 & Q52 & Q510 & Q511 & AG5 & GK5).
  pose proof (rgb_fs_seg fr _ fr5 [14; 15]%nat ltac:(rgb_inL) (rgb_fs_set fr fr3 _ FS3) GK5) as FS5.
  apply (H_rgb (mkFP fr5 cs5) C A M1 md r5 (s - 112)%Z pixs w h datas 0%Z _ S CK HW1 Q52
           ltac:(rgb_m16 Hs16) ltac:(unfold RGB_STACK; lia) ltac:(lia) Q51 ltac:(rgb_rok) ltac:(csr; reflexivity) Q510 Q511 ltac:(lia)
           PXs1 HOK Hw Hh Lps Lds kR bR Hrm ltac:(lia) ltac:(lia)).
  intros A2 m2 vm2 r6 pt dt HW2 CS6 PM2 P6 PN RM2.
  destruct PN as (Gt & Tt & At & Gdt & Tdt & Adt & NEt & Lt1 & Lt2 & Lt3 & Lt4 & Lt5 & Lt6 & Kt & PXt & Dt).
  cbn [p_wpl p_h set_data pix_hdr] in Tdt, Lt6.
  pose proof (sub_live_new2 A A2 _ _ _ _ Lt1 Lt2 Lt5 Lt6 Kt) as SL2.
  assert (SOK2 : store_ok SEGS m2 (Z_to_bv 64 (s - 112)) 112 = true) by rgb_sok CK HW2.
  assert (PM2' : POSTM C A s M1 m2) by (eapply POSTM_mono; [|exact PM2]; lia).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW2) | apply (pbl_C1 al_rom fr5 cs5 r6 m2 s pt FZ5 ltac:(lia) ltac:(lia) SOK2);
                    first [csr; reflexivity | rgb_fr; reflexivity] |].
  intros fin (fr7 & cs7 & r7 & M7 & -> & FZ7 & RI7 & S88 & Q71 & Q72 & Q710 & Q711 & Q712 & AG7 & F710 & F711 & GK7).
  pose proof (rgb_fs_seg fr _ fr7 [10; 11]%nat ltac:(rgb_inL) FS5 GK7) as FS7.
  destruct (rinv_WP2 C A A2 m2 (with_vmmaps vm2 md) M7 [((s - 88)%Z, 8%Z)] s CK HW2 SL2 Hhi RI7 ltac:(rgb_lc)) as [HW7 PM7].
  assert (PXt7 : PIXat M7 pt (hdv w h 8 0 dt)).
  { apply (PIXat_frame m2); [exact PXt|]. intros x Hx. apply (rgb_rinv_frame m2 M7 (s - 88) 8 x RI7). lia. }
  pose proof (rgb_px_livk A M1 m2 pixs _ PXs1 (proj2 PM2) Lps) as PXs2.
  pose proof (rgb_px_rinv m2 M7 pixs _ (s - 88) 8 PXs2 RI7 ltac:(lia)) as PXs7.
  pose proof (rgb_fk_frm C (s - 112) M1 m2 M1 (s - 76) s CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia) (rgb_fk_refl M1 (s - 76) s)) as FK2.
  pose proof (rgb_fk_rinv m2 M7 M1 (s - 88) 8 (s - 76) s RI7 ltac:(lia) ltac:(lia) ltac:(lia) FK2) as FK7.
  pose proof (POSTM_trans C A s m M1 M7 PM1 (POSTM_trans C A s M1 m2 M7 PM2' PM7)) as PMk7.
  assert (OCt2 : ocomp C A A2 M7 pt dt w h).
  { unfold ocomp. right. do 11 (split; [first [assumption | lia] |]). exact PXt7. }
  enough (KR : forall fr8 cs8 A3 m3 vm3 r8 (rr drr : Z),
     W C A3 m3 (with_vmmaps vm3 (with_vmmaps vm2 md)) -> frm_zero cs8 -> cs_kept r7 r8 -> POSTM C A2 (s - 112)%Z M7 m3 ->
     getr r8 10 = Z_to_bv 64 rr -> ocomp C A A3 m3 rr drr w h -> (forall q, ~ cblk rr drr q -> live A3 q = live A2 q) ->
     (forall q, cblk rr drr q -> ~ cblk pt dt q) ->
     (forall x : reg, In (u x) fs_list -> reg_get fr8 x = reg_get fr7 x) ->
     aroom A3 vm3 (kR - RK_pix - RK_bg)%Z (bR - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h)%Z ->
     realizes SEGS (mkCfg (@mkst (mkFP fr8 cs8) r8 (getr r7 1) m3 al_rom) (with_vmmaps vm3 (with_vmmaps vm2 md))) S).
  { apply (pixBilateralGray_W H_amb H_gev H_bd fr7 cs7 C A2 M7 (with_vmmaps vm2 md) r7 (s - 112) pt w h dt (getr r7 1) S CK HW7 FZ7 Q72
             ltac:(rgb_m16 Hs16) ltac:(unfold BG_WIN, BC_WIN; lia) ltac:(lia) eq_refl ltac:(rewrite Q71; rgb_rok)
             ltac:(csr; reflexivity) Q710 Q711 Q712 F710 F711 PXt7 (hdr_ok_32_8 w h ltac:(lia) ltac:(lia) HOK) Hw22 Hh22 Lt5 Lt6 Lt3
             (kR - RK_pix) (bR - RB_pixT (4 * (wpl_of w 8 * h))) ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia)).
    - intros fr8 cs8 A3 m3 vm3 r8 HW8 FZ8 CS8 PM8 Z8 LV8 FSg8 RM8.
      apply (KR fr8 cs8 A3 m3 vm3 r8 0%Z 0%Z HW8 FZ8 CS8 PM8 Z8 (or_introl (conj eq_refl eq_refl))
               (fun q _ => LV8 q) (fun q CB => False_ind _ (proj1 CB eq_refl)) FSg8 RM8).
    - intros fr8 cs8 A3 m3 vm3 r8 pd dd HW8 FZ8 CS8 PM8 P8 PN8 FSg8 RM8.
      destruct PN8 as (Gd & Td & Ad & Gdd & Tdd & Add & NEd & Ld1 & Ld2 & Ld3 & Ld4 & Ld5 & Ld6 & Kd & PXd & Dd).
      cbn [p_wpl p_h set_data pix_hdr] in Tdd, Ld6.
      apply (KR fr8 cs8 A3 m3 vm3 r8 pd dd HW8 FZ8 CS8 PM8 P8); [ | | | exact FSg8 | exact RM8].
      + unfold ocomp. right.
        do 11 (split; [first [assumption | lia | (eapply pbl_sub_none; [exact SL2 | assumption])] |]). exact PXd.
      + intros q N. apply Kd; intro E; apply N; (split; [lia|]); [left | right]; exact E.
      + intros q CB1 CB2. exact (rgb_disj C A A2 M7 pt dt w h pd dd OCt2 Ld1 Ld2 q CB2 CB1). }
  intros fr8 cs8 A3 m3 vm3 r8 rr drr HW8 FZ8 CS8 PM8 P8 OC8 LV8 DJ8 FSg8 RM8.
  rewrite with_vmmaps_twice in HW8 |- *. rewrite Q71.
  pose proof (rgb_ok_range C A A3 m3 rr drr w h OC8) as RRr.
  assert (SOK8 : store_ok SEGS m3 (Z_to_bv 64 (s - 112)) 112 = true) by rgb_sok CK HW8.
  pose proof (rgb_fs_gray fr fr7 fr8 FS7 FSg8) as FS8.
  assert (PM8' : POSTM C A s M7 m3) by (apply (POSTM_sub C A A2 s M7 m3 SL2); eapply POSTM_mono; [|exact PM8]; lia).
  pose proof (rgb_sub_k A A2 A3 rr drr SL2 (rgb_ok_fr C A A3 m3 rr drr w h OC8) LV8) as SL3.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW8) | apply (pbl_C2 al_rom (mkFP fr8 cs8) r8 m3 s rr ltac:(lia) RRr SOK8);
                    first [exact P8 | csr; reflexivity] |].
  intros fin (r9 & M9 & -> & RI9 & S96 & Q91 & Q92 & Q919 & Q910 & AG9).
  destruct (rinv_WP2 C A A3 m3 (with_vmmaps vm3 md) M9 [((s - 96)%Z, 8%Z)] s CK HW8 SL3 Hhi RI9 ltac:(rgb_lc)) as [HW9 PM9].
  pose proof (rgb_ok_free C A A2 A3 M7 m3 pt dt w h rr drr OCt2 (fun q CB1 CB2 => DJ8 q CB2 CB1) LV8
                (fun x G T _ X => rgb_mem_livk C A2 M7 m3 pt (proj2 PM8) x G T Lt5 X)) as OCt3.
  pose proof (rgb_ok_same C A A3 A3 m3 M9 pt dt w h OCt3 (fun q => eq_refl) (rgb_mem_rinv C A3 m3 M9 pt (s - 96) 8 RI9 ltac:(lia))) as OCt9.
  pose proof (rgb_ok_same C A A3 A3 m3 M9 rr drr w h OC8 (fun q => eq_refl) (rgb_mem_rinv C A3 m3 M9 rr (s - 96) 8 RI9 ltac:(lia))) as OCr9.
  pose proof (rgb_fk_frm C (s - 112) M7 m3 M7 (s - 88) (s - 80) CK (proj1 PM8) ltac:(lia) ltac:(lia) ltac:(lia) (rgb_fk_refl M7 (s - 88) (s - 80))) as FKt3.
  pose proof (rgb_fk_rinv m3 M9 M7 (s - 96) 8 (s - 88) (s - 80) RI9 ltac:(lia) ltac:(lia) ltac:(lia) FKt3) as FKt9.
  pose proof (rgb_fk_use M9 M7 (s - 88) (s - 80) (s - 88) 8 _ FKt9 ltac:(lia) ltac:(lia) S88) as S88'.
  eapply rgb_rz_pc; [apply (pixDestroy_ocomp_W (mkFP fr8 cs8) C A A3 M9 (with_vmmaps vm3 md) r9 (s - 112) (s - 88) pt dt w h (getr r9 1) S
                       CK HW9 Q92 ltac:(rgb_m16 Hs16) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) eq_refl ltac:(rewrite Q91; rgb_rok)
                       ltac:(csr; reflexivity) Q910 ltac:(rgb_m8 Hs16) ltac:(lia) ltac:(lia) S88' OCt9 N8) | apply bv_eq; reflexivity].
  intros A4 m10 vm4 r10 HW10 CS10 F10x K10 SLx10 PD10 RT10.
  rewrite with_vmmaps_twice in HW10 |- *. rewrite Q91.
  pose proof (rgb_ok_free C A A3 A4 M9 m10 rr drr w h pt dt OCr9 DJ8 K10
                (rgb_mem_postd C A4 (s - 112) (s - 88) M9 m10 rr PD10 ltac:(lia))) as OCr10.
  pose proof (rgb_lv A A A2 A3 A4 (fun _ => True) rr drr pt dt (fun q _ => eq_refl) Lt1 Lt2 ltac:(lia) Kt LV8 F10x K10) as LVr.
  pose proof (rgb_sub_k A A3 A4 pt dt SL3 (fun _ => conj Lt1 Lt2) K10) as SL4.
  pose proof (POSTM_sub C A A4 s M9 m10 SL4 (POSTD_POSTM_win C A4 m10 (with_vmmaps vm4 md) (s - 112) s (s - 88) M9 CK HW10
                ltac:(lia) ltac:(lia) ltac:(lia) Hhi PD10)) as PM10.
  pose proof (POSTM_trans C A s m M7 m10 PMk7 (POSTM_trans C A s M7 m3 m10 PM8' (POSTM_trans C A s m3 M9 m10 PM9 PM10))) as PMk10.
  pose proof (rgb_room0 A3 (m_vmmaps (with_vmmaps vm3 md)) A4 vm4 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM8) RT10) as RM10.
  pose proof (rgb_fk_frm C (s - 112) M7 m3 M1 (s - 76) s CK (proj1 PM8) ltac:(lia) ltac:(lia) ltac:(lia) FK7) as FK3.
  pose proof (rgb_fk_rinv m3 M9 M1 (s - 96) 8 (s - 76) s RI9 ltac:(lia) ltac:(lia) ltac:(lia) FK3) as FK9.
  pose proof (rgb_fk_frmx C (s - 112) (s - 88) M9 m10 M1 (s - 76) s CK (proj1 PD10) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FK9) as FK10.
  pose proof (rgb_fk_frmx C (s - 112) (s - 88) M9 m10 M9 (s - 96) (s - 88) CK (proj1 PD10) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                (rgb_fk_refl M9 (s - 96) (s - 88))) as FKr10.
  pose proof (rgb_px_livk A2 M7 m3 pixs _ PXs7 (proj2 PM8) (SL2 _ _ Lps)) as PXs3.
  pose proof (rgb_px_rinv m3 M9 pixs _ (s - 96) 8 PXs3 RI9 ltac:(lia)) as PXs9.
  pose proof (rgb_px_postd C A4 (s - 112) (s - 88) M9 m10 pixs _ PXs9 PD10 (SL4 _ _ Lps) ltac:(lia)) as PXs10.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW10) | apply (pbl_C3 al_rom (mkFP fr8 cs8) r10 m10 s pixs ltac:(lia) ltac:(lia)); csr; reflexivity |].
  intros fin (r11 & M11 & -> & -> & Q111 & Q112 & Q1110 & Q1111 & AG11).
  apply (H_rgb (mkFP fr8 cs8) C A4 m10 (with_vmmaps vm4 md) r11 (s - 112)%Z pixs w h datas 1%Z _ S CK HW10 Q112
           ltac:(rgb_m16 Hs16) ltac:(unfold RGB_STACK; lia) ltac:(lia) Q111 ltac:(rgb_rok) ltac:(csr; reflexivity) Q1110 Q1111 ltac:(lia)
           PXs10 HOK Hw Hh (SL4 _ _ Lps) (SL4 _ _ Lds) (kR - RK_pix - RK_bg)%Z (bR - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h)%Z
           ltac:(rewrite with_vmmaps_vmmaps; exact RM10) ltac:(lia) ltac:(lia)).
  intros A5 m12 vm5 r12 ptg dtg HW12 CS12 PM12 P12 PNg RM12.
  rewrite with_vmmaps_twice in HW12 |- *.
  destruct PNg as (Ggt & Tgt & Agt & Ggdt & Tgdt & Agdt & NEgt & Lg1 & Lg2 & Lg3 & Lg4 & Lg5 & Lg6 & Kg & PXgt & Dgt).
  cbn [p_wpl p_h set_data pix_hdr] in Tgdt, Lg6.
  pose proof (sub_live_trans A A4 A5 SL4 (sub_live_new2 A4 A5 _ _ _ _ Lg1 Lg2 Lg5 Lg6 Kg)) as SL5.
  assert (SOK12 : store_ok SEGS m12 (Z_to_bv 64 (s - 112)) 112 = true) by rgb_sok CK HW12.
  assert (PM12' : POSTM C A s m10 m12) by (apply (POSTM_sub C A A4 s m10 m12 SL4); eapply POSTM_mono; [|exact PM12]; lia).
  pose proof (rgb_ok_fresh C A A4 A5 m10 m12 rr drr w h ptg dtg OCr10 Lg1 Lg2 Kg (rgb_mem_livk C A4 m10 m12 rr (proj2 PM12))) as OCr12.
  pose proof (rgb_disj C A A4 m10 rr drr w h ptg dtg OCr10 Lg1 Lg2) as DJrtg.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW12) | apply (pbl_C4 al_rom fr8 cs8 r12 m12 s ptg FZ8 ltac:(lia) ltac:(lia) SOK12);
                    first [csr; reflexivity | rgb_fr; reflexivity] |].
  intros fin (fr13 & cs13 & r13 & M13 & -> & FZ13 & RI13 & Sg88 & Q131 & Q132 & Q1310 & Q1311 & Q1312 & AG13 & F1310 & F1311 & GK13).
  pose proof (rgb_fs_seg fr _ fr13 [10; 11]%nat ltac:(rgb_inL) FS8 GK13) as FS13.
  destruct (rinv_WP2 C A A5 m12 (with_vmmaps vm5 md) M13 [((s - 88)%Z, 8%Z)] s CK HW12 SL5 Hhi RI13 ltac:(rgb_lc)) as [HW13 PM13].
  pose proof (rgb_px_rinv m12 M13 ptg _ (s - 88) 8 PXgt RI13 ltac:(lia)) as PXgt13.
  pose proof (rgb_ok_same C A A5 A5 m12 M13 rr drr w h OCr12 (fun q => eq_refl) (rgb_mem_rinv C A5 m12 M13 rr (s - 88) 8 RI13 ltac:(lia))) as OCr13.
  pose proof (rgb_px_livk A4 m10 m12 pixs _ PXs10 (proj2 PM12) (SL4 _ _ Lps)) as PXs12.
  pose proof (rgb_px_rinv m12 M13 pixs _ (s - 88) 8 PXs12 RI13 ltac:(lia)) as PXs13.
  pose proof (rgb_fk_frm C (s - 112) m10 m12 M1 (s - 76) s CK (proj1 PM12) ltac:(lia) ltac:(lia) ltac:(lia) FK10) as FK12.
  pose proof (rgb_fk_rinv m12 M13 M1 (s - 88) 8 (s - 76) s RI13 ltac:(lia) ltac:(lia) ltac:(lia) FK12) as FK13.
  pose proof (rgb_fk_frm C (s - 112) m10 m12 M9 (s - 96) (s - 88) CK (proj1 PM12) ltac:(lia) ltac:(lia) ltac:(lia) FKr10) as FKr12.
  pose proof (rgb_fk_rinv m12 M13 M9 (s - 88) 8 (s - 96) (s - 88) RI13 ltac:(lia) ltac:(lia) ltac:(lia) FKr12) as FKr13.
  pose proof (POSTM_trans C A s m m10 M13 PMk10 (POSTM_trans C A s m10 m12 M13 PM12' PM13)) as PMk13.
  assert (OCgt5 : ocomp C A A5 M13 ptg dtg w h).
  { unfold ocomp. right. do 11 (split; [first [assumption | lia | (eapply pbl_sub_none; [exact SL4 | assumption])] |]). exact PXgt13. }
  enough (KRg : forall fr14 cs14 A6 m14 vm6 r14 (gg dgg : Z),
     W C A6 m14 (with_vmmaps vm6 (with_vmmaps vm5 md)) -> frm_zero cs14 -> cs_kept r13 r14 -> POSTM C A5 (s - 112)%Z M13 m14 ->
     getr r14 10 = Z_to_bv 64 gg -> ocomp C A A6 m14 gg dgg w h -> (forall q, ~ cblk gg dgg q -> live A6 q = live A5 q) ->
     (forall q, cblk gg dgg q -> ~ cblk ptg dtg q) -> (forall q, cblk gg dgg q -> ~ cblk rr drr q) -> ocomp C A A6 m14 rr drr w h ->
     (forall x : reg, In (u x) fs_list -> reg_get fr14 x = reg_get fr13 x) ->
     aroom A6 vm6 (kR - RK_pix - RK_bg - RK_pix - RK_bg)%Z
       (bR - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h)%Z ->
     realizes SEGS (mkCfg (@mkst (mkFP fr14 cs14) r14 (getr r13 1) m14 al_rom) (with_vmmaps vm6 (with_vmmaps vm5 md))) S).
  { apply (pixBilateralGray_W H_amb H_gev H_bd fr13 cs13 C A5 M13 (with_vmmaps vm5 md) r13 (s - 112) ptg w h dtg (getr r13 1) S
             CK HW13 FZ13 Q132 ltac:(rgb_m16 Hs16) ltac:(unfold BG_WIN, BC_WIN; lia) ltac:(lia) eq_refl ltac:(rewrite Q131; rgb_rok)
             ltac:(csr; reflexivity) Q1310 Q1311 Q1312 F1310 F1311 PXgt13 (hdr_ok_32_8 w h ltac:(lia) ltac:(lia) HOK) Hw22 Hh22 Lg5 Lg6 Lg3
             (kR - RK_pix - RK_bg - RK_pix) (bR - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h - RB_pixT (4 * (wpl_of w 8 * h)))
             ltac:(rewrite with_vmmaps_vmmaps; exact RM12) ltac:(lia) ltac:(lia)).
    - intros fr14 cs14 A6 m14 vm6 r14 HW14 FZ14 CS14 PM14 Z14 LV14 FSg14 RM14.
      apply (KRg fr14 cs14 A6 m14 vm6 r14 0%Z 0%Z HW14 FZ14 CS14 PM14 Z14 (or_introl (conj eq_refl eq_refl))
               (fun q _ => LV14 q) (fun q CB => False_ind _ (proj1 CB eq_refl)) (fun q CB => False_ind _ (proj1 CB eq_refl))
               (rgb_ok_same C A A5 A6 M13 m14 rr drr w h OCr13 LV14 (rgb_mem_livk C A5 M13 m14 rr (proj2 PM14))) FSg14 RM14).
    - intros fr14 cs14 A6 m14 vm6 r14 pd dd HW14 FZ14 CS14 PM14 P14 PN14 FSg14 RM14.
      destruct PN14 as (Gd & Td & Ad & Gdd & Tdd & Add & NEd & Ld1 & Ld2 & Ld3 & Ld4 & Ld5 & Ld6 & Kd & PXd & Dd).
      cbn [p_wpl p_h set_data pix_hdr] in Tdd, Ld6.
      apply (KRg fr14 cs14 A6 m14 vm6 r14 pd dd HW14 FZ14 CS14 PM14 P14); [ | | | | | exact FSg14 | exact RM14].
      + unfold ocomp. right.
        do 11 (split; [first [assumption | lia | (eapply pbl_sub_none; [exact SL5 | assumption])] |]). exact PXd.
      + intros q N. apply Kd; intro E; apply N; (split; [lia|]); [left | right]; exact E.
      + intros q CB1 CB2. exact (rgb_disj C A A5 M13 ptg dtg w h pd dd OCgt5 Ld1 Ld2 q CB2 CB1).
      + intros q CB1 CB2. exact (rgb_disj C A A5 M13 rr drr w h pd dd OCr13 Ld1 Ld2 q CB2 CB1).
      + exact (rgb_ok_fresh C A A5 A6 M13 m14 rr drr w h pd dd OCr13 Ld1 Ld2 Kd (rgb_mem_livk C A5 M13 m14 rr (proj2 PM14))). }
  intros fr14 cs14 A6 m14 vm6 r14 gg dgg HW14 FZ14 CS14 PM14 P14 OC14 LV14 DJ14t DJ14r OCr14 FSg14 RM14.
  rewrite with_vmmaps_twice in HW14 |- *. rewrite Q131.
  pose proof (rgb_ok_range C A A6 m14 gg dgg w h OC14) as RRg.
  assert (SOK14 : store_ok SEGS m14 (Z_to_bv 64 (s - 112)) 112 = true) by rgb_sok CK HW14.
  pose proof (rgb_fs_gray fr fr13 fr14 FS13 FSg14) as FS14.
  assert (PM14' : POSTM C A s M13 m14) by (apply (POSTM_sub C A A5 s M13 m14 SL5); eapply POSTM_mono; [|exact PM14]; lia).
  pose proof (rgb_sub_k A A5 A6 gg dgg SL5 (rgb_ok_fr C A A6 m14 gg dgg w h OC14) LV14) as SL6.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW14) | apply (pbl_C5 al_rom (mkFP fr14 cs14) r14 m14 s gg ltac:(lia) RRg SOK14);
                    first [exact P14 | csr; reflexivity] |].
  intros fin (r15 & M15 & -> & RI15 & S104 & Q151 & Q152 & Q1520 & Q1510 & AG15).
  destruct (rinv_WP2 C A A6 m14 (with_vmmaps vm6 md) M15 [((s - 104)%Z, 8%Z)] s CK HW14 SL6 Hhi RI15 ltac:(rgb_lc)) as [HW15 PM15].
  pose proof (rgb_ok_free C A A5 A6 M13 m14 ptg dtg w h gg dgg OCgt5 (fun q CB1 CB2 => DJ14t q CB2 CB1) LV14
                (fun x G T _ X => rgb_mem_livk C A5 M13 m14 ptg (proj2 PM14) x G T Lg5 X)) as OCgt14.
  pose proof (rgb_ok_same C A A6 A6 m14 M15 ptg dtg w h OCgt14 (fun q => eq_refl) (rgb_mem_rinv C A6 m14 M15 ptg (s - 104) 8 RI15 ltac:(lia))) as OCgt15.
  pose proof (rgb_ok_same C A A6 A6 m14 M15 gg dgg w h OC14 (fun q => eq_refl) (rgb_mem_rinv C A6 m14 M15 gg (s - 104) 8 RI15 ltac:(lia))) as OCg15.
  pose proof (rgb_ok_same C A A6 A6 m14 M15 rr drr w h OCr14 (fun q => eq_refl) (rgb_mem_rinv C A6 m14 M15 rr (s - 104) 8 RI15 ltac:(lia))) as OCr15.
  pose proof (rgb_fk_frm C (s - 112) M13 m14 M13 (s - 88) (s - 80) CK (proj1 PM14) ltac:(lia) ltac:(lia) ltac:(lia) (rgb_fk_refl M13 (s - 88) (s - 80))) as FKt14.
  pose proof (rgb_fk_rinv m14 M15 M13 (s - 104) 8 (s - 88) (s - 80) RI15 ltac:(lia) ltac:(lia) ltac:(lia) FKt14) as FKt15.
  pose proof (rgb_fk_use M15 M13 (s - 88) (s - 80) (s - 88) 8 _ FKt15 ltac:(lia) ltac:(lia) Sg88) as Sg88'.
  eapply rgb_rz_pc; [apply (pixDestroy_ocomp_W (mkFP fr14 cs14) C A A6 M15 (with_vmmaps vm6 md) r15 (s - 112) (s - 88) ptg dtg w h (getr r15 1) S
                       CK HW15 Q152 ltac:(rgb_m16 Hs16) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) eq_refl ltac:(rewrite Q151; rgb_rok)
                       ltac:(csr; reflexivity) Q1510 ltac:(rgb_m8 Hs16) ltac:(lia) ltac:(lia) Sg88' OCgt15 N8) | apply bv_eq; reflexivity].
  intros A7 m16 vm7 r16 HW16 CS16 F16x K16 SL16 PD16 RT16.
  rewrite with_vmmaps_twice in HW16 |- *. rewrite Q151.
  pose proof (rgb_ok_free C A A6 A7 M15 m16 gg dgg w h ptg dtg OCg15 DJ14t K16
                (rgb_mem_postd C A7 (s - 112) (s - 88) M15 m16 gg PD16 ltac:(lia))) as OCg16.
  pose proof (rgb_ok_free C A A6 A7 M15 m16 rr drr w h ptg dtg OCr15 DJrtg K16
                (rgb_mem_postd C A7 (s - 112) (s - 88) M15 m16 rr PD16 ltac:(lia))) as OCr16.
  pose proof (rgb_lv A A4 A5 A6 A7 (fun q => ~ cblk rr drr q) gg dgg ptg dtg (fun q N => LVr q I N)
                (pbl_sub_none A A4 _ SL4 Lg1) (pbl_sub_none A A4 _ SL4 Lg2) ltac:(lia) Kg LV14 F16x K16) as LVg.
  pose proof (rgb_sub_k A A6 A7 ptg dtg SL6 (fun _ => conj (pbl_sub_none A A4 _ SL4 Lg1) (pbl_sub_none A A4 _ SL4 Lg2)) K16) as SL7.
  pose proof (POSTM_sub C A A7 s M15 m16 SL7 (POSTD_POSTM_win C A7 m16 (with_vmmaps vm7 md) (s - 112) s (s - 88) M15 CK HW16
                ltac:(lia) ltac:(lia) ltac:(lia) Hhi PD16)) as PM16.
  pose proof (POSTM_trans C A s m M13 m16 PMk13 (POSTM_trans C A s M13 m14 m16 PM14' (POSTM_trans C A s m14 M15 m16 PM15 PM16))) as PMk16.
  pose proof (rgb_room0 A6 (m_vmmaps (with_vmmaps vm6 md)) A7 vm7 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM14) RT16) as RM16.
  pose proof (rgb_fk_frm C (s - 112) M13 m14 M1 (s - 76) s CK (proj1 PM14) ltac:(lia) ltac:(lia) ltac:(lia) FK13) as FK14.
  pose proof (rgb_fk_rinv m14 M15 M1 (s - 104) 8 (s - 76) s RI15 ltac:(lia) ltac:(lia) ltac:(lia) FK14) as FK15.
  pose proof (rgb_fk_frmx C (s - 112) (s - 88) M15 m16 M1 (s - 76) s CK (proj1 PD16) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FK15) as FK16.
  pose proof (rgb_fk_frm C (s - 112) M13 m14 M9 (s - 96) (s - 88) CK (proj1 PM14) ltac:(lia) ltac:(lia) ltac:(lia) FKr13) as FKr14.
  pose proof (rgb_fk_rinv m14 M15 M9 (s - 104) 8 (s - 96) (s - 88) RI15 ltac:(lia) ltac:(lia) ltac:(lia) FKr14) as FKr15.
  pose proof (rgb_fk_frmx C (s - 112) (s - 88) M15 m16 M9 (s - 96) (s - 88) CK (proj1 PD16) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FKr15) as FKr16.
  pose proof (rgb_fk_frmx C (s - 112) (s - 88) M15 m16 M15 (s - 104) (s - 96) CK (proj1 PD16) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                (rgb_fk_refl M15 (s - 104) (s - 96))) as FKg16.
  pose proof (rgb_px_livk A5 M13 m14 pixs _ PXs13 (proj2 PM14) (SL5 _ _ Lps)) as PXs14.
  pose proof (rgb_px_rinv m14 M15 pixs _ (s - 104) 8 PXs14 RI15 ltac:(lia)) as PXs15.
  pose proof (rgb_px_postd C A7 (s - 112) (s - 88) M15 m16 pixs _ PXs15 PD16 (SL7 _ _ Lps) ltac:(lia)) as PXs16.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW16) | apply (pbl_C6 al_rom (mkFP fr14 cs14) r16 m16 s pixs ltac:(lia) ltac:(lia)); csr; reflexivity |].
  intros fin (r17 & M17 & -> & -> & Q171 & Q172 & Q1710 & Q1711 & AG17).
  apply (H_rgb (mkFP fr14 cs14) C A7 m16 (with_vmmaps vm7 md) r17 (s - 112)%Z pixs w h datas 2%Z _ S CK HW16 Q172
           ltac:(rgb_m16 Hs16) ltac:(unfold RGB_STACK; lia) ltac:(lia) Q171 ltac:(rgb_rok) ltac:(csr; reflexivity) Q1710 Q1711 ltac:(lia)
           PXs16 HOK Hw Hh (SL7 _ _ Lps) (SL7 _ _ Lds) (kR - RK_pix - RK_bg - RK_pix - RK_bg)%Z
           (bR - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h)%Z
           ltac:(rewrite with_vmmaps_vmmaps; exact RM16) ltac:(lia) ltac:(lia)).
  intros A8 m18 vm8 r18 ptb dtb HW18 CS18 PM18 P18 PNb RM18.
  rewrite with_vmmaps_twice in HW18 |- *.
  destruct PNb as (Gbt & Tbt & Abt & Gbdt & Tbdt & Abdt & NEbt & Lb1 & Lb2 & Lb3 & Lb4 & Lb5 & Lb6 & Kb & PXbt & Dbt).
  cbn [p_wpl p_h set_data pix_hdr] in Tbdt, Lb6.
  pose proof (sub_live_trans A A7 A8 SL7 (sub_live_new2 A7 A8 _ _ _ _ Lb1 Lb2 Lb5 Lb6 Kb)) as SL8.
  assert (SOK18 : store_ok SEGS m18 (Z_to_bv 64 (s - 112)) 112 = true) by rgb_sok CK HW18.
  assert (PM18' : POSTM C A s m16 m18) by (apply (POSTM_sub C A A7 s m16 m18 SL7); eapply POSTM_mono; [|exact PM18]; lia).
  pose proof (rgb_ok_fresh C A A7 A8 m16 m18 rr drr w h ptb dtb OCr16 Lb1 Lb2 Kb (rgb_mem_livk C A7 m16 m18 rr (proj2 PM18))) as OCr18.
  pose proof (rgb_ok_fresh C A A7 A8 m16 m18 gg dgg w h ptb dtb OCg16 Lb1 Lb2 Kb (rgb_mem_livk C A7 m16 m18 gg (proj2 PM18))) as OCg18.
  pose proof (rgb_disj C A A7 m16 rr drr w h ptb dtb OCr16 Lb1 Lb2) as DJrtb.
  pose proof (rgb_disj C A A7 m16 gg dgg w h ptb dtb OCg16 Lb1 Lb2) as DJgtb.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW18) | apply (pbl_C7 al_rom fr14 cs14 r18 m18 s ptb FZ14 ltac:(lia) ltac:(lia) SOK18);
                    first [csr; reflexivity | rgb_fr; reflexivity] |].
  intros fin (fr19 & cs19 & r19 & M19 & -> & FZ19 & RI19 & Sb88 & Q191 & Q192 & Q1910 & Q1911 & Q1912 & AG19 & F1910 & F1911 & GK19).
  pose proof (rgb_fs_seg fr _ fr19 [10; 11]%nat ltac:(rgb_inL) FS14 GK19) as FS19.
  destruct (rinv_WP2 C A A8 m18 (with_vmmaps vm8 md) M19 [((s - 88)%Z, 8%Z)] s CK HW18 SL8 Hhi RI19 ltac:(rgb_lc)) as [HW19 PM19].
  pose proof (rgb_px_rinv m18 M19 ptb _ (s - 88) 8 PXbt RI19 ltac:(lia)) as PXbt19.
  pose proof (rgb_ok_same C A A8 A8 m18 M19 rr drr w h OCr18 (fun q => eq_refl) (rgb_mem_rinv C A8 m18 M19 rr (s - 88) 8 RI19 ltac:(lia))) as OCr19.
  pose proof (rgb_ok_same C A A8 A8 m18 M19 gg dgg w h OCg18 (fun q => eq_refl) (rgb_mem_rinv C A8 m18 M19 gg (s - 88) 8 RI19 ltac:(lia))) as OCg19.
  pose proof (rgb_fk_frm C (s - 112) m16 m18 M1 (s - 76) s CK (proj1 PM18) ltac:(lia) ltac:(lia) ltac:(lia) FK16) as FK18.
  pose proof (rgb_fk_rinv m18 M19 M1 (s - 88) 8 (s - 76) s RI19 ltac:(lia) ltac:(lia) ltac:(lia) FK18) as FK19.
  pose proof (rgb_fk_frm C (s - 112) m16 m18 M9 (s - 96) (s - 88) CK (proj1 PM18) ltac:(lia) ltac:(lia) ltac:(lia) FKr16) as FKr18.
  pose proof (rgb_fk_rinv m18 M19 M9 (s - 88) 8 (s - 96) (s - 88) RI19 ltac:(lia) ltac:(lia) ltac:(lia) FKr18) as FKr19.
  pose proof (rgb_fk_frm C (s - 112) m16 m18 M15 (s - 104) (s - 96) CK (proj1 PM18) ltac:(lia) ltac:(lia) ltac:(lia) FKg16) as FKg18.
  pose proof (rgb_fk_rinv m18 M19 M15 (s - 88) 8 (s - 104) (s - 96) RI19 ltac:(lia) ltac:(lia) ltac:(lia) FKg18) as FKg19.
  pose proof (POSTM_trans C A s m m16 M19 PMk16 (POSTM_trans C A s m16 m18 M19 PM18' PM19)) as PMk19.
  assert (OCbt8 : ocomp C A A8 M19 ptb dtb w h).
  { unfold ocomp. right. do 11 (split; [first [assumption | lia | (eapply pbl_sub_none; [exact SL7 | assumption])] |]). exact PXbt19. }
  enough (KRb : forall fr20 cs20 A9 m20 vm9 r20 (bb dbb : Z),
     W C A9 m20 (with_vmmaps vm9 (with_vmmaps vm8 md)) -> frm_zero cs20 -> cs_kept r19 r20 -> POSTM C A8 (s - 112)%Z M19 m20 ->
     getr r20 10 = Z_to_bv 64 bb -> ocomp C A A9 m20 bb dbb w h -> (forall q, ~ cblk bb dbb q -> live A9 q = live A8 q) ->
     (forall q, cblk bb dbb q -> ~ cblk ptb dtb q) -> (forall q, cblk bb dbb q -> ~ cblk rr drr q) -> (forall q, cblk bb dbb q -> ~ cblk gg dgg q) ->
     ocomp C A A9 m20 rr drr w h -> ocomp C A A9 m20 gg dgg w h ->
     (forall x : reg, In (u x) fs_list -> reg_get fr20 x = reg_get fr19 x) ->
     aroom A9 vm9 (kR - RK_pix - RK_bg - RK_pix - RK_bg - RK_pix - RK_bg)%Z
       (bR - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h
           - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h)%Z ->
     realizes SEGS (mkCfg (@mkst (mkFP fr20 cs20) r20 (getr r19 1) m20 al_rom) (with_vmmaps vm9 (with_vmmaps vm8 md))) S).
  { apply (pixBilateralGray_W H_amb H_gev H_bd fr19 cs19 C A8 M19 (with_vmmaps vm8 md) r19 (s - 112) ptb w h dtb (getr r19 1) S
             CK HW19 FZ19 Q192 ltac:(rgb_m16 Hs16) ltac:(unfold BG_WIN, BC_WIN; lia) ltac:(lia) eq_refl ltac:(rewrite Q191; rgb_rok)
             ltac:(csr; reflexivity) Q1910 Q1911 Q1912 F1910 F1911 PXbt19 (hdr_ok_32_8 w h ltac:(lia) ltac:(lia) HOK) Hw22 Hh22 Lb5 Lb6 Lb3
             (kR - RK_pix - RK_bg - RK_pix - RK_bg - RK_pix)
             (bR - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h - RB_pixT (4 * (wpl_of w 8 * h)))
             ltac:(rewrite with_vmmaps_vmmaps; exact RM18) ltac:(lia) ltac:(lia)).
    - intros fr20 cs20 A9 m20 vm9 r20 HW20 FZ20 CS20 PM20 Z20 LV20 FSg20 RM20.
      apply (KRb fr20 cs20 A9 m20 vm9 r20 0%Z 0%Z HW20 FZ20 CS20 PM20 Z20 (or_introl (conj eq_refl eq_refl))
               (fun q _ => LV20 q) (fun q CB => False_ind _ (proj1 CB eq_refl)) (fun q CB => False_ind _ (proj1 CB eq_refl))
               (fun q CB => False_ind _ (proj1 CB eq_refl))
               (rgb_ok_same C A A8 A9 M19 m20 rr drr w h OCr19 LV20 (rgb_mem_livk C A8 M19 m20 rr (proj2 PM20)))
               (rgb_ok_same C A A8 A9 M19 m20 gg dgg w h OCg19 LV20 (rgb_mem_livk C A8 M19 m20 gg (proj2 PM20))) FSg20 RM20).
    - intros fr20 cs20 A9 m20 vm9 r20 pd dd HW20 FZ20 CS20 PM20 P20 PN20 FSg20 RM20.
      destruct PN20 as (Gd & Td & Ad & Gdd & Tdd & Add & NEd & Ld1 & Ld2 & Ld3 & Ld4 & Ld5 & Ld6 & Kd & PXd & Dd).
      cbn [p_wpl p_h set_data pix_hdr] in Tdd, Ld6.
      apply (KRb fr20 cs20 A9 m20 vm9 r20 pd dd HW20 FZ20 CS20 PM20 P20); [ | | | | | | | exact FSg20 | exact RM20].
      + unfold ocomp. right.
        do 11 (split; [first [assumption | lia | (eapply pbl_sub_none; [exact SL8 | assumption])] |]). exact PXd.
      + intros q N. apply Kd; intro E; apply N; (split; [lia|]); [left | right]; exact E.
      + intros q CB1 CB2. exact (rgb_disj C A A8 M19 ptb dtb w h pd dd OCbt8 Ld1 Ld2 q CB2 CB1).
      + intros q CB1 CB2. exact (rgb_disj C A A8 M19 rr drr w h pd dd OCr19 Ld1 Ld2 q CB2 CB1).
      + intros q CB1 CB2. exact (rgb_disj C A A8 M19 gg dgg w h pd dd OCg19 Ld1 Ld2 q CB2 CB1).
      + exact (rgb_ok_fresh C A A8 A9 M19 m20 rr drr w h pd dd OCr19 Ld1 Ld2 Kd (rgb_mem_livk C A8 M19 m20 rr (proj2 PM20))).
      + exact (rgb_ok_fresh C A A8 A9 M19 m20 gg dgg w h pd dd OCg19 Ld1 Ld2 Kd (rgb_mem_livk C A8 M19 m20 gg (proj2 PM20))). }
  intros fr20 cs20 A9 m20 vm9 r20 bb dbb HW20 FZ20 CS20 PM20 P20 OC20 LV20 DJ20t DJ20r DJ20g OCr20 OCg20 FSg20 RM20.
  rewrite with_vmmaps_twice in HW20 |- *. rewrite Q191.
  pose proof (rgb_ok_range C A A9 m20 bb dbb w h OC20) as RRb.
  assert (SOK20 : store_ok SEGS m20 (Z_to_bv 64 (s - 112)) 112 = true) by rgb_sok CK HW20.
  pose proof (rgb_fs_gray fr fr19 fr20 FS19 FSg20) as FS20.
  assert (PM20' : POSTM C A s M19 m20) by (apply (POSTM_sub C A A8 s M19 m20 SL8); eapply POSTM_mono; [|exact PM20]; lia).
  pose proof (rgb_sub_k A A8 A9 bb dbb SL8 (rgb_ok_fr C A A9 m20 bb dbb w h OC20) LV20) as SL9.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW20) | apply (pbl_C8 al_rom (mkFP fr20 cs20) r20 m20 s bb ltac:(lia) RRb SOK20);
                    first [exact P20 | csr; reflexivity] |].
  intros fin (r21 & M21 & -> & RI21 & S112 & Q211 & Q212 & Q218 & Q2110 & AG21).
  destruct (rinv_WP2 C A A9 m20 (with_vmmaps vm9 md) M21 [((s - 112)%Z, 8%Z)] s CK HW20 SL9 Hhi RI21 ltac:(rgb_lc)) as [HW21 PM21].
  pose proof (rgb_ok_free C A A8 A9 M19 m20 ptb dtb w h bb dbb OCbt8 (fun q CB1 CB2 => DJ20t q CB2 CB1) LV20
                (fun x G T _ X => rgb_mem_livk C A8 M19 m20 ptb (proj2 PM20) x G T Lb5 X)) as OCbt20.
  pose proof (rgb_ok_same C A A9 A9 m20 M21 ptb dtb w h OCbt20 (fun q => eq_refl) (rgb_mem_rinv C A9 m20 M21 ptb (s - 112) 8 RI21 ltac:(lia))) as OCbt21.
  pose proof (rgb_ok_same C A A9 A9 m20 M21 bb dbb w h OC20 (fun q => eq_refl) (rgb_mem_rinv C A9 m20 M21 bb (s - 112) 8 RI21 ltac:(lia))) as OCb21.
  pose proof (rgb_ok_same C A A9 A9 m20 M21 rr drr w h OCr20 (fun q => eq_refl) (rgb_mem_rinv C A9 m20 M21 rr (s - 112) 8 RI21 ltac:(lia))) as OCr21.
  pose proof (rgb_ok_same C A A9 A9 m20 M21 gg dgg w h OCg20 (fun q => eq_refl) (rgb_mem_rinv C A9 m20 M21 gg (s - 112) 8 RI21 ltac:(lia))) as OCg21.
  pose proof (rgb_fk_frm C (s - 112) M19 m20 M19 (s - 88) (s - 80) CK (proj1 PM20) ltac:(lia) ltac:(lia) ltac:(lia) (rgb_fk_refl M19 (s - 88) (s - 80))) as FKt20.
  pose proof (rgb_fk_rinv m20 M21 M19 (s - 112) 8 (s - 88) (s - 80) RI21 ltac:(lia) ltac:(lia) ltac:(lia) FKt20) as FKt21.
  pose proof (rgb_fk_use M21 M19 (s - 88) (s - 80) (s - 88) 8 _ FKt21 ltac:(lia) ltac:(lia) Sb88) as Sb88'.
  eapply rgb_rz_pc; [apply (pixDestroy_ocomp_W (mkFP fr20 cs20) C A A9 M21 (with_vmmaps vm9 md) r21 (s - 112) (s - 88) ptb dtb w h (getr r21 1) S
                       CK HW21 Q212 ltac:(rgb_m16 Hs16) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) eq_refl ltac:(rewrite Q211; rgb_rok)
                       ltac:(csr; reflexivity) Q2110 ltac:(rgb_m8 Hs16) ltac:(lia) ltac:(lia) Sb88' OCbt21 N8) | apply bv_eq; reflexivity].
  intros A10 m22 vm10 r22 HW22 CS22 F22x K22 SL22 PD22 RT22.
  rewrite with_vmmaps_twice in HW22 |- *. rewrite Q211.
  pose proof (rgb_ok_free C A A9 A10 M21 m22 bb dbb w h ptb dtb OCb21 DJ20t K22
                (rgb_mem_postd C A10 (s - 112) (s - 88) M21 m22 bb PD22 ltac:(lia))) as OCb22.
  pose proof (rgb_ok_free C A A9 A10 M21 m22 gg dgg w h ptb dtb OCg21 DJgtb K22
                (rgb_mem_postd C A10 (s - 112) (s - 88) M21 m22 gg PD22 ltac:(lia))) as OCg22.
  pose proof (rgb_ok_free C A A9 A10 M21 m22 rr drr w h ptb dtb OCr21 DJrtb K22
                (rgb_mem_postd C A10 (s - 112) (s - 88) M21 m22 rr PD22 ltac:(lia))) as OCr22.
  pose proof (rgb_lv A A7 A8 A9 A10 (fun q => ~ cblk rr drr q /\ ~ cblk gg dgg q) bb dbb ptb dtb (fun q H => LVg q (proj1 H) (proj2 H))
                (pbl_sub_none A A7 _ SL7 Lb1) (pbl_sub_none A A7 _ SL7 Lb2) ltac:(lia) Kb LV20 F22x K22) as LVb.
  pose proof (rgb_sub_k A A9 A10 ptb dtb SL9 (fun _ => conj (pbl_sub_none A A7 _ SL7 Lb1) (pbl_sub_none A A7 _ SL7 Lb2)) K22) as SL10.
  pose proof (POSTM_sub C A A10 s M21 m22 SL10 (POSTD_POSTM_win C A10 m22 (with_vmmaps vm10 md) (s - 112) s (s - 88) M21 CK HW22
                ltac:(lia) ltac:(lia) ltac:(lia) Hhi PD22)) as PM22.
  pose proof (POSTM_trans C A s m M19 m22 PMk19 (POSTM_trans C A s M19 m20 m22 PM20' (POSTM_trans C A s m20 M21 m22 PM21 PM22))) as PMk22.
  pose proof (rgb_room0 A9 (m_vmmaps (with_vmmaps vm9 md)) A10 vm10 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM20) RT22) as RM22.
  pose proof (rgb_fk_frm C (s - 112) M19 m20 M1 (s - 76) s CK (proj1 PM20) ltac:(lia) ltac:(lia) ltac:(lia) FK19) as FK20.
  pose proof (rgb_fk_rinv m20 M21 M1 (s - 112) 8 (s - 76) s RI21 ltac:(lia) ltac:(lia) ltac:(lia) FK20) as FK21.
  pose proof (rgb_fk_frmx C (s - 112) (s - 88) M21 m22 M1 (s - 76) s CK (proj1 PD22) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FK21) as FK22.
  pose proof (rgb_fk_frm C (s - 112) M19 m20 M9 (s - 96) (s - 88) CK (proj1 PM20) ltac:(lia) ltac:(lia) ltac:(lia) FKr19) as FKr20.
  pose proof (rgb_fk_rinv m20 M21 M9 (s - 112) 8 (s - 96) (s - 88) RI21 ltac:(lia) ltac:(lia) ltac:(lia) FKr20) as FKr21.
  pose proof (rgb_fk_frmx C (s - 112) (s - 88) M21 m22 M9 (s - 96) (s - 88) CK (proj1 PD22) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FKr21) as FKr22.
  pose proof (rgb_fk_frm C (s - 112) M19 m20 M15 (s - 104) (s - 96) CK (proj1 PM20) ltac:(lia) ltac:(lia) ltac:(lia) FKg19) as FKg20.
  pose proof (rgb_fk_rinv m20 M21 M15 (s - 112) 8 (s - 104) (s - 96) RI21 ltac:(lia) ltac:(lia) ltac:(lia) FKg20) as FKg21.
  pose proof (rgb_fk_frmx C (s - 112) (s - 88) M21 m22 M15 (s - 104) (s - 96) CK (proj1 PD22) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FKg21) as FKg22.
  pose proof (rgb_fk_frmx C (s - 112) (s - 88) M21 m22 M21 (s - 112) (s - 104) CK (proj1 PD22) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                (rgb_fk_refl M21 (s - 112) (s - 104))) as FKb22.
  pose proof (rgb_ok_range C A A10 m22 rr drr w h OCr22) as RRr'.
  pose proof (rgb_ok_range C A A10 m22 gg dgg w h OCg22) as RRg'.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW22) | apply (pbl_C9 al_rom (mkFP fr20 cs20) r22 m22 s rr gg bb ltac:(lia) RRr' RRg' RRb);
                    csr; reflexivity |].
  intros fin (r23 & M23 & -> & -> & Q231 & Q232 & Q2310 & Q2311 & Q2312 & AG23).
  apply (H_cri (mkFP fr20 cs20) C A10 m22 (with_vmmaps vm10 md) r23 (s - 112)%Z rr gg bb w h _ S CK HW22 Q232
           ltac:(rgb_m16 Hs16) ltac:(unfold CRI_STACK; lia) ltac:(lia) Q231 ltac:(rgb_rok) ltac:(csr; reflexivity) Q2310 Q2311 Q2312
           (ocomp_rgb C A A10 m22 rr drr w h OCr22) (ocomp_rgb C A A10 m22 gg dgg w h OCg22) (ocomp_rgb C A A10 m22 bb dbb w h OCb22)
           HOK Hw Hh (kR - RK_pix - RK_bg - RK_pix - RK_bg - RK_pix - RK_bg)%Z
           (bR - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h
               - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bg w h)%Z
           ltac:(rewrite with_vmmaps_vmmaps; exact RM22) ltac:(lia) ltac:(lia)).
  intros A11 m24 vm11 r24 HW24 CS24 PM24 OUT24 RM24.
  rewrite with_vmmaps_twice in HW24 |- *.
  assert (OUTp : exists pd, getr r24 10 = Z_to_bv 64 pd /\
            ((pd = 0%Z /\ forall q, live A11 q = live A10 q) \/
             (exists dd, pixr_new C A10 A11 m24 pd dd (set_data (pix_hdr w h 32) dd)))).
  { destruct OUT24 as [[Z0 LV0] | (pd & dd & P0 & PN0)].
    - exists 0%Z. split; [exact Z0 | left; split; [reflexivity | exact LV0]].
    - exists pd. split; [exact P0 | right; exists dd; exact PN0]. }
  clear OUT24. destruct OUTp as (pd & P24 & OUTd).
  assert (PDR : (0 <= pd < 2 ^ 64)%Z).
  { destruct OUTd as [[-> _] | (dd & PN0)]; [lia | destruct PN0 as (Gp & Tp & _); lia]. }
  assert (SL11 : sub_live A A11).
  { destruct OUTd as [[_ LV0] | (dd & PN0)].
    - intros q k LQ. rewrite LV0. exact (SL10 q k LQ).
    - destruct PN0 as (_ & _ & _ & _ & _ & _ & _ & L1 & L2 & _ & _ & L5 & L6 & Kp & _).
      exact (sub_live_trans A A10 A11 SL10 (sub_live_new2 A10 A11 _ _ _ _ L1 L2 L5 L6 Kp)). }
  assert (OK24 : forall c dc, ocomp C A A10 m22 c dc w h -> ocomp C A A11 m24 c dc w h).
  { intros c dc OC. destruct OUTd as [[_ LV0] | (dd & PN0)].
    - exact (rgb_ok_same C A A10 A11 m22 m24 c dc w h OC LV0 (rgb_mem_livk C A10 m22 m24 c (proj2 PM24))).
    - destruct PN0 as (_ & _ & _ & _ & _ & _ & _ & L1 & L2 & _ & _ & _ & _ & Kp & _).
      exact (rgb_ok_fresh C A A10 A11 m22 m24 c dc w h pd dd OC L1 L2 Kp (rgb_mem_livk C A10 m22 m24 c (proj2 PM24))). }
  pose proof (OK24 rr drr OCr22) as OCr24. pose proof (OK24 gg dgg OCg22) as OCg24. pose proof (OK24 bb dbb OCb22) as OCb24.
  assert (PM24' : POSTM C A s m22 m24) by (apply (POSTM_sub C A A10 s m22 m24 SL10); eapply POSTM_mono; [|exact PM24]; lia).
  pose proof (POSTM_trans C A s m m22 m24 PMk22 PM24') as PMk24.
  pose proof (rgb_fk_frm C (s - 112) m22 m24 M1 (s - 76) s CK (proj1 PM24) ltac:(lia) ltac:(lia) ltac:(lia) FK22) as FK24.
  pose proof (rgb_fk_frm C (s - 112) m22 m24 M9 (s - 96) (s - 88) CK (proj1 PM24) ltac:(lia) ltac:(lia) ltac:(lia) FKr22) as FKr24.
  pose proof (rgb_fk_frm C (s - 112) m22 m24 M15 (s - 104) (s - 96) CK (proj1 PM24) ltac:(lia) ltac:(lia) ltac:(lia) FKg22) as FKg24.
  pose proof (rgb_fk_frm C (s - 112) m22 m24 M21 (s - 112) (s - 104) CK (proj1 PM24) ltac:(lia) ltac:(lia) ltac:(lia) FKb22) as FKb24.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW24) | apply (pbl_C10 al_rom (mkFP fr20 cs20) r24 m24 s pd ltac:(lia) PDR);
                    first [exact P24 | csr; reflexivity] |].
  intros fin (r25 & M25 & -> & -> & Q251 & Q252 & Q258 & Q2510 & AG25).
  pose proof (rgb_fk_use m24 M9 (s - 96) (s - 88) (s - 96) 8 _ FKr24 ltac:(lia) ltac:(lia) S96) as Sr.
  eapply rgb_rz_pc; [apply (pixDestroy_ocomp_W (mkFP fr20 cs20) C A A11 m24 (with_vmmaps vm11 md) r25 (s - 112) (s - 96) rr drr w h (getr r25 1) S
                       CK HW24 Q252 ltac:(rgb_m16 Hs16) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) eq_refl ltac:(rewrite Q251; rgb_rok)
                       ltac:(csr; reflexivity) Q2510 ltac:(rgb_m8 Hs16) ltac:(lia) ltac:(lia) Sr OCr24 N8) | apply bv_eq; reflexivity].
  intros A12 m26 vm12 r26 HW26 CS26 F26x K26 SL26 PD26 RT26.
  rewrite with_vmmaps_twice in HW26 |- *. rewrite Q251.
  pose proof (rgb_ok_free C A A11 A12 m24 m26 gg dgg w h rr drr OCg24 DJ14r K26
                (rgb_mem_postd C A12 (s - 112) (s - 96) m24 m26 gg PD26 ltac:(lia))) as OCg26.
  pose proof (rgb_ok_free C A A11 A12 m24 m26 bb dbb w h rr drr OCb24 DJ20r K26
                (rgb_mem_postd C A12 (s - 112) (s - 96) m24 m26 bb PD26 ltac:(lia))) as OCb26.
  pose proof (rgb_sub_k A A11 A12 rr drr SL11 (rgb_ok_fr C A A11 m24 rr drr w h OCr24) K26) as SL12.
  pose proof (POSTM_sub C A A12 s m24 m26 SL12 (POSTD_POSTM_win C A12 m26 (with_vmmaps vm12 md) (s - 112) s (s - 96) m24 CK HW26
                ltac:(lia) ltac:(lia) ltac:(lia) Hhi PD26)) as PM26.
  pose proof (rgb_fk_frmx C (s - 112) (s - 96) m24 m26 M1 (s - 76) s CK (proj1 PD26) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FK24) as FK26.
  pose proof (rgb_fk_frmx C (s - 112) (s - 96) m24 m26 M15 (s - 104) (s - 96) CK (proj1 PD26) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FKg24) as FKg26.
  pose proof (rgb_fk_frmx C (s - 112) (s - 96) m24 m26 M21 (s - 112) (s - 104) CK (proj1 PD26) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FKb24) as FKb26.
  pose proof (rgb_room0 A11 (m_vmmaps (with_vmmaps vm11 md)) A12 vm12 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM24) RT26) as RM26.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW26) | apply (pbl_C11 al_rom (mkFP fr20 cs20) r26 m26 s ltac:(lia)); csr; reflexivity |].
  intros fin (r27 & M27 & -> & -> & Q271 & Q272 & Q2710 & AG27).
  pose proof (rgb_fk_use m26 M15 (s - 104) (s - 96) (s - 104) 8 _ FKg26 ltac:(lia) ltac:(lia) S104) as Sg.
  eapply rgb_rz_pc; [apply (pixDestroy_ocomp_W (mkFP fr20 cs20) C A A12 m26 (with_vmmaps vm12 md) r27 (s - 112) (s - 104) gg dgg w h (getr r27 1) S
                       CK HW26 Q272 ltac:(rgb_m16 Hs16) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) eq_refl ltac:(rewrite Q271; rgb_rok)
                       ltac:(csr; reflexivity) Q2710 ltac:(rgb_m8 Hs16) ltac:(lia) ltac:(lia) Sg OCg26 N8) | apply bv_eq; reflexivity].
  intros A13 m28 vm13 r28 HW28 CS28 F28x K28 SL28 PD28 RT28.
  rewrite with_vmmaps_twice in HW28 |- *. rewrite Q271.
  pose proof (rgb_ok_free C A A12 A13 m26 m28 bb dbb w h gg dgg OCb26 DJ20g K28
                (rgb_mem_postd C A13 (s - 112) (s - 104) m26 m28 bb PD28 ltac:(lia))) as OCb28.
  pose proof (rgb_sub_k A A12 A13 gg dgg SL12 (rgb_ok_fr C A A12 m26 gg dgg w h OCg26) K28) as SL13.
  pose proof (POSTM_sub C A A13 s m26 m28 SL13 (POSTD_POSTM_win C A13 m28 (with_vmmaps vm13 md) (s - 112) s (s - 104) m26 CK HW28
                ltac:(lia) ltac:(lia) ltac:(lia) Hhi PD28)) as PM28.
  pose proof (rgb_fk_frmx C (s - 112) (s - 104) m26 m28 M1 (s - 76) s CK (proj1 PD28) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FK26) as FK28.
  pose proof (rgb_fk_frmx C (s - 112) (s - 104) m26 m28 M21 (s - 112) (s - 104) CK (proj1 PD28) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FKb26) as FKb28.
  pose proof (rgb_room0 A12 (m_vmmaps (with_vmmaps vm12 md)) A13 vm13 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM26) RT28) as RM28.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW28) | apply (pbl_C12 al_rom (mkFP fr20 cs20) r28 m28 s ltac:(lia)); csr; reflexivity |].
  intros fin (r29 & M29 & -> & -> & Q291 & Q292 & Q2910 & AG29).
  pose proof (rgb_fk_use m28 M21 (s - 112) (s - 104) (s - 112) 8 _ FKb28 ltac:(lia) ltac:(lia) S112) as Sb.
  eapply rgb_rz_pc; [apply (pixDestroy_ocomp_W (mkFP fr20 cs20) C A A13 m28 (with_vmmaps vm13 md) r29 (s - 112) (s - 112) bb dbb w h (getr r29 1) S
                       CK HW28 Q292 ltac:(rgb_m16 Hs16) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) eq_refl ltac:(rewrite Q291; rgb_rok)
                       ltac:(csr; reflexivity) Q2910 ltac:(rgb_m8 Hs16) ltac:(lia) ltac:(lia) Sb OCb28 N8) | apply bv_eq; reflexivity].
  intros A14 m30 vm14 r30 HW30 CS30 F30x K30 SL30 PD30 RT30.
  rewrite with_vmmaps_twice in HW30 |- *. rewrite Q291.
  pose proof (rgb_sub_k A A13 A14 bb dbb SL13 (rgb_ok_fr C A A13 m28 bb dbb w h OCb28) K30) as SL14.
  pose proof (POSTM_sub C A A14 s m28 m30 SL14 (POSTD_POSTM_win C A14 m30 (with_vmmaps vm14 md) (s - 112) s (s - 112) m28 CK HW30
                ltac:(lia) ltac:(lia) ltac:(lia) Hhi PD30)) as PM30.
  pose proof (rgb_fk_frmx C (s - 112) (s - 112) m28 m30 M1 (s - 76) s CK (proj1 PD30) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FK28) as FK30.
  pose proof (rgb_room0 A13 (m_vmmaps (with_vmmaps vm13 md)) A14 vm14 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM28) RT30) as RM30.
  pose proof (POSTM_trans C A s m m24 m30 PMk24 (POSTM_trans C A s m24 m26 m30 PM26 (POSTM_trans C A s m26 m28 m30 PM28 PM30))) as PMk30.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW30) | |].
  { apply (pbl_XE al_rom fr20 cs20 r30 m30 s ret (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
             (Z_to_bv 64 (u (reg_get fr 8))) (Z_to_bv 64 (u (reg_get fr 9))) FZ20 ltac:(lia) Hret H1).
    all: first [ (apply (rgb_fk_use m30 M1 (s - 76) s); [exact FK30 | lia | lia | assumption]) | csr; reflexivity ]. }
  intros fin (fr31 & cs31 & r31 & M31 & -> & FZ31 & -> & X2 & X10 & X8 & X9 & X18 & X19 & X20 & AG31 & XG8 & XG9 & XGK).
  apply (HK fr31 cs31 A14 m30 vm14 r31 HW30 FZ31).
  - apply cs_kept_of_rest; [rewrite X2, H2; reflexivity | exact X8 | exact X9 |].
    intros x Hx. cbn [In cs_rest] in Hx.
    repeat (destruct Hx as [<-|Hx]; [first [exact X18 | exact X19 | exact X20 | (csr; reflexivity)]|]). destruct Hx.
  - exact PMk30.
  - destruct OUTd as [[-> LV0] | (dd & PN0)].
    + left. split; [csr; reflexivity|].
      intros q. apply (rgb_lv_end A A10 A11 A12 A13 A14 rr drr gg dgg bb dbb (fun _ => True)
                 (fun q a b c => LVb q (conj a b) c) (rgb_cblk_none C A A10 m22 rr drr w h OCr22)
                 (rgb_cblk_none C A A10 m22 gg dgg w h OCg22) (rgb_cblk_none C A A10 m22 bb dbb w h OCb22)
                 (fun q _ => LV0 q) F26x K26 F28x K28 F30x K30 q I).
    + right. exists pd, dd. split; [csr; reflexivity|].
      destruct PN0 as (Gp & Tp & Ap & Gd & Td & Ad & NE & L1 & L2 & L3 & L4 & L5 & L6 & Kp & PXp & Dp).
      pose proof (rgb_notin C A A10 m22 rr drr w h pd OCr22 L1) as NRp. pose proof (rgb_notin C A A10 m22 rr drr w h dd OCr22 L2) as NRd.
      pose proof (rgb_notin C A A10 m22 gg dgg w h pd OCg22 L1) as NGp. pose proof (rgb_notin C A A10 m22 gg dgg w h dd OCg22 L2) as NGd.
      pose proof (rgb_notin C A A10 m22 bb dbb w h pd OCb22 L1) as NBp. pose proof (rgb_notin C A A10 m22 bb dbb w h dd OCb22 L2) as NBd.
      assert (L14p : live A14 (Z_to_bv 64 pd) = Some 64%Z) by (rewrite (K30 _ NBp), (K28 _ NGp), (K26 _ NRp); exact L5).
      assert (L14d : live A14 (Z_to_bv 64 dd) = Some (4 * (p_wpl (set_data (pix_hdr w h 32) dd) * p_h (set_data (pix_hdr w h 32) dd)))%Z)
        by (rewrite (K30 _ NBd), (K28 _ NGd), (K26 _ NRd); exact L6).
      pose proof (rgb_px_postd C A12 (s - 112) (s - 96) m24 m26 pd _ PXp PD26 ltac:(rewrite (K26 _ NRp); exact L5) ltac:(lia)) as PXp26.
      pose proof (rgb_px_postd C A13 (s - 112) (s - 104) m26 m28 pd _ PXp26 PD28 ltac:(rewrite (K28 _ NGp), (K26 _ NRp); exact L5) ltac:(lia)) as PXp28.
      pose proof (rgb_px_postd C A14 (s - 112) (s - 112) m28 m30 pd _ PXp28 PD30 L14p ltac:(lia)) as PXp30.
      unfold pixr_new.
      do 7 (split; [assumption|]).
      split; [exact (pbl_sub_none A A10 _ SL10 L1)|]. split; [exact (pbl_sub_none A A10 _ SL10 L2)|].
      split; [exact L3|]. split; [exact L4|]. split; [exact L14p|]. split; [exact L14d|].
      split; [| split; [exact PXp30 | exact Dp]].
      intros q NQ1 NQ2. apply (rgb_lv_end A A10 A11 A12 A13 A14 rr drr gg dgg bb dbb (fun q => q <> Z_to_bv 64 pd /\ q <> Z_to_bv 64 dd)
                 (fun q a b c => LVb q (conj a b) c) (rgb_cblk_none C A A10 m22 rr drr w h OCr22)
                 (rgb_cblk_none C A A10 m22 gg dgg w h OCg22) (rgb_cblk_none C A A10 m22 bb dbb w h OCb22)
                 (fun q H => Kp q (proj1 H) (proj2 H)) F26x K26 F28x K28 F30x K30 q (conj NQ1 NQ2)).
  - intros x Hx.
    destruct (@bv_eq_dec 5 x 8%bv) as [->|N8']; [rewrite XG8; apply Z_to_bv_bv_unsigned|].
    destruct (@bv_eq_dec 5 x 9%bv) as [->|N9']; [rewrite XG9; apply Z_to_bv_bv_unsigned|].
    rewrite (XGK x (fs_notin_p x [8; 9]%nat Hx N8' N9' ltac:(rgb_inL))). exact (FS20 x Hx N8' N9').
  - rewrite RBv. apply (aroom_mono _ _ _ _ _ _ RM30); lia.
Qed.

Theorem pixBilateral_W : pixBilateral_contract.
Proof.
  intros fr cs C A m md regs s pixs w h d cm datas ret S.
  destruct (Z.eq_dec cm 0) as [Ecm|Ecm]; [|exact (pbl_case_cm fr cs C A m md regs s pixs w h d cm datas ret S Ecm)].
  destruct (Z.eq_dec d 8) as [E8|E8].
  - destruct (Z_lt_le_dec w 22) as [Hw|Hw];
      [exact (pbl_case_w fr cs C A m md regs s pixs w h d cm datas ret S Ecm (or_introl E8) (or_introl Hw))|].
    destruct (Z_lt_le_dec h 22) as [Hh|Hh];
      [exact (pbl_case_w fr cs C A m md regs s pixs w h d cm datas ret S Ecm (or_introl E8) (or_intror Hh))|].
    exact (pbl_case_g fr cs C A m md regs s pixs w h d cm datas ret S Ecm E8 Hw Hh).
  - destruct (Z.eq_dec d 32) as [E32|E32]; [|exact (pbl_case_d fr cs C A m md regs s pixs w h d cm datas ret S Ecm E8 E32)].
    destruct (Z_lt_le_dec w 22) as [Hw|Hw];
      [exact (pbl_case_w fr cs C A m md regs s pixs w h d cm datas ret S Ecm (or_intror E32) (or_introl Hw))|].
    destruct (Z_lt_le_dec h 22) as [Hh|Hh];
      [exact (pbl_case_w fr cs C A m md regs s pixs w h d cm datas ret S Ecm (or_intror E32) (or_intror Hh))|].
    exact (pbl_case_rgb fr cs C A m md regs s pixs w h d cm datas ret S Ecm E32 Hw Hh).
Qed.

End PblW.
