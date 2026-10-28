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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptRoomK LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB LeptCellsB LeptRoomPC LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptPixCreateST V2LeptPixCopyT V2LeptPixDestroyK V2LeptPixDestroyH V2LeptPixMisc V2LeptCmap2 V2LeptKernCreateS V2LeptKernDestroyS V2LeptKernDestroySA V2LeptBl_iface V2LeptBl2_iface V2LeptBl3_iface V2LeptKvals V2LeptBge_iface V2LeptAmbW V2LeptKinv V2LeptBgeSegs V2LeptBgeRun.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpBound FpReal.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2LeptBgeW () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8WalksLib9rostr_chkI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C7ARocqVerifyHarness?AgentSubmission6Common9Leptonica8SumSpecs3SSP9rostr_winC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00C5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB4cellI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI46Stdlib5Lists4List6Exists00C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:asr_callocI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4lctx00C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc8aic_baseC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase2ASK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission2V2BV2LeptKernDestroyS4kobjC45stdpp9bitvector;definitions7Z_to_bvC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_A0K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3mulC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase4liveC47Corelib4Init5Logic3notC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LIVKC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr02C45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common7StepTac6u_Z2bvC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB8LIVK_rdnC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_vmC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB7cellsAtC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB5c_offC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB5c_lenC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB5c_valC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC46Stdlib5Lists4List?Forall_inv_tailI47Corelib4Init6Specif7sumbool00I47Corelib4Init6Specif5sumor00C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init6Specif5sumor02K47Corelib4Init6Specif3sig01K47Corelib4Init6Specif5sumor01C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init9Datatypes7nat_recI47Corelib4Init6Specif3sig00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK45stdpp9bitvector;definitions2bv01I47Corelib4Init5Logic2or00C47Corelib4Init5Logic9False_indC46Stdlib5Lists4List2InC47Corelib4Init5Logic6or_indC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecB7fs_listK47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums8positive00I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3Cok00C5ARocqVerifyHarness?AgentSubmission6Common7FPSteps8frm_zeroC45stdpp9bitvector;definitions4BvWfC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_topC5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5PIXatC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixHdr6hdr_okC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBl3_iface4korgC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure5aroomC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBl2_iface6RB_bgeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs7cs_keptC4ELinuxProcessSemantics5Riscv3Sem7reg_getK5ARocqVerifyHarness?AgentSubmission6Common8PropExec7FPState01C5ARocqVerifyHarness?AgentSubmission6Common:AllocIface6al_romC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPixCreate8pixr_newC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6ll_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_img64C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ro_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_roC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_lg_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_lgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ag_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_agC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=pin_errno_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_errnoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_hcellC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3inZC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_hcellC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;pin_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:ll_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs<pin_ro_belowC4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3subI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6pix_wf00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs9pix_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8bytes_atK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8PIX_rd_wC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_wC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8PIX_rd_hC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_hC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8PIX_rd_dC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_dC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith4dvalC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith<wpl_of_rangeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith6wpl_ofC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase9W_sok_winC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL>RB_pixT_nonnegC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL7RB_pixTC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure?alloc_margin_geC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure<alloc_marginK46Stdlib9micromega5Tauto8GFormula01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL8RB_kernSC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstI47Corelib4Init9Datatypes4prod00I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission6Common5Reach5reachC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW19W_clr_gotC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW19W_clr_sevC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun5ge_AwC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun5ge_AhC5ARocqVerifyHarness?AgentSubmission6Common5Hoare:regs_agreeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9DitherLib4rinvC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=sub_live_reflK47Corelib4Init5Logic2or01K47Corelib5Lists7ListDef6Forall02c5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBgeW8ge_savedC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission6Common7StoreOk9mem_growsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;POSTM_rangeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB>agree_of_rangeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB9agree_winC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface<callee_savedC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun5ge_W2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots9LIVK_byteC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs;PIXat_frameC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL8RB_cmapTK6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5cmapv01C5ARocqVerifyHarness?AgentSubmission2V2?V2LeptCmapValid7cmap_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5c_arrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8c_nallocC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptPixCopyT8pixt_newC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB<agree_of_FRMC5ARocqVerifyHarness?AgentSubmission6Common8PropExec9u64_rangeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8WalksLib8zbv_selfC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun6ge_XcpK47Corelib4Init5Logic2or02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=cs_kept_introC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:aroom_monoC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptPixCopyT5cmresC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3c_dC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3c_nC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptPixCopyT2TKC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptPixCopyT=pixCopy_szT_WC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase>lept_stderr1_WC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun4ge_Ac5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBgeW9kobj_livkC5ARocqVerifyHarness?AgentSubmission2V2AV2LeptKernCreateS4kernC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptRoomK7RK_kernC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8sub_liveC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun4ge_BK47Corelib4Init5Logic2ex01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB=agree_of_rinvC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB<cellsAt_consC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_cmapC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5p_wplC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_dataC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_xresC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_yresC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptBl_iface6bl_srcC5ARocqVerifyHarness?AgentSubmission2V2BV2LeptKernDestroyS9kern_kobjC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBord_iface6RB_abgC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun5ge_CnC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;sub_live_eqC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:LIVK_transc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBgeW<cellsAt_tailC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun6ge_Cn2C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun7ge_XerrC45stdpp9bitvector;definitions9bv_eq_decc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBgeW<ex_range_decC46Stdlib9micromega;ZifyClasses6eq_iffC5ARocqVerifyHarness?AgentSubmission2V29V2LeptErr@returnErrorPtr_WC5ARocqVerifyHarness?AgentSubmission2V2CV2LeptKernDestroySABkernelDestroy_SA_WC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs>sub_live_transC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun4ge_CK47Corelib4Init9Datatypes4prod01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8LIVK_subC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs;PIX_rd_dataC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs:PIX_rd_wplC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun4ge_DC56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs?mod16_plus_mod4C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBgeSegs6ge_geoC5ARocqVerifyHarness?AgentSubmission2V2;V2LeptCmap29blk_apartC5ARocqVerifyHarness?AgentSubmission2V2;V2LeptCmap27blk_sokC56Stdlib6ZArith6BinInt1Z6to_natC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9DitherLib8rinv_rdnC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBgeSegs?wr_readable_bgeC56Stdlib6ZArith4Znat5Z2Nat2idC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9DitherLib8reg_readC5ARocqVerifyHarness?AgentSubmission6Common8PropExec:rdn_lengthC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBgeSegs5ge_rdC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBgeSegs7ge_nestC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBgeSegs5ge_fpC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun4ge_EC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun4ge_FC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs4p_rcC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_textC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptPixDestroy9pixd_postC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom6roomtrC5ARocqVerifyHarness?AgentSubmission6Common8VmLedgerAwith_vmmaps_twiceC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBgeRun4ge_Gc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBgeW;fs_notin_geC56Stdlib6ZArith6BinInt1Z7sub_0_rC5ARocqVerifyHarness?AgentSubmission2V2AV2LeptPixDestroyKApixDestroy_keep_WC5ARocqVerifyHarness?AgentSubmission2V2AV2LeptPixCreateSTApixCreate_sureT_WC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptAmbWJpixAddMirroredBorder_gen_WI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs1W00C5ARocqVerifyHarness?AgentSubmission2V2>V2LeptPixCopyT3hdvC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5POSTMK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixHdr7pix_hdrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8set_dataC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_sp0C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK46Stdlib9micromega7EnvRing5PExpr04C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecW;exW_blk_rngC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega5Tauto8GFormula06C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6w_pureK47Corelib5Lists7ListDef6Forall01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptCmapArr8rinv_WP2C5ARocqVerifyHarness?AgentSubmission6Common7SeqExec6v_jalrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;POSTM_transC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB:cells_keepC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3FRMC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6CMAPatC46Stdlib5Lists4List9nth_errorC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB;cellsAt_nthC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:POSTM_monoC5ARocqVerifyHarness?AgentSubmission6Common5Reach8rz_reachC47Corelib4Init5Logic7f_equalC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9POSTM_subK46Stdlib9micromega=RingMicromega5Psatz01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9DitherLib5inregC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase5LLU16C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LSTKC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBge_iface6RK_bgeI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL:RB_cmapT_0C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom6RK_pixC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBgeSegs3GNLI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSetC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBge_iface9BGE_STACKI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8LSTK_valC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64I47Corelib7Numbers7BinNums1N00c5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBgeW;str_ge_fmtWc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBgeW;str_ge_procC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase3LSFC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomPC:RK_pixcopyI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init9Datatypes:comparison01c5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBgeW;str_ge_msgTc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBgeW8bgew_fxdC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptKinv>kernelInvert_Wc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBgeWGpixBilateralGrayExact_H".
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma str_ge_fmtW : str16 69472 85.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBgeW ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;3p;2p;4p;7p10000p4p70R0p1000`p4p710R1p8P0p1001<p4p710R0p8p1001Zp4p70R2P1p8P2P0p8p1002Hp4p7210P0p8p10034p4p70R2P1p8P2P0p8g003jj11Tg004Oj10Tg0054j14Tg005Rj3NTg006Zj3=Tg0074j26Tg007Pj27Tg007kj2@Tg0097j2;Tg009Tj2?Tg009nj1>Tg00:Nj1MTg00:nj1LTg00;Lj1KTg00;jj1DTg00<Uj2<Tg00=8j3CTg00=[j2BTg00>=j2ETg00>ij3ATg00?Hj4FTg00@:j4GTg00@Uj4HTg00A@j7ITg00Adj7JTf0R0#0#0#0#0p=2%00#0p=5g00BHR2/<0p=3P2f1R1g00BfP0CHp=8P1g00CMR3g00ClR4P4g00DLR5P0g00DlFIp=9f2R6P3P4P4P5P1P0FJp=:g00ELR4g00Elg00G>R3#2#1#1#1#1#0#1#1#0#2#4R7%03R8#1#0#1R9#0#1#4R:3Ng00GcR;3=R<g00HCR=/6:%13#5#1#0#5#4R>,6:'7R?%08#5#2#2#2#4R8/67R@1@7:,;7%03#5#1#5#2#2#2#4R3'6'7'71?4;RAP<dg00HaR<#>%M<%L2%K2%D2R<1<2=%3:R:'8,9<%3>,8:,9<5:<%38%37R8'8,9<%19#0#4R9#39C28%33'8,9<5:<3:1B<5P0P6PA1E06==4;dAA2=1CFb1b2b31;79/63,7@,7?P0b0CGo"). Qed.
Lemma str_ge_proc : str16 73628 21.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBgeW ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;3p;2p;4p;7g004Oj10Tg003jj11Tg0054j14Tg005Rj3NTg006Zj3=Tg0074j27Tg007Pj26Tg007kj2@Tg0097j2;Tg009Tj2?Tg009nj1>Tg00:Nj1MTg00:nj1LTg00;Lj1KTg00;jj1DTg00<Uj2<Tg00=8j3CTg00=[j2BTg00>=j2ETg00>ij3ATg00?Hj4FTg00@:j4GTg00@Uj4HTg00A@j7ITg00Adj7JTf0R0#0#0p=2%00#0#0#0p=5g00BHR1/<0p=3P1f1R2g00BfP0CHp=8P2g00CMR3g00ClR4P4g00DLR5P0g00DlFIp=9f2R6P3P4P4P5P2P0FJp=:g00ELR4g00Elg00G>R3#0#2#1#1#1#1#1#1#2#1#1#1#2#4R7%03R8#1#0#1#4R93Ng00GcR:3=R;g00HCR</79%13#0R=#0#1#0#2#4R>,79'6R?%08#2#5#5#5#4R8/77R@1@79,;7%03#2#1#2#5#5#5#4R3'7'6'61?4:RAP;dg00HaR;#>%M;%L1%K1%D1R;1<1<%39R9'8,9;%3>,89,9;5:;%38%37R8'8,9;%1=#0#4R=#39C18%33'8,9;5:;3:1B;5P0P6PA1E06==4:dAA1<2CFb1b2b31;7=/73,6@,6?P0b0CGo"). Qed.
Lemma str_ge_msgT : str16 72325 13.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBgeW ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;3p;2p;4p;7g004Oj10Tg003jj11Tg0054j14Tg005Rj3FTg006Zj3<Tg0074j25Tg007Pj26Tg007kj2@Tg0097j2;Tg009Tj2?Tg009nj1>Tg00:Nj1NTg00:nj1MTg00;Lj1LTg00;jj1ETg00<Uj2=Tg00=8j3CTg00=[j2BTg00>=j2DTg00>ij3ATg00?Hj4GTg00@:j4HTg00@Uj4ITg00A@j7JTg00Adj7KTf0R0#0#0p=7%00#0#0#0p=2g00BHR1/=0p=3P1f1R2g00BfP0CIp=8P2g00CMR3g00ClR4P4g00DLR5P0g00DlFJp=9f2R6P3P4P4P5P2P0FKp=:g00ELR4g00Elg00G>R3#0#7#1#1#0#1#0#1#2#1#0#1#4R7%13#0R8#1#4R93Fg00GcR:3<R;g00HCR</59%08#1#0#7#4R8,59'6R=%03#7R>#0#2#2#2#4R?/57R@1@79,;7%03#7#1#7#2#2#2#4R3'5'6'61?4:RAP;dg00HaR;#>%N;%M1%L1%E1R;1=1<%39R9'8,9;%38,89,9;5:;%3?%37R?'8,9;%1>#4R>#39C1?%33'8,9;5:;3:1B;5P0P6PA1D06=<4:dAA1<2CGb1b2b31;7>/53,6@,6=P0b0CHo"). Qed.

Section BgeW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Hypothesis H_kinv : kernelInvert_contract.
Hypothesis H_ambg : forall (fx : FPState) C A m md regs (s pixs l r t b : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + AMB_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 l -> getr regs 12 = Z_to_bv 64 r -> getr regs 13 = Z_to_bv 64 t -> getr regs 14 = Z_to_bv 64 b ->
  bl_src A m pixs v -> (1 <= l <= 64)%Z -> (1 <= r <= 64)%Z -> (1 <= t <= 64)%Z -> (1 <= b <= 64)%Z ->
  (l <= p_w v)%Z -> (r <= p_w v)%Z -> (t <= p_h v)%Z -> (b <= p_h v)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_pixT (4 * (wpl_of (p_w v + l + r) 8 * (p_h v + t + b))) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd data, getr regs' 10 = Z_to_bv 64 pixd /\ hdr_ok (p_w v + l + r) (p_h v + t + b) 8 /\
                            pixr_new C A A' m' pixd data (set_data (pix_hdr (p_w v + l + r) (p_h v + t + b) 8) data))) ->
     aroom A' vm' (kR - RK_pix) (bR - RB_pixT (4 * (wpl_of (p_w v + l + r) 8 * (p_h v + t + b)))) ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixAddMirroredBorder) m al_rom) md) S.
(* [comment removed for export] *)
#[local] Instance bgew_fxd : FPState | 100 := mkFP bvmap_empty (Z_to_bv 32 0).
#[local] Opaque RiscvSemantics.store_ok.


(* [comment removed for export] *)
Definition hide (P : Prop) : Prop := P.
Ltac hideH H := lazymatch type of H with ?P => change P with (hide P) in H end.

(* [comment removed for export] *)
Lemma kobj_livk : forall C A A' (m m' : word -> option byte) kel arr h w rows,
  kobj C A m kel arr h w rows -> LIVK A m m' -> (forall (q : word) k, live A q = Some k -> live A' q = Some k) -> (0 <= h)%Z -> (0 <= w)%Z ->
  (alloc_top (c_vm C) < 2 ^ 64)%Z -> kobj C A' m' kel arr h w rows.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBgeW ()) ["BgeW"] "h01ih14__x1h21jh31Hh47__arithh54__x2h64__ffh78__varmaph85__with91kh:1qh;7__sat25h<7__sat26h=4__x3h>4__x4h?4__x5h@1zhA7__sat17hB7__sat18hC4cstrhD1xhE4__p1hF1nhG2HahH4__x6hI2bshJ1mhK1ohL1AhM2A'hN2AThO1ChP4CK24hQ4DISThR2G1hS2G2hT2G3hU2G4hV2G5hW2G6hX2G7hY2GahZ2Gkh[2H1h\2H2h]2Hhh^2Hih_2Hwh`2LKha2Lahb3La0hc2Lkhd3Lk0he4NEkahf1Rhg4ROWShh4Rarrhi3Rsxhj3Rsyhk3SUBhl4TOPahm4TOPkhn1aho3arrhp1hhq3kelhr2m'hs4rowsht1whu1yp%0p%1p&0p;3p;2p;1p;;p;4p;6p;@p;7p;8p;<p;Bp100IMp4p70R0p100JRp4p710p8P0p100K3p4p710p8P0p100KPp4p710p8g00Kmk30eTg00M6k30dTg00N;k30QTg00ODk20HTg004Oj1TTg00PEk10?Tg00Pck10<Tg00QFj1{Tg00Qhl;JTg0054j1]Tg0074R0j29Tg003jk103Tg00Rgj20Tg00SMj4GTg00TPk10>Tg00:Nk10=Tg00U2j1XTg00UQj22Tg00Unj4gTg00W1j1[Tg007PR1j27Tg00WJj6ITg00XMk20aTg00Xjj2@Tg00YFR2j1`Tg0097R3j2?Tg00Yfj2MTg00ZHk10YTg00Zmk20XTg00[Uk30WTg009nk10VTg00:nk10TTg00;Lk10STg00;jk10PTg00\9j2iTg00=[k20OTg009Tk20;Tg00>=k20NTg006Zj3ATg00>ik30MTg00?Hk40KTg00\\k20:Tg00<Uk209Tg00]Fk208Tg00]oj2nTg00^[k30ITg00_>k307Tg00`8m@06Tg001<j6|Tg00aAj2mTg00bIk10GTg00bgk40FTg00cJj4vTg00d5k20ETg00daj3yTg00eDk20LTg00emk301Tg00@:j4}Tg00fVk40BTg00gYk10RTg00hQj4^Tg00iIk20ATg00igk40UTg00@Uk400Tg00A@k70@Tg00jEj8~Tg00jik30cTg00kRj3rTg00=8k30bTg00l2m<0`Tg00lWmB0^Tg00m=m<0]Tg00mbk60\Tg00nFk60[Tg00Adk70_Tf3R4f2R5f1R6f0R7H0B$0Rp=4g00BHR8/M7p=b1067,m5,M4p=S1m67,M5p=3AA867p=Ug00HCR9/97p=B1@67,75p=1f6R:f5R;f4R<P4P5P6CGP7Cgp=51?67,05p=:f7R=?A:;g00ElS00P4P5P6C^=A<7'7p=;P;P<P4P5Cg1M865A:/77p=6AA8<4#[AA856#[/77'7p==19;<1?45/96/77'7p=>AA867#[p=<P;P<P4P5Cg=A:6/77p=E%[<AA456/77'7p>0DQ00P:1?<4,0;P5C^=A=6/77p=CQ00P<P4P5C^=A;6/77p=W1?45/96/77p=jP<P4P5P6Cg=A;7p=81?56/97p=DAA856#[/77p=a1767,75p=q19=:1?;</94AA856#[/77'7'7p=NQ00P;1?45,0<P6C^=A:7p=ZAA<451767'7p=HQ00P;P<P4C^1m67,M55A:p>0ZQ00P4P5P6C^=A<7p=pP:P;P<P4Cg1256,M85A=/77p=Y1267,M8p=wQ00P5P6P7C^p=l1M679A45p=u20A87p=kP8P5P6P7H0Up=QP5g00CMR>g00ClR?P?g00DLR@P8P6g00BfP7H00g00DlRAK0@p=FP4P>P?P?P@P5P6P7G~p=o20987p=f20887p=eB0c867p=Rg00HaRB?r67p>0JP8P6g00njP7H00p=dP6P>P?P?P@P7PAK0@p=KB0b867p=LP:P>P?P?P@P;P<P4P>P?P?P@P5P6P7G~G~p=OP8P<P4P5P6P7E|p=c1067,m5p=xAA567,74p>0520;87p=Pg00oQS01P8P8P8P2P2P;P<P4P5P6P7N<0`p>04P8P8P8P8P8P8P3P7P6P5P3P4P<P;P:P=f8R3f9R2NB0^p=tP8P8P0P=P0P:P;P<P4P5P6P7N<0]p=sArB679rB59rB49rB<p=hP8P6g0100P7H00p=\P6P>P?P?P@P7J0\p=_P6P>P?P?P@P7J0[p>02P5P>P?P?P@P6P7K0_p=z1267,?5p>0CP:P;P<P4P5P6P7C}C}p=Vp,2ALR>p,2CLR0p,3ASRRA:0e>0RC40dB0Q>0CRD-0H>S02Q02g00G>S03#TS04#TS05#TRE#TRF#T#TRG$0?RH$0<RI&0?E$0<RJ#{[S06Q06P8\8P>P0PAP2P3P:P<P4P5P6P7M;JP1Q03#]RK/9;P;Q03$03S07#TS08#T#T#]RLP>P0PCf:RMC4RN%{8ROP>PDP210H;RP%bLS09POP>PDP>P0PCPMCGRQPP&0>8RR&0=JRJ#{RSP=PPg010WS0:#XS0;#XS0<#XS0=#XRTPJPTPHP4CSPSP=PHP;Q05#]RUPTPJPTPHP5CSPSP=PHP;%]FRF%XTS0>#XS0?#X#XRV10H<S0@93JVPKP<P<%]ERE/24S0APN1U;<S0BPOP>PDP2Q0@CgQ0A#bPOP>PDPQQ0@PR%B7RQ?17<PKP4P6O1RNPN12U<RWP>P0PCf<RXC4PNP:PNP=POP>PDf;RY10HNRNPWPOP>PDP>P0PCPXPNF5PRPSP212E6RW9:H:PVA3JVNG;F6D=E>[^08%B6RN?16;A1N6:1U45S0C#[RZP:P<O1P:P4O1'<[[[^28^08'7FEI0DE>GCGCEWFEFECjP>P0PCPMP3P=EIPOP>PDf=R[P6%b7R\E8POP>PDP[P5%b6R]E8[^98^:I%B:S0DQ0DP>P0PCf?R^C4R_Q04#]R`%]GRG+0aRa'@P>P0PAf@Rbf>RcPXPYPMP2P3P=M;J[[[[[P719K=RdP3PLP>P0PCP[C4RePOP>PDPX10H3RfQ09POP>PDP>P0PCP[CGRgPfPRPSPMPfPTPJPTPHP:CSRhPSPMPHP3PUPTA3JTPPSPMPHP3PFPV10H=Ri93JV12E:S0E=D=ePOP>PDPXPiQ0EPOP>PDPgPiPRA1Q7=PKP:P6O1RgPg12U=ReP_PgP2PgPMPOP>PDPc10HgRgPePOP>PDP>P0PCP^PgF5PRPSPXA:H2WPVA3JVgG;F6D=E>[^08A1N63A1N62RgP2P<O1P2P4O1'<\Z[[^28^08'7FEF69a3=5qdGCGCEWFEFECjP1P>P0PCPcC4Rd9D2LPOP>PDP[10H2ReQ09POP>PDP>P0PCPcCGR_PePRPSPYPePTA3JTiPSPYPHP2PUPTPhPSPYPHP2PFPVA3JVfPKP3P312E=S0FPdP2P3POP>PDP[PfQ0FPOP>PDP_PfPRA1Q73PKP=P6O1RfPf12U3R_P>P0PCPbC4RdPfPMPfPYPOP>PDP^10HfRfP_POP>PDP>P0PCPbPfF5PRPSP[A:HMWPVA3JVfG;F6D=E>[^08A1N6MPMP<O1PMP4O1'<\Z[\g^28^08'7FEF6GNGCGCEWFEFEP>P0PCPcPXPYEIPOP>PDfARgP6P\E8POP>PDPgP5P]E8[^98^:I%BMRfP>P0PCfCR_C4Rh/@aP>P0PAfDRifBRjPbP^PcP[PXPYM;J[\f[[[P7ADYLdPOP>PDPb10HXRdQ09POP>PDP>P0PCPgCGRfPdPRPSPcPdPTPJPTPHPMCSRkPSPcPHPXPUPTA3JTePSPcPHPXPFPV10HYRe93JVPKPYPY12EMS0GP>P0PCPgC4PXPYPOP>PDPbPeQ0GPOP>PDPfPePRA1Q7YPKPMP6O1RfPf12UYRlPhPfP[PfPcPOP>PDPj10HfRfPlPOP>PDP>P0PCP_PfF5PRPSPbA:H[WPVA3JVfG;F6D=E>[^08A1N6XA1N6[RfP[P<O1P[P4O1'<\Z[[^28^08'7FEF6GNGCGCEWFEFEP1POP>PDPg10H[RlQ09E8POP>PDP>P0PCPjCGRhPlPRPSP^PlPTA3JTePSP^PHP[PUPTPkPSP^PHP[PFPVA3JVdPKPXPX12EYS0HP>P0PCPjC4P[PXPOP>PDPgPdQ0HPOP>PDPhPdPRA1Q7XPKPYP6O1RdPd12UXRhP>P0PCPiC4PdPcPdP^POP>PDP_10HdRdPhPOP>PDP>P0PCPiPdF5PRPSPgA:HcWPVA3JVdG;F6D=E>[^08A1N6cPcP<O1PcP4O1'<\Z[\f^28^08'7FEF6GNGCGCEWFEP>P0PCPjPbP^EIPOP>PDfERfP6P\E8POP>PDPfP5P]E8[^98^:I%BcRdP>P0PCfGRhC4Rk/@aP>P0PAfHRefFRmPiP_PjPgPbP^M;J[\d[[[P7POP>PDP_10H^RdQ09E8POP>PDP>P0PCPfCGRn10HbRoPRPSPjPoPTPJPTPHPcCSRpPSPjPHPbPUPTA3JTlPSPjPHPbPFPVA3JVdPKP^P^12EcS0IP>P0PCPfC4PbP^POP>PDPiPdQ0IPOP>PDPnPdPRA1Q7^PKPcP6O1RnPn12U^RlPkPnPgPnPjPOP>PDPm10HnRnPlPOP>PDP>P0PCPhPnF5PRPSPiA:HgWPVA3JVnG;F6D=E>[^08A1N6bA1N6gRnPgP<O1PgP4O1'<\Z[[^28^08'7FEF6GNGCGCEWFEP1POP>PDP>P0PCPmCGRl10HgRkPRE8PSP_PkPTA3JTdPSP_PHPgPUPTPpPSP_PHPgPFPVA3JVoPKPbPb12E^S0JP>P0PCPmC4PgPbPOP>PDPfPoQ0JPOP>PDPlPoPRA1Q7bPKP^P6O1RoPo12UbRlP>P0PCPeC4PoPjPoP_POP>PDPh10HoRoPlPOP>PDP>P0PCPeCGRlPoPRPSPfPHPjPWPVA3JVoFZFEF6D=E>[^08A1N6jPjP<O1PjP4O1'<\Z[\n^28^08'7FEF6GNGCGCEWP>P0PCPmPiP_EIPOP>PDfIRnP6P\E8POP>PDPnP5P]E8[^98^:I%BjRoP>P0PCfKRpC4Rd/@aP>P0PAfLRqfJRrPePhPmPfPiP_M;J[\o[[[P7POP>PDPl10H_RlPRE8PSPm10HiRoPTPJPTPHPjCSRsPSPmPHPiPUPTA3JTkPSPmPHPiPFPVA3JVlPKP_P_12EjS0KP>P0PCPnC4PiP_POP>PDPePlQ0KPOP>PDP>P0PCPnPlF5PRA1Q7_PKPjP6O1RkPk12U_RtPdPkPfPkPmPOP>PDPr10HkRkPtPOP>PDP>P0PCPpPkF5PRPSPeA:HfWPVA3JVkG;F6D=E>[^08A1N6iA1N6fRkPfP<O1PfP4O1'<\Z[[^28^08DHF6GNGCGCEWP1PSPh10HfRtPTPJPTPlK0ZPSPhPHPfPUPTPsPSPhPHPfPFPVA3JVoPKPiPi12E_S0LP>P0PCPrC4PfPiPOP>PDPnPoQ0LPOP>PDP>P0PCPrPoF5PRA1Q7iPKP_P6O1RoPo12UiRsP>P0PCPqC4PoPmPoPhPOP>PDPp10HoRoPsPOP>PDP>P0PCPqPoF5PRPSPnA:HmWPVA3JVoG;F6D=E>[^08A1N6mPmP<O1PmP4O1'<\Z[\k^28^08DHF6GNGCGCP>P0PCPrPePhEIPOP>PDfMRkP6P\E8POP>PDPkP5P]E8[^98^:I%BmRoP>P0PCfORsC4Rl/@aP>P0PAfPRdfNRuPqPpPrPnPePhM;J[\o[[[P7PSPn10HhRoPTA3JTtRtDpPSPrPHPePUPTPtPSPrPHPePFPVA3JVoPKPhPh12EmS0MP>P0PCPkC4PePhPOP>PDPqPoQ0MPOP>PDP>P0PCPkPoF5PRA1Q7hPKPmP6O1RoPo12UhRtPlPoPnPoPrPOP>PDPu10HoRoPtPOP>PDP>P0PCPsPoF5PRPSPqA:HnWPVA3JVoG;F6D=E>[^08A1N6eA1N6nRoPnP<O1PnP4O1'<\Z[[^28^08DHF6GNGCGCP1PSPpPHPnPUPTPJPTPHPmCSFZPSPpPHPnPFPV10HeRt93JVPKPePe12EhS0NP>P0PCPuC4PnPePOP>PDPkPtQ0NPOP>PDP>P0PCPuPtF5PRA1Q7ePKPhP6O1RlPl12UeRvP>P0PCPdC4PlPrPlPpPOP>PDPs10HlRlPvPOP>PDP>P0PCPdPlF5PRPSPkA:HrWPVA3JVlG;F6D=E>[^08A1N6rPrP<O1PrP4O1'<\Z[\o^28^08DHF6GNGCP>P0PCPuPqPpEIPOP>PDfQRoP6P\E8POP>PDPoP5P]E8[^98^:I%BrRlP>P0PCfSRvC4Rw/@aP>P0PAfTRxfRRyPdPsPuPkPqPpM;J[\l[[[P7PSPkPHPpPUPTA3JTtFZPSPuPHPqPFPV10HpRt93JVPKPpPp12ErS0OP>P0PCPoC4PqPpPOP>PDPdPtQ0OPOP>PDP>P0PCPoPtF5PRA1Q7pPKPrP6O1RtPt12UpRlPwPtPkPtPuPOP>PDPy10HtRtPlPOP>PDP>P0PCPvPtF5PRPSPdA:HkWPVA3JVtG;F6D=E>[^08A1N6qA1N6kRtPkP<O1PkP4O1'<\Z[[^28^08DHF6GNGCP1PSPsPHPkPFPV10HqRl93JVFZPKPqPq12EpS0PP>P0PCPyC4PkPqPOP>PDPoPlQ0PPOP>PDP>P0PCPyPlF5PRA1Q7qPKPpP6O1RlPl12UqRwP>P0PCPxC4PlPuPlPsPOP>PDPv10HlRlPwPOP>PDP>P0PCPxPlF5PRPSPoA:HuWPVA3JVlG;F6D=E>[^08A1N6uPuP<O1PuP4O1'<\Z[\t^28^08DHF6GNP>P0PCPyPdPsEIPOP>PDfURtP6P\E8POP>PDPtP5P]E8[^98^:I%BuRlP>P0PCfWRwC4Rz/@aP>P0PAfXR{fVR|PxPvPyPoPdPsM;J[\l[[[P7PSPoPHPsPFPVPJPVPHPuCSFZPKPsPs12EuRlP>P0PCPtC4PdPsPOP>PDPx10HsR}PlPOP>PDP>P0PCPtP}F5PRA1Q7sPKPuP6O1RuPu12UsR}PzPuPoPuPyPOP>PDP|10HuRuP}POP>PDP>P0PCPwPuF5PRPSPxA:HoWPVA3JVuG;F6D=E>[^08A1N6dA1N6oRuPoP<O1PoP4O1'<\Z[[^28^08DHF6GNP119KdPd12EsR}P>P0PCP|C4POP>PDPt10HdRzP}POP>PDP>P0PCP|PzF5PRA1Q7dPKPsP6O1RzPz12UdR}P>P0PCP{C4PzPyPzPvPOP>PDPw10HzRzP}POP>PDP>P0PCP{PzF5PRPSPtA:HyWPVA3JVzG;F6D=E>[^08A1N6yPyP<O1PyP4O1'<\Z[\u^28^08DHF69aodCjP>P0PCP|PxPvEIPOP>PDfYRoP6P\E8POP>PDPoP5P]E8[^98^:I%ByRuP>P0PCf[RzC4S0Q/@aP>P0PAf\R}fZRlP{PwP|PtPxPvM;J[\u[[[P719KyPv12EyRuP>P0PCPoC4POP>PDP{10HvR~PuPOP>PDP>P0PCPoP~F5PRA1Q7vPKPyP6O1RyPy12UvR~Q0QPyPtPyP|POP>PDPl10HyRyP~POP>PDP>P0PCPzPyF5PRPSP{A:HtWPVA3JVyG;F6D=E>[^08A1N6xA1N6tRyPtP<O1PtP4O1'<\Z[[^28^08DHF69axvCjP112EvR~P>P0PCPlC45DxPOP>PDPo10HxRuP~POP>PDP>P0PCPlPuF5PRA1Q7xPKPvP6O1RuPu12UxR~P>P0PCP}C4S0QPuP|PuPwPOP>PDPz10HuRuP~POP>PDP>P0PCP}PuF5PRPSPoA:H|WPVA3JVuG;F6D=E>[^08A1N6|P|P<O1P|P4O1'<\Z[\y^28^08DHF69atxP>P0PCPlP{PwEIPOP>PDf]RxP6P\E8POP>PDPxP5P]E8[^98^:I%B|S0RQ0RP>P0PCf_RyC4S0S/@aP>P0PAf`Ruf^R~P}PzPlPoP{PwM;J[[[[[P712EtQ0Q5D|POP>PDP}10HwRtPEP|POP>PDP>P0PCPxPtF5PRA1Q7wPKP|P6O1R|P|12UwRtQ0SP|PoP|PlPOP>PDP~10H|R|PtPOP>PDP>P0PCPyP|F5PRPSP}A:HoWPVA3JV|G;F6D=E>[^08A1N6{A1N6oR|PoP<O1PoP4O1'<\Z[[^28^08DHGY9a{wP11<o{POP>PDPx10H{RoPEPwPOP>PDP>P0PCP~PoF5PRA1Q7{PKPwP6O1RoPo12U{R{P>P0PCPuC4PoPlPoPzPOP>PDPy10HoRoP{POP>PDP>P0PCPuPoF5PRPSPxA:HlWPVA3JVoG;F6D=E>[^08A1N6lPlP<O1PlP4O1'<\Z[\|^28^08DHGYP>P0PCP~P}PzEIPOP>PDfaR|P6P\E8POP>PDP|P5P]E8[^98^:I%BlRoP>P0PCfcS0SC4S0Q/@aP>P0PAfdR{fbRtPuPyP~PxP}PzM;J[\o[[[P71<zlPOP>PDPu10HzRoPEPlPOP>PDP>P0PCP|PoF5PRA1Q7zPKPlP6O1RoPo12UzS0RQ0QPoPxPoP~POP>PDPt10HoRoQ0RPOP>PDP>P0PCQ0SPoF5PRPSPuA:HxWPVA3JVoG;F6D=E>[^08A1N6}A1N6xS0RPxP<O1PxP4O1'<\Z[[^28^08DHGYP1POP>PDP|10H}Ro1wEzE8POP>PDP>P0PCPtPoF5PRA1Q7}PKPzP6O1RoPo12U}R}P>P0PCP{C4PoP~PoPyPOP>PDQ0S10HoRoP}POP>PDP>P0PCP{PoF5PRPSP|A:H~WPVA3JVoG;F6D=E>[^08Q0RA1N6~P~P<O1P~P4O1'<\Z[[^28^08DHP>P0PCPtPuPyEIPOP>PDfeS0RP6P\E8POP>PDQ0RP5P]E8[^98^:I%B~S0QQ0QP>P0PCfgS0TC4S0U/@aP>P0PAfhRoffR}P{Q0SPtP|PuPyM;J[[[[[P7POP>PDQ0S10H~1wExE8POP>PDP>P0PCQ0R10HyF5PRA1Q7yPKP~P6O1R~P~12UyRxQ0UP~P|P~PtPOP>PDP}10H~R~PxPOP>PDP>P0PCQ0TP~F5PRPSP{A:H|WPVA3JV~G;F6D=E>[^08A1N6uA1N6|R~P|P<O1P|P4O1'<\Z[[^28^08DHP1POP>PDP>P0PCP}CG10HuPRE8A1Q7uPKPyP6O1RxPx12UuRuP>P0PCPoC4PxPtPxQ0SPOP>PDQ0T10HxRxPuPOP>PDP>P0PCPoCGS0UPxPRPSQ0RPHPtPWPVA3JVxFZFEF6D=E>[^08A1N6tPtP<O1PtP4O1'<\Z[\~^28^08'7P>P0PCP}P{Q0SEIPOP>PDfiS0QP6P\E8POP>PDQ0QP5P]E8[^98^:I%BtR~P>P0PCfkRxC4Ru/@aP>P0PAflS0VfjS0WPoQ0TP}Q0RP{Q0SM;J[\~[[[P7POP>PDQ0U10HtPRE8Q0S91Q7PKPtP6O1RtPtQ0S,2UR~PuPtQ0RPtP}POP>PDQ0W10HtRtP~POP>PDP>P0PCPxPtF5PRPSPoQ0R=:HWPVA3JVtG;F6D=E>[^08A1N6{Q0R91N6RtQ0RP<O1Q0RP4O1'<\Z[[^28^08'7P1A1Q7{PKQ0SP6O1R~P~12U{RuP>P0PCQ0VC4P~P}P~Q0TPOP>PDPx10H~R~PuPOP>PDP>P0PCQ0VP~F5PRPSQ0QA:H}WPVA3JV~G;F6D=E>[^08A1N6}P}P<O1P}P4O1'<\Z[\t^28^08P>P0PCQ0WPoQ0TEIPOP>PDfmS0UP6P\E8POP>PDQ0UP5P]E8[^98^:I%B}RtP>P0PCfoR~C4/@aP>P0PAfpRAfnRuQ0VPxQ0WQ0QPoQ0TM;J[\t[[[P7A1Q7}PKQ0RP6O1RtPt12U}R}P>P0PCPuC4PtPoPtQ0QPOP>PDQ0U10HtRtP}POP>PDP>P0PCPuPtF5PRPSPxA:HoWPVA3JVtG;F6D=E>[^08A1N6oQ0Q91N6Q0QP<O1Q0QP4O1'<\Z[[^28^08P>P0PCQ0UPxQ0WEIPOP>PDPAP6P\E8POP>PDPAP5P]E8[^98^:IQ0Q#BS0WQ0WP>P0PCfrRIC4/@aQ01fqS0X/95S0Y%`51?IL5D4S0ZPSfuS0[Q0@P41MJ5DpS0@PSfvS0\?lP<PSP7PJP<CuXKSP7Q0[?lP<S0]P>P0PCQ00fxRPQ0\Q0[ftR],0HS0^PLP;P<PMP{P]197:X@8&0Y<S0_%`<#BS0`20X`GR{1@9`%BG1@9a[[R\%B`Rxg0116RoB0W`G6UWGRG%Ba\o^GxRx&0VBS0a&0=BS0b%k5S0c&0T8S0d7Q6S0e&0S8RB&0P8RoQ03,i8RtQ04,i8R}5FoS04&0>?R?Q04Co20Oo@S04P7P5g00ELS03g00GcR@+0;Q0320N75;A@dB0M896H0KR@b6b7b8X18X5819761965[^18^58P7P2PPP:O3b4bAbBbCQ0^-0:HS0^Q0_Q0`P{P\PGPxQ0aQ0b%k6S03PBPo%fK=FotP?20989S0f=FotCoQ04P@b6b7b8X18S0g19K7PN[^18S0hP7PPPAO2b4bAbBbCQ0_Q0`P{P\PGPxQ0<#eS0<Q0;#eQ0:-088S0:'RS0;'Rg011RS0i'nQ0a+0JS0jQ0bQ0ePBPo%f`>0I8HS0k,d},KoS0lP?Po%fLS0m,LtS0n=Fo}S0oP?Q0k,dt,KoS0pFOQ04P@b6b7b8X18X581@6aS0qAD6L5S0r1@5a[[^18^58P7P>P0PCf}S0sC4S0tPPPMQ0VO4S0ub4bAbBbC607]S0vDcP]%`;1?7LS0w5D:X@8Q0_Q0`P{P\PGPxQ0aQ0bQ0c%k47Q6PBPo1Lt}Q07,i8R`Q0m'L5FoR9P?P9CoQ04P@b6b7b8X18X58X=81?5LR99D761?4L9D65[^18^58^=8P7PP%`3P2P;O4b4bAbBbCQ0^Q0vDcP]Q0w/9aX@8Q0_Q0`P{P\PGPxQ0jQ0bQ0ePBPoQ0lP?PoQ0oP?Q0nQ0k5FoFOQ04P@b6b7b8X18X58Q0qQ0r199a[[^18^58Q0ub4bAbBbCQ0^Q0vDcN@06E|WfW\W[XIJWFXD8Q01Q0YQ0ZQ0@PSQ0]PJP4Cu[[[^IJ]F^D819K~1?~LR9P>P0PCP]C4S0Y'9S0ZPOP>PDPI10H~S0@Q09E8S09POP>PDP>P0PCP]CGS0]Q0@PRE8S0vPSPAQ0@PTQ0U9xTHS0^,MJDpS0uPSPA1?~US0q,0HPTQ0V9xTHS0V,MJDpS0rPSPA1?~FS0o,0HPV10HuS0l,mVS0e,MJDpS0j19KuS0`Q0U,2ES0_Q0Y5DuS0Y1<~uS0xPOP>PDPIQ0lQ0_#bE8S0yPOP>PDQ0]Q0lPRE8S0]A1Q7uS0zQ0UP6O1RQ,9KS0U12UuS0{P>P0PCQ0\C45DQS0|1<QAS0}Q0X,<QS0~POP>PDP]10HQRQQ0{#bS0{POP>PDP>P0PCQ0\CGPQPRE8S10PSA:HAWS11=lIVA3JVQS12H05FE3q3q[^08S13A1N6~A1N6APAP<O1S14PAP4O1'<\Z[[^28^08S15'7S16'7S17'7S18'7S19'7S1:'7S1;'7S1<'7S1='7RZ'7RN'7RW'7Q0TQ0ZPWQ0SQ09PNP<Q0@PLPyO3Q0vPZPzQ0uQ1=P7P~PTQ0^P{P\PGPxQ0aQ0bQ03PBAFottQ04P@b6b7b8X181977^18P7PIO1Rzb4b;b<%`TRZ,?~Ry/99S0^Q0q/99P7XD8RN1967$0GXu8XD8S1=PyQ0qPNPNPNP8P8g012>1?67H0F#PXJ8XF8S0uP~P~%P~PZPUPNPNQ01%`7#PWDS01PTPU%PUJ04S0vM:tP9P9%P9S0@GsP{P\PGPxQ0aQ0bQ03PB%fUS09,LtRyQ0n5FoQ04P@b6b7b8X181?7URWQ0w'9^18Pzb4b;b<CvQ0^ePwO6Q0rQ1<P7Q0qPTQ0VP{P\PGPxQ0aQ0bQ03PBAFotyQ04P@b6b7b8X18197W^18Pzb4b;b<Q0q/?ZS0V/99S1<Q0q/?URw/99PNQ1=Q0VPwPNPNPNQ0uQ0qQ0qQ0q#PPZPUQ0vM:tP9P9Q0@GsP{P\PGPxQ0aQ0bQ03PBQ09,LyQ0n5FoQ04P@b6b7b8X18Q0w9DWU^18Pzb4b;b<CvQ1<ePvO6Q0jQ1;P7Q0oPVQ0eP{P\PGPxQ0aQ0bQ03PB%fF,LtRv9FotQ04P@b6b7b8X181?7FRF,97^18Pzb4b;b<Q0o%`VRW'?Ry/99RZQ0o/?ERw/99PNQ1=PyPwPNPNPNQ0uQ0oQ0oQ0o#PPWPEPNPNQ01PVPE%PEJ04RwM:tP9P9Q0@GsP{P\PGPxQ0aQ0bQ03PB%fER9,LvQ0n5FoQ04P@b6b7b8X18Q0w9DFE^18Pzb4b;b<CvPZePsO6Q0`Q1:PpQ0YQ19PhQ0xQ18P_Q0yQ17P<Q0lQ0_P^O3Q0]Q16PYQ13Q15Q0zP2P6P7O2Q0UQ0|Q0}Q0~POP>PDQ0[PQQ0{Q10PSfsRQQ11;lVQ12H05FE3q3qP1PuP5O1Ru,9KPu12U~RZP>P0PCfwRzC4PuQ0XPuPIPOP>PDQ0\10HuRuPZPOP>PDP>P0PCPzPuF5PRPSP]Q0X12E55:HPVA3JVuG;F6D=CjPKP~P4O1R~P~12UARAP>P0PCPPC4P~PIP~PQPOP>PDQ0\10H~R~PAPOP>PDP>P0PCPPP~F5PRPSP]Q0A9:HIPVA3JV~G;F6D=E>P7Q14,9KQ0XP;O1R~12UIRAP>P0PCfzRuC4P~P]P~Q0[POP>PDfyRZ10H~R~PAPOP>PDP>P0PCPuP~F5PRPSPz12E;RA9:H]PVA3JV~G;F6D=CjP1PIP:O1RI12UQR~P>P0PCf{RFC43DPIQ0[PIQ0\POP>PDPu10HIRIP~POP>PDP>P0PCPFPIF5PRPSPPQ0[Q0E5:HPVA3JVIG;F6D=PKPQP=O1RQPQ12U]RIP>P0PCf|R~C4PQQ0\PQPzPOP>PDPu10HQRQPIPOP>PDP>P0PCP~PQF5PRPSPPQ0\Q0F5:HPVA3JVQG;F6D=E>P7P]P3O1Q0[,2UQ0t3DQ0[P2O1R]PPP]PZPOP>PDQ0s10H]R]PUQ0\POP>PDP>P0PCf~RQP]F5PRPSPF12E29:HPPVA3JV]G;GYD=P1Q0\PMO1RM/<ZPOP>PDPQ10HMR]PUPzPOP>PDP>P0PCp+01@RIP]F5PRPSP~Q0G9:HZPVA3JV]G;GY9aMuPKPzPYO1RYPY12UPRzP>P0PCp+01ARMC4PYPuPYPFPOP>PDPQ10HYRYPzPOP>PDP>P0PCPMPYF5PRPSP~Q0H9:HuPVA3JVYG;F6D=E>P7PPPXO1/<FPZP[O1RZQ0sPOP>PDp+01BRP10HZRZPUPuPOP>PDP>P0PCp+01CRYPZF5PRPSPI12E[9:H~PVA3JVZG;GY3aP1PuPcO1Rc/<QPOP>PDPY10HcRcPUPFPOP>PDP>P0PCp+01DRuPcF5PRPSPMQ0sQ0I5:HPVA3JVcG;GYPKPFP^O1R^P^12U~RFP>P0PCp+01ERcC4P^PQP^PIPOP>PDPY10H^R^PFPOP>PDP>P0PCPcP^F5PRPSPMQ0J9:HQPVA3JV^G;F6D=E>P7P~PbO1/<MPOP>PDp+01FR~Q0sPgO1,0HR^PUPQPOP>PDP>P0PCp+01GRFP^F5PRPSPu12Eg9:HMPVA3JV^G;GYP1POP>PDPFPQPjO1,0HRj1wUIE8POP>PDP>P0PCp+01HRQPjF5PRPSPcQ0K9:HPPVA3JVjG;PKPIP_O1R_P_12UMRIP>P0PCp+01IRjC4P_PYP_PuPOP>PDPF10H_R_PIPOP>PDP>P0PCPjP_F5PRPSPcQ0L9:HYPVA3JV_G;F6D=E>P7POP>PDPjPMPiO1,0H1wUPE8POP>PDP>P0PCp+01KRiPPPfO1,0HRMF5PRPSPQ12Ef9:HcPVA3JVMG;P1POP>PDP>P0PCp+01LR1CGPYPmO1,0HRmPRE8PSPjPHP~Q0MPVA3JVmFZPKPuPhO1RhPh12UcRuP>P0PCp+01MRmC4PhPFPhPQPOP>PDPi10HhRhPuPOP>PDP>P0PCPmPhF5PRPSPjQ0N9:HFPVA3JVhG;F6D=E>P7POP>PDP>P0PCp+01NRhCGPcPeO1,0HPRE8PSP1PHPj12EnPVPJPVPHP~PnO1CSFZPFPrO1Rr,9K12UQRUP>P0PCp+01PRKC45DrRFp+01JRn,<rR~1<riRePOP>PDPh10HrRr%bUE8RcPOP>PDP>P0PCPKCGPrPRE8RRPSQ0O,?nRK,0HRD=l1VROPJ1mVrCuRu'7RY'7RM'7R_'7RI'7PfPFPIPgP~P_P[PePMP2PcPYPsPrPUP;O3PRPuP6PSAlmDVPSP7PJPQPpO19xVHCuXKSP7POP>P0PCQ00p+01OPmP110HnRO12EjRjPKPVPdPlPnQ0P,?iRi,97X@8P{P\PGPxp-0RlQ0:Q0:Q0=#eRd'RQ0i'n+0ERVPVPVPVPVPVPVPVQ0aDhDhRVQ0bQ0cQ0d%k<RS7Q47Q6PBPoQ07$03,i8Rp/\`,Ko,_oRQP?Po1\pt,Ko,_oRJP?PoQ0f=Fo}202o:5zoP?Po1\`t,Ko,_oRDP?Ay89},LtRu9FotFOFOQ04P@b6b7b8X18X58X=8X>8WEQ0Cg012bRR[1U<6PR[%B4/7:1U;4PR[RU1?<ARA,9<[[[[^18^58^=8^>8^ElP71@k1PnPkO1RrPhPkPmPXPbPqP|O9b4b;b<20:HOROP{P\PGPxQ0gQ0hP7PmQ0QO2b4b;b<P{P\PGPx%eTRTQ0;,RdRd'RQ0i'nRH20L8ERYQ0?#e6018Q0>#e:018YQ0<Q0:'R,RT'R'RQ0i'nRTPTPHPHPTPTPHQ0aDhDhQ0b%k;RH9QS5Q0d%k:7Q47Q6PBPo1\p},Ko,_oP?PoPJP?PoQ0fQ08,i8RT5FoQ05,i8RY,dT,Ko5zoP?PoQ0k,d`,KoP?Po1\}t,Ko,_oP?PoAy89Y,Lt=Fo`P?PoQ0m,L}=Fo`P?Q0pCoFOFOFOQ04P@b6b7b8X18X58X=8X>8X?8XH81U;6PR[RT1U:6PR[Q0D?1:;1@;aRcQ0BPR[12E3=D;=AD=L31@=a[[[[[[[^18^58^=8^>8^?8^H8P7PrPkP1P>P0PCp+01SC4RCPhPmPXPbPqPsP|Q0RPPO=b4b;b<607nRPDcPnB0C7EnR09DiWX@81?KWRi1?njRj'91?KER>/9jPNQ1=PiP>PNPNPNQ0uPKPK%PKPWPEPwM:tPjPj%PjGsP{P\PGPxPVQ0bQ0d9QS5Q0d?Q4H7Q6RHPBPo1\pY,Ko,_oP?PoPJP?Po202o=1d}`,Ko5zoP?Po1\Yt,Ko,_oP?1Lu9Ay89`,Lt5FoFOFOQ04P@b6b7b8X18X58X=8X>8X?8XEl1U<4PR[A1=4<1U:4PR[Q0E,?<9DAE[[\T[^18^58^=8^>8^?8^ElP7%BkPrPhP1PkPmPXPbPqP|O:b4b;b<CvPOPPDcPn190aX@8P{P\PGPxQ0i,ndRdPdPdPdPdPdPdPdQ0aDhDhQ0bPHPBPoPQP?PoPJP?PoQ0k,dY,KoP?PoPDP?PoAFouYP?Q0k9FouCoFOFOQ04P@b6b7b8X18X58X=8X>8X?81U<5PR[19A=Q0E=D;a[\U\c\T[^18^58^=8^>8^?8P7PrPCPhP1PmPXPbPsP|Q0RO:b4b;b<POPPDcN@06E|FVFVFVWXWWP6P7O2n2001000000121000000W3WVP6P7O2n2001000000121000000W3WUP6P7O2n2001000000121000000W3WTP6P7O2n2001000000121000000W3WSP6P7O2n2001000000121000000W3WRP6P7O2n2001000000121000000bnW^X08P:C}FVFVFVFVFVFVbPWNW_W]WkW`WQWgP6P7O2n2101000000121000000W3WbP6P7O2n2011000000121000000W3WaP6P7O2n2011000000121000000W3WeP6P7O2n2011000000121000000W3WlP6P7O2n2011000000121000000W3WYP6P7O2n2011000000121000000W3WhP6P7O2n2011000000121000000W3WiP6P7O2n2011000000121000000W3WjP6P7O2n2011000000121000000W3WdP6P7O2n2011000000121000000W3WcP6P7O2n2011000000121000000W3WmP6P7O2n2011000000121000000W3WZP6P7O2n2011000000121000000W3WsXt8Xp8Xo8Xq8WrWJWMWLWOo"). Qed.

Lemma cellsAt_tail : forall (m : word -> option byte) base c L, cellsAt SEGS m base (c :: L) -> cellsAt SEGS m base L.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBgeW ()) ["BgeW"] "h01ch11Hh21Lh34baseh41mp;1p;3p;4p;2p;5g004Oj10Tg00PEj12Tg00Pcj11Tg00QFj13Tg00:Nj14Tg00kRj3<Tg013?j4;Tg014Gj18Tg0097j27Tg00Rgj26Tg015Mj15Tg00hQj49Tg016Sj1:Tg017Yj2@Tg00Yfj2?Tg006Zj3>Tg018Vj5=Tg00G>#0#0#0R0#0#0#0#2R1#1%20#1R0#3[g00BHg00IMR2%42g00ElR3f3f2R4f1R5f0R65<2C;P2%40R0#3P3f5f4%86'7,61%56R1C9%:6,@1,?03>X02P4P5P6D=W1W2W0W3W4o"). Qed.

Lemma ex_range_dec : forall (P : Z -> Prop), (forall i, {P i} + {~ P i}) ->
  forall (n : nat) (lo : Z), {i | (lo <= i < lo + Z.of_nat n)%Z /\ P i} + {forall i, (lo <= i < lo + Z.of_nat n)%Z -> ~ P i}.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBgeW ()) ["BgeW"] "p'0h01ih14__x1h24__x2h32Hih47__arithh54__ffh68__varmaph75__with84__x3h91ni001nh:1si011sh;1xi021xh<4cstrh=2loh>3Hi0h?1Yh@4__p1hA1DhB2IHhC1NhD2N'hE2NEhF1PhG1ai031ahH1ei041ehI1mhJ1yi051pp;1p;2p;4p;6p;3p;7p;<p;Bp;8g00W1j12Tg019:R0j2OTg0074j25Tg007PR1j21Tg019ZR2j2<Tg00YFR3j14Tg0097R4j20Tg00XjR5j23Tg00bIj1?Tg00bgj4uTg009Tj2ITg01:8j6GTg01:aj4STg009nj1gTg00:Nj1fTg00iIj2WTg00:nj1bTg00igj4QTg00;Lj1aTg00;jj1`Tg00\9j2KTg004Oj1_Tg00<Uj2PTg00TPj1]Tg00nFj6\Tg00=[j2[Tg00>=j2ZTg006Zj3ATg00>ij3tTg00?Hj4sTg01;Hj3YTg00U2R6j1:Tg0054j1qTg00ZHj1JTg00cJj4VTg00@:j4UTg01;fj4RTg01<Bj3TTg003jj1pTg01<`j2oTg001<j7iTg00@Uj4LTg00mbj6hTg01=@j4jTg01=aR7j2kTg00l2l<HTg00lWlBlTg00m=l<mTg00A@j7nTg00=8j3eTg00Adj7dTg00jEj8cTf1R8f0R9#4'0p=^f2R:1389'1p=>g00BHR;/k9p=71I;9p=6g00oQR<P;P;P;P3P3f3R=P:P8g010WR>g00HCR?P9M<Hp=rP;P;P;P;P;P;P4P9P8P:P4P=f4R4f5R@f6RAf7RBf8RCf9RDMBlp=FP;P;P5PBP5PAP@P4P=P:P8P9M<mp=EP;P8g00BfP9CLp=DP8g00CMR5g00ClREPEg00DLRFP9g00DlFnp=9Ae;89p=;P;P8g00njP9CLp=CP:P5PEPEPFP8P9Fdp=BP=P5PEPEPFP:P8P9Gcp=@15:8/19p=X154=%49,08,3:'1p=8P<P<P;P;P6P3P3P=g01>=P:P8P9M<Hp=NP<P;P;P;P3P3P@P4P=P:P8P9M<Hp=M154=1089,3:'1p==p-0R3\;P8P9O1R6%26'O^0;1589R61^8:7>9RGP@P9O1RH'1X0;#7PAP8O1RI#2RJ\G^0;'<^=;RGX9<%4>R>,089>69R6P4P9O1RK'1X0;#7P@P8O1#2\6^0;15:8RL10:>RM,38RN'110:?9>L8ROPLPNPLP9X;;RNP?O1RP,0:RQ,38%?LPN1389#?XJ;X;;RLP8P8%68PMPQPNPNPNP;P;g012>1089Cu#6XI;X9;RQP:P:%6:P>PPPNPN%49#6X;<RP1I;?CrM:FGEEGP9CSPOg00HaRO#gR>%fOROP;1W;:RMP8%b;CQRR%a;RS%`;RTg00G>RU,K;RV%_U,K;RW'D,9TRX1P;?RY,;V,CW,9T5BT%]ERZPTP5PEPEPFP4E\C@1[TFR[P9P:g00ELR\g00GcR]'I1Z9:=A\]dAt;?8CsR]b5b6b7X1;X2;X@31598R\109?7>8P=[^1;^2;^@3P9PBP=O1#2P=P4P8O4b4b>X36X0;3YX=;PK%2H,OHP0PIPJ%:@RJ#4RI,0=RH,399X=9RKPCP9O1'1X0;#7PDP8O1#2\K^0;'<P9PBP:O1RKP4P9P9P4%:AD8R6PDP9O1R3'1X0;R^#7f:R_P8O1#2R`\6^0;P;P^P=15==R^13=HR6'1RaPCP=O1Pa%4@Ra%qURb'0Rc,0=Rd,3=Re,1^P^P6P^Pe%?^PNPLP=P=%6=R^PHPdPNPNPNPQP=P=P^PIPcPNPNPPPJPc109bRcX;;RJP@Pa%6aCNEMM:FGEEG%J@15?aP>POPRPSPT1DYW,9TPZ1DVV,9T1P;bRY,;W,;V,CV,9T5BTC@P[P]b5b6b7X1;X2;15?8P8P8P8P810:bRRD=[^1;^2;P9%4BRaP@P8O3b4b<CVP9CUCR3TW?P9O1%2KP410=bRKO1104bRIP9P9PIPAD8RI/13X0;#7P`\I^0;'<P210@bR2P9P9P2PaD=RaP_P9O1'1X0;#7f;R2P8O1#2\a^0;PAP9P9PA%:CD8RaP2P9O1RI'1X0;#7f<R`P8O1#2R3\a^0;'<P910AbRAP9P9PAPCD8RA/1IX0;#7P7P;10BbR7P9P9P7PDD8P`P9O1R7'1X0;PCP9P9PC%:_D8RIf=RaP9O1'1X0;#7f>R^P8O1#2\I^0;'<P910DbRIP9P9PIP2D8P^P9O1'1P110_bR1P8P8P1P`D8f?R1P8O1P`P9P9P`%:^D8RIfARdP9O1'1X0;#7fBRHP8O1#2Re\I^0;'<P910`bR`P=P=P`%4^R`D=PHP4O1P1P9P9P1%:dD8RdfDP9O1'1X0;R6#7fEP8O1#2\d^0;P;P6P@15^@R6f@Rd#:Rf#4Rg,0^Rh,3@Ri'1RjfCP@O1Pj%4dRj/0bRk,0^Rl,3@Rm,16P6PiP6Pm%?6PNPLP@P@%6@PhPlPNPNPNPQP^P^%6^PgPkPNPNPPPfPkPJPdPj%6jCNEMM:FGEEG%Jd15?jP>POP;PMP81W;=CQRMPSPT1;VYRk/DW,9T%pU,K;RU,;k,CW,9T5BTRkPZ1;UY,;V,CW,9T9BTXRXC@P[P]b5b6b7X1;X2;X8;PcP8P8PcP:D=P8P:P:P8PKD=[^1;^2;^8;P9%4HPBPdP=O4b4b<CVP9CUCR3TW?W3P8P9O2n2001000000121000000WGX0;P8P9O2n2001101000121102103W:P9O1P3\A^0;PBP9P9PB%:DD8RA/17X0;#7PaP8O1#2\A^0;1o8CAA;8CRC%2C'OP0AA;:DR0%20P1P=O1#2P9AA;=_R_P;P2Pe^3IX0;%:aRI#4Re,02R1,329X22PDW3P4P9P=FiWHP9O1%2_P@P41524R@1341R_'1%4aRD/0b,029>@4RbP@P_P@PNPJPDO1R_O1R0,02RC,34%?@PNPLP4P4%64P1PCPNPNPNPQP2P2%62PeP0PNPNPPPIP_PJPaPD%6DCNEMM:FGEEGP=CSPb%J^15?`P>POPMPSPTPXPZPTPTP5PEPEPFP;PWg0100PVCL,9TEhPZPkC@C@P[P]b5b6b7X1;X2;X8;109R9>\8AA;:8g012b[PRP=P=PRP4D=[[^1;^2;^8;P9PjPBP^P:P=O5b4b<b>O2WEP9O1n200110100021010411100b:X3AX0;3YWDP9O1n200110100021110111100b:WCP9O1n200110100021110511100b:X=;XBGX9<P9CjX9<WAWFo"). Qed.

(* [comment removed for export] *)
Lemma fs_notin_ge : forall r : reg, In (u r) fs_list -> r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBgeW ()) ["BgeW"] "p'0h01Hh12H0h21eh32Hrh41ri001pi011zp;1p;2p;3p;7p;4p;6g004Oj15Tg003jj16Tg00PEj1BTg00Pcj1ATg00\\j29Tg0054j14Tg01>aj3;Tg006Zj38Tg00W1j1:Tg007Pj2?Tg01?Dj22Tg01?^j2ETg001<j7<Tg00@:j4>Tg01@=j3DTg000`j6CTg01@Tj6@Tg00BHR0f0R1g01A03Dp=7f1R2=801p=0P0f3R3f2R4g01B7R5P2P1ECp=1P3g012bR6P6P4P2P1E@p==f4P3P6P4P2P1E@p=3g00G>R3#5R7#6R8#BR9#AR:1991#7R;%68R<#4R==;95R>98:2R?#:R@%63R3#5RA#5RB#4RC=;95RD98:2RE#:RF%6ARA#4RG=;95RH98:2RI#:RJ%63R3#5#4RK=;95RL98:2RM#:RN%63#4R3=;95R598:2RO#:RP'?RQ'?RR'?P:P>P6^3;X4:R;199>#7%57R7#5#4R>/0=RS%67R7#4RT/0=RU%57#4RV/0=RW%67#4R7/0=RX%58R8#5#4RY/0=RZ%68#4R8/0=R[%5<#4R\/0=R]%6<#4R</0=R^%5B#4R_/0=R`%6B#4RB/0=Ra%5A#4Rb/0=Rc%6A#4RA/0=Rd/26Re'2Rf'2Rg'2Rh'2Ri'2Rj'2Rk'2Rl'2Rm'2Rn'2RoP>P0p-0RpP1P6g01BSRqPpP1P6g0116RrP6n011000003100001000000RsP6n011010003001010010100X20RtP=P1C1P61E61Rub1P6eX0SPUPnPTP0PpP1P6PqPpP1PsP6P6n011000003101001010000RSP6n011010003001010010100X20RvP=P1C1P6Pub0P6eX1UPWPmPVPtP=P1C1P6Pub1P6eX0WPXPlP7P0PpP1P6PqPpP1PqPpP1PqPpP1P6PsP6n011000003101001010000RsP6P6n011000003101001010000RWP6P6n011000003101001010000P6n011010003001010010100X20P=P1C1P6Pub0P6eX1XPZPkPYPtP=P1C1P6Pub1P6eX0ZP[PjP8PvP=P1C1P6Pub0P6eX1[P]PiP\PtP=P1C1P6Pub1P6eX0]P^PhP<P0PpP1P6PqPpP1PqPpP1PqPpP1PrP6P6n011000003100001000000RrP6P6n011000003101001010000R]P6P6n011000003101001010000P6n011010003001010010100X20P=P1C1P6Pub0P6eX1^P`PgP_PtP=P1C1P6Pub1P6eX0`PaPfPBPvP=P1C1P6Pub0P6eX1aPcPePbPtP=P1C1P6Pub1P6eX0cPdPAP0PpP1P6PqPpP1PqPpP1PqPpP1P6PrP6n011000003101001010000RcP6P6n011000003101001010000P6P6n011000003101001010000P6n011010003001010010100X20P=P1C1P6Pub0P6eX1dPuX16RdP1C=X0eP1D3X1fP1D3X0gP1D3X1hP1D3X0iP1D3X1jP1D3X0kP1D3X1lP1D3X0mP1D3X1nP1D3X0oP1D3W3P4P1P2F<X0?P@ePFPRP:PDP;199D#710>CRD10TCRR10VCR@107CR?10YCRo108CRn10\CRm10<CRl10_CRk10BCRj10bCRi10ACRh/26Rg'2Rf'2Re'2R='2Ra'2R`'2R^'2R['2RZ'2RX'2RUP>P0PpP1P6PqPpP1P6PsP6n011000003101001010000P6n011010003001010010100X20RwPCP1C1P6Pub1P6eX0DPRPXPTP0PpP1P6PrP6n011010003001010010100X20RrPCP1C1P6Pub0P6eX1RP@PZPVP0PpP1P6PcP6n011010003001010010100X20RcPCP1C1P6Pub1P6eX0@P?P[P7PrPCP1C1P6Pub0P6eX1?PoP^PYP0PpP1P6PqPpP1P6PqPpP1P6PSP6n011000003101001010000R?P6n011000003101001010000P6n011010003001010010100X20PCP1C1P6Pub1P6eX0oPnP`P8PrPCP1C1P6Pub0P6eX1nPmPaP\PcPCP1C1P6Pub1P6eX0mPlP=P<PrPCP1C1P6Pub0P6eX1lPkPeP_PwPCP1C1P6Pub1P6eX0kPjPfPBPrPCP1C1P6Pub0P6eX1jPiPgPbPcPCP1C1P6Pub1P6eX0iPhPAPrPCP1C1P6Pub0P6eX1hPdP1C=X0gP1D3X1fP1D3X0eP1D3X1=P1D3X0aP1D3X1`P1D3X0^P1D3X1[P1D3X0ZP1D3X1XP1D3X0UP1D3W3P4P1P2F<X0EPFePJPQP:PHP;199H#710>GRH10TGRQ10VGRF107GRE10YGRU108GRX10\GRZ10<GR[10_GR^10BGR`10bGRa10AGR=/26Re'2Rf'2Rg'2Rh'2RC'2Ri'2Rc'2Rj'2Rk'2Rw'2RlP>PtPGP1C1P6Pub1P6eX0HPQPwPTP0PpP1P6PWP6n011010003001010010100X20RWPGP1C1P6Pub0P6eX1QPFPkPVPtPGP1C1P6Pub1P6eX0FPEPjP7P0PpP1P6P]P6n011010003001010010100X20R]PGP1C1P6Pub0P6eX1EPUPcPYPtPGP1C1P6Pub1P6eX0UPXPiP8P0PpP1P6PqPpP1P?P6P6n011000003101001010000P6n011010003001010010100X20PGP1C1P6Pub0P6eX1XPZPCP\PtPGP1C1P6Pub1P6eX0ZP[PhP<P]PGP1C1P6Pub0P6eX1[P^PgP_PtPGP1C1P6Pub1P6eX0^P`PfPBPWPGP1C1P6Pub0P6eX1`PaPePbPtPGP1C1P6Pub1P6eX0aP=PAP]PGP1C1P6Pub0P6eX1=PdP1C=X0eP1D3X1fP1D3X0gP1D3X1hP1D3X0CP1D3X1iP1D3X0cP1D3X1jP1D3X0kP1D3X1wP1D3X0lP1D3W3P4P1P2F<X0IPJePNPPP:PLP;199L#710>KRL10TKRJ10VKRI107KRl10YKRw108KRk10\KRj10<KRc10_KRi10BKRC10bKRh10AKRg/26Rf'2Re'2R='2RG'2R]'2Ra'2R`'2RW'2R^'2R['2RZP>P0PpP1P6PsP6n011010003001010010100X20RsPKP1C1P6Pub1P6eX0LPJP[PTPrPKP1C1P6Pub0P6eX1JPIP^PVP0PpP1P6P?P6n011010003001010010100X20R?PKP1C1P6Pub1P6eX0IPlPWP7PrPKP1C1P6Pub0P6eX1lPwP`PYPsPKP1C1P6Pub1P6eX0wPkPaP8PrPKP1C1P6Pub0P6eX1kPjP]P\P0PpP1P6PqPpP1P6PqPpP1PSP6P6n011000003101001010000RSP6n011000003101001010000P6n011010003001010010100X20PKP1C1P6Pub1P6eX0jPcPGP<PrPKP1C1P6Pub0P6eX1cPiP=P_PsPKP1C1P6Pub1P6eX0iPCPePBPrPKP1C1P6Pub0P6eX1CPhPfPbP?PKP1C1P6Pub1P6eX0hPgPAPrPKP1C1P6Pub0P6eX1gPdP1C=X0fP1D3X1eP1D3X0=P1D3X1GP1D3X0]P1D3X1aP1D3X0`P1D3X1WP1D3X0^P1D3X1[P1D3X0ZP1D3W3P4P1P2F<X0MPNeP:P5P;1995#710>3R510T3R910V3R;1073R:10Y3RN1083RM10\3RZ10<3R[10_3R^10B3RW10b3R`10A3Ra/26R]'2RG'2R='2Re'2Rf'2Rg'2RK'2Rr'2Rh'2R?'2RCP>PtP3P1C1P6Pub1P6eX05P9P?PTPvP3P1C1P6Pub0P6eX19P;PhPVPtP3P1C1P6Pub1P6eX0;P:PrP7P0PpP1P6PSP6n011010003001010010100X20R7P3P1C1P6Pub0P6eX1:PNPKPYPtP3P1C1P6Pub1P6eX0NPMPgP8PvP3P1C1P6Pub0P6eX1MPZPfP\PtP3P1C1P6Pub1P6eX0ZP[PeP<P0PpP1P6PqPpP1PSP6P6n011000003101001010000P6n011010003001010010100X20P3P1C1P6Pub0P6eX1[P^P=P_PtP3P1C1P6Pub1P6eX0^PWPGPBPvP3P1C1P6Pub0P6eX1WP`P]PbPtP3P1C1P6Pub1P6eX0`PaPAP7P3P1C1P6Pub0P6eX1aPdP1C=X0]P1D3X1GP1D3X0=P1D3X1eP1D3X0fP1D3X1gP1D3X0KP1D3X1rP1D3X0hP1D3X1?P1D3X0CP1D3W3P4P1P2F<X0OPPeC>C>C>C>W3W4o"). Qed.

(* [comment removed for export] *)
Definition ge_saved (regs : bvmap 5 word) : list cell :=
  [(136%Z, 8%nat, u (getr regs 1)); (128%Z, 8%nat, u (getr regs 8)); (120%Z, 8%nat, u (getr regs 9)); (112%Z, 8%nat, u (getr regs 18));
   (104%Z, 8%nat, u (getr regs 19)); (96%Z, 8%nat, u (getr regs 20)); (88%Z, 8%nat, u (getr regs 21)); (80%Z, 8%nat, u (getr regs 22));
   (72%Z, 8%nat, u (getr regs 23)); (64%Z, 8%nat, u (getr regs 24)); (56%Z, 8%nat, u (getr regs 25)); (48%Z, 8%nat, u (getr regs 26))].

Lemma bge_m16_8 : forall z : Z, (z mod 16 = 0)%Z -> (z mod 8 = 0)%Z.
Proof.
  intros z H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
  destruct H as [k Hk]. exists (2 * k)%Z. lia.
Qed.

Lemma bge_m16_4 : forall z : Z, (z mod 16 = 0)%Z -> (z mod 4 = 0)%Z.
Proof.
  intros z H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
  destruct H as [k Hk]. exists (4 * k)%Z. lia.
Qed.

Lemma bge_m16_sub : forall s k : Z, (s mod 16 = 0)%Z -> (k mod 16 = 0)%Z -> ((s - k) mod 16 = 0)%Z.
Proof. intros s k Hs Hk. rewrite Zminus_mod, Hs, Hk. reflexivity. Qed.

Lemma bge_m8_sub : forall s k : Z, (s mod 8 = 0)%Z -> (k mod 8 = 0)%Z -> ((s - k) mod 8 = 0)%Z.
Proof. intros s k Hs Hk. rewrite Zminus_mod, Hs, Hk. reflexivity. Qed.

Lemma bge_clr : forall C A m md (lo hi : Z), W C A m md ->
  (exists clo chi, In (clo, chi) ll_clr /\ (clo <= lo)%Z /\ (hi <= chi)%Z) -> (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z ->
  forall j, (lo <= j < hi)%Z -> m (Z_to_bv 64 j) = None.
Proof.
  intros C A m md lo hi HW (clo & chi & I & L1 & L2) H0 H1.
  exact (exW_clr_None C A m md lo hi clo chi HW I L1 L2 H0 H1).
Qed.

Ltac bge_clr HW :=
  apply (bge_clr _ _ _ _ _ _ HW); [cbv [ll_clr LLU16];
    first [ (do 2 eexists; split; [left; reflexivity | split; lia])
          | (do 2 eexists; split; [right; left; reflexivity | split; lia])
          | (do 2 eexists; split; [right; right; left; reflexivity | split; lia]) ] | lia | lia].

Lemma bge_rz_pc : forall (fx : FPState) regs (pc pc' : word) (m : word -> option byte) md (S : TSet),
  realizes SEGS (mkCfg (@mkst fx regs pc m al_rom) md) S -> pc' = pc -> realizes SEGS (mkCfg (@mkst fx regs pc' m al_rom) md) S.
Proof. intros fx regs pc pc' m md S H E. subst pc'. exact H. Qed.

Lemma bge_reach_pc : forall (fx : FPState) regs (pc pc' : word) (m : word -> option byte) (P : machine_state -> Prop),
  reach SEGS (@mkst fx regs pc m al_rom) P -> pc' = pc -> reach SEGS (@mkst fx regs pc' m al_rom) P.
Proof. intros fx regs pc pc' m P H E. subst pc'. exact H. Qed.

Lemma bge_px_livk : forall A (m m' : word -> option byte) p v, PIXat m p v -> LIVK A m m' -> live A (Z_to_bv 64 p) = Some 64%Z ->
  PIXat m' p v.
Proof.
  intros A m m' p v PX LK L. pose proof PX as (P0 & P64 & _).
  apply (PIXat_frame m m' p v PX). intros x Hx.
  pose proof (LK (Z_to_bv 64 p) 64%Z (u x - p)%Z L ltac:(lia)) as E.
  unfold at_ in E. rewrite u_Z2bv in E by lia. replace (p + (u x - p))%Z with (u x) in E by lia.
  rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

Lemma bge_kvals_eq : forall (m m' : word -> option byte) h w rows f, kvals m h w rows f ->
  (forall i j, (0 <= i < h)%Z -> (0 <= j < w)%Z ->
     rdn SEGS m' (Z_to_bv 64 (rows i + 4 * j)) 4 = rdn SEGS m (Z_to_bv 64 (rows i + 4 * j)) 4) ->
  kvals m' h w rows f.
Proof. intros m m' h w rows f KV E i j Hi Hj. rewrite (E i j Hi Hj). exact (KV i j Hi Hj). Qed.

Lemma bge_kvals_livk : forall A (m m' : word -> option byte) h w rows f, kvals m h w rows f -> LIVK A m m' -> (0 <= w)%Z ->
  (forall i, (0 <= i < h)%Z -> live A (Z_to_bv 64 (rows i)) = Some (4 * w)%Z /\ (0 <= rows i)%Z /\ (rows i + 4 * w < 2 ^ 64)%Z) ->
  kvals m' h w rows f.
Proof.
  intros A m m' h w rows f KV LK Hw R. apply (bge_kvals_eq m m' h w rows f KV). intros i j Hi Hj.
  destruct (R i Hi) as (L & P0 & P1).
  apply (livk_rdn A m m' (rows i) (4 * w) (rows i + 4 * j) 4 LK L); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma bge_kern_sub : forall C A A' (m : word -> option byte) kel arr h w rows, kern C A A' m kel arr h w rows -> sub_live A A'.
Proof.
  intros C A A' m kel arr h w rows K q k E.
  destruct K as (_ & _ & _ & _ & LK & _ & _ & _ & _ & _ & _ & _ & _ & _ & LA & _ & ROWS & _ & REST).
  rewrite REST; [exact E | | |].
  - intros ->. rewrite LK in E. discriminate.
  - intros ->. rewrite LA in E. discriminate.
  - intros i Hi ->. destruct (ROWS i Hi) as (_ & _ & _ & _ & _ & _ & LR & _). rewrite LR in E. discriminate.
Qed.

Definition ge_sv (s : Z) (regs : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, getr regs 1); ((s - 16)%Z, getr regs 8); ((s - 24)%Z, getr regs 9); ((s - 32)%Z, getr regs 18);
   ((s - 40)%Z, getr regs 19); ((s - 48)%Z, getr regs 20); ((s - 56)%Z, getr regs 21); ((s - 64)%Z, getr regs 22);
   ((s - 72)%Z, getr regs 23); ((s - 80)%Z, getr regs 24); ((s - 88)%Z, getr regs 25); ((s - 96)%Z, getr regs 26);
   ((s - 104)%Z, getr regs 27)].

Ltac bge_fa :=
  apply Forall_forall; let av := fresh "av" in let Hav := fresh "Hav" in intros av Hav; cbn [In ge_sv] in Hav;
  repeat (destruct Hav as [<-|Hav]; [cbn [fst]; try unfold LSF; lia|]); destruct Hav.

Lemma bge_rinv_out : forall R (m m' : word -> option byte) (lo hi : Z), rinv R m m' ->
  (forall r, In r R -> (lo <= fst r)%Z /\ (fst r + snd r <= hi)%Z) -> forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x.
Proof.
  intros R m m' lo hi [_ RI] HR x Hx. apply RI. intros r Hr Hin. apply Hx. destruct (HR r Hr) as [A1 A2].
  unfold inreg in Hin. lia.
Qed.

Lemma bge_live_split : forall (X Y : AS) (kel arr : Z) (rows : Z -> Z),
  live X (Z_to_bv 64 kel) = live Y (Z_to_bv 64 kel) -> live X (Z_to_bv 64 arr) = live Y (Z_to_bv 64 arr) ->
  (forall i, (0 <= i < 41)%Z -> live X (Z_to_bv 64 (rows i)) = live Y (Z_to_bv 64 (rows i))) ->
  (forall q, q <> Z_to_bv 64 kel -> q <> Z_to_bv 64 arr -> (forall i, (0 <= i < 41)%Z -> q <> Z_to_bv 64 (rows i)) -> live X q = live Y q) ->
  forall q, live X q = live Y q.
Proof.
  intros X Y kel arr rows Ek Ea Er Eo q.
  destruct (@bv_eq_dec 64 q (Z_to_bv 64 kel)) as [->|Nk]; [exact Ek|].
  destruct (@bv_eq_dec 64 q (Z_to_bv 64 arr)) as [->|Na]; [exact Ea|].
  destruct (ex_range_dec (fun i => q = Z_to_bv 64 (rows i)) (fun i => @bv_eq_dec 64 q (Z_to_bv 64 (rows i))) 41 0) as [(i & Hi & ->) | NR].
  - apply Er. change (Z.of_nat 41) with 41%Z in Hi. lia.
  - apply Eo; [exact Nk | exact Na |]. intros i Hi E. apply (NR i); [change (Z.of_nat 41) with 41%Z; lia | exact E].
Qed.

Lemma bge_wpl8 : forall w : Z, (0 <= w)%Z -> (w <= 4 * wpl_of w 8)%Z.
Proof.
  intros w Hw. unfold wpl_of.
  pose proof (Z.mod_pos_bound (w * 8 + 31) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (w * 8 + 31) 32 ltac:(lia)) as D. lia.
Qed.

Lemma bge_rd1 : forall C A (m : word -> option byte) md (p n a : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n ->
  (0 <= p)%Z -> (p + n < 2 ^ 64)%Z -> (p <= a < p + n)%Z -> exists b, rdn SEGS m (Z_to_bv 64 a) 1 = Some [b].
Proof.
  intros C A m md p n a CK HW L P0 P1 Ha.
  destruct (blk_byte C A m md (Z_to_bv 64 p) n (Z_to_bv 64 a) CK HW L ltac:(rewrite !u_Z2bv by lia; lia)) as (_ & D & _).
  cbn [rdn]. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; exact (D eq_refl)].
Qed.

Lemma bge_none_sub : forall (X Y : AS) (q : word), sub_live X Y -> live Y q = None -> live X q = None.
Proof. intros X Y q SB N. destruct (live X q) as [k|] eqn:E; [|reflexivity]. rewrite (SB q k E) in N. discriminate. Qed.

Lemma bge_neq : forall (X : AS) (p q : word) k, live X p = None -> live X q = Some k -> p <> q.
Proof. intros X p q k Np Lq E. subst q. rewrite Np in Lq. discriminate. Qed.

Lemma bge_cellsZ_rdn : forall (m m' : word -> option byte) (l : list (Z * word)),
  (forall av, In av l -> rdn SEGS m' (Z_to_bv 64 (fst av)) 8 = rdn SEGS m (Z_to_bv 64 (fst av)) 8) -> cellsZ m l -> cellsZ m' l.
Proof.
  intros m m' l. induction l as [|[a v] t IH]; intros E CZ; [exact I|].
  cbn [cellsZ] in CZ |- *. destruct CZ as [C1 C2]. split.
  - pose proof (E (a, v) (or_introl eq_refl)) as Ea. cbn [fst] in Ea. rewrite Ea. exact C1.
  - apply IH; [intros av Hav; apply E; right; exact Hav | exact C2].
Qed.

Lemma fs_notin_10 : forall r : reg, In (u r) fs_list -> r <> 10%bv.
Proof. intros r H E. subst r. vm_compute in H. repeat (destruct H as [H|H]; [discriminate H|]). exact H. Qed.

Lemma bgw_rinv_out : forall (m m' : word -> option byte) (lo hi : Z), mem_grows m m' ->
  (forall a : word, ~ (lo <= u a < hi)%Z -> m' a = m a) -> rinv [(lo, (hi - lo)%Z)] m m'.
Proof.
  intros m m' lo hi G O. split; [exact G|]. intros a Ha. apply O. intros X.
  apply (Ha (lo, (hi - lo)%Z)); [left; reflexivity | unfold inreg; cbn [fst snd]; lia].
Qed.

Lemma bgw_rdn_keep : forall (m m' : word -> option byte) (lo hi z : Z) (n : nat), mem_grows m m' ->
  (forall a : word, ~ (lo <= u a < hi)%Z -> m' a = m a) -> (0 <= z)%Z -> (z + Z.of_nat n <= 2 ^ 64)%Z ->
  (hi <= z \/ z + Z.of_nat n <= lo)%Z -> rdn SEGS m' (Z_to_bv 64 z) n = rdn SEGS m (Z_to_bv 64 z) n.
Proof.
  intros m m' lo hi z n G O Hz Hzn D.
  apply (rinv_rdn SEGS [(lo, (hi - lo)%Z)] m m' z n (bgw_rinv_out m m' lo hi G O) Hz Hzn).
  intros r [<-|[]]. cbn [fst snd]. lia.
Qed.

Lemma bgw_rinv_frame : forall (m m' : word -> option byte) (lo n : Z) (x : word), rinv [(lo, n)] m m' -> ~ (lo <= u x < lo + n)%Z -> m' x = m x.
Proof. intros m m' lo n x [_ R] Hx. apply R. intros r [<-|[]]. exact Hx. Qed.

Lemma bgw_m16_8 : forall z : Z, (z mod 16 = 0)%Z -> (z mod 8 = 0)%Z.
Proof. intros z H. pose proof (mod16_plus_mod8 z 0 H eq_refl) as E. rewrite Z.add_0_r in E. exact E. Qed.

Lemma bge_case_w : forall fr cs C A m md regs (s pixs w h datas skel arrs rkel arrr : Z) (rowss rowsr : Z -> Z) (ret : word) (S : TSet),
  (w <= 82 \/ h <= 82)%Z ->
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BGE_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 skel -> getr regs 12 = Z_to_bv 64 rkel ->
  PIXat m pixs (hdv w h 8 0 datas) -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 8 * h))%Z ->
  kobj C A m skel arrs 41 41 rowss -> korg m skel 20 20 -> kobj C A m rkel arrr 1 256 rowsr ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_bge <= kR)%Z -> (RB_bge w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 0 -> (forall q, live A' q = live A q) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bge) (bR - RB_bge w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  (forall fr' cs' A' m' vm' regs' (pixd datad : Z), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pixd -> pixr_new C A A' m' pixd datad (set_data (pix_hdr w h 8) datad) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bge) (bR - RB_bge w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3ad78) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pixs w h datas skel arrs rkel arrr rowss rowsr ret S Hwh CK HW FZ H2 Hs16 Hslo Hshi H1 Hret H4
    H10 H11 H12 PX HD Hw1 Hh1 Lp Ld KOs KGs KOr kR bR AR HkR HbR K1 K2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (LSFv : LSF = 3376%Z) by reflexivity.
  unfold BGE_STACK, AMB_STACK in Hslo.
  pose proof HD as (DV & Hw2 & Hh2 & Hsz).
  pose proof PX as (Hp0 & Hp64 & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  pose proof KOs as (Ks1 & Ks2 & Ks3 & Ks4 & Ks5 & Ks6 & _).
  pose proof KOr as (Kr1 & Kr2 & Kr3 & _).
  destruct (blk_range C A m md (Z_to_bv 64 skel) 24 CK HW Ks3 ltac:(lia)) as [Gks _]. rewrite u_Z2bv in Gks by lia.
  destruct (blk_range C A m md (Z_to_bv 64 rkel) 24 CK HW Kr3 ltac:(lia)) as [Gkr _]. rewrite u_Z2bv in Gkr by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ks3) as (_ & ALk & _). rewrite u_Z2bv in ALk by lia.
  pose proof (bgw_m16_8 _ ALp) as ALp8. pose proof (bgw_m16_8 _ ALk) as ALk8.
  pose proof (PIX_rd_w SEGS m pixs _ PX) as RDw. pose proof (PIX_rd_h SEGS m pixs _ PX) as RDh.
  pose proof (PIX_rd_d SEGS m pixs _ PX) as RDd. cbn [p_w p_h p_d hdv] in RDw, RDh, RDd.
  pose proof (W_sok_win C A m md (s - 176) 176 CK HW ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SOK.
  assert (RKB : (RK_pixcopy <= RK_bge)%Z) by (unfold RK_bge, RK_kern, RK_pixcopy, RK_pix, RK_cmapcopy; lia).
  assert (RBB : (RB_pixT (4 * (wpl_of w 8 * h)) + RB_cmapT 0 <= RB_bge w h)%Z).
  { assert (RBP : forall n, (0 <= RB_pixT n)%Z) by (intros n; unfold RB_pixT, RB_hdrT; lia).
    assert (RBK : (0 <= RB_kernS 41 41)%Z).
    { unfold RB_kernS. pose proof (alloc_margin_ge 24 ltac:(lia)). pose proof (alloc_margin_ge (41 * 8)%Z ltac:(lia)).
      pose proof (alloc_margin_ge (41 * 4)%Z ltac:(lia)). lia. }
    replace (RB_cmapT 0) with 0%Z by reflexivity.
    pose proof (RBP (4 * (wpl_of (w + 41) 8 * (h + 41)))%Z). unfold RB_bge. lia. }
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | |].
  { destruct (Z_le_gt_dec w 82) as [Hw82|Hw82].
    - apply (ge_Aw al_rom (mkFP fr cs) regs m s pixs skel rkel w h).
      all: first [ assumption
                 | (let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply (w_clr _ _ _ _ HW);
                    rewrite u_Z2bv by lia; cbv [inZs inZ fst snd ll_clr LLU16]; lia)
                 | lia ].
    - apply (ge_Ah al_rom (mkFP fr cs) regs m s pixs skel rkel w h).
      all: first [ assumption
                 | (let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply (w_clr _ _ _ _ HW);
                    rewrite u_Z2bv by lia; cbv [inZs inZ fst snd ll_clr LLU16]; lia)
                 | lia ]. }
  intros fin (r1 & M1 & -> & RI1 & C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27 & CW & CH &
              Q1 & Q2 & Q9 & Q10 & Q11 & AG1).
  destruct (rinv_WP2 C A A m md M1 [((s - 176)%Z, 176%Z)] s CK HW (sub_live_refl A) Hshi RI1
              ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])) as [HW1 PM1].
  replace (Z_to_bv 64 0x17e28) with (0x17e28 : word) by (apply bv_eq; reflexivity).
  apply (lept_stderr1_W (fx := mkFP fr cs) C A M1 md r1 (s - 176) 69472 73628 85 21 (Z_to_bv 64 0x3aff4) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 ltac:(apply fmts1_16; cbn [In]; repeat (first [left; reflexivity | right])) str_ge_fmtW str_ge_proc).
  intros m2 r2 HW2 OUT2 GR2 CS2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 176)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 pixs) by (csr; reflexivity).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW2) | apply (ge_W2 al_rom (mkFP fr cs) r2 m2 s pixs ltac:(lia) ltac:(lia) E2 E9) |].
  intros fin (r3 & M3 & -> & -> & R1 & R2 & R10 & R11 & AG3).
  replace (Z_to_bv 64 0x1a314) with (0x1a314 : word) by (apply bv_eq; reflexivity).
  assert (E4 : getr r3 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  assert (PX2 : PIXat m2 pixs (hdv w h 8 0 datas)).
  { apply (PIXat_frame M1); [apply (PIXat_frame m); [exact PX|] |].
    - intros x Hx. apply (bgw_rinv_frame m M1 (s - 176) 176 x RI1). lia.
    - intros x Hx. apply OUT2. lia. }
  apply (pixCopy_szT_W (fx := mkFP fr cs) C A m2 md r3 (s - 176) pixs w h 8 0 datas (CMAPV 0 0 0 0 0) (Z_to_bv 64 0x3b000) S CK HW2 R2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) R1 ltac:(red; apply bv_eq; reflexivity)
           E4 R10 R11 PX2 HD Hw1 Hh1 Lp Ld (or_introl eq_refl) kR bR AR ltac:(lia) ltac:(lia)).
  unfold TK. intros A1 m4 vm1 r4 HW4 CS4 PM4 OUT4 RM4.
  assert (F2 : getr r4 2 = Z_to_bv 64 (s - 176)) by (csr; reflexivity).
  assert (K : forall (z : Z) (n : nat), (s - 176 <= z)%Z -> (z + Z.of_nat n <= s)%Z -> rdn SEGS m4 (Z_to_bv 64 z) n = rdn SEGS M1 (Z_to_bv 64 z) n).
  { intros z n Z1 Z2. rewrite (FRM_rdn16 C (s - 176) m2 m4 z n CK (proj1 PM4)) by lia.
    apply (bgw_rdn_keep M1 m2 (s - 176 - LSF) (s - 176) z n GR2 OUT2); lia. }
  eapply rz_reach; [exact (w_pure _ _ _ _ HW4) | |].
  { apply (ge_Xcp al_rom (mkFP fr cs) r4 m4 s (u (getr r4 10)) ret (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)
             (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
             (getr regs 27)).
    all: first [ assumption | exact (bv_unsigned_in_range 64 (getr r4 10)) | (symmetry; apply Z_to_bv_bv_unsigned)
               | (rewrite K; [assumption | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]) | lia ]. }
  intros fin (r5 & M5 & -> & -> & X2 & X10 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27 & AG5).
  assert (CSK : cs_kept regs r5).
  { apply cs_kept_of_rest; [rewrite X2, H2; reflexivity | exact X8 | exact X9 |].
    intros r Hr. cbn [In cs_rest] in Hr.
    repeat (destruct Hr as [<-|Hr];
            [first [exact X18 | exact X19 | exact X20 | exact X21 | exact X22 | exact X23 | exact X24 | exact X25 | exact X26
                   | exact X27 | (csr; reflexivity)]|]).
    destruct Hr. }
  assert (PMM : POSTM C A s m m4).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans.
    + eapply (POSTM_range C A M1 md m2); [exact CK | exact HW1 | exact OUT2 | lia | lia | lia].
    + eapply POSTM_mono; [|exact PM4]. lia. }
  assert (RMM : aroom A1 vm1 (kR - RK_bge) (bR - RB_bge w h)) by (apply (aroom_mono _ _ _ _ _ _ RM4); lia).
  destruct OUT4 as [[Z10 LV] | (pixd & cd & data & P10 & PT)].
  - apply (K1 fr cs A1 m4 vm1 r5 HW4 FZ CSK PMM);
      [rewrite X10, Z_to_bv_bv_unsigned; exact Z10 | exact LV | intros r _; reflexivity | exact RMM].
  - apply (K2 fr cs A1 m4 vm1 r5 pixd data HW4 FZ CSK PMM);
      [rewrite X10, Z_to_bv_bv_unsigned; exact P10 | | intros r _; reflexivity | exact RMM].
    destruct PT as (Gp & Tp & Ap & Gd & Td & Ad & NE & L1 & L2 & L3 & L4 & L5 & L6 & PXd & CR).
    destruct CR as [[-> KEEP] | (ad & CMOK & _)];
      [| exfalso; destruct CMOK as [[X|[X|[X|X]]] _]; cbn in X; discriminate X].
    exact (conj Gp (conj Tp (conj Ap (conj Gd (conj Td (conj Ad (conj NE (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 (conj L6
             (conj KEEP (conj PXd eq_refl))))))))))))))).
Qed.

Lemma bge_case_main : forall fr cs C A m md regs (s pixs w h datas skel arrs rkel arrr : Z) (rowss rowsr : Z -> Z) (ret : word) (S : TSet),
  (83 <= w)%Z -> (83 <= h)%Z ->
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BGE_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 skel -> getr regs 12 = Z_to_bv 64 rkel ->
  PIXat m pixs (hdv w h 8 0 datas) -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 8 * h))%Z ->
  kobj C A m skel arrs 41 41 rowss -> korg m skel 20 20 -> kobj C A m rkel arrr 1 256 rowsr ->
  forall (ksf rsf : Z -> Z -> Z), kvals m 41 41 rowss ksf -> ksf 20%Z 20%Z = p_one_s -> kvals m 1 256 rowsr rsf -> rsf 0%Z 0%Z = p_one_s ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_bge <= kR)%Z -> (RB_bge w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 0 -> (forall q, live A' q = live A q) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bge) (bR - RB_bge w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  (forall fr' cs' A' m' vm' regs' (pixd datad : Z), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pixd -> pixr_new C A A' m' pixd datad (set_data (pix_hdr w h 8) datad) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bge) (bR - RB_bge w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3ad78) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pixs w h datas skel arrs rkel arrr rowss rowsr ret S Hw83 Hh83
    CK HW FZ H2 Hs16 Hslo Hshi H1 Hret H4 H10 H11 H12 PX HD Hw1 Hh1 Lp Ld KOs KGs KOr ksf rsf KVs Ks0 KVr Kr0 kR bR AR HkR HbR K1 K2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold BGE_STACK, AMB_STACK, LSF in Hslo.
  pose proof HD as (DV & Hw2 & Hh2 & Hsz).
  pose proof PX as (Pp0 & Pp64 & PWF & _).
  pose proof (wf_w _ PWF) as Ww. pose proof (wf_h _ PWF) as Wh. cbn [hdv p_w p_h] in Ww, Wh.
  pose proof KOs as (Gs & TOPs & Ls & L0s & Rs0 & Rs4 & Rsa & Gsa & TOPsa & NEsa & Lsa & L0sa & ROWSs & DISTs).
  pose proof KOr as (Gr & TOPr & Lr & L0r & Rr0 & Rr4 & Rra & Gra & TOPra & NEra & Lra & L0ra & ROWSr & DISTr).
  destruct (exW_blk_rng C A m md pixs 64 CK HW Lp ltac:(lia) ltac:(lia)) as (Pq1 & Pq2 & Pq3).
  destruct (exW_blk_rng C A m md skel 24 CK HW Ls ltac:(lia) ltac:(lia)) as (Sq1 & Sq2 & Sq3).
  destruct (exW_blk_rng C A m md rkel 24 CK HW Lr ltac:(lia) ltac:(lia)) as (Rq1 & Rq2 & Rq3).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & Pal & _). rewrite u_Z2bv in Pal by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ls) as (_ & Sal & _). rewrite u_Z2bv in Sal by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lr) as (_ & Ral & _). rewrite u_Z2bv in Ral by lia.
  pose proof (W_sok_win C A m md (s - 176) 176 CK HW ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SOK.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | |].
  { apply (ge_A al_rom (mkFP fr cs) regs m s pixs skel rkel w h).
    all: first [ assumption | lia | exact (PIX_rd_w SEGS m pixs _ PX) | exact (PIX_rd_h SEGS m pixs _ PX)
               | exact (PIX_rd_d SEGS m pixs _ PX) | exact (proj1 KGs) | exact (proj2 KGs) | bge_clr HW
               | (apply bge_m16_8; assumption) ]. }
  intros fin (regs1 & M1 & -> & RI1 & S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27
              & Lw1 & Lh1 & Ld1 & L41a & L41b & R11 & R12 & R19 & R118 & R18 & R110 & AG1).
  destruct (rinv_WP2 C A A m md M1 [((s - 176)%Z, 176%Z)] s CK HW (sub_live_refl A) Hshi RI1
              ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])) as [HW1 PM1].
  assert (KOs1 : kobj C A M1 skel arrs 41 41 rowss)
    by exact (kobj_livk C A A m M1 skel arrs 41 41 rowss KOs (proj2 PM1) (fun q k E => E) ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (KGs1 : korg M1 skel 20 20).
  { destruct KGs as [KG8 KG12]. split.
    - rewrite (livk_rdn A m M1 skel 24 (skel + 8) 4 (proj2 PM1) Ls) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact KG8.
    - rewrite (livk_rdn A m M1 skel 24 (skel + 12) 4 (proj2 PM1) Ls) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact KG12. }
  pose proof (RB_pixT_nonneg (4 * (wpl_of (w + 41) 8 * (h + 41)))) as RBn1.
  pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))) as RBn2.
  unfold RB_bge in HbR. unfold RK_bge, RK_pixcopy, RK_cmapcopy, RK_pix, RK_kern in HkR.
  assert (CZ1 : cellsZ M1 (ge_sv s regs)) by (cbn [cellsZ ge_sv]; repeat split; assumption).
  apply (H_kinv fr cs C A M1 md regs1 (s - 176)%Z skel arrs rowss (getr regs1 1) S CK HW1 FZ R12
           (bge_m16_sub s 176%Z Hs16 eq_refl) ltac:(unfold KER_STACK, LSF; lia) ltac:(lia) eq_refl
           ltac:(rewrite R11; apply ret_ok_even; vm_compute; reflexivity)
           ltac:(rewrite (AG1 4%bv ltac:(notin_lit)); exact H4) R110 KOs1 KGs1 kR bR AR
           ltac:(unfold RK_kern; lia) ltac:(lia)).
  intros fr2 cz2 A2 m2 vm2 regs2 HW2 FZ2 CK2 PM2 (kel & arr & rows & R210 & KN & KG2 & KV2) FS2 AR2.
  rewrite R11.
  pose proof KN as (Gk & TOPk & ALk & LA2k & LAk & L0k & Rk0 & Rk4 & Rk16 & Ga & TOPa & ALa & NEka & LA2a & LAa & L0a & ROWSk & DISTk & RESTk).
  pose proof (bge_kern_sub C A A2 m2 kel arr 41 41 rows KN) as SUB2.
  destruct (exW_blk_rng C A2 m2 (with_vmmaps vm2 md) kel 24 CK HW2 LA2k ltac:(lia) ltac:(lia)) as (Kq1 & Kq2 & Kq3).
  assert (CZ2 : cellsZ m2 (ge_sv s regs)).
  { apply (cellsZ_frm C (s - 176) M1 m2 _ CK (proj1 PM2) ltac:(lia)); [|exact CZ1].
    bge_fa. }
  pose proof (LIVK_trans A m M1 m2 (proj2 PM1) (proj2 PM2)) as LK2.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW2) | |].
  { apply (ge_B al_rom (mkFP fr2 cz2) regs2 m2 s pixs kel).
    all: first [ assumption | lia | exact (proj1 KG2) | exact (proj2 KG2) | (apply bge_m16_8; assumption)
               | exact (W_sok_win C A2 m2 (with_vmmaps vm2 md) (s - 176) 176 CK HW2 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
               | (rewrite (cs_kept_get regs1 regs2 2%bv CK2 cs2); exact R12)
               | (rewrite (cs_kept_get regs1 regs2 9%bv CK2 cs9); exact R19) ]. }
  intros fin (regs3 & M3 & -> & RI3 & K144 & L120 & L124 & L128 & L132 & R31 & R32 & R310 & R311 & R312 & R313 & R314 & AG3).
  destruct (rinv_WP2 C A A2 m2 (with_vmmaps vm2 md) M3 [((s - 144)%Z, 8%Z); ((s - 132)%Z, 16%Z)] s CK HW2 SUB2 Hshi RI3
              ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]]))
    as [HW3 PM3].
  pose proof (LIVK_trans A m m2 M3 LK2 (proj2 PM3)) as LK3.
  assert (G34 : getr regs3 4 = getr regs 4).
  { rewrite (AG3 4%bv ltac:(notin_lit)), (cs_kept_get regs1 regs2 4%bv CK2 cs4). exact (AG1 4%bv ltac:(notin_lit)). }
  assert (BL : bl_src A2 M3 pixs (hdv w h 8 0 datas)).
  { unfold bl_src. refine (conj (bge_px_livk A m M3 pixs _ PX LK3 Lp) _).
    cbn [hdv p_w p_h p_d p_cmap p_wpl p_data p_xres p_yres].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hw1|]. split; [exact Hh1|].
    split; [reflexivity|]. split; [exact (SUB2 _ _ Lp)|]. split; [exact (SUB2 _ _ Ld)|]. split; reflexivity. }
  apply (H_ambg (mkFP fr2 cz2) C A2 M3 (with_vmmaps vm2 md) regs3 (s - 176)%Z pixs 20%Z 21%Z 20%Z 21%Z (hdv w h 8 0 datas) (getr regs3 1) S
           CK HW3 R32 (bge_m16_sub s 176%Z Hs16 eq_refl) ltac:(unfold AMB_STACK, LSF; lia) ltac:(lia) eq_refl
           ltac:(rewrite R31; apply ret_ok_even; vm_compute; reflexivity)
           ltac:(rewrite G34; exact H4) R310 R311 R312 R313 R314 BL ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(cbn [hdv p_w]; lia) ltac:(cbn [hdv p_w]; lia) ltac:(cbn [hdv p_h]; lia) ltac:(cbn [hdv p_h]; lia)
           (kR - RK_kern 41)%Z (bR - RB_kernS 41 41)%Z AR2 ltac:(unfold RK_pix, RK_kern; lia)
           ltac:(cbn [hdv p_w p_h]; replace (w + 20 + 21)%Z with (w + 41)%Z by lia; replace (h + 20 + 21)%Z with (h + 41)%Z by lia; lia)).
  intros A3 m3 vm3 regs4 HW4 CK4 PM4 RES4 AR4.
  rewrite R31.
  cbn [hdv p_w p_h] in AR4. replace (w + 20 + 21)%Z with (w + 41)%Z in AR4 by lia. replace (h + 20 + 21)%Z with (h + 41)%Z in AR4 by lia.
  assert (G33 : getr regs3 3 = getr regs 3).
  { rewrite (AG3 3%bv ltac:(notin_lit)), (cs_kept_get regs1 regs2 3%bv CK2 cs3). exact (AG1 3%bv ltac:(notin_lit)). }
  destruct (rinv_WP2 C A2 A2 m2 (with_vmmaps vm2 md) M3 [((s - 144)%Z, 8%Z); ((s - 132)%Z, 16%Z)] s CK HW2 (sub_live_refl A2) Hshi RI3
              ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]]))
    as [_ PM3b].
  assert (CZ3 : cellsZ M3 (ge_sv s regs)).
  { apply (cellsZ_out m2 M3 (s - 144) (s - 116) _ (bge_rinv_out _ m2 M3 (s - 144) (s - 116) RI3
             ltac:(intros r [<-|[<-|[]]]; cbn [fst snd]; lia))); [bge_fa | exact CZ2]. }
  assert (CZ4 : cellsZ m3 (ge_sv s regs)).
  { apply (cellsZ_frm C (s - 176) M3 m3 _ CK (proj1 PM4) ltac:(lia)); [bge_fa | exact CZ3]. }
  pose proof (W_sok_win C A3 m3 (with_vmmaps vm3 md) (s - 176) 176 CK HW4 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SOK4.
  assert (G42 : getr regs4 2 = Z_to_bv 64 (s - 176)) by (rewrite (cs_kept_get regs3 regs4 2%bv CK4 cs2); exact R32).
  destruct RES4 as [[R410 LV4] | (pixt & datat & R410 & HDt & PNt)].
  - assert (SUB23 : sub_live A2 A3) by (intros q k E; rewrite LV4; exact E).
    assert (SUB3 : sub_live A A3) by (intros q k E; apply SUB23; apply SUB2; exact E).
    eapply rz_reach; [exact (w_pure _ _ _ _ HW4) | apply (ge_Cn al_rom (mkFP fr2 cz2) regs4 m3 s); first [lia | assumption] |].
    intros fin (regs5 & M5 & -> & RI5 & P152 & R51 & R52 & R510 & AG5).
    destruct (rinv_WP2 C A A3 m3 (with_vmmaps vm3 md) M5 [((s - 152)%Z, 8%Z)] s CK HW4 SUB3 Hshi RI5
                ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])) as [HW5 PM5].
    destruct (rinv_WP2 C A2 A3 m3 (with_vmmaps vm3 md) M5 [((s - 152)%Z, 8%Z)] s CK HW4 SUB23 Hshi RI5
                ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])) as [_ PM5b].
    pose proof (LIVK_trans A2 m2 M3 M5 (proj2 PM3b) (LIVK_trans A2 M3 m3 M5 (proj2 PM4) (proj2 PM5b))) as LKk5.
    assert (KO5 : kobj C A3 M5 kel arr 41 41 rows)
      by exact (kobj_livk C A2 A3 m2 M5 kel arr 41 41 rows (kern_kobj C A A2 m2 kel arr 41 41 rows KN) LKk5 SUB23 ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (S144 : rdn SEGS M5 (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel))).
    { rewrite w2l_Z8 by lia.
      rewrite (rinv_rdn SEGS _ m3 M5 (s - 144) 8 RI5) by (try (intros r [<-|[]]); cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 176) M3 m3 (s - 144) 8 CK (proj1 PM4)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      exact K144. }
    assert (G54 : getr regs5 4 = getr regs 4).
    { rewrite (AG5 4%bv ltac:(notin_lit)), (cs_kept_get regs3 regs4 4%bv CK4 cs4). exact G34. }
    eapply bge_rz_pc; [apply (kernelDestroy_SA_W (fx := mkFP fr2 cz2) C A3 M5 (with_vmmaps vm3 md) regs5 (s - 176) (s - 144) kel arr 41 41 rows
        (getr regs5 1) S CK HW5 R52 (bge_m16_sub s 176 Hs16 eq_refl) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
        (bge_m16_8 _ (bge_m16_sub s 144 Hs16 eq_refl)) eq_refl ltac:(rewrite R51; apply ret_ok_even; vm_compute; reflexivity)
        ltac:(rewrite G54; exact H4) R510 S144 KO5 ltac:(lia) ltac:(lia) _ _ AR4) | apply bv_eq; vm_compute; reflexivity].
    intros A6 m6 vm6 regs6 HW6 CK6 Lk6 La6 Lr6 LQ6 PM6 R6 KEEP6 AR6.
    rewrite R51.
    assert (EQ6 : forall q, live A6 q = live A q).
    { apply (bge_live_split A6 A kel arr rows).
      - rewrite Lk6, LAk. reflexivity.
      - rewrite La6, LAa. reflexivity.
      - intros i Hi. rewrite (Lr6 i Hi). destruct (ROWSk i Hi) as (_ & _ & _ & _ & _ & _ & LR & _). rewrite LR. reflexivity.
      - intros q Nk Na Nr. rewrite (LQ6 q Nk Na Nr), LV4. exact (RESTk q Nk Na Nr). }
    assert (SUB6 : sub_live A A6) by (intros q k E; rewrite EQ6; exact E).
    assert (G62 : getr regs6 2 = Z_to_bv 64 (s - 176)) by (rewrite (cs_kept_get regs5 regs6 2%bv CK6 cs2); exact R52).
    eapply rz_reach; [exact (w_pure _ _ _ _ HW6) | apply (ge_Cn2 al_rom (mkFP fr2 cz2) regs6 m6 s); first [lia | assumption | bge_clr HW6] |].
    intros fin (regs7 & M7 & -> & -> & R71 & R72 & R710 & R711 & R712 & AG7).
    assert (G74 : getr regs7 4 = getr regs 4).
    { rewrite (AG7 4%bv ltac:(notin_lit)), (cs_kept_get regs5 regs6 4%bv CK6 cs4). exact G54. }
    eapply bge_rz_pc; [apply (returnErrorPtr_W (fx := mkFP fr2 cz2) C A6 m6 (with_vmmaps vm6 md) regs7 (s - 176) _ _ 13 21 (getr regs7 1) (Z_to_bv 64 0) S
        CK HW6 R72 (bge_m16_sub s 176 Hs16 eq_refl) ltac:(unfold LSF; lia) ltac:(lia) eq_refl
        ltac:(rewrite R71; apply ret_ok_even; vm_compute; reflexivity) R710 R711 R712 str_ge_msgT str_ge_proc) | apply bv_eq; vm_compute; reflexivity].
    intros m8 regs8 HW8 OUT8 GR8 CS8 V8.
    rewrite R71.
    assert (CZ8 : cellsZ m8 (ge_sv s regs)).
    { assert (CZ5 : cellsZ M5 (ge_sv s regs)).
      { apply (cellsZ_out m3 M5 (s - 152) (s - 144) _ (bge_rinv_out _ m3 M5 (s - 152) (s - 144) RI5
                 ltac:(intros r [<-|[]]; cbn [fst snd]; lia))); [bge_fa | exact CZ4]. }
      assert (CZ6 : cellsZ m6 (ge_sv s regs)).
      { apply (cellsZ_frm C (s - 144 + 8) M5 m6 _ CK (proj1 PM6) ltac:(lia)); [bge_fa | exact CZ5]. }
      apply (cellsZ_out m6 m8 (s - 176 - (16 + LSF)) (s - 176) _ OUT8); [bge_fa | exact CZ6]. }
    cbn [cellsZ ge_sv] in CZ8. destruct CZ8 as (Z1 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & _).
    assert (G82 : getr regs8 2 = Z_to_bv 64 (s - 176)) by (rewrite (cs_kept_get regs7 regs8 2%bv CS8 cs2); exact R72).
    eapply rz_reach; [exact (w_pure _ _ _ _ HW8) | apply (ge_Xerr al_rom (mkFP fr2 cz2) regs8 m8 s 0 ret (getr regs 1) (getr regs 8) (getr regs 9)
        (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
        (getr regs 26) (getr regs 27)); first [lia | assumption] |].
    intros fin (regs9 & M9 & -> & -> & R92 & R910 & R98 & R99 & R918 & R919 & R920 & R921 & R922 & R923 & R924 & R925 & R926 & R927 & AG9).
    apply (K1 fr2 cz2 A6 m8 vm6 regs9 HW8 FZ2).
    + apply cs_kept_intro; [rewrite R92, H2; reflexivity | | | exact R98 | exact R99 | exact R918 | exact R919 | exact R920
        | exact R921 | exact R922 | exact R923 | exact R924 | exact R925 | exact R926 | exact R927].
      * rewrite (AG9 3%bv ltac:(notin_lit)), (cs_kept_get regs7 regs8 3%bv CS8 cs3), (AG7 3%bv ltac:(notin_lit)),
          (cs_kept_get regs5 regs6 3%bv CK6 cs3), (AG5 3%bv ltac:(notin_lit)), (cs_kept_get regs3 regs4 3%bv CK4 cs3). exact G33.
      * rewrite (AG9 4%bv ltac:(notin_lit)), (cs_kept_get regs7 regs8 4%bv CS8 cs4). exact G74.
    + eapply POSTM_trans; [exact PM1|].
      eapply POSTM_trans; [exact (POSTM_mono C A (s - 176) s M1 m2 ltac:(lia) PM2)|].
      eapply POSTM_trans; [exact PM3|].
      eapply POSTM_trans; [exact (POSTM_mono C A (s - 176) s M3 m3 ltac:(lia) (POSTM_sub C A A2 (s - 176) M3 m3 SUB2 PM4))|].
      eapply POSTM_trans; [exact PM5|].
      eapply POSTM_trans; [exact (POSTM_mono C A (s - 144 + 8) s M5 m6 ltac:(lia) (POSTM_sub C A A6 _ M5 m6 SUB6 PM6))|].
      exact (POSTM_sub C A A6 s m6 m8 SUB6 (POSTM_range C A6 m6 (with_vmmaps vm6 md) m8 (s - 176 - (16 + LSF)) (s - 176) s CK HW6 OUT8
               ltac:(unfold LSF; lia) ltac:(lia) Hshi)).
    + exact R910.
    + exact EQ6.
    + exact FS2.
    + apply (aroom_mono A6 vm6 _ _ _ _ AR6); unfold RK_bge, RB_bge, RK_pixcopy, RK_cmapcopy, RK_pix, RK_kern; lia.
  - cbn [hdv p_w p_h] in HDt, PNt.
    replace (w + 20 + 21)%Z with (w + 41)%Z in HDt, PNt by lia.
    replace (h + 20 + 21)%Z with (h + 41)%Z in HDt, PNt by lia.
    pose proof PNt as (Tq1 & Tq2 & Tal & Td1 & Td2 & Tdal & NEpt & LA2p & LA2d & L0pt & L0dt & LA3pt & LA3dt & REST3 & PXt & _).
    cbn [set_data pix_hdr p_wpl p_h p_data] in Td2, LA3dt.
    assert (SUB23 : sub_live A2 A3).
    { intros q k E. rewrite REST3.
      - exact E.
      - intros ->. rewrite LA2p in E. discriminate.
      - intros ->. rewrite LA2d in E. discriminate. }
    assert (SUB3 : sub_live A A3) by (intros q k E; apply SUB23; apply SUB2; exact E).
    pose proof HDt as (_ & Hwt & Hht & Hszt).
    pose proof (wpl_of_range (w + 41) 8 ltac:(lia) DV) as WPt.
    pose proof (wpl_of_range w 8 ltac:(lia) DV) as WPd.
    pose proof (bge_wpl8 (w + 41) ltac:(lia)) as W4t. pose proof (bge_wpl8 w ltac:(lia)) as W4d.
    assert (FR3 : forall (a : Z) (n : nat), (s - 116 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
              rdn SEGS M3 (Z_to_bv 64 a) n = rdn SEGS M1 (Z_to_bv 64 a) n).
    { intros a n Ha Hn.
      rewrite (rinv_rdn SEGS _ m2 M3 a n RI3) by (try (intros r [<-|[<-|[]]]); cbn [fst snd]; lia).
      apply (FRM_rdn16 C (s - 176) M1 m2 a n CK (proj1 PM2)); lia. }
    assert (Lw3 : rdn SEGS m3 (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w)).
    { rewrite (FRM_rdn16 C (s - 176) M3 m3 (s - 108) 4 CK (proj1 PM4)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FR3 (s - 108)%Z 4%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact Lw1. }
    assert (Lh3 : rdn SEGS m3 (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h)).
    { rewrite (FRM_rdn16 C (s - 176) M3 m3 (s - 112) 4 CK (proj1 PM4)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FR3 (s - 112)%Z 4%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact Lh1. }
    eapply rz_reach; [exact (w_pure _ _ _ _ HW4) | apply (ge_C al_rom (mkFP fr2 cz2) regs4 m3 s pixt w h); first [lia | assumption] |].
    intros fin (regs5 & M5 & -> & RI5 & P152 & R51 & R52 & R519 & R510 & R511 & R512 & AG5).
    destruct (rinv_WP2 C A A3 m3 (with_vmmaps vm3 md) M5 [((s - 152)%Z, 8%Z)] s CK HW4 SUB3 Hshi RI5
                ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])) as [HW5 PM5].
    destruct (rinv_WP2 C A3 A3 m3 (with_vmmaps vm3 md) M5 [((s - 152)%Z, 8%Z)] s CK HW4 (sub_live_refl A3) Hshi RI5
                ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])) as [_ PM5c].
    assert (G54 : getr regs5 4 = getr regs 4).
    { rewrite (AG5 4%bv ltac:(notin_lit)), (cs_kept_get regs3 regs4 4%bv CK4 cs4). exact G34. }
    eapply bge_rz_pc; [apply (pixCreate_sureT_W (fx := mkFP fr2 cz2) C A3 M5 (with_vmmaps vm3 md) regs5 (s - 176) w h 8 (getr regs5 1) S
        CK HW5 R52 (bge_m16_sub s 176 Hs16 eq_refl) ltac:(unfold LSF; lia) ltac:(lia) eq_refl
        ltac:(rewrite R51; apply ret_ok_even; vm_compute; reflexivity) ltac:(rewrite G54; exact H4) R510 R511 R512 Hw1 Hh1 HD
        _ _ AR4 ltac:(unfold RK_pix, RK_kern; lia) ltac:(lia)) | apply bv_eq; vm_compute; reflexivity].
    intros A6 m6 vm6 regs6 pixd datad HW6 CK6 PM6 R610 PNd AR6.
    rewrite R51.
    pose proof PNd as (Dq1 & Dq2 & Dal & Dd1 & Dd2 & Ddal & NEpd & LA3pd & LA3dd & L0pd & L0dd & LA6pd & LA6dd & REST6 & PXd & _).
    cbn [set_data pix_hdr p_wpl p_h p_data] in Dd2, LA6dd.
    assert (SUB36 : sub_live A3 A6).
    { intros q k E. rewrite REST6.
      - exact E.
      - intros ->. rewrite LA3pd in E. discriminate.
      - intros ->. rewrite LA3dd in E. discriminate. }
    assert (SUB6 : sub_live A A6) by (intros q k E; apply SUB36; apply SUB3; exact E).
    assert (SUB26 : sub_live A2 A6) by (intros q k E; apply SUB36; apply SUB23; exact E).
    pose proof (LIVK_trans A3 m3 M5 m6 (proj2 PM5c) (proj2 PM6)) as LKt6.
    pose proof (bge_px_livk A3 m3 m6 pixt _ PXt LKt6 LA3pt) as PXt6.
    assert (G62 : getr regs6 2 = Z_to_bv 64 (s - 176)) by (rewrite (cs_kept_get regs5 regs6 2%bv CK6 cs2); exact R52).
    assert (G619 : getr regs6 19 = Z_to_bv 64 pixt) by (rewrite (cs_kept_get regs5 regs6 19%bv CK6 cs19); exact R519).
    assert (G68 : getr regs6 8 = Z_to_bv 64 rkel).
    { rewrite (cs_kept_get regs5 regs6 8%bv CK6 cs8), (AG5 8%bv ltac:(notin_lit)), (cs_kept_get regs3 regs4 8%bv CK4 cs8),
        (AG3 8%bv ltac:(notin_lit)), (cs_kept_get regs1 regs2 8%bv CK2 cs8). exact R18. }
    pose proof (W_sok_win C A6 m6 (with_vmmaps vm6 md) (s - 176) 176 CK HW6 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SOK6.
    eapply rz_reach; [exact (w_pure _ _ _ _ HW6) | apply (ge_D al_rom (mkFP fr2 cz2) regs6 m6 s pixt pixd rkel datat datad (wpl_of (w + 41) 8) (wpl_of w 8));
       first [lia | assumption | exact (PIX_rd_data SEGS m6 pixt _ PXt6) | exact (PIX_rd_wpl SEGS m6 pixt _ PXt6)
             | exact (PIX_rd_data SEGS m6 pixd _ PXd) | exact (PIX_rd_wpl SEGS m6 pixd _ PXd) | (apply bge_m16_8; assumption)] |].
    intros fin (regs7 & M7 & -> & RI7 & D160 & D168 & R72 & R79 & R719 & R720 & R78 & R710 & AG7).
    destruct (rinv_WP2 C A A6 m6 (with_vmmaps vm6 md) M7 [((s - 168)%Z, 16%Z)] s CK HW6 SUB6 Hshi RI7
                ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])) as [HW7 PM7].
    destruct (rinv_WP2 C A6 A6 m6 (with_vmmaps vm6 md) M7 [((s - 168)%Z, 16%Z)] s CK HW6 (sub_live_refl A6) Hshi RI7
                ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])) as [_ PM7c].
    pose proof (LIVK_trans A2 m2 M3 m3 (proj2 PM3b) (proj2 PM4)) as LKk3.
    assert (LKk7 : LIVK A2 m2 M7).
    { apply (LIVK_trans A2 m2 m3 M7 LKk3). apply (LIVK_sub A2 A3 m3 M7 SUB23).
      apply (LIVK_trans A3 m3 m6 M7 LKt6). exact (LIVK_sub A3 A6 m6 M7 SUB36 (proj2 PM7c)). }
    assert (LK7 : LIVK A m M7).
    { apply (LIVK_trans A m M3 M7 LK3). apply (LIVK_trans A M3 m3 M7 (LIVK_sub A A2 M3 m3 SUB2 (proj2 PM4))).
      apply (LIVK_trans A m3 M5 M7 (proj2 PM5)). apply (LIVK_trans A M5 m6 M7 (LIVK_sub A A3 M5 m6 SUB3 (proj2 PM6))).
      exact (proj2 PM7). }
    destruct (exW_blk_rng C A6 m6 (with_vmmaps vm6 md) arr (8 * 41) CK HW6 (SUB26 _ _ LA2a) ltac:(lia) ltac:(lia)) as (Aq1 & Aq2 & Aq3).
    destruct (exW_blk_rng C A m md arrr (8 * 1) CK HW Lra ltac:(lia) ltac:(lia)) as (Rrq1 & Rrq2 & Rrq3).
    pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lra) as (_ & Rral & _). rewrite u_Z2bv in Rral by lia.
    destruct (ROWSr 0%Z ltac:(lia)) as (Rw1 & Rw2 & _ & _ & LRr0 & _ & RRr0).
    destruct (exW_blk_rng C A m md (rowsr 0%Z) (4 * 256) CK HW LRr0 ltac:(lia) ltac:(lia)) as (Rwq1 & Rwq2 & Rwq3).
    pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) LRr0) as (_ & Rwal & _). rewrite u_Z2bv in Rwal by lia.
    pose proof (bge_m16_8 _ ALk) as ALk8. pose proof (bge_m16_8 _ ALa) as ALa8. pose proof (bge_m16_8 _ Rral) as Rral8.
    pose proof (bge_m16_4 _ Rwal) as Rwal4. pose proof (bge_m16_4 _ Tdal) as Tdal4. pose proof (bge_m16_4 _ Ddal) as Ddal4.
    assert (GEO : ge_geo (s - 176) w h (wpl_of (w + 41) 8) (4 * wpl_of (w + 41) 8) (h + 41) (wpl_of w 8) (4 * wpl_of w 8)
                    datat datad kel arr rkel arrr (rowsr 0%Z)).
    { unfold ge_geo. repeat split; lia. }
    assert (FR7 : forall M', rinv [(datad, (4 * wpl_of w 8 * h)%Z)] M7 M' -> forall (a : Z) (n : nat), (s - 144 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
              rdn SEGS M' (Z_to_bv 64 a) n = rdn SEGS M3 (Z_to_bv 64 a) n).
    { intros M' RIM a n Ha Hn.
      rewrite (rinv_rdn SEGS _ M7 M' a n RIM) by (try (intros r [<-|[]]); cbn [fst snd]; lia).
      rewrite (rinv_rdn SEGS _ m6 M7 a n RI7) by (try (intros r [<-|[]]); cbn [fst snd]; lia).
      rewrite (FRM_rdn16 C (s - 176) M5 m6 a n CK (proj1 PM6)) by lia.
      rewrite (rinv_rdn SEGS _ m3 M5 a n RI5) by (try (intros r [<-|[]]); cbn [fst snd]; lia).
      apply (FRM_rdn16 C (s - 176) M3 m3 a n CK (proj1 PM4)); lia. }
    assert (KVs1 : kvals M1 41 41 rowss ksf).
    { apply (bge_kvals_livk A m M1 41 41 rowss ksf KVs (proj2 PM1) ltac:(lia)).
      intros i Hi. destruct (ROWSs i Hi) as (Ri1 & Ri2 & _ & _ & LRi & _ & _). split; [exact LRi | lia]. }
    pose proof (KV2 ksf KVs1) as KVk.
    assert (GRD : forall M', rinv [(datad, (4 * wpl_of w 8 * h)%Z)] M7 M' ->
              ge_rd M' (s - 176) w h (4 * wpl_of (w + 41) 8) (h + 41) datat datad kel arr rkel arrr (rowsr 0%Z) rows
                (fun i j => ksf (40 - i) (40 - j))%Z (fun d => rsf 0 d)%Z).
    { intros M' RIM.
      destruct (rinv_WP2 C A3 A6 M7 (with_vmmaps vm6 md) M' [(datad, (4 * wpl_of w 8 * h)%Z)] s CK HW7 SUB36 Hshi RIM
                  ltac:(apply Forall_cons; [right; exists (Z_to_bv 64 datad), (4 * (wpl_of w 8 * h))%Z; rewrite u_Z2bv by lia; cbn [fst snd];
                          split; [exact LA6dd | split; [exact LA3dd | split; [exact L0dd | lia]]] | apply Forall_nil])) as [HWM PMM].
      pose proof (LIVK_trans A2 m2 M7 M' LKk7 (LIVK_sub A2 A3 M7 M' SUB23 (proj2 PMM))) as LKkM.
      pose proof (LIVK_trans A m M7 M' LK7 (LIVK_sub A A3 M7 M' SUB3 (proj2 PMM))) as LKM.
      assert (KVkM : kvals M' 41 41 rows (fun i j => ksf (40 - i) (40 - j))%Z).
      { apply (bge_kvals_livk A2 m2 M' 41 41 rows _ KVk LKkM ltac:(lia)).
        intros i Hi. destruct (ROWSk i Hi) as (Ri1 & Ri2 & _ & _ & _ & LA2r & _ & _ & _). split; [exact LA2r | lia]. }
      assert (KVrM : kvals M' 1 256 rowsr rsf).
      { apply (bge_kvals_livk A m M' 1 256 rowsr rsf KVr LKM ltac:(lia)).
        intros i Hi. destruct (ROWSr i Hi) as (Ri1 & Ri2 & _ & _ & LRi & _ & _). split; [exact LRi | lia]. }
      unfold ge_rd.
      split; [replace (s - 176 + 32)%Z with (s - 144)%Z by lia;
              rewrite (FR7 M' RIM (s - 144)%Z 8%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact K144|].
      split; [replace (s - 176 + 16)%Z with (s - 160)%Z by lia;
              rewrite (rinv_rdn SEGS _ M7 M' (s - 160) 8 RIM) by (try (intros r [<-|[]]); cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
              exact D160|].
      split; [replace (s - 176 + 44)%Z with (s - 132)%Z by lia;
              rewrite (FR7 M' RIM (s - 132)%Z 4%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact L132|].
      split; [replace (s - 176 + 48)%Z with (s - 128)%Z by lia;
              rewrite (FR7 M' RIM (s - 128)%Z 4%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact L128|].
      split; [replace (s - 176 + 52)%Z with (s - 124)%Z by lia;
              rewrite (FR7 M' RIM (s - 124)%Z 4%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact L124|].
      split; [replace (s - 176 + 56)%Z with (s - 120)%Z by lia;
              rewrite (FR7 M' RIM (s - 120)%Z 4%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact L120|].
      split; [replace (s - 176 + 64)%Z with (s - 112)%Z by lia;
              rewrite (FR7 M' RIM (s - 112)%Z 4%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
              rewrite (FR3 (s - 112)%Z 4%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Lh1|].
      split; [replace (s - 176 + 68)%Z with (s - 108)%Z by lia;
              rewrite (FR7 M' RIM (s - 108)%Z 4%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
              rewrite (FR3 (s - 108)%Z 4%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Lw1|].
      split; [intros p Hp; exact (bge_rd1 C A6 M' (with_vmmaps vm6 md) datat (4 * (wpl_of (w + 41) 8 * (h + 41))) p CK HWM
                                    (SUB36 _ _ LA3dt) ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [rewrite (livk_rdn A2 m2 M' kel 24 (kel + 16) 8 LKkM LA2k) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
              rewrite Rk16, w2l_Z8 by lia; reflexivity|].
      split; [intros q Hq; destruct (ROWSk q Hq) as (Kw1 & Kw2 & Kwal & _ & _ & LA2r & _ & _ & RRq);
              destruct (exW_blk_rng C A2 m2 (with_vmmaps vm2 md) (rows q) (4 * 41) CK HW2 LA2r ltac:(lia) ltac:(lia)) as (Rqq1 & Rqq2 & Rqq3);
              pose proof (bge_m16_4 _ Kwal) as Kwal4;
              split; [rewrite (livk_rdn A2 m2 M' arr (8 * 41) (arr + 8 * q) 8 LKkM LA2a) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
                      rewrite RRq, w2l_Z8 by lia; reflexivity | lia]|].
      split; [intros q t Hq Ht; exact (KVkM q t Hq ltac:(lia))|].
      split; [rewrite (livk_rdn A m M' rkel 24 (rkel + 16) 8 LKM Lr) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
              rewrite Rra, w2l_Z8 by lia; reflexivity|].
      split; [rewrite (livk_rdn A m M' arrr (8 * 1) arrr 8 LKM Lra) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
              replace (arrr + 8 * 0)%Z with arrr in RRr0 by lia; rewrite RRr0, w2l_Z8 by lia; reflexivity|].
      split; [intros d Hd; exact (KVrM 0%Z d ltac:(lia) ltac:(lia))|].
      split; [intros q Hq; apply (W_img16 C A6 M' (with_vmmaps vm6 md) q HWM); lia|].
      split; [exact Ks0 | exact Kr0]. }
    assert (SOKd : store_ok SEGS M7 (Z_to_bv 64 datad) (Z.to_nat (4 * wpl_of w 8 * h)) = true).
    { replace (4 * wpl_of w 8 * h)%Z with (4 * (wpl_of w 8 * h))%Z by ring.
      exact (blk_sok C A6 M7 (with_vmmaps vm6 md) datad _ CK HW7 LA6dd ltac:(lia) ltac:(nia) ltac:(lia)). }
    eapply rz_reach; [exact (w_pure _ _ _ _ HW7) | eapply bge_reach_pc;
       [exact (ge_nest al_rom fr2 cz2 regs7 M7 (s - 176) w h (wpl_of (w + 41) 8) (4 * wpl_of (w + 41) 8) (h + 41) (wpl_of w 8) (4 * wpl_of w 8)
                 datat datad kel arr rkel arrr (rowsr 0%Z) rows (fun i j => ksf (40 - i) (40 - j))%Z (fun d => rsf 0 d)%Z FZ2 GEO GRD SOKd R72 R710 R79 R719 R78)
       | apply bv_eq; vm_compute; reflexivity] |].
    intros fin (fr8 & cz8 & regs8 & M8 & -> & FZ8 & RI8 & AG8 & GF8).
    destruct (rinv_WP2 C A A6 M7 (with_vmmaps vm6 md) M8 [(datad, (4 * wpl_of w 8 * h)%Z)] s CK HW7 SUB6 Hshi RI8
                ltac:(apply Forall_cons; [right; exists (Z_to_bv 64 datad), (4 * (wpl_of w 8 * h))%Z; rewrite u_Z2bv by lia; cbn [fst snd];
                        split; [exact LA6dd | split; [exact (bge_none_sub A A3 _ SUB3 LA3dd) | split; [exact L0dd | lia]]] | apply Forall_nil]))
      as [HW8 PM8].
    destruct (rinv_WP2 C A3 A6 M7 (with_vmmaps vm6 md) M8 [(datad, (4 * wpl_of w 8 * h)%Z)] s CK HW7 SUB36 Hshi RI8
                ltac:(apply Forall_cons; [right; exists (Z_to_bv 64 datad), (4 * (wpl_of w 8 * h))%Z; rewrite u_Z2bv by lia; cbn [fst snd];
                        split; [exact LA6dd | split; [exact LA3dd | split; [exact L0dd | lia]]] | apply Forall_nil])) as [_ PM8c].
    assert (G82 : getr regs8 2 = Z_to_bv 64 (s - 176)) by (rewrite (AG8 2%bv ltac:(unfold GNL; notin_lit)); exact R72).
    eapply rz_reach; [exact (w_pure _ _ _ _ HW8) | eapply bge_reach_pc;
       [apply (ge_E al_rom (mkFP fr8 cz8) regs8 M8 s); first [lia | assumption] | apply bv_eq; vm_compute; reflexivity] |].
    intros fin (regs9 & M9 & -> & -> & R91 & R92 & R910 & AG9).
    assert (G94 : getr regs9 4 = getr regs 4).
    { rewrite (AG9 4%bv ltac:(notin_lit)), (AG8 4%bv ltac:(unfold GNL; notin_lit)), (AG7 4%bv ltac:(notin_lit)),
        (cs_kept_get regs5 regs6 4%bv CK6 cs4). exact G54. }
    pose proof (LIVK_trans A2 m2 M7 M8 LKk7 (LIVK_sub A2 A3 M7 M8 SUB23 (proj2 PM8c))) as LKk8.
    assert (KO8 : kobj C A6 M8 kel arr 41 41 rows)
      by exact (kobj_livk C A2 A6 m2 M8 kel arr 41 41 rows (kern_kobj C A A2 m2 kel arr 41 41 rows KN) LKk8 SUB26 ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (S144 : rdn SEGS M8 (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel))).
    { rewrite w2l_Z8 by lia. rewrite (FR7 M8 RI8 (s - 144)%Z 8%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact K144. }
    eapply bge_rz_pc; [apply (kernelDestroy_SA_W (fx := mkFP fr8 cz8) C A6 M8 (with_vmmaps vm6 md) regs9 (s - 176) (s - 144) kel arr 41 41 rows
        (getr regs9 1) S CK HW8 R92 (bge_m16_sub s 176 Hs16 eq_refl) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
        (bge_m16_8 _ (bge_m16_sub s 144 Hs16 eq_refl)) eq_refl ltac:(rewrite R91; apply ret_ok_even; vm_compute; reflexivity)
        ltac:(rewrite G94; exact H4) R910 S144 KO8 ltac:(lia) ltac:(lia) _ _ AR6) | apply bv_eq; vm_compute; reflexivity].
    intros A10 m10 vm10 regs10 HW10 CK10 Lk10 La10 Lr10 LQ10 PM10 R10' KEEP10 AR10.
    rewrite R91.
    assert (LA10 : forall (q : word) k, live A2 q = None -> live A6 q = Some k -> live A10 q = Some k).
    { intros q k N L. rewrite LQ10; [exact L | exact (bge_neq A2 q _ _ N LA2k) | exact (bge_neq A2 q _ _ N LA2a) |].
      intros i Hi. destruct (ROWSk i Hi) as (_ & _ & _ & _ & _ & LA2r & _ & _ & _). exact (bge_neq A2 q _ _ N LA2r). }
    pose proof (LA10 _ _ LA2p (SUB36 _ _ LA3pt)) as LA10pt.
    pose proof (LA10 _ _ LA2d (SUB36 _ _ LA3dt)) as LA10dt.
    pose proof (LA10 _ _ (bge_none_sub A2 A3 _ SUB23 LA3pd) LA6pd) as LA10pd.
    pose proof (LA10 _ _ (bge_none_sub A2 A3 _ SUB23 LA3dd) LA6dd) as LA10dd.
    assert (G102 : getr regs10 2 = Z_to_bv 64 (s - 176)) by (rewrite (cs_kept_get regs9 regs10 2%bv CK10 cs2); exact R92).
    eapply rz_reach; [exact (w_pure _ _ _ _ HW10) | apply (ge_F al_rom (mkFP fr8 cz8) regs10 m10 s); first [lia | assumption] |].
    intros fin (regs11 & M11 & -> & -> & R111 & R112 & R1110 & AG11).
    assert (G114 : getr regs11 4 = getr regs 4).
    { rewrite (AG11 4%bv ltac:(notin_lit)), (cs_kept_get regs9 regs10 4%bv CK10 cs4). exact G94. }
    pose proof (LIVK_trans A3 m3 M7 M8 (LIVK_trans A3 m3 m6 M7 LKt6 (LIVK_sub A3 A6 m6 M7 SUB36 (proj2 PM7c))) (proj2 PM8c)) as LKt8.
    pose proof (bge_px_livk A10 M8 m10 pixt _ (bge_px_livk A3 m3 M8 pixt _ PXt LKt8 LA3pt) (proj2 PM10) LA10pt) as PXt10.
    assert (P152b : rdn SEGS m10 (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pixt)).
    { rewrite (KEEP10 (s - 152)%Z 8%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (rinv_rdn SEGS _ M7 M8 (s - 152) 8 RI8) by (try (intros r [<-|[]]); cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (rinv_rdn SEGS _ m6 M7 (s - 152) 8 RI7) by (try (intros r [<-|[]]); cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 176) M5 m6 (s - 152) 8 CK (proj1 PM6)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      exact P152. }
    eapply bge_rz_pc; [apply (pixDestroy_free_W (fx := mkFP fr8 cz8) C A10 m10 (with_vmmaps vm10 md) regs11 (s - 176) (s - 152) pixt
        (4 * (wpl_of (w + 41) 8 * (h + 41)))%Z (set_data (pix_hdr (w + 41) (h + 41) 8) datat) None (getr regs11 1) S
        CK HW10 R112 (bge_m16_sub s 176 Hs16 eq_refl) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) eq_refl
        ltac:(rewrite R111; apply ret_ok_even; vm_compute; reflexivity) ltac:(rewrite G114; exact H4)
        (bge_m8_sub s 152 (bge_m16_8 s Hs16) eq_refl) R1110 ltac:(unfold slotok; split; lia) P152b PXt10 eq_refl eq_refl eq_refl
        LA10pt L0pt LA10dt L0dt ltac:(nia) (fun E => NEpt (eq_sym E)) ltac:(intros p k E; discriminate E)) | apply bv_eq; vm_compute; reflexivity].
    intros A12 m12 vm12 regs12 HW12 CK12 Lp12 Ld12 LQ12 SUB12 PD12 R12' RT12.
    rewrite R111.
    cbn [set_data pix_hdr p_data] in Ld12, LQ12.
    pose proof (POSTD_POSTM_win C A12 m12 (with_vmmaps vm12 md) (s - 176) s (s - 152) m10 CK HW12 ltac:(lia) ltac:(lia) ltac:(lia) Hshi PD12) as PM12.
    assert (CZ12 : cellsZ m12 (ge_sv s regs)).
    { assert (CZ5 : cellsZ M5 (ge_sv s regs)).
      { apply (cellsZ_out m3 M5 (s - 152) (s - 144) _ (bge_rinv_out _ m3 M5 (s - 152) (s - 144) RI5
                 ltac:(intros r [<-|[]]; cbn [fst snd]; lia))); [bge_fa | exact CZ4]. }
      assert (CZ6 : cellsZ m6 (ge_sv s regs)).
      { apply (cellsZ_frm C (s - 176) M5 m6 _ CK (proj1 PM6) ltac:(lia)); [bge_fa | exact CZ5]. }
      assert (CZ7 : cellsZ M7 (ge_sv s regs)).
      { apply (cellsZ_out m6 M7 (s - 168) (s - 152) _ (bge_rinv_out _ m6 M7 (s - 168) (s - 152) RI7
                 ltac:(intros r [<-|[]]; cbn [fst snd]; lia))); [bge_fa | exact CZ6]. }
      assert (CZ8 : cellsZ M8 (ge_sv s regs)).
      { apply (cellsZ_out M7 M8 datad (datad + 4 * wpl_of w 8 * h) _ (bge_rinv_out _ M7 M8 datad (datad + 4 * wpl_of w 8 * h) RI8
                 ltac:(intros r [<-|[]]; cbn [fst snd]; lia))); [bge_fa | exact CZ7]. }
      assert (CZ10 : cellsZ m10 (ge_sv s regs)).
      { apply (cellsZ_frm C (s - 144 + 8) M8 m10 _ CK (proj1 PM10) ltac:(lia)); [bge_fa | exact CZ8]. }
      apply (bge_cellsZ_rdn m10 m12); [|exact CZ10].
      intros av Hav. cbn [In ge_sv] in Hav.
      pose proof (POSTD_rdn_above C A12 (s - 176) (s - 152) m10 m12 (fst av) 8 CK PD12) as E.
      rewrite p16_segs in E. apply E; repeat (destruct Hav as [<-|Hav]; [cbn [fst Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]); destruct Hav. }
    cbn [cellsZ ge_sv] in CZ12. destruct CZ12 as (Z1 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & _).
    assert (G122 : getr regs12 2 = Z_to_bv 64 (s - 176)) by (rewrite (cs_kept_get regs11 regs12 2%bv CK12 cs2); exact R112).
    assert (P168 : rdn SEGS m12 (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 pixd)).
    { pose proof (POSTD_rdn_above C A12 (s - 176) (s - 152) m10 m12 (s - 168) 8 CK PD12) as E. rewrite p16_segs in E.
      rewrite E by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (KEEP10 (s - 168)%Z 8%nat) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (rinv_rdn SEGS _ M7 M8 (s - 168) 8 RI8) by (try (intros r [<-|[]]); cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      exact D168. }
    eapply rz_reach; [exact (w_pure _ _ _ _ HW12) | apply (ge_G al_rom (mkFP fr8 cz8) regs12 m12 s pixd ret (getr regs 1) (getr regs 8) (getr regs 9)
        (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
        (getr regs 26) (getr regs 27)); first [lia | assumption] |].
    intros fin (regs13 & M13 & -> & -> & R132 & R1310 & R138 & R139 & R1318 & R1319 & R1320 & R1321 & R1322 & R1323 & R1324 & R1325
                & R1326 & R1327 & AG13).
    assert (SUB10 : sub_live A A10).
    { intros q k E. rewrite LQ10; [exact (SUB6 _ _ E) | intros ->; rewrite LAk in E; discriminate | intros ->; rewrite LAa in E; discriminate |].
      intros i Hi ->. destruct (ROWSk i Hi) as (_ & _ & _ & _ & _ & _ & LRA & _ & _). rewrite LRA in E. discriminate. }
    assert (SUB12' : sub_live A A12).
    { intros q k E. rewrite LQ12; [exact (SUB10 _ _ E) | intros ->; rewrite (bge_none_sub A A2 _ SUB2 LA2p) in E; discriminate
        | intros ->; rewrite (bge_none_sub A A2 _ SUB2 LA2d) in E; discriminate]. }
    assert (Npt : Z_to_bv 64 pixd <> Z_to_bv 64 pixt) by exact (bge_neq A3 _ _ _ LA3pd LA3pt).
    assert (Ndt : Z_to_bv 64 pixd <> Z_to_bv 64 datat) by exact (bge_neq A3 _ _ _ LA3pd LA3dt).
    assert (Ntd : Z_to_bv 64 datad <> Z_to_bv 64 pixt) by exact (bge_neq A3 _ _ _ LA3dd LA3pt).
    assert (Ndd : Z_to_bv 64 datad <> Z_to_bv 64 datat) by exact (bge_neq A3 _ _ _ LA3dd LA3dt).
    assert (LA12pd : live A12 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite (LQ12 _ Npt Ndt); exact LA10pd).
    assert (LA12dd : live A12 (Z_to_bv 64 datad) = Some (4 * (wpl_of w 8 * h))%Z) by (rewrite (LQ12 _ Ntd Ndd); exact LA10dd).
    apply (K2 fr8 cz8 A12 m12 vm12 regs13 pixd datad HW12 FZ8).
    + apply cs_kept_intro; [rewrite R132, H2; reflexivity | | | exact R138 | exact R139 | exact R1318 | exact R1319 | exact R1320
        | exact R1321 | exact R1322 | exact R1323 | exact R1324 | exact R1325 | exact R1326 | exact R1327].
      * rewrite (AG13 3%bv ltac:(notin_lit)), (cs_kept_get regs11 regs12 3%bv CK12 cs3), (AG11 3%bv ltac:(notin_lit)),
          (cs_kept_get regs9 regs10 3%bv CK10 cs3), (AG9 3%bv ltac:(notin_lit)), (AG8 3%bv ltac:(unfold GNL; notin_lit)),
          (AG7 3%bv ltac:(notin_lit)), (cs_kept_get regs5 regs6 3%bv CK6 cs3), (AG5 3%bv ltac:(notin_lit)),
          (cs_kept_get regs3 regs4 3%bv CK4 cs3). exact G33.
      * rewrite (AG13 4%bv ltac:(notin_lit)), (cs_kept_get regs11 regs12 4%bv CK12 cs4). exact G114.
    + eapply POSTM_trans; [exact PM1|].
      eapply POSTM_trans; [exact (POSTM_mono C A (s - 176) s M1 m2 ltac:(lia) PM2)|].
      eapply POSTM_trans; [exact PM3|].
      eapply POSTM_trans; [exact (POSTM_mono C A (s - 176) s M3 m3 ltac:(lia) (POSTM_sub C A A2 (s - 176) M3 m3 SUB2 PM4))|].
      eapply POSTM_trans; [exact PM5|].
      eapply POSTM_trans; [exact (POSTM_mono C A (s - 176) s M5 m6 ltac:(lia) (POSTM_sub C A A3 (s - 176) M5 m6 SUB3 PM6))|].
      eapply POSTM_trans; [exact PM7|].
      eapply POSTM_trans; [exact PM8|].
      eapply POSTM_trans; [exact (POSTM_mono C A (s - 144 + 8) s M8 m10 ltac:(lia) (POSTM_sub C A A10 _ M8 m10 SUB10 PM10))|].
      exact (POSTM_sub C A A12 s m10 m12 SUB12' PM12).
    + exact R1310.
    + unfold pixr_new. cbn [set_data pix_hdr p_wpl p_h p_data].
      split; [exact Dq1|]. split; [exact Dq2|]. split; [exact Dal|]. split; [exact Dd1|]. split; [exact Dd2|]. split; [exact Ddal|].
      split; [exact NEpd|]. split; [exact (bge_none_sub A A3 _ SUB3 LA3pd)|]. split; [exact (bge_none_sub A A3 _ SUB3 LA3dd)|].
      split; [exact L0pd|]. split; [exact L0dd|]. split; [exact LA12pd|]. split; [exact LA12dd|].
      split; [|split; [|reflexivity]].
      * intros q N1 N2.
        destruct (@bv_eq_dec 64 q (Z_to_bv 64 pixt)) as [->|N3]; [rewrite Lp12; symmetry; exact (bge_none_sub A A2 _ SUB2 LA2p)|].
        destruct (@bv_eq_dec 64 q (Z_to_bv 64 datat)) as [->|N4]; [rewrite Ld12; symmetry; exact (bge_none_sub A A2 _ SUB2 LA2d)|].
        rewrite (LQ12 q N3 N4).
        destruct (@bv_eq_dec 64 q (Z_to_bv 64 kel)) as [->|Nk]; [rewrite Lk10, LAk; reflexivity|].
        destruct (@bv_eq_dec 64 q (Z_to_bv 64 arr)) as [->|Na]; [rewrite La10, LAa; reflexivity|].
        destruct (ex_range_dec (fun i => q = Z_to_bv 64 (rows i)) (fun i => @bv_eq_dec 64 q (Z_to_bv 64 (rows i))) 41 0) as [(i & Hi & ->) | NR].
        -- change (Z.of_nat 41) with 41%Z in Hi. rewrite (Lr10 i ltac:(lia)).
           destruct (ROWSk i ltac:(lia)) as (_ & _ & _ & _ & _ & _ & LRA & _ & _). rewrite LRA. reflexivity.
        -- assert (Nr : forall i, (0 <= i < 41)%Z -> q <> Z_to_bv 64 (rows i))
             by (intros i Hi E; apply (NR i); [change (Z.of_nat 41) with 41%Z; lia | exact E]).
           rewrite (LQ10 q Nk Na Nr), (REST6 q N1 N2), (REST3 q N3 N4). exact (RESTk q Nk Na Nr).
      * pose proof (bge_px_livk A6 m6 M7 pixd _ PXd (proj2 PM7c) LA6pd) as PXd7.
        pose proof (live_apart C A6 M7 (with_vmmaps vm6 md) (Z_to_bv 64 pixd) (Z_to_bv 64 datad) 64 (4 * (wpl_of w 8 * h)) CK HW7 LA6pd LA6dd
                      ltac:(intros E; apply NEpd; apply (f_equal bv_unsigned) in E; rewrite !u_Z2bv in E by lia; exact E) ltac:(lia) ltac:(nia)) as DJ.
        rewrite !u_Z2bv in DJ by lia.
        assert (PXd8 : PIXat M8 pixd (set_data (pix_hdr w h 8) datad)).
        { apply (PIXat_frame M7 M8 pixd _ PXd7). intros x Hx.
          apply (bge_rinv_out _ M7 M8 datad (datad + 4 * wpl_of w 8 * h) RI8 ltac:(intros r [<-|[]]; cbn [fst snd]; lia)). lia. }
        exact (bge_px_livk A12 m10 m12 pixd _ (bge_px_livk A10 M8 m10 pixd _ PXd8 (proj2 PM10) LA10pd) (proj2 PM12) LA12pd).
    + intros r Hr. destruct (fs_notin_ge r Hr) as (N11 & N12 & N13 & N14 & N15).
      rewrite (GF8 r (fs_notin_10 r Hr) N11 N12 N13 N14 N15). exact (FS2 r Hr).
    + pose proof (RT12 _ _ AR10 ltac:(unfold RK_pix, RK_kern; lia) ltac:(lia)) as AR12.
      apply (aroom_mono A12 vm12 _ _ _ _ AR12); unfold RK_bge, RB_bge, RK_pixcopy, RK_cmapcopy, RK_pix, RK_kern; lia.
Qed.

Theorem pixBilateralGrayExact_H : forall fr cs C A m md regs (s pixs w h datas skel arrs rkel arrr : Z) (rowss rowsr : Z -> Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BGE_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 skel -> getr regs 12 = Z_to_bv 64 rkel ->
  PIXat m pixs (hdv w h 8 0 datas) -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 8 * h))%Z ->
  kobj C A m skel arrs 41 41 rowss -> korg m skel 20 20 -> kobj C A m rkel arrr 1 256 rowsr ->
  forall (ksf rsf : Z -> Z -> Z), kvals m 41 41 rowss ksf -> ksf 20%Z 20%Z = p_one_s -> kvals m 1 256 rowsr rsf -> rsf 0%Z 0%Z = p_one_s ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_bge <= kR)%Z -> (RB_bge w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 0 -> (forall q, live A' q = live A q) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bge) (bR - RB_bge w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  (forall fr' cs' A' m' vm' regs' (pixd datad : Z), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pixd -> pixr_new C A A' m' pixd datad (set_data (pix_hdr w h 8) datad) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bge) (bR - RB_bge w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3ad78) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pixs w h datas skel arrs rkel arrr rowss rowsr ret S
    CK HW FZ H2 Hs16 Hslo Hshi H1 Hret H4 H10 H11 H12 PX HD Hw1 Hh1 Lp Ld KOs KGs KOr ksf rsf KVs Ks0 KVr Kr0 kR bR AR HkR HbR K1 K2.
  destruct (Z_le_gt_dec w 82) as [Hw|Hw]; [|destruct (Z_le_gt_dec h 82) as [Hh|Hh]].
  - exact (bge_case_w fr cs C A m md regs s pixs w h datas skel arrs rkel arrr rowss rowsr ret S (or_introl Hw)
             CK HW FZ H2 Hs16 Hslo Hshi H1 Hret H4 H10 H11 H12 PX HD Hw1 Hh1 Lp Ld KOs KGs KOr kR bR AR HkR HbR K1 K2).
  - exact (bge_case_w fr cs C A m md regs s pixs w h datas skel arrs rkel arrr rowss rowsr ret S (or_intror Hh)
             CK HW FZ H2 Hs16 Hslo Hshi H1 Hret H4 H10 H11 H12 PX HD Hw1 Hh1 Lp Ld KOs KGs KOr kR bR AR HkR HbR K1 K2).
  - exact (bge_case_main fr cs C A m md regs s pixs w h datas skel arrs rkel arrr rowss rowsr ret S ltac:(lia) ltac:(lia)
             CK HW FZ H2 Hs16 Hslo Hshi H1 Hret H4 H10 H11 H12 PX HD Hw1 Hh1 Lp Ld KOs KGs KOr ksf rsf KVs Ks0 KVr Kr0 kR bR AR HkR HbR K1 K2).
Qed.
End BgeW.

(* [comment removed for export] *)
Section BgeClosed.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
Theorem pixBilateralGrayExact_W : pixBilateralGrayExact_contract.
Proof.
  exact (pixBilateralGrayExact_H kernelInvert_W (fun fx => pixAddMirroredBorder_gen_W (fx := fx))).
Qed.
End BgeClosed.
