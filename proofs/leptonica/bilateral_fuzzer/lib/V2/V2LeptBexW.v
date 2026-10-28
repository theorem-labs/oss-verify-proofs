(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib LeptExecB LeptSlots.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptCmap2 V2LeptPixHdr V2LeptPixCreate V2LeptPixCreateT2 V2LeptPixDestroyH
  V2LeptKernCreateS V2LeptKernDestroyS V2LeptPblW V2LeptRgbc V2LeptCri V2LeptBexSegs V2LeptBl_iface V2LeptBl2_iface V2LeptBl3_iface V2LeptBge_iface V2LeptBex_iface V2LeptKobjLib V2LeptPixCopyT V2LeptKvals.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomK LeptRoomPC LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpReal.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2LeptBexW () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:asr_callocC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc8aic_baseC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase2ASK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8sub_liveI47Corelib4Init9Datatypes6option00C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase4liveK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic9False_indK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission6Common:AllocIface7al_segsI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4lctx00I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3Cok00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots5POSTDC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_topC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2or00C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots?POSTD_rdn_aboveC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase8p16_segsI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes3nat00C5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase5LLU16C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LSTKC5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC5ARocqVerifyHarness?AgentSubmission6Common7FPSteps8frm_zeroC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs6framexC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase6cellsZC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5PIXatC5ARocqVerifyHarness?AgentSubmission2V2BV2LeptKernDestroyS4kobjC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBl3_iface4korgC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4list01C46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics5Riscv3Sem7reg_getC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith6wpl_ofC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL7RB_pixTC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBl2_iface6RB_bgeC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure5aroomK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW5ocompC56Stdlib6ZArith6BinInt1Z3mulK5ARocqVerifyHarness?AgentSubmission6Common8PropExec7FPState01C5ARocqVerifyHarness?AgentSubmission6Common:AllocIface6al_romC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_vmC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_sp0C56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6ll_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_img64C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ro_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_roC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_lg_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_lgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ag_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_agC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=pin_errno_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_errnoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_hcellC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3inZC47Corelib4Init5Logic3notI47Corelib4Init5Logic3and00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_hcellC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;pin_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:ll_devnullC56Stdlib6ZArith6BinInt1Z2ltC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs<pin_ro_belowC4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6pix_wf00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs9pix_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8bytes_atC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9blk_rangeK46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common7StepTac6u_Z2bvK46Stdlib9micromega=RingMicromega5Psatz02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL>RB_pixT_nonnegC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL>RB_c2dS_nonnegC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL7RB_c2dSC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure?alloc_margin_geC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure<alloc_marginC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL8RB_kernSC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL=RB_kernS_c2dSC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixHdr6hdr_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith4dvalC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith<wpl_of_rangeK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW;hdr_ok_32_8C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptKobjLib:kobj_livesC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure<aroom_nonnegC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC45stdpp9bitvector;definitions5bv_eqC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec6v_jalrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs7cs_keptC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixHdr7pix_hdrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8set_dataC5ARocqVerifyHarness?AgentSubmission2V2AV2LeptPixCreateT28pixr_newC5ARocqVerifyHarness?AgentSubmission6Common8VmLedgerAwith_vmmaps_twiceC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_A0C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs>sub_live_transC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:POSTM_monoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9POSTM_subC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;POSTM_transC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LIVKI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs=framex_boundsC46Stdlib5Lists4List;Forall_implC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase:cellsZ_frmC5ARocqVerifyHarness?AgentSubmission2V2;V2LeptCmap27LIVK_atC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs;PIXat_frameC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptKobjLib:kobj_keepLC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptKobjLib:korg_keepKC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase9W_sok_winC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;cs_kept_getC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs7bx_R1_0C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstK47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission6Common5Hoare:regs_agreeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6w_pureC5ARocqVerifyHarness?AgentSubmission6Common9PureModel9mp_haltedC5ARocqVerifyHarness?AgentSubmission6Common9PureModel7mp_lazyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:POSTM_reflK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=sub_live_reflC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission6Common7CatExecDlength_N_to_le_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6WP_winC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:GrayACELib<wbytes_out_ZC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase:cellsZ_outC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec?rdn_wbytes_hit8K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica5W2Lib6w2l_Z8C5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW4cblkC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase9FRM_rdn16C5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW9ocomp_subC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs7bx_R2_0C46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission2V29V2LeptErr9rdn_afterC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW:ocomp_keepC47Corelib4Init5Logic8eq_transC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs4p_rcC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_textC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_cmapC47Corelib4Init5Logic6eq_symK47Corelib4Init9Datatypes4prod01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_dataC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC5ARocqVerifyHarness?AgentSubmission6Common8VmLedgerBwith_vmmaps_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots?POSTD_POSTM_winc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBexW;POSTD_rdn16C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptKobjLib4kblkC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptKobjLib=kobj_blk_liveC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptKobjLib:kobj_keepDC45stdpp9bitvector;definitions9bv_eq_decI47Corelib4Init6Specif7sumbool00c5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBexW9sub_noneLC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:aroom_monoC5ARocqVerifyHarness?AgentSubmission2V2AV2LeptPixDestroyHApixDestroy_free_WC5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg9rz_mstepsC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptPixCopyT3hdvK47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPixCreate8pixr_newK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission2V2:V2LeptRgbcDpixGetRGBComponent_WI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs1W00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5POSTMK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr05C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5p_wplC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_hC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3FRMC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC5ARocqVerifyHarness?AgentSubmission6Common7CatExec6wbytesI5ARocqVerifyHarness?AgentSubmission6Common6CatSim6msteps00K46Stdlib9micromega5Tauto8GFormula07C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom6roomtrK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs4I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecB7fs_listC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom6RK_pixC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBge_iface6RK_bgeK47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBl2_ifaceEPC_pixGetRGBComponentC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8LSTK_valC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBex_iface9BEX_STACKC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs8C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs18I47Corelib7Numbers7BinNums8positive00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs9C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs19C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs3C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs21C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs22C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs23C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs24C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs25C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs26C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs27C5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBge_ifaceHPC_pixBilateralGrayExactC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs7bx_R1_1C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs7bx_R2_1C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs20C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs7bx_R1_2C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs7bx_R2_2K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs5bx_F0C5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW9ocomp_rgbC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs5bx_F1C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs5bx_F2C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs5bx_F3C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs4bx_EC56Stdlib6ZArith6BinInt1Z7sub_0_rC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBex_iface6RK_bexC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBex_iface6RB_bexC56Stdlib6ZArith6BinInt1Z3eqbC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=cs_kept_introC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblW8cblk_decC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptPblWBpixDestroy_ocomp_WC5ARocqVerifyHarness?AgentSubmission2V29V2LeptCriCpixCreateRGBImage_WC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBl2_ifaceDPC_pixCreateRGBImageC5ARocqVerifyHarness?AgentSubmission6Common8VmLedger@with_vmmaps_sameC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs7bx_R3_0C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs7bx_R3_1c5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBexW5FINALc5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBexW6ROUND2c5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBexW6ROUND1c5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBexW6ROUND0C5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_dC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs4bx_AC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs3FRXC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs;framex_initC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs7FRX_outC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs5bx_T8C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBexSegs6bx_T32c5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBexW6main32C5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBex_ifaceJpixBilateralExact_contractC5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSetC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBex_ifaceDPC_pixBilateralExactC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptBge_iface9BGE_STACK".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac rr_solve :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx.

Section BexW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
Hypothesis H_bge : pixBilateralGrayExact_contract.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma sub_noneL : forall (A A' : AS) (q : word), sub_live A A' -> live A' q = None -> live A q = None.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBexW ()) ["BexW"] "p'0h01Eh11Nh21oi001oh31Ah42A'h51Hh63SUBh71eh81kh91qi011zp;3p;2p;1p;5p;4p;6p10000p4p70R0g000`R1p4p710R2p8P0p1001<p4p710R0p8p1001Zp4p70R3P2p8P3P0p8p1002Hp4p70R3P2p8P3P0p8g003>j3>Tg004Gj3=Tg005Pj28Tg006Qj12Tg0076j1<Tg007Tj1:Tg0087j59Tg009>R0j17Tg009`j41Tg00:cj16Tg00;Ej30Tg00;_j24Tg00<9j23TP1j65Tg00<[j2;Tp,2ALR1p,2CLR3p,3ASR9>13R25=1R4'8R5g00=:#2#2#2#2#2#2#<#:P1P3P2f2R2f1R3D9g00=_R6#7R7P1P4P2P3C1%66R830P1P4f4R9P2C1P7f0R:,47P1P4f5R;f3R<C1=07:P0P6P1P4f7R=P;C1=07:A0738]0P3P1P4f8R>f6R?C1136:507P7P1P4P>P=C1A07:8X27P;1363R;P?P=P3P:O3E5A07;8P71362P0P6p-0P:g00>=g00>YR0n10110000021000000X77g00?6P8P:E5P0136<=078/;:b5b1W0X86P:O1P1P4P?P9C1=0781478W0n10110000021010100P:O1b0b2W1W6W9X45W3o"). Qed.

Lemma POSTD_rdn16 : forall C A (s pp : Z) m m' (a : Z) (n : nat), Cok C -> POSTD C A s pp m m' ->
  (s <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z -> (c_top C - LSTK <= s)%Z -> (pp + 8 <= a \/ a + Z.of_nat n <= pp)%Z ->
  rdn SEGS m' (Z_to_bv 64 a) n = rdn SEGS m (Z_to_bv 64 a) n.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBexW ()) ["BexW"] "h01Ah11Ch21ah31mh42m'h51nh62pph71sh81lp;1p;3p;2p;5p;:p;4p;Cp;6g00?Rj19Tg00@2j1ITg003>j3?Tg00A0j3<Tg004Gj3HTg005Pj2GTg006Qj10Tg0076j14Tg007Tj17Tg009>j15Tg00B5j5;Tg00C9l::Tg00D>j21Tg00DZj18Tg00E:j23Tg00EWj12Tg00F5j2FTg00FRj4ETg00GVj2BTg00H3j2@Tg00HMj2ATg00I3j46Tg00;Ej3>Tg00IklCCTg00K:j3DTg000`j6=Tg00L5#9R0p,2ALR1#Ip,2CLR2p,3ASR9?12R35<1R4AH123,G1R5g00=_R6g00=:#0R7#0#0R8#0#0#0R9#4R:#7%48#7R;#5[R<g00M4R=P1P2P3g00MSR>f7R?D;R@P1P2P3P>f8RAP?f6RBf5RCf4RDf3REM::RF11?ERG%8E,3D%27%29'F'1R9P1P2P3f;R7CEg00NK'Bf9RH'1RI%28,3H/1B%8C,3B/1H'@R8%9;#5f>R;PA1A:?R:PBC6P;PHP:PBC63>[[[[[[]5^26^4<]3^66]7]0]1X80P1P2P3P>p,4PINSf=f<P7f:PHPAP?PBPCPDPEf2f1f0MCCV8VIV9VGVFV@X5=X26X4<X3<X66X76X05X14g00ONp,3P169D12E=o"). Qed.

Lemma kvals_keep : forall C A s (m m' : word -> option byte) kel arr h w rows f,
  kobj C A m kel arr h w rows -> POSTM C A s m m' -> kvals m h w rows f -> kvals m' h w rows f.
Proof.
  intros C A s m m' kel arr h w rows f HK [_ HL] HV i j Hi Hj.
  destruct (HV i j Hi Hj) as [R FBf]. split; [|exact FBf].
  destruct HK as (_&_&_&_&_&_&_&_&_&_&_&_&HR&_).
  destruct (HR i Hi) as (R1&R2&_&_&R5&_&_).
  pose proof (alloc_top_lt_errno (c_vm C)) as AT.
  assert (SM : (0 <= stack_max_size)%Z) by first [unfold stack_max_size; lia | vm_compute; discriminate].
  rewrite <- R. apply rdn_ext.
  - rewrite u_Z2bv by lia. change (Z.of_nat 4) with 4%Z. lia.
  - intros x Hx. rewrite u_Z2bv in Hx by lia. change (Z.of_nat 4) with 4%Z in Hx.
    eapply LIVK_at; [exact HL | exact R5 | lia | lia | lia].
Qed.

Section Main32.
Variables (fr : bvmap 5 word) (cs : bv 32) (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word).
Variables (s pixs w h datas skel arrs rkel arrr : Z) (rowss rowsr : Z -> Z) (ret : word) (S : TSet) (kR bR : Z).
Variables (ksf rsf : Z -> Z -> Z).
#[local] Notation RGBW := (4 * (wpl_of w 8 * h))%Z.
#[local] Notation K1 := (RK_pix + RK_bge)%Z.
#[local] Notation B1 := (RB_pixT (4 * (wpl_of w 8 * h)) + RB_bge w h)%Z.
Hypothesis CK : Cok C. Hypothesis HW : W C A m md. Hypothesis Hz : frm_zero cs.
Hypothesis H2 : getr regs 2 = Z_to_bv 64 s. Hypothesis Hs16 : (s mod 16 = 0)%Z.
Hypothesis Hlo : (c_top C - LSTK + BEX_STACK <= s)%Z. Hypothesis Hhi : (s <= c_top C)%Z.
Hypothesis Hret : ret_ok ret. Hypothesis H4 : getr regs 4 = Z_to_bv 64 352880.
Hypothesis PXs : PIXat m pixs (hdv w h 32 0 datas). Hypothesis HOK : hdr_ok w h 32. Hypothesis Hw1 : (1 <= w)%Z. Hypothesis Hh1 : (1 <= h)%Z.
Hypothesis Lps : live A (Z_to_bv 64 pixs) = Some 64%Z. Hypothesis Lds : live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 32 * h))%Z.
Hypothesis KOs0 : kobj C A m skel arrs 41 41 rowss. Hypothesis KOr0 : kobj C A m rkel arrr 1 256 rowsr.
Hypothesis KVs0 : kvals m 41 41 rowss ksf. Hypothesis KVs1 : ksf 20%Z 20%Z = p_one_s.
Hypothesis KVr0 : kvals m 1 256 rowsr rsf. Hypothesis KVr1 : rsf 0%Z 0%Z = p_one_s.
Hypothesis Hrm : aroom A (m_vmmaps md) kR bR. Hypothesis Hrk : (RK_bex 32 <= kR)%Z. Hypothesis Hrb : (RB_bex w h 32 <= bR)%Z.
Hypothesis KN : forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 0 -> (forall q, live A' q = live A q) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bex 32) (bR - RB_bex w h 32) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S.
Hypothesis KP : forall fr' cs' A' m' vm' regs' (pixd datad : Z), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pixd -> pixr_new C A A' m' pixd datad (set_data (pix_hdr w h 32) datad) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bex 32) (bR - RB_bex w h 32) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S.

Lemma bxr_m16 : forall z c, (z mod 16 = 0)%Z -> ((z - 16 * c) mod 16 = 0)%Z.
Proof using.
  intros z c H. clear - H. pose proof (Z.div_mod z 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E.
  rewrite E. replace (16 * (z / 16) - 16 * c)%Z with ((z / 16 - c) * 16)%Z by lia. apply Z.mod_mul. lia.
Qed.
Lemma bxr_m8 : forall z c, (z mod 16 = 0)%Z -> ((z - 8 * c) mod 8 = 0)%Z.
Proof using.
  intros z c H. clear - H. pose proof (Z.div_mod z 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E.
  rewrite E. replace (16 * (z / 16) - 8 * c)%Z with ((2 * (z / 16) - c) * 8)%Z by lia. apply Z.mod_mul. lia.
Qed.
Lemma bxr_wout : forall (mm : word -> option byte) (a : Z) (v : word) (x : word),
  (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z -> ~ (a <= u x < a + 8)%Z -> wbytes mm (Z_to_bv 64 a) (word_to_le_bytes 8 v) x = mm x.
Proof using.
  intros mm a v x J0 J1 J2. clear - J0 J1 J2. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | exact J2].
Qed.
Lemma bxr_rbge_nn : forall ww hh, (0 <= RB_bge ww hh)%Z.
Proof using.
  intros ww hh. clear - ww hh. unfold RB_bge, RB_kernS.
  pose proof (alloc_margin_ge 24 ltac:(lia)). pose proof (alloc_margin_ge (41 * 8) ltac:(lia)). pose proof (alloc_margin_ge (41 * 4) ltac:(lia)).
  pose proof (RB_pixT_nonneg (4 * (wpl_of (ww + 41) 8 * (hh + 41)))). pose proof (RB_pixT_nonneg (4 * (wpl_of ww 8 * hh))). lia.
Qed.
Lemma bxr_cfrm : forall CC s' (m1 m2 : word -> option byte) ss rt r0, Cok CC -> FRM CC s' m1 m2 -> (c_top CC - LSTK <= s')%Z -> (s' <= ss - 48)%Z ->
  (80 <= ss)%Z -> (ss < 2 ^ 64)%Z -> cellsZ m1 (framex ss rt r0) -> cellsZ m2 (framex ss rt r0).
Proof using PINS P16.
  intros CC s' m1 m2 ss rt r0 CK' FR Hl Hs Ha Hb CE. clear - PINS P16 CK' FR Hl Hs Ha Hb CE. apply (cellsZ_frm CC s' m1 m2 _ CK' FR Hl); [|exact CE].
  eapply Forall_impl; [|exact (framex_bounds ss rt r0 Ha Hb)]. intros [a0 v0] [X Y]; cbn [fst] in *; lia.
Qed.
Lemma bxr_cout : forall (m1 m2 : word -> option byte) (lo hi : Z) ss rt r0, (forall x : word, ~ (lo <= u x < hi)%Z -> m2 x = m1 x) ->
  (hi <= ss - 48)%Z -> (80 <= ss)%Z -> (ss < 2 ^ 64)%Z -> cellsZ m1 (framex ss rt r0) -> cellsZ m2 (framex ss rt r0).
Proof using PINS P16.
  intros m1 m2 lo hi ss rt r0 OUT Hh Ha Hb CE. clear - PINS P16 OUT Hh Ha Hb CE. apply (cellsZ_out m1 m2 lo hi _ OUT); [|exact CE].
  eapply Forall_impl; [|exact (framex_bounds ss rt r0 Ha Hb)]. intros [a0 v0] [X Y]; cbn [fst] in *; lia.
Qed.
Ltac bxr_pc RUN :=
  lazymatch type of RUN with msteps _ (@mkst _ _ ?pc _ _) _ =>
    lazymatch goal with |- realizes _ (mkCfg (@mkst _ _ ?pc0 _ _) _) _ =>
      replace pc0 with pc by (apply bv_eq; reflexivity) end end.
Ltac bxr_setpc t :=
  lazymatch goal with |- realizes _ (mkCfg (@mkst _ _ ?pc0 _ _) _) _ => replace pc0 with t by (apply bv_eq; reflexivity) end.
Ltac bxr_step RUN HWx :=
  bxr_pc RUN; eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWx)) | exact (mp_lazy _ (w_pure _ _ _ _ HWx)) | exact RUN |]; clear RUN.
Ltac zl := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.


(* [comment removed for export] *)
Lemma ROUND0 : forall fra csa Aa Ma vma ra,
    (W C Aa Ma (with_vmmaps vma md)) ->
    (frm_zero csa) ->
    (POSTM C A s m Ma) ->
    (sub_live A Aa) ->
    (cellsZ Ma (framex s ret regs)) ->
    (PIXat Ma pixs (hdv w h 32 0 datas)) ->
    (kobj C Aa Ma skel arrs 41 41 rowss) ->
    (korg Ma skel 20 20) ->
    (kobj C Aa Ma rkel arrr 1 256 rowsr) ->
    (getr ra 2 = Z_to_bv 64 (s - 80)) ->
    (getr ra 1 = Z_to_bv 64 240844) ->
    (getr ra 10 = Z_to_bv 64 pixs) ->
    (getr ra 11 = Z_to_bv 64 0) ->
    (getr ra 9 = Z_to_bv 64 pixs) ->
    (getr ra 8 = Z_to_bv 64 skel) ->
    (getr ra 18 = Z_to_bv 64 rkel) ->
    (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr ra x = getr regs x) ->
    (forall r : reg, In (u r) fs_list -> reg_get fra r = reg_get fr r) ->
    (forall q, live Aa q = live A q) ->
    (aroom Aa vma (kR - 0 * K1) (bR - 0 * B1)) ->
    (forall frb csb Ab Mb vmb rb cr dr,
       (W C Ab Mb (with_vmmaps vmb md)) ->
       (frm_zero csb) ->
       (POSTM C A s m Mb) ->
       (sub_live A Ab) ->
       (cellsZ Mb (framex s ret regs)) ->
       (rdn SEGS Mb (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 cr)) ->
       (PIXat Mb pixs (hdv w h 32 0 datas)) ->
       (kobj C Ab Mb skel arrs 41 41 rowss) ->
       (korg Mb skel 20 20) ->
       (kobj C Ab Mb rkel arrr 1 256 rowsr) ->
       (getr rb 2 = Z_to_bv 64 (s - 80)) ->
       (getr rb 9 = Z_to_bv 64 pixs) ->
       (getr rb 8 = Z_to_bv 64 skel) ->
       (getr rb 18 = Z_to_bv 64 rkel) ->
       (getr rb 19 = Z_to_bv 64 cr) ->
       (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rb x = getr regs x) ->
       (forall r : reg, In (u r) fs_list -> reg_get frb r = reg_get fr r) ->
       (ocomp C A Ab Mb cr dr w h) ->
       (forall q, ~ cblk cr dr q -> live Ab q = live A q) ->
       (aroom Ab vmb (kR - 1 * K1) (bR - 1 * B1)) ->
       realizes SEGS (mkCfg (@mkst (mkFP frb csb) rb (240876 : word) Mb al_rom) (with_vmmaps vmb md)) S) ->
    realizes SEGS (mkCfg (@mkst (mkFP fra csa) ra (Z_to_bv 64 PC_pixGetRGBComponent) Ma al_rom) (with_vmmaps vma md)) S.
Proof.
  intros fra csa Aa Ma vma ra HWa Hza PMa SUBa CEa PXa KOsa KGa KOra Ra2 Ra1 Ra10 Ra11 Ra9 Ra8 Ra18 RRa FSa LVa RMa HK.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as HLS. cbn [snd ll_img LLU16] in T5.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  unfold BEX_STACK, BGE_STACK, AMB_STACK, LSF in Hlo.
  assert (Hs80 : (80 <= s)%Z) by lia. assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (Hwp8 : (0 < wpl_of w 8)%Z) by (unfold wpl_of; apply Z.div_str_pos; lia).
  assert (HP8 : (0 < 4 * (wpl_of w 8 * h))%Z) by (pose proof (Z.mul_pos_pos (wpl_of w 8) h Hwp8 ltac:(lia)); lia).
  assert (RKp : RK_pix = 2%Z) by reflexivity.
  assert (RKb : (0 <= RK_bge)%Z) by (unfold RK_bge, RK_kern, RK_pixcopy, RK_cmapcopy, RK_pix; lia).
  pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))) as RBX. pose proof (RB_pixT_nonneg (4 * (wpl_of w 32 * h))) as RBY.
  pose proof (bxr_rbge_nn w h) as RBG.
  pose proof Hrk as Hrk'. pose proof Hrb as Hrb'. unfold RK_bex in Hrk'. unfold RB_bex in Hrb'.
  change ((32 =? 8)%Z) with false in Hrk', Hrb'. cbv iota in Hrk', Hrb'.
  pose proof PXa as (Gps & TOPps & _).
  assert (Lpsa : live Aa (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite LVa; exact Lps).
  pose proof (kobj_lives _ _ _ _ _ _ _ _ KOsa) as (Lsk & _).
  pose proof (kobj_lives _ _ _ _ _ _ _ _ KOra) as (Lrk & _).
  apply (pixGetRGBComponent_W (fx := mkFP fra csa) C Aa Ma (with_vmmaps vma md) ra (s - 80)%Z pixs w h datas 0%Z (getr ra 1) S CK HWa Ra2
           (bxr_m16 s 5 Hs16) ltac:(unfold RGB_STACK, LSF; lia) ltac:(lia) eq_refl ltac:(rewrite Ra1; red; apply bv_eq; reflexivity)
           ltac:(csr; reflexivity) Ra10 Ra11 ltac:(lia) PXa HOK Hw1 Hh1 Lpsa ltac:(rewrite LVa; exact Lds)
           (kR - 0 * K1)%Z (bR - 0 * B1)%Z ltac:(rewrite with_vmmaps_vmmaps; exact RMa) ltac:(lia) ltac:(lia)).
  intros A1 m1 vm1 r1 c dc HW1 CS1 PM1 R1_10 PN1 RM1.
  rewrite with_vmmaps_twice in HW1 |- *. rewrite Ra1.
  destruct PN1 as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & LEQ1 & PXd & _).
  change (dc + 4 * (wpl_of w 8 * h) <= alloc_top (c_vm C))%Z in TOPd.
  change (live A1 (Z_to_bv 64 dc) = Some (4 * (wpl_of w 8 * h))%Z) in L1d.
  change (PIXat m1 c (hdv w h 8 0 dc)) in PXd.
  assert (SUB1 : sub_live Aa A1) by exact (sub_live_new2 _ _ _ _ _ _ L0p L0d L1p L1d LEQ1).
  assert (SUBA1 : sub_live A A1) by exact (sub_live_trans _ _ _ SUBa SUB1).
  assert (PMa1 : POSTM C Aa s Ma m1) by (eapply POSTM_mono; [|exact PM1]; lia).
  pose proof (bxr_cfrm C (s - 80) Ma m1 s ret regs CK (proj1 PM1) ltac:(lia) ltac:(lia) Hs80 Hs64 CEa) as CE1.
  assert (SOK1 : store_ok SEGS m1 (Z_to_bv 64 (s - 56)) 8 = true) by (apply (W_sok_win C A1 m1 (with_vmmaps vm1 md)); [exact CK | exact HW1 | lia | zl]).
  destruct (bx_R1_0 al_rom (mkFP fra csa) r1 m1 s c skel rkel Hs80 Hs64 SOK1 ltac:(csr; reflexivity) R1_10 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r2 & RUN1 & Q2 & Q10 & Q11 & Q12 & Q1 & AG2).
  bxr_step RUN1 HW1.
  set (M1 := wbytes m1 (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 c))) in *.
  assert (OUT1 : forall x : word, ~ (s - 56 <= u x < s - 56 + 8)%Z -> M1 x = m1 x) by (intros x Hx; apply bxr_wout; [lia | lia | exact Hx]).
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C Aa s Ma M1) by (subst M1; wp_win CK).
  destruct WP1 as [HWM1 PMaM1].
  assert (PMmM1 : POSTM C A s m M1) by (eapply POSTM_trans; [exact PMa | eapply POSTM_sub; [exact SUBa | exact PMaM1]]).
  pose proof (bxr_cout m1 M1 (s - 56) (s - 56 + 8) s ret regs OUT1 ltac:(lia) Hs80 Hs64 CE1) as CEM1.
  assert (PXd1 : PIXat M1 c (hdv w h 8 0 dc)) by (apply (PIXat_frame m1); [exact PXd | intros x Hx; apply OUT1; lia]).
  assert (LIVa1 : forall q k, live Aa q = Some k -> live A1 q = live Aa q).
  { intros q k Lq. apply LEQ1; intros E; subst q; congruence. }
  assert (KOs1 : kobj C A1 M1 skel arrs 41 41 rowss) by exact (kobj_keepL C Aa A1 Ma M1 s skel arrs 41 41 rowss KOsa ltac:(lia) LIVa1 PMaM1).
  assert (KOr1 : kobj C A1 M1 rkel arrr 1 256 rowsr) by exact (kobj_keepL C Aa A1 Ma M1 s rkel arrr 1 256 rowsr KOra ltac:(lia) LIVa1 PMaM1).
  assert (KG1 : korg M1 skel 20 20) by exact (korg_keepK C Aa Ma Aa Ma M1 s skel arrs 41 41 rowss 20 20 KOsa Lsk PMaM1 KGa).
  pose proof (kvals_keep C A s m M1 skel arrs 41 41 rowss ksf KOs0 PMmM1 KVs0) as KVs.
  pose proof (kvals_keep C A s m M1 rkel arrr 1 256 rowsr rsf KOr0 PMmM1 KVr0) as KVr.
  assert (NA_c : live A (Z_to_bv 64 c) = None) by (rewrite <- LVa; exact L0p).
  assert (NA_dc : live A (Z_to_bv 64 dc) = None) by (rewrite <- LVa; exact L0d).
  assert (NCBa : forall q k, live Aa q = Some k -> ~ cblk c dc q).
  { intros q k Lq [_ [E|E]]; subst q; congruence. }
  assert (CONT : forall fr2 cs2 A2 m2 vm2 r3 cr dr,
      W C A2 m2 (with_vmmaps vm2 md) -> frm_zero cs2 -> cs_kept r2 r3 -> POSTM C A1 (s - 80) M1 m2 ->
      getr r3 10 = Z_to_bv 64 cr -> ocomp C A1 A2 m2 cr dr w h -> (forall q, ~ cblk cr dr q -> live A2 q = live A1 q) -> sub_live A1 A2 ->
      (forall r : reg, In (u r) fs_list -> reg_get fr2 r = reg_get fra r) ->
      aroom A2 vm2 (kR - 0 * K1 - RK_pix - RK_bge) (bR - 0 * B1 - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bge w h) ->
      realizes SEGS (mkCfg (@mkst (mkFP fr2 cs2) r3 (getr r2 1) m2 al_rom) (with_vmmaps vm2 md)) S).
  { intros fr2 cs2 A2 m2 vm2 r3 cr dr HW2 Hz2 CS2 PM2 R3_10 OC2 LV2 SUB2 FS2 RM2.
    rewrite Q1.
    assert (Bcr : (0 <= cr < 2 ^ 64)%Z) by (destruct OC2 as [[-> _] | (G1 & G2 & _)]; lia).
    assert (NCr : forall q, cblk cr dr q -> ~ cblk c dc q).
    { intros q [NZ Eq] [_ Eq']. destruct OC2 as [[E0 _] | (_ & _ & _ & _ & _ & L0r & L0dr & _)]; [exact (NZ E0) |].
      destruct Eq as [E|E]; destruct Eq' as [E'|E']; rewrite E in E';
        [rewrite E' in L0r | rewrite E' in L0r | rewrite E' in L0dr | rewrite E' in L0dr]; congruence. }
    assert (SOK2 : store_ok SEGS m2 (Z_to_bv 64 (s - 64)) 8 = true) by (apply (W_sok_win C A2 m2 (with_vmmaps vm2 md)); [exact CK | exact HW2 | lia | zl]).
    destruct (bx_R2_0 al_rom (mkFP fr2 cs2) r3 m2 s cr Hs80 Hs64 SOK2 ltac:(csr; reflexivity) R3_10) as (r4 & RUN2 & P2 & P19 & P10 & P1 & AG4).
    bxr_step RUN2 HW2.
    set (M3 := wbytes m2 (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (Z_to_bv 64 cr))) in *.
    assert (PMa2 : POSTM C A1 s M1 m2) by (eapply POSTM_mono; [|exact PM2]; lia).
    assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A1 s M1 M3) by (subst M3; wp_win CK).
    destruct WP3 as [HW3 PM13].
    assert (OUT3 : forall x : word, ~ (s - 64 <= u x < s - 64 + 8)%Z -> M3 x = m2 x) by (intros x Hx; apply bxr_wout; [lia | lia | exact Hx]).
    pose proof (bxr_cfrm C (s - 80) M1 m2 s ret regs CK (proj1 PM2) ltac:(lia) ltac:(lia) Hs80 Hs64 CEM1) as CE2.
    pose proof (bxr_cout m2 M3 (s - 64) (s - 64 + 8) s ret regs OUT3 ltac:(lia) Hs80 Hs64 CE2) as CEM3.
    assert (RD3 : rdn SEGS M3 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 c)).
    { apply (rdn_after m2 M3 _ _ (s - 56) 8 _ OUT3); [lia | zl | zl |].
      rewrite (FRM_rdn16 C (s - 80) M1 m2 (s - 56) 8 CK (proj1 PM2) ltac:(lia) ltac:(zl) ltac:(lia)).
      unfold M1. rewrite <- (w2l_Z8 c) by lia. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
    assert (OCc : ocomp C Aa A2 M3 c dc w h).
    { apply (ocomp_keep C Aa A1 A2 m1 M3 c dc w h).
      - right. exact (conj Gp (conj TOPp (conj Gd (conj TOPd (conj NEpd (conj L0p (conj L0d (conj L00p (conj L00d (conj L1p (conj L1d PXd))))))))))).
      - intros x _ _ _ Hx. rewrite (LIVK_at A1 M1 M3 c 64 x (proj2 PM13) L1p ltac:(lia) ltac:(lia) Hx). apply OUT1. lia.
      - intros q k _ Lq. exact (SUB2 q k Lq). }
    apply (pixDestroy_ocomp_W (mkFP fr2 cs2) C Aa A2 M3 (with_vmmaps vm2 md) r4 (s - 80) (s - 56) c dc w h (getr r4 1) S CK HW3 P2 (bxr_m16 s 5 Hs16)
             ltac:(unfold ALLOC_STACK; lia) ltac:(lia) eq_refl ltac:(rewrite P1; red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) P10
             (bxr_m8 s 7 Hs16) ltac:(lia) ltac:(lia) RD3 OCc HP8).
    intros A3 m3 vm3 r5 HW5 CS5 D1 D2 SUB3 PD3 RT3.
    rewrite with_vmmaps_twice in HW5 |- *. rewrite with_vmmaps_vmmaps in RT3.
    rewrite P1. bxr_setpc (240876 : word).
    assert (SUBa3 : sub_live Aa A3).
    { intros q k Lq. rewrite (D2 q (NCBa q k Lq)). apply SUB2, SUB1. exact Lq. }
    assert (SUBA3 : sub_live A A3) by exact (sub_live_trans _ _ _ SUBa SUBa3).
    assert (LIVa3 : forall q k, live Aa q = Some k -> live A3 q = live Aa q).
    { intros q k Lq. rewrite (D2 q (NCBa q k Lq)), (SUB2 q k (SUB1 q k Lq)), Lq. reflexivity. }
    pose proof (POSTD_POSTM_win C A3 m3 (with_vmmaps vm3 md) (s - 80) s (s - 56) M3 CK HW5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PD3) as PM33.
    pose proof (POSTD_POSTM_win C A3 m3 (with_vmmaps vm3 md) (s - 80) (s - 48) (s - 56) M3 CK HW5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PD3) as PM34.
    assert (PMaa3 : POSTM C Aa s Ma m3).
    { eapply POSTM_trans; [exact PMaM1 |]. eapply POSTM_trans; [exact (POSTM_sub C Aa A1 s M1 M3 SUB1 PM13) |].
      exact (POSTM_sub C Aa A3 s M3 m3 SUBa3 PM33). }
    pose proof (bxr_cfrm C (s - 48) M3 m3 s ret regs CK (proj1 PM34) ltac:(lia) ltac:(lia) Hs80 Hs64 CEM3) as CE3.
    assert (RD64 : rdn SEGS m3 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 cr)).
    { rewrite (POSTD_rdn16 C A3 (s - 80) (s - 56) M3 m3 (s - 64) 8 CK PD3 ltac:(lia) ltac:(zl) ltac:(lia) ltac:(right; zl)).
      unfold M3. rewrite <- (w2l_Z8 cr) by lia. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
    assert (PX3 : PIXat m3 pixs (hdv w h 32 0 datas)).
    { apply (PIXat_frame Ma); [exact PXa |]. intros x Hx. exact (LIVK_at Aa Ma m3 pixs 64 x (proj2 PMaa3) Lpsa ltac:(lia) ltac:(lia) Hx). }
    assert (OC3 : ocomp C A A3 m3 cr dr w h).
    { apply (ocomp_keep C A A2 A3 m2 m3 cr dr w h (ocomp_sub C A1 A A2 m2 cr dr w h SUBA1 OC2)).
      - intros x Lx Tx Gx Hx.
        assert (L3r : live A3 (Z_to_bv 64 cr) = Some 64%Z) by (rewrite D2; [exact Lx | apply NCr; split; [lia | left; reflexivity]]).
        rewrite (LIVK_at A3 M3 m3 cr 64 x (proj2 PM33) L3r ltac:(lia) ltac:(lia) Hx). apply OUT3. lia.
      - intros q k CB Lq. rewrite D2 by (apply NCr; exact CB). exact Lq. }
    assert (RM3 : aroom A3 vm3 (kR - 1 * K1) (bR - 1 * B1)).
    { pose proof (aroom_nonneg _ _ _ _ RM2) as [N1 N2].
      pose proof (RT3 _ _ RM2 ltac:(lia) ltac:(lia)) as RM3'.
      apply (aroom_mono _ _ _ _ _ _ RM3'); lia. }
    apply (HK fr2 cs2 A3 m3 vm3 r5 cr dr HW5 Hz2).
    - eapply POSTM_trans; [exact PMa | exact (POSTM_sub C A Aa s Ma m3 SUBa PMaa3)].
    - exact SUBA3.
    - exact CE3.
    - exact RD64.
    - exact PX3.
    - exact (kobj_keepL C Aa A3 Ma m3 s skel arrs 41 41 rowss KOsa ltac:(lia) LIVa3 PMaa3).
    - exact (korg_keepK C Aa Ma Aa Ma m3 s skel arrs 41 41 rowss 20 20 KOsa Lsk PMaa3 KGa).
    - exact (kobj_keepL C Aa A3 Ma m3 s rkel arrr 1 256 rowsr KOra ltac:(lia) LIVa3 PMaa3).
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - rr_solve.
    - intros r Hr. rewrite (FS2 r Hr). exact (FSa r Hr).
    - exact OC3.
    - intros q NQ. destruct (cblk_dec c dc q) as [CB | NCB'].
      + rewrite (D1 q CB). destruct CB as [_ [-> | ->]]; symmetry; assumption.
      + rewrite (D2 q NCB'), (LV2 q NQ). rewrite <- (LVa q).
        apply LEQ1; intros E; apply NCB'; (split; [lia | first [left; exact E | right; exact E]]).
    - exact RM3. }
  bxr_setpc (Z_to_bv 64 PC_pixBilateralGrayExact).
  apply (H_bge fra csa C A1 M1 (with_vmmaps vm1 md) r2 (s - 80)%Z c w h dc skel arrs rkel arrr rowss rowsr (getr r2 1) S
           CK HWM1 Hza Q2 (bxr_m16 s 5 Hs16) ltac:(unfold BGE_STACK, AMB_STACK, LSF; lia) ltac:(lia) eq_refl ltac:(rewrite Q1; red; apply bv_eq; reflexivity)
           ltac:(csr; reflexivity) Q10 Q11 Q12 PXd1 (hdr_ok_32_8 w h ltac:(lia) ltac:(lia) HOK) Hw1 Hh1 L1p L1d KOs1 KG1 KOr1
           ksf rsf KVs KVs1 KVr KVr1 (kR - 0 * K1 - RK_pix)%Z (bR - 0 * B1 - RB_pixT (4 * (wpl_of w 8 * h)))%Z
           ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia)).
  - intros fr2 cs2 A2 m2 vm2 r3 HW2 Hz2 CS2 PM2 R3_10 LIVEQ FS2 RM2.
    rewrite with_vmmaps_twice in HW2 |- *.
    apply (CONT fr2 cs2 A2 m2 vm2 r3 0%Z 0%Z HW2 Hz2 CS2 PM2 R3_10).
    + left. split; reflexivity.
    + intros q _. exact (LIVEQ q).
    + exact (sub_live_eq _ _ LIVEQ).
    + exact FS2.
    + exact RM2.
  - intros fr2 cs2 A2 m2 vm2 r3 cr dr HW2 Hz2 CS2 PM2 R3_10 PN2 FS2 RM2.
    rewrite with_vmmaps_twice in HW2 |- *.
    destruct PN2 as (Gr & TOPr & ALr & Gdr & TOPdr & ALdr & NErd & L0r & L0dr & L00r & L00dr & L2r & L2dr & LEQ2 & PXr & _).
    change (dr + 4 * (wpl_of w 8 * h) <= alloc_top (c_vm C))%Z in TOPdr.
    change (live A2 (Z_to_bv 64 dr) = Some (4 * (wpl_of w 8 * h))%Z) in L2dr.
    change (PIXat m2 cr (hdv w h 8 0 dr)) in PXr.
    apply (CONT fr2 cs2 A2 m2 vm2 r3 cr dr HW2 Hz2 CS2 PM2 R3_10).
    + right. exact (conj Gr (conj TOPr (conj Gdr (conj TOPdr (conj NErd (conj L0r (conj L0dr (conj L00r (conj L00dr (conj L2r (conj L2dr PXr))))))))))).
    + intros q NQ. apply LEQ2; intros E; apply NQ; (split; [lia | first [left; exact E | right; exact E]]).
    + exact (sub_live_new2 _ _ _ _ _ _ L0r L0dr L2r L2dr LEQ2).
    + exact FS2.
    + exact RM2.
Qed.

Lemma bx1_pix_keep : forall C0 A0 s0 (m0 m1 : word -> option byte) (p : Z) v,
  POSTM C0 A0 s0 m0 m1 -> live A0 (Z_to_bv 64 p) = Some 64%Z -> (0 <= p)%Z -> (p + 64 <= 2 ^ 64)%Z -> PIXat m0 p v -> PIXat m1 p v.
Proof using PINS P16.
  intros C0 A0 s0 m0 m1 p v PM L P0 P64 PX.
  apply (PIXat_frame m0 m1 p v PX). intros x Hx.
  exact (LIVK_at A0 m0 m1 p 64 x (proj2 PM) L P0 P64 Hx).
Qed.

Lemma bx1_cells_postd : forall C0 A0 s0 pp (m0 m1 : word -> option byte) l, Cok C0 -> POSTD C0 A0 s0 pp m0 m1 ->
  (c_top C0 - LSTK <= s0)%Z -> Forall (fun av => s0 <= fst av /\ fst av + 8 <= 2 ^ 64 /\ pp + 8 <= fst av)%Z l ->
  cellsZ m0 l -> cellsZ m1 l.
Proof using PINS P16.
  intros C0 A0 s0 pp m0 m1 l CK0 PD Hs F. clear - PINS P16 CK0 PD Hs F.
  induction F as [|av t Fa Ft IH]; intros CZ; [exact I|].
  destruct av as [a v]. cbn [fst] in Fa. cbn [cellsZ] in CZ |- *. destruct CZ as [R T]. split; [|exact (IH T)].
  rewrite (POSTD_rdn16 C0 A0 s0 pp m0 m1 a 8 CK0 PD) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R.
Qed.

Ltac bx1_pc RUN :=
  match type of RUN with msteps _ (@mkst _ _ ?pc _ _) _ =>
    match goal with |- context [@mkst ?fx ?r ?pc0 ?mm al_rom] => replace pc0 with pc by (apply bv_eq; reflexivity) end
  end.
Ltac bx1_n8 := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac bx1_fb FB := eapply Forall_impl; [|exact FB];
  let a0 := fresh "a0" in let v0 := fresh "v0" in let X := fresh "X" in let Y := fresh "Y" in
  intros [a0 v0] [X Y]; cbn [fst snd] in X, Y |- *; lia.


(* [comment removed for export] *)
Lemma ROUND1 : forall fra csa Aa Ma vma ra cr dr,
    (W C Aa Ma (with_vmmaps vma md)) ->
    (frm_zero csa) ->
    (POSTM C A s m Ma) ->
    (sub_live A Aa) ->
    (cellsZ Ma (framex s ret regs)) ->
    (rdn SEGS Ma (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 cr)) ->
    (PIXat Ma pixs (hdv w h 32 0 datas)) ->
    (kobj C Aa Ma skel arrs 41 41 rowss) ->
    (korg Ma skel 20 20) ->
    (kobj C Aa Ma rkel arrr 1 256 rowsr) ->
    (getr ra 2 = Z_to_bv 64 (s - 80)) ->
    (getr ra 1 = Z_to_bv 64 240888) ->
    (getr ra 10 = Z_to_bv 64 pixs) ->
    (getr ra 11 = Z_to_bv 64 1) ->
    (getr ra 9 = Z_to_bv 64 pixs) ->
    (getr ra 8 = Z_to_bv 64 skel) ->
    (getr ra 18 = Z_to_bv 64 rkel) ->
    (getr ra 19 = Z_to_bv 64 cr) ->
    (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr ra x = getr regs x) ->
    (forall r : reg, In (u r) fs_list -> reg_get fra r = reg_get fr r) ->
    (ocomp C A Aa Ma cr dr w h) ->
    (forall q, ~ cblk cr dr q -> live Aa q = live A q) ->
    (aroom Aa vma (kR - 1 * K1) (bR - 1 * B1)) ->
    (forall frb csb Ab Mb vmb rb cr dr cg dg,
       (W C Ab Mb (with_vmmaps vmb md)) ->
       (frm_zero csb) ->
       (POSTM C A s m Mb) ->
       (sub_live A Ab) ->
       (cellsZ Mb (framex s ret regs)) ->
       (rdn SEGS Mb (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 cr)) ->
       (rdn SEGS Mb (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 cg)) ->
       (PIXat Mb pixs (hdv w h 32 0 datas)) ->
       (kobj C Ab Mb skel arrs 41 41 rowss) ->
       (korg Mb skel 20 20) ->
       (kobj C Ab Mb rkel arrr 1 256 rowsr) ->
       (getr rb 2 = Z_to_bv 64 (s - 80)) ->
       (getr rb 9 = Z_to_bv 64 pixs) ->
       (getr rb 8 = Z_to_bv 64 skel) ->
       (getr rb 18 = Z_to_bv 64 rkel) ->
       (getr rb 19 = Z_to_bv 64 cr) ->
       (getr rb 20 = Z_to_bv 64 cg) ->
       (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rb x = getr regs x) ->
       (forall r : reg, In (u r) fs_list -> reg_get frb r = reg_get fr r) ->
       (ocomp C A Ab Mb cr dr w h) ->
       (ocomp C A Ab Mb cg dg w h) ->
       (forall q, cblk cr dr q -> cblk cg dg q -> False) ->
       (forall q, ~ cblk cr dr q -> ~ cblk cg dg q -> live Ab q = live A q) ->
       (aroom Ab vmb (kR - 2 * K1) (bR - 2 * B1)) ->
       realizes SEGS (mkCfg (@mkst (mkFP frb csb) rb (240920 : word) Mb al_rom) (with_vmmaps vmb md)) S) ->
    realizes SEGS (mkCfg (@mkst (mkFP fra csa) ra (Z_to_bv 64 PC_pixGetRGBComponent) Ma al_rom) (with_vmmaps vma md)) S.
Proof.
  intros fra csa Aa Ma vma ra cr dr HWa Hza PMa SUBa CEa Rcr PXa KOsa KGa KOra G2 G1 G10 G11 G9 G8 G18 G19 GR FSa OCr LVa HRa KC.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. pose proof pin_img64 as IMG.
  unfold BEX_STACK, BGE_STACK, AMB_STACK, LSF in Hlo.
  unfold RK_bex, RB_bex in Hrk, Hrb. cbn [Z.eqb Pos.eqb] in Hrk, Hrb.
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (S80 : (80 <= s)%Z) by lia.
  assert (RKc : (0 <= RK_pix /\ 0 <= RK_bge)%Z) by (unfold RK_bge, RK_kern, RK_pixcopy, RK_cmapcopy, RK_pix; lia).
  pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))) as Rp8.
  pose proof (RB_pixT_nonneg (4 * (wpl_of w 32 * h))) as Rp32.
  assert (Rbge : (0 <= RB_bge w h)%Z).
  { unfold RB_bge. rewrite RB_kernS_small by lia.
    pose proof (RB_pixT_nonneg (4 * (wpl_of (w + 41) 8 * (h + 41)))). pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))). lia. }
  assert (Hwpl : (1 <= wpl_of w 8)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia).
  assert (Hn8 : (0 < 4 * (wpl_of w 8 * h))%Z) by nia.
  pose proof PXa as (Hps0 & Hps64 & _).
  assert (Lps_a : live Aa (Z_to_bv 64 pixs) = Some 64%Z) by (apply SUBa; exact Lps).
  assert (Lds_a : live Aa (Z_to_bv 64 datas) = Some (4 * (wpl_of w 32 * h))%Z) by (apply SUBa; exact Lds).
  pose proof (kobj_lives _ _ _ _ _ _ _ _ KOsa) as (Lsk & _).
  pose proof (framex_bounds s ret regs S80 Hs64) as FB.
  assert (G4 : getr ra 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  apply (pixGetRGBComponent_W (fx := mkFP fra csa) C Aa Ma (with_vmmaps vma md) ra (s - 80)%Z pixs w h datas 1%Z (Z_to_bv 64 240888) S
           CK HWa G2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold RGB_STACK, LSF; lia) ltac:(lia)
           G1 ltac:(red; apply bv_eq; reflexivity) G4 G10 G11 ltac:(lia) PXa HOK Hw1 Hh1 Lps_a Lds_a
           (kR - 1 * K1)%Z (bR - 1 * B1)%Z ltac:(rewrite with_vmmaps_vmmaps; exact HRa) ltac:(lia) ltac:(lia)).
  intros A1 M1 vm1 r1 pixt datat HW1 CS1 PM1 R1t PN1 HR1.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct PN1 as (Tp0 & Tptop & _ & Td0 & Tdtop & _ & Tne & LtA & LdA & L0t & L0d & Lt1 & Ld1 & LEQ1 & PXt1 & _).
  cbn [p_wpl p_h set_data pix_hdr] in Tdtop, Ld1.
  assert (SUB1 : sub_live Aa A1) by exact (sub_live_new2 _ _ _ _ _ _ LtA LdA Lt1 Ld1 LEQ1).
  destruct (bx_R1_1 al_rom (mkFP fra csa) r1 M1 s pixt skel rkel S80 Hs64
              (W_sok_win C A1 M1 _ (s - 56) 8 CK HW1 ltac:(lia) ltac:(bx1_n8))
              ltac:(csr; reflexivity) R1t ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r2 & RUN2 & Q2 & Q10 & Q11 & Q12 & Q1 & AG2).
  bx1_pc RUN2.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |]. clear RUN2.
  set (M2 := wbytes M1 (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 pixt))) in *.
  assert (OUT2 : forall x : word, ~ (s - 56 <= u x < s - 48)%Z -> M2 x = M1 x).
  { intros x Hx. unfold M2. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (HW2 : W C A1 M2 (with_vmmaps vm1 md)).
  { unfold M2. apply W_store_win; [exact CK | exact HW1 | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; bx1_n8]. }
  assert (P2' : POSTM C A1 s M1 M2).
  { unfold M2. eapply POSTM_wbytes_win; [exact CK | exact HW1 | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; bx1_n8 | lia]. }
  assert (P1 : POSTM C Aa s Ma M1) by (eapply POSTM_mono; [|exact PM1]; lia).
  assert (P2 : POSTM C Aa s Ma M2) by (eapply POSTM_trans; [exact P1 | exact (POSTM_sub _ _ _ _ _ _ SUB1 P2')]).
  assert (P2m : POSTM C A s m M2) by (eapply POSTM_trans; [exact PMa | exact (POSTM_sub _ _ _ _ _ _ SUBa P2)]).
  assert (PXt2 : PIXat M2 pixt (hdv w h 8 0 datat)) by exact (bx1_pix_keep C A1 s M1 M2 pixt _ P2' Lt1 ltac:(lia) ltac:(lia) PXt1).
  assert (CE2 : cellsZ M2 (framex s ret regs)).
  { apply (cellsZ_out M1 M2 (s - 56) (s - 48) _ OUT2); [bx1_fb FB|].
    apply (cellsZ_frm C (s - 80) Ma M1 _ CK (proj1 PM1) ltac:(lia)); [bx1_fb FB | exact CEa]. }
  assert (Rcr2 : rdn SEGS M2 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 cr)).
  { apply (rdn_after M1 M2 (s - 56) (s - 48) (s - 64) 8 _ OUT2 ltac:(lia) ltac:(bx1_n8) ltac:(bx1_n8)).
    rewrite (FRM_rdn16 C (s - 80) Ma M1 (s - 64) 8 CK (proj1 PM1)) by bx1_n8. exact Rcr. }
  assert (Rpt2 : rdn SEGS M2 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 pixt)).
  { unfold M2. rewrite rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia). rewrite w2b_Z by lia. reflexivity. }
  assert (EXT1 : forall q k, live Aa q = Some k -> live A1 q = live Aa q) by (intros q k L; rewrite L; exact (SUB1 q k L)).
  pose proof (kobj_keepL C Aa A1 Ma M2 s skel arrs 41 41 rowss KOsa ltac:(lia) EXT1 P2) as KOs2.
  pose proof (kobj_keepL C Aa A1 Ma M2 s rkel arrr 1 256 rowsr KOra ltac:(lia) EXT1 P2) as KOr2.
  pose proof (korg_keepK C Aa Ma Aa Ma M2 s skel arrs 41 41 rowss 20 20 KOsa Lsk P2 KGa) as KG2.
  pose proof (kvals_keep C A s m M2 skel arrs 41 41 rowss ksf KOs0 P2m KVs0) as KVs2.
  pose proof (kvals_keep C A s m M2 rkel arrr 1 256 rowsr rsf KOr0 P2m KVr0) as KVr2.
  assert (FIN : forall fr' cs' A2 M3 vm2 r3 (c dg : Z),
    W C A2 M3 (with_vmmaps vm2 md) -> frm_zero cs' -> cs_kept r2 r3 -> POSTM C A1 (s - 80) M2 M3 ->
    getr r3 10 = Z_to_bv 64 c -> (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fra r) ->
    sub_live A1 A2 -> ocomp C A1 A2 M3 c dg w h -> (forall q, ~ cblk c dg q -> live A2 q = live A1 q) ->
    aroom A2 vm2 (kR - 2 * K1) (bR - 2 * B1) ->
    realizes SEGS (mkCfg (@mkst (mkFP fr' cs') r3 (Z_to_bv 64 240904) M3 al_rom) (with_vmmaps vm2 md)) S).
  { intros fr' cs' A2 M3 vm2 r3 c dg HW3 Hz3 CS3 PM3 R3c FS3 SUB12 OCg LVg HR2.
    assert (Hc : (0 <= c < 2 ^ 64)%Z).
    { unfold ocomp in OCg. destruct OCg as [[-> _]|(Cg0 & Cgt & _)]; lia. }
    destruct (bx_R2_1 al_rom (mkFP fr' cs') r3 M3 s c S80 Hs64
                (W_sok_win C A2 M3 _ (s - 72) 8 CK HW3 ltac:(lia) ltac:(bx1_n8))
                ltac:(csr; reflexivity) R3c)
      as (r4 & RUN4 & V2 & V20 & V10 & V1 & AG4).
    bx1_pc RUN4.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |]. clear RUN4.
    set (M4 := wbytes M3 (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (Z_to_bv 64 c))) in *.
    assert (OUT4 : forall x : word, ~ (s - 72 <= u x < s - 64)%Z -> M4 x = M3 x).
    { intros x Hx. unfold M4. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
    assert (HW4 : W C A2 M4 (with_vmmaps vm2 md)).
    { unfold M4. apply W_store_win; [exact CK | exact HW3 | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; bx1_n8]. }
    assert (P4' : POSTM C A2 s M3 M4).
    { unfold M4. eapply POSTM_wbytes_win; [exact CK | exact HW3 | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; bx1_n8 | lia]. }
    assert (SUBa2 : sub_live Aa A2) by exact (sub_live_trans _ _ _ SUB1 SUB12).
    assert (P3 : POSTM C Aa s M2 M3) by (apply (POSTM_sub _ _ _ _ _ _ SUB1); eapply POSTM_mono; [|exact PM3]; lia).
    assert (P4 : POSTM C Aa s Ma M4).
    { eapply POSTM_trans; [exact P2|]. eapply POSTM_trans; [exact P3|]. exact (POSTM_sub _ _ _ _ _ _ SUBa2 P4'). }
    pose proof (SUB12 _ _ Lt1) as Lt2. pose proof (SUB12 _ _ Ld1) as Ld2.
    assert (PXt4 : PIXat M4 pixt (hdv w h 8 0 datat)).
    { apply (bx1_pix_keep C A2 s M3 M4 pixt _ P4' Lt2 ltac:(lia) ltac:(lia)).
      exact (bx1_pix_keep C A1 (s - 80) M2 M3 pixt _ PM3 Lt1 ltac:(lia) ltac:(lia) PXt2). }
    assert (Rpt4 : rdn SEGS M4 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 pixt)).
    { apply (rdn_after M3 M4 (s - 72) (s - 64) (s - 56) 8 _ OUT4 ltac:(lia) ltac:(bx1_n8) ltac:(bx1_n8)).
      rewrite (FRM_rdn16 C (s - 80) M2 M3 (s - 56) 8 CK (proj1 PM3)) by bx1_n8. exact Rpt2. }
    assert (Rcr4 : rdn SEGS M4 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 cr)).
    { apply (rdn_after M3 M4 (s - 72) (s - 64) (s - 64) 8 _ OUT4 ltac:(lia) ltac:(bx1_n8) ltac:(bx1_n8)).
      rewrite (FRM_rdn16 C (s - 80) M2 M3 (s - 64) 8 CK (proj1 PM3)) by bx1_n8. exact Rcr2. }
    assert (Rcg4 : rdn SEGS M4 (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 c)).
    { unfold M4. rewrite rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia). rewrite w2b_Z by lia. reflexivity. }
    assert (CE4 : cellsZ M4 (framex s ret regs)).
    { apply (cellsZ_out M3 M4 (s - 72) (s - 64) _ OUT4); [bx1_fb FB|].
      apply (cellsZ_frm C (s - 80) M2 M3 _ CK (proj1 PM3) ltac:(lia)); [bx1_fb FB | exact CE2]. }
    apply (pixDestroy_free_W (fx := mkFP fr' cs') C A2 M4 (with_vmmaps vm2 md) r4 (s - 80) (s - 56) pixt (4 * (wpl_of w 8 * h))
             (hdv w h 8 0 datat) None (Z_to_bv 64 240920) S CK HW4 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold ALLOC_STACK; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity)
             ltac:(rewrite <- Zminus_mod_idemp_l, (pbl_m16_8 s Hs16); reflexivity) V10 ltac:(unfold slotok; lia) Rpt4 PXt4
             eq_refl eq_refl eq_refl Lt2 L0t Ld2 L0d Hn8 ltac:(cbn; lia) ltac:(intros ? ? X; discriminate X)).
    intros A3 M5 vm3 r5 HW5 CS5 D1 D2 D3 SUB32 PD5 RD5 RT5.
    rewrite with_vmmaps_twice in HW5 |- *. rewrite with_vmmaps_vmmaps in RT5.
    cbn [p_data hdv] in D2, D3.
    assert (NT : forall q k, live Aa q = Some k -> q <> Z_to_bv 64 pixt /\ q <> Z_to_bv 64 datat).
    { intros q k L. split; intros ->; congruence. }
    assert (SUBa3 : sub_live Aa A3).
    { intros q k L. destruct (NT q k L) as [N1 N2]. rewrite (D3 q N1 N2). exact (SUBa2 q k L). }
    assert (P5' : POSTM C A3 s M4 M5)
      by exact (POSTD_POSTM_win C A3 M5 _ (s - 80) s (s - 56) M4 CK HW5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PD5).
    assert (P5 : POSTM C Aa s Ma M5) by (eapply POSTM_trans; [exact P4 | exact (POSTM_sub _ _ _ _ _ _ SUBa3 P5')]).
    replace (Z_to_bv 64 240920) with (240920 : word) by (apply bv_eq; reflexivity).
    apply (KC fr' cs' A3 M5 vm3 r5 cr dr c dg HW5 Hz3).
    - eapply POSTM_trans; [exact PMa | exact (POSTM_sub _ _ _ _ _ _ SUBa P5)].
    - exact (sub_live_trans _ _ _ SUBa SUBa3).
    - apply (bx1_cells_postd C A3 (s - 80) (s - 56) M4 M5 _ CK PD5 ltac:(lia)); [bx1_fb FB | exact CE4].
    - rewrite (POSTD_rdn16 C A3 (s - 80) (s - 56) M4 M5 (s - 64) 8 CK PD5) by bx1_n8. exact Rcr4.
    - rewrite (POSTD_rdn16 C A3 (s - 80) (s - 56) M4 M5 (s - 72) 8 CK PD5) by bx1_n8. exact Rcg4.
    - exact (bx1_pix_keep C Aa s Ma M5 pixs _ P5 Lps_a Hps0 ltac:(lia) PXa).
    - apply (kobj_keepL C Aa A3 Ma M5 s skel arrs 41 41 rowss KOsa ltac:(lia)); [|exact P5].
      intros q k L. rewrite L. exact (SUBa3 q k L).
    - exact (korg_keepK C Aa Ma Aa Ma M5 s skel arrs 41 41 rowss 20 20 KOsa Lsk P5 KGa).
    - apply (kobj_keepL C Aa A3 Ma M5 s rkel arrr 1 256 rowsr KOra ltac:(lia)); [|exact P5].
      intros q k L. rewrite L. exact (SUBa3 q k L).
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - rr_solve.
    - intros r0 Hr. rewrite (FS3 r0 Hr). exact (FSa r0 Hr).
    - apply (ocomp_keep C A Aa A3 Ma M5 cr dr w h OCr).
      + intros x L T G Hx. exact (LIVK_at Aa Ma M5 cr 64 x (proj2 P5) L ltac:(lia) ltac:(lia) Hx).
      + intros q k _ L. exact (SUBa3 q k L).
    - apply (ocomp_sub C A1 A A3 M5 c dg w h (sub_live_trans _ _ _ SUBa SUB1)).
      apply (ocomp_keep C A1 A2 A3 M3 M5 c dg w h OCg).
      + intros x L T G Hx.
        unfold ocomp in OCg. destruct OCg as [[E _]|(_ & _ & _ & _ & _ & LcA1 & LdA1 & _)]; [lia|].
        assert (N1 : Z_to_bv 64 c <> Z_to_bv 64 pixt) by (intros E; congruence).
        assert (N2 : Z_to_bv 64 c <> Z_to_bv 64 datat) by (intros E; congruence).
        pose proof (D3 _ N1 N2) as L3. rewrite L in L3.
        transitivity (M4 x).
        * exact (LIVK_at A3 M4 M5 c 64 x (proj2 P5') L3 ltac:(lia) ltac:(lia) Hx).
        * exact (LIVK_at A2 M3 M4 c 64 x (proj2 P4') L ltac:(lia) ltac:(lia) Hx).
      + intros q k [Nc Hq] L.
        unfold ocomp in OCg. destruct OCg as [[E _]|(_ & _ & _ & _ & _ & LcA1 & LdA1 & _)]; [contradiction|].
        assert (N1 : q <> Z_to_bv 64 pixt) by (destruct Hq as [-> | ->]; intros E; congruence).
        assert (N2 : q <> Z_to_bv 64 datat) by (destruct Hq as [-> | ->]; intros E; congruence).
        rewrite (D3 q N1 N2). exact L.
    - intros q [Nr Hq1] [Ng Hq2].
      unfold ocomp in OCr, OCg.
      destruct OCr as [[E _]|(_ & _ & _ & _ & _ & _ & _ & _ & _ & Lcr & Ldr & _)]; [contradiction|].
      destruct OCg as [[E _]|(_ & _ & _ & _ & _ & LcA1 & LdA1 & _)]; [contradiction|].
      destruct Hq1 as [-> | ->]; [pose proof (SUB1 _ _ Lcr) as L1 | pose proof (SUB1 _ _ Ldr) as L1];
        destruct Hq2 as [E | E]; rewrite E in L1; congruence.
    - intros q N1 N2. rewrite <- (LVa q N1).
      destruct (bv_eq_dec _ q (Z_to_bv 64 pixt)) as [->|E1]; [rewrite D1, LtA; reflexivity|].
      destruct (bv_eq_dec _ q (Z_to_bv 64 datat)) as [->|E2]; [rewrite D2, LdA; reflexivity|].
      rewrite (D3 q E1 E2), (LVg q N2). exact (LEQ1 q E1 E2).
    - pose proof (aroom_nonneg _ _ _ _ HR2) as [K0 B0].
      pose proof (RT5 _ _ HR2 ltac:(lia) ltac:(lia)) as HR3. rewrite !Z.sub_0_r in HR3. exact HR3. }
  match goal with |- context [@mkst ?fx ?r ?pc ?mm al_rom] =>
    replace pc with (Z_to_bv 64 PC_pixBilateralGrayExact) by (apply bv_eq; reflexivity) end.
  apply (H_bge fra csa C A1 M2 (with_vmmaps vm1 md) r2 (s - 80)%Z pixt w h datat skel arrs rkel arrr rowss rowsr (Z_to_bv 64 240904) S
           CK HW2 Hza Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold BGE_STACK, AMB_STACK, LSF; lia) ltac:(lia)
           Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q10 Q11 Q12
           PXt2 (hdr_ok_32_8 w h ltac:(lia) ltac:(lia) HOK) Hw1 Hh1 Lt1 Ld1 KOs2 KG2 KOr2
           ksf rsf KVs2 KVs1 KVr2 KVr1
           (kR - 1 * K1 - RK_pix)%Z (bR - 1 * B1 - RB_pixT (4 * (wpl_of w 8 * h)))%Z
           ltac:(rewrite with_vmmaps_vmmaps; exact HR1) ltac:(lia) ltac:(lia)).
  - intros fr' cs' A2 M3 vm2 r3 HW3 Hz3 CS3 PM3 R3 LEQ2 FS3 HR2.
    rewrite with_vmmaps_twice in HW3 |- *.
    apply (FIN fr' cs' A2 M3 vm2 r3 0%Z 0%Z HW3 Hz3 CS3 PM3 R3 FS3 (sub_live_eq _ _ LEQ2)
             ltac:(unfold ocomp; left; split; reflexivity) (fun q _ => LEQ2 q)).
    pose proof (aroom_nonneg _ _ _ _ HR2) as [K0 B0].
    eapply aroom_mono; [exact HR2 | lia | lia].
  - intros fr' cs' A2 M3 vm2 r3 pixd datad HW3 Hz3 CS3 PM3 R3 PN2 FS3 HR2.
    rewrite with_vmmaps_twice in HW3 |- *.
    destruct PN2 as (U1 & U2 & _ & U4 & U5 & _ & U7 & U8 & U9 & U10 & U11 & U12 & U13 & U14 & U15 & _).
    cbn [p_wpl p_h set_data pix_hdr] in U5, U13.
    apply (FIN fr' cs' A2 M3 vm2 r3 pixd datad HW3 Hz3 CS3 PM3 R3 FS3 (sub_live_new2 _ _ _ _ _ _ U8 U9 U12 U13 U14)).
    + unfold ocomp. right.
      exact (conj U1 (conj U2 (conj U4 (conj U5 (conj U7 (conj U8 (conj U9 (conj U10 (conj U11 (conj U12 (conj U13 U15))))))))))).
    + intros q N. apply U14.
      * intros E. apply N. split; [lia | left; exact E].
      * intros E. apply N. split; [lia | right; exact E].
    + pose proof (aroom_nonneg _ _ _ _ HR2) as [K0 B0].
      eapply aroom_mono; [exact HR2 | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma ROUND2 : forall fra csa Aa Ma vma ra cr dr cg dg,
    (W C Aa Ma (with_vmmaps vma md)) ->
    (frm_zero csa) ->
    (POSTM C A s m Ma) ->
    (sub_live A Aa) ->
    (cellsZ Ma (framex s ret regs)) ->
    (rdn SEGS Ma (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 cr)) ->
    (rdn SEGS Ma (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 cg)) ->
    (PIXat Ma pixs (hdv w h 32 0 datas)) ->
    (kobj C Aa Ma skel arrs 41 41 rowss) ->
    (korg Ma skel 20 20) ->
    (kobj C Aa Ma rkel arrr 1 256 rowsr) ->
    (getr ra 2 = Z_to_bv 64 (s - 80)) ->
    (getr ra 1 = Z_to_bv 64 240932) ->
    (getr ra 10 = Z_to_bv 64 pixs) ->
    (getr ra 11 = Z_to_bv 64 2) ->
    (getr ra 9 = Z_to_bv 64 pixs) ->
    (getr ra 8 = Z_to_bv 64 skel) ->
    (getr ra 18 = Z_to_bv 64 rkel) ->
    (getr ra 19 = Z_to_bv 64 cr) ->
    (getr ra 20 = Z_to_bv 64 cg) ->
    (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr ra x = getr regs x) ->
    (forall r : reg, In (u r) fs_list -> reg_get fra r = reg_get fr r) ->
    (ocomp C A Aa Ma cr dr w h) ->
    (ocomp C A Aa Ma cg dg w h) ->
    (forall q, cblk cr dr q -> cblk cg dg q -> False) ->
    (forall q, ~ cblk cr dr q -> ~ cblk cg dg q -> live Aa q = live A q) ->
    (aroom Aa vma (kR - 2 * K1) (bR - 2 * B1)) ->
    (forall frb csb Ab Mb vmb rb cr dr cg dg cb db,
       (W C Ab Mb (with_vmmaps vmb md)) ->
       (frm_zero csb) ->
       (POSTM C A s m Mb) ->
       (sub_live A Ab) ->
       (cellsZ Mb (framex s ret regs)) ->
       (rdn SEGS Mb (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 cr)) ->
       (rdn SEGS Mb (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 cg)) ->
       (rdn SEGS Mb (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 cb)) ->
       (PIXat Mb pixs (hdv w h 32 0 datas)) ->
       (kobj C Ab Mb skel arrs 41 41 rowss) ->
       (korg Mb skel 20 20) ->
       (kobj C Ab Mb rkel arrr 1 256 rowsr) ->
       (getr rb 2 = Z_to_bv 64 (s - 80)) ->
       (getr rb 9 = Z_to_bv 64 pixs) ->
       (getr rb 8 = Z_to_bv 64 cb) ->
       (getr rb 18 = Z_to_bv 64 rkel) ->
       (getr rb 19 = Z_to_bv 64 cr) ->
       (getr rb 20 = Z_to_bv 64 cg) ->
       (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rb x = getr regs x) ->
       (forall r : reg, In (u r) fs_list -> reg_get frb r = reg_get fr r) ->
       (ocomp C A Ab Mb cr dr w h) ->
       (ocomp C A Ab Mb cg dg w h) ->
       (ocomp C A Ab Mb cb db w h) ->
       (forall q, cblk cr dr q -> cblk cg dg q -> False) ->
       (forall q, cblk cr dr q -> cblk cb db q -> False) ->
       (forall q, cblk cg dg q -> cblk cb db q -> False) ->
       (forall q, ~ cblk cr dr q -> ~ cblk cg dg q -> ~ cblk cb db q -> live Ab q = live A q) ->
       (aroom Ab vmb (kR - 3 * K1) (bR - 3 * B1)) ->
       realizes SEGS (mkCfg (@mkst (mkFP frb csb) rb (240964 : word) Mb al_rom) (with_vmmaps vmb md)) S) ->
    realizes SEGS (mkCfg (@mkst (mkFP fra csa) ra (Z_to_bv 64 PC_pixGetRGBComponent) Ma al_rom) (with_vmmaps vma md)) S.
Proof.
  intros fra csa Aa Ma vma ra cr dr cg dg HWa Hza PMa SLa CZa RCr RCg PXa KOs KOrg KOr
         Q2 Q1 Q10 Q11 Q9 Q8 Q18 Q19 Q20 QCS FSa OCr OCg DJ LVa RMa HK.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LSv.
  assert (ER : RGB_STACK = 4512%Z) by reflexivity.
  assert (EG : BGE_STACK = 4688%Z) by reflexivity.
  assert (EB : BEX_STACK = 4768%Z) by reflexivity.
  assert (EA : ALLOC_STACK = 1024%Z) by reflexivity.
  pose proof (kobj_lives _ _ _ _ _ _ _ _ KOs) as (LKs & _ & Hk1 & Hk2).
  assert (Hs80 : (80 <= s)%Z) by lia.
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (HM80 : ((s - 80) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  assert (HM56 : ((s - 56) mod 8 = 0)%Z).
  { pose proof (Z.div_mod s 16 ltac:(lia)) as E. rewrite Hs16, Z.add_0_r in E. rewrite E.
    replace (16 * (s / 16) - 56)%Z with ((2 * (s / 16) - 7) * 8)%Z by lia. apply Z.mod_mul. lia. }
  pose proof PXa as (Hp0 & Hp64 & _).
  assert (EKb : RK_bex 32 = (3 * (RK_pix + RK_bge) + RK_pix)%Z) by reflexivity.
  assert (EKp : RK_pix = 2%Z) by reflexivity.
  assert (EKg : (0 <= RK_bge)%Z) by (unfold RK_bge, RK_kern, RK_pixcopy, RK_cmapcopy, RK_pix; lia).
  assert (EBb : RB_bex w h 32 = (3 * (RB_pixT (4 * (wpl_of w 8 * h)) + RB_bge w h) + RB_pixT (4 * (wpl_of w 32 * h)))%Z) by reflexivity.
  assert (RBg : (0 <= RB_bge w h)%Z).
  { unfold RB_bge, RB_kernS.
    pose proof (RB_pixT_nonneg (4 * (wpl_of (w + 41) 8 * (h + 41)))). pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))).
    pose proof (alloc_margin_ge 24 ltac:(lia)). pose proof (alloc_margin_ge (41 * 8) ltac:(lia)).
    pose proof (alloc_margin_ge (41 * 4) ltac:(lia)). lia. }
  pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))) as RBp8.
  pose proof (RB_pixT_nonneg (4 * (wpl_of w 32 * h))) as RBp32.
  assert (WP8 : (1 <= wpl_of w 8)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia).
  assert (PMt : forall m', POSTM C Aa (s - 48) Ma m' -> POSTM C A s m m').
  { intros m' P. apply (POSTM_trans C A s m Ma m' PMa). apply (POSTM_mono C A (s - 48)); [lia|].
    exact (POSTM_sub C A Aa (s - 48) Ma m' SLa P). }
  assert (CBa : forall r0 d0 q, ocomp C A Aa Ma r0 d0 w h -> cblk r0 d0 q -> exists k, live Aa q = Some k).
  { intros r0 d0 q O [N [-> | ->]];
      (destruct O as [[E1 E2]|(_ & _ & _ & _ & _ & _ & _ & _ & _ & La & Ld & _)]; [contradiction | eexists; eassumption]). }
  apply (pixGetRGBComponent_W (fx := mkFP fra csa) C Aa Ma (with_vmmaps vma md) ra (s - 80)%Z pixs w h datas 2%Z (Z_to_bv 64 240932) S
           CK HWa Q2 HM80 ltac:(lia) ltac:(lia) Q1 ltac:(apply ret_ok_even; rewrite u_Z2bv by lia; reflexivity) ltac:(csr; reflexivity)
           Q10 Q11 ltac:(lia) PXa HOK Hw1 Hh1 (SLa _ _ Lps) (SLa _ _ Lds) (kR - 2 * K1)%Z (bR - 2 * B1)%Z
           ltac:(rewrite with_vmmaps_vmmaps; exact RMa) ltac:(lia) ltac:(lia)).
  intros A1 m1 vm1 r1 t dt HW1 CS1 PM1 T10 PN1 RM1.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct PN1 as (Gt1 & Tt1 & Mt1 & Gd1 & Td1 & Md1 & NEt & LAat & LAad & L0t & L0d & L1t & L1d & K1o & PX1 & _).
  cbn [p_wpl p_h set_data pix_hdr] in Td1, L1d.
  assert (SU1 : sub_live Aa A1).
  { intros q k Hq. rewrite K1o; [exact Hq | intros ->; congruence | intros ->; congruence]. }
  assert (SLA1 : sub_live A A1) by exact (sub_live_trans _ _ _ SLa SU1).
  assert (NTD : forall q, live A1 q = None -> ~ cblk t dt q).
  { intros q Hq [_ [-> | ->]]; congruence. }
  assert (SOK1 : store_ok SEGS m1 (Z_to_bv 64 (s - 56)) 8 = true)
    by (apply (W_sok_win C A1 m1 (with_vmmaps vm1 md)); [exact CK | exact HW1 | lia | cbn; lia]).
  destruct (bx_R1_2 al_rom (mkFP fra csa) r1 m1 s t skel rkel Hs80 Hs64 SOK1 ltac:(csr; reflexivity) T10
              ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r2 & MS1 & U2 & U10 & U11 & U12 & U1 & AG2).
  assert (PMa1 : POSTM C Aa (s - 48) Ma m1) by (apply (POSTM_mono C Aa (s - 80)); [lia | exact PM1]).
  destruct (WP_win C A1 Aa Ma m1 (with_vmmaps vm1 md) (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 t)) (s - 48) CK (conj HW1 PMa1) SU1
              ltac:(rewrite u_Z2bv by lia; lia)
              ltac:(rewrite u_Z2bv by lia; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(lia))
    as [HW2 PMa2].
  set (m2 := wbytes m1 (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 t))) in *.
  bxr_pc MS1.
  pose proof (w_pure _ _ _ _ HW1) as [MH1 ML1 _].
  eapply rz_msteps; [exact MH1 | exact ML1 | exact MS1 |].
  assert (M21 : forall x : word, ~ (s - 56 <= u x < s - 56 + 8)%Z -> m2 x = m1 x).
  { intros x Hx. unfold m2. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | exact Hx]. }
  assert (PX2 : PIXat m2 t (hdv w h 8 0 dt)) by (eapply PIXat_frame; [exact PX1|]; intros x Hx; exact (M21 x ltac:(lia))).
  assert (KOs2 : kobj C A1 m2 skel arrs 41 41 rowss).
  { apply (kobj_keepL C Aa A1 Ma m2 (s - 48)); [exact KOs | lia | intros q k Hq; rewrite Hq; exact (SU1 q k Hq) | exact PMa2]. }
  assert (KOr2 : kobj C A1 m2 rkel arrr 1 256 rowsr).
  { apply (kobj_keepL C Aa A1 Ma m2 (s - 48)); [exact KOr | lia | intros q k Hq; rewrite Hq; exact (SU1 q k Hq) | exact PMa2]. }
  assert (KOrg2 : korg m2 skel 20 20) by exact (korg_keepK C Aa Ma Aa Ma m2 (s - 48) skel arrs 41 41 rowss 20 20 KOs LKs PMa2 KOrg).
  assert (KVs2 : kvals m2 41 41 rowss ksf) by exact (kvals_keep C A s m m2 skel arrs 41 41 rowss ksf KOs0 (PMt m2 PMa2) KVs0).
  assert (KVr2 : kvals m2 1 256 rowsr rsf) by exact (kvals_keep C A s m m2 rkel arrr 1 256 rowsr rsf KOr0 (PMt m2 PMa2) KVr0).
  assert (GEN : forall fr3 cs3 A3 m3 vm3 r3 (c dc : Z),
    W C A3 m3 (with_vmmaps vm3 md) -> frm_zero cs3 -> cs_kept r2 r3 -> POSTM C A1 (s - 80) m2 m3 ->
    getr r3 10 = Z_to_bv 64 c ->
    (forall r : reg, In (u r) fs_list -> reg_get fr3 r = reg_get fra r) ->
    aroom A3 vm3 (kR - 2 * K1 - RK_pix - RK_bge) (bR - 2 * B1 - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bge w h) ->
    (forall q, ~ cblk c dc q -> live A3 q = live A1 q) ->
    (forall q, cblk c dc q -> live A1 q = None) ->
    ocomp C A A3 m3 c dc w h ->
    realizes SEGS (mkCfg (@mkst (mkFP fr3 cs3) r3 (Z_to_bv 64 240948) m3 al_rom) (with_vmmaps vm3 md)) S).
  { intros fr3 cs3 A3 m3 vm3 r3 c dc HW3 Hz3 CS3 PM3 C10 FS3 RM3 AS1 AS2 OCb.
    assert (Hc : (0 <= c < 2 ^ 64)%Z) by (destruct OCb as [[-> _]|(Gc & Tc & _)]; lia).
    assert (SU3 : sub_live A1 A3).
    { intros q k Hq. destruct (cblk_dec c dc q) as [B|B]; [rewrite (AS2 q B) in Hq; discriminate | rewrite (AS1 q B); exact Hq]. }
    assert (SUa3 : sub_live Aa A3) by exact (sub_live_trans _ _ _ SU1 SU3).
    assert (SOK3 : store_ok SEGS m3 (Z_to_bv 64 (s - 80)) 8 = true)
      by (apply (W_sok_win C A3 m3 (with_vmmaps vm3 md)); [exact CK | exact HW3 | lia | cbn; lia]).
    destruct (bx_R2_2 al_rom (mkFP fr3 cs3) r3 m3 s c Hs80 Hs64 SOK3 ltac:(csr; reflexivity) C10) as (r4 & MS2 & V2 & V8 & V10 & V1 & AG4).
    assert (PMa3 : POSTM C Aa (s - 48) Ma m3).
    { apply (POSTM_trans C Aa (s - 48) Ma m2 m3 PMa2). apply (POSTM_sub C Aa A1 (s - 48) m2 m3 SU1).
      apply (POSTM_mono C A1 (s - 80)); [lia | exact PM3]. }
    destruct (WP_win C A3 Aa Ma m3 (with_vmmaps vm3 md) (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (Z_to_bv 64 c)) (s - 48) CK (conj HW3 PMa3) SUa3
                ltac:(rewrite u_Z2bv by lia; lia)
                ltac:(rewrite u_Z2bv by lia; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(lia))
      as [HW4 PMa4].
    set (m4 := wbytes m3 (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (Z_to_bv 64 c))) in *.
    bxr_pc MS2.
    pose proof (w_pure _ _ _ _ HW3) as [MH3 ML3 _].
    eapply rz_msteps; [exact MH3 | exact ML3 | exact MS2 |].
    assert (M43 : forall x : word, ~ (s - 80 <= u x < s - 80 + 8)%Z -> m4 x = m3 x).
    { intros x Hx. unfold m4. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | exact Hx]. }
    assert (RD56 : rdn SEGS m4 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 t)).
    { unfold m4. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 80) m2 m3 (s - 56) 8 CK (proj1 PM3) ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(lia)).
      unfold m2. rewrite rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia). rewrite w2b_Z by lia. reflexivity. }
    assert (PX4 : PIXat m4 t (hdv w h 8 0 dt)).
    { eapply PIXat_frame; [exact PX1|]. intros x Hx.
      rewrite (M43 x ltac:(lia)), (LIVK_at A1 m2 m3 t 64 x (proj2 PM3) L1t ltac:(lia) ltac:(lia) Hx).
      exact (M21 x ltac:(lia)). }
    assert (OCt : ocomp C Aa A3 m4 t dt w h).
    { right. exact (conj Gt1 (conj Tt1 (conj Gd1 (conj Td1 (conj NEt (conj LAat (conj LAad (conj L0t (conj L0d
                      (conj (SU3 _ _ L1t) (conj (SU3 _ _ L1d) PX4))))))))))). }
    bxr_setpc (104492 : word).
    apply (pixDestroy_ocomp_W (mkFP fr3 cs3) C Aa A3 m4 (with_vmmaps vm3 md) r4 (s - 80)%Z (s - 56)%Z t dt w h (Z_to_bv 64 240964) S
             CK HW4 V2 HM80 ltac:(lia) ltac:(lia) V1 ltac:(apply ret_ok_even; rewrite u_Z2bv by lia; reflexivity) ltac:(csr; reflexivity)
             V10 HM56 ltac:(lia) ltac:(lia) RD56 OCt ltac:(nia)).
    intros A5 m5 vm5 r5 HW5 CS5 D1 D2 SU53 PD5 RT5.
    rewrite with_vmmaps_twice in HW5 |- *.
    rewrite with_vmmaps_vmmaps in RT5.
    assert (SUa5 : sub_live Aa A5).
    { intros q k Hq. rewrite D2; [exact (SUa3 q k Hq) | intros [_ [-> | ->]]; congruence]. }
    assert (PM45 : POSTM C A5 (s - 48) m4 m5)
      by exact (POSTD_POSTM_win C A5 m5 (with_vmmaps vm5 md) (s - 80) (s - 48) (s - 56) m4 CK HW5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PD5).
    assert (PMa5 : POSTM C Aa (s - 48) Ma m5)
      by exact (POSTM_trans C Aa (s - 48) Ma m4 m5 PMa4 (POSTM_sub C Aa A5 (s - 48) m4 m5 SUa5 PM45)).
    assert (KEEP : forall a, (s - 72 <= a <= s - 64)%Z -> rdn SEGS m5 (Z_to_bv 64 a) 8 = rdn SEGS Ma (Z_to_bv 64 a) 8).
    { intros a Ha.
      rewrite (POSTD_rdn16 C A5 (s - 80) (s - 56) m4 m5 a 8 CK PD5 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(lia)
                 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
      unfold m4. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 80) m2 m3 a 8 CK (proj1 PM3) ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(lia)).
      unfold m2. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      exact (FRM_rdn16 C (s - 80) Ma m1 a 8 CK (proj1 PM1) ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(lia)). }
    assert (RD80 : rdn SEGS m5 (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 c)).
    { rewrite (POSTD_rdn16 C A5 (s - 80) (s - 56) m4 m5 (s - 80) 8 CK PD5 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)
                 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
      unfold m4. rewrite rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia). rewrite w2b_Z by lia. reflexivity. }
    assert (OCb5 : ocomp C A A5 m5 c dc w h).
    { apply (ocomp_keep C A A3 A5 m3 m5 c dc w h OCb).
      - intros x Lx Tx Gx Rx.
        assert (L5 : live A5 (Z_to_bv 64 c) = Some 64%Z).
        { rewrite D2; [exact Lx|]. apply NTD. apply AS2. split; [lia | left; reflexivity]. }
        rewrite (LIVK_at A5 m4 m5 c 64 x (proj2 PM45) L5 ltac:(lia) ltac:(lia) Rx).
        apply M43. lia.
      - intros q k B Hq. rewrite D2; [exact Hq|]. apply NTD. exact (AS2 q B). }
    assert (OK5 : forall r0 d0, ocomp C A Aa Ma r0 d0 w h -> ocomp C A A5 m5 r0 d0 w h).
    { intros r0 d0 O. apply (ocomp_keep C A Aa A5 Ma m5 r0 d0 w h O).
      - intros x Lx Tx Gx Rx. exact (LIVK_at Aa Ma m5 r0 64 x (proj2 PMa5) Lx ltac:(lia) ltac:(lia) Rx).
      - intros q k _ Hq. exact (SUa5 q k Hq). }
    assert (DJc : forall r0 d0 q, ocomp C A Aa Ma r0 d0 w h -> cblk r0 d0 q -> cblk c dc q -> False).
    { intros r0 d0 q O X Y. destruct (CBa r0 d0 q O X) as [k Hk]. pose proof (SU1 q k Hk) as Hkk.
      rewrite (AS2 q Y) in Hkk. discriminate. }
    assert (LV5 : forall q, ~ cblk cr dr q -> ~ cblk cg dg q -> ~ cblk c dc q -> live A5 q = live A q).
    { intros q N1 N2 N3. destruct (cblk_dec t dt q) as [B|B].
      - rewrite (D1 q B). symmetry. apply (sub_noneL A Aa q SLa). destruct B as [_ [-> | ->]]; assumption.
      - rewrite (D2 q B), (AS1 q N3), K1o.
        + exact (LVa q N1 N2).
        + intros E. apply B. split; [lia | left; exact E].
        + intros E. apply B. split; [lia | right; exact E]. }
    assert (RM3' : aroom A3 vm3 (kR - 3 * K1) (bR - 3 * B1)).
    { replace (kR - 3 * K1)%Z with (kR - 2 * K1 - RK_pix - RK_bge)%Z by lia.
      replace (bR - 3 * B1)%Z with (bR - 2 * B1 - RB_pixT (4 * (wpl_of w 8 * h)) - RB_bge w h)%Z by lia. exact RM3. }
    pose proof (aroom_nonneg _ _ _ _ RM3') as [RN1 RN2].
    assert (RM5 : aroom A5 vm5 (kR - 3 * K1) (bR - 3 * B1)).
    { pose proof (RT5 _ _ RM3' ltac:(lia) ltac:(lia)) as X. rewrite !Z.sub_0_r in X. exact X. }
    bxr_setpc (240964 : word).
    apply (HK fr3 cs3 A5 m5 vm5 r5 cr dr cg dg c dc HW5 Hz3 (PMt m5 PMa5) (sub_live_trans _ _ _ SLa SUa5)).
    - eapply cellsZ_frm; [exact CK | exact (proj1 PMa5) | lia | | exact CZa].
      eapply Forall_impl; [| exact (framex_bounds s ret regs Hs80 Hs64)]. intros [a0 v0] [X Y]; cbn [fst] in *; lia.
    - rewrite KEEP by lia. exact RCr.
    - rewrite KEEP by lia. exact RCg.
    - exact RD80.
    - eapply PIXat_frame; [exact PXa|]. intros x Hx. exact (LIVK_at Aa Ma m5 pixs 64 x (proj2 PMa5) (SLa _ _ Lps) ltac:(lia) ltac:(lia) Hx).
    - apply (kobj_keepL C Aa A5 Ma m5 (s - 48)); [exact KOs | lia | intros q k Hq; rewrite Hq; exact (SUa5 q k Hq) | exact PMa5].
    - exact (korg_keepK C Aa Ma Aa Ma m5 (s - 48) skel arrs 41 41 rowss 20 20 KOs LKs PMa5 KOrg).
    - apply (kobj_keepL C Aa A5 Ma m5 (s - 48)); [exact KOr | lia | intros q k Hq; rewrite Hq; exact (SUa5 q k Hq) | exact PMa5].
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - rr_solve.
    - intros r Hr. rewrite (FS3 r Hr). exact (FSa r Hr).
    - exact (OK5 cr dr OCr).
    - exact (OK5 cg dg OCg).
    - exact OCb5.
    - exact DJ.
    - intros q X Y. exact (DJc cr dr q OCr X Y).
    - intros q X Y. exact (DJc cg dg q OCg X Y).
    - exact LV5.
    - exact RM5. }
  bxr_setpc (Z_to_bv 64 PC_pixBilateralGrayExact).
  apply (H_bge fra csa C A1 m2 (with_vmmaps vm1 md) r2 (s - 80)%Z t w h dt skel arrs rkel arrr rowss rowsr (Z_to_bv 64 240948) S
           CK HW2 Hza U2 HM80 ltac:(lia) ltac:(lia) U1 ltac:(apply ret_ok_even; rewrite u_Z2bv by lia; reflexivity) ltac:(csr; reflexivity)
           U10 U11 U12 PX2 (hdr_ok_32_8 w h ltac:(lia) ltac:(lia) HOK) Hw1 Hh1 L1t L1d KOs2 KOrg2 KOr2 ksf rsf KVs2 KVs1 KVr2 KVr1
           (kR - 2 * K1 - RK_pix)%Z (bR - 2 * B1 - RB_pixT (4 * (wpl_of w 8 * h)))%Z ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia)).
  - intros fr3 cs3 A3 m3 vm3 r3 HW3 Hz3 CS3 PM3 C10 LV3 FS3 RM3.
    apply (GEN fr3 cs3 A3 m3 vm3 r3 0%Z 0%Z HW3 Hz3 CS3 PM3 C10 FS3 RM3).
    + intros q _. exact (LV3 q).
    + intros q [N _]. exfalso. exact (N eq_refl).
    + left. split; reflexivity.
  - intros fr3 cs3 A3 m3 vm3 r3 c dc HW3 Hz3 CS3 PM3 C10 PN3 FS3 RM3.
    destruct PN3 as (Gc & Tc & Mc & Gdc & Tdc & Mdc & NEc & L1c & L1dc & L0c & L0dc & L3c & L3dc & K3o & PX3 & _).
    cbn [p_wpl p_h set_data pix_hdr] in Tdc, L3dc.
    apply (GEN fr3 cs3 A3 m3 vm3 r3 c dc HW3 Hz3 CS3 PM3 C10 FS3 RM3).
    + intros q N. apply K3o.
      * intros E. apply N. split; [lia | left; exact E].
      * intros E. apply N. split; [lia | right; exact E].
    + intros q [_ [-> | ->]]; assumption.
    + right. exact (conj Gc (conj Tc (conj Gdc (conj Tdc (conj NEc (conj (sub_noneL A A1 _ SLA1 L1c)
                      (conj (sub_noneL A A1 _ SLA1 L1dc) (conj L0c (conj L0dc (conj L3c (conj L3dc PX3))))))))))).
Qed.

Lemma fz_u_rng : forall x : word, (0 <= u x < 2 ^ 64)%Z.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as X. unfold bv_modulus in X. exact X. Qed.

Lemma fz_oc_none : forall C0 Ar A0 m0 c dc w0 h0, ocomp C0 Ar A0 m0 c dc w0 h0 -> forall q, cblk c dc q -> live Ar q = None.
Proof.
  intros C0 Ar A0 m0 c dc w0 h0 OC q [NZ Hq]. unfold ocomp in OC.
  destruct OC as [[E _] | (_ & _ & _ & _ & _ & L1 & L2 & _)]; [exfalso; exact (NZ E)|].
  destruct Hq as [-> | ->]; assumption.
Qed.

Lemma fz_oc_some : forall C0 Ar A0 m0 c dc w0 h0, ocomp C0 Ar A0 m0 c dc w0 h0 -> forall q, cblk c dc q -> exists k, live A0 q = Some k.
Proof.
  intros C0 Ar A0 m0 c dc w0 h0 OC q [NZ Hq]. unfold ocomp in OC.
  destruct OC as [[E _] | (_ & _ & _ & _ & _ & _ & _ & _ & _ & L1 & L2 & _)]; [exfalso; exact (NZ E)|].
  destruct Hq as [-> | ->]; eexists; eassumption.
Qed.

Lemma fz_notc : forall C0 Ar A0 m0 c dc w0 h0 q, ocomp C0 Ar A0 m0 c dc w0 h0 -> live A0 q = None -> ~ cblk c dc q.
Proof.
  intros C0 Ar A0 m0 c dc w0 h0 q OC L Cq.
  destruct (fz_oc_some C0 Ar A0 m0 c dc w0 h0 OC q Cq) as [k Lk]. congruence.
Qed.

Lemma fz_oc_step : forall C0 Ar A0 A0' B m0 m0' c dc w0 h0, ocomp C0 Ar A0 m0 c dc w0 h0 -> LIVK B m0 m0' ->
  (alloc_top (c_vm C0) + 64 <= 2 ^ 64)%Z ->
  (forall q k, cblk c dc q -> live A0 q = Some k -> live B q = Some k) ->
  (forall q k, cblk c dc q -> live A0 q = Some k -> live A0' q = Some k) -> ocomp C0 Ar A0' m0' c dc w0 h0.
Proof.
  intros C0 Ar A0 A0' B m0 m0' c dc w0 h0 OC LV AT HB HA.
  apply (ocomp_keep C0 Ar A0 A0' m0 m0' c dc w0 h0 OC); [|exact HA].
  intros x L T G Hx. apply (LIVK_at B m0 m0' c 64 x LV); [| lia | lia | exact Hx].
  apply HB; [split; [lia | left; reflexivity] | exact L].
Qed.

Lemma fz_rt0 : forall A0 vm0 A0' vm0' k b, roomtr A0 vm0 A0' vm0' 0 0 -> aroom A0 vm0 k b -> aroom A0' vm0' k b.
Proof.
  intros A0 vm0 A0' vm0' k b RT R. pose proof (aroom_nonneg _ _ _ _ R) as [Hk Hb].
  pose proof (RT k b R ltac:(lia) ltac:(lia)) as R'. rewrite !Z.sub_0_r in R'. exact R'.
Qed.

Lemma fz_fx : forall s0 ret0 rr s', (80 <= s0)%Z -> (s0 < 2 ^ 64)%Z -> (s' <= s0 - 48)%Z ->
  Forall (fun av => s' <= fst av /\ fst av + 8 <= 2 ^ 64)%Z (framex s0 ret0 rr).
Proof.
  intros s0 ret0 rr s' X1 X2 X3. eapply Forall_impl; [|exact (framex_bounds s0 ret0 rr X1 X2)].
  intros av [Y1 Y2]; cbv beta; lia.
Qed.

Lemma fz_subnone : forall (A0 A0' : AS) (q : word), sub_live A0 A0' -> live A0' q = None -> live A0 q = None.
Proof. intros A0 A0' q SL L. destruct (live A0 q) as [k|] eqn:E; [rewrite (SL q k E) in L; discriminate L | reflexivity]. Qed.


(* [comment removed for export] *)
Lemma FINAL : forall frn csn An mn vmn rn cr dr cg dg cb db,
    (W C An mn (with_vmmaps vmn md)) ->
    (frm_zero csn) ->
    (POSTM C A s m mn) ->
    (sub_live A An) ->
    (cellsZ mn (framex s ret regs)) ->
    (rdn SEGS mn (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 cr)) ->
    (rdn SEGS mn (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 cg)) ->
    (rdn SEGS mn (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 cb)) ->
    (PIXat mn pixs (hdv w h 32 0 datas)) ->
    (kobj C An mn skel arrs 41 41 rowss) ->
    (korg mn skel 20 20) ->
    (kobj C An mn rkel arrr 1 256 rowsr) ->
    (getr rn 2 = Z_to_bv 64 (s - 80)) ->
    (getr rn 9 = Z_to_bv 64 pixs) ->
    (getr rn 8 = Z_to_bv 64 cb) ->
    (getr rn 18 = Z_to_bv 64 rkel) ->
    (getr rn 19 = Z_to_bv 64 cr) ->
    (getr rn 20 = Z_to_bv 64 cg) ->
    (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rn x = getr regs x) ->
    (forall r : reg, In (u r) fs_list -> reg_get frn r = reg_get fr r) ->
    (ocomp C A An mn cr dr w h) ->
    (ocomp C A An mn cg dg w h) ->
    (ocomp C A An mn cb db w h) ->
    (forall q, cblk cr dr q -> cblk cg dg q -> False) ->
    (forall q, cblk cr dr q -> cblk cb db q -> False) ->
    (forall q, cblk cg dg q -> cblk cb db q -> False) ->
    (forall q, ~ cblk cr dr q -> ~ cblk cg dg q -> ~ cblk cb db q -> live An q = live A q) ->
    (aroom An vmn (kR - 3 * K1) (bR - 3 * B1)) ->
    realizes SEGS (mkCfg (@mkst (mkFP frn csn) rn (240964 : word) mn al_rom) (with_vmmaps vmn md)) S.
Proof.
  intros frn csn An mn vmn rn cr dr cg dg cb db HWn Hzn PMn SUBn CZn Rcr Rcg Rcb PXn KOs KGs KOr
         G2 G9 G8 G18 G19 G20 GR GFS OCr OCg OCb Xrg Xrb Xgb LVn RMn.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in T5.
  pose proof (fz_u_rng (c_sp0 C)) as USP.
  unfold BEX_STACK, BGE_STACK, AMB_STACK, LSF in Hlo.
  assert (AT64 : (alloc_top (c_vm C) + 64 <= 2 ^ 64)%Z) by lia.
  assert (S80 : (80 <= s)%Z) by lia.
  assert (S64 : (s < 2 ^ 64)%Z) by lia.
  change (RK_bex 32) with (3 * (RK_pix + RK_bge) + RK_pix)%Z in Hrk.
  change (RB_bex w h 32) with (3 * (RB_pixT (4 * (wpl_of w 8 * h)) + RB_bge w h) + RB_pixT (4 * (wpl_of w 32 * h)))%Z in Hrb.
  pose proof (pbl_m16_8 s Hs16) as Hs8.
  assert (HWPL : (0 < 4 * (wpl_of w 8 * h))%Z).
  { assert (WP8 : (1 <= wpl_of w 8)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia). nia. }
  destruct (bx_F0 al_rom (mkFP frn csn) rn mn cr cg cb G19 G20 G8) as (r0 & M0 & F10 & F11 & F12 & F1r & AG0).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWn)) | exact (mp_lazy _ (w_pure _ _ _ _ HWn)) | exact M0 |]. clear M0.
  replace (0x1cae0 : word) with (Z_to_bv 64 PC_pixCreateRGBImage) by (apply bv_eq; reflexivity).
  apply (pixCreateRGBImage_W (fx := mkFP frn csn) C An mn (with_vmmaps vmn md) r0 (s - 80)%Z cr cg cb w h (Z_to_bv 64 0x3ad54) S CK HWn
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CRI_STACK, LSF; lia) ltac:(lia)
           F1r ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) F10 F11 F12
           (ocomp_rgb _ _ _ _ _ _ _ _ OCr) (ocomp_rgb _ _ _ _ _ _ _ _ OCg) (ocomp_rgb _ _ _ _ _ _ _ _ OCb) HOK Hw1 Hh1
           (kR - 3 * K1)%Z (bR - 3 * B1)%Z ltac:(rewrite with_vmmaps_vmmaps; exact RMn) ltac:(lia) ltac:(lia)).
  intros A1 m1 vm1 r1 HW1 CS1 PM1 OUT RM1.
  rewrite with_vmmaps_twice in HW1 |- *.
  replace (Z_to_bv 64 0x3ad54) with (0x3ad54 : word) by (apply bv_eq; reflexivity).
  assert (SUB1 : sub_live An A1).
  { destruct OUT as [[_ LQ] | (pixd & datad & _ & PN)].
    - apply sub_live_eq. exact LQ.
    - destruct PN as (_ & _ & _ & _ & _ & _ & _ & L0p & L0d & _ & _ & L1p & L1d & LEQ & _).
      exact (sub_live_new2 An A1 _ _ _ _ L0p L0d L1p L1d LEQ). }
  assert (D0 : exists d0, getr r1 10 = Z_to_bv 64 d0) by (exists (u (getr r1 10)); rewrite Z_to_bv_bv_unsigned; reflexivity).
  destruct D0 as [d0 G10].
  assert (SUBA1 : sub_live A A1) by exact (sub_live_trans A An A1 SUBn SUB1).
  assert (OCr1 : ocomp C A A1 m1 cr dr w h)
    by (apply (fz_oc_step C A An A1 An mn m1 cr dr w h OCr (proj2 PM1) AT64); [intros q k _ L; exact L | intros q k _ L; exact (SUB1 q k L)]).
  assert (OCg1 : ocomp C A A1 m1 cg dg w h)
    by (apply (fz_oc_step C A An A1 An mn m1 cg dg w h OCg (proj2 PM1) AT64); [intros q k _ L; exact L | intros q k _ L; exact (SUB1 q k L)]).
  assert (OCb1 : ocomp C A A1 m1 cb db w h)
    by (apply (fz_oc_step C A An A1 An mn m1 cb db w h OCb (proj2 PM1) AT64); [intros q k _ L; exact L | intros q k _ L; exact (SUB1 q k L)]).
  destruct (bx_F1 al_rom (mkFP frn csn) r1 m1 s d0 ltac:(csr; reflexivity) G10) as (r2 & M2 & K2 & K8 & K10 & K1r & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact M2 |]. clear M2.
  assert (RS1 : rdn SEGS m1 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 cr))
    by (rewrite (FRM_rdn16 C (s - 80) mn m1 (s - 64) 8 CK (proj1 PM1)) by lia; exact Rcr).
  apply (pixDestroy_ocomp_W (mkFP frn csn) C A A1 m1 (with_vmmaps vm1 md) r2 (s - 80)%Z (s - 64)%Z cr dr w h (0x3ad60 : word) S CK HW1
           K2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)
           ltac:(rewrite K1r; apply bv_eq; reflexivity) ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) K10
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs8; reflexivity) ltac:(lia) ltac:(lia) RS1 OCr1 HWPL).
  intros A2 m2 vm2 r3 HW2 CS2 D2a D2b SUB2 PD2 RT2.
  rewrite with_vmmaps_twice in HW2 |- *. rewrite with_vmmaps_vmmaps in RT2.
  assert (PM2 : POSTM C A2 (s - 56) m1 m2)
    by (apply (POSTD_POSTM_win C A2 m2 _ (s - 80) (s - 56) (s - 64) m1 CK HW2); [lia | lia | lia | lia | exact PD2]).
  assert (RS2 : rdn SEGS m2 (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 cg)).
  { pose proof (POSTD_rdn_above C A2 (s - 80) (s - 64) m1 m2 (s - 72) 8 CK PD2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as X2.
    rewrite ?p16_segs in X2. rewrite X2. rewrite (FRM_rdn16 C (s - 80) mn m1 (s - 72) 8 CK (proj1 PM1)) by lia. exact Rcg. }
  assert (OCg2 : ocomp C A A2 m2 cg dg w h).
  { apply (fz_oc_step C A A1 A2 A2 m1 m2 cg dg w h OCg1 (proj2 PM2) AT64);
      intros q k Cq L; rewrite D2b by (intros Cr; exact (Xrg q Cr Cq)); exact L. }
  assert (OCb2 : ocomp C A A2 m2 cb db w h).
  { apply (fz_oc_step C A A1 A2 A2 m1 m2 cb db w h OCb1 (proj2 PM2) AT64);
      intros q k Cq L; rewrite D2b by (intros Cr; exact (Xrb q Cr Cq)); exact L. }
  destruct (bx_F2 al_rom (mkFP frn csn) r3 m2 s ltac:(csr; reflexivity)) as (r4 & M4 & L2 & L10 & L1r & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact M4 |]. clear M4.
  apply (pixDestroy_ocomp_W (mkFP frn csn) C A A2 m2 (with_vmmaps vm2 md) r4 (s - 80)%Z (s - 72)%Z cg dg w h (0x3ad68 : word) S CK HW2
           L2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)
           ltac:(rewrite L1r; apply bv_eq; reflexivity) ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) L10
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs8; reflexivity) ltac:(lia) ltac:(lia) RS2 OCg2 HWPL).
  intros A3 m3 vm3 r5 HW3 CS3 D3a D3b SUB3 PD3 RT3.
  rewrite with_vmmaps_twice in HW3 |- *. rewrite with_vmmaps_vmmaps in RT3.
  assert (PM3 : POSTM C A3 (s - 56) m2 m3)
    by (apply (POSTD_POSTM_win C A3 m3 _ (s - 80) (s - 56) (s - 72) m2 CK HW3); [lia | lia | lia | lia | exact PD3]).
  assert (RS3 : rdn SEGS m3 (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 cb)).
  { pose proof (POSTD_rdn_above C A3 (s - 80) (s - 72) m2 m3 (s - 80) 8 CK PD3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as X3.
    pose proof (POSTD_rdn_above C A2 (s - 80) (s - 64) m1 m2 (s - 80) 8 CK PD2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as X2.
    rewrite ?p16_segs in X3, X2. rewrite X3, X2. rewrite (FRM_rdn16 C (s - 80) mn m1 (s - 80) 8 CK (proj1 PM1)) by lia. exact Rcb. }
  assert (OCb3 : ocomp C A A3 m3 cb db w h).
  { apply (fz_oc_step C A A2 A3 A3 m2 m3 cb db w h OCb2 (proj2 PM3) AT64);
      intros q k Cq L; rewrite D3b by (intros Cg; exact (Xgb q Cg Cq)); exact L. }
  destruct (bx_F3 al_rom (mkFP frn csn) r5 m3 s ltac:(csr; reflexivity)) as (r6 & M6 & N2 & N10 & N1r & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact M6 |]. clear M6.
  apply (pixDestroy_ocomp_W (mkFP frn csn) C A A3 m3 (with_vmmaps vm3 md) r6 (s - 80)%Z (s - 80)%Z cb db w h (0x3ad70 : word) S CK HW3
           N2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)
           ltac:(rewrite N1r; apply bv_eq; reflexivity) ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) N10
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs8; reflexivity) ltac:(lia) ltac:(lia) RS3 OCb3 HWPL).
  intros A4 m4 vm4 r7 HW4 CS4 D4a D4b SUB4 PD4 RT4.
  rewrite with_vmmaps_twice in HW4 |- *. rewrite with_vmmaps_vmmaps in RT4.
  assert (PM4 : POSTM C A4 (s - 56) m3 m4)
    by (apply (POSTD_POSTM_win C A4 m4 _ (s - 80) (s - 56) (s - 80) m3 CK HW4); [lia | lia | lia | lia | exact PD4]).
  assert (CZ4 : cellsZ m4 (framex s ret regs)).
  { apply (cellsZ_frm C (s - 56) m3 m4 _ CK (proj1 PM4) ltac:(lia) (fz_fx s ret regs (s - 56) S80 S64 ltac:(lia))).
    apply (cellsZ_frm C (s - 56) m2 m3 _ CK (proj1 PM3) ltac:(lia) (fz_fx s ret regs (s - 56) S80 S64 ltac:(lia))).
    apply (cellsZ_frm C (s - 56) m1 m2 _ CK (proj1 PM2) ltac:(lia) (fz_fx s ret regs (s - 56) S80 S64 ltac:(lia))).
    apply (cellsZ_frm C (s - 80) mn m1 _ CK (proj1 PM1) ltac:(lia) (fz_fx s ret regs (s - 80) S80 S64 ltac:(lia))).
    exact CZn. }
  destruct (bx_E al_rom (mkFP frn csn) r7 regs m4 s d0 ret S80 S64 Hret CZ4 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r8 & M8 & E2 & E1 & E10 & ER & AG8).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact M8 |]. clear M8.
  assert (CSK : cs_kept regs r8) by (apply cs_kept_intro; csr; reflexivity).
  pose proof (fz_oc_none _ _ _ _ _ _ _ _ OCr) as NAr.
  pose proof (fz_oc_none _ _ _ _ _ _ _ _ OCg) as NAg.
  pose proof (fz_oc_none _ _ _ _ _ _ _ _ OCb) as NAb.
  assert (SUBA2 : sub_live A A2).
  { intros q k L. rewrite D2b by (intros Cr; rewrite (NAr q Cr) in L; discriminate L). exact (SUBA1 q k L). }
  assert (SUBA3 : sub_live A A3).
  { intros q k L. rewrite D3b by (intros Cg; rewrite (NAg q Cg) in L; discriminate L). exact (SUBA2 q k L). }
  assert (SUBA4 : sub_live A A4).
  { intros q k L. rewrite D4b by (intros Cb; rewrite (NAb q Cb) in L; discriminate L). exact (SUBA3 q k L). }
  assert (PMf : POSTM C A s m m4).
  { apply (POSTM_trans C A s m mn m4 PMn).
    apply (POSTM_trans C A s mn m1 m4 (POSTM_sub C A An s mn m1 SUBn (POSTM_mono C An (s - 80) s mn m1 ltac:(lia) PM1))).
    apply (POSTM_trans C A s m1 m2 m4 (POSTM_sub C A A2 s m1 m2 SUBA2 (POSTM_mono C A2 (s - 56) s m1 m2 ltac:(lia) PM2))).
    apply (POSTM_trans C A s m2 m3 m4 (POSTM_sub C A A3 s m2 m3 SUBA3 (POSTM_mono C A3 (s - 56) s m2 m3 ltac:(lia) PM3))).
    exact (POSTM_sub C A A4 s m3 m4 SUBA4 (POSTM_mono C A4 (s - 56) s m3 m4 ltac:(lia) PM4)). }
  assert (LG4 : forall q, ~ cblk cr dr q -> ~ cblk cg dg q -> ~ cblk cb db q -> live A4 q = live A1 q).
  { intros q Nr Ng Nb. rewrite (D4b q Nb), (D3b q Ng), (D2b q Nr). reflexivity. }
  assert (LF4 : forall q, cblk cr dr q \/ cblk cg dg q \/ cblk cb db q -> live A4 q = None).
  { intros q [Cq | [Cq | Cq]].
    - rewrite (D4b q (fun Cb => Xrb q Cq Cb)), (D3b q (fun Cg => Xrg q Cq Cg)). exact (D2a q Cq).
    - rewrite (D4b q (fun Cb => Xgb q Cq Cb)). exact (D3a q Cq).
    - exact (D4a q Cq). }
  assert (LA4 : forall q, (live A4 q = live A1 q /\ live An q = live A q) \/ (live A4 q = None /\ live A q = None)).
  { intros q.
    destruct (cblk_dec cr dr q) as [Cr | Nr]; [right; split; [apply LF4; left; exact Cr | exact (NAr q Cr)] |].
    destruct (cblk_dec cg dg q) as [Cg | Ng]; [right; split; [apply LF4; right; left; exact Cg | exact (NAg q Cg)] |].
    destruct (cblk_dec cb db q) as [Cb | Nb]; [right; split; [apply LF4; right; right; exact Cb | exact (NAb q Cb)] |].
    left. split; [exact (LG4 q Nr Ng Nb) | exact (LVn q Nr Ng Nb)]. }
  assert (RMf : aroom A4 vm4 (kR - RK_bex 32) (bR - RB_bex w h 32)).
  { change (RK_bex 32) with (3 * (RK_pix + RK_bge) + RK_pix)%Z.
    change (RB_bex w h 32) with (3 * (RB_pixT (4 * (wpl_of w 8 * h)) + RB_bge w h) + RB_pixT (4 * (wpl_of w 32 * h)))%Z.
    apply (fz_rt0 _ _ _ _ _ _ RT4). apply (fz_rt0 _ _ _ _ _ _ RT3). apply (fz_rt0 _ _ _ _ _ _ RT2).
    pose proof (aroom_nonneg _ _ _ _ RM1) as [NN1 NN2].
    apply (aroom_mono _ _ _ _ _ _ RM1); lia. }
  destruct OUT as [[R10 LQ] | (pixd & datad & R10 & PN)].
  - apply (KN frn csn A4 m4 vm4 r8 HW4 Hzn CSK PMf).
    + rewrite E10, <- G10. exact R10.
    + intros q. destruct (LA4 q) as [[E4 EA] | [E4 EA]]; [rewrite E4, LQ; exact EA | rewrite E4, EA; reflexivity].
    + exact GFS.
    + exact RMf.
  - destruct PN as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & L0p & L0d & L00p & L00d & L1p & L1d & LEQ & PXd & PD).
    assert (NCp : forall c dc, ocomp C A An mn c dc w h -> ~ cblk c dc (Z_to_bv 64 pixd))
      by (intros c dc OC; exact (fz_notc _ _ _ _ _ _ _ _ _ OC L0p)).
    assert (NCd : forall c dc, ocomp C A An mn c dc w h -> ~ cblk c dc (Z_to_bv 64 datad))
      by (intros c dc OC; exact (fz_notc _ _ _ _ _ _ _ _ _ OC L0d)).
    assert (L2p : live A2 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite D2b by exact (NCp _ _ OCr); exact L1p).
    assert (L3p : live A3 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite D3b by exact (NCp _ _ OCg); exact L2p).
    assert (L4p : live A4 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite D4b by exact (NCp _ _ OCb); exact L3p).
    assert (L4d : live A4 (Z_to_bv 64 datad) = live A1 (Z_to_bv 64 datad)) by exact (LG4 _ (NCd _ _ OCr) (NCd _ _ OCg) (NCd _ _ OCb)).
    apply (KP frn csn A4 m4 vm4 r8 pixd datad HW4 Hzn CSK PMf).
    + rewrite E10, <- G10. exact R10.
    + refine (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7
             (conj (fz_subnone _ _ _ SUBn L0p) (conj (fz_subnone _ _ _ SUBn L0d) (conj L00p (conj L00d
             (conj L4p (conj (eq_trans L4d L1d) (conj _ (conj _ PD))))))))))))))).
      * intros q Q1 Q2. destruct (LA4 q) as [[E4 EA] | [E4 EA]]; [rewrite E4, (LEQ q Q1 Q2); exact EA | rewrite E4, EA; reflexivity].
      * apply (PIXat_frame m3); [| intros x Hx; exact (LIVK_at A4 m3 m4 pixd 64 x (proj2 PM4) L4p ltac:(lia) ltac:(lia) Hx)].
        apply (PIXat_frame m2); [| intros x Hx; exact (LIVK_at A3 m2 m3 pixd 64 x (proj2 PM3) L3p ltac:(lia) ltac:(lia) Hx)].
        apply (PIXat_frame m1); [exact PXd | intros x Hx; exact (LIVK_at A2 m1 m2 pixd 64 x (proj2 PM2) L2p ltac:(lia) ltac:(lia) Hx)].
    + exact GFS.
    + exact RMf.
Qed.

(* [comment removed for export] *)
Lemma main32 : forall ra M1,
    W C A M1 md ->
    (POSTM C A s m M1) ->
    (cellsZ M1 (framex s ret regs)) ->
    (PIXat M1 pixs (hdv w h 32 0 datas)) ->
    (kobj C A M1 skel arrs 41 41 rowss) ->
    (korg M1 skel 20 20) ->
    (kobj C A M1 rkel arrr 1 256 rowsr) ->
    (getr ra 2 = Z_to_bv 64 (s - 80)) ->
    (getr ra 1 = Z_to_bv 64 240844) ->
    (getr ra 10 = Z_to_bv 64 pixs) ->
    (getr ra 11 = Z_to_bv 64 0) ->
    (getr ra 9 = Z_to_bv 64 pixs) ->
    (getr ra 8 = Z_to_bv 64 skel) ->
    (getr ra 18 = Z_to_bv 64 rkel) ->
    (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr ra x = getr regs x) ->
    realizes SEGS (mkCfg (@mkst (mkFP fr cs) ra (Z_to_bv 64 PC_pixGetRGBComponent) M1 al_rom) md) S.
Proof using All.
ltac2:(KReplay.run1 (kr_t_V2LeptBexW ()) ["BexW"; "Main32"] "p'0h02H0h11Hh21bh31xi001xh41eh51qh62b1h72b2h81nh91rh:5regs'h;3HW1h<2Hxh=3RUNh>7__arithh?7__sat19h@4__x1hA4__x2hB4__x3hC2mdhD3AGphE3AGqhF2AbhG2AchH2AdhI5CDgbdhJ5CDrbdhK5CDrgchL5CDrgdhM3FRahN3FRbhO3FRchP3FRdhQ3FSbhR3FSchS3FSdhT3FZbhU3FZchV3FZdhW3HWbhX3HWchY3HWdhZ4KGsah[4KGsbh\4KGsch]4KGsdh^4KOrah_4KOrbh`4KOrcha4KOrdhb4KOsahc4KOsbhd4KOsche4KOsdhf4LIVbhg4LIVchh4LIVdhi2M1hj2Mbhk2Mchl2Mdhm3NNbhn3NNkho4OCbdhp4OCgchq4OCgdhr4OCrbhs4OCrcht4OCrdhu2P1hv3P10hw3P11hx3PMahy3PMbhz3PMch{3PMdh|3PXah}3PXbh~3PXci013PXdi022Q1i033Q10i043Q11i053RMbi063RMci073RMdi083RRai093RRbi0:3RRci0;3RRdi0<3Ra1i0=4Ra10i0>4Ra11i0?4Ra18i0@3Ra2i0A3Ra8i0B3Ra9i0C4Rb18i0D4Rb19i0E3Rb2i0F3Rb8i0G3Rb9i0H4Rc18i0I4Rc19i0J3Rc2i0K4Rc20i0L3Rc8i0M3Rc9i0N4Rd18i0O4Rd19i0P3Rd2i0Q4Rd20i0R3Rd8i0S3Rd9i0T4SLbdi0U4SLgci0V4SLgdi0W4SLrbi0X4SLrci0Y4SLrdi0Z4SUBbi0[4SUBci0\4SUBdi0]4__ffi0^8__varmapi0_5__witi0`2cbi0a2cgi0b3cg2i0c2cri0d3cr1i0e3cr2i0f3csbi0g3csci0h3csdi0i2dbi0j2dgi0k3dg2i0l2dri0m3dr1i0n3dr2i0o3frbi0p3frci0q3frdi0r2rai0s2rbi0t3rb2i0u2rci0v3rc2i0w2rdi0x3vmbi0y3vmci0z3vmdi0{1pi0|1zp%0p%1p%2p&0p;1p;2p;3p;9p;5p;;p;4p;8p;6p;7p;<p;Xp;Vp;Pp;Kg006Qj1<Tg00P`j1ATg0076j1mTg007Tj1PTg00QEk20gTg009>j1{Tg003>k30UTg02eKl9lTg00Sgk30GTg00Tcj2kTg00EWj1?Tg02`Tk50@Tg00U\j3sTg00Vcl;XTg00Wbj4pTg00X^j2@Tg00YAj3JTg00GVj2oTg00HMj2:Tg00Ydk106Tg00ZDj3gTg00Z[j21Tg02T6k10FTg01Z\k80DTg016lS00j2^Tg00cij2DTg00dgk10CTg025fj5=Tg00R1j2CTg03nOk10?Tg001<j63Tg02>Bk40fTg00[Tj27Tg00\>j2qTg00;_j28Tg004Gk30]Tg009`j4]Tg00E:j2}Tg00\hk20\Tg00cLj2|Tg00]nk10[Tg00_6k20ZTg01Bek20YTg00hck20XTg00?Rk10:Tg02jLk209Tg02mFk40WTg01D4k10VTg01DRk10TTg01E=k20STg01IGj2zTg00:ck10RTg02kNk30QTg030\k30PTg02mdk30OTg02nGk70NTg02jjk80MTg01E`k20LTg01Fnk30KTg01GMk40JTg00D>k207Tg02]Bm<0ITg005Pk20HTg00Rkj1vTg0087j5uTg00a8j1WTg00aWj2hTg00<9j2iTg00;Ej30Tg026_j3aTg00bTl;bTg02H2j3ITg016Sj1dTg00`4j7tTg03oTk60ETg027?S01k204Tg027Yj3MTg028Um902Tg029Zk205Tg02:Yk201Tg01\Ok30BTg00H3R0j22Tg00<[k20ATg000`j6;Tg040Qk60>Tg041NmX0eTg042FmV0dTg02_Vm90=Tg043?mP0cTg0448mK0bTg02dIk80aTg02fOk200Tg02gDj3~Tg02i=k40`Tg02ihk70_Tg00I3k40^Tg0377k30;Tg02aNk30<Tg02bhj3rTf6R1f5R2f4R3g00MSS02f3R4f2R5f1R6f0R7L0ap=c%<7#?p=H1156=047p=6%A7#Ap=F%<7#Ap=N%<7#A#A#<p=OAJ456=a37p=Rg039[R80077p=Zg00ONS0320056;~7p>081|67,o5p=Qg00=_R9P6g03<_P7H0`p=yP6g03:9R:g03:XR;P;g03;8R<P7g03<?K0_p=xQ03P5P6P7H0^p=eg00?6R=9J67p=>Aa5679a34p=_%A7#<p=\Q03P2P3P4P5P6D=<0;7p=V%<7#<p=[A0234AM567'^p=GA0456/^7p=`1^67,^5p=EQ03P3P4P5P6P7D=80;2p>03Q031C56-004;~7p=jQ03f7R>/D1P2P3P4P5D=0006;~7p=SA0967p=4g00>YR?,27p=BP9P4P5P=P6P7E;p=51:679045p=wA0234A0567/2?'2p=YA0123A0456/27'2p=911451167503p=L1867:0<45p=fA0567/2?p=TA02341256;r7p=UB0<5679r34p=nAr5679r34p=Kg00=:R@#<RA#ARB#mRC%<ARD#<RE#<RF#<RG#<RH#mRI#PRJ+0gRK%mE#PRL#{\JS04p,2ALRMp,2CLRNp,3ASRRO:0UMNRPp,1CRQp,1ARRP7p,2mdRSFcPMPNPPQ02PQPRp,1sRTp,1mS05P6M9lp,3retp,4regsRU60GTS06,k5p,4pixsS07p,1wS08p,1hS09%?GP8p,5datasI0@S0:5s4PMPNPOPQPRP3p,4skelS0;p,4arrsS0<%<BRV#<RW#A#?S0=Q0=p,5rowssS0>M;XP2Q0;%?WS0?Q0?CpPMPNPOPQPRP1p,4rkelS0@p,4arrrS0A%?@RX%<H#HS0Bp,5rowsrS0CM;XPJf8RY%?AS0DP=Q0D,@Cd5JC%<W#H,oT,:IS0EC6PJf9RWP=1@CXd9JCXRZ%F@#N#O#O#O#H,:IC6PJf:R[%?VR\P=1@C\d5JCR]Q07,:IR^C6PJf;S0F%ABRB#?R_P=1@C_d5JCR`1:I8C6PJf<Ra%ADRb#?S0GP=Q0G,@Cd5JCP^C6PJf=Rc%?ES0HP=Q0H,@Cd5JCQ0;,:IS0IC6PJf>S0J%<bS0K#?S0LP=Q0L,@Cd5JCQ0@,:IS0MC6%PCREPEPC%A@Rd#?S0NP=Q0N,@CdPEPC%?DS0OP=Q0O,@CdPEPC%AV#?S0PP=Q0P,@CdPEPC%HBS0QP=Q0Q,@CdPEPC%AB#?S0RP=Q0R,@CdPEPC%<dRB#<RV#HS0SP=Q0S,@CdPEPC%AV#?S0TP=Q0T,@CdPEPC%ABRB#HS0UP=Q0U,@CdPEPC%AB#?S0VP=Q0V,@Cd&06ERBDRDRDRDRDRDRDRDRDR9gE7PJfAS0WP611U6S0XC6[]3PMPNPOPR&0FSRVp,2kRS0Yp,2bRS0Zp,3HrmRDL0DQ0Y#ZS0[Q0Z#ZS0\'^Q00Q0[Q0\p,2frRep,2csRf'DRgfBRhg03Dg,:IS0]Q0W&0CMRiD=p,1SRj808SP7Q0[Q0\g03JSRk1CVSRlPgfFS0^Q0]fES0_PiD=@087jXCkPkPSPMPNPPPQPRQ0_P7FcXCkfCS0`Pl&0?SS0aE3PMPNPPPQPRfDS0bPlFcPePfPRQ0_PVQ0^P7p,2HzQ0`PMPNPPPRH0fPhQ0Wf@S0cf?S0dQ0JPcPaQ0FP[PWPYP>P117C7g03A>5g9S0e1qe6S0f,8JUX9E%{9S0gPMB0]MNPS0hPRP7C]'8X5JPMPNPOPRPVQ0YQ0ZQ0Yg03BERVg03CJRe'}S0i7Q8Q0ZQ0OQ08Q0H+0\Q09'|'|$0[RfQ08Q09+0ZRl'}S0j7Q8PD%?FRF-0YTRD%ZT%ZF20XTF#Z[[RFg03=FRk$06&0:kP920995P620994H0W&0V9&0T9RkP:P;P;P<20S98Rg1z9@Rm'y,xk&0R;PkP:P;P;P<1z9A1z9d60Q9:0P9g:0O9mRd,yg,xk1ydm,xkK0NL0M20Lk<P7P5g03I5g03IU'8B0K986H0Jc0]c0^c0_X@9XA9XB9Rk%Z71}549Q68R8#Z20786'^[^@9^A9^B9R8P7PePVQ0YP3O4b>b?PDPFPkP8P7PlPfQ0ZP4O4b>b?N<0I%mG#PS0kQ0h-0HMS0lQ04g03@GS0mPMPNPPPQP2P31C4SFc%v>PMPNPPQ02PQPRPTQ05P1M9lPMPNPPPRPYDuQ06,kY&0:LS0n#{S0o%?H,oT,:IS0pg03DH#W#W#W#W#W#W#W#WRH5eWQ0n1hH1'i30Q07Q0:5s[PMPNPOPQPaQ0FQ0;Q0<Q0=Q0=Q0>M;XPaQ0;Q0?Q0?CpPMPNPOPQQ0JPcQ0@Q0APXQ0BQ0CM;XPJPaQ0D,>CRLQ0EC6PJPcQ0G,>CRGP^C6PJQ0JQ0H,>CRfQ0IC6PJQ0dQ0L,>CRlQ0MC6PJQ0c%Ab#?S0q,>CRbQ0d,:IS0rC6PEQ0N,>CR8PEQ0O,>CRkPEQ0P,>CRFPEQ0Q,>CRDPEQ0R,>CRVPEQ0S,>CRePEQ0T,>CR<PEQ0U,>CRdQ0V,>CRm=aEBD_D_D_D_9gE7S0sPJQ0`P6Q0XC6[^3EQ0efIRg/q6Q0f50J[^9EPMPNPOPQPRQ0^Q0_PhQ0WQ08Q09M;bQ0bQ0`;I7#dQ0gPMQ0hPgP6C]PMQ0hPRP6C]30[^5JPMPNPOfHRAQ0^Q0YQ0i7QXQ0ZQ0j7QXFtPifKR;fJR:'DQ0^PAQ07PYJ0EfLRn/D;RofGRp%F@#N#O#N#F#O#HRqP=1@Iqd5JIPJePgPiPoP7%A@#O#\#F#F#F#\#HRoP=1@Iod5JIPJeS0tPgPiD=EVPJP7P]P^C6S0uPJ117`S0v1:IXRrPJ117ZS0w%F@#N#O#N#F#F#[#H,:IRsPEPZPEP]AaE`BD_9gE7X3ES0xPpP7EGC`3EX:K-04KQ01PKfMR`/DnR]PA1>IqRqP:PiD=RZP]P71>IoRoP:PiJ03PJP71>C\R]P^C6S0y1>C_Rt,17S0z=0JrRu1>CXRv,17S0{=0JsRwPEPvPEP]AaEtBD_9gE7X3ERB?MA73E3EX:KPZPgPSPjCjP7fORZfNRx'DRyP:PqPnPiPyP7PoPnPiD=EVQ0yAMB:79Euw3EQ00fPRw/DZRuP;PqP`PiPuP6PoP`PiD=EVPJP6P]P^C6S0|116tS0}=0JrPJ116vS0~PsPBP;P6EG3EfQS10/DwS11PnPqPxPiD=P`PSPjCjP7fRS12Q10'DS13P`PqPZPiQ13P4PoPZPiD=EVPJP3P]P^C6S14113tS15=0JrPJ113vS16PsPBPxP3EG3EQ00PJP2P]P^C6S17PJ112tS18PrPJ112vS19PsPBPZP2EGC`fUS1:fTS1;'DS1<PwPqQ12PiD=Q10PSPjCjP7PJP>P]P^C6S1=PJ11YtS1>PrPJ11YvS1?PsPBQ12PYEGC`Q0011WtS1@=0JrPJ11WvS1APsPBfSS1BPWEGfYS1CfXS1DQ1;PqfVS1EPiQ1:/CSPjGSP7Q0F/1tS1F=0JrPJ11avS1GPsPBQ1EPaEGQ0011cvS1H=0JsfWS1I=MBcf]S1Jf\RrQ1DPqfZS1KPiQ1C/CSPjGSP7Q0d/1vS1L=0JsQ1KQ0c5MBQ03f`S1Mf_S1N'DRsf[S1OPqQ1JPiD=PsQ0WPoQ1JPiD=1CrSRsPjPMPNPPQ02PQf^S1PQ1JPsQ1DN902Rq-05s201sqPcg03J5Rq%P7Rs%P6RuQ00%P5?06717451746'4Ry[Rz17561757'4%P4?056R{[R|%P3?045\yB0B567S1QP7n2001000000120000000W7W6W8P|^7u^6s^8qP7PIQ0]Po17Io,89O4b1S1RQ0]PoPJe50JS1SPJQ0]fbRyfaS1TQ0`P7Q1NPiQ1P/CSPjGSX2JQ1TQ1MQ1NQ1PQ1JPhQ1OQ1KQ1CQ1DQ1IQ1EQ1:Q1;Q1BQ12Q10PwPJ11rLR}Q0E90J7X2JS1UPJQ0EQ1UQ0E,8JS1VP}PZE311hLS1WP6PLA0EvLR}A0E]LS1XA0EtLS1Y#BS1Z'2R~'2P0P}P~P?P7Q00PzP|17341735'4\{Q1QP6n2001000000120000000X7uX6sX8qR{Pz^7u^6s^8qRqP7PCPvPLP6O417CvRs17CLS1Q'4PXP9p-0RuP7P?g03O4S1[PuP7P?P?g00>=S1\n0110{0003100001000000S1]P?n0110|0003001010{1010{X49RzQ0DP7C5P?20A?7R|b0b1b0P0Q1XQ1ZP?P7P{PqP7PCP]PLP6O417C]R~Q1Q'4P\P9PuP7P?Q1[PuP7P?Q1[PuP7Q1\P?P?n0110{0003100001000000S1ZP?n0110{00031010{1010{00P?n0110|0003001010{1010{X49S1XQ0DP7C5P?P|b0b1b0P0Q1YP?P?P7P{PqP7PCPtPLP6O417CtR}Q1Q'4P_P9PuP7P?Q1ZP?n0110|0003001010{1010{X49S1QQ0DP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000010000n200100000021000011000W1O2S1YE3P5P[P1PJ11rGS1^A0J7^X2JS1_PJP^Q1_18J^S1`Q1^PxE311hGS1^P6PGA0EvGS1aA0E]GS1bA0EtGS1c#BS1d'2S1e'2P0Q1aQ1eP?P7P{PqP7PCPvPGP6O417CGS1e,4sPXPzQ0GP7C5P?P|b0b1b0P0Q1bQ1dP?P7P{PqP7PCP]PGP6O4Q1e,4~P\P9PuP7P?Q1[PuP7P?Q1\P?n0110{0003100001000000S1\P?n0110|0003001010{1010{X49S1dQ0GP7C5P?P|b0b1b0P0Q1cP?P?P7P{PqP7PCPtPGP6O4Q1e,4}P_P9PuP7P?Q1[PuP7Q1ZP?P?n0110{00031010{1010{00P?n0110|0003001010{1010{X49S1ZQ0GP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000011000n200100000021000011000W1O2S0GE3PJ11rfS1eQ0I90J7X2JS1cPJQ0IQ1cQ0I,8JS1bQ1eP`E311hfS1eP6PfA0EvfS1aA0E]fS1fA0EtfS1g#BS1h'2S1i'2P0Q1aQ1iP?P7P{PqP7PCPvPfP6O417CfS1i,4sPXPzQ0HP7C5P?P|b0b1b0P0Q1fQ1hP?P7P{PqP7PCP]PfP6O4Q1i,4~P\Q1XQ0HP7C5P?P|b0b1b0P0Q1gP?P?P7P{PqP7PCPtPfP6O4Q1i,4}P_Q1QQ0HP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000011000n200100000021000011000W1O2S0HE3PJ11rlS1iQ0M90J7X2JS1gPJQ0MQ1gQ0M,8JS1hQ1iPnE311hlS1iP6PlA0EvlS1fA0E]lS1aA0EtlS1j#BS1k'2S1l'2P0Q1fQ1lP?P7P{PqP7PCPvPlP6O417ClS1l,4sPXPzQ0LP7C5P?P|b0b1b0P0Q1aQ1kP?P7P{PqP7PCP]PlP6O4Q1l,4~P\P9PuP7P?Q1[PuP7P?Q1[PuP7Q1[PuP7P?Q1]P?n0110{00031010{1010{00P?P?n0110{00031010{1010{00S1]P?n0110{00031010{1010{00P?n0110|0003001010{1010{X49S1kQ0LP7C5P?P|b0b1b0P0Q1jP?P?P7P{PqP7PCPtPlP6O4Q1l,4}P_Q1QQ0LP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000011000n200100000021000011000W1O2S0LE3PJ11rbS1lPJP7PIPrCwX2JS1jPJQ1O,:IS1aQ1jQ1a,8JQ1lP;E311hbS1lP6PbA0EvbS1aA0E]bS1jA0EtbS1f#BS1m'2S1n'2P0Q1aQ1nP?P7P{PqP7PCPvPbP6O417CbS1n,4sPXPzQ0qP7C5P?P|b0b1b0P0Q1jQ1mP?P7P{PqP7PCP]PbP6O4Q1n,4~P\Q1dQ0qP7C5P?P|b0b1b0P0Q1fP?P?P7P{PqP7PCPtPbP6O4Q1n,4}P_P9PuP7P?Q1[PuP7Q1]P?P?n0110{00031010{1010{00P?n0110|0003001010{1010{X49S1]Q0qP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000011000n200100000021000011000W1O2S0qE3Q0sP0A0E86S1nPEPkP6PEPFP6PEPDP6PEPVP6PEPeP6PEP<P6PEPdP6PEPmP6EYF9F9F9S1fPJQ0_P5PUP5DLS1mP7PEP8PJQ0^P711U7S1jC6X3ES1aPJQ1N/18S1o11U8S1p90J7X2JS1qPJQ1pQ1qQ1p,8JS1rQ1oP`P8A0E88PEPkP8PEPFP8PEPDP8PEPVP8PEPeP8PEP<P8PEPdP8PEPmP8EYF9F9F9PEP8CfS1oO2E3Q0_/18S1sP3P8A0Ev8S1tA0E]8S1uA0Et8S1v#BS1w'2S1x'2P0Q1tQ1xP?P7P{PqP7PCPvP8P6O417C8S1x,4sPXPzQ0NP7C5P?P|b0b1b0P0Q1uQ1wP?P7P{PqP7PCP]P8P6O4Q1x,4~P\Q1dQ0NP7C5P?P|b0b1b0P0Q1vP?P?P7P{PqP7PCPtP8P6O4Q1x,4}P_Q1ZQ0NP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000010000n200100000021000011000W1O2S1xE3P5P7E;P0A0Ek5S1vPEPFP5PEPDP5PEPVP5PEPeP5PEP<P5PEPdP5ATEm5F9F9F9S1wPJQ0^P4PUP4DLS1uP7PEPkPJPpP7Q1jC6X3ES1tPJQ1M/1kS1y11UkS1z90J7X2JS1{PJQ1zQ1{PJ%<@#\#F#[#N#[#F#\#[#H,:IS1|A0J77X2JQ1|,8JQ1zp,2H4E3S1|Q1yPxPkPEP8PkA0EkkS1yPEPFPkPEPDPkPEPVPkPEPePkPEP<PkPEPdPkATEmkF9F9F9S1}Q1yQ1}PEPkCfEUS1}O2E3Q0^/1kS1yP2PkA0EvkS1~A0E]kS20A0EtkS21#BS22'2S23'2P0Q1~Q23P?P7P{PqP7PCPvPkP6O417CkS23,4sPXPzQ0OP7C5P?P|b0b1b0P0Q20Q22P?P7P{PqP7PCP]PkP6O4Q23,4~P\Q1XQ0OP7C5P?P|b0b1b0P0Q21P?P?P7P{PqP7PCPtPkP6O4Q23,4}P_Q1QQ0OP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000010000n200100000021000011000W1O2S0OE3P4P7E;P0A0EF4S23PEPDP4PEPVP4PEPeP4PEP<P4PEPdP4PEPmP4EYF9F9S21PJPpP3PUP3DLS22P7PEPFPJPAP7Q1jC6X3ES20PJQ1T/1FS1~11UFS2490J7X2JS25PJQ24Q25Q24,8JS26Q1~PZPFPEP8PFA0EkFS1~A0EFFS27PEPDPFPEPVPFPEPePFPEP<PFPEPdPFPEPmPFEYF9F9S28'2S29Q1~Q29Q27Q2818EFDnEUS28O2E311pFS27P1PFA0EvFS29A0E]FS1~A0EtFS2:#BS2;'2S2<'2P0Q29Q2<P?P7P{PqP7PCPvPFP6O417CFS2<,4sPXPzQ0PP7C5P?P|b0b1b0P0Q1~Q2;P?P7P{PqP7PCP]PFP6O4Q2<,4~P\Q1dQ0PP7C5P?P|b0b1b0P0Q2:P?P?P7P{PqP7PCPtPFP6O4Q2<,4}P_Q1ZQ0PP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000011000n200100000021000011000W1O2S0PE3P3P7E;P0A0ED3S2<PEPVP3PEPeP3PEP<P3PEPdP3ATEm3F9F9S2:PJPAP2PUP2DLS2;P7PEPDPJPgP7Q1jC6X3ES1~PJ11yDS2911UDS2=90J7X2JS2>PJQ2=Q2>Q2=,8JS2?Q29PwPDPEP8PDA0EkDS29A0EFDS2@A0EDDS2APEPVPDPEPePDPEP<PDPEPdPDATEmDF9F9S2B'2S2C'2S2DQ29Q2DQ2@Q2CQ2AQ2BPEPDCfDKEUS2BO2E311ADS2AP>PDA0EvDS2CA0E]DS2@A0EtDS2D#BS29'2S2E'2P0Q2CQ2EP?P7P{PqP7PCPvPDP6O417CDS2E,4sPXPzQ0QP7C5P?P|b0b1b0P0Q2@Q29P?P7P{PqP7PCP]PDP6O4Q2E,4~P\P9PuP7P?Q1[PuP7P?Q1[PuP7Q1\P?P?n0110{00031010{1010{00S1\P?n0110{00031010{1010{00P?n0110|0003001010{1010{X49Q0QP7C5P?P|b0b1b0P0Q2DP?P?P7P{PqP7PCPtPDP6O4Q2E,4}P_Q1QQ0QP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000011000n200100000021000011000W1O2S0QE3P2P7E;P0A0EV2S2EPEPeP2PEP<P2PEPdP2PEPmP2EYF9S2DPJPgP1PUP1DLS29P7PEPVPJP:P7Q1jC6X3ES2@PJfcS2C/1VS2F11UVS2G90J7X2JS2HPJQ2GQ2HQ2G,8JS2IQ2FQ10PVPEP8PVA0EkVS2FA0EFVS2JA0EDVS2KA0EVVS2LPEPePVPEP<PVPEPdPVPEPmPVEYF9S2M'2S2N'2S2O'2S2PQ2FQ2PQ2JQ2OQ2KQ2NQ2LQ2M18EVDnDKEUS2MO2E311gVS2LPYPVA0EvVS2NA0E]VS2KA0EtVS2O#BS2J'2S2P'2P0Q2NQ2PP?P7P{PqP7PCPvPVP6O417CVS2P,4sPXPzQ0RP7C5P?P|b0b1b0P0Q2KQ2JP?P7P{PqP7PCP]PVP6O4Q2P,4~P\Q1dQ0RP7C5P?P|b0b1b0P0Q2OP?P?P7P{PqP7PCPtPVP6O4Q2P,4}P_P9PuP7P?Q1[PuP7Q1\P?P?n0110{00031010{1010{00P?n0110|0003001010{1010{X49Q0RP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000011000n200100000021000011000W1O2S0RE3P1P7E;P0A0Ee1S1\PEP<P1PEPdP1ATEm1F9S1[PJP:P>PUP>DLS2PP7PEPePJP;P7Q1jC6X3ES2OPJfdS2J/1eRu11UeS2K90J7X2JS2NPJQ2KQ2NQ2K,8JS2FPuQ12PePEP8PeA0EkeS2QA0EFeS2RA0EDeS2SA0EVeS2TA0EeeS2UPEP<PePEPdPeATEmeF9S2V'2S2W'2S2X'2S2Y'2RuQ2QPuQ2RQ2YQ2SQ2XQ2TQ2WQ2UQ2VPEPeCfDKDKEUS2VO2E311:eS2UPWPeA0EveS2WA0E]eS2TA0EteS2X#BS2S'2Ru'2P0Q2WPuP?P7P{PqP7PCPvPeP6O417CeRu,4sPXPzQ0SP7C5P?P|b0b1b0P0Q2TQ2SP?P7P{PqP7PCP]PeP6O414~uP\Q1XQ0SP7C5P?P|b0b1b0P0Q2XP?P?P7P{PqP7PCPtPeP6O414}uP_Q1QQ0SP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000011000n200100000021000011000W1O2S0SE3P>P7E;P0A0E<>S2XPEPdP>PEPmP>EYS2SPJP;PYPUPYDLS2TP7PEP<PJPnP7Q1jC6X3ES2WPJfeS2Y/1<Ru11U<S2R90J7X2JS2QPJQ2RQ2QQ2R,8JS2ZPuQ1BP<PEP8P<A0Ek<S2[A0EF<S2\A0ED<S2]A0EV<S2^A0Ee<S2_A0E<<S2`PEPdP<PEPmP<EYS2a'2S2b'2S2c'2S2d'2S2e'2RuQ2[PuQ2\Q2eQ2]Q2dQ2^Q2cQ2_Q2bQ2`Q2a18E<DnDKDKEUS2aO2E311;<S2`P[P<A0Ev<S2bA0E]<S2_A0Et<S2c#BS2^'2Ru'2P0Q2bPuP?P7P{PqP7PCPvP<P6O417C<Ru,4sPXPzQ0TP7C5P?P|b0b1b0P0Q2_Q2^P?P7P{PqP7PCP]P<P6O414~uP\Q1dQ0TP7C5P?P|b0b1b0P0Q2cP?P?P7P{PqP7PCPtP<P6O414}uP_Q1ZQ0TP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000011000n200100000021000011000W1O2S0TE3PYP7E;P0A0EdYS1ZATEmYS2cPJPnPWPUPWDLS2^P7PEPdPJP`P7Q1jC6X3ES2_PJffS2b/1dRu11UdS2d90J7X2JS2]PJQ2dQ2]Q2d,8JS2ePuQ1;PdPEP8PdA0EkdS2\A0EFdS2[A0EDdS2fA0EVdS2gA0EedS2hA0E<dS2iA0EddS2jATEmdS2k'2S2l'2S2m'2S2n'2S2o'2S2p'2RuQ2\PuQ2[Q2pQ2fQ2oQ2gQ2nQ2hQ2mQ2iQ2lQ2jQ2kPEPdCfDKDKDKEUS2kO2E311ndS2jQ0FPdA0EvdS2lA0E]dS2iA0EtdS2m#BS2h'2Ru'2P0Q2lPuP?P7P{PqP7PCPvPdP6O417CdRu,4sPXPzQ0UP7C5P?P|b0b1b0P0Q2iQ2hP?P7P{PqP7PCP]PdP6O414~uP\Q1kQ0UP7C5P?P|b0b1b0P0Q2mP?P?P7P{PqP7PCPtPdP6O414}uP_Q1QQ0UP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000011000n200100000021000011000W1O2S0UE3PWP7E;P0A0EmWS2mP?PJP`P[PUP[DLS1kP7PEPmPJPxP7Q1jC6X3ES1jPJfgS2h/1mRu11UmS2i90J7X2JS2lPJQ2iQ2lQ2i,8JS2nPuQ1:PmPEP8PmA0EkmS2gA0EFmS2oA0EDmS2fA0EVmS2pA0EemS2[A0E<mS2\A0EdmS2qA0EmmS2r#BS2s'2S2t'2S2u'2S2v'2S2w'2S2x'2RuQ2gPuQ2oQ2xQ2fQ2wQ2pQ2vQ2[Q2uQ2\Q2tQ2qQ2sQ2rP?18EmDnDKDKDKEUS2rO2E311`mS2sPaPmA0EvmS2qA0E]mS2tA0EtmS2\#BS2u'2Ru'2P0Q2qPuP?P7P{PqP7PCPvPmP6O417CmRu,4sPXPzQ0VP7C5P?P|b0b1b0P0Q2tQ2uP?P7P{PqP7PCP]PmP6O414~uP\Q1dQ0VP7C5P?P|b0b1b0P0Q2\P?P?P7P{PqP7PCPtPmP6O414}uP_Q1]Q0VP7C5P?P|b0b1b0P7n200100000021000010000n200100000021000011000n200100000021000011000W1O2S0VE3P[P7E;P?PJPxQ0FPUQ0FDLP7n010000000S1]n200100000021100010000n200100000021100011000n200100000021100011000n200100000021100011000n200100000021100011000n200100000021100011000n200100000021100011000n200100000021100011000n200100000021100011000W<X3EPgPAPpQ0^Q0kQ0lQ04Q0mPMPNPPPQP>P11C2SFc%vWPMPNPPQ02PQPRPTQ05PYM9lPMPNPPPRP[DuQ06,k[Q0oQ0FQ0p;eHQ0n1hHY'iS2\30Q0oQ0K#<#H,oT,:IS0K=eaHQ0n1hH>'i30Q07Q0:5scPMPNPOPQQ0dQ0JQ0;Q0<Q0=Q0=Q0>M;XQ0dQ0;Q0?Q0?CpPMPNPOPQQ0WQ0cQ0@Q0APXQ0BQ0CM;XPJQ0dPLQ0EC6PJQ0cPGP^C6PJQ0WPfQ0IC6Q1iQ0M50JPJQ0`Pb1:IhC6PJQ0bQ0?,>CRUQ0W,:IC6Q0sPJPpP6Q0XC6[^3EQ0e1q`6Q0f50J[^9EPMPNPOPQPRP:PgQ0^Q0_Q08Q09M;bPMPNPOPQPRP;P:Q0_Q0bQ08Q09M;bAIgA7AIAp6P?[[^5JAI:g7#dAIgA6#dQ0gPMQ0hPwP5C]PMQ0hPRP5C]30[[^5JPMPNPOPxPnQ0YQ0DQ0i3QQ0ZQ0DQ0j3QFtPiQ11PnPxQ07Q0FJ0>Q13P`%F@#N#O#\#[#F#[#HRuP=1@Iud5JIPJePZPiQ13P7Q0tPZPiD=EVQ0uPJQ0vQ0D,:IR=PJQ0w%F@#N#O#\#N#[#\#H,:IR@Q0xP`P7EGC`3EX:K-04KQ01PKQ1BQ12'DS01Px1>IuRuPwPiD=S0uQ01P7PoPwPiJ03Q0yQ0z=0J=S0zQ0{=0J@S0{AMBx73E3EX:KQ0uPZPSPjCjP7Q1<PwPuQ12PiQ1<P7PoQ12PiD=EVQ0yQ0zQ0{AMBw73E3EQ00Q1EQ1:'DS0yQ10PuQ1BPiQ0yP6PoQ1BPiD=EVQ0|Q0}=0J=PJQ0~P@PBQ10P6EG3EQ1IQ1EQ12PuQ1;PiQ1B/CSPjGSP7Q1DQ1I'DS0|Q1BPuQ1:PiQ0|P4PoQ1:PiD=EVQ14Q15=0J=PJQ16P@PBQ1;P3EG3EQ00Q17PJQ18P=PJQ19P@PBQ1:P2EGC`Q1OQ1KQ1EPuQ1DPiQ1I/CSPjGSP7Q1=PJQ1>P=PJQ1?P@PBQ1DPYEGC`Q00Q1@=0J=PJQ1AP@PBQ1CPWEGQ1NQ1PQ1KPuPrPiQ1O/CSPjGSP7Q1F=0J=PJQ1GP@PBPrPaEGQ00Q1H=0J@Q1J=MBcQ2CPyQ1PPuQ1MPiQ1N/CSPjGSP7Q1L=0J@Q1MQ0c5MBQ03Q2bQ2Y'DRBQ1TPuQ2CPiD=PBQ0WPoQ2CPiD=1CySRBPjPMPNPPQ02PQQ2JQ2CPBPrN902Ru-05B201BuPcQ1RQ1SPJQ0]fhRuQ2hQ0`P7Q2YPiQ2J/CSPjGSX2JQ2hQ2bQ2YQ2JQ2CPhQ1TQ1MQ1NQ1PQ1JPrQ1OQ1KQ1CQ1DQ1IQ1EQ1:Q1;Q1BPJ11yLRLQ1UPJQ0EQ1UQ1VPLQ12E3Q1WQ1YE3P5P[P1PJ11yGRLQ1_PJP^Q1_Q1`PLQ10E3Q1^Q0GE3PJ11yfRLQ1cPJQ0IQ1cQ1bPLPwE3Q1eQ0HE3PJ11ylRLQ1gPJQ0MQ1gQ1hPLPZE3Q1iQ0LE3PJ11ybRLPJP7PIPyCwX2JRrPJQ1T,:IRjPr18JjPLPxE3Q1lQ0qE3PJ11yURyPJP7PIQ1MCwX2JRLPJQ1N,:IRjPL18JjPyP`E311hUP6PUA0EvURyA0E]URjA0EtURL#BRr'2Ri'2P0PyPiP?P7P{PqP7PCPvPUP6O417CURv,4sPXPzQ0?P7C5P?P|b0b1b0P0PjPrP?P7P{PqP7PCP]PUP6O414~vP\Q1XQ0?P7C5P?P|b0b1b0P0PLP?P?P7P{PqP7PCPtPUP6O414}vP_Q1QQ0?P7C5P?P|b0b1b0P7n200100000021000010000n200100000021000011000n200100000021000011000W1O2E3Q0sP0Q1nQ1fQ1mP7PEP8Q1aPJQ2Y/18R|Q1qPJQ1pQ1qQ1rP|PZP8Q1oO2E3Q1sQ1xE3P5P7E;P0Q1vQ1wQ1uP7PEPkQ1tPJQ2b/1kR8Q1{PJQ1zQ1{Q1|P8PwPkQ1}O2E3Q1yQ0OE3P4P7E;P0Q23Q21Q22P7PEPFQ20PJQ2h/1FRkQ25PJQ24Q25Q26PkQ10PFQ28O2E3Q27Q0PE3P3P7E;P0Q2<Q2:Q2;P7PEPDQ1~PJ11uDRuQ2>PJQ2=Q2>Q2?PuQ12PDQ2BO2E3Q2AQ0QE3P2P7E;P0Q2EQ2DQ29P7PEPVQ2@PJfi/1VRDQ2HPJQ2GQ2HQ2IPDQ1BPVQ2MO2E3Q2LQ0RE3P1P7E;P0Q1\Q1[Q2PP7PEPeQ2OPJfj/1eRVQ2NPJQ2KQ2NQ2FPVQ1;PeQ2VO2E3Q2UQ0SE3P>P7E;P0Q2XQ2SQ2TP7PEP<Q2WPJfk/1<ReQ2QPJQ2RQ2QQ2ZPeQ1:P<Q2aO2E3Q2`Q0TE3PYP7E;P0Q1ZQ2cQ2^P7PEPdQ2_PJfl/1dR<Q2]PJQ2dQ2]Q2eP<Q1EPdQ2kO2E3Q2jQ0UE3PWP7E;P0Q2mP?Q1kP7PEPmQ1jPJfm/1mR0Q2lPJQ2iQ2lQ2nP0Q1IPmQ2rO2E3Q2sQ0VE3P[P7E;Q1]n200100000021100010000n200100000021100011000n200100000021100011000n200100000021100011000n200100000021100011000n200100000021100011000n200100000021100011000n200100000021100011000n200100000021100011000W<X3EP;P:PgPAPpQ0^Q0kQ0lQ04Q0mPMPNPPPQPWPY1C>SFcQ0F#vPMPNPPQ02PQPRPTQ05P[M9lPMPNPPPRPaDuQ06,kaQ0oQ0p=ecHQ0n1hH['i30Q0oQ0JQ0K;eHQ0n1hHW'i30Q0oQ0dQ0E;eHQ2\30Q0cQ07Q0:3sPMPNPOPQPhQ0WQ0;Q0<Q0=Q0=Q0>M;XPhQ0;Q0?Q0?CpPMPNPOPQQ0bQ0`Q0@Q0APXQ0BQ0CM;XQ1WQ0E50JPJQ0`PGP^C6PJQ0bPfQ0rC6PJQ0_PlQ0MC6PJQ0^PbQ0_,:IC6PJPpPUQ0b,:IC6Q0sPJP:P6Q0XC6[^3EQ0e1qw6Q0f50J[^9EPMPNPOPQPRP`PnPgPAQ08Q09M;bPMPNPOPQPRPxP`PAPpQ08Q09M;bPMPNPOPQPRPZPxPpQ0^Q08Q09M;bAI`n7AIn;6P?[[^5JRQAIx`7AI;:6P?[[^5JAIwZ7#dAIZx6#dAIx`5#dQ0gPMQ0hQ1IP4C]PMQ0hPRP4C]30[[[^5JPMPNPOQ1;Q12Q0YQ0NQ0i3QQ0ZQ0NQ0j3QFtQ1IQ1EQ1:Q1;Q1BQ12Q10PwPZPxP`PnP;P:PgPAPpQ0^Q0_Q0bQ0`PhQ0WQ0cQ0dQ0JPcPaQ0FP[PWPYP>P1P2P3P4P5P6P7NX0eY07WhXIQWJWLWoWqWtWSY0;Y0QY0OY0NY0RY0SY0PWaW]WeY01Y0TY0VY0YWPY0\W{WVWYZ0i9Z0`9Z0k9Z0b9Z0n9Z0e9Z0wKY0zWlWHY0hZ0qKNV0dPoP7E;b1N90=WDWuP6P7O2n2001000000121000000W1WwP6P7O2n2001000000121000000W1WvP6P7O2n2001000000121000000W1W=P6P7O2n2011000000121000000W1Z0vKP6P7O2n2011000000121100000b4Y06WgWKWpWsWRY0:Y0KY0IY0HY0LY0MY0JW`W\WdW~Y0UY0XWOY0[WzWUWXZ0j9Z0a9Z0m9Z0d9Z0uKY0yWkWGY0gZ0pKNP0cPoP7E;b1N90=WEY02P6P7O2n2001000000121000000W1Y04P6P7O2n2001000000121000000W1Y03P6P7O2n2001000000121000000W1W=P6P7O2n2011000000121000000W1Z0tKP6P7O2n2011000000121100000b4Y05WfWrWQY09Y0DY0CY0FY0GY0EW_W[WcW}Y0WWNY0ZWyWTWWZ0l9Z0c9Z0sKY0xWjWFY0fZ0oKNK0bb;PSQ0aE;WmWnP6P7O2n2001000000121000000b1Y08Y0?Y0AY0BY0>Y0=Y0<Y0@W^WZWbW|WMWxW;WiY0ro"). Qed.

End Main32.

Lemma bxw_ag : forall (L : list reg) regs regs' (r : reg),
  regs_agree (fun x => In x L) regs regs' -> existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = false ->
  getr regs' r = getr regs r.
Proof.
  intros L regs regs' r AG E. apply AG. intros Hin.
  assert (T : existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = true).
  { apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

Ltac bxw_g AG r := rewrite (bxw_ag _ _ _ r AG ltac:(vm_compute; reflexivity)).
Ltac bxw_ag2 A1 A2 :=
  lazymatch goal with
  | |- getr _ ?r = _ => bxw_g A2 r; bxw_g A1 r; reflexivity
  end.
Ltac bxw_to pc :=
  lazymatch goal with
  | |- realizes _ (mkCfg (@mkst _ _ ?pc0 _ _) _) _ => replace pc0 with pc by (apply bv_eq; reflexivity)
  end.
Ltac bxw_run HW RUN :=
  lazymatch type of RUN with
  | msteps _ (@mkst _ _ ?pc _ _) _ => bxw_to pc
  end;
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |]; clear RUN.


(* [comment removed for export] *)
Theorem pixBilateralExact_W : pixBilateralExact_contract.
Proof.
  unfold pixBilateralExact_contract.
  intros fr cs C A m md regs s pixs w h d datas skel arrs rkel arrr rowss rowsr ret S
    CK HW Hz H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PXs HOK Hd Hw1 Hh1 Lps Lds KOs KORG KOr
    ksf rsf KVs0 KVs1 KVr0 KVr1 kR bR Hrm Hrk Hrb KN KP.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof Hlo as Hlo'. unfold BEX_STACK, BGE_STACK, AMB_STACK, LSF in Hlo'.
  assert (HloB : (c_top C - LSTK + BGE_STACK <= s)%Z) by (unfold BEX_STACK in Hlo; lia).
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs80 : (80 <= s)%Z) by lia.
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  pose proof PXs as (Pp0 & Pp64 & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (ALp8 : (pixs mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pixs); apply mod16_plus_mod8; [exact ALp | reflexivity]).
  pose proof (kobj_lives _ _ _ _ _ _ _ _ KOs) as (Lks & _ & Hks1 & Hks24).
  destruct (bx_A al_rom (mkFP fr cs) regs m s pixs skel rkel (hdv w h d 0 datas) ret Hs80 Hs64 ltac:(lia) PXs ltac:(lia) eq_refl Hd ALp8
              ltac:(lia) (W_sok_win C A m md (s - 80) 80 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & A2 & A8 & A9 & A18 & A10 & AG1).
  bxw_run HW RUN1.
  set (M1 := FRX m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold FRX; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (framex_init m s ret regs Hs80 Hs64) as CL1. fold M1 in CL1.
  assert (KEEP : forall M M' p v, LIVK A M M' -> live A (Z_to_bv 64 p) = Some 64%Z -> PIXat M p v -> PIXat M' p v).
  { intros M M' p v LK Lp PX. pose proof PX as (P0 & P64 & _). apply (PIXat_frame M); [exact PX|].
    intros x Hx. exact (LIVK_at A M M' p 64 x LK Lp ltac:(lia) ltac:(lia) Hx). }
  pose proof (KEEP m M1 pixs _ (proj2 PM1) Lps PXs) as PXs1.
  pose proof (kobj_keepL C A A m M1 s skel arrs 41 41 rowss KOs ltac:(lia) (fun q k _ => eq_refl) PM1) as KOs1.
  pose proof (kobj_keepL C A A m M1 s rkel arrr 1 256 rowsr KOr ltac:(lia) (fun q k _ => eq_refl) PM1) as KOr1.
  pose proof (korg_keepK C A m A m M1 s skel arrs 41 41 rowss 20 20 KOs Lks PM1 KORG) as KORG1.
  assert (KVs2 : kvals M1 41 41 rowss ksf) by (eapply kvals_keep; first [exact H_bge | exact KOs | exact PM1 | exact KVs0]).
  assert (KVr2 : kvals M1 1 256 rowsr rsf) by (eapply kvals_keep; first [exact H_bge | exact KOr | exact PM1 | exact KVr0]).
  destruct Hd as [D8 | D32]; subst d.
  -
    destruct (bx_T8 al_rom (mkFP fr cs) r1 regs M1 s pixs skel rkel ret Hs80 Hs64 CL1 A2 A8 A9 A18 A10)
      as (r2 & RUN2 & B2 & B1 & B10 & B11 & B12 & BR & AG2).
    bxw_run HW1 RUN2.
    bxw_to (Z_to_bv 64 PC_pixBilateralGrayExact).
    assert (CS2 : cs_kept regs r2).
    { apply cs_kept_intro;
        first [ solve [rewrite B2, H2; reflexivity]
              | solve [apply BR; cbn [In]; repeat first [left; reflexivity | right]]
              | solve [bxw_ag2 AG1 AG2] ]. }
    apply (H_bge fr cs C A M1 md r2 s pixs w h datas skel arrs rkel arrr rowss rowsr ret S CK HW1 Hz B2 Hs16 HloB Hhi B1 Hret
             ltac:(bxw_g AG2 (4%bv : reg); bxw_g AG1 (4%bv : reg); exact H4)
             B10 B11 B12 PXs1 HOK Hw1 Hh1 Lps Lds KOs1 KORG1 KOr1 ksf rsf KVs2 KVs1 KVr2 KVr1 kR bR Hrm Hrk Hrb).
    + intros fr' cs' A' m' vm' r' HW' Hz' CS' PM' R10 LV FS RM.
      apply (KN fr' cs' A' m' vm' r' HW' Hz' ltac:(intros x Hx; rewrite (CS' x Hx); exact (CS2 x Hx))
               (POSTM_trans _ _ _ _ _ _ PM1 PM') R10 LV FS RM).
    + intros fr' cs' A' m' vm' r' pixd datad HW' Hz' CS' PM' R10 PN FS RM.
      apply (KP fr' cs' A' m' vm' r' pixd datad HW' Hz' ltac:(intros x Hx; rewrite (CS' x Hx); exact (CS2 x Hx))
               (POSTM_trans _ _ _ _ _ _ PM1 PM') R10 PN FS RM).
  -
    destruct (bx_T32 al_rom (mkFP fr cs) r1 M1 pixs A9 A10) as (r2 & RUN2 & C10 & C11 & C1 & AG2).
    bxw_run HW1 RUN2.
    bxw_to (Z_to_bv 64 PC_pixGetRGBComponent).
    apply (main32 fr cs C A m md regs s pixs w h datas skel arrs rkel arrr rowss rowsr ret S kR bR ksf rsf
             CK HW Hz H2 Hs16 Hlo Hhi Hret H4 PXs HOK Hw1 Hh1 Lps Lds KOs KOr KVs0 KVs1 KVr0 KVr1 Hrm Hrk Hrb KN KP r2 M1
             HW1 PM1 CL1 PXs1 KOs1 KORG1 KOr1).
    + bxw_g AG2 (2%bv : reg). exact A2.
    + exact C1.
    + exact C10.
    + exact C11.
    + bxw_g AG2 (9%bv : reg). exact A9.
    + bxw_g AG2 (8%bv : reg). exact A8.
    + bxw_g AG2 (18%bv : reg). exact A18.
    + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [bxw_ag2 AG1 AG2|]). destruct Hx.
Qed.

End BexW.
