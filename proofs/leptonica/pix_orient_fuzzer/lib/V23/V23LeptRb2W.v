(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LiaRel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRbLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixCopyTR O23LeptPixHdrT2 O23LeptRb2W.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixCreateT2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptErr V23LeptCmap2 V23LeptRb2 V23LeptRot90cwW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23LeptPadBitsW V23LeptPixCreateW0 V23LeptPixCreateT2 V23LeptScaleRes.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require RefStep3.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require LiaFast.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23LeptRb2W () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8WalksLib9rostr_chkI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C7ARocqVerifyHarness?AgentSubmission6Common9Leptonica8SumSpecs3SSP9rostr_winC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00C5ARocqVerifyHarness@ProcessOversightKTgt_pix_orient_fuzzer_ubsan1M?loaded_segmentsK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7mul_1_rC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith6wpl_ofK46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:asr_callocC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc8aic_baseC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase2ASK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LIVKC45stdpp9bitvector;definitions7Z_to_bvC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase4liveK47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5PIXatC56Stdlib6ZArith6BinInt1Z3powI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6pix_wf00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs9pix_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8bytes_atC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3O23<O23LeptCmap27LIVK_atC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs;PIXat_frameI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs4pixv00I47Corelib4Init5Logic4True00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8sub_liveC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C47Corelib4Init5Logic3notc5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W5LIVKfC5ARocqVerifyHarness?AgentSubmission6Common5Hoare3at_C45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission6Common8PropExec9u64_rangeC5ARocqVerifyHarness?AgentSubmission6Common7StepTac6u_Z2bvK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission3O23@O23LeptPixCopyTR7zbv_ne2I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op201I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4lctx00I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3Cok00I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs1W00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_topC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5w_invC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase<ai_live_hullC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface7round16C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase5ownedC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface8al_in_roC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface8al_in_rwC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:round16_geC4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8blk_byteC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8heap_gapC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6ll_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3inZC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3winC5ARocqVerifyHarness?AgentSubmission3V23<V23LeptCmap29blk_apartI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission6Common:AllocIface:al_globalsI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission3V23;V23LeptBase5LLU16C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LSTKC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica5PFLib;rdn_definedC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2ex00c5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W6rbw_tbC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst7Inj_Z_Zc5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W3FTbC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_vmK46Stdlib9micromega5Tauto8GFormula01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9blk_rangeC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC5ARocqVerifyHarness?AgentSubmission6Common7CatExec6wbytesC5ARocqVerifyHarness?AgentSubmission6Common7CatExecDlength_N_to_le_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6WP_blkC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit>wbytes_outsideC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5POSTMC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission6Common5Hoare:regs_agreeC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface6al_romC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_sp0C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7mod_addC5ARocqVerifyHarness?AgentSubmission3V23<O23LeptRbLib@rbl_flip2_boundsC5ARocqVerifyHarness?AgentSubmission3V23?V23LeptRot90cwW<r90w_rd4_blkC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC56Stdlib6ZArith6BinInt1Z4lxorC5ARocqVerifyHarness?AgentSubmission3V23?V23LeptRot90cwW<r90w_sok_blkC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W:rbw_tab_rdC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb24rb_WC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6w_pureC5ARocqVerifyHarness?AgentSubmission6Common9PureModel9mp_haltedC5ARocqVerifyHarness?AgentSubmission6Common9PureModel7mp_lazyc5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W9FTb_storeC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb25rb_WxC5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg9rz_mstepsC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb25rb_WnC47Corelib4Init9Datatypes7nat_indK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00K46Stdlib9micromega=RingMicromega5Psatz01I5ARocqVerifyHarness?AgentSubmission6Common6CatSim6msteps00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8LSTK_valI47Corelib7Numbers7BinNums8positive00C5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb24rb_RC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith4Znat5Z2Nat2idK47Corelib4Init5Logic2or01C47Corelib4Init5Logic6or_indc5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W:rb_words_WC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb25rb_RnK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission6Common7FPSteps8frm_zeroC5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okC5ARocqVerifyHarness?AgentSubmission3O23@O23LeptPixCopyTR4hdvrC5ARocqVerifyHarness?AgentSubmission3O23?O23LeptPixHdrT26hdr_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_A0C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure5aroomC4ELinuxProcessSemantics5Riscv3Sem7reg_getC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs7cs_keptC5ARocqVerifyHarness?AgentSubmission3O23BO23LeptPixCreateT28pixr_newK5ARocqVerifyHarness?AgentSubmission6Common8PropExec7FPState01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_img64C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ro_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_roC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_lg_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_lgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ag_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_agC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=pin_errno_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_errnoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_hcellC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_hcellC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;pin_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:ll_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs<pin_ro_belowC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith4dvalc5ARocqVerifyHarness?AgentSubmission3O23;O23LeptRb2W8rbw_wpl1C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs7wf_dataC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_datac5ARocqVerifyHarness?AgentSubmission3O23;O23LeptRb2W7rbw_posC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL>RB_pixT_nonnegC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL7RB_pixTC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_dC5ARocqVerifyHarness?AgentSubmission3V23;V23LeptBase9W_sok_winC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb25rb_A1C5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb25MRB_AC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_wC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_hC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:POSTM_reflI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3V23;V23LeptBase6cellsZC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb23FRBC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8WalksLib?rdn_wbytes_hit4C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;POSTM_rangec5ARocqVerifyHarness?AgentSubmission3O23;O23LeptRb2W8LIVKe_ofC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb24rb_EC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=cs_kept_introC5ARocqVerifyHarness?AgentSubmission3V23;V23LeptBase5str16C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;sub_live_eqC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec6v_jalrC5ARocqVerifyHarness?AgentSubmission6Common7StoreOk9mem_growsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9POSTM_subC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8LIVK_subc5ARocqVerifyHarness?AgentSubmission3O23;O23LeptRb2W;LIVKe_transc5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W3RBCK47Corelib5Lists7ListDef6Forall02I47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission3V23;V23LeptBase:cellsZ_outC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;cs_kept_getC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptErr@returnErrorPtr_WC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:aroom_monoC46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtI47Corelib4Init6Specif7sumbool00C5ARocqVerifyHarness?AgentSubmission3V23;V23LeptBase9W_sev_gotC5ARocqVerifyHarness?AgentSubmission3V23;V23LeptBase5W_sevC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb25rb_AhC5ARocqVerifyHarness?AgentSubmission6Common8VmLedger@with_vmmaps_sameC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb25rb_A2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5p_wplC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:POSTM_monoc5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W;LIVKe_win_dC5ARocqVerifyHarness?AgentSubmission3V23;V23LeptBase:cellsZ_frmC5ARocqVerifyHarness?AgentSubmission3V23;V23LeptBase9FRM_rdn16C5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb24rb_BC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;W_store_winC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb25rb_CnC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs@POSTM_wbytes_winC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:LIVK_transc5ARocqVerifyHarness?AgentSubmission3O23;O23LeptRb2W<rbw_PIX_livkC56Stdlib6ZArith6BinInt1Z6eq_decC5ARocqVerifyHarness?AgentSubmission3V23BV23LeptPixCreateW0>pixCreate_w0_Wc5ARocqVerifyHarness?AgentSubmission3O23;O23LeptRb2W<rbw_wpl_halfc5ARocqVerifyHarness?AgentSubmission3O23;O23LeptRb2W8rbw_prodC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom6roomtrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=sub_live_new2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs>sub_live_transc5ARocqVerifyHarness?AgentSubmission3O23;O23LeptRb2W=rbw_live_noneC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_xresC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_yresC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb24rb_CC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb25MRB_CC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs9PIXat_outC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb2:rb_wr_res0C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs7scratchC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geK47Corelib4Init5Logic2ex01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;POSTM_localC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7rdn_extC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb24rb_DC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z:mul_div_lec5ARocqVerifyHarness?AgentSubmission3O23;O23LeptRb2W6rbw_ksC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z<divide_transC5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb25rb_RxC5ARocqVerifyHarness?AgentSubmission3O23?O23LeptPixHdrT27pix_hdrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8set_datac5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W9rb_rows_WC5ARocqVerifyHarness?AgentSubmission3V23?V23LeptScaleResGpixScaleResolution_05_WC5ARocqVerifyHarness?AgentSubmission3V23BV23LeptPixCreateT2@pixCreate_szT2_WC5ARocqVerifyHarness?AgentSubmission3V23?V23LeptPadBitsW9padbits_WC47Corelib4Init9Datatypes3fstC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6WP_winC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec?rdn_wbytes_hit8C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:SumWalkTac@rdn_wbytes_out_ZK47Corelib4Init9Datatypes4prod01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3FRMC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;POSTM_transK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common8FPStepsV8fpv_readC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom6RK_pixC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs2K4ELinuxProcessSemantics5Riscv5Instr4ffmt01C5ARocqVerifyHarness?AgentSubmission3V23:V23LeptRb23F05K46Stdlib9micromega=RingMicromega3Op204C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSetc5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W9RB2_STACKI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecB7fs_listc5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W7str_rb2C5ARocqVerifyHarness?AgentSubmission3V23;V23LeptBase3LSFC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs3C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs4C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs24C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs25C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs26C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs27c5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W:str_rb2_hsK46Stdlib9micromega=RingMicromega3Op206c5ARocqVerifyHarness?AgentSubmission3V23;V23LeptRb2W<str_rb2_pixdC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs9C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs8C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs18C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs19C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs23".   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_rel.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_rel.
(* [comment removed for export] *)
Local Ltac kc_clear := repeat match goal with H : _ |- _ => clear H end.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma str_rb2_hs : str16 0x16370 21.
Proof.
ltac2:(KReplay.run1 (kr_t_V23LeptRb2W ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;3p;2p;4p;7p10000p4p70R0p1000`p4p710R1p8P0p1001<p4p710R0p8p1001Zp4p70R2P1p8P2P0p8p1002Hp4p70R2P1p8P2P0p8g003>j11Tg003cj10Tg004Hj15Tg004fj3FTg005nj3<Tg006Hj26Tg006dj27Tg007?j2@Tg008Kj2;Tg008hj2?Tg009Bj1>Tg009bj1NTg00:Bj1MTg00:`j1LTg00;>j1ETg00;ij2=Tg00<Lj3CTg00<oj2BTg00=Qj2DTg00>=j3ATg00>\j4GTg00?Nj4HTg00?ij4ITg00@Tj7JTg00A8j7KTf0R0#1#1p=3%10#1#1#1p=2g00A\R2/=0p=4P2f1R1g00B:P0CIp=8P1g00BaR3g00C@R4P4g00C`R5P0g00D@FJp=9f2R6P3P4P4P5P1P0FKp=:g00D`R4g00E@g00FSR3#1#0#0#1#3#0#0#1#0#0#0#2#5R7%13R8#0R9#1#0#5R:3Fg00G8R;3<R<g00GXR=/6:%03#3#0#1#3#5R>,6:'7R?%18#3#2#2#2#5R8/67R@1@7:,;7%33#0#1#3#0#0#2#2#2#5R3'6'7'71?4;RAP<dg00H6R<#>%N<%M2%L2%E2R<1=2=%4:R:'8,9<%4>,8:,9<5:<%48%47R8'8,9<%09#0#5R9#49C28%43'8,9<5:<3:1B<5P0P6PA1D06=<4;dAA2=1CGb1b2b31;79/63,7@,7?P0b0CHo"). Qed.        (* [comment removed for export] *)
Lemma str_rb2_pixd : str16 0x126da 13.
Proof.
ltac2:(KReplay.run1 (kr_t_V23LeptRb2W ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;3p;2p;4p;7g003cj10Tg004Hj14Tg003>j11Tg004fj3LTg005nj3=Tg006Hj27Tg006dj28Tg007?j2ATg008Kj2<Tg008hj2?Tg009Bj1OTg009bj1NTg00:Bj1MTg00:`j1KTg00;>j1HTg00;ij2>Tg00<Lj3ETg00<oj2DTg00=Qj2CTg00>=j3FTg00>\j4GTg00?Nj4BTg00?ij4ITg00@Tj7JTg00A8j7@Tf0R0#1#1p=6%00#1p=2%10#1#1#1p=5g00A\R1/>0p=3P1f1R2g00B:P0CIp=9P2g00BaR3g00C@R4P4g00C`R5P0g00D@FJp=:f2R6P3P4P4P5P2P0F@p=;g00D`R4g00E@g00FSR3#6R7#0#6#0#2#0#2#0#2#2#4R8%03R9#1R:#0#4R;3Lg00G8R<3=R=g00GXR>/7;%1:#2#6#4R:,7;'8R?%67#5#5#5#4R7/78R@1A8;,<8%63#2#6#0#0#5#5#5#4R3'7'8'81?4<RAP=dg00H6R=#O%N=%M1%K1%H1R=1>1>%3;R;'9,:=%3:,9;,:=5;=%37%38R7'9,:=%29#4R9#39E17%33'9,:=5;=3;1D=5P0P6PA1C06==4<dAF1>2CGb1b2b31<89/73,8@,8?P0b0CBo"). Qed.      (* [comment removed for export] *)
Lemma str_rb2 : str16 0x16386 20.
Proof.
ltac2:(KReplay.run1 (kr_t_V23LeptRb2W ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;3p;2p;4p;7g003>j10Tg003cj11Tg004Hj15Tg004fj3FTg005nj3<Tg006Hj26Tg006dj27Tg007?j2@Tg008Kj2;Tg008hj2?Tg009Bj1>Tg009bj1NTg00:Bj1MTg00:`j1LTg00;>j1ETg00;ij2=Tg00<Lj3CTg00<oj2BTg00=Qj2DTg00>=j3ATg00>\j4GTg00?Nj4HTg00?ij4ITg00@Tj7JTg00A8j7KTf0R0#0#0p=3%00#0#0#0p=2g00A\R1/=0p=4P1f1R2g00B:P0CIp=8P2g00BaR3g00C@R4P4g00C`R5P0g00D@FJp=9f2R6P3P4P4P5P2P0FKp=:g00D`R4g00E@g00FSR3#0#1#1#0#3#1#1#1#2#1#1#0#5R7%03R8#1#3#5R93Fg00G8R:3<R;g00GXR</69%13#3#1R=#0#3#5R>,69'7R?%08#3#2#2#2#5R8/67R@1@79,;7%33#1#0#3#1#1#2#2#2#5R3'6'7'71?4:RAP;dg00H6R;#>%N;%M1%L1%E1R;1=1<%49R9'8,9;%4>,89,9;5:;%48%47R8'8,9;%5=R=#49C18%43'8,9;5:;3:1B;5P0P6PA1D06=<4:dAA1<2CGb1b2b31;7=/63,7@,7?P0b0CHo"). Qed.           (* [comment removed for export] *)

Section Rb2L.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Definition LIVKf := LIVKe.

(* [comment removed for export] *)
Lemma LIVKe_win_d : forall C A m md m' (d kd lo hi : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 d) = Some kd -> (0 <= d < 2 ^ 64)%Z -> (0 <= kd)%Z ->
  (forall a : word, ~ (lo <= u a < hi)%Z -> ~ (d <= u a < d + kd)%Z -> m' a = m a) -> (c_top C - LSTK <= lo)%Z -> (hi <= c_top C)%Z ->
  LIVKe A d m m'.
Proof using PINS.
ltac2:(KReplay.run1 (kr_t_V23LeptRb2W ()) ["Rb2L"] "h04__x1h14__x2h27__arithh34__ffh44__p1h58__varmaph65__with74__x3h81ih96__sat1h:4__x4h;4__x5h<1Hh=2H1h>6__sat0h?6__sat2h@2APhA2HahB2_HhC3_H0hD4__p2hE1ahF1zhG1AhH1ChI2CKhJ2H0hK2HWhL2HdhM3HhihN2HihO3Hk0hP3HkdhQ3HlohR1LhS2LdhT2NEhU2NWhV3OUThW1RhX2RRhY1ThZ3TOPh[3_H1h\3_H2h]1dh^2hih_1kh`2kdha2lohb1mhc2m'hd2mdhe1qhf1xp%0p&0p;3p;2p;1p;5p;8p;4p;9p;6p;@p;Bp;7g00[9k30GTg01:;k30FTg00\Bj3~Tg00]Kj2sTg003>j1NTg00^Lj1lTg00^jj1iTg00_Mj1gTg01;@j5{Tg01<Dj8wTg00a2j2UTg00aXj4dTg00b[j2bTg005nj33Tg004Hj1`Tg00dDk20=Tg00h@j20Tg010fj12Tg008Kj27Tg01=Fj4]Tg013Rj2\Tg006Hj2>Tg01>Jj1ATg01?Al9xTg01@El9vTg01APj2PTg01B0j1;Tg01Bnj1DTg0129j21Tg01Cfj4GTg00K@j1cTg01Djj2ITg01Eij2JTg01Fhk20ETg01H1k10DTg00I?j2=Tg014Rk10CTg00hjk20@Tg00iRk30?Tg009Bk10>Tg009bk10<Tg00I[j2TTg00Uoj4OTg00:`k10;Tg00;>k10:Tg00;ij2kTg00J9j2RTg003cj1jTg00<Lj3XTg00<ok206Tg008hk205Tg00=Qk203Tg00>=k302Tg00>\k401Tg00RFj1WTg00Q]j2QTg00:Bj1}Tg006dR0j2:Tg00j6j3|Tg015Pj3fTg001<j6zTg01Hll@yTg01J3j5_Tg01K:k100Tg01L?j2KTg01MAj5@Tg01NCmB04Tg01OBj2YTg000`j6uTg013ok307Tg01O\j7tTg017Qk608Tg011?k409Tg00?ij4eTg00@Tj7mTg00A8j7nTg00PRj8oTg00SNj3rTg00T7j2qTg00UOj3pTg00J\k60ATg01P@k20BTg00GXR1f0R2'>p=4f2R3f1R4/=2':p=8f3R5/>31=42':p=?A3342#2p=[g00A\R6?321p=Sf5R7f4R8?353#2%24/:2':':p=F1>34/:2p=Z1:42,:3p=a1734/>2p=9P3g00BaR9g00C@R:P:g00C`R;P6P4g00B:P2Ceg00D@R<Fmp=5P3P9P:P:P;P6P4g00Q6P2CeP<Fmp=CP3P9P:P:P;P4P2Fnp=^P7P9P:P:P;P8P9P:P:P;P5P3FnP4P2Gop=EAr642p=<g00Vl,q2p=Mg00H6R<?p42p=LP4P9P:P:P;P2J0Ap=VP5P9P:P:P;P3P4P2Gop=H20B42#2p=B%24/:2p=6P8P5P3P4P2D@#2p=hp,2ALR=p,2CLR>p,3ASRS00:0G=>R?40FA~=>?R@,s=g00FSRA#NRB#NRC#NRD#NRE#N#NRF#lRG#iRH%lD#iRD#gRI[g01QAPI^fHP=P>P?g01R7RJf8RKD{P=P>P?PJf9RLPKf7RMf6RNGw%g6ROP=P@PL1UG7Cd1b6833%4NRP%`BRQ%`FRF+0=RR78NPM10G2RSPSPNC?#2f:RS10G4RTPT17SLC?#2f<RTP3O1f>RUP3O153I[[^EHP=P>P?PUC]g01S1S01'\/>MP=P>P?f?RVC],>MP=P@fBP3Cd1b6453O1UGV9[H5%43RO?835P=P@fERWfDRXfCRY#ARZP7P8P=P>P?PJfFR[PWPXPYPTM9xP3M9v%4810G7R\%`ERE'P#S%;8,7\%DZ%42RZ%;7R\782P=P@fGR]11M4R^CGPIP[P^O1%cDRD1I=^1J=^#2EF[^863Z3aP0%4710GNR^/PE#S%AX#D99^\%;N98Z2P=P@fHR^11K4R\CGPIP]P\O1PD1I=\1J=\#2EF[^863aPX11M7R\O1P[P\O153IP2%4M10GLR\/PE#S%;K%A]#D59\%;LR\98Z2P=P@fKR_f;R`/14RaCGPIfJRbPaO1PD1I=a1J=a#2EF[^863aP010GSRa/PE#S17a\%A^#D%;S98Z2P=P@fLRS11T4RaCGPIP_PaO1PD1I=a1J=a#2EF[^863ZP^11`LRaO1PbPaO153IP210GT/PE#Sf=RE,0G%;T'7%A_#D%;ERa98Z2P=P@fOR\11V4RcCGPIfNRdPcO1PD1I=c1J=c#2EF[^863ZP010GU%AS#D79a%;U98Z2P=P@fPRaf@Rc/14ReCGPIP\PeO1PD1I=e1J=e#2EF[^86PS11VEREO1PdPEO153IP210Gc%;V%Ad#D39fARc#;RE98Z2P=P@fSR@11Y4ReCGPIfRRfPeO1PD1I=e1J=e#2EF[^8620EcL1>cEfQRE#ARc$0D%Dcg01T4'=&0CX10GXRc#4?8cRP610GWRc/7YRL10G[ReP2P217eWC?XF620@QFRe1=1Q%4F1=1R[[Rg%4QRhg00mkRiB0?QF4UWARF%4R\i^AhRh&0><Ri&0<<R<P61T63RjP41T65CO&0;6Rk&0:6RlPl1k61Rm1R6BRn55lRo%jA,R6Rp9ClnS02%c:Rq1R6ARAAX6AnRr55lAX6ApRs9Clr5^lEE206l;RtP2P3g00D`Rug00G8Rv+0520323=3uvdB02614H01R1b3b5b6X06X16X76%44Rv?843P41743RuPu1745C?[^06^16^76P2P]P[10G^RuPYO4b2b9b?1UGL,0GPePgPFPhp-0Rwg00VMRx#WRy#WRz,Q6R{1Q6yRy1Q6xRx'<R|'<R}#M/LiP<P6PjP4%}6RjCOPkPlPlA5lmAR~1Vl8PqPlPlPo1Vl7PqA5lmrEEEEPtP1b3b5b6X06X16X4wWD1:Z31:O81735#4[[^06^16^4w^DwP21=[]1=uRP[PuP5PYO6b2b9b?PePgPFPh%WzRz#W,Q6RO1Q6zRz/<}'<#M/LiP<P6P61T68P3PjCOP4P61T67P5PjCOCORjPkPl%jB,R6RB1k6Q=|6GRQ5ClPqPl1R6CRC95lpPqPlAX6AC=5lBPqPlPl1VlMQ02PqAClrQEECHCHCHPtP1b3b5b6X06X16X76X:6X;6X4w1=8R1>58A937NA8K871787RK/=R[[[[^06^16^76^:6^;6^4wP2%4[fVRN#A#D%;]P]P[PuP8P7PMPYO:b2b9b?5fLEzPc11WY,0GRLPL17cXC?RcePcP=P>P?PJp,4PINSfWRcPNfURLfTRMP[PW11[XRXPdfMRuPYP2M@yP=P>P?PcPXD_PIPLPXO1PD&00JRJ10GX'KP=P>P?PcPXD@1B=X'6EFP0P=P>P?fXRX11]WRWD_PNPWO1=3ID10GW,KJP=P>P?PXPWD@1B=W'6'6'6PL11^[RWO1PcPWO153IP2P=P>P?fZRWfIRY/1]D_fYR]11b^R^O1=3ID10G^,KJP=P>P?f[RrP^D@1B=^'6'6'6P0PW11_YRYO1=[ID10GY,KJP=P>P?f\R^PYD@1B=Y'6'6P]11SbRbO1PrPbO153IP2P^11u_O1=[ID11dSRS,0G,KJP=P>P?f_RDPSD@1B=S'6'6P011\uRu,0G,KJ#2P=P>P?f`RSPuD@1B=u'6f]Ru11adRdO1PDPdO153IP211E\,0G,KJ#2P=P>P?fcRJ11faRaD@1B=a'6P0P=P>P?fdR011@EREDh1B=Efa11MfRfO1PJPfO153IP2P=P>P?ffRI11L@Dh11NM,B=P=P>Q00fhRLfgRfPIfeRIPc1UGJREPNfbRaPDf^PMPuP@PiP<1T64R@PkPlP~PqP~CHPtP1b3b5b6X06Pv\Z^06P2PcP\O2b2PrNB0410GcR\10GERE79NA9Ea\'YP61UG0,0G10G]RE?9X2A920E'YXF6P2P0PePgPFPhPiP<P@PkPlPlP~1Vl5REPqP~EEPtP1b3b5b6X06X4w1:Z4Pv[^06^4wP21=fRPfPSO3b2b>b9PePgPFPhPiP<P@PkPlPlPEAClAQRQPqPQEEPtP1b3b5b6X06X4wA842R1=4R[^06^4wP2%4fPfPSO3b2b>b95f0Eu10GXRS?9c0A90JS'YP^11]cRcPJ10GcRcPcPaC?RaP81<{x,<z#M1<O|#M/Li'LP<PjPkPlPlA5lCpAClpBPqPlA5lBAPqPlB076AnR|=5lCPqA5l|pAClpA5^lCHCHEEPtP1b3b5b6X06X16X76X:6X;6P5P3P3P8C?1>741\35/>71\58P7P7P5C?[[[^06^16^76^:6^;6P2P0PI11r],0GQ01P=P>P?flC]P4P^PuO8b2P=P>P?fk11WXD@eO1WW%2aePePgPFPh1<zx,<O#M1<{y,<O#M/Li'LP<PjPkPlPlP9P:P:P;AX6CBRB=5lAA5lsCFtPqPlPlA5lCnAClnBPqPlP9P:P:P;A5lAnAClns5^lJ08EECHPtP1b3b5b6X06X16X76X:6X;6A9582A9235'YP8P3P3PKC?P3P5P51738C?g00om[[[^06^16^76^:6^;6P2Pr10G^Pf11^W,0GPLP5P[O7b2b>b9O3b@b@W\WUP4P2O2n2001000000121000000W=W[P4P2O2n2001000000121000000W=WCP4P2O2n2001000000121000000W=WBP4P2O2n2001000000121000000bEbXbJbYb<WCWZP4P2O2n2001000000121000000W<WBP4P2O2n2001000000121000000W<WOP4P2O2n2001000000121000000b<WNWTWRX86X_6XeHPVP`PUPTH09eWMWQWVXPPWLWSWKWIX^6Xa6X`6X]6WcWdWbWGWHo"). Qed.

(* [comment removed for export] *)
Definition rbw_tb (m : word -> option byte) (tab i : Z) : byte :=
  match rdn SEGS m (Z_to_bv 64 (tab + i)) 1 with Some (b :: _) => b | _ => Z_to_bv 8 0 end.
Lemma rbw_tab_rd : forall C A m md (tab : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 tab) = Some 256%Z -> (0 <= tab)%Z -> (tab + 256 < 2 ^ 64)%Z ->
  forall i : Z, (0 <= i < 256)%Z -> rdn SEGS m (Z_to_bv 64 (tab + i)) 1 = Some [rbw_tb m tab i].
Proof using PINS.
ltac2:(KReplay.run1 (kr_t_V23LeptRb2W ()) ["Rb2L"] "p'0h04__x1h14__x2h24__p1h37__arithh44__ffh56__sat2h66__sat3h78__varmaph85__with92Lbh:1Rh;4__x3h<1Hh=4__p2h>1xi001xh?3Hk0h@2bshA1ehB2HahC1mhD1yhE1zhF1AhG1ChH2CKhI1DhJ2H0hK2H1hL2HWhM2HihN2HkhO1LhP2_HhQ3_H0hR1ahS1bi011bhT2b'hU1ihV1khW1li021lhX2mdhY1ni031nhZ1oh[1th\3tabi042l0p%0p&0p;3p;2p;1p;5p;8p;4p;<p;6p;@p;7p;Bg00[9k30ATg01:;k30@Tg00\Bj3zTg00]Kj2qTg003>j1>Tg00^Lj1gTg00^jj1`Tg00_MS00j1YTg01;@j5wTg01<Dj8tTg00a2j2:Tg00aXj4mTg004Hj1OTg008KR0j20Tg00dDk20<Tg00I?R1j21Tg006dR2j22Tg00RFj1ITg00hjk203Tg00iRj3~Tg00Q]j2LTg00T7j2RTg009Bj1jTg00UOj37Tg009bR3j1\Tg00I[j2ZTg00:Bj1sTg00Uoj4bTg00:`j1pTg00;>j1nTg00;ij2QTg00J9j2VTg00K@j1[Tg00<Lj3PTg00<ok20?Tg008hj2STg00>=k30>Tg00>\j4lTg01TmR4j1iTg006HR5j2?Tg01UMj1hTg01Ukk40;Tg01VNl<cTg00j6k308Tg01W3k407Tg00h@j2FTg005nj36Tg01W^k304Tg01XDk602Tg01Xmk401Tg003ck100Tg00=Qj2|Tg015Pj3^Tg001<j6XTg01Hll@yTg01J3j5WTg010fj1;Tg01K:j1xTg01L?j2NTg01MAj5MTg01P@j2KTg01YTj7{Tg00b[j2ETg01Z[j2<Tg01[;S01j2uTg01[Uj3CTg000`j6]Tg00oNj2dTg00SNk305Tg00?ij4aTg00@Tk706Tg00J\j6rTg00PRj8fTg00A8j7eTg01\Pl<oTg01]5mB0=Tg01][j4kTf3R6f2R7f1R8f0R9'E36p=Tg00GXR:/?9p=8g00A\R;@0589p=DP;P8g00B:P9Cap=AP8g00BaR<g00C@R=P=g00C`R>P9g00D@K06p=5P8P<P=P=P>P9Erp=UP6P<P=P=P>P7P8P9Gfp=Jf5R?P<P=P=P>f4R@P<P=P=P>P6P7FeP8P9Gfp==1S;9p=Hg01^SRAP;P;P;P4P4P?P@P6P7P8P9M<op>0:P;P;P;P;P;P;P0P9P8P7P0P6P@P?f6R0f7R4f8RBf9RCNB0=p>09P;P8g00Q6P9Cap=G1089,:7p=3P7P<P=P=P>P8P9Fep=}%;8/29p=91289,27p=vg00E@R<P6P7P8Ck=6@9p=4A6A89p=BP<P61:78P9Ckp=_A7789,E6p=@p,2ALRDp,2CLREp,3ASR:0ADERF40@AzDEFRG,qDg00FSRH#>RI#>#>RJ#>#>#>RK#gRL#`%gJRJ#`RM#YRN[g01QAPDPEPFg01R7ROP@DwPDPEPFPOP?P@P6P7Gt%Y;PDPGP?1:L7CmP;%>K#>#ORGCT%8610@G%OIRP%OKRK+0<RQ'1%89RR119G'2P<PC1048R<g00VMRS#IRT203PKRU11:P%8K11:Q[[RV%8PRWg00mkRXA~PK8UWBRK%8Q\X^BWRWp-0RYg00H6RZ%ITR[,L;R\1L;T1L;SR]'DR^'DR_g00VlR`'R%jZRa37Rb%\ZRcP;1Z;7S02P8%s;CbRd%p;Re%n;RfPf1Q;:Rg1V;IRI'A,5fRh1Uf@Ri%[=R=Pf1V;HRj,Ag,5fRkP=AP;jIRl,Ag,5fCJE=20?f>R>P9P7g00D`Rmg00G8Rn'SS03B0>;:8S04ClRob4b7b8X0;X1;W2%88Rp/271076Rq#8\p[^0;^1;^2YP911@GP@f:RrP6P0O5b3b5b6%iTRs,0<Rt/?Q%OHRu,0<Rv/?QP;P;P5P9X>;RwP51?89#hXD;X>;PtPvPwPwPwP;P;g01_21089H0;#HXC;XY;P<P<%H<PsPuPwPw%i9#HX>APTPu%HuJ0:R<N:09PQPQ%HQM<cPUPVPKPWPbPcPdPePfPfPi1Q;GRi,GI,5fRIP=PfAP;jiRi1Q;P>08;LRP'G,5fRdP=1Q;uRb9P;l/AP,5fCJE=P>Pob4b7b8X0;X1;X2Y118G,27108G/1Q10qu/?Q[[^0;^1;^2YP9%8@P@PrP6P?O5b3b5b6H07119s,2RPDPEPFPOp,4PINSf=Rof<Rvf;RtPr1:LCR5PG10C6S05/08Rx,:LRyPBP4P0P;PC10r@=3L7Rz,FLR{,?9109GR|,1{'2XE;P;Px1?r910rG,19'2XE;118sR},2p118u,2pR~PpP}PpPwPuO1R},181SYpA6Yppe:04ppP;P;P1PwP11189#hXD;X>;P8P8%H8PsP}P<M<cJ02P9H01R<P~PUPVPKPW%I[R[#I,L;1D\]'D/R`1L;[R[/D^/R`=7Za57ZPcP;Q02P81Z;6CbR^PePfPf&00H,V;RH,Ag,5fR]1GHb,5fRbP=PfPfPhPIP=AP;lHRH,Aj,5f1GHi,5f5}fE=E=P>P9P7Q031|97=6mndQ04ClRnb4b7b8X0;X1;X;;%87Rm117uRi'2117GRl,2m10q@Rq,?7107GR\,1q'2[[^0;^1;^;;P9P?P4PoP6P0O5b3b5b6b?1FLyRqP<P~PUPVPKPW1D[_/R`=7ZaRZPcP^PePfPfP]1Uf?R]P=PfPfPh1Uf0RhP=PfPkP=1AgH,5fCJE=E=P>Pnb4b7b8X0;X1;X;;X2YX=Y12m612m?106@/0?Rg#8\m[[^0;^1;^;;^2Y^=YP9114G11?uP?P4PoP6P0PCO8b3b5b6b?P<P~PUPVPKPWPZPcP^PePfPfP]PbP=PfPfPhPIP=PfPdP=1GHP,5fCJE=E=P>Pnb4b7b8X0;X1;X;;X2YX=Y126i12?l11\Q11gQ[[[^0;^1;^;;^2Y^=YP9%84%8?P?P4PoP6P0PBO8b3b5b6b?5^xEX1FL5PUPVPKPWPaPc1Z;8R5PePfPkP=PkCJP>Pnb4b7b8X0;Pp\R^0;P9PvPBO2b3b5b6PUPVPKPWPaPcP5PePfPdP=1GjP,5fCJP>Pnb4b7b8X0;11|Q118Q[^0;P9PvP4O2b3b5b65^CEXM@yPDPEPFPoPyDWPtPyO1%[MRQ56N#;%xORO/NqPDPEPFPoPyDM1KDy#;'9'93vP2PDPEPFf>RyPzDWPvPzO1=6NQ1NO{PDPEPFPyPzDM1KDz#;'9'9'9Po10t?Rz=3L6O1=6NQ#;P9PDPEPFf@R{10v0Rv=3L@DWf?Rq10o4R|=3L?RnO1=6NQ1FLn,NOPDPEPFfAR>PnDM1KDn#;'9'9'9P2P{10yBRn=3L0RfO1=6NQ#;1FLf,NOPDPEPFfBRPPfDM1KDf#;'9'9P>10qC=3L4O1=6NQ#;P9PP10{rRf=3LBO1=6NQ#;10>tRQ=3LCRN,FL,NOPDPEPFfERFPNDM1KDN#;'9'9P8WQWIP8P9O2n2001000000120000000W<WPP8P9O2n2001000000121000000bRWNXV;F{%\MRN%YNRDPrA3LB7PT1EN9RBD41<M9/BTRr'2X@N'uQ01PNPtPLQ05PTC_RE=6DB/2rX@NPDPEPNACtC6%jMRt57MCTP9PDPo1:LzPTPBD4/2rP2PDPy1:LvPT1EN8D41<M8/BTRvPDPq1:L|PTPNPMACqo4PtC@D4P9PDP{1:LnPT1EN6D41<M@/BTP3PMPDfCR@1:LQPTPBD4PDPFA3L@oPTPNPMACF@oPtC@D4R@^9v]:P?PDPP1:LfPT1ENtD41<Mt/BTPAPSPAPYP9PXg00omRSn0110300020010000XAAg010JRfPTP9E]PS1d@9b<W9W:P3PMPDfGR@A3LFqPTPNPMP7P9C@D4A7M68,<M/BTPDfIRqA3L@>PTPNPMACq@>PtC@D4]9]:P9PDfFRqfD=3LyPTPNPMP8PtC@D4A7M7t,<M/BTPDPNPMP6PtC@R6PDP9PNQ00PNPMP9P3PMPMP91:J:RJP8n10110200020020101104PJn10110000021010200=7MtCTXZD1SD6fHR6PL10q{PTC_RJP8EXPDPJPNAC6q{=7MtCTeW9W:PDfJA3L6PPTPNPMP?A7M89C@D4A7M7897M0,<M/BTPA1<M7#I#IPAPYP9PSPAPYP9PSPXn0110300020010000n0110300020010103XAAPfPTP9E]PSPDfMRDfKRS=3LFPTPNPMACDSFPtC@D4/d9b<W9W:X[NXTMP8P9O2n10110200020121101102XWNXSMP8P9O2n10110200020021101102P8P9O2W9W:P8P9O2n2001000000121000000W<X@NP8P9O2n2001000000121100000bAWMXU;WKWJWOWLWHX\;WXWCWFWGo"). Qed.

Section Loops.
Variables (C : lctx) (Ar A : AS) (md : Model) (mB : word -> option byte) (s datad wpld hd kd datas wpls ks tab wplsi : Z) (S : TSet).
Hypothesis CK : Cok C.
Hypothesis SUB : sub_live Ar A.
Hypothesis Ld : live A (Z_to_bv 64 datad) = Some kd.
Hypothesis Hkd : (4 * wpld * hd <= kd)%Z.
Hypothesis Ldr : live Ar (Z_to_bv 64 datad) = None.
Hypothesis Ld0 : live (c_A0 C) (Z_to_bv 64 datad) = None.
Hypothesis Ls : live A (Z_to_bv 64 datas) = Some ks.
Hypothesis Hks : (8 * wpls * hd <= ks)%Z.
Hypothesis Lt : live A (Z_to_bv 64 tab) = Some 256%Z.
Hypothesis Hdd : (0 <= datad < 2 ^ 64)%Z.
Hypothesis Hal : (datad mod 4 = 0)%Z.
Hypothesis Hds : (0 <= datas < 2 ^ 64)%Z.
Hypothesis Htab : (1 <= tab < 2 ^ 64)%Z.
Hypothesis Hhd : (1 <= hd < 2 ^ 24)%Z.
Hypothesis Hwpld : (1 <= wpld < 2 ^ 24)%Z.
Hypothesis Hwpls : (1 <= wpls < 2 ^ 24)%Z.
Hypothesis Hwi1 : (1 <= wplsi)%Z.
Hypothesis Hwi2 : (wplsi <= wpls)%Z.
Hypothesis Hwi3 : (wplsi <= 2 * wpld)%Z.
Variable h : Z.
Hypothesis Hwmin : Z.min wpls (2 * wpld) = wplsi.
Hypothesis Hds1 : (1 <= datas)%Z.
Hypothesis Hdsal : (datas mod 4 = 0)%Z.
Hypothesis Hdd1 : (1 <= datad)%Z.
Hypothesis Hdsr : (datas + ks + 4096 < 2 ^ 64)%Z.
Hypothesis Hddr : (datad + kd + 4096 < 2 ^ 64)%Z.
Hypothesis Htabr : (tab + 256 + 4096 < 2 ^ 64)%Z.
Hypothesis Hh2 : (2 <= h < 2 ^ 31)%Z.
Hypothesis Hhh : hd = h / 2.
Hypothesis Hm1 : (h * wpls < 2 ^ 31)%Z.
Hypothesis Hm2 : (hd * wpld < 2 ^ 31)%Z.
Hypothesis Hs : (256 <= s < 2 ^ 64)%Z.
Hypothesis Hsd : (datad + kd <= s - 208 \/ s <= datad)%Z.
Hypothesis Q136 : rdn SEGS mB (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wpls)).
Hypothesis Q128 : rdn SEGS mB (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)).
Hypothesis Q144 : rdn SEGS mB (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.min wpls (2 * wpld)))).
Hypothesis Q176 : rdn SEGS mB (Z_to_bv 64 (s - 176)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * wpls))).
Hypothesis Q184 : rdn SEGS mB (Z_to_bv 64 (s - 184)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (datas + 4 * wpls))).
Hypothesis Q160 : rdn SEGS mB (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3fffffff)).
Hypothesis Q168 : rdn SEGS mB (Z_to_bv 64 (s - 168)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2 * wpls))).
Hypothesis Q152 : rdn SEGS mB (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (h - 1))).

(* [comment removed for export] *)
Definition FTb (m : word -> option byte) : Prop := forall a : word, ~ (datad <= u a < datad + 4 * wpld * hd)%Z -> m a = mB a.

Lemma FTb_store : forall m (tgt : Z) (wv : word), W C A m md -> POSTM C Ar s mB m -> FTb m ->
  (datad <= tgt)%Z -> (tgt + 2 <= datad + 4 * wpld * hd)%Z ->
  W C A (wbytes m (Z_to_bv 64 tgt) (word_to_le_bytes 2 wv)) md /\ POSTM C Ar s mB (wbytes m (Z_to_bv 64 tgt) (word_to_le_bytes 2 wv))
  /\ FTb (wbytes m (Z_to_bv 64 tgt) (word_to_le_bytes 2 wv)).
Proof using Hdd Ld0 Ldr Hkd Ld SUB CK kd PINS.
ltac2:(KReplay.run1 (kr_t_V23LeptRb2W ()) ["Rb2L"; "Loops"] "h04__x1h14__x2h27__arithh36__sat3h46__sat4h54__x3h64__x4h74__x5h84__ffh98__varmaph:5__with;1zh<4__p1h=4__x6h>1nh?2Hah@1xhA2GdhB4TOPdhC1ahD1mhE3ATLhF2FThG2H1hH2H2hI2HWhJ2P1hK2PMhL2W1hM2WPhN1ohO3tgthP2wvhQ1yp%0p&0p;1p;3p;2p;4p;5p;?p;6p;Hp;7p;8p;9p;<p;Bg003>j13Tg00^Lj1gTg00^jj1aTg00_Mj1pTg00[9k30@Tg01_Vj1QTg006HR0j20Tg004Hj1STg008KR1j21Tg00LEj2>Tg01`Nj4iTg01H1k10?Tg01Bnk10>Tg00I?j22Tg00a2j27Tg00hjk20;Tg00dDk200Tg00iRj3{Tg00RFj1PTg00Q]j2GTg00Rej3RTg00T7j2KTg009Bj1uTg00UOj3ITg009bj1sTg00I[j2HTg00:Bj1qTg00:`j1mTg00;>j1lTg00;ij2OTg00K@j1kTg01aQj5jTg00j6j3hTg003cj1fTg00J9j2ETg00Kbj3UTg00<ok20=Tg008hj2eTg00=Qk20<Tg005nj3dTg00>=k30:Tg00>\k406Tg01b5m?05Tg00h@j2=Tg006dS00j25Tg01c=j29Tg01dEj3Aj4zTg00J\j6~Tg015Pj3ZTg000`j6cTg00?Nj4VTg01TmR2j1bTg01UMj1_Tg01Ukj4yTg01W3j4YTg01Z[j2]Tg01e?j2`Tg001<j6MTg01fGlHwTg010fj1vTg01OBj2FTg01gLj6|Tg017Qj6}Tg01O\j7tTg01h4k601Tg01<Dk802Tg01i7l9rTg00SNk303Tg00Uok404Tg00?ij4WTg00@Tj7\Tg00PRj8TTg00<Lk307Tg00A8k708Tg01\Pm<09Tg01]5lBoTg01VNl<nTf6R3f5R4f4R5g01R7R6f3R7f2R8f1R9f0R:L02p=;f7R;P3P4P6P5P7P8P9P:M9rp=<g00GXR</0:p=Bg00A\R=@039:p=6P=P8P9P:H04p=@P8g00BaR>g00C@R?P?g00C`R@P=P9g00B:RAP:CWg00D@RBF\p=4P7P>P?P?P@P8P9P:GTp=NP4P>P?P?P@P5P>P?P?P@P=P7PAP8CWPBF\P9P:GTp=:B07=9:p=8P=P9g00Q6P:CWp=LP9P>P?P?P@P:PBF\p=JP3P>P?P?P@P4P5P7P>P?P?P@P8P9P:GTGTp=DP8P>P?P?P@P9P:K08p=[P=P5P7P8P9P:EMp=C1e=:p=?g01^SRBP=P=P=P2P2P4P5P7P8P9P:N<09p=xP=P=P=P=P=P=P1P:P9P8P1P7P5P4P3P;f8R1f9R2MBop=^P=P=P0P;P0P3P4P5P7P8P9P:M<np=Xg00FSR0#3R;#3RA#3RC#3#3#3RD#gRE#aRF%gC#aRC#pRG[p,2ALRHp,2CLRIp,3ASR:0@HIRJp,1CRKp,1ARLP8p,2mdRMF;PHPIPJPKp,2ArRNp,1sROp,2mBRPP7G<%Q5p,5datadRQ/05%S;RR,14RS%SARTp,4wpldRU'>p,2hdRV'>,1QS01'0PHPIPJPKCiRW$0?&0>WRWg01T4'2PHPIPJP6p,4PINSRXPKPLP1PM17EQRYp,2kdRZp,2CKR[P4p,2LdR\%SDR]-0;RR^12<R%B]200R]R_,2<[[R`%BRRag00mkRbA{R]9UW?R]%B_\bRb^?aRcg00H6Rdg00VMRe#PRf#PRg#PRh#P,G=Ri1G=hRh5R=1G=gRj9R=i1G=fRf9R=i1G=eRe=R=i'6'6'6g00VlRk'K%udRl3I%sdRm1H=5S02%q=Rn7@81H=4?@7nS037@9S04%m=Ro%l=RpPpPp1O=<Rq1O=RRr%k?RsPpPpP>P?P?P@DjPsAh=rERt94pqCNE:PsPp%f;,E=Ru/8r1E=ARA1O=TS051E=;R;5U=%f0S06,E=Rv5U=Rw'854pPsPpPpPAPuPsPpPpPw1E=0R0Ps1Lq0,JpE:E:FD20=p@RxP:P8g00D`Ryg00G8Rz'e20<:8=dyzdB0:=<9H06Rzb8b9b:X0=X1=X5=X6=X7=Pb\a1>T8/>7,15,0S10431>T5/>4RS/07S0712<5[[[[^0=^1=^5=^6=^7=P:f:R<PQPVPUPZP9P5P4p,3HkdRaO9b2b3b4N?05%3D#3#3#3#3#3#SRD1=EYRb'0Ry11bZR{/0WR|'5Q00PyP|PHPIPJPKPL17E219g15A<R1PMF;PHPIPJPKPNPOPPP1G<%Q1'5'5P:P=Pb10D:X;=P9PQP^P`P]Pcp-0R1PlPm1H=9R2PoPpA4pq0S08PpP>P?P?P@P7E~Rq5[pPsQ08CNPxPzb8b9b:X0=W<%B:/59%B9[^0=^<1P:12Q_PQp,3HddR}O3b2b3b4P^P`P]PcPlPmP2PoPp1L0t,JpS099[pqPsQ09CNPxPzb8b9b:X0=X<112:_,59129_[^0=^<1P:%BQPQP}O3b2b3b45ZQR}Ec10DQP=Pb11:ZS0:/0WX;=P9PQP}Ec11QZR1/0WPHPIPJP6PXPKPNPLPPf?RXPMPYf>RY,7ER6PZf=S0;,9gRqPOP[PHPIPJPKPLPXPMF;PHPIPJPKPNPOPPPXG<f<S0<f;R[CVP\p,3Ldrp,3Ld0p,3SUBPQ17EXS0=,=ES0>,0:X;=PY10Q:X;=P^P`P]PcPlPm1H=8R\?@9nPoPpA4p0;R2PsP2CNPxPzb8b9b:X0=X1=10:91098[^0=^1=P:fAR2PQQ0<O3b2b3b410QYe1=E6S0?P^P`P]Pc16fe,6jR~/Kk=IdlS0@PmA@\8n9@n9PoPpPp1O=DPuPsPpPpPuP0PsQ08E:E:PxPzb8b9b:X0=X1=S0810D91089%B8[[^0=^1=S0AP:PQP2P5Q0<O4b2b3b4P^P`P]Pc16h~,6i/Kk=IdlS0<PmQ021H=37@8Q037@9S03PoPp18uAQ06#3,E=R~54pS06PsPp1L~t,JpS02PsPp180rR~18uw54pS0BPsPpA4pwAS0CPsQ09FDFDPxPzb8b9b:X0=X1=X5=X6=X7=X==S091157/04S0D123_S0E118RR41>T7/>5RT,13'0Rw10S3R3125_[[[[^0=^1=^5=^6=^7=^==S0FP:PWPQPZPVPUP2P7P<P[PaO:b2b3b45ZYS0GDCPbP}DCPBPgQ0>%b:RD'1/0{X>BPY%bgRn,1:R\/0{X;=PQ11XnQ0:'0X;=11YnS0:/01S0>11YRS0H/01P:X@=R{109:#_XQ=X@=S0IQ0:Q0HP{P{P{P=P=g01_2119:Cy#?XD=X>=S0HPYPY%?YPnPRP{P{%?DX@BPgPR%?RExS0:M:^P1P1%?1GXP^P`P]PcQ0@PmQ04PoPpPpP~Q05=U=A=U=uRu,8;PsPpPpPuPvPs18;v94p~E:E:PxPzb8b9b:X0=X1=X5=X6=X7=11:R119T'0Q071175,04[[^0=^1=^5=^6=^7=P:PVPUPZPQP2P[PaO7b2b3b4CYQ0>ePbP}DCQ0?Q0GDC1]CqQ0;,`gEMMHwPHPIPJPKPLAAX6qRqPMF;PHPIPJPKPNPOPPPqG<'5Q00PHPIPJPKPLf@RqQ0=19gY3ARYPMF;PHPIPJPKPNPOPPPYG<PHPIPJPKPL17Eq19gX5A2RXPMF;PHPIPJPKPNPOPPPXG<%QX'5'5P:PHPIPJPKPLfBRX17E219gq3APMF;PHPIPJPKPNPOPPfCRY17EX19g23AG<PHPIPJPKPLfDRL17EY19gX3AR6PMF;PHPIPJPKPNPOPPP6G<RO%Q6R6'5P9POP6P:1=E:RO,0QQ01,2O'5#vPGfFROP9O1PPP8O19dG:XNGP2P9P:O2POfERG,7ERP19gLRNP9CzPNPOPPP9PBPg17EO,=ERK/1DRD/0_X>BPG10\_X;=11GnRJ/0_RI11GRRH/0_P{Q0IPJPHP{P{P{Q0HPGPG%?GPnPRQ0:M:^RnP_P_%?_GXP^P`P]PcQ0<PmQ03PoPpQ06PsPpQ02PsPpQ0BPsPpQ0CPsA4p~tFDFDPxPzb8b9b:X0=X1=X5=X6=X7=X==Q0DQ0E115RRR/0_\3\w[[^0=^1=^5=^6=^7=^==P:PWPQPZPVPUfHRZP<P2PXPaO:Rab2b3b4CYPIe1=EPRPP^P`P]PcQ08Q0AP:PQPZP[PYO4b2b3b4P^P`P]PcQ09Q0FPab2b3b45ZGRaDC1]CNRN1`gLRLEMPBPg1=E8Rg/2K10Dg'FX>BPG12g:10\g'FX;=1=E9RE/2GRG10JER\'FRB10HERD,FGPGP\PGPD%_GP{Q0IPJPHPnPEPE%?EGXE|16he,6i/Kk16jf,6i/Kk=Idl5IdPmQ04PoPpPpP>P?P?P@A4pv018vuRu,L0,Jp5[pE}PsPp18;rRr=4puPsPpPpPvP;PsPpP>P?P?P@1L0;,JpA4pr0FtE:FDPxPzb8b9b:X0=X1=X5=X6=X7=108:118T,2:'5g00om[117S,041057127510R7'F[[[^0=^1=^5=^6=^7=P:PVPUPQPOPgP9PqP2O8b2CYPBePPPaDCPNPLEMJ01EMW?XCFP6eCVCVWJWLP9P:O2n2001000000121000000bMbBbAXB|XAyP9P:O2n2001000000121000000bCbEWHWGWFWKWIXPFXO=WDo"). Qed.

Lemma FTb_cell : forall m (x : Z) (n : nat), FTb m -> (s - 208 <= x)%Z -> (x + Z.of_nat n <= s)%Z ->
  rdn SEGS m (Z_to_bv 64 x) n = rdn SEGS mB (Z_to_bv 64 x) n.
Proof.
  intros m x n FT Hx Hn. apply rdn_ext; [rewrite u_Z2bv by lia; lia |].
  intros a Ha. rewrite u_Z2bv in Ha by lia. apply FT. nia.
Qed.

Local Ltac rg := csr; first [ reflexivity | f_equal; lia | f_equal; nia ].
Local Ltac rzm HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Local Ltac cellQ FT Q := etransitivity; [apply FTb_cell; [exact FT | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia] | exact Q].

Definition WREG (k : Z) (r0 : bvmap 5 word) : Prop :=
  getr r0 25 = Z_to_bv 64 (datas + 8 * wpls * k) /\ getr r0 26 = Z_to_bv 64 (datas + 8 * wpls * k) /\
  getr r0 12 = Z_to_bv 64 (datas + 8 * wpls * k + 4 * wpls) /\
  getr r0 6 = Z_to_bv 64 (2 ^ 64 - 1 - (datas + 8 * wpls * k + 4 * wpls)) /\
  getr r0 29 = Z_to_bv 64 1 /\ getr r0 24 = Z_to_bv 64 1 /\ getr r0 30 = Z_to_bv 64 1 /\ getr r0 27 = Z_to_bv 64 1 /\
  getr r0 7 = Z_to_bv 64 (2 ^ 64 - 1 - tab) /\ getr r0 22 = Z_to_bv 64 0xffffffffaaaaaaaa /\
  getr r0 1 = Z_to_bv 64 (datad + 4 * wpld * k) /\ getr r0 28 = Z_to_bv 64 0 /\ getr r0 20 = Z_to_bv 64 2 /\
  getr r0 11 = Z_to_bv 64 tab.

Lemma rb_word1 : forall (r0 r : bvmap 5 word) (m : word -> option byte) (k j : Z),
  W C A m md -> POSTM C Ar s mB m -> FTb m -> (0 <= k < hd)%Z -> (0 <= j < wplsi)%Z ->
  WREG k r0 -> regs_agree (fun x => In x [8; 9; 13; 19; 21; 23; 31]%list) r0 r ->
  getr r 19 = Z_to_bv 64 (datad + 4 * wpld * k + 2 * j) -> getr r 8 = Z_to_bv 64 (datad + 4 * wpld * k + 2 * j) ->
  getr r 21 = Z_to_bv 64 (4 * j) -> getr r 23 = Z_to_bv 64 (wplsi - j) ->
  exists r1 m1, msteps SEGS (mkst r (Z_to_bv 64 0xa72bc) m al_rom) (mkst r1 (Z_to_bv 64 0xa735c) m1 al_rom)
    /\ W C A m1 md /\ POSTM C Ar s mB m1 /\ FTb m1
    /\ regs_agree (fun x => In x [8; 9; 13; 19; 21; 23; 31]%list) r0 r1
    /\ getr r1 19 = Z_to_bv 64 (datad + 4 * wpld * k + 2 * (j + 1)) /\ getr r1 8 = Z_to_bv 64 (datad + 4 * wpld * k + 2 * (j + 1))
    /\ getr r1 21 = Z_to_bv 64 (4 * (j + 1)) /\ getr r1 23 = Z_to_bv 64 (wplsi - (j + 1)).
Proof.
  intros r0 r m k j HW PM FT Hk Hj WR AG E19 E8 E21 E23.
  destruct WR as (W25 & W26 & W12 & W6 & W29 & W24 & W30 & W27 & W7 & W22 & W1 & W28 & W20 & W11).
  assert (Bk : (wpld * (k + 1) <= wpld * hd)%Z) by nia.
  assert (Bs : (8 * wpls * k + 8 * wpls <= ks)%Z) by nia.
  assert (Kd : (0 <= wpld * k)%Z) by nia.
  assert (Ks : (0 <= wpls * k)%Z) by nia.
  assert (Ud : u (Z_to_bv 64 datad) = datad) by (apply u_Z2bv; lia).
  assert (Us : u (Z_to_bv 64 datas) = datas) by (apply u_Z2bv; lia).
  assert (Gd : (4096 <= datad)%Z).
  { destruct (blk_range C A m md (Z_to_bv 64 datad) kd CK HW Ld ltac:(nia)) as [G _]. rewrite Ud in G. exact G. }
  destruct (r90w_rd4_blk C A m md (Z_to_bv 64 datas) ks (datas + 8 * wpls * k + 4 * j) CK HW Ls
              ltac:(rewrite Us; lia) ltac:(rewrite Us; lia) ltac:(rewrite Us; lia)) as (b1 & v1 & R1 & _).
  destruct (r90w_rd4_blk C A m md (Z_to_bv 64 datas) ks (datas + 8 * wpls * k + 4 * wpls + 4 * j) CK HW Ls
              ltac:(rewrite Us; lia) ltac:(rewrite Us; lia) ltac:(rewrite Us; lia)) as (b2 & v2 & R2 & _).
  pose proof (rdn_length _ _ _ _ _ R1) as LB1. pose proof (rdn_length _ _ _ _ _ R2) as LB2.
  rewrite <- (RefStep3.Z_to_le_bytes_to_Z b1), LB1 in R1. rewrite <- (RefStep3.Z_to_le_bytes_to_Z b2), LB2 in R2.
  pose proof (rbw_tab_rd C A m md tab CK HW Lt ltac:(lia) ltac:(lia)) as TB.
  assert (Hal2 : (datad mod 2 = 0)%Z).
  { apply Z.mod_divide; [lia|]. apply (Z.divide_trans 2%Z 4%Z); [exists 2%Z; reflexivity | apply Z.mod_divide; [lia | exact Hal]]. }
  assert (L4 : ((datad + 4 * wpld * k) mod 4 = 0)%Z).
  { replace (datad + 4 * wpld * k)%Z with (datad + (wpld * k) * 4)%Z by ring. rewrite Z_mod_plus_full. exact Hal. }
  assert (A1 : ((datas + 8 * wpls * k + 4 * j) mod 4 = 0)%Z).
  { replace (datas + 8 * wpls * k + 4 * j)%Z with (datas + (2 * wpls * k + j) * 4)%Z by ring. rewrite Z_mod_plus_full. exact Hdsal. }
  assert (A2 : ((datas + 8 * wpls * k + 4 * wpls + 4 * j) mod 4 = 0)%Z).
  { replace (datas + 8 * wpls * k + 4 * wpls + 4 * j)%Z with (datas + (2 * wpls * k + wpls + j) * 4)%Z by ring.
    rewrite Z_mod_plus_full. exact Hdsal. }
  assert (A3 : ((datad + 4 * wpld * k + 2 * j) mod 2 = 0)%Z).
  { replace (datad + 4 * wpld * k + 2 * j)%Z with (datad + (2 * wpld * k + j) * 2)%Z by ring. rewrite Z_mod_plus_full. exact Hal2. }
  destruct (rbl_flip2_bounds (datad + 4 * wpld * k) wpld j ltac:(lia) L4 ltac:(lia)) as (FL1 & FL2).
  assert (SK : store_ok SEGS m (Z_to_bv 64 (Z.lxor (datad + 4 * wpld * k + 2 * j) 2)) 2 = true).
  { apply (r90w_sok_blk C A m md (Z_to_bv 64 datad) kd _ 2 CK HW Ld); rewrite ?Ud; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  destruct (rb_W al_rom r m (datas + 8 * wpls * k) (datas + 8 * wpls * k + 4 * wpls) (4 * j) (datad + 4 * wpld * k + 2 * j)
              (datad + 4 * wpld * k) tab (wplsi - j) (bytes_le_to_Z b1) (bytes_le_to_Z b2) (rbw_tb m tab)
              ltac:(lia) ltac:(lia) ltac:(lia) A1 ltac:(lia) ltac:(lia) A2 ltac:(lia) ltac:(lia) ltac:(lia) A3
              ltac:(lia) ltac:(lia) ltac:(lia) R1 R2 TB SK
              ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg)
              ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg))
    as (r1 & wv & RUN & F19 & F8 & F21 & F23 & AG1).
  destruct (FTb_store m (Z.lxor (datad + 4 * wpld * k + 2 * j) 2) wv HW PM FT ltac:(lia) ltac:(lia)) as (HW1 & PM1 & FT1).
  exists r1, (wbytes m (Z_to_bv 64 (Z.lxor (datad + 4 * wpld * k + 2 * j) 2)) (word_to_le_bytes 2 wv)).
  split; [exact RUN|]. split; [exact HW1|]. split; [exact PM1|]. split; [exact FT1|].
  split; [eapply regs_agree_trans; [exact AG | exact AG1]|].
  rewrite F19, F8, F21, F23. repeat split; f_equal; lia.
Qed.

Lemma rb_words_W : forall (n : nat) (r0 r : bvmap 5 word) (m : word -> option byte) (k j : Z),
  W C A m md -> POSTM C Ar s mB m -> FTb m -> (0 <= k < hd)%Z -> (0 <= j)%Z -> (Z.of_nat n = wplsi - 1 - j)%Z ->
  WREG k r0 -> regs_agree (fun x => In x [8; 9; 13; 19; 21; 23; 31]%list) r0 r ->
  getr r 19 = Z_to_bv 64 (datad + 4 * wpld * k + 2 * j) -> getr r 8 = Z_to_bv 64 (datad + 4 * wpld * k + 2 * j) ->
  getr r 21 = Z_to_bv 64 (4 * j) -> getr r 23 = Z_to_bv 64 (wplsi - j) ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTb m' -> regs_agree (fun x => In x [8; 9; 13; 19; 21; 23; 31]%list) r0 r' ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0xa7360) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0xa72bc) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros r0 r m k j HW PM FT Hk Hj Hn WR AG E19 E8 E21 E23 K.
  - destruct (rb_word1 r0 r m k j HW PM FT Hk ltac:(lia) WR AG E19 E8 E21 E23)
      as (r1 & m1 & RUN & HW1 & PM1 & FT1 & AG1 & F19 & F8 & F21 & F23).
    rzm HW RUN.
    assert (RX : msteps SEGS (mkst r1 (Z_to_bv 64 0xa735c) m1 al_rom) (mkst r1 (Z_to_bv 64 0xa7360) m1 al_rom)).
    { apply rb_Wx. rewrite F23. f_equal. lia. }
    rzm HW1 RX. exact (K m1 r1 HW1 PM1 FT1 AG1).
  - destruct (rb_word1 r0 r m k j HW PM FT Hk ltac:(lia) WR AG E19 E8 E21 E23)
      as (r1 & m1 & RUN & HW1 & PM1 & FT1 & AG1 & F19 & F8 & F21 & F23).
    rzm HW RUN.
    assert (RN : msteps SEGS (mkst r1 (Z_to_bv 64 0xa735c) m1 al_rom) (mkst r1 (Z_to_bv 64 0xa72bc) m1 al_rom)).
    { apply (rb_Wn al_rom r1 m1 (wplsi - (j + 1))); [lia | exact F23]. }
    rzm HW1 RN.
    exact (IH r0 r1 m1 k (j + 1)%Z HW1 PM1 FT1 Hk ltac:(lia) ltac:(lia) WR AG1 F19 F8 F21 F23 K).
Qed.

Definition RREG (r0 : bvmap 5 word) : Prop :=
  getr r0 2 = Z_to_bv 64 (s - 208) /\ getr r0 10 = Z_to_bv 64 wpld /\ getr r0 14 = Z_to_bv 64 (4 * wpls) /\
  getr r0 18 = Z_to_bv 64 datad /\ getr r0 29 = Z_to_bv 64 1 /\ getr r0 11 = Z_to_bv 64 tab /\
  getr r0 24 = Z_to_bv 64 1 /\ getr r0 7 = Z_to_bv 64 (2 ^ 64 - 1 - tab) /\ getr r0 22 = Z_to_bv 64 0xffffffffaaaaaaaa /\
  getr r0 28 = Z_to_bv 64 0 /\ getr r0 20 = Z_to_bv 64 2.

Lemma rb_rows_W : forall (n : nat) (r0 r : bvmap 5 word) (m : word -> option byte) (k : Z),
  W C A m md -> POSTM C Ar s mB m -> FTb m -> (0 <= k)%Z -> (Z.of_nat n = hd - 1 - k)%Z ->
  RREG r0 -> regs_agree (fun x => In x [1; 5; 6; 8; 9; 12; 13; 15; 16; 17; 19; 21; 23; 25; 26; 27; 30; 31]%list) r0 r ->
  getr r 15 = Z_to_bv 64 (2 * k * wpls) -> getr r 16 = Z_to_bv 64 (k * wpld) -> getr r 17 = Z_to_bv 64 k ->
  getr r 5 = Z_to_bv 64 (2 * k) ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTb m' ->
     regs_agree (fun x => In x [1; 5; 6; 8; 9; 12; 13; 15; 16; 17; 19; 21; 23; 25; 26; 27; 30; 31]%list) r0 r' ->
     getr r' 15 = Z_to_bv 64 (2 * (hd - 1) * wpls) -> getr r' 16 = Z_to_bv 64 ((hd - 1) * wpld) ->
     getr r' 17 = Z_to_bv 64 (hd - 1) -> getr r' 5 = Z_to_bv 64 (2 * (hd - 1)) ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0xa7360) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0xa71e8) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros r0 r m k HW PM FT Hk Hn RR AG E15 E16 E17 E5 K.
  all: pose proof RR as (R2 & R10 & R14 & R18 & R29 & R11 & R24 & R7 & R22 & R28 & R20).
  all: assert (B1 : (wpls * (k + 1) <= wpls * hd)%Z) by nia.
  all: assert (B2 : (wpld * (k + 1) <= wpld * hd)%Z) by nia.
  all: assert (B3 : (2 * hd <= h)%Z) by (rewrite Hhh; apply Z.mul_div_le; lia).
  all: assert (B4 : (2 * (k + 1) * wpls <= h * wpls)%Z) by nia.
  all: assert (B5 : ((k + 1) * wpld <= hd * wpld)%Z) by nia.
  all: destruct (rb_R al_rom r m s k wpls wpld datas datad tab
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(nia) ltac:(nia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(nia) ltac:(lia) ltac:(nia)
          ltac:(cellQ FT Q136) ltac:(cellQ FT Q128) ltac:(cellQ FT Q144) ltac:(cellQ FT Q176) ltac:(cellQ FT Q184)
          ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg))
        as (r1 & RUN1 & G26 & G25 & G1 & G27 & G21 & G8 & G19 & G12 & G6 & G30 & G23 & AG1).
  all: rzm HW RUN1.
  all: apply (rb_words_W (Z.to_nat (wplsi - 1)) r1 r1 m k 0 HW PM FT ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia));
    [ unfold WREG; repeat split; rg | apply regs_agree_refl | rg | rg | rg | rg | ].
  all: intros m' r' HW' PM' FT' AG'.
  - assert (Ek : k = (hd - 1)%Z) by lia. subst k.
    apply (K m' r' HW' PM' FT'); [| rg | rg | rg | rg].
    eapply regs_agree_trans; [exact AG |]. eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG'].
  - destruct (rb_Rn al_rom r' m' s k h wpls wpld ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(cellQ FT' Q160) ltac:(cellQ FT' Q168) ltac:(cellQ FT' Q152)
                ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg) ltac:(rg))
      as (r2 & RUN2 & H17 & H5 & H16 & H15 & AG2).
    rzm HW' RUN2.
    apply (IH r0 r2 m' (k + 1)%Z HW' PM' FT' ltac:(lia) ltac:(lia) RR); [| exact H15 | exact H16 | exact H17 | exact H5 | exact K].
    eapply regs_agree_trans; [exact AG |]. eapply regs_agree_trans; [regs_agree_weaken AG1 |].
    eapply regs_agree_trans; [regs_agree_weaken AG' | regs_agree_weaken AG2].
Qed.

End Loops.
End Rb2L.

(* [comment removed for export] *)
Definition RB2_STACK : Z := 208 + 112 + LSF.
Definition PC_pixReduceRankBinary2 : Z := 0xa6f20.

Definition RBCu (s : Z) (ret : word) (regs : bvmap 5 word) : list (Z * word) :=
  [(s - 8, ret); (s - 16, getr regs 8); (s - 24, getr regs 9); (s - 32, getr regs 18); (s - 40, getr regs 19); (s - 48, getr regs 20);
   (s - 56, getr regs 21); (s - 64, getr regs 22); (s - 72, getr regs 23); (s - 80, getr regs 24); (s - 88, getr regs 25);
   (s - 96, getr regs 26); (s - 104, getr regs 27)]%Z.

Section Rb2W.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma rbm_D_wp : forall C A0 Aw m0 m md (s pixd tab wpls wpld h datas : Z), Cok C ->
  W C Aw m md -> POSTM C A0 s m0 m -> sub_live A0 Aw ->
  (0 <= c_top C - LSTK)%Z -> (c_top C - LSTK <= s - 208)%Z -> (s <= c_top C)%Z -> (s < 2 ^ 64)%Z ->
  W C Aw (MRB_D m s pixd tab wpls wpld h datas) md /\ POSTM C A0 s m0 (MRB_D m s pixd tab wpls wpld h datas).
Proof.
  intros C A0 Aw m0 m md s pixd tab wpls wpld h datas CK HW PM SB H0 Hlo Hhi Hs.
  unfold MRB_D. destruct (wpls <? 2 * wpld)%Z; cbv beta iota zeta; wp_win CK.
Qed.

Lemma rbm_D_out : forall m (s pixd tab wpls wpld h datas : Z) (x : word), (208 <= s)%Z -> (s < 2 ^ 64)%Z ->
  ~ (s - 208 <= u x < s - 136)%Z -> MRB_D m s pixd tab wpls wpld h datas x = m x.
Proof.
  intros m s pixd tab wpls wpld h datas x Hs0 Hs Hx.
  unfold MRB_D. destruct (wpls <? 2 * wpld)%Z; cbv beta iota zeta;
    rewrite !wbytes_outside; try reflexivity; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma rbm_D_cells : forall m (s pixd tab wpls wpld h datas : Z), (208 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS (MRB_D m s pixd tab wpls wpld h datas) (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.min wpls (2 * wpld)))) /\
  rdn SEGS (MRB_D m s pixd tab wpls wpld h datas) (Z_to_bv 64 (s - 176)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * wpls))) /\
  rdn SEGS (MRB_D m s pixd tab wpls wpld h datas) (Z_to_bv 64 (s - 184)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (datas + 4 * wpls))) /\
  rdn SEGS (MRB_D m s pixd tab wpls wpld h datas) (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3fffffff)) /\
  rdn SEGS (MRB_D m s pixd tab wpls wpld h datas) (Z_to_bv 64 (s - 168)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2 * wpls))) /\
  rdn SEGS (MRB_D m s pixd tab wpls wpld h datas) (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (h - 1))) /\
  rdn SEGS (MRB_D m s pixd tab wpls wpld h datas) (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 tab)) /\
  rdn SEGS (MRB_D m s pixd tab wpls wpld h datas) (Z_to_bv 64 (s - 200)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)).
Proof.
  intros m s pixd tab wpls wpld h datas Hs0 Hs.
  unfold MRB_D. destruct (Z.ltb_spec wpls (2 * wpld)) as [Hlt | Hge]; cbv beta iota zeta;
    [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; repeat match goal with |- _ /\ _ => split end; rdn_solve.
Qed.



(* [comment removed for export] *)
Theorem pixReduceRankBinary2_W : forall fr cs C Ar A m md regs (s pixs rc w h cm datas tab : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + RB2_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 tab ->
  PIXat m pixs (hdvr rc w h 1 cm datas) -> O23LeptPixHdrT2.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  live Ar (Z_to_bv 64 datas) = None -> live (c_A0 C) (Z_to_bv 64 datas) = None -> pixs <> datas ->
  live A (Z_to_bv 64 tab) = Some 256%Z -> (0 <= tab < 2 ^ 64)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_pixT (4 * (wpl_of (w / 2) 1 * (h / 2))) <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     cs_kept regs regs' -> POSTM C Ar s m m' -> LIVKe A datas m m' -> PIXat m' pixs (hdvr rc w h 1 cm datas) ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd data, getr regs' 10 = Z_to_bv 64 pixd /\ (2 <= w)%Z /\ (2 <= h)%Z /\ O23LeptPixHdrT2.hdr_ok (w / 2) (h / 2) 1 /\
             O23LeptPixCreateT2.pixr_new C A A' m' pixd data (set_data (O23LeptPixHdrT2.pix_hdr (w / 2) (h / 2) 1) data)) ) ->
     aroom A' vm' (kR - RK_pix) (bR - RB_pixT (4 * (wpl_of (w / 2) 1 * (h / 2)))) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (0xa6f20 : word) m al_rom) md) S.
Proof using P16 PINS.
  intros fr cs C Ar A m md regs s pixs rc w h cm datas tab ret S CK HW FZ SUB H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PXs HOK Hw Hh Lps Lds Ldr Ld0 NEsd Lt Htab kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold RB2_STACK, LSF in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (ck_top C CK) as CT.
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof (wf_data _ WFs) as Rds. cbn [p_data hdvr] in Rds.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  assert (ALps8 : (pixs mod 8 = 0)%Z) by (clear - ALps; Z.div_mod_to_equations; lia).
  pose proof (rbw_wpl1 w ltac:(lia)) as Wpls.
  pose proof (rbw_pos (wpl_of w 1) h ltac:(lia) ltac:(lia)) as Pds.
  destruct (blk_range C A m md (Z_to_bv 64 datas) _ CK HW Lds Pds) as [Gds TOPds]. rewrite u_Z2bv in Gds, TOPds by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lds) as (_ & ALds & _). rewrite u_Z2bv in ALds by lia.
  destruct (blk_range C A m md (Z_to_bv 64 tab) 256 CK HW Lt ltac:(lia)) as [Gtb TOPtb]. rewrite u_Z2bv in Gtb, TOPtb by lia.
  assert (NEsdw : Z_to_bv 64 pixs <> Z_to_bv 64 datas) by (intros E; apply (f_equal bv_unsigned) in E; rewrite !u_Z2bv in E by lia; lia).
  pose proof (blk_apart C A m md _ _ _ _ CK HW Lps Lds NEsdw ltac:(lia) ltac:(lia)) as APsd. rewrite !u_Z2bv in APsd by lia.
  assert (LKS : forall (A2 : AS) (M M' : word -> option byte) md2 (lo hi : Z), W C A2 M md2 -> sub_live A A2 -> (c_top C - LSTK <= lo)%Z ->
            (forall x : word, ~ (lo <= u x < hi)%Z -> M' x = M x) -> LIVKe A datas M M').
  { intros A2 M M' md2 lo hi HWM SB Hlo' OUTM q k i Lq NEq Hi.
    destruct (blk_range C A2 M md2 q k CK HWM (SB _ _ Lq) ltac:(lia)) as [Gq TOPq].
    apply OUTM. unfold at_. rewrite u_Z2bv by (pose proof (u64_range q); lia). lia. }
  destruct (rb_A1 (fx := mkFP fr cs) al_rom regs m s pixs tab (hdvr rc w h 1 cm datas) ret ltac:(lia) Hs64 Hs16 ltac:(lia) ALps8 PXs ltac:(lia) eq_refl
              (W_sok_win C A m md (s - 208) 208 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q18 & Q20 & Q21 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (MRB_A m s (hdvr rc w h 1 cm datas) ret regs) md /\ POSTM C Ar s m (MRB_A m s (hdvr rc w h 1 cm datas) ret regs))
    by (unfold MRB_A, DIMB, FRB; cbn [p_w p_h p_d hdvr]; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall x : word, ~ (s - 208 <= u x < s)%Z -> MRB_A m s (hdvr rc w h 1 cm datas) ret regs x = m x).
  { intros x Hx. unfold MRB_A, DIMB, FRB. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (CE1 : cellsZ (MRB_A m s (hdvr rc w h 1 cm datas) ret regs) (RBCu s ret regs)).
  { unfold MRB_A, DIMB, FRB, RBCu. cbn [cellsZ p_w p_h p_d hdvr]. repeat split; rdn_solve. }
  assert (R112 : rdn SEGS (MRB_A m s (hdvr rc w h 1 cm datas) ret regs) (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))).
  { unfold MRB_A, DIMB. cbn [p_w p_h p_d hdvr]. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (R108 : rdn SEGS (MRB_A m s (hdvr rc w h 1 cm datas) ret regs) (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))).
  { unfold MRB_A, DIMB. cbn [p_w p_h p_d hdvr]. rdn_peel1. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (LK1 : LIVKe A datas m (MRB_A m s (hdvr rc w h 1 cm datas) ret regs)) by exact (LKS A m _ md (s - 208)%Z s HW (sub_live_refl A) ltac:(lia) OUT1).
  assert (PXs1 : PIXat (MRB_A m s (hdvr rc w h 1 cm datas) ret regs) pixs (hdvr rc w h 1 cm datas)) by (apply (PIXat_frame m _ _ _ PXs); intros x Hx; apply OUT1; lia).
  set (M1 := MRB_A m s (hdvr rc w h 1 cm datas) ret regs) in *.
  destruct (Z.eq_dec h 1) as [Eh1 | Hh1].
  - rewrite Eh1 in R112.
    destruct (rb_Ah (fx := mkFP fr cs) al_rom r1 M1 s ltac:(lia) Hs64 R112 (W_sev_got C A M1 md HW1) (W_sev C A M1 md HW1) Q2)
      as (r2 & RUN2 & V1 & V10 & V11 & V12 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    apply (returnErrorPtr_W (fx := mkFP fr cs) C A M1 md r2 (s - 208) _ _ 21 20 _ (Z_to_bv 64 0) S CK HW1 ltac:(csr; reflexivity)
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity)
             V10 V11 V12 str_rb2_hs str_rb2).
    intros m3 r3 HW3 OUT3 GR3 CS3 A10. unfold LSF in OUT3.
    replace (Z_to_bv 64 0xa73b4) with (0xa73b4 : word) by (apply bv_eq; reflexivity).
    assert (CE3 : cellsZ m3 (RBCu s ret regs)) by (apply (cellsZ_out M1 m3 (s - 208 - (16 + 3376)) (s - 208)); [exact OUT3 | unfold RBCu; repeat constructor; cbn [fst]; lia | exact CE1]).
    unfold RBCu in CE3.
    destruct (rb_E (fx := mkFP fr cs) al_rom r3 m3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) Hs64 Hret CE3 ltac:(csr; reflexivity))
      as (r4 & RUN4 & W2 & W1 & W10 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
    assert (LK3 : LIVKe A datas m m3)
      by (eapply LIVKe_trans; [exact LK1 | exact (LKS A M1 m3 md (s - 208 - (16 + 3376))%Z (s - 208)%Z HW1 (sub_live_refl A) ltac:(lia) OUT3)]).
    rewrite <- (with_vmmaps_same md). apply (HK fr cs A m3 (m_vmmaps md) r4).
    + rewrite with_vmmaps_same. exact HW3.
    + exact FZ.
    + intros r _. reflexivity.
    + apply cs_kept_intro; csr; reflexivity.
    + eapply POSTM_trans; [exact PM1 |]. apply (POSTM_sub C Ar A s M1 m3 SUB).
      eapply (POSTM_range C A M1 md m3); [exact CK | exact HW1 | exact OUT3 | lia | lia | lia].
    + exact LK3.
    + exact (LIVKe_pix A datas m m3 pixs (hdvr rc w h 1 cm datas) LK3 Lps NEsd Rds PXs).
    + left. split; [rewrite W10; exact A10 | intros q; reflexivity].
    + pose proof (RB_pixT_nonneg (4 * (wpl_of (w / 2) 1 * (h / 2)))). apply (aroom_mono A (m_vmmaps md) kR bR _ _ Hrm); room_consts; lia.
  - assert (Hh2' : (2 <= h)%Z) by lia.
    destruct (rb_A2 (fx := mkFP fr cs) al_rom r1 M1 s pixs h (hdvr rc w h 1 cm datas) ltac:(lia) Hs64 ltac:(lia) ALps8 PXs1 ltac:(lia) ltac:(lia)
                (W_sok_win C A M1 md (s - 136) 16 CK HW1 ltac:(lia) ltac:(cbn; lia)) R112 Q2 Q18)
      as (r2 & RUN2 & V1 & V10 & V11 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    assert (WP2 : W C A (MRB_A2 M1 s (hdvr rc w h 1 cm datas)) md /\ POSTM C Ar s m (MRB_A2 M1 s (hdvr rc w h 1 cm datas))) by (unfold MRB_A2; cbn [p_wpl p_data hdvr]; wp_win CK).
    destruct WP2 as [HW2 PM2].
    assert (OUT2 : forall x : word, ~ (s - 136 <= u x < s - 120)%Z -> MRB_A2 M1 s (hdvr rc w h 1 cm datas) x = M1 x).
    { intros x Hx. unfold MRB_A2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (R136 : rdn SEGS (MRB_A2 M1 s (hdvr rc w h 1 cm datas)) (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (wpl_of w 1)))).
    { unfold MRB_A2. cbn [p_wpl p_data hdvr]. rdn_solve. }
    assert (R128 : rdn SEGS (MRB_A2 M1 s (hdvr rc w h 1 cm datas)) (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas))).
    { unfold MRB_A2. cbn [p_wpl p_data hdvr]. rdn_solve. }
    assert (R112b : rdn SEGS (MRB_A2 M1 s (hdvr rc w h 1 cm datas)) (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)))
      by (eapply (rdn_after M1 _ (s - 136) (s - 120)); [exact OUT2 | lia | cbn; lia | cbn; lia | exact R112]).
    assert (R108b : rdn SEGS (MRB_A2 M1 s (hdvr rc w h 1 cm datas)) (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)))
      by (eapply (rdn_after M1 _ (s - 136) (s - 120)); [exact OUT2 | lia | cbn; lia | cbn; lia | exact R108]).
    assert (CE2 : cellsZ (MRB_A2 M1 s (hdvr rc w h 1 cm datas)) (RBCu s ret regs)) by (apply (cellsZ_out M1 _ (s - 136) (s - 120)); [exact OUT2 | unfold RBCu; repeat constructor; cbn [fst]; lia | exact CE1]).
    assert (LK2 : LIVKe A datas m (MRB_A2 M1 s (hdvr rc w h 1 cm datas)))
      by (eapply LIVKe_trans; [exact LK1 | exact (LKS A M1 _ md (s - 136)%Z (s - 120)%Z HW1 (sub_live_refl A) ltac:(lia) OUT2)]).
    assert (PXs2 : PIXat (MRB_A2 M1 s (hdvr rc w h 1 cm datas)) pixs (hdvr rc w h 1 cm datas)) by (apply (PIXat_frame M1 _ _ _ PXs1); intros x Hx; apply OUT2; lia).
    set (M2 := MRB_A2 M1 s (hdvr rc w h 1 cm datas)) in *.
    apply (V23LeptPadBitsW.padbits_W (fx := mkFP fr cs) C Ar A M2 md r2 (s - 208) pixs (hdvr rc w h 1 cm datas) _ S CK HW2 SUB ltac:(csr; reflexivity)
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity) V10 V11 PXs2
             ltac:(left; reflexivity) ltac:(cbn [p_w hdvr]; lia) ltac:(cbn [p_h hdvr]; lia) eq_refl Lps Lds Ldr Ld0 NEsdw).
    intros m3 r3 HW3 CS3 PM3 PXs3 FR3 PB3.
    replace (Z_to_bv 64 0xa70a0) with (0xa70a0 : word) by (apply bv_eq; reflexivity).
    cbn [p_data p_wpl p_h hdvr] in FR3. unfold LSF in FR3.
    assert (OUT3 : forall x : word, (s - 208 <= u x)%Z -> m3 x = M2 x) by (intros x Hx; apply FR3; lia).
    assert (F3 : forall (a : Z) (n : nat), (s - 208 <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z -> rdn SEGS m3 (Z_to_bv 64 a) n = rdn SEGS M2 (Z_to_bv 64 a) n).
    { intros a n Ha Hn. apply rdn_ext; [rewrite u_Z2bv by lia; lia |]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply OUT3. lia. }
    assert (CE3 : cellsZ m3 (RBCu s ret regs)).
    { apply (cellsZ_keep M2 m3); [| exact CE2]. unfold RBCu. repeat constructor; cbn [fst]; first [lia | intros x Hx; apply OUT3; lia]. }
    assert (LK3 : LIVKe A datas M2 m3).
    { intros q k i Lq NEq Hi.
      destruct (blk_range C A M2 md q k CK HW2 Lq ltac:(lia)) as [Gq TOPq].
      destruct (blk_apart C A M2 md q (Z_to_bv 64 datas) k _ CK HW2 Lq Lds NEq ltac:(lia) ltac:(lia)) as [D|D]; rewrite u_Z2bv in D by lia;
        apply FR3; unfold at_; rewrite u_Z2bv by (pose proof (u64_range q); lia); lia. }
    assert (LK03 : LIVKe A datas m m3) by (eapply LIVKe_trans; [exact LK2 | exact LK3]).
    assert (PM03 : POSTM C Ar s m m3) by (eapply POSTM_trans; [exact PM2 | eapply POSTM_mono; [| exact PM3]; lia]).
    assert (R108c : rdn SEGS m3 (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))) by (rewrite F3 by (cbn; lia); exact R108b).
    assert (R112c : rdn SEGS m3 (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))) by (rewrite F3 by (cbn; lia); exact R112b).
    destruct (rb_B (fx := mkFP fr cs) al_rom r3 m3 s w h ltac:(lia) Hs64 ltac:(lia) ltac:(lia) R108c R112c ltac:(csr; reflexivity))
      as (r4 & RUN4 & B1 & B10 & B11 & B12 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
    assert (Q4 : getr r4 4 = getr regs 4) by (csr; reflexivity). rewrite H4 in Q4.
    assert (TAILN : forall A1 m4 vm1 r5, W C A1 m4 (with_vmmaps vm1 md) -> cs_kept r4 r5 -> POSTM C A (s - 208) m3 m4 -> getr r5 10 = Z_to_bv 64 0 ->
              (forall q, live A1 q = live A q) -> aroom A1 vm1 (kR - RK_pix) (bR - RB_pixT (4 * (wpl_of (w / 2) 1 * (h / 2)))) ->
              realizes SEGS (mkCfg (@mkst (mkFP fr cs) r5 (Z_to_bv 64 0xa70c8) m4 al_rom) (with_vmmaps vm1 md)) S).
    { intros A1 m4 vm1 r5 HW4 CS4 PM4 R10 LIVEQ Hrm4.
      replace (Z_to_bv 64 0xa70c8) with (0xa70c8 : word) by (apply bv_eq; reflexivity).
      assert (SUBa : sub_live A A1) by (apply sub_live_eq; exact LIVEQ).
      assert (SUBr : sub_live Ar A1) by (eapply sub_live_trans; [exact SUB | exact SUBa]).
      assert (PM04 : POSTM C Ar s m m4) by (eapply POSTM_trans; [exact PM03 | apply (POSTM_sub C Ar A s m3 m4 SUB); eapply POSTM_mono; [| exact PM4]; lia]).
      destruct (rb_Cn (fx := mkFP fr cs) al_rom r5 m4 s ltac:(lia) Hs64 (W_sok_win C A1 m4 _ (s - 120) 8 CK HW4 ltac:(lia) ltac:(cbn; lia))
                  (W_sev_got C A1 m4 _ HW4) (W_sev C A1 m4 _ HW4) ltac:(csr; reflexivity) R10)
        as (r6 & RUN6 & N1 & N10 & N11 & N12 & AG6).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |].
      assert (WP5 : W C A1 (wbytes m4 (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm1 md) /\
                    POSTM C Ar s m (wbytes m4 (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0)))) by wp_win CK.
      destruct WP5 as [HW5 PM5].
      assert (OUT5 : forall x : word, ~ (s - 120 <= u x < s - 112)%Z -> wbytes m4 (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0)) x = m4 x).
      { intros x Hx. rewrite wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
      set (M5 := wbytes m4 (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0))) in *.
      apply (returnErrorPtr_W (fx := mkFP fr cs) C A1 M5 _ r6 (s - 208) _ _ 13 20 _ (Z_to_bv 64 0) S CK HW5 ltac:(csr; reflexivity)
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) N1 ltac:(red; apply bv_eq; reflexivity)
               N10 N11 N12 str_rb2_pixd str_rb2).
      intros m6 r7 HW6 OUT6 GR6 CS6 A10. unfold LSF in OUT6.
      replace (Z_to_bv 64 0xa73b4) with (0xa73b4 : word) by (apply bv_eq; reflexivity).
      assert (CE6 : cellsZ m6 (RBCu s ret regs)).
      { apply (cellsZ_out M5 m6 (s - 208 - (16 + 3376)) (s - 208)); [exact OUT6 | unfold RBCu; repeat constructor; cbn [fst]; lia |].
        apply (cellsZ_out m4 M5 (s - 120) (s - 112)); [exact OUT5 | unfold RBCu; repeat constructor; cbn [fst]; lia |].
        apply (cellsZ_frm C (s - 208) m3 m4 _ CK (proj1 PM4) ltac:(lia)); [unfold RBCu; repeat constructor; cbn [fst]; lia | exact CE3]. }
      unfold RBCu in CE6.
      destruct (rb_E (fx := mkFP fr cs) al_rom r7 m6 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) Hs64 Hret CE6 ltac:(csr; reflexivity))
        as (r8 & RUN8 & W2 & W1 & W10 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & AG8).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN8 |].
      assert (LK6 : LIVKe A datas m m6).
      { eapply LIVKe_trans; [exact LK03 |]. eapply LIVKe_trans; [exact (LIVKe_of A datas m3 m4 (proj2 PM4)) |].
        eapply LIVKe_trans; [exact (LKS A1 m4 M5 _ (s - 120)%Z (s - 112)%Z HW4 SUBa ltac:(lia) OUT5) |].
        exact (LKS A1 M5 m6 _ (s - 208 - (16 + 3376))%Z (s - 208)%Z HW5 SUBa ltac:(lia) OUT6). }
      apply (HK fr cs A1 m6 vm1 r8).
      + exact HW6.
      + exact FZ.
      + intros r _. reflexivity.
      + apply cs_kept_intro; csr; reflexivity.
      + eapply POSTM_trans; [exact PM5 |]. apply (POSTM_sub C Ar A1 s M5 m6 SUBr).
        eapply (POSTM_range C A1 M5 _ m6); [exact CK | exact HW5 | exact OUT6 | lia | lia | lia].
      + exact LK6.
      + exact (LIVKe_pix A datas m m6 pixs (hdvr rc w h 1 cm datas) LK6 Lps NEsd Rds PXs).
      + left. split; [rewrite W10; exact A10 | exact LIVEQ].
      + exact Hrm4. }
    destruct (Z.eq_dec w 1) as [Ew1 | Hw1].
    + assert (B10' : getr r4 10 = Z_to_bv 64 0) by (rewrite B10, Ew1; reflexivity).
      apply (V23LeptPixCreateW0.pixCreate_w0_W (fx := mkFP fr cs) C A m3 md r4 (s - 208) (h / 2) 1 _ S CK HW3 ltac:(csr; reflexivity)
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) B1 ltac:(red; apply bv_eq; reflexivity)
               B10' B11 B12 ltac:(left; reflexivity)).
      intros m4 r5 HW4 CS4 PM4 R10.
      rewrite <- (with_vmmaps_same md).
      apply (TAILN A m4 (m_vmmaps md) r5); [rewrite with_vmmaps_same; exact HW4 | exact CS4 | exact PM4 | exact R10 | intros q; reflexivity |].
      pose proof (RB_pixT_nonneg (4 * (wpl_of (w / 2) 1 * (h / 2)))). apply (aroom_mono A (m_vmmaps md) kR bR _ _ Hrm); room_consts; lia.
    + assert (Hw2' : (2 <= w)%Z) by lia.
      destruct (rbw_wpl_half w ltac:(lia)) as [Wpld Hwd].
      assert (Hhd : (1 <= h / 2 <= 10000)%Z) by (split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
      apply (V23LeptPixCreateT2.pixCreate_szT2_W (fx := mkFP fr cs) C A m3 md r4 (s - 208) (w / 2) (h / 2) 1 _ S CK HW3 ltac:(csr; reflexivity)
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) B1 ltac:(red; apply bv_eq; reflexivity) Q4
               B10 B11 B12 ltac:(lia) ltac:(lia) (rbw_prod (w / 2) (h / 2) Hwd Hhd) ltac:(lia)).
      intros A1 m4 vm1 r5 HW4 CS4 PM4 OUT4 HRT4.
      destruct OUT4 as [[R10 LIVEQ] | (pixd & data & Hres & HOKd & PN)].
      { exact (TAILN A1 m4 vm1 r5 HW4 CS4 PM4 R10 LIVEQ (HRT4 kR bR Hrm Hrk Hrb)). }
      pose proof (HRT4 kR bR Hrm Hrk Hrb) as Hrm1.
      destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & LEQ & PXd & Edata).
      cbn [p_wpl p_h set_data O23LeptPixHdrT2.pix_hdr] in TOPd, L1d.
      assert (ALp8 : (pixd mod 8 = 0)%Z) by (clear - ALp; Z.div_mod_to_equations; lia).
      assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in L0p; discriminate).
      assert (SUBa : sub_live A A1) by (eapply sub_live_new2; [exact L0p | exact L0d | exact L1p | exact L1d | exact LEQ]).
      assert (SUBr : sub_live Ar A1) by (eapply sub_live_trans; [exact SUB | exact SUBa]).
      pose proof (SUBa _ _ Lps) as Lps1. pose proof (SUBa _ _ Lds) as Lds1. pose proof (SUBa _ _ Lt) as Lt1.
      pose proof (blk_apart C A1 m4 _ _ _ _ _ CK HW4 Lps1 L1p NEsp ltac:(lia) ltac:(lia)) as APsp. rewrite !u_Z2bv in APsp by lia.
      assert (PM04 : POSTM C Ar s m m4) by (eapply POSTM_trans; [exact PM03 | apply (POSTM_sub C Ar A s m3 m4 SUB); eapply POSTM_mono; [| exact PM4]; lia]).
      pose proof (rbw_PIX_livk A m3 m4 pixs (hdvr rc w h 1 cm datas) (proj2 PM4) Lps PXs3) as PXs4.
      assert (LK04 : LIVKe A datas m m4) by (eapply LIVKe_trans; [exact LK03 | exact (LIVKe_of A datas m3 m4 (proj2 PM4))]).
      assert (F4 : forall (a : Z) (n : nat), (s - 208 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z -> rdn SEGS m4 (Z_to_bv 64 a) n = rdn SEGS m3 (Z_to_bv 64 a) n)
        by (intros a n Ha Hn; exact (FRM_rdn16 C (s - 208) m3 m4 a n CK (proj1 PM4) Ha Hn ltac:(lia))).
      assert (LKX : forall (M M' : word -> option byte) (p n lo hi : Z), W C A1 M (with_vmmaps vm1 md) -> live A1 (Z_to_bv 64 p) = Some n ->
                live A (Z_to_bv 64 p) = None -> (0 <= p < 2 ^ 64)%Z -> (0 <= n)%Z -> (p <= lo)%Z -> (hi <= p + n)%Z ->
                (forall x : word, ~ (s - 208 <= u x < s)%Z -> ~ (lo <= u x < hi)%Z -> M' x = M x) -> LIVKe A datas M M').
      { intros M M' p n lo hi HWM Lp1 Lp0 Hp Hn Hlo' Hhi' OUTM q k i Lq NEq Hi.
        pose proof (SUBa _ _ Lq) as Lq1.
        assert (NEqp : q <> Z_to_bv 64 p) by (intros E; subst q; rewrite Lq in Lp0; discriminate).
        destruct (blk_range C A1 M _ q k CK HWM Lq1 ltac:(lia)) as [Gq TOPq].
        destruct (blk_apart C A1 M _ q (Z_to_bv 64 p) k n CK HWM Lq1 Lp1 NEqp ltac:(lia) Hn) as [D|D]; rewrite u_Z2bv in D by lia;
          apply OUTM; unfold at_; rewrite u_Z2bv by (pose proof (u64_range q); lia); lia. }
      destruct (rb_C al_rom fr cs r5 m4 s pixd pixs (hdvr rc w h 1 cm datas) ltac:(lia) Hs64 ltac:(lia) ltac:(lia) ALp8 ltac:(lia) ALps8
                  ltac:(intros E; apply NEsp; rewrite E; reflexivity) PXs4 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
                  (W_sok_win C A1 m4 _ (s - 120) 8 CK HW4 ltac:(lia) ltac:(cbn; lia))
                  (r90w_sok_blk C A1 m4 _ (Z_to_bv 64 pixd) 64 (pixd + 24) 8 CK HW4 L1p ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
                  ltac:(csr; reflexivity) Hres ltac:(csr; reflexivity))
        as (fr1 & r6 & RUN6 & FA0 & FA1 & FS6 & C1 & C10 & C19 & AG6).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |].
      replace (Z_to_bv 64 0x6f748) with (0x6f748 : word) by (apply bv_eq; reflexivity).
      assert (WP6 : W C A1 (MRB_C m4 s pixd) (with_vmmaps vm1 md) /\ POSTM C Ar s m (MRB_C m4 s pixd)).
      { unfold MRB_C. apply (WP_blk C Ar A1 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | wp_win CK | exact L1p | exact (rbw_live_none Ar A _ SUB L0p) | exact L00p | exact SUBr
          | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
      destruct WP6 as [HW6 PM6].
      assert (OUT6 : forall x : word, ~ (s - 120 <= u x < s - 112)%Z -> ~ (pixd + 24 <= u x < pixd + 32)%Z -> MRB_C m4 s pixd x = m4 x).
      { intros x Hx1 Hx2. unfold MRB_C. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
      assert (PXd6 : PIXat (MRB_C m4 s pixd) pixd (set_data (O23LeptPixHdrT2.pix_hdr (w / 2) (h / 2) 1) data)).
      { unfold MRB_C. apply O23LeptPixCopyTR.PIX_wr_res0; [| reflexivity | reflexivity].
        apply (PIXat_frame m4); [exact PXd |]. intros x Hx. rewrite wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
      assert (LK06 : LIVKe A datas m (MRB_C m4 s pixd)).
      { eapply LIVKe_trans; [exact LK04 |].
        apply (LKX m4 (MRB_C m4 s pixd) pixd 64%Z (pixd + 24)%Z (pixd + 32)%Z HW4 L1p L0p ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        intros x Hx1 Hx2. apply OUT6; [lia | exact Hx2]. }
      apply (V23LeptScaleRes.pixScaleResolution_05_W fr1 cs C A1 (MRB_C m4 s pixd) _ r6 pixd (set_data (O23LeptPixHdrT2.pix_hdr (w / 2) (h / 2) 1) data) _ S CK HW6 FZ C1 ltac:(red; apply bv_eq; reflexivity) C10 FA0 FA1 PXd6
               eq_refl eq_refl L1p L00p).
      intros fr2 cs2 m7 r7 HW7 FZ7 FS7 AG7 R10' PXd7 OUT7.
      assert (LK07 : LIVKe A datas m m7).
      { eapply LIVKe_trans; [exact LK06 |].
        apply (LKX (MRB_C m4 s pixd) m7 pixd 64%Z (pixd + 24)%Z (pixd + 32)%Z HW6 L1p L0p ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        intros x _ Hx. exact (OUT7 x Hx). }
      assert (PM07 : POSTM C Ar s m m7).
      { eapply POSTM_trans; [exact PM6 |]. apply (POSTM_local C Ar A1 (MRB_C m4 s pixd) _ m7 s CK HW6 SUBr).
        intros a NE. right. exists (Z_to_bv 64 pixd), 64%Z. split; [exact L1p | split; [exact (rbw_live_none Ar A _ SUB L0p) |]].
        rewrite u_Z2bv by lia.
        destruct (Z_lt_le_dec (u a) (pixd + 24)) as [Ha|Ha]; [exfalso; apply NE; apply OUT7; lia |].
        destruct (Z_lt_le_dec (u a) (pixd + 32)) as [Hb|Hb]; [lia | exfalso; apply NE; apply OUT7; lia]. }
      assert (F7 : forall (a : Z) (n : nat), (s - 208 <= a)%Z -> (a + Z.of_nat n <= s)%Z -> (a + Z.of_nat n <= s - 120 \/ s - 112 <= a)%Z ->
                rdn SEGS m7 (Z_to_bv 64 a) n = rdn SEGS M2 (Z_to_bv 64 a) n).
      { intros a n Ha Hn Hd. rewrite <- F3 by lia. rewrite <- F4 by lia.
        apply rdn_ext; [rewrite u_Z2bv by lia; lia |]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        rewrite OUT7 by lia. apply OUT6; lia. }
      assert (R136f : rdn SEGS m7 (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (wpl_of w 1)))) by (rewrite F7 by (cbn; lia); exact R136).
      assert (R128f : rdn SEGS m7 (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas))) by (rewrite F7 by (cbn; lia); exact R128).
      assert (R112f : rdn SEGS m7 (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))) by (rewrite F7 by (cbn; lia); exact R112b).
      assert (CE7 : cellsZ m7 (RBCu s ret regs)).
      { apply (cellsZ_keep (MRB_C m4 s pixd) m7); [unfold RBCu; repeat constructor; cbn [fst]; first [lia | intros x Hx; apply OUT7; lia] |].
        apply (cellsZ_keep m4 (MRB_C m4 s pixd)); [unfold RBCu; repeat constructor; cbn [fst]; first [lia | intros x Hx; apply OUT6; lia] |].
        apply (cellsZ_frm C (s - 208) m3 m4 _ CK (proj1 PM4) ltac:(lia)); [unfold RBCu; repeat constructor; cbn [fst]; lia | exact CE3]. }
      assert (ALdat4 : (data mod 4 = 0)%Z) by (clear - ALd; Z.div_mod_to_equations; lia).
      assert (ALds4 : (datas mod 4 = 0)%Z) by (clear - ALds; Z.div_mod_to_equations; lia).
      destruct (rb_D (fx := mkFP fr2 cs2) al_rom r7 m7 s pixd tab h (wpl_of w 1) datas (set_data (O23LeptPixHdrT2.pix_hdr (w / 2) (h / 2) 1) data) ltac:(lia) Hs64 ltac:(lia) ALp8 PXd7 ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn [p_wpl set_data O23LeptPixHdrT2.pix_hdr]; lia) ltac:(lia) ALds4
                  ltac:(cbn [p_data set_data]; lia) ltac:(cbn [p_data set_data]; exact ALdat4)
                  (W_sok_win C A1 m7 _ (s - 208) 72 CK HW7 ltac:(lia) ltac:(cbn; lia)) R136f R128f R112f
                  ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
        as (r8 & RUN8 & D2 & D10 & D11 & D14 & D15 & D16 & D17 & D5 & D7 & D18 & D20 & D22 & D24 & D28 & D29 & D19 & AG8).
      cbn [p_wpl p_data set_data O23LeptPixHdrT2.pix_hdr] in D10, D18.
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
      replace (p_wpl (set_data (O23LeptPixHdrT2.pix_hdr (w / 2) (h / 2) 1) data)) with (wpl_of (w / 2) 1) by reflexivity.
      set (mB := MRB_D m7 s pixd tab (wpl_of w 1) (wpl_of (w / 2) 1) h datas).
      assert (WPB : W C A1 mB (with_vmmaps vm1 md) /\ POSTM C Ar s m mB)
        by (subst mB; apply rbm_D_wp; [exact CK | exact HW7 | exact PM07 | exact SUBr | lia | lia | lia | lia]).
      destruct WPB as [HWB PMB].
      assert (OUTB : forall x : word, ~ (s - 208 <= u x < s - 136)%Z -> mB x = m7 x)
        by (intros x Hx; subst mB; apply rbm_D_out; [lia | lia | exact Hx]).
      assert (Q136 : rdn SEGS mB (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (wpl_of w 1))))
        by (eapply (rdn_after m7 mB (s - 208) (s - 136)); [exact OUTB | lia | cbn; lia | cbn; lia | exact R136f]).
      assert (Q128 : rdn SEGS mB (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)))
        by (eapply (rdn_after m7 mB (s - 208) (s - 136)); [exact OUTB | lia | cbn; lia | cbn; lia | exact R128f]).
      destruct (rbm_D_cells m7 s pixd tab (wpl_of w 1) (wpl_of (w / 2) 1) h datas ltac:(lia) Hs64)
        as (Q144 & Q176 & Q184 & Q160 & Q168 & Q152 & Q208 & Q200).
      assert (CEB : cellsZ mB (RBCu s ret regs)) by (apply (cellsZ_out m7 mB (s - 208) (s - 136)); [exact OUTB | unfold RBCu; repeat constructor; cbn [fst]; lia | exact CE7]).
      assert (PXdB : PIXat mB pixd (set_data (O23LeptPixHdrT2.pix_hdr (w / 2) (h / 2) 1) data)) by (apply (PIXat_frame m7); [exact PXd7 | intros x Hx; apply OUTB; lia]).
      assert (LKB : LIVKe A datas m mB) by (eapply LIVKe_trans; [exact LK07 | exact (LKS A1 m7 mB _ (s - 208)%Z (s - 136)%Z HW7 SUBa ltac:(lia) OUTB)]).
      assert (Hks : (8 * (wpl_of w 1) * (h / 2) <= 4 * ((wpl_of w 1) * h))%Z) by (apply rbw_ks; [lia | lia | apply Z.mul_div_le; lia]).
      assert (Hhk : (0 <= h - 1 <= 2 * (h / 2 - 1) + 2)%Z) by (pose proof (Z.div_mod h 2 ltac:(lia)); pose proof (Z.mod_pos_bound h 2 ltac:(lia)); lia).
      assert (H2hd : (2 * (h / 2) <= h)%Z) by (apply Z.mul_div_le; lia).
      apply (rb_rows_W (fx := mkFP fr2 cs2) C Ar A1 (with_vmmaps vm1 md) mB s data (wpl_of (w / 2) 1) (h / 2) (4 * ((wpl_of (w / 2) 1) * (h / 2))) datas (wpl_of w 1) (4 * ((wpl_of w 1) * h)) tab
               (Z.min (wpl_of w 1) (2 * (wpl_of (w / 2) 1))) S
               CK SUBr L1d ltac:(nia) (rbw_live_none Ar A _ SUB L0d) L00d Lds1 Hks Lt1 ltac:(lia) ALdat4 Rds ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(lia) ltac:(lia) ltac:(lia) h eq_refl ltac:(lia) ALds4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(nia) ltac:(nia)
               ltac:(lia) ltac:(lia) Q136 Q128 Q144 Q176 Q184 Q160 Q168 Q152
               (Z.to_nat (h / 2 - 1)) r8 r8 mB 0%Z HWB (POSTM_refl C Ar s mB) ltac:(intros a _; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)
               ltac:(unfold RREG; repeat split; assumption) (regs_agree_refl _ _)
               ltac:(rewrite D15; f_equal; lia) ltac:(rewrite D16; f_equal; lia) ltac:(rewrite D17; f_equal; lia) ltac:(rewrite D5; f_equal; lia)).
      intros m9 r9 HW9 PM9 FT9 AG9 E15 E16 E17 E5. red in FT9.
      assert (F9 : forall (a : Z) (n : nat), (s - 208 <= a)%Z -> (a + Z.of_nat n <= s)%Z -> rdn SEGS m9 (Z_to_bv 64 a) n = rdn SEGS mB (Z_to_bv 64 a) n).
      { intros a n Ha Hn. apply rdn_ext; [rewrite u_Z2bv by lia; lia |]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply FT9. lia. }
      assert (CE9 : cellsZ m9 (RBCu s ret regs)).
      { apply (cellsZ_keep mB m9); [| exact CEB]. unfold RBCu. repeat constructor; cbn [fst]; first [lia | intros x Hx; apply FT9; lia]. }
      unfold RBCu in CE9.
      destruct (rb_Rx (fx := mkFP fr2 cs2) al_rom r9 m9 s (h / 2 - 1) h (wpl_of w 1) (wpl_of (w / 2) 1) pixd tab ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) Hs64 Hret ltac:(lia) Hhk ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(nia) ltac:(nia) ltac:(lia) ltac:(lia)
                  ltac:(rewrite F9 by (cbn; lia); exact Q160) ltac:(rewrite F9 by (cbn; lia); exact Q168) ltac:(rewrite F9 by (cbn; lia); exact Q152)
                  ltac:(rewrite F9 by (cbn; lia); exact Q208) ltac:(rewrite F9 by (cbn; lia); exact Q200) CE9
                  ltac:(csr; reflexivity) E17 E5 E16 ltac:(csr; reflexivity) E15)
        as (r10 & RUN10 & X2 & X1 & X10 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27 & AG10).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN10 |].
      assert (APpd : (pixd + 64 <= data \/ data + 4 * ((wpl_of (w / 2) 1) * (h / 2)) <= pixd)%Z).
      { assert (NEw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (intros E; apply (f_equal bv_unsigned) in E; rewrite !u_Z2bv in E by lia; lia).
        pose proof (blk_apart C A1 m7 _ _ _ _ _ CK HW7 L1p L1d NEw ltac:(lia) ltac:(lia)) as D. rewrite !u_Z2bv in D by lia. exact D. }
      assert (PXd9 : PIXat m9 pixd (set_data (O23LeptPixHdrT2.pix_hdr (w / 2) (h / 2) 1) data)) by (apply (PIXat_frame mB); [exact PXdB | intros x Hx; apply FT9; nia]).
      assert (LK9 : LIVKe A datas m m9).
      { eapply LIVKe_trans; [exact LKB |].
        apply (LKX mB m9 data (4 * ((wpl_of (w / 2) 1) * (h / 2)))%Z data (data + 4 * ((wpl_of (w / 2) 1) * (h / 2)))%Z HWB L1d L0d ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        intros x _ Hx. apply FT9. nia. }
      apply (HK fr2 cs2 A1 m9 vm1 r10).
      * exact HW9.
      * exact FZ7.
      * intros r Hr. rewrite (FS7 r Hr). exact (FS6 r Hr).
      * apply cs_kept_intro; csr; reflexivity.
      * eapply POSTM_trans; [exact PMB | exact PM9].
      * exact LK9.
      * exact (LIVKe_pix A datas m m9 pixs (hdvr rc w h 1 cm datas) LK9 Lps NEsd Rds PXs).
      * right. exists pixd, data. split; [exact X10 | split; [lia | split; [lia | split; [exact HOKd |]]]].
        unfold O23LeptPixCreateT2.pixr_new. do 15 (split; [assumption |]). assumption.
      * exact Hrm1.
Qed.
End Rb2W.
